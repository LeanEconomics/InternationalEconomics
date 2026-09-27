import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The small open economy with many periods

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§2.1, pp. 60–61. A small open economy faces a constant world interest rate
`r > 0` (p. 66). Net foreign assets `B t` are predetermined at date `t`, and
the current account is `CA_t = B_{t+1} − B_t = Y_t + r B_t − C_t − G_t − I_t`
(O&R (2.2), p. 60).
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics

/-- A small open economy facing the constant world rate `r > 0`. -/
structure Economy where
  r : ℝ
  r_pos : 0 < r

/-- Paths of net foreign assets, output, consumption, government spending and investment. -/
structure Paths where
  B : ℕ → ℝ
  Y : ℕ → ℝ
  C : ℕ → ℝ
  G : ℕ → ℝ
  I : ℕ → ℝ

namespace Economy

/-- The current account `CA_t = Y_t + r B_t − C_t − G_t − I_t` (O&R (2.2), p. 60). -/
def ca (e : Economy) (p : Paths) (t : ℕ) : ℝ :=
  p.Y t + e.r * p.B t - p.C t - p.G t - p.I t

/-- The period budget constraints: `B_{t+1} − B_t = CA_t` on every date. -/
def Flow (e : Economy) (p : Paths) : Prop :=
  ∀ t, p.B (t + 1) - p.B t = e.ca p t

/-- The period constraints in the form O&R (2.3), p. 60:
`(1 + r) B_t = C_t + G_t + I_t − Y_t + B_{t+1}`. -/
theorem flow_iff (e : Economy) (p : Paths) :
    e.Flow p ↔ ∀ t, (1 + e.r) * p.B t = p.C t + p.G t + p.I t - p.Y t + p.B (t + 1) := by
  unfold Flow ca
  constructor
  · intro h t
    linarith [h t]
  · intro h t
    linarith [h t]

end Economy

end ObstfeldRogoff.SmallOpenEconomyDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Present values and discounted telescoping

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§2.1–§2.2, pp. 60–78. The chapter's intertemporal arguments rest on one piece of
algebra. A quantity obeying `A_{s+1} = (1 + r) A_s + N_s` satisfies, after
discounting by `1/(1 + r)` and telescoping,

  `(1 + r)^{-n} A_n = A_0 + Σ_{s<n} (1 + r)^{-(s+1)} N_s`.

With `A` net foreign assets and `N` net output less absorption, this is the
finite-horizon budget constraint O&R (2.4). Its limit as `n → ∞` turns the
transversality condition (2.13) into the intertemporal budget constraint
(2.14): `discounted_tendsto_zero_iff`. With `A` a share price and `N = −d` the
dividend, the same identity gives the forward solution of an asset-pricing
recursion, O&R (2.56)–(2.57): `forward_solution_iff`.

Present values carry explicit `Summable` hypotheses. The book's standing
assumption (p. 66), that discounted quantities grow at a net rate below `r`,
is one sufficient condition: `summable_of_growth`.

Also here: the permanent value `X̃` of O&R (2.17) and its annuity property,
geometric sums (footnote 1, p. 62), and variable interest rates. For
variable rates, footnote 13's identity `Σ_{s>t} R_{t,s} r_s = 1` needs the
discount factors to vanish, which the book leaves unstated.
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue

open Filter Topology Finset

/-- The one-period discount factor `1/(1 + r)`. -/
noncomputable def disc (r : ℝ) : ℝ := (1 + r)⁻¹

theorem disc_pos {r : ℝ} (hr : 0 < 1 + r) : 0 < disc r := inv_pos.2 hr

theorem disc_lt_one {r : ℝ} (hr : 0 < r) : disc r < 1 := inv_lt_one_of_one_lt₀ (by linarith)

theorem one_add_mul_disc {r : ℝ} (hr : 0 < 1 + r) : (1 + r) * disc r = 1 :=
  mul_inv_cancel₀ hr.ne'

/-- **Discounted telescoping**, O&R (2.4), p. 61: if `A_{s+1} = (1 + r) A_s + N_s` then
`(1 + r)^{-n} A_n = A_0 + Σ_{s<n} (1 + r)^{-(s+1)} N_s`. -/
theorem discounted_telescope {r : ℝ} (hr : 0 < 1 + r) {A N : ℕ → ℝ}
    (h : ∀ s, A (s + 1) = (1 + r) * A s + N s) (n : ℕ) :
    disc r ^ n * A n = A 0 + ∑ s ∈ range n, disc r ^ (s + 1) * N s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← add_assoc, ← ih, h n, pow_succ]
    have := one_add_mul_disc hr
    linear_combination disc r ^ n * A n * this

/-- The discounted terminal stock converges, to `A_0 + Σ (1 + r)^{-(s+1)} N_s`. -/
theorem tendsto_discounted {r : ℝ} (hr : 0 < 1 + r) {A N : ℕ → ℝ}
    (h : ∀ s, A (s + 1) = (1 + r) * A s + N s)
    (hs : Summable fun s => disc r ^ (s + 1) * N s) :
    Tendsto (fun n => disc r ^ n * A n) atTop
      (𝓝 (A 0 + ∑' s, disc r ^ (s + 1) * N s)) := by
  simp_rw [discounted_telescope hr h]
  exact tendsto_const_nhds.add hs.hasSum.tendsto_sum_nat

/-- **Transversality ⇔ intertemporal budget constraint**, O&R (2.13) ⇔ (2.14), p. 64: the
discounted terminal stock vanishes iff `A_0 + Σ (1 + r)^{-(s+1)} N_s = 0`. -/
theorem discounted_tendsto_zero_iff {r : ℝ} (hr : 0 < 1 + r) {A N : ℕ → ℝ}
    (h : ∀ s, A (s + 1) = (1 + r) * A s + N s)
    (hs : Summable fun s => disc r ^ (s + 1) * N s) :
    Tendsto (fun n => disc r ^ n * A n) atTop (𝓝 0) ↔
      A 0 + ∑' s, disc r ^ (s + 1) * N s = 0 := by
  have ht := tendsto_discounted hr h hs
  constructor
  · intro h0
    exact tendsto_nhds_unique ht h0
  · intro heq
    rwa [heq] at ht

/-- **No-Ponzi condition**, O&R p. 65 and footnote 4: the discounted terminal stock has a
nonnegative limit iff `A_0 + Σ (1 + r)^{-(s+1)} N_s ≥ 0`. -/
theorem noPonzi_iff {r : ℝ} (hr : 0 < 1 + r) {A N : ℕ → ℝ}
    (h : ∀ s, A (s + 1) = (1 + r) * A s + N s)
    (hs : Summable fun s => disc r ^ (s + 1) * N s) :
    (∃ L, 0 ≤ L ∧ Tendsto (fun n => disc r ^ n * A n) atTop (𝓝 L)) ↔
      0 ≤ A 0 + ∑' s, disc r ^ (s + 1) * N s := by
  have ht := tendsto_discounted hr h hs
  constructor
  · rintro ⟨L, hL, hlim⟩
    rwa [tendsto_nhds_unique ht hlim]
  · intro h0
    exact ⟨_, h0, ht⟩

/-- **Forward telescoping** for an asset-pricing recursion `(1 + r) V_s = d_{s+1} + V_{s+1}`
(O&R (2.53), p. 101): `V_0 = Σ_{s<n} (1 + r)^{-(s+1)} d_{s+1} + (1 + r)^{-n} V_n`. -/
theorem forward_telescope {r : ℝ} (hr : 0 < 1 + r) {V D : ℕ → ℝ}
    (h : ∀ s, (1 + r) * V s = D (s + 1) + V (s + 1)) (n : ℕ) :
    V 0 = ∑ s ∈ range n, disc r ^ (s + 1) * D (s + 1) + disc r ^ n * V n := by
  have h' : ∀ s, V (s + 1) = (1 + r) * V s + -D (s + 1) := fun s => by linarith [h s]
  rw [discounted_telescope hr h' n]
  simp [mul_neg]

/-- **The fundamental asset-pricing equation and bubbles**, O&R (2.56)–(2.57), p. 102: the price
equals the present value of dividends iff the no-bubble condition `(1 + r)^{-n} V_n → 0` holds. -/
theorem forward_solution_iff {r : ℝ} (hr : 0 < 1 + r) {V D : ℕ → ℝ}
    (h : ∀ s, (1 + r) * V s = D (s + 1) + V (s + 1))
    (hs : Summable fun s => disc r ^ (s + 1) * D (s + 1)) :
    V 0 = ∑' s, disc r ^ (s + 1) * D (s + 1) ↔
      Tendsto (fun n => disc r ^ n * V n) atTop (𝓝 0) := by
  have h' : ∀ s, V (s + 1) = (1 + r) * V s + -D (s + 1) := fun s => by linarith [h s]
  have hs' : Summable fun s => disc r ^ (s + 1) * -D (s + 1) := by
    simpa [mul_neg] using hs.neg
  rw [discounted_tendsto_zero_iff hr h' hs']
  simp only [mul_neg, tsum_neg]
  constructor <;> intro e <;> linarith

/-- **The bubble term**: the price exceeds the present value of dividends by exactly the limit
of the discounted price. -/
theorem tendsto_bubble {r : ℝ} (hr : 0 < 1 + r) {V D : ℕ → ℝ}
    (h : ∀ s, (1 + r) * V s = D (s + 1) + V (s + 1))
    (hs : Summable fun s => disc r ^ (s + 1) * D (s + 1)) :
    Tendsto (fun n => disc r ^ n * V n) atTop
      (𝓝 (V 0 - ∑' s, disc r ^ (s + 1) * D (s + 1))) := by
  have h' : ∀ s, V (s + 1) = (1 + r) * V s + -D (s + 1) := fun s => by linarith [h s]
  have hs' : Summable fun s => disc r ^ (s + 1) * -D (s + 1) := by
    simpa [mul_neg] using hs.neg
  have := tendsto_discounted hr h' hs'
  simpa [mul_neg, tsum_neg, sub_eq_add_neg] using this

/-! ### Geometric sums and present values -/

/-- `Σ_{s≥0} (1 + r)^{-s} = (1 + r)/r` for `r > 0`. -/
theorem hasSum_disc_pow {r : ℝ} (hr : 0 < r) : HasSum (fun s => disc r ^ s) ((1 + r) / r) := by
  have h := hasSum_geometric_of_lt_one (disc_pos (by linarith : (0 : ℝ) < 1 + r)).le
    (disc_lt_one hr)
  convert h using 1
  have h1 : (1 : ℝ) + r ≠ 0 := by linarith
  have h2 : r ≠ 0 := hr.ne'
  have h3 : 1 - (1 + r)⁻¹ = r / (1 + r) := by field_simp; ring
  unfold disc
  rw [h3, inv_div]

/-- **Finite geometric sum**, O&R footnote 1, p. 62:
`Σ_{s=0}^{T} (1 + r)^{-s} = (1 + r)(1 − (1 + r)^{-(T+1)})/r`. -/
theorem sum_range_disc_pow {r : ℝ} (hr : 0 < r) (T : ℕ) :
    ∑ s ∈ range (T + 1), disc r ^ s = (1 + r) * (1 - disc r ^ (T + 1)) / r := by
  have hne : disc r ≠ 1 := (disc_lt_one hr).ne
  rw [geom_sum_eq hne]
  have h1 : (1 : ℝ) + r ≠ 0 := by linarith
  have h2 : r ≠ 0 := hr.ne'
  have h3 : (1 + r)⁻¹ - 1 = -(r / (1 + r)) := by field_simp; ring
  unfold disc
  rw [h3, div_neg, ← neg_div, neg_sub, div_div_eq_mul_div]
  ring

/-- The present value `Σ_{s≥0} (1 + r)^{-s} X_s` of a sequence (meaningful when summable). -/
noncomputable def pv (r : ℝ) (X : ℕ → ℝ) : ℝ := ∑' s, disc r ^ s * X s

/-- The permanent value `X̃ = (r/(1 + r)) Σ (1 + r)^{-s} X_s`, O&R (2.17), p. 74: the constant
flow with the same present value. -/
noncomputable def permanent (r : ℝ) (X : ℕ → ℝ) : ℝ := r / (1 + r) * pv r X

/-- The present value of a constant flow `c` is `(1 + r) c / r`. -/
theorem pv_const {r : ℝ} (hr : 0 < r) (c : ℝ) : pv r (fun _ => c) = (1 + r) / r * c := by
  unfold pv
  rw [tsum_mul_right, (hasSum_disc_pow hr).tsum_eq]

/-- **Annuity property of the permanent value**, O&R (2.17): the constant flow `X̃` has the same
present value as `X`. No summability is needed. -/
theorem pv_permanent {r : ℝ} (hr : 0 < r) (X : ℕ → ℝ) :
    pv r (fun _ => permanent r X) = pv r X := by
  rw [pv_const hr, permanent]
  have : (1 : ℝ) + r ≠ 0 := by linarith
  field_simp

/-- Present values are additive for summable flows. -/
theorem pv_add {r : ℝ} {X Y : ℕ → ℝ} (hX : Summable fun s => disc r ^ s * X s)
    (hY : Summable fun s => disc r ^ s * Y s) :
    pv r (fun s => X s + Y s) = pv r X + pv r Y := by
  unfold pv
  simp_rw [mul_add]
  exact hX.tsum_add hY

/-- Present values respect subtraction for summable flows. -/
theorem pv_sub {r : ℝ} {X Y : ℕ → ℝ} (hX : Summable fun s => disc r ^ s * X s)
    (hY : Summable fun s => disc r ^ s * Y s) :
    pv r (fun s => X s - Y s) = pv r X - pv r Y := by
  unfold pv
  simp_rw [mul_sub]
  exact hX.tsum_sub hY

/-- Present values scale. -/
theorem pv_smul (r c : ℝ) (X : ℕ → ℝ) : pv r (fun s => c * X s) = c * pv r X := by
  unfold pv
  simp_rw [mul_left_comm _ c]
  exact tsum_mul_left

/-- Permanent values are additive for summable flows. -/
theorem permanent_add {r : ℝ} {X Y : ℕ → ℝ} (hX : Summable fun s => disc r ^ s * X s)
    (hY : Summable fun s => disc r ^ s * Y s) :
    permanent r (fun s => X s + Y s) = permanent r X + permanent r Y := by
  unfold permanent
  rw [pv_add hX hY]
  ring

/-- Permanent values respect subtraction for summable flows. -/
theorem permanent_sub {r : ℝ} {X Y : ℕ → ℝ} (hX : Summable fun s => disc r ^ s * X s)
    (hY : Summable fun s => disc r ^ s * Y s) :
    permanent r (fun s => X s - Y s) = permanent r X - permanent r Y := by
  unfold permanent
  rw [pv_sub hX hY]
  ring

/-- The permanent value of a constant flow is the flow itself. -/
theorem permanent_const {r : ℝ} (hr : 0 < r) (c : ℝ) : permanent r (fun _ => c) = c := by
  rw [permanent, pv_const hr]
  have : (1 : ℝ) + r ≠ 0 := by linarith
  field_simp

/-- Peeling off the first term: `PV(X) = X_0 + PV(X_{·+1})/(1 + r)`. -/
theorem pv_eq_head_add {r : ℝ} {X : ℕ → ℝ} (hX : Summable fun s => disc r ^ s * X s) :
    pv r X = X 0 + disc r * pv r (fun s => X (s + 1)) := by
  unfold pv
  rw [hX.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, pow_succ]
  congr 1
  refine tsum_congr fun s => ?_
  ring

/-- **Growth below the interest rate implies summability** (the standing assumption, O&R
p. 66): if `|X_s| ≤ M (1 + g)^s` with `−1 < g < r`, the discounted flow is summable. -/
theorem summable_of_growth {r g M : ℝ} (hg : -1 < g) (hgr : g < r) {X : ℕ → ℝ}
    (hb : ∀ s, |X s| ≤ M * (1 + g) ^ s) : Summable fun s => disc r ^ s * X s := by
  have hr : 0 < 1 + r := by linarith
  have hq0 : 0 ≤ (1 + g) / (1 + r) := div_nonneg (by linarith) hr.le
  have hq1 : (1 + g) / (1 + r) < 1 := (div_lt_one hr).2 (by linarith)
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_left M) ?_
  intro s
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (disc_pos hr).le _), div_pow]
  have hd : disc r ^ s * (1 + r) ^ s = 1 := by
    rw [← mul_pow, mul_comm, one_add_mul_disc hr, one_pow]
  calc disc r ^ s * |X s| ≤ disc r ^ s * (M * (1 + g) ^ s) :=
        mul_le_mul_of_nonneg_left (hb s) (pow_nonneg (disc_pos hr).le _)
    _ = M * ((1 + g) ^ s / (1 + r) ^ s) := by
        field_simp
        linear_combination M * (1 + g) ^ s * hd

/-- **The present value of a geometrically growing flow**: for `−1 < g < r`,
`Σ (1 + r)^{-s} (1 + g)^s c = (1 + r) c/(r − g)` (O&R p. 68: `Y/(r − g)` is the present value
of output growing at rate `g`). -/
theorem pv_geometric {r g : ℝ} (hg : -1 < g) (hgr : g < r) (c : ℝ) :
    pv r (fun s => (1 + g) ^ s * c) = (1 + r) / (r - g) * c := by
  have hr : 0 < 1 + r := by linarith
  have hq0 : 0 ≤ (1 + g) / (1 + r) := div_nonneg (by linarith) hr.le
  have hq1 : (1 + g) / (1 + r) < 1 := (div_lt_one hr).2 (by linarith)
  unfold pv
  have e : ∀ s : ℕ, disc r ^ s * ((1 + g) ^ s * c) = ((1 + g) / (1 + r)) ^ s * c := by
    intro s
    unfold disc
    rw [div_pow, inv_pow]
    ring
  simp_rw [e]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1]
  have hrg : r - g ≠ 0 := by linarith
  have h1 : (1 : ℝ) + r ≠ 0 := by linarith
  have e2 : 1 - (1 + g) / (1 + r) = (r - g) / (1 + r) := by field_simp; ring
  rw [e2, inv_div]

/-! ### Variable interest rates (O&R §2.2.2, pp. 76–78) -/

/-- The discount factor over `n` periods with one-period rates `ρ 0, …, ρ (n − 1)`:
`∏_{v<n} (1 + ρ v)^{-1}` (O&R (2.21), p. 76, with the dating shifted to start at 0). -/
noncomputable def varDisc (ρ : ℕ → ℝ) (n : ℕ) : ℝ := ∏ v ∈ range n, (1 + ρ v)⁻¹

theorem varDisc_zero (ρ : ℕ → ℝ) : varDisc ρ 0 = 1 := by simp [varDisc]

theorem varDisc_succ (ρ : ℕ → ℝ) (n : ℕ) : varDisc ρ (n + 1) = varDisc ρ n * (1 + ρ n)⁻¹ := by
  rw [varDisc, varDisc, prod_range_succ]

theorem varDisc_pos {ρ : ℕ → ℝ} (hρ : ∀ v, 0 < 1 + ρ v) (n : ℕ) : 0 < varDisc ρ n :=
  prod_pos fun v _ => inv_pos.2 (hρ v)

/-- `R_{n} − R_{n+1} = ρ_n R_{n+1}`: the one-period change in the discount factor. -/
theorem varDisc_sub_succ {ρ : ℕ → ℝ} (hρ : ∀ v, 0 < 1 + ρ v) (n : ℕ) :
    varDisc ρ n - varDisc ρ (n + 1) = ρ n * varDisc ρ (n + 1) := by
  rw [varDisc_succ]
  have := (hρ n).ne'
  field_simp
  ring

/-- **Discounted telescoping with variable rates**, the finite form behind O&R (2.23): if
`A_{s+1} = (1 + ρ_s) A_s + N_s` then `R_n A_n = A_0 + Σ_{s<n} R_{s+1} N_s`. -/
theorem varDisc_telescope {ρ : ℕ → ℝ} (hρ : ∀ v, 0 < 1 + ρ v) {A N : ℕ → ℝ}
    (h : ∀ s, A (s + 1) = (1 + ρ s) * A s + N s) (n : ℕ) :
    varDisc ρ n * A n = A 0 + ∑ s ∈ range n, varDisc ρ (s + 1) * N s := by
  induction n with
  | zero => simp [varDisc_zero]
  | succ n ih =>
    rw [sum_range_succ, ← add_assoc, ← ih, h n, varDisc_succ]
    have := (hρ n).ne'
    field_simp

/-- **The variable-rate intertemporal budget constraint**, O&R (2.23), p. 77: if the discounted
flows are summable, `R_n A_n → 0` iff `A_0 + Σ R_{s+1} N_s = 0`. -/
theorem varDisc_tendsto_zero_iff {ρ : ℕ → ℝ} (hρ : ∀ v, 0 < 1 + ρ v) {A N : ℕ → ℝ}
    (h : ∀ s, A (s + 1) = (1 + ρ s) * A s + N s)
    (hs : Summable fun s => varDisc ρ (s + 1) * N s) :
    Tendsto (fun n => varDisc ρ n * A n) atTop (𝓝 0) ↔
      A 0 + ∑' s, varDisc ρ (s + 1) * N s = 0 := by
  have ht : Tendsto (fun n => varDisc ρ n * A n) atTop
      (𝓝 (A 0 + ∑' s, varDisc ρ (s + 1) * N s)) := by
    simp_rw [varDisc_telescope hρ h]
    exact tendsto_const_nhds.add hs.hasSum.tendsto_sum_nat
  constructor
  · intro h0
    exact tendsto_nhds_unique ht h0
  · intro heq
    rwa [heq] at ht

/-- **O&R footnote 13, p. 78**: with nonnegative rates, `Σ_{n≥0} ρ_n R_{n+1} = 1` provided the
discount factors `R_n` tend to zero. The book leaves the last hypothesis unstated; it fails,
for example, if all rates are zero. -/
theorem hasSum_rate_mul_varDisc {ρ : ℕ → ℝ} (hρ0 : ∀ v, 0 ≤ ρ v)
    (hlim : Tendsto (varDisc ρ) atTop (𝓝 0)) :
    HasSum (fun n => ρ n * varDisc ρ (n + 1)) 1 := by
  have hρ : ∀ v, 0 < 1 + ρ v := fun v => by linarith [hρ0 v]
  have hnn : ∀ n, 0 ≤ ρ n * varDisc ρ (n + 1) := fun n =>
    mul_nonneg (hρ0 n) (varDisc_pos hρ _).le
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hsum : ∀ N, ∑ n ∈ range N, ρ n * varDisc ρ (n + 1) = 1 - varDisc ρ N := by
    intro N
    induction N with
    | zero => simp [varDisc_zero]
    | succ N ih =>
      rw [sum_range_succ, ih, ← varDisc_sub_succ hρ N]
      ring
  simp_rw [hsum]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hlim

/-- The footnote-13 identity fails without its extra hypothesis: with all rates zero the
discount factors are identically one and the sum is zero, not one. -/
theorem rate_mul_varDisc_zero_rates : (∑' n, (fun _ : ℕ => (0 : ℝ)) n *
    varDisc (fun _ => 0) (n + 1)) = 0 := by
  simp

end ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The intertemporal budget constraint of a small open economy

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§2.1, pp. 60–68, and Chapter 2 Exercise 1, pp. 124–125.

The date `t` of the book is normalised to `0`; `shiftPaths` restarts any path at a
later date and preserves the period constraints, so every result applies at any `t`.

* The finite-horizon constraint O&R (2.4), p. 61, is equivalent to the period
  constraints (2.2) (`flow_iff_finite_ibc`).
* Given the period constraints and summable present values, the transversality
  condition (2.13) is equivalent to the intertemporal budget constraint (2.14), p. 64
  (`transversality_iff_ibc`); the no-Ponzi-game condition is equivalent to the weak
  inequality (footnote 4, p. 65; `noPonzi_iff_ibc_le`).
* Nonnegative consumption bounds foreign debt by the value of future net output, p. 65
  (`debt_limit`), and solvency is a statement about trade surpluses, p. 66
  (`ibc_iff_trade_surplus`).
* A steady debt–output ratio, p. 68 (`steady_ratio_burden`).
* The naive limit condition fails, (2.12), p. 64 (`naive_path`, `naive_limit_zero_iff`).
* Exercise 1 on current-account sustainability. Part (b) holds only for
  `ξ r < 2 (1 + r)`, not for every `ξ > 0` (`ex1_not_summable`).
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint

open Filter Topology Finset PresentValue

/-- The trade balance `TB_s ≡ Y_s − C_s − I_s − G_s`, O&R p. 66. -/
def tradeBalance (p : Paths) (s : ℕ) : ℝ := p.Y s - p.C s - p.I s - p.G s

/-- The paths restarted at date `t`: the book's general date `t`, O&R §2.1, p. 60. -/
def shiftPaths (p : Paths) (t : ℕ) : Paths :=
  ⟨fun s => p.B (t + s), fun s => p.Y (t + s), fun s => p.C (t + s),
    fun s => p.G (t + s), fun s => p.I (t + s)⟩

/-- The deviation from the period constraint O&R (2.2) at date `s`. -/
def residual (e : Economy) (p : Paths) (s : ℕ) : ℝ :=
  p.B (s + 1) - (1 + e.r) * p.B s - tradeBalance p s

/-- The period constraints O&R (2.2), p. 60, as the recursion
`B_{s+1} = (1 + r) B_s + TB_s`. -/
theorem flow_iff_recursion (e : Economy) (p : Paths) :
    e.Flow p ↔ ∀ s, p.B (s + 1) = (1 + e.r) * p.B s + tradeBalance p s := by
  unfold Economy.Flow Economy.ca tradeBalance
  constructor <;> intro h s <;> linarith [h s]

/-- The period constraints O&R (2.2) hold at every date after `t` when they hold
from date `0`: the book's date `t` may be normalised to `0`. -/
theorem flow_shiftPaths (e : Economy) (p : Paths) (h : e.Flow p) (t : ℕ) :
    e.Flow (shiftPaths p t) := by
  intro s
  have := h (t + s)
  unfold Economy.ca at this ⊢
  simpa only [shiftPaths, add_assoc] using this

/-- Accounting identity behind O&R (2.4), p. 61, with no hypotheses: the finite-horizon
constraint holds up to the discounted sum of the period residuals. -/
theorem finite_identity (e : Economy) (p : Paths) (T : ℕ) :
    ∑ s ∈ range (T + 1), disc e.r ^ s * (p.C s + p.I s) + disc e.r ^ T * p.B (T + 1)
      = (1 + e.r) * p.B 0 + ∑ s ∈ range (T + 1), disc e.r ^ s * (p.Y s - p.G s)
        + ∑ s ∈ range (T + 1), disc e.r ^ s * residual e p s := by
  have hd := one_add_mul_disc (show 0 < 1 + e.r by linarith [e.r_pos])
  induction T with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, pow_zero, one_mul, residual,
      tradeBalance]
    ring
  | succ T ih =>
    rw [sum_range_succ, sum_range_succ (fun s => disc e.r ^ s * (p.Y s - p.G s)),
      sum_range_succ (fun s => disc e.r ^ s * residual e p s)]
    simp only [residual, tradeBalance] at ih ⊢
    rw [pow_succ]
    linear_combination ih + disc e.r ^ T * p.B (T + 1) * hd

/-- **Finite-horizon budget constraint**, O&R (2.4), p. 61: the period constraints imply
`Σ_{s≤T} (1+r)^{-s}(C_s + I_s) + (1+r)^{-T} B_{T+1} = (1+r) B_0 + Σ_{s≤T} (1+r)^{-s}(Y_s − G_s)`. -/
theorem finite_ibc (e : Economy) (p : Paths) (h : e.Flow p) (T : ℕ) :
    ∑ s ∈ range (T + 1), disc e.r ^ s * (p.C s + p.I s) + disc e.r ^ T * p.B (T + 1)
      = (1 + e.r) * p.B 0 + ∑ s ∈ range (T + 1), disc e.r ^ s * (p.Y s - p.G s) := by
  have hr := (flow_iff_recursion e p).1 h
  have h0 : ∀ s, residual e p s = 0 := fun s => by unfold residual; linarith [hr s]
  simpa [h0] using finite_identity e p T

/-- **O&R (2.4) ⇔ (2.2)**, p. 61: the finite-horizon constraints for every horizon `T`
hold iff every period constraint holds. -/
theorem flow_iff_finite_ibc (e : Economy) (p : Paths) :
    e.Flow p ↔ ∀ T, ∑ s ∈ range (T + 1), disc e.r ^ s * (p.C s + p.I s)
      + disc e.r ^ T * p.B (T + 1)
      = (1 + e.r) * p.B 0 + ∑ s ∈ range (T + 1), disc e.r ^ s * (p.Y s - p.G s) := by
  refine ⟨finite_ibc e p, fun h => ?_⟩
  have hS : ∀ T, ∑ s ∈ range (T + 1), disc e.r ^ s * residual e p s = 0 := fun T => by
    linarith [finite_identity e p T, h T]
  have hd : disc e.r ≠ 0 := (disc_pos (show 0 < 1 + e.r by linarith [e.r_pos])).ne'
  have h0 : ∀ s, residual e p s = 0 := by
    intro s
    cases s with
    | zero => simpa using hS 0
    | succ n =>
      have := hS (n + 1)
      rw [sum_range_succ, hS n, zero_add] at this
      exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hd)
  refine (flow_iff_recursion e p).2 fun s => ?_
  have := h0 s
  unfold residual at this
  linarith

/-- The discounted terminal stock `(1+r)^{-T} B_{T+1}` of O&R (2.4) converges to
`(1+r) B_0 + PV(Y − G) − PV(C + I)`, given the period constraints and summability. -/
theorem tendsto_terminal (e : Economy) (p : Paths) (h : e.Flow p)
    (hCI : Summable fun s => disc e.r ^ s * (p.C s + p.I s))
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s)) :
    Tendsto (fun T => disc e.r ^ T * p.B (T + 1)) atTop
      (𝓝 ((1 + e.r) * p.B 0 + pv e.r (fun s => p.Y s - p.G s)
        - pv e.r (fun s => p.C s + p.I s))) := by
  unfold pv
  have h1 := hYG.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h2 := hCI.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h3 := ((tendsto_const_nhds (x := (1 + e.r) * p.B 0)).add h1).sub h2
  refine h3.congr fun T => ?_
  simp only [Function.comp]
  linarith [finite_ibc e p h T]

/-- **Transversality ⇔ intertemporal budget constraint**, O&R (2.13) ⇔ (2.14), p. 64:
under the period constraints and summable present values,
`lim (1+r)^{-T} B_{T+1} = 0` iff `PV(C + I) = (1+r) B_0 + PV(Y − G)`. -/
theorem transversality_iff_ibc (e : Economy) (p : Paths) (h : e.Flow p)
    (hCI : Summable fun s => disc e.r ^ s * (p.C s + p.I s))
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s)) :
    Tendsto (fun T => disc e.r ^ T * p.B (T + 1)) atTop (𝓝 0) ↔
      pv e.r (fun s => p.C s + p.I s)
        = (1 + e.r) * p.B 0 + pv e.r (fun s => p.Y s - p.G s) := by
  have ht := tendsto_terminal e p h hCI hYG
  constructor
  · intro h0
    have := tendsto_nhds_unique ht h0
    linarith
  · intro hi
    rwa [show (1 + e.r) * p.B 0 + pv e.r (fun s => p.Y s - p.G s)
      - pv e.r (fun s => p.C s + p.I s) = 0 by linarith] at ht

/-- **No-Ponzi-game condition**, O&R footnote 4, p. 65: `lim (1+r)^{-T} B_{T+1} ≥ 0` iff
`PV(C + I) ≤ (1+r) B_0 + PV(Y − G)`. -/
theorem noPonzi_iff_ibc_le (e : Economy) (p : Paths) (h : e.Flow p)
    (hCI : Summable fun s => disc e.r ^ s * (p.C s + p.I s))
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s)) :
    (∃ L, 0 ≤ L ∧ Tendsto (fun T => disc e.r ^ T * p.B (T + 1)) atTop (𝓝 L)) ↔
      pv e.r (fun s => p.C s + p.I s)
        ≤ (1 + e.r) * p.B 0 + pv e.r (fun s => p.Y s - p.G s) := by
  have ht := tendsto_terminal e p h hCI hYG
  constructor
  · rintro ⟨L, hL, hL'⟩
    have := tendsto_nhds_unique ht hL'
    linarith
  · intro hi
    exact ⟨_, by linarith, ht⟩

/-- **Unrequited gift**, O&R p. 65: `lim (1+r)^{-T} B_{T+1} > 0` iff the present value of
absorption falls strictly short of wealth, `PV(C + I) < (1+r) B_0 + PV(Y − G)`. -/
theorem terminal_pos_iff_ibc_lt (e : Economy) (p : Paths) (h : e.Flow p)
    (hCI : Summable fun s => disc e.r ^ s * (p.C s + p.I s))
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s)) :
    (∃ L, 0 < L ∧ Tendsto (fun T => disc e.r ^ T * p.B (T + 1)) atTop (𝓝 L)) ↔
      pv e.r (fun s => p.C s + p.I s)
        < (1 + e.r) * p.B 0 + pv e.r (fun s => p.Y s - p.G s) := by
  have ht := tendsto_terminal e p h hCI hYG
  constructor
  · rintro ⟨L, hL, hL'⟩
    have := tendsto_nhds_unique ht hL'
    linarith
  · intro hi
    exact ⟨_, by linarith, ht⟩

/-- **Debt limit**, O&R p. 65: if consumption is nonnegative and the (no-Ponzi) budget
constraint holds, then `−(1+r) B_0 ≤ Σ (1+r)^{-s}(Y_s − G_s − I_s)`. -/
theorem debt_limit (e : Economy) (p : Paths) (hC : ∀ s, 0 ≤ p.C s)
    (hCs : Summable fun s => disc e.r ^ s * p.C s)
    (hIs : Summable fun s => disc e.r ^ s * p.I s)
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s))
    (hibc : pv e.r (fun s => p.C s + p.I s)
      ≤ (1 + e.r) * p.B 0 + pv e.r (fun s => p.Y s - p.G s)) :
    -((1 + e.r) * p.B 0) ≤ pv e.r (fun s => p.Y s - p.G s - p.I s) := by
  rw [pv_sub hYG hIs]
  rw [pv_add hCs hIs] at hibc
  have hd := disc_pos (show 0 < 1 + e.r by linarith [e.r_pos])
  have : 0 ≤ pv e.r p.C := tsum_nonneg fun s => mul_nonneg (pow_nonneg hd.le _) (hC s)
  linarith

/-- **Debt limit, book form**, O&R p. 65: for a debtor (`B_0 ≤ 0`), foreign debt `−B_0` is
bounded by the market value of future net output `Σ (1+r)^{-s}(Y_s − G_s − I_s)`. -/
theorem debt_limit_debtor (e : Economy) (p : Paths) (hB : p.B 0 ≤ 0) (hC : ∀ s, 0 ≤ p.C s)
    (hCs : Summable fun s => disc e.r ^ s * p.C s)
    (hIs : Summable fun s => disc e.r ^ s * p.I s)
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s))
    (hibc : pv e.r (fun s => p.C s + p.I s)
      ≤ (1 + e.r) * p.B 0 + pv e.r (fun s => p.Y s - p.G s)) :
    -p.B 0 ≤ pv e.r (fun s => p.Y s - p.G s - p.I s) := by
  have := debt_limit e p hC hCs hIs hYG hibc
  nlinarith [e.r_pos]

/-- The present value of the trade balance is `PV(Y − G) − PV(C + I)`, O&R p. 66. -/
theorem pv_tradeBalance (e : Economy) (p : Paths)
    (hCI : Summable fun s => disc e.r ^ s * (p.C s + p.I s))
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s)) :
    pv e.r (tradeBalance p)
      = pv e.r (fun s => p.Y s - p.G s) - pv e.r (fun s => p.C s + p.I s) := by
  have : tradeBalance p = fun s => (p.Y s - p.G s) - (p.C s + p.I s) := by
    funext s
    unfold tradeBalance
    ring
  rw [this, pv_sub hYG hCI]

/-- **Solvency as trade surpluses**, O&R p. 66: the intertemporal budget constraint (2.14)
holds iff `−(1+r) B_0 = Σ (1+r)^{-s} TB_s`. -/
theorem ibc_iff_trade_surplus (e : Economy) (p : Paths)
    (hCI : Summable fun s => disc e.r ^ s * (p.C s + p.I s))
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s)) :
    pv e.r (fun s => p.C s + p.I s)
        = (1 + e.r) * p.B 0 + pv e.r (fun s => p.Y s - p.G s) ↔
      -((1 + e.r) * p.B 0) = pv e.r (tradeBalance p) := by
  rw [pv_tradeBalance e p hCI hYG]
  constructor <;> intro h <;> linarith

/-- O&R (2.13) ⇔ p. 66: under the period constraints, transversality holds iff the present
value of trade surpluses repays the initial debt with interest. -/
theorem transversality_iff_trade_surplus (e : Economy) (p : Paths) (h : e.Flow p)
    (hCI : Summable fun s => disc e.r ^ s * (p.C s + p.I s))
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s)) :
    Tendsto (fun T => disc e.r ^ T * p.B (T + 1)) atTop (𝓝 0) ↔
      -((1 + e.r) * p.B 0) = pv e.r (tradeBalance p) :=
  (transversality_iff_ibc e p h hCI hYG).trans (ibc_iff_trade_surplus e p hCI hYG)

/-- **Steady debt–output ratio**, O&R p. 68: if `B_{s+1} = (1+g) B_s`, the period constraints
force `TB_s = −(r − g) B_s`. -/
theorem steady_ratio_trade_balance (e : Economy) (p : Paths) {g : ℝ} (h : e.Flow p)
    (hB : ∀ s, p.B (s + 1) = (1 + g) * p.B s) (s : ℕ) :
    tradeBalance p s = -(e.r - g) * p.B s := by
  linarith [(flow_iff_recursion e p).1 h s, hB s]

/-- O&R p. 68: with `Y_{s+1} = (1+g) Y_s` and `−1 < g < r`, `Y_s/(r − g)` is the market
value of a claim to all output from date `s` on, `Σ_{v≥0} (1+r)^{-(v+1)} Y_{s+v}`. -/
theorem output_claim_value (e : Economy) (p : Paths) {g : ℝ} (hg : -1 < g) (hgr : g < e.r)
    (hY : ∀ s, p.Y (s + 1) = (1 + g) * p.Y s) (s : ℕ) :
    ∑' v, disc e.r ^ (v + 1) * p.Y (s + v) = p.Y s / (e.r - g) := by
  have hYv : ∀ v, p.Y (s + v) = (1 + g) ^ v * p.Y s := by
    intro v
    induction v with
    | zero => simp
    | succ v ih => rw [← add_assoc, hY, ih, pow_succ]; ring
  have hf : (fun v => disc e.r ^ (v + 1) * p.Y (s + v))
      = fun v => disc e.r * (disc e.r ^ v * ((1 + g) ^ v * p.Y s)) := by
    funext v
    rw [hYv, pow_succ]
    ring
  have hp := pv_geometric hg hgr (p.Y s)
  unfold pv at hp
  rw [hf, tsum_mul_left, hp]
  have h1 : (1 + e.r) ≠ 0 := by linarith [e.r_pos]
  have h2 : e.r - g ≠ 0 := by linarith
  unfold disc
  field_simp

/-- **Debt burden**, O&R p. 68: along a steady debt–output path, the trade surplus needed as a
share of output is the ratio of debt to the market value of future output,
`TB_s/Y_s = −B_s / [Y_s/(r − g)]`. -/
theorem steady_ratio_burden (e : Economy) (p : Paths) {g : ℝ} (hg : -1 < g) (hgr : g < e.r)
    (h : e.Flow p) (hB : ∀ s, p.B (s + 1) = (1 + g) * p.B s)
    (hY : ∀ s, p.Y (s + 1) = (1 + g) * p.Y s) (s : ℕ) (hYs : p.Y s ≠ 0) :
    tradeBalance p s / p.Y s = -(e.r - g) * p.B s / p.Y s ∧
      tradeBalance p s / p.Y s = -p.B s / ∑' v, disc e.r ^ (v + 1) * p.Y (s + v) := by
  rw [output_claim_value e p hg hgr hY s, steady_ratio_trade_balance e p h hB s]
  refine ⟨rfl, ?_⟩
  have h2 : e.r - g ≠ 0 := by linarith
  field_simp

/-- O&R p. 68: a constant debt–output ratio with growth `−1 < g < r` satisfies the
transversality condition (2.13). -/
theorem steady_ratio_transversality (e : Economy) (p : Paths) {g : ℝ} (hg : -1 < g)
    (hgr : g < e.r) (hB : ∀ s, p.B (s + 1) = (1 + g) * p.B s) :
    Tendsto (fun T => disc e.r ^ T * p.B (T + 1)) atTop (𝓝 0) := by
  have hBn : ∀ n, p.B n = (1 + g) ^ n * p.B 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hB, ih, pow_succ]; ring
  have h1 : 0 < 1 + e.r := by linarith [e.r_pos]
  have hq0 : 0 ≤ (1 + g) * disc e.r := mul_nonneg (by linarith) (disc_pos h1).le
  have hq1 : (1 + g) * disc e.r < 1 := by
    unfold disc
    rw [← div_eq_mul_inv, div_lt_one h1]
    linarith
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const ((1 + g) * p.B 0)
  rw [zero_mul] at this
  refine this.congr fun T => ?_
  rw [hBn (T + 1), mul_pow, pow_succ]
  ring

/-- **The naive path**, O&R (2.12), p. 64: with constant output `Ȳ`, constant consumption
`C̄` and `G = I = 0`, `B_n = B_0 + (r B_0 + Ȳ − C̄)((1+r)^n − 1)/r` (the book's
`B_{t+T+1}` is `n = T + 1`). -/
theorem naive_path (e : Economy) (p : Paths) {Ybar Cbar : ℝ} (h : e.Flow p)
    (hY : ∀ s, p.Y s = Ybar) (hC : ∀ s, p.C s = Cbar) (hG : ∀ s, p.G s = 0)
    (hI : ∀ s, p.I s = 0) (n : ℕ) :
    p.B n = p.B 0 + (e.r * p.B 0 + Ybar - Cbar) * ((1 + e.r) ^ n - 1) / e.r := by
  have hr := e.r_pos.ne'
  induction n with
  | zero => simp
  | succ n ih =>
    rw [(flow_iff_recursion e p).1 h n, ih]
    simp only [tradeBalance, hY, hC, hG, hI]
    field_simp
    ring

/-- O&R p. 64: if `C̄ < r B_0 + Ȳ`, net foreign assets diverge to `+∞`. -/
theorem naive_tendsto_atTop (e : Economy) (p : Paths) {Ybar Cbar : ℝ} (h : e.Flow p)
    (hY : ∀ s, p.Y s = Ybar) (hC : ∀ s, p.C s = Cbar) (hG : ∀ s, p.G s = 0)
    (hI : ∀ s, p.I s = 0) (hlt : Cbar < e.r * p.B 0 + Ybar) :
    Tendsto p.B atTop atTop := by
  have hk : 0 < (e.r * p.B 0 + Ybar - Cbar) / e.r := div_pos (by linarith) e.r_pos
  have hp := tendsto_pow_atTop_atTop_of_one_lt (show 1 < 1 + e.r by linarith [e.r_pos])
  have := tendsto_atTop_add_const_left _ (p.B 0 - (e.r * p.B 0 + Ybar - Cbar) / e.r)
    (hp.const_mul_atTop hk)
  refine this.congr fun n => ?_
  rw [naive_path e p h hY hC hG hI n]
  ring

/-- O&R p. 64: if `C̄ > r B_0 + Ȳ`, net foreign assets diverge to `−∞`. -/
theorem naive_tendsto_atBot (e : Economy) (p : Paths) {Ybar Cbar : ℝ} (h : e.Flow p)
    (hY : ∀ s, p.Y s = Ybar) (hC : ∀ s, p.C s = Cbar) (hG : ∀ s, p.G s = 0)
    (hI : ∀ s, p.I s = 0) (hgt : e.r * p.B 0 + Ybar < Cbar) :
    Tendsto p.B atTop atBot := by
  have hk : (e.r * p.B 0 + Ybar - Cbar) / e.r < 0 := div_neg_of_neg_of_pos (by linarith) e.r_pos
  have hp := tendsto_pow_atTop_atTop_of_one_lt (show 1 < 1 + e.r by linarith [e.r_pos])
  have := tendsto_atBot_add_const_left _ (p.B 0 - (e.r * p.B 0 + Ybar - Cbar) / e.r)
    (hp.const_mul_atTop_of_neg hk)
  refine this.congr fun n => ?_
  rw [naive_path e p h hY hC hG hI n]
  ring

/-- **Failure of the naive limit**, O&R p. 64: for a constant plan, `lim B_n = 0` holds only
in the accidental case `C̄ = Ȳ` and `B_0 = 0`. -/
theorem naive_limit_zero_iff (e : Economy) (p : Paths) {Ybar Cbar : ℝ} (h : e.Flow p)
    (hY : ∀ s, p.Y s = Ybar) (hC : ∀ s, p.C s = Cbar) (hG : ∀ s, p.G s = 0)
    (hI : ∀ s, p.I s = 0) :
    Tendsto p.B atTop (𝓝 0) ↔ Cbar = Ybar ∧ p.B 0 = 0 := by
  constructor
  · intro ht
    rcases lt_trichotomy Cbar (e.r * p.B 0 + Ybar) with hlt | heq | hgt
    · exact absurd ht (not_tendsto_nhds_of_tendsto_atTop
        (naive_tendsto_atTop e p h hY hC hG hI hlt) 0)
    · have hc : ∀ n, p.B n = p.B 0 := fun n => by
        rw [naive_path e p h hY hC hG hI n, heq]; ring
      have h0 : Tendsto p.B atTop (𝓝 (p.B 0)) :=
        tendsto_const_nhds.congr fun n => (hc n).symm
      have hB0 := tendsto_nhds_unique h0 ht
      refine ⟨?_, hB0⟩
      rw [heq, hB0]
      ring
    · exact absurd ht (not_tendsto_nhds_of_tendsto_atBot
        (naive_tendsto_atBot e p h hY hC hG hI hgt) 0)
  · rintro ⟨hCY, hB0⟩
    have hc : ∀ n, p.B n = 0 := fun n => by
      rw [naive_path e p h hY hC hG hI n, hCY, hB0]; ring
    exact tendsto_const_nhds.congr fun n => (hc n).symm

/-- **Transversality for the constant plan**, O&R (2.13), p. 64: with constant `Ȳ`, `C̄` and
`G = I = 0`, the transversality condition holds iff `C̄ = r B_0 + Ȳ`, the only constant plan
meeting the intertemporal budget constraint (2.14). -/
theorem naive_transversality_iff (e : Economy) (p : Paths) {Ybar Cbar : ℝ} (h : e.Flow p)
    (hY : ∀ s, p.Y s = Ybar) (hC : ∀ s, p.C s = Cbar) (hG : ∀ s, p.G s = 0)
    (hI : ∀ s, p.I s = 0) :
    Tendsto (fun T => disc e.r ^ T * p.B (T + 1)) atTop (𝓝 0) ↔
      Cbar = e.r * p.B 0 + Ybar := by
  have hCI : (fun s => p.C s + p.I s) = fun _ => Cbar := by
    funext s; simp [hC, hI]
  have hYG : (fun s => p.Y s - p.G s) = fun _ => Ybar := by
    funext s; simp [hY, hG]
  have hs := (hasSum_disc_pow e.r_pos).summable
  have hsC : Summable fun s => disc e.r ^ s * (p.C s + p.I s) := by
    simpa only [hC, hI, add_zero] using hs.mul_right Cbar
  have hsY : Summable fun s => disc e.r ^ s * (p.Y s - p.G s) := by
    simpa only [hY, hG, sub_zero] using hs.mul_right Ybar
  rw [transversality_iff_ibc e p h hsC hsY, hCI, hYG, pv_const e.r_pos, pv_const e.r_pos]
  have hr := e.r_pos.ne'
  have h1 : (1 + e.r) / e.r ≠ 0 := div_ne_zero (by linarith [e.r_pos]) hr
  have key : (1 + e.r) / e.r * Cbar - ((1 + e.r) * p.B 0 + (1 + e.r) / e.r * Ybar)
      = (1 + e.r) / e.r * (Cbar - (e.r * p.B 0 + Ybar)) := by
    field_simp
  constructor
  · intro hi
    rw [hi, sub_self] at key
    exact sub_eq_zero.1 ((mul_eq_zero.1 key.symm).resolve_left h1)
  · intro hi
    subst hi
    field_simp

/-- **Exercise 1(a)**, O&R p. 124: under the rule `TB_s = −ξ r B_s`, the period constraints
give `B_{s+1} = [1 + (1 − ξ) r] B_s`. -/
theorem ex1_recursion (e : Economy) (p : Paths) {ξ : ℝ} (h : e.Flow p)
    (hTB : ∀ s, tradeBalance p s = -ξ * e.r * p.B s) (s : ℕ) :
    p.B (s + 1) = (1 + (1 - ξ) * e.r) * p.B s := by
  linear_combination (flow_iff_recursion e p).1 h s + hTB s

/-- Exercise 1(a), O&R p. 124, solved: `B_s = [1 + (1 − ξ) r]^s B_0`. -/
theorem ex1_path (e : Economy) (p : Paths) {ξ : ℝ} (h : e.Flow p)
    (hTB : ∀ s, tradeBalance p s = -ξ * e.r * p.B s) (s : ℕ) :
    p.B s = (1 + (1 - ξ) * e.r) ^ s * p.B 0 := by
  induction s with
  | zero => simp
  | succ n ih => rw [ex1_recursion e p h hTB n, ih, pow_succ]; ring

/-- Exercise 1(b), O&R p. 124: the discounted trade balance is geometric,
`(1+r)^{-s} TB_s = q^s (−ξ r B_0)` with `q = [1 + (1 − ξ) r]/(1 + r)`. -/
theorem ex1_discounted_tb (e : Economy) (p : Paths) {ξ : ℝ} (h : e.Flow p)
    (hTB : ∀ s, tradeBalance p s = -ξ * e.r * p.B s) (s : ℕ) :
    disc e.r ^ s * tradeBalance p s
      = ((1 + (1 - ξ) * e.r) * disc e.r) ^ s * (-ξ * e.r * p.B 0) := by
  rw [hTB, ex1_path e p h hTB, mul_pow]
  ring

/-- **Exercise 1(b)**, O&R p. 124: for `0 < ξ` and `ξ r < 2(1 + r)` (i.e. `ξ < 2 + 2/r`) the
discounted trade balances are summable and `Σ (1+r)^{-s} TB_s = −(1+r) B_0`: the
intertemporal budget constraint holds. -/
theorem ex1_ibc (e : Economy) (p : Paths) {ξ : ℝ} (h : e.Flow p)
    (hTB : ∀ s, tradeBalance p s = -ξ * e.r * p.B s) (hξ : 0 < ξ)
    (hξ2 : ξ * e.r < 2 * (1 + e.r)) :
    Summable (fun s => disc e.r ^ s * tradeBalance p s) ∧
      pv e.r (tradeBalance p) = -((1 + e.r) * p.B 0) := by
  have h1 : 0 < 1 + e.r := by linarith [e.r_pos]
  have hq : |(1 + (1 - ξ) * e.r) * disc e.r| < 1 := by
    unfold disc
    rw [← div_eq_mul_inv, abs_lt, lt_div_iff₀ h1, div_lt_one h1]
    constructor <;> nlinarith [e.r_pos]
  have hf : (fun s => disc e.r ^ s * tradeBalance p s)
      = fun s => ((1 + (1 - ξ) * e.r) * disc e.r) ^ s * (-ξ * e.r * p.B 0) := by
    funext s
    exact ex1_discounted_tb e p h hTB s
  refine ⟨hf ▸ (summable_geometric_of_abs_lt_one hq).mul_right _, ?_⟩
  unfold pv
  rw [hf, tsum_mul_right, tsum_geometric_of_abs_lt_one hq]
  have hne : 1 - (1 + (1 - ξ) * e.r) * disc e.r = ξ * e.r * disc e.r := by
    have := one_add_mul_disc h1
    linear_combination -this
  rw [hne]
  have hd := (disc_pos h1).ne'
  have hr := e.r_pos.ne'
  have := one_add_mul_disc h1
  field_simp
  linear_combination p.B 0 * this

/-- Exercise 1(b), O&R p. 124: for `0 < ξ` and `ξ r < 2(1 + r)` the transversality condition
(2.13) holds along the rule's path. -/
theorem ex1_transversality (e : Economy) (p : Paths) {ξ : ℝ} (h : e.Flow p)
    (hTB : ∀ s, tradeBalance p s = -ξ * e.r * p.B s) (hξ : 0 < ξ)
    (hξ2 : ξ * e.r < 2 * (1 + e.r)) :
    Tendsto (fun T => disc e.r ^ T * p.B (T + 1)) atTop (𝓝 0) := by
  have h1 : 0 < 1 + e.r := by linarith [e.r_pos]
  have hq : |(1 + (1 - ξ) * e.r) * disc e.r| < 1 := by
    unfold disc
    rw [← div_eq_mul_inv, abs_lt, lt_div_iff₀ h1, div_lt_one h1]
    constructor <;> nlinarith [e.r_pos]
  have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq).mul_const
    ((1 + (1 - ξ) * e.r) * p.B 0)
  rw [zero_mul] at this
  refine this.congr fun T => ?_
  rw [ex1_path e p h hTB (T + 1), mul_pow, pow_succ]
  ring

/-- **Correction to Exercise 1(b)**, O&R p. 124: the claim "for any `ξ > 0`" fails for large
`ξ`. If `ξ r ≥ 2(1 + r)` and `B_0 ≠ 0`, the ratio `[1 + (1 − ξ) r]/(1 + r) ≤ −1` and the
discounted trade balances are not summable, so the present value in (2.14) does not exist. -/
theorem ex1_not_summable (e : Economy) (p : Paths) {ξ : ℝ} (h : e.Flow p)
    (hTB : ∀ s, tradeBalance p s = -ξ * e.r * p.B s) (hξ2 : 2 * (1 + e.r) ≤ ξ * e.r)
    (hB0 : p.B 0 ≠ 0) :
    ¬ Summable (fun s => disc e.r ^ s * tradeBalance p s) := by
  intro hs
  have h1 : 0 < 1 + e.r := by linarith [e.r_pos]
  have hq : 1 ≤ |(1 + (1 - ξ) * e.r) * disc e.r| := by
    have : (1 + (1 - ξ) * e.r) * disc e.r ≤ -1 := by
      unfold disc
      rw [← div_eq_mul_inv, div_le_iff₀ h1]
      linarith
    rw [abs_of_neg (by linarith)]
    linarith
  have hξ : 0 < ξ := by
    by_contra hn
    push Not at hn
    nlinarith [e.r_pos]
  have hc : 0 < |ξ * e.r * p.B 0| := abs_pos.2 (mul_ne_zero (mul_pos hξ e.r_pos).ne' hB0)
  have hbig : ∀ s, |ξ * e.r * p.B 0| ≤ |disc e.r ^ s * tradeBalance p s| := by
    intro s
    rw [ex1_discounted_tb e p h hTB, abs_mul (_ ^ s), abs_pow, neg_mul, neg_mul, abs_neg]
    exact le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hq)
  have ht := hs.tendsto_atTop_zero.abs
  rw [abs_zero] at ht
  obtain ⟨s, hs'⟩ := (ht.eventually (gt_mem_nhds hc)).exists
  exact absurd (hbig s) (not_le.2 hs')

/-- **Exercise 1(c)**, O&R p. 125: with `G = I = 0` and constant output `Ȳ`, the rule means
consumption `C_s = Ȳ + ξ r B_s`. -/
theorem ex1_consumption (p : Paths) {ξ r Ybar : ℝ} (hY : ∀ s, p.Y s = Ybar)
    (hG : ∀ s, p.G s = 0) (hI : ∀ s, p.I s = 0)
    (hTB : ∀ s, tradeBalance p s = -ξ * r * p.B s) (s : ℕ) :
    p.C s = Ybar + ξ * r * p.B s := by
  have := hTB s
  unfold tradeBalance at this
  rw [hY, hG, hI] at this
  linarith

/-- **Exercise 1(c)**, O&R p. 125: for a debtor (`B_0 < 0`) with `0 < ξ < 1`, debt grows
without bound, `B_s → −∞`, although the budget constraint holds (`ex1_ibc`). -/
theorem ex1_debt_unbounded (e : Economy) (p : Paths) {ξ : ℝ} (h : e.Flow p)
    (hTB : ∀ s, tradeBalance p s = -ξ * e.r * p.B s) (hξ1 : ξ < 1) (hB0 : p.B 0 < 0) :
    Tendsto p.B atTop atBot := by
  have hq : 1 < 1 + (1 - ξ) * e.r := by nlinarith [e.r_pos]
  have := (tendsto_pow_atTop_atTop_of_one_lt hq).atTop_mul_const_of_neg hB0
  exact this.congr fun s => (ex1_path e p h hTB s).symm

/-- **Exercise 1(c)**, O&R p. 125: for `B_0 < 0` and `0 < ξ < 1`, eventually the debt exceeds
the value of all future output, `−(1+r) B_s > Σ (1+r)^{-v} Ȳ`, and consumption
`C_s = Ȳ + ξ r B_s` turns negative. The budget constraint holds only because the rule
eventually demands infeasible (negative) consumption. -/
theorem ex1_eventually_infeasible (e : Economy) (p : Paths) {ξ Ybar : ℝ} (h : e.Flow p)
    (hY : ∀ s, p.Y s = Ybar) (hG : ∀ s, p.G s = 0) (hI : ∀ s, p.I s = 0)
    (hTB : ∀ s, tradeBalance p s = -ξ * e.r * p.B s) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hB0 : p.B 0 < 0) :
    ∃ S, ∀ s, S ≤ s →
      pv e.r (fun _ => Ybar) < -((1 + e.r) * p.B s) ∧ p.C s < 0 := by
  have hr := e.r_pos
  have ht := ex1_debt_unbounded e p h hTB hξ1 hB0
  have hev := ht.eventually (eventually_lt_atBot (min (-Ybar / e.r) (-Ybar / (ξ * e.r))))
  obtain ⟨S, hS⟩ := eventually_atTop.1 hev
  refine ⟨S, fun s hs => ?_⟩
  have hb := hS s hs
  have hb1 : p.B s < -Ybar / e.r := lt_of_lt_of_le hb (min_le_left _ _)
  have hb2 : p.B s < -Ybar / (ξ * e.r) := lt_of_lt_of_le hb (min_le_right _ _)
  rw [lt_div_iff₀ hr] at hb1
  rw [lt_div_iff₀ (mul_pos hξ hr)] at hb2
  rw [pv_const hr, ex1_consumption p hY hG hI hTB s]
  refine ⟨?_, by linarith⟩
  have h1 : 0 < 1 + e.r := by linarith
  rw [div_mul_eq_mul_div, div_lt_iff₀ hr]
  nlinarith

end ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal consumption over an infinite horizon

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§2.1, pp. 60–73, and Supplement A.1, pp. 715–718. A consumer with time-separable
utility `Σ β^s u(C_s)` (O&R (2.11), p. 63) chooses a consumption path whose present
value does not exceed lifetime wealth `W`. Investment and government spending
are netted out of `W`, as the intertemporal budget constraint (2.14) allows.

The book assumes an optimum exists (p. 63) and reads off the Euler equation
(2.5). We prove:
* **sufficiency** (`isOptimal_of_euler`): if `u` is concave, a positive path that
  satisfies the Euler equation `u'(C_s) = (1 + r) β u'(C_{s+1})` and exhausts wealth
  is optimal among all admissible paths. Iterating the Euler equation gives
  `β^s u'(C_s) = u'(C_0)(1 + r)^{-s}`, so the gain from any deviation is bounded by
  `u'(C_0)` times its present-value cost;
* **strict optimality** when `u` is strictly concave: any other admissible path is
  strictly worse, so the optimum is unique;
* **necessity**: at an optimum the budget constraint binds
  (`pv_eq_of_optimal`, the book's transversality property) and the Euler equation
  holds (`euler_of_optimal`, by moving consumption between adjacent dates);
* **the consumption tilt** (p. 71): consumption rises, stays flat or falls as
  `β(1 + r)` is above, equal to or below one;
* **dynamic consistency** (§2.1.4, p. 72): the continuation of an optimal plan is
  optimal given the wealth it leaves;
* **Strotz** (p. 73): with the quasi-hyperbolic weight `(1 + γ)` on current utility,
  the marginal rate of substitution between two future dates changes once the
  first of them arrives.

Admissible paths are positive, have a summable present value and summable
lifetime utility: the explicit counterpart of the book's convergence assumption.
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality

open PresentValue Filter Topology Set Finset

/-- The tangent line of a concave function lies weakly above its graph (copied from the
`IntertemporalTrade` project so that this project builds on its own). -/
theorem concave_le_tangent' {f : ℝ → ℝ} {S : Set ℝ} (hf : ConcaveOn ℝ S f) {x y d : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f d x) : f y ≤ f x + d * (y - x) := by
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · have h := hf.le_slope_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    linarith
  · simp
  · have h := hf.slope_le_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    linarith

/-- The strict tangent inequality for a strictly concave function. -/
theorem strictConcave_lt_tangent {f : ℝ → ℝ} {S : Set ℝ} (hf : StrictConcaveOn ℝ S f)
    {x y d : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hxy : y ≠ x) (hd : HasDerivAt f d x) :
    f y < f x + d * (y - x) := by
  rcases lt_or_gt_of_ne hxy with hyx | hxy
  · have h := hf.lt_slope_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field, lt_div_iff₀ (by linarith)] at h
    linarith
  · have h := hf.slope_lt_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field, div_lt_iff₀ (by linarith)] at h
    linarith

/-- Lifetime utility `Σ_{s≥0} β^s u(C_s)`, O&R (2.11), p. 63. -/
noncomputable def lifetimeUtility (u : ℝ → ℝ) (β : ℝ) (C : ℕ → ℝ) : ℝ := ∑' s, β ^ s * u (C s)

/-- An admissible consumption path at interest rate `r` and wealth `W`: positive, with summable
present value and lifetime utility, and present value at most `W` (O&R (2.14)). -/
def Admissible (u : ℝ → ℝ) (β r W : ℝ) (C : ℕ → ℝ) : Prop :=
  (∀ s, 0 < C s) ∧ Summable (fun s => disc r ^ s * C s) ∧
    Summable (fun s => β ^ s * u (C s)) ∧ pv r C ≤ W

/-- An optimal path: admissible and at least as good as every admissible path. -/
def IsOptimal (u : ℝ → ℝ) (β r W : ℝ) (C : ℕ → ℝ) : Prop :=
  Admissible u β r W C ∧ ∀ D, Admissible u β r W D → lifetimeUtility u β D ≤ lifetimeUtility u β C

/-- **Iterated Euler equation**, Supplement A (SA(3)), p. 717: if `u'(C_s) = (1 + r) β u'(C_{s+1})`
for all `s`, then `(β(1 + r))^s u'(C_s) = u'(C_0)`. -/
theorem euler_iterate {u' : ℝ → ℝ} {β r : ℝ} {C : ℕ → ℝ}
    (he : ∀ s, u' (C s) = (1 + r) * β * u' (C (s + 1))) (s : ℕ) :
    (β * (1 + r)) ^ s * u' (C s) = u' (C 0) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [← ih, he s, pow_succ]
    ring

/-- The discounted marginal utility equals `u'(C₀)` times the market discount factor:
`β^s u'(C_s) = u'(C₀)(1 + r)^{-s}` (Supplement A, p. 717). -/
theorem discounted_marginal_utility {u' : ℝ → ℝ} {β r : ℝ} (hr : 0 < 1 + r) {C : ℕ → ℝ}
    (he : ∀ s, u' (C s) = (1 + r) * β * u' (C (s + 1))) (s : ℕ) :
    β ^ s * u' (C s) = u' (C 0) * disc r ^ s := by
  have h := euler_iterate he s
  rw [mul_pow] at h
  have hd : (1 + r) ^ s * disc r ^ s = 1 := by rw [← mul_pow, one_add_mul_disc hr, one_pow]
  calc β ^ s * u' (C s) = β ^ s * (1 + r) ^ s * u' (C s) * disc r ^ s := by
        linear_combination (-(β ^ s * u' (C s))) * hd
    _ = u' (C 0) * disc r ^ s := by rw [h]

/-- A finite modification of a summable sequence: if `g` agrees with `f` off a finite set `S`,
then `g` is summable and `Σ g = Σ f + Σ_{t∈S} (g t − f t)`. -/
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

/-- **Sufficiency of the Euler equation**, O&R pp. 62–65 and Supplement A: with `u` concave and
differentiable and `β > 0`, a positive path satisfying the Euler equation and exhausting wealth,
`PV(C) = W`, is optimal. The proof bounds the utility gain of any admissible `D` by
`u'(C₀)(PV(D) − PV(C)) ≤ 0`. -/
theorem isOptimal_of_euler {u u' : ℝ → ℝ} {β r W : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    (hconc : ConcaveOn ℝ (Ioi 0) u) (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    {C : ℕ → ℝ} (hC : Admissible u β r W C) (hbind : pv r C = W) (hpos : 0 ≤ u' (C 0))
    (he : ∀ s, u' (C s) = (1 + r) * β * u' (C (s + 1))) :
    IsOptimal u β r W C := by
  refine ⟨hC, fun D hD => ?_⟩
  obtain ⟨hCpos, hCpv, hCu, -⟩ := hC
  obtain ⟨hDpos, hDpv, hDu, hDW⟩ := hD
  have hterm : ∀ s, β ^ s * u (D s) ≤
      β ^ s * u (C s) + u' (C 0) * (disc r ^ s * D s - disc r ^ s * C s) := by
    intro s
    have t := concave_le_tangent' hconc (mem_Ioi.2 (hCpos s)) (mem_Ioi.2 (hDpos s))
      (hu _ (hCpos s))
    have key : β ^ s * (u' (C s) * (D s - C s)) =
        u' (C 0) * (disc r ^ s * D s - disc r ^ s * C s) := by
      rw [← mul_assoc, discounted_marginal_utility hr he s]
      ring
    have := mul_le_mul_of_nonneg_left t (pow_nonneg hβ.le s)
    linarith
  have hsum : Summable fun s => β ^ s * u (C s) + u' (C 0) *
      (disc r ^ s * D s - disc r ^ s * C s) := hCu.add ((hDpv.sub hCpv).mul_left _)
  have hle := hDu.tsum_le_tsum hterm hsum
  rw [hCu.tsum_add ((hDpv.sub hCpv).mul_left _), tsum_mul_left, hDpv.tsum_sub hCpv] at hle
  unfold lifetimeUtility
  have hpvD : ∑' s, disc r ^ s * D s ≤ ∑' s, disc r ^ s * C s := by
    have := hDW
    unfold pv at this hbind
    linarith
  nlinarith

/-- **Strict optimality and uniqueness**: with `u` strictly concave, every admissible path other
than the Euler path is strictly worse. -/
theorem lifetimeUtility_lt_of_euler {u u' : ℝ → ℝ} {β r W : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    (hconc : StrictConcaveOn ℝ (Ioi 0) u) (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    {C : ℕ → ℝ} (hC : Admissible u β r W C) (hbind : pv r C = W) (hpos : 0 ≤ u' (C 0))
    (he : ∀ s, u' (C s) = (1 + r) * β * u' (C (s + 1))) {D : ℕ → ℝ}
    (hD : Admissible u β r W D) (hne : D ≠ C) :
    lifetimeUtility u β D < lifetimeUtility u β C := by
  obtain ⟨hCpos, hCpv, hCu, -⟩ := hC
  obtain ⟨hDpos, hDpv, hDu, hDW⟩ := hD
  obtain ⟨k, hk⟩ : ∃ k, D k ≠ C k := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have key : ∀ s, β ^ s * (u' (C s) * (D s - C s)) =
      u' (C 0) * (disc r ^ s * D s - disc r ^ s * C s) := fun s => by
    rw [← mul_assoc, discounted_marginal_utility hr he s]
    ring
  have hterm : ∀ s, β ^ s * u (D s) ≤
      β ^ s * u (C s) + u' (C 0) * (disc r ^ s * D s - disc r ^ s * C s) := by
    intro s
    have t := concave_le_tangent' hconc.concaveOn (mem_Ioi.2 (hCpos s)) (mem_Ioi.2 (hDpos s))
      (hu _ (hCpos s))
    have := mul_le_mul_of_nonneg_left t (pow_nonneg hβ.le s)
    linarith [key s]
  have hstrict : β ^ k * u (D k) <
      β ^ k * u (C k) + u' (C 0) * (disc r ^ k * D k - disc r ^ k * C k) := by
    have t := strictConcave_lt_tangent hconc (mem_Ioi.2 (hCpos k)) (mem_Ioi.2 (hDpos k)) hk
      (hu _ (hCpos k))
    have := mul_lt_mul_of_pos_left t (pow_pos hβ k)
    linarith [key k]
  have hsum : Summable fun s => β ^ s * u (C s) + u' (C 0) *
      (disc r ^ s * D s - disc r ^ s * C s) := hCu.add ((hDpv.sub hCpv).mul_left _)
  have hlt := hDu.tsum_lt_tsum hterm hstrict hsum
  rw [hCu.tsum_add ((hDpv.sub hCpv).mul_left _), tsum_mul_left, hDpv.tsum_sub hCpv] at hlt
  unfold lifetimeUtility
  have hpvD : ∑' s, disc r ^ s * D s ≤ ∑' s, disc r ^ s * C s := by
    have := hDW
    unfold pv at this hbind
    linarith
  nlinarith

/-- **The budget constraint binds at an optimum** (O&R pp. 64–65, footnote 4; Supplement A,
SA(4)): with `u` strictly increasing and `β > 0`, an optimal path exhausts wealth. -/
theorem pv_eq_of_optimal {u : ℝ → ℝ} {β r W : ℝ}
    (hmono : StrictMonoOn u (Ioi 0)) {C : ℕ → ℝ} (hC : IsOptimal u β r W C) :
    pv r C = W := by
  obtain ⟨⟨hCpos, hCpv, hCu, hCW⟩, hmax⟩ := hC
  by_contra hne
  have hlt : pv r C < W := lt_of_le_of_ne hCW hne
  set δ := W - pv r C with hδ
  have hδpos : 0 < δ := by linarith
  set D : ℕ → ℝ := fun s => if s = 0 then C 0 + δ else C s with hD
  have hoff : ∀ t, t ∉ ({0} : Finset ℕ) → D t = C t := fun t ht => by
    simp only [Finset.mem_singleton] at ht
    simp [hD, ht]
  obtain ⟨hDpv, hDpv_eq⟩ := tsum_eq_add_of_eqOn_compl hCpv {0}
    (g := fun t => disc r ^ t * D t) fun t ht => by simp only [hoff t ht]
  obtain ⟨hDu, hDu_eq⟩ := tsum_eq_add_of_eqOn_compl hCu {0}
    (g := fun t => β ^ t * u (D t)) fun t ht => by simp only [hoff t ht]
  have hDpos : ∀ s, 0 < D s := fun s => by
    by_cases hs : s = 0
    · simp only [hD, hs]; simp only [↓reduceIte]; linarith [hCpos 0]
    · simp only [hD, hs]; simp only [↓reduceIte]; exact hCpos s
  have hDW : pv r D ≤ W := by
    unfold pv
    rw [hDpv_eq]
    simp [hD]
    unfold pv at hδ
    linarith
  have hgain := hmax D ⟨hDpos, hDpv, hDu, hDW⟩
  unfold lifetimeUtility at hgain
  rw [hDu_eq] at hgain
  have hu0 : u (C 0) < u (C 0 + δ) :=
    hmono (mem_Ioi.2 (hCpos 0)) (mem_Ioi.2 (by linarith [hCpos 0])) (by linarith)
  simp [hD] at hgain
  linarith

/-- **Euler equation**, O&R (2.5), p. 61: at an optimum with differentiable `u`,
`u'(C_s) = (1 + r) β u'(C_{s+1})` for every `s`. The proof moves `ε` of consumption from date
`s` to date `s + 1`, which leaves the present value unchanged. -/
theorem euler_of_optimal {u u' : ℝ → ℝ} {β r W : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) {C : ℕ → ℝ} (hC : IsOptimal u β r W C)
    (s : ℕ) : u' (C s) = (1 + r) * β * u' (C (s + 1)) := by
  obtain ⟨⟨hCpos, hCpv, hCu, hCW⟩, hmax⟩ := hC
  -- the perturbed path
  let D : ℝ → ℕ → ℝ := fun ε t =>
    if t = s then C s - ε else if t = s + 1 then C (s + 1) + (1 + r) * ε else C t
  have hoff : ∀ ε t, t ∉ ({s, s + 1} : Finset ℕ) → D ε t = C t := fun ε t ht => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    simp [D, ht.1, ht.2]
  have hne : s + 1 ≠ s := Nat.succ_ne_self s
  have hDs : ∀ ε, D ε s = C s - ε := fun ε => by simp [D]
  have hDs1 : ∀ ε, D ε (s + 1) = C (s + 1) + (1 + r) * ε := fun ε => by simp [D]
  -- present value is unchanged
  have hpvD : ∀ ε, Summable (fun t => disc r ^ t * D ε t) ∧ pv r (D ε) = pv r C := by
    intro ε
    obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hCpv {s, s + 1}
      (g := fun t => disc r ^ t * D ε t) fun t ht => by simp only [hoff ε t ht]
    refine ⟨h1, ?_⟩
    unfold pv
    rw [h2, Finset.sum_pair hne.symm, hDs, hDs1, pow_succ]
    have := one_add_mul_disc hr
    linear_combination (disc r ^ s * ε) * this
  -- utility changes only at s and s + 1
  have huD : ∀ ε, Summable (fun t => β ^ t * u (D ε t)) ∧ lifetimeUtility u β (D ε) =
      lifetimeUtility u β C + (β ^ s * u (C s - ε) - β ^ s * u (C s)) +
        (β ^ (s + 1) * u (C (s + 1) + (1 + r) * ε) - β ^ (s + 1) * u (C (s + 1))) := by
    intro ε
    obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hCu {s, s + 1}
      (g := fun t => β ^ t * u (D ε t)) fun t ht => by simp only [hoff ε t ht]
    refine ⟨h1, ?_⟩
    unfold lifetimeUtility
    rw [h2, Finset.sum_pair hne.symm, hDs, hDs1]
    ring
  -- for small ε the perturbed path is positive, hence admissible
  have hcont1 : Continuous fun ε : ℝ => C s - ε := by fun_prop
  have hcont2 : Continuous fun ε : ℝ => C (s + 1) + (1 + r) * ε := by fun_prop
  have hev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C s - ε :=
    (hcont1.tendsto 0).eventually (lt_mem_nhds (by simpa using hCpos s))
  have hev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C (s + 1) + (1 + r) * ε :=
    (hcont2.tendsto 0).eventually (lt_mem_nhds (by simpa using hCpos (s + 1)))
  set φ : ℝ → ℝ := fun ε => β ^ s * u (C s - ε) + β ^ (s + 1) * u (C (s + 1) + (1 + r) * ε)
  have hloc : IsLocalMax φ 0 := by
    filter_upwards [hev1, hev2] with ε h1 h2
    have hpos : ∀ t, 0 < D ε t := fun t => by
      by_cases ht : t = s
      · rw [ht, hDs]; exact h1
      by_cases ht1 : t = s + 1
      · rw [ht1, hDs1]; exact h2
      rw [hoff ε t (by simp [ht, ht1])]
      exact hCpos t
    have hadm : Admissible u β r W (D ε) :=
      ⟨hpos, (hpvD ε).1, (huD ε).1, by rw [(hpvD ε).2]; exact hCW⟩
    have := hmax _ hadm
    rw [(huD ε).2] at this
    simp only [φ, sub_zero, mul_zero, add_zero]
    linarith
  have hd1 : HasDerivAt (fun ε : ℝ => C s - ε) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub (C s)
  have hd2 : HasDerivAt (fun ε : ℝ => C (s + 1) + (1 + r) * ε) (1 + r) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 + r)).const_add (C (s + 1))
  have hA : HasDerivAt (fun ε => β ^ s * u (C s - ε)) (β ^ s * (u' (C s) * (-1))) 0 := by
    have h1 : HasDerivAt u (u' (C s)) ((fun ε : ℝ => C s - ε) 0) := by
      simpa using hu _ (hCpos s)
    exact (h1.comp (0 : ℝ) hd1).const_mul _
  have hB : HasDerivAt (fun ε => β ^ (s + 1) * u (C (s + 1) + (1 + r) * ε))
      (β ^ (s + 1) * (u' (C (s + 1)) * (1 + r))) 0 := by
    have h1 : HasDerivAt u (u' (C (s + 1))) ((fun ε : ℝ => C (s + 1) + (1 + r) * ε) 0) := by
      simpa using hu _ (hCpos (s + 1))
    exact (h1.comp (0 : ℝ) hd2).const_mul _
  have h0 := hloc.hasDerivAt_eq_zero (hA.add hB)
  rw [pow_succ] at h0
  have hβs : 0 < β ^ s := pow_pos hβ s
  have : β ^ s * (u' (C s) - (1 + r) * β * u' (C (s + 1))) = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_left hβs.ne'
  linarith

/-- The derivative of a strictly concave function is strictly decreasing (copied from the
`IntertemporalTrade` project). -/
theorem deriv_lt_of_strictConcave' {f : ℝ → ℝ} {S : Set ℝ} (hf : StrictConcaveOn ℝ S f)
    {x y dx dy : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hdx : HasDerivAt f dx x)
    (hdy : HasDerivAt f dy y) : dy < dx :=
  (hf.lt_slope_of_hasDerivAt hx hy hxy hdy).trans (hf.slope_lt_of_hasDerivAt hx hy hxy hdx)

/-- **Consumption tilts up** (O&R p. 71): if `β(1 + r) > 1` and `u' > 0`, a path satisfying the
Euler equation is strictly increasing. -/
theorem tilt_up {u u' : ℝ → ℝ} {β r : ℝ} (hconc : StrictConcaveOn ℝ (Ioi 0) u)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hβr : 1 < β * (1 + r)) {C : ℕ → ℝ} (hCpos : ∀ s, 0 < C s)
    (he : ∀ s, u' (C s) = (1 + r) * β * u' (C (s + 1))) (s : ℕ) : C s < C (s + 1) := by
  have hp := hpos _ (hCpos (s + 1))
  have hgt : u' (C (s + 1)) < u' (C s) := by rw [he s]; nlinarith
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · exact absurd hgt (deriv_lt_of_strictConcave' hconc (mem_Ioi.2 (hCpos _))
      (mem_Ioi.2 (hCpos _)) hlt (hu _ (hCpos _)) (hu _ (hCpos _))).not_gt
  · rw [heq] at hgt
    exact lt_irrefl _ hgt

/-- **Consumption tilts down** (O&R p. 71): if `β(1 + r) < 1`, a path satisfying the Euler equation
is strictly decreasing. -/
theorem tilt_down {u u' : ℝ → ℝ} {β r : ℝ} (hconc : StrictConcaveOn ℝ (Ioi 0) u)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hβr : β * (1 + r) < 1) {C : ℕ → ℝ} (hCpos : ∀ s, 0 < C s)
    (he : ∀ s, u' (C s) = (1 + r) * β * u' (C (s + 1))) (s : ℕ) : C (s + 1) < C s := by
  have hp := hpos _ (hCpos (s + 1))
  have hlt' : u' (C s) < u' (C (s + 1)) := by rw [he s]; nlinarith
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · exact absurd hlt' (deriv_lt_of_strictConcave' hconc (mem_Ioi.2 (hCpos _))
      (mem_Ioi.2 (hCpos _)) hlt (hu _ (hCpos _)) (hu _ (hCpos _))).not_gt
  · rw [heq] at hlt'
    exact lt_irrefl _ hlt'

/-- **Flat consumption** (O&R p. 62): if `β(1 + r) = 1`, a path satisfying the Euler equation is
constant. -/
theorem flat_of_beta_mul {u u' : ℝ → ℝ} {β r : ℝ} (hconc : StrictConcaveOn ℝ (Ioi 0) u)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hβr : β * (1 + r) = 1) {C : ℕ → ℝ}
    (hCpos : ∀ s, 0 < C s) (he : ∀ s, u' (C s) = (1 + r) * β * u' (C (s + 1))) (s : ℕ) :
    C s = C 0 := by
  have step : ∀ t, C (t + 1) = C t := by
    intro t
    have heq : u' (C t) = u' (C (t + 1)) := by
      rw [he t]; linear_combination u' (C (t + 1)) * hβr
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd heq (deriv_lt_of_strictConcave' hconc (mem_Ioi.2 (hCpos _))
        (mem_Ioi.2 (hCpos _)) hlt (hu _ (hCpos _)) (hu _ (hCpos _))).ne
    · exact absurd heq (deriv_lt_of_strictConcave' hconc (mem_Ioi.2 (hCpos _))
        (mem_Ioi.2 (hCpos _)) hlt (hu _ (hCpos _)) (hu _ (hCpos _))).ne'
  induction s with
  | zero => rfl
  | succ s ih => rw [step s, ih]

/-- **Dynamic consistency**, O&R §2.1.4, p. 72: the continuation of a date-0 optimal plan is optimal
at date 1 given the wealth it leaves, `W₁ = (1 + r)(W − C₀)` (Supplement A, SA(5)). -/
theorem continuation_optimal {u : ℝ → ℝ} {β r W : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    {C : ℕ → ℝ} (hC : IsOptimal u β r W C) :
    IsOptimal u β r ((1 + r) * (W - C 0)) (fun s => C (s + 1)) := by
  obtain ⟨⟨hCpos, hCpv, hCu, hCW⟩, hmax⟩ := hC
  have hd := one_add_mul_disc hr
  have hpv_tail : Summable fun s => disc r ^ s * C (s + 1) := by
    have := (summable_nat_add_iff 1).2 hCpv
    have h2 : Summable fun s => disc r * (disc r ^ s * C (s + 1)) := by
      simpa [pow_succ, mul_comm, mul_assoc, mul_left_comm] using this
    have h3 := h2.mul_left (1 + r)
    simpa [← mul_assoc, hd] using h3
  have hu_tail : Summable fun s => β ^ s * u (C (s + 1)) := by
    have := (summable_nat_add_iff 1).2 hCu
    have h2 : Summable fun s => β * (β ^ s * u (C (s + 1))) := by
      simpa [pow_succ, mul_comm, mul_assoc, mul_left_comm] using this
    have h3 := h2.mul_left β⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ hβ.ne'] using h3
  have hsplit_pv : pv r C = C 0 + disc r * pv r (fun s => C (s + 1)) := pv_eq_head_add hCpv
  have hsplit_u : lifetimeUtility u β C =
      u (C 0) + β * lifetimeUtility u β (fun s => C (s + 1)) := by
    unfold lifetimeUtility
    rw [hCu.tsum_eq_zero_add, ← tsum_mul_left]
    simp only [pow_zero, one_mul]
    congr 1
    exact tsum_congr fun s => by rw [pow_succ]; ring
  refine ⟨⟨fun s => hCpos (s + 1), hpv_tail, hu_tail, ?_⟩, fun D hD => ?_⟩
  · have : disc r * pv r (fun s => C (s + 1)) ≤ W - C 0 := by linarith
    have h1 := mul_le_mul_of_nonneg_left this hr.le
    rwa [← mul_assoc, hd, one_mul] at h1
  · obtain ⟨hDpos, hDpv, hDu, hDW⟩ := hD
    -- prepend C₀ to D
    set E : ℕ → ℝ := fun s => Nat.casesOn s (C 0) D with hE
    have hE0 : E 0 = C 0 := rfl
    have hEs : ∀ s, E (s + 1) = D s := fun s => rfl
    have hEpv : Summable fun s => disc r ^ s * E s := by
      rw [← summable_nat_add_iff 1]
      simpa [hEs, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hDpv.mul_left (disc r)
    have hEu : Summable fun s => β ^ s * u (E s) := by
      rw [← summable_nat_add_iff 1]
      simpa [hEs, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hDu.mul_left β
    have hEpos : ∀ s, 0 < E s := fun s => by
      cases s with
      | zero => exact hCpos 0
      | succ s => exact hDpos s
    have hEsplit : pv r E = C 0 + disc r * pv r D := by
      rw [pv_eq_head_add hEpv]
      rfl
    have hEW : pv r E ≤ W := by
      rw [hEsplit]
      have h1 := mul_le_mul_of_nonneg_left hDW (disc_pos hr).le
      have : disc r * ((1 + r) * (W - C 0)) = W - C 0 := by
        rw [← mul_assoc, mul_comm (disc r), hd, one_mul]
      linarith
    have hle := hmax E ⟨hEpos, hEpv, hEu, hEW⟩
    have hEsplit_u : lifetimeUtility u β E = u (C 0) + β * lifetimeUtility u β D := by
      unfold lifetimeUtility
      rw [hEu.tsum_eq_zero_add, ← tsum_mul_left]
      simp only [pow_zero, one_mul, hE0]
      congr 1
      exact tsum_congr fun s => by rw [pow_succ, hEs]; ring
    rw [hEsplit_u, hsplit_u] at hle
    have := (mul_le_mul_iff_of_pos_left hβ).1 (by linarith : β * lifetimeUtility u β D ≤
      β * lifetimeUtility u β (fun s => C (s + 1)))
    exact this

/-- **Strotz's time inconsistency**, O&R p. 73: with quasi-hyperbolic utility
`(1 + γ) u(C_t) + Σ_{s>t} β^{s−t} u(C_s)`, the marginal rate of substitution between dates 1 and 2
is `u'(C₁)/(β u'(C₂))` as seen from date 0 but `(1 + γ) u'(C₁)/(β u'(C₂))` once date 1 arrives. The
two differ whenever `γ ≠ 0`, so the date-0 plan is not carried out. -/
theorem strotz_mrs_differ {β γ du1 du2 : ℝ} (hβ : 0 < β) (h1 : 0 < du1) (h2 : 0 < du2)
    (hγ : γ ≠ 0) : β * du1 / (β ^ 2 * du2) ≠ (1 + γ) * du1 / (β * du2) := by
  intro heq
  have hβ2 : β * du1 / (β ^ 2 * du2) = du1 / (β * du2) := by
    field_simp
  rw [hβ2, eq_div_iff (by positivity), div_mul_cancel₀ _ (by positivity)] at heq
  have : γ * du1 = 0 := by linarith
  exact hγ ((mul_eq_zero.1 this).resolve_right h1.ne')

end ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The fundamental current-account equation

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§2.1.3 and §2.2, pp. 62–78. Date 0 stands for the book's date `t`. Net output
flows `Y, G, I` are sequences from date 0 on, `B₀` is initial net foreign
assets, and lifetime wealth is `W₀ = (1 + r)B₀ + PV(Y − G − I)` (O&R (2.19)).
The current account is `CA₀ = Y₀ + rB₀ − C₀ − G₀ − I₀` (O&R (2.2)).

* With flat consumption (`β(1 + r) = 1`), the intertemporal budget constraint
  pins down `C = rW₀/(1 + r)` (O&R (2.10), p. 62). The current account is then
  `CA = (Y − Ỹ) − (I − Ĩ) − (G − G̃)` (**O&R (2.18)**, p. 74), where `X̃` is the
  permanent value of O&R (2.17): output above its permanent level is saved,
  and investment or government spending above theirs is financed by borrowing.
* If consumption grows geometrically at gross rate `γ < 1 + r` (the isoelastic
  case, `γ = (1 + r)^σ β^σ`), then `C₀ = (r + ϑ)W₀/(1 + r)` with `ϑ = 1 − γ`
  (O&R (2.16), p. 71). The current account acquires the tilt term
  `−ϑ W₀/(1 + r)` (O&R (2.20), p. 75).
* With variable interest rates and discount weights `R_s`, the same algebra
  gives O&R (2.26), p. 78.
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount

open PresentValue

/-- Lifetime wealth `W₀ = (1 + r) B₀ + PV(Y − G − I)`, O&R (2.19), p. 71. -/
noncomputable def wealth (r B0 : ℝ) (Y G I : ℕ → ℝ) : ℝ :=
  (1 + r) * B0 + pv r (fun s => Y s - G s - I s)

/-- The date-0 current account `CA₀ = Y₀ + rB₀ − C₀ − G₀ − I₀`, O&R (2.2). -/
def currentAccount (r B0 C0 : ℝ) (Y G I : ℕ → ℝ) : ℝ := Y 0 + r * B0 - C0 - G 0 - I 0

/-- **Consumption with `β(1 + r) = 1`**, O&R (2.10), p. 62: if consumption is constant at `C̄` and
the intertemporal budget constraint `PV(C) = W₀` holds, then `C̄ = r W₀/(1 + r)`. -/
theorem flat_consumption_level {r B0 Cbar : ℝ} (hr : 0 < r) {Y G I : ℕ → ℝ}
    (hibc : pv r (fun _ => Cbar) = wealth r B0 Y G I) :
    Cbar = r / (1 + r) * wealth r B0 Y G I := by
  rw [pv_const hr] at hibc
  rw [← hibc]
  have : (1 : ℝ) + r ≠ 0 := by linarith
  field_simp

/-- Consumption out of wealth equals interest on assets plus permanent net output:
`r W₀/(1 + r) = rB₀ + (Y − G − I)~`. -/
theorem annuity_wealth (r B0 : ℝ) (hr : 0 < 1 + r) (Y G I : ℕ → ℝ) :
    r / (1 + r) * wealth r B0 Y G I = r * B0 + permanent r (fun s => Y s - G s - I s) := by
  unfold wealth permanent
  field_simp

/-- **The fundamental current-account equation**, O&R (2.18), p. 74: if consumption equals the
annuity value of wealth, `C₀ = rW₀/(1 + r)`, then
`CA₀ = (Y₀ − Ỹ) − (I₀ − Ĩ) − (G₀ − G̃)`. Summability of the three flows lets the permanent value
split. -/
theorem fundamental_current_account {r B0 C0 : ℝ} (hr : 0 < r) {Y G I : ℕ → ℝ}
    (hY : Summable fun s => disc r ^ s * Y s) (hG : Summable fun s => disc r ^ s * G s)
    (hI : Summable fun s => disc r ^ s * I s) (hC : C0 = r / (1 + r) * wealth r B0 Y G I) :
    currentAccount r B0 C0 Y G I =
      (Y 0 - permanent r Y) - (I 0 - permanent r I) - (G 0 - permanent r G) := by
  have hYG : Summable fun s => disc r ^ s * (Y s - G s) := by
    simpa [mul_sub] using hY.sub hG
  have hsplit : permanent r (fun s => Y s - G s - I s) =
      permanent r Y - permanent r G - permanent r I := by
    rw [permanent_sub hYG hI, permanent_sub hY hG]
  rw [currentAccount, hC, annuity_wealth r B0 (by linarith) Y G I, hsplit]
  ring

/-- **(2.10) ⇒ (2.18)**: with constant consumption satisfying the intertemporal budget constraint,
the current account obeys the fundamental equation. -/
theorem fundamental_current_account_of_flat {r B0 Cbar : ℝ} (hr : 0 < r) {Y G I : ℕ → ℝ}
    (hY : Summable fun s => disc r ^ s * Y s) (hG : Summable fun s => disc r ^ s * G s)
    (hI : Summable fun s => disc r ^ s * I s)
    (hibc : pv r (fun _ => Cbar) = wealth r B0 Y G I) :
    currentAccount r B0 Cbar Y G I =
      (Y 0 - permanent r Y) - (I 0 - permanent r I) - (G 0 - permanent r G) :=
  fundamental_current_account hr hY hG hI (flat_consumption_level hr hibc)

/-- **A permanent shock leaves the current account unchanged** (O&R p. 75): adding a constant `c`
to output adds `c` to permanent output as well. -/
theorem permanent_shock_no_ca {r : ℝ} (hr : 0 < r) {Y : ℕ → ℝ}
    (hY : Summable fun s => disc r ^ s * Y s) (c : ℝ) :
    (Y 0 + c) - permanent r (fun s => Y s + c) = Y 0 - permanent r Y := by
  have hc : Summable fun s => disc r ^ s * c :=
    (hasSum_disc_pow hr).summable.mul_right c
  rw [permanent_add hY hc, permanent_const hr]
  ring

/-- **A temporary shock is saved** (O&R pp. 74–75): raising date-0 output alone by `d` raises
`Y₀ − Ỹ` by `d/(1 + r)`, which is positive: most of a temporary windfall goes to the current
account. -/
theorem temporary_shock_ca {r : ℝ} (hr : 0 < r) {Y : ℕ → ℝ}
    (hY : Summable fun s => disc r ^ s * Y s) (d : ℝ) :
    (Y 0 + d) - permanent r (fun s => Y s + if s = 0 then d else 0) =
      (Y 0 - permanent r Y) + d / (1 + r) := by
  have hd : Summable fun s => disc r ^ s * (if s = 0 then d else 0) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro s hs
    simp only [Finset.mem_singleton] at hs
    simp [hs]
  rw [permanent_add hY hd]
  have : permanent r (fun s => if s = 0 then d else 0) = r / (1 + r) * d := by
    unfold permanent pv
    rw [tsum_eq_single 0 (fun s hs => by simp [hs])]
    simp
  rw [this]
  have : (1 : ℝ) + r ≠ 0 := by linarith
  field_simp
  ring

/-! ### Tilted consumption (O&R (2.16), (2.20)) -/

/-- **Consumption with geometric growth**, O&R (2.16), p. 71: if `C_s = γ^s C₀` with
`0 ≤ γ < 1 + r` and `PV(C) = W₀`, then `C₀ = (1 + r − γ) W₀/(1 + r)`. In the isoelastic case
`γ = (1 + r)^σ β^σ`, this is `C₀ = (r + ϑ)W₀/(1 + r)` with `ϑ = 1 − γ`. -/
theorem geometric_consumption_level {r γ C0 W : ℝ} (hr : 0 < 1 + r) (hγ : 0 ≤ γ)
    (hγr : γ < 1 + r) (hibc : pv r (fun s => γ ^ s * C0) = W) :
    C0 = (1 + r - γ) / (1 + r) * W := by
  have hq0 : 0 ≤ γ / (1 + r) := div_nonneg hγ hr.le
  have hq1 : γ / (1 + r) < 1 := (div_lt_one hr).2 hγr
  unfold pv at hibc
  have e : ∀ s : ℕ, disc r ^ s * (γ ^ s * C0) = (γ / (1 + r)) ^ s * C0 := by
    intro s
    unfold disc
    rw [div_pow, inv_pow]
    ring
  simp_rw [e] at hibc
  rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1] at hibc
  rw [← hibc]
  have h1 : (1 : ℝ) + r ≠ 0 := hr.ne'
  have h2 : (1 + r - γ) ≠ 0 := by linarith
  have e2 : 1 - γ / (1 + r) = (1 + r - γ) / (1 + r) := by field_simp
  rw [e2, inv_div]
  field_simp

/-- **The tilted fundamental equation**, O&R (2.20), p. 75: if `C₀ = (r + ϑ)W₀/(1 + r)` then
`CA₀ = (Y₀ − Ỹ) − (I₀ − Ĩ) − (G₀ − G̃) − ϑ W₀/(1 + r)`. -/
theorem tilted_current_account {r ϑ B0 C0 : ℝ} (hr : 0 < r) {Y G I : ℕ → ℝ}
    (hY : Summable fun s => disc r ^ s * Y s) (hG : Summable fun s => disc r ^ s * G s)
    (hI : Summable fun s => disc r ^ s * I s)
    (hC : C0 = (r + ϑ) / (1 + r) * wealth r B0 Y G I) :
    currentAccount r B0 C0 Y G I =
      (Y 0 - permanent r Y) - (I 0 - permanent r I) - (G 0 - permanent r G) -
        ϑ * wealth r B0 Y G I / (1 + r) := by
  have h0 := fundamental_current_account hr hY hG hI (C0 := r / (1 + r) * wealth r B0 Y G I) rfl
  have e : currentAccount r B0 C0 Y G I = currentAccount r B0 (r / (1 + r) * wealth r B0 Y G I)
      Y G I - ϑ * wealth r B0 Y G I / (1 + r) := by
    unfold currentAccount
    rw [hC]
    ring
  rw [e, h0]

/-- **(2.16) ⇒ (2.20)**: with consumption growing at gross rate `γ = 1 − ϑ < 1 + r` and satisfying
the intertemporal budget constraint, the current account obeys the tilted equation. -/
theorem tilted_current_account_of_growth {r γ B0 C0 : ℝ} (hr : 0 < r) (hγ : 0 ≤ γ)
    (hγr : γ < 1 + r) {Y G I : ℕ → ℝ}
    (hY : Summable fun s => disc r ^ s * Y s) (hG : Summable fun s => disc r ^ s * G s)
    (hI : Summable fun s => disc r ^ s * I s)
    (hibc : pv r (fun s => γ ^ s * C0) = wealth r B0 Y G I) :
    currentAccount r B0 C0 Y G I =
      (Y 0 - permanent r Y) - (I 0 - permanent r I) - (G 0 - permanent r G) -
        (1 - γ) * wealth r B0 Y G I / (1 + r) := by
  refine tilted_current_account hr hY hG hI ?_
  rw [geometric_consumption_level (by linarith) hγ hγr hibc]
  ring_nf

/-- Rising consumption (`γ > 1`, i.e. `ϑ < 0`) lowers saving relative to the flat case when wealth
is positive: the tilt term `−ϑW₀/(1 + r)` is negative iff `ϑ > 0`. -/
theorem tilt_term_neg_iff {r ϑ W : ℝ} (hr : 0 < 1 + r) (hW : 0 < W) :
    -(ϑ * W / (1 + r)) < 0 ↔ 0 < ϑ := by
  rw [neg_lt_zero, div_pos_iff_of_pos_right hr]
  exact ⟨fun h => pos_of_mul_pos_left h hW.le, fun h => mul_pos h hW⟩

/-! ### Variable interest rates (O&R (2.25)–(2.26), pp. 77–78) -/

/-- **The fundamental equation with variable interest rates**, O&R (2.26), p. 78. Discount weights
`R_s` (with `R₀ = 1`), their sum `S`, weighted means `Ñ = Σ R_s N_s / S` of net output
`N = Y − G − I` and `Γ̃ = Σ R_s g_s / S` of consumption growth factors `g_s = C_s/C₀`, and
`r̃ = (1 + r₀)/S`. If `C_s = g_s C₀` satisfies the budget constraint
`Σ R_s C_s = (1 + r₀)B₀ + Σ R_s N_s`, then
`CA₀ = (r₀ − r̃)B₀ + (N₀ − Ñ) + ((Γ̃ − 1)/Γ̃)(r̃ B₀ + Ñ)`. -/
theorem variable_rate_current_account {r0 B0 C0 S SN SG N0 : ℝ} (hS : 0 < S) (hSG : 0 < SG)
    (hibc : C0 * SG = (1 + r0) * B0 + SN) :
    r0 * B0 + N0 - C0 =
      (r0 - (1 + r0) / S) * B0 + (N0 - SN / S) +
        ((SG / S - 1) / (SG / S)) * ((1 + r0) / S * B0 + SN / S) := by
  have hC : C0 = ((1 + r0) * B0 + SN) / SG := by
    field_simp
    linarith
  rw [hC]
  field_simp
  ring

/-- With constant consumption (`g_s = 1`, so `Γ̃ = 1`) the variable-rate equation reduces to
`CA₀ = (r₀ − r̃)B₀ + (N₀ − Ñ)` (O&R footnote 14, `σ = 0`). -/
theorem variable_rate_current_account_flat {r0 B0 C0 S SN N0 : ℝ} (hS : 0 < S)
    (hibc : C0 * S = (1 + r0) * B0 + SN) :
    r0 * B0 + N0 - C0 = (r0 - (1 + r0) / S) * B0 + (N0 - SN / S) := by
  have := variable_rate_current_account (N0 := N0) hS hS hibc
  rw [this, div_self hS.ne', sub_self, zero_div, zero_mul, add_zero]

end ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Consumption functions

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §2.1 (pp. 60–73),
§2.5.3 (pp. 114–116), Chapter 2 Exercise 2 (p. 125) and Supplement A.2 to Chapter 2
(pp. 718–721). Date 0 stands for the book's date `t`.

* **Finite horizon** (O&R (2.9), p. 62): with `β(1 + r) = 1` the constant consumption level that
  exhausts the budget over `T + 1` dates, and its limit (2.10) as `T → ∞`.
* **Annuity value** (footnote 2, p. 62): `C = rW/(1 + r)` is the only rule that keeps wealth
  constant under `W_{t+1} = (1 + r)(W_t − C_t)`.
* **Isoelastic utility** (O&R (2.15)–(2.16), pp. 70–71): derivative and strict concavity of
  `C^{1−1/σ}/(1 − 1/σ)` via `Real.rpow`; the Euler equation is equivalent to the growth rule
  `C_{s+1} = (1 + r)^σβ^σ C_s`; the consumption function
  `C = [1 − (1 + r)^{σ−1}β^σ]W = (r + ϑ)W/(1 + r)`; the Euler path is **optimal** (via
  `isOptimal_of_euler`) when `(1 + r)^{σ−1}β^σ < 1`, and **no optimum exists** when
  `(1 + r)^{σ−1}β^σ ≥ 1` (footnote 8), which requires `σ > 1`; consumption falls with `β`.
  The logarithmic case `σ = 1` is proved separately.
* **Dynamic programming** (Supplement A.2): `J(W) = Θ W^{1−1/σ}/(1 − 1/σ)` satisfies the Bellman
  equation, the maximum being attained uniquely at `C = [1 − β^σ(1 + r)^{σ−1}]W`. This is the
  fixed-point identity only; that `J` is the true value function is not claimed.
* **Endogenous labour** (§2.5.3): the partial derivatives of
  `[C^γ(L̄ − L)^{1−γ}]^{1−1/σ}/(1 − 1/σ)`, the leisure rule `L̄ − L = (1 − γ)C/(γw)`, the
  consumption-growth equation, and the upward tilt under rising wages when `σ < 1`, even with
  `β(1 + r) = 1`.
* **Uncertain lifetimes** (Exercise 2): `Σ_T φ^T(1 − φ)Σ_{s≤T} β^s u(C_s) = Σ_s (φβ)^s u(C_s)`,
  by an honest interchange of summation under absolute summability.
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions

open PresentValue FundamentalCurrentAccount ConsumptionOptimality Filter Topology Set Finset

/-! ### Finite horizon with `β(1 + r) = 1` (O&R (2.8)–(2.10)) -/

/-- **Finite-horizon consumption**, O&R (2.9), p. 62: a constant consumption level `C̄` that
satisfies the finite-horizon budget constraint (2.8) over dates `0, …, T`, with net output
`N = Y − G − I`, is `C̄ = [1/(1 − (1 + r)^{-(T+1)})] (r/(1 + r)) [(1 + r)B₀ + Σ (1 + r)^{-s} N_s]`.
Here `disc r ^ (T + 1) = (1 + r)^{-(T+1)}`. -/
theorem finite_horizon_consumption {r B0 Cbar : ℝ} (hr : 0 < r) (N : ℕ → ℝ) (T : ℕ)
    (hibc : ∑ s ∈ range (T + 1), disc r ^ s * Cbar =
      (1 + r) * B0 + ∑ s ∈ range (T + 1), disc r ^ s * N s) :
    Cbar = 1 / (1 - disc r ^ (T + 1)) * (r / (1 + r)) *
      ((1 + r) * B0 + ∑ s ∈ range (T + 1), disc r ^ s * N s) := by
  rw [← Finset.sum_mul, sum_range_disc_pow hr] at hibc
  rw [← hibc]
  have h1 : disc r ^ (T + 1) < 1 := pow_lt_one₀ (disc_pos (by linarith)).le (disc_lt_one hr)
    (Nat.succ_ne_zero T)
  have h2 : 1 - disc r ^ (T + 1) ≠ 0 := by linarith
  have h3 : (1 : ℝ) + r ≠ 0 := by linarith
  field_simp

/-- **The infinite-horizon limit**, O&R (2.9) → (2.10), p. 62: if `C_T` is the constant consumption
level that exhausts the budget over dates `0, …, T`, then as `T → ∞`, `C_T → rW₀/(1 + r)`, the
annuity value of wealth. Summability of discounted net output is assumed explicitly. -/
theorem finite_horizon_tendsto {r B0 : ℝ} (hr : 0 < r) {Y G I : ℕ → ℝ}
    (hN : Summable fun s => disc r ^ s * (Y s - G s - I s)) {C : ℕ → ℝ}
    (hC : ∀ T, ∑ s ∈ range (T + 1), disc r ^ s * C T =
      (1 + r) * B0 + ∑ s ∈ range (T + 1), disc r ^ s * (Y s - G s - I s)) :
    Tendsto C atTop (𝓝 (r / (1 + r) * wealth r B0 Y G I)) := by
  have hC' : C = fun T => 1 / (1 - disc r ^ (T + 1)) * (r / (1 + r)) *
      ((1 + r) * B0 + ∑ s ∈ range (T + 1), disc r ^ s * (Y s - G s - I s)) :=
    funext fun T => finite_horizon_consumption hr _ T (hC T)
  rw [hC']
  have hd0 : 0 ≤ disc r := (disc_pos (by linarith)).le
  have hpow : Tendsto (fun T : ℕ => disc r ^ (T + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hd0 (disc_lt_one hr)).comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun T : ℕ => 1 / (1 - disc r ^ (T + 1))) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hpow).inv₀ (by norm_num)
    simpa using this
  have hsum : Tendsto (fun T : ℕ => ∑ s ∈ range (T + 1), disc r ^ s * (Y s - G s - I s)) atTop
      (𝓝 (pv r fun s => Y s - G s - I s)) :=
    hN.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have := (hinv.mul_const (r / (1 + r))).mul ((tendsto_const_nhds (x := (1 + r) * B0)).add hsum)
  simpa [wealth] using this

/-! ### Annuity value keeps wealth constant (O&R footnote 2, p. 62) -/

/-- **Only the annuity rule keeps wealth unchanged**, O&R footnote 2, p. 62: with the wealth
transition `W_{t+1} = (1 + r)(W_t − C_t)` (Supplement A, SA(5)), next period's wealth equals
current wealth if and only if `C_t = rW_t/(1 + r)`. -/
theorem wealth_unchanged_iff {r W C : ℝ} (hr : 0 < 1 + r) :
    (1 + r) * (W - C) = W ↔ C = r / (1 + r) * W := by
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- **The annuity rule keeps wealth constant forever**, O&R footnote 2, p. 62: if
`W_{t+1} = (1 + r)(W_t − C_t)` and `C_t = rW_t/(1 + r)` at every date, then `W_t = W₀`. -/
theorem annuity_wealth_constant {r : ℝ} (hr : 0 < 1 + r) {W C : ℕ → ℝ}
    (hlaw : ∀ t, W (t + 1) = (1 + r) * (W t - C t)) (hC : ∀ t, C t = r / (1 + r) * W t)
    (t : ℕ) : W t = W 0 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [hlaw t, (wealth_unchanged_iff hr).2 (hC t), ih]

/-! ### Isoelastic (CRRA) utility (O&R (2.15)–(2.16), p. 70–71) -/

/-- Isoelastic period utility `u(C) = C^{1−1/σ}/(1 − 1/σ)`, O&R p. 70 (for `σ ≠ 1`). -/
noncomputable def crra (σ c : ℝ) : ℝ := c ^ (1 - σ⁻¹) / (1 - σ⁻¹)

/-- Marginal utility of the isoelastic utility, `u'(C) = C^{−1/σ}`, O&R p. 70. -/
noncomputable def crraMU (σ c : ℝ) : ℝ := c ^ (-σ⁻¹)

/-- Gross consumption growth `(1 + r)^σ β^σ` along the isoelastic Euler path, O&R (2.15). -/
noncomputable def crraGrowth (σ r β : ℝ) : ℝ := (1 + r) ^ σ * β ^ σ

/-- The ratio `(1 + r)^{σ−1} β^σ` of consumption growth to `1 + r`, O&R p. 71; it must be
below one for the consumption function (2.16) to be defined. -/
noncomputable def crraTilt (σ r β : ℝ) : ℝ := (1 + r) ^ (σ - 1) * β ^ σ

/-- The derivative of the isoelastic utility, O&R p. 70: `u'(C) = C^{−1/σ}` for `C > 0`,
`σ ≠ 1`. -/
theorem crra_hasDerivAt {σ c : ℝ} (hσ1 : σ ≠ 1) (hc : 0 < c) :
    HasDerivAt (crra σ) (crraMU σ c) c := by
  have hp : 1 - σ⁻¹ ≠ 0 := by
    intro h
    have : σ⁻¹ = 1 := by linarith
    exact hσ1 (by simpa using congrArg (·⁻¹) this)
  have h := (Real.hasDerivAt_rpow_const (p := 1 - σ⁻¹) (Or.inl hc.ne')).div_const (1 - σ⁻¹)
  unfold crra crraMU
  convert h using 1
  rw [mul_div_cancel_left₀ _ hp]
  ring_nf

/-- The isoelastic utility is strictly concave on `(0, ∞)` for every `σ > 0`, `σ ≠ 1`
(O&R p. 70): its derivative `C^{−1/σ}` is strictly decreasing. -/
theorem crra_strictConcaveOn {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) :
    StrictConcaveOn ℝ (Ioi 0) (crra σ) := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0)
  · intro x hx
    exact (crra_hasDerivAt hσ1 hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro x hx y hy hxy
    rw [(crra_hasDerivAt hσ1 hx).deriv, (crra_hasDerivAt hσ1 hy).deriv]
    exact Real.rpow_lt_rpow_of_neg hx hxy (by simpa using inv_pos.2 hσ)

/-- **Isoelastic Euler equation**, O&R (2.15), p. 70: for positive consumption levels,
`u'(C_s) = (1 + r)β u'(C_{s+1})` holds if and only if `C_{s+1} = (1 + r)^σ β^σ C_s`. -/
theorem crra_euler_iff {σ r β c c' : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hc : 0 < c) (hc' : 0 < c') :
    crraMU σ c = (1 + r) * β * crraMU σ c' ↔ c' = crraGrowth σ r β * c := by
  unfold crraMU crraGrowth
  have hg : 0 < (1 + r) ^ σ * β ^ σ * c := by positivity
  have hσ' : σ ≠ 0 := hσ.ne'
  constructor
  · intro h
    have hl := congrArg Real.log h
    rw [Real.log_rpow hc, Real.log_mul (by positivity) (by positivity), Real.log_rpow hc',
      Real.log_mul hr.ne' hβ.ne'] at hl
    apply Real.log_injOn_pos (mem_Ioi.2 hc') (mem_Ioi.2 hg)
    rw [Real.log_mul (by positivity) hc.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hr, Real.log_rpow hβ]
    field_simp at hl
    linarith
  · intro h
    apply Real.log_injOn_pos (mem_Ioi.2 (by positivity)) (mem_Ioi.2 (by positivity))
    rw [Real.log_rpow hc, Real.log_mul (by positivity) (by positivity), Real.log_rpow hc',
      Real.log_mul hr.ne' hβ.ne', h, Real.log_mul (by positivity) hc.ne',
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hr, Real.log_rpow hβ]
    field_simp
    ring

/-- The isoelastic Euler path is geometric, O&R (2.15), p. 70: a positive path satisfies the Euler
equation at every date if and only if `C_s = ((1 + r)^σ β^σ)^s C₀`. -/
theorem crra_euler_path_iff {σ r β : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    {C : ℕ → ℝ} (hC : ∀ s, 0 < C s) :
    (∀ s, crraMU σ (C s) = (1 + r) * β * crraMU σ (C (s + 1))) ↔
      ∀ s, C s = crraGrowth σ r β ^ s * C 0 := by
  constructor
  · intro h s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [(crra_euler_iff hσ hr hβ (hC s) (hC (s + 1))).1 (h s), ih, pow_succ]
      ring
  · intro h s
    refine (crra_euler_iff hσ hr hβ (hC s) (hC (s + 1))).2 ?_
    rw [h (s + 1), h s, pow_succ]
    ring

/-- Consumption growth over `1 + r`: `(1 + r)^σ β^σ = (1 + r) · (1 + r)^{σ−1} β^σ`. -/
theorem crraGrowth_eq {σ r β : ℝ} (hr : 0 < 1 + r) :
    crraGrowth σ r β = (1 + r) * crraTilt σ r β := by
  unfold crraGrowth crraTilt
  rw [Real.rpow_sub_one hr.ne']
  field_simp

/-- **The isoelastic consumption function**, O&R (2.16), p. 71: if consumption follows the Euler
path `C_s = ((1 + r)^σ β^σ)^s C₀`, `(1 + r)^{σ−1}β^σ < 1` and the budget constraint
`PV(C) = W₀` holds, then `C₀ = [1 − (1 + r)^{σ−1}β^σ] W₀ = (r + ϑ)W₀/(1 + r)` with
`ϑ = 1 − (1 + r)^σ β^σ`. Derived from `geometric_consumption_level`. -/
theorem crra_consumption_function {σ r β C0 W : ℝ} (hr : 0 < 1 + r) (hβ : 0 ≤ β)
    (htilt : crraTilt σ r β < 1) (hibc : pv r (fun s => crraGrowth σ r β ^ s * C0) = W) :
    C0 = (1 - crraTilt σ r β) * W ∧ C0 = (r + (1 - crraGrowth σ r β)) / (1 + r) * W := by
  have hγ0 : 0 ≤ crraGrowth σ r β :=
    mul_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hβ _)
  have hγr : crraGrowth σ r β < 1 + r := by
    rw [crraGrowth_eq hr]
    nlinarith
  have h := geometric_consumption_level hr hγ0 hγr hibc
  refine ⟨?_, ?_⟩
  · rw [h, crraGrowth_eq hr]
    field_simp
  · rw [h]
    ring_nf

/-- **The isoelastic Euler path is optimal**, O&R (2.15)–(2.16), pp. 70–71: with `β > 0`,
`1 + r > 0`, `σ > 0`, `σ ≠ 1`, `(1 + r)^{σ−1}β^σ < 1` and `W₀ > 0`, the path
`C_s = ((1 + r)^σ β^σ)^s [1 − (1 + r)^{σ−1}β^σ] W₀` is optimal among all admissible paths.
Its lifetime utility is summable because `β u(C_{s+1})/u(C_s)`-ratios equal
`β((1 + r)^σβ^σ)^{1−1/σ} = (1 + r)^{σ−1}β^σ < 1`; the proof applies `isOptimal_of_euler`. -/
theorem crra_isOptimal {σ r β W : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hr : 0 < 1 + r) (hβ : 0 < β)
    (htilt : crraTilt σ r β < 1) (hW : 0 < W) :
    IsOptimal (crra σ) β r W (fun s => crraGrowth σ r β ^ s * ((1 - crraTilt σ r β) * W)) := by
  set γ := crraGrowth σ r β with hγdef
  set κ := crraTilt σ r β with hκdef
  set C0 := (1 - κ) * W with hC0
  have hγ : 0 < γ := mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hβ _)
  have hκpos : 0 < κ := mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hβ _)
  have hκ0 : 0 ≤ κ := hκpos.le
  have hC0pos : 0 < C0 := mul_pos (by linarith) hW
  have hd : ∀ s : ℕ, disc r ^ s * (γ ^ s * C0) = κ ^ s * C0 := by
    intro s
    have hγeq : γ = (1 + r) * κ := crraGrowth_eq hr
    have h1 := one_add_mul_disc hr
    calc disc r ^ s * (γ ^ s * C0) = ((1 + r) * disc r) ^ s * κ ^ s * C0 := by
          rw [hγeq, mul_pow, mul_pow]; ring
      _ = κ ^ s * C0 := by rw [h1, one_pow, one_mul]
  -- utility along the path is geometric with ratio `κ`
  have hβγ : β * γ ^ (1 - σ⁻¹) = κ := by
    apply Real.log_injOn_pos (mem_Ioi.2 (mul_pos hβ (Real.rpow_pos_of_pos hγ _)))
      (mem_Ioi.2 hκpos)
    rw [hγdef, hκdef]
    unfold crraGrowth crraTilt
    rw [Real.log_mul hβ.ne' (by positivity), Real.log_rpow (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hr, Real.log_rpow hβ,
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hr, Real.log_rpow hβ]
    field_simp
    ring
  have hu : ∀ s : ℕ, β ^ s * crra σ (γ ^ s * C0) = κ ^ s * (C0 ^ (1 - σ⁻¹) / (1 - σ⁻¹)) := by
    intro s
    have hpow : (γ ^ s) ^ (1 - σ⁻¹) = (γ ^ (1 - σ⁻¹)) ^ s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hγ.le, mul_comm, Real.rpow_mul hγ.le,
        Real.rpow_natCast]
    unfold crra
    rw [Real.mul_rpow (pow_nonneg hγ.le s) hC0pos.le, hpow, ← hβγ, mul_pow]
    ring
  have hpv : Summable fun s => disc r ^ s * (γ ^ s * C0) := by
    simp_rw [hd]
    exact (summable_geometric_of_lt_one hκ0 htilt).mul_right _
  refine isOptimal_of_euler (u' := crraMU σ) hβ hr (crra_strictConcaveOn hσ hσ1).concaveOn
    (fun c hc => crra_hasDerivAt hσ1 hc) ⟨fun s => by positivity, hpv, ?_, ?_⟩ ?_ ?_ ?_
  · simp_rw [hu]
    exact (summable_geometric_of_lt_one hκ0 htilt).mul_right _
  · exact le_of_eq (by
      unfold pv
      simp_rw [hd]
      rw [tsum_mul_right, tsum_geometric_of_lt_one hκ0 htilt, hC0]
      field_simp [show (1 : ℝ) - κ ≠ 0 by linarith])
  · unfold pv
    simp_rw [hd]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hκ0 htilt, hC0]
    field_simp [show (1 : ℝ) - κ ≠ 0 by linarith]
  · exact Real.rpow_nonneg (by positivity) _
  · exact (crra_euler_path_iff hσ hr hβ (fun s => by positivity)).2 fun s => by
      simp only [pow_zero, one_mul, hγdef]

/-- **No optimum when `(1 + r)^{σ−1}β^σ ≥ 1`**, O&R p. 71 and footnote 8: then no admissible path
is optimal, for any wealth. An optimum would satisfy the Euler equation, so
`C_s = ((1 + r)^σβ^σ)^s C₀`, and its discounted terms `((1 + r)^{σ−1}β^σ)^s C₀ ≥ C₀ > 0` would not
be summable: "it is always possible to do a little better". -/
theorem crra_no_optimum {σ r β W : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hr : 0 < 1 + r) (hβ : 0 < β)
    (htilt : 1 ≤ crraTilt σ r β) (C : ℕ → ℝ) : ¬ IsOptimal (crra σ) β r W C := by
  intro hopt
  have he := euler_of_optimal (u' := crraMU σ) hβ hr (fun c hc => crra_hasDerivAt hσ1 hc) hopt
  obtain ⟨⟨hCpos, hCpv, -, -⟩, -⟩ := hopt
  have hpath := (crra_euler_path_iff hσ hr hβ hCpos).1 he
  have hge : ∀ s : ℕ, C 0 ≤ disc r ^ s * C s := by
    intro s
    have h1 := one_add_mul_disc hr
    have e : disc r ^ s * C s = crraTilt σ r β ^ s * C 0 := by
      calc disc r ^ s * C s = ((1 + r) * disc r) ^ s * crraTilt σ r β ^ s * C 0 := by
            rw [hpath s, crraGrowth_eq hr, mul_pow, mul_pow]; ring
        _ = crraTilt σ r β ^ s * C 0 := by rw [h1, one_pow, one_mul]
    rw [e]
    exact le_mul_of_one_le_left (hCpos 0).le (one_le_pow₀ htilt)
  have ht := hCpv.tendsto_atTop_zero
  have := ge_of_tendsto ht (Eventually.of_forall hge)
  linarith [hCpos 0]

/-- **O&R footnote 8, p. 71**: with `0 < β < 1`, `r > 0` and `σ > 0`, the inequality
`(1 + r)^{σ−1}β^σ ≥ 1` (in particular the book's `> 1`) is possible only if `σ > 1`. -/
theorem one_lt_sigma_of_one_le_tilt {σ r β : ℝ} (hσ : 0 < σ) (hr : 0 < r) (hβ0 : 0 < β)
    (hβ1 : β < 1) (htilt : 1 ≤ crraTilt σ r β) : 1 < σ := by
  by_contra h
  push Not at h
  have h1 : (1 + r) ^ (σ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
    (by linarith)
  have h2 : β ^ σ < 1 := Real.rpow_lt_one hβ0.le hβ1 hσ
  have h3 : 0 ≤ (1 + r) ^ (σ - 1) := Real.rpow_nonneg (by linarith) _
  unfold crraTilt at htilt
  nlinarith [Real.rpow_nonneg hβ0.le σ]

/-- **Consumption falls with patience**, O&R p. 71: given `r` (and hence wealth `W₀ > 0`),
isoelastic consumption `C₀ = [1 − (1 + r)^{σ−1}β^σ] W₀` is strictly decreasing in `β > 0`. -/
theorem crra_consumption_strictAnti_beta {σ r W : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hW : 0 < W) : StrictAntiOn (fun β => (1 - crraTilt σ r β) * W) (Ioi 0) := by
  intro β1 hβ1 β2 _ h12
  have h := Real.rpow_lt_rpow (le_of_lt hβ1) h12 hσ
  have hp : 0 < (1 + r) ^ (σ - 1) := Real.rpow_pos_of_pos hr _
  simp only [crraTilt]
  nlinarith [mul_lt_mul_of_pos_left h hp]

/-- **The logarithmic case `σ = 1`**, O&R pp. 63 and 70–71: with `u = log`, `0 < β < 1` and
`W₀ > 0`, the path `C_s = ((1 + r)β)^s (1 − β) W₀` is optimal. This is the limit `σ → 1` of
(2.16): consumption is the fraction `1 − β` of wealth, whatever `r`. -/
theorem log_isOptimal {r β W : ℝ} (hr : 0 < 1 + r) (hβ0 : 0 < β) (hβ1 : β < 1) (hW : 0 < W) :
    IsOptimal Real.log β r W (fun s => ((1 + r) * β) ^ s * ((1 - β) * W)) := by
  set C0 := (1 - β) * W with hC0
  have hC0pos : 0 < C0 := mul_pos (by linarith) hW
  have hk : 0 < (1 + r) * β := mul_pos hr hβ0
  have hd : ∀ s : ℕ, disc r ^ s * (((1 + r) * β) ^ s * C0) = β ^ s * C0 := by
    intro s
    have h1 := one_add_mul_disc hr
    calc disc r ^ s * (((1 + r) * β) ^ s * C0) = ((1 + r) * disc r) ^ s * β ^ s * C0 := by
          rw [mul_pow, mul_pow]; ring
      _ = β ^ s * C0 := by rw [h1, one_pow, one_mul]
  have hu : ∀ s : ℕ, β ^ s * Real.log (((1 + r) * β) ^ s * C0) =
      Real.log ((1 + r) * β) * ((s : ℝ) ^ 1 * β ^ s) + Real.log C0 * β ^ s := by
    intro s
    rw [Real.log_mul (pow_pos hk s).ne' hC0pos.ne', Real.log_pow]
    ring
  have hg := summable_geometric_of_lt_one hβ0.le hβ1
  have hpv : Summable fun s => disc r ^ s * (((1 + r) * β) ^ s * C0) := by
    simp_rw [hd]
    exact hg.mul_right _
  have hpveq : pv r (fun s => ((1 + r) * β) ^ s * C0) = W := by
    unfold pv
    simp_rw [hd]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0.le hβ1, hC0]
    field_simp [show (1 : ℝ) - β ≠ 0 by linarith]
  refine isOptimal_of_euler (u' := fun c => c⁻¹) hβ0 hr strictConcaveOn_log_Ioi.concaveOn
    (fun c hc => Real.hasDerivAt_log hc.ne') ⟨fun s => by positivity, hpv, ?_, hpveq.le⟩ hpveq
    (by positivity) ?_
  · simp_rw [hu]
    have hnorm : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
    have hn : Summable fun n : ℕ => (n : ℝ) ^ 1 * β ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
    exact (hn.mul_left _).add (hg.mul_left _)
  · intro s
    rw [pow_succ]
    field_simp

/-! ### Dynamic programming: the isoelastic value function (Supplement A.2, pp. 718–721) -/

/-- Discounted utility of consumption growth: `β((1 + r)^σβ^σ)^{1−1/σ} = (1 + r)^{σ−1}β^σ`
(Supplement A.2, p. 721, and O&R p. 71). -/
theorem beta_mul_crraGrowth_rpow {σ r β : ℝ} (hσ : σ ≠ 0) (hr : 0 < 1 + r) (hβ : 0 < β) :
    β * crraGrowth σ r β ^ (1 - σ⁻¹) = crraTilt σ r β := by
  unfold crraGrowth crraTilt
  apply Real.log_injOn_pos (mem_Ioi.2 (by positivity)) (mem_Ioi.2 (by positivity))
  rw [Real.log_mul hβ.ne' (by positivity), Real.log_rpow (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hr, Real.log_rpow hβ,
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hr, Real.log_rpow hβ]
  field_simp
  ring

/-- The marginal-utility counterpart: `(1 + r)β((1 + r)^σβ^σ)^{−1/σ} = 1`. -/
theorem crraGrowth_rpow_neg_inv {σ r β : ℝ} (hσ : σ ≠ 0) (hr : 0 < 1 + r) (hβ : 0 < β) :
    (1 + r) * β * crraGrowth σ r β ^ (-σ⁻¹) = 1 := by
  unfold crraGrowth
  apply Real.log_injOn_pos (mem_Ioi.2 (by positivity)) (mem_Ioi.2 one_pos)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hr.ne' hβ.ne',
    Real.log_rpow (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hr, Real.log_rpow hβ, Real.log_one]
  field_simp
  ring

/-- The coefficient `Θ = [1 − β^σ(1 + r)^{σ−1}]^{−1/σ}` of the isoelastic value function,
Supplement A.2, p. 721. -/
noncomputable def crraTheta (σ r β : ℝ) : ℝ := (1 - crraTilt σ r β) ^ (-σ⁻¹)

/-- The conjectured value function `J(W) = Θ W^{1−1/σ}/(1 − 1/σ)`, Supplement A.2, p. 720. -/
noncomputable def crraValue (σ r β W : ℝ) : ℝ := crraTheta σ r β * crra σ W

/-- **The Bellman right-hand side at the policy**, Supplement A.2, SA(7) and p. 721: with
`C = [1 − β^σ(1 + r)^{σ−1}]W`, `u(C) + βJ((1 + r)(W − C)) = J(W)` for `W > 0`. -/
theorem crra_bellman_fixed_point {σ r β W : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (htilt : crraTilt σ r β < 1) (hW : 0 < W) :
    crra σ ((1 - crraTilt σ r β) * W) +
      β * crraValue σ r β ((1 + r) * (W - (1 - crraTilt σ r β) * W)) = crraValue σ r β W := by
  set κ := 1 - crraTilt σ r β with hκ
  have hκpos : 0 < κ := by linarith
  have hγ : 0 < crraGrowth σ r β :=
    mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hβ _)
  have hD : (1 + r) * (W - κ * W) = crraGrowth σ r β * W := by
    rw [crraGrowth_eq hr, hκ]; ring
  have hκp : κ ^ (1 - σ⁻¹) = κ * crraTheta σ r β := by
    unfold crraTheta
    rw [← hκ, sub_eq_add_neg, Real.rpow_add hκpos, Real.rpow_one]
  have hb := beta_mul_crraGrowth_rpow hσ.ne' hr hβ
  unfold crraValue crra
  rw [hD, Real.mul_rpow hκpos.le hW.le, Real.mul_rpow hγ.le hW.le, hκp]
  have e : β * (crraTheta σ r β * (crraGrowth σ r β ^ (1 - σ⁻¹) * W ^ (1 - σ⁻¹) / (1 - σ⁻¹)))
      = crraTheta σ r β * (β * crraGrowth σ r β ^ (1 - σ⁻¹)) * (W ^ (1 - σ⁻¹) / (1 - σ⁻¹)) := by
    ring
  rw [e, hb]
  have e2 : crraTilt σ r β = 1 - κ := by rw [hκ]; ring
  rw [e2]
  ring

/-- **The policy strictly maximises the Bellman right-hand side**, Supplement A.2, SA(6)–SA(8):
for `0 < C < W`, `C ≠ [1 − β^σ(1 + r)^{σ−1}]W`, `u(C) + βJ((1 + r)(W − C)) < J(W)`. The proof uses
the tangent-line inequality of the strictly concave `u` at `C*` and at `(1 + r)(W − C*)`, and the
first-order condition SA(8) `u'(C*) = (1 + r)βJ'((1 + r)(W − C*))`. -/
theorem crra_bellman_strict_max {σ r β W C : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hr : 0 < 1 + r)
    (hβ : 0 < β) (htilt : crraTilt σ r β < 1) (hW : 0 < W) (hC0 : 0 < C) (hCW : C < W)
    (hne : C ≠ (1 - crraTilt σ r β) * W) :
    crra σ C + β * crraValue σ r β ((1 + r) * (W - C)) < crraValue σ r β W := by
  rw [← crra_bellman_fixed_point hσ hr hβ htilt hW]
  set κ := 1 - crraTilt σ r β with hκ
  set γ := crraGrowth σ r β with hγdef
  set Θ := crraTheta σ r β with hΘ
  have hκpos : 0 < κ := by linarith
  have hγ : 0 < γ := mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hβ _)
  have hΘpos : 0 < Θ := Real.rpow_pos_of_pos hκpos _
  have hCs : 0 < κ * W := mul_pos hκpos hW
  have hDs : (1 + r) * (W - κ * W) = γ * W := by
    rw [hγdef, crraGrowth_eq hr, hκ]; ring
  have hDspos : 0 < γ * W := mul_pos hγ hW
  have hDpos : 0 < (1 + r) * (W - C) := mul_pos hr (by linarith)
  have hconc := crra_strictConcaveOn hσ hσ1
  have t1 := strictConcave_lt_tangent hconc (mem_Ioi.2 hCs) (mem_Ioi.2 hC0) hne
    (crra_hasDerivAt hσ1 hCs)
  have t2 := concave_le_tangent' hconc.concaveOn (mem_Ioi.2 hDspos) (mem_Ioi.2 hDpos)
    (crra_hasDerivAt hσ1 hDspos)
  -- the first-order condition SA(8)
  have hfoc : crraMU σ (κ * W) = (1 + r) * β * Θ * crraMU σ (γ * W) := by
    unfold crraMU
    rw [Real.mul_rpow hκpos.le hW.le, Real.mul_rpow hγ.le hW.le]
    have h := crraGrowth_rpow_neg_inv hσ.ne' hr hβ
    rw [← hγdef] at h
    calc κ ^ (-σ⁻¹) * W ^ (-σ⁻¹) = Θ * W ^ (-σ⁻¹) := by rw [hΘ]; rfl
      _ = (1 + r) * β * γ ^ (-σ⁻¹) * Θ * W ^ (-σ⁻¹) := by rw [h, one_mul]
      _ = _ := by ring
  unfold crraValue
  rw [← hΘ, hDs]
  have t2' := mul_le_mul_of_nonneg_left t2 (mul_pos hβ hΘpos).le
  have key : crraMU σ (κ * W) * (C - κ * W) +
      β * Θ * (crraMU σ (γ * W) * ((1 + r) * (W - C) - γ * W)) = 0 := by
    rw [hfoc, ← hDs]; ring
  linarith

/-- **The isoelastic value function solves the Bellman equation**, Supplement A.2, SA(6)–SA(7),
p. 721: for `W > 0`, `J(W) = max_{0<C<W} {u(C) + βJ((1 + r)(W − C))}`, the maximum being attained
(uniquely, by `crra_bellman_strict_max`) at `C = [1 − β^σ(1 + r)^{σ−1}]W`. This is the fixed-point
identity only: that `J` is the true value function needs a separate verification argument. -/
theorem crra_bellman_isGreatest {σ r β W : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hr : 0 < 1 + r)
    (hβ : 0 < β) (htilt : crraTilt σ r β < 1) (hW : 0 < W) :
    IsGreatest {v | ∃ C, 0 < C ∧ C < W ∧ v = crra σ C + β * crraValue σ r β ((1 + r) * (W - C))}
      (crraValue σ r β W) := by
  have hκ0 : 0 < crraTilt σ r β :=
    mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hβ _)
  refine ⟨⟨(1 - crraTilt σ r β) * W, mul_pos (by linarith) hW, by nlinarith,
    (crra_bellman_fixed_point hσ hr hβ htilt hW).symm⟩, ?_⟩
  rintro v ⟨C, hC0, hCW, rfl⟩
  by_cases hne : C = (1 - crraTilt σ r β) * W
  · rw [hne, crra_bellman_fixed_point hσ hr hβ htilt hW]
  · exact (crra_bellman_strict_max hσ hσ1 hr hβ htilt hW hC0 hCW hne).le

/-- The book's form of the policy, Supplement A.2, SA(10): with `Θ` as above,
`W/(1 + β^σ(1 + r)^{σ−1}Θ^σ) = [1 − β^σ(1 + r)^{σ−1}]W`. -/
theorem crra_policy_formula {σ r β W : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (htilt : crraTilt σ r β < 1) :
    W / (1 + crraTilt σ r β * crraTheta σ r β ^ σ) = (1 - crraTilt σ r β) * W := by
  have hκpos : 0 < 1 - crraTilt σ r β := by linarith
  have hΘ : crraTheta σ r β ^ σ = (1 - crraTilt σ r β)⁻¹ := by
    unfold crraTheta
    rw [← Real.rpow_mul hκpos.le, neg_mul, inv_mul_cancel₀ hσ.ne', Real.rpow_neg_one]
  have hκ0 : 0 < crraTilt σ r β :=
    mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hβ _)
  rw [hΘ]
  field_simp
  ring

/-! ### Endogenous labour supply (O&R §2.5.3, pp. 114–116) -/

/-- Isoelastic utility over consumption and leisure `ℓ = L̄ − L`,
`u(C, ℓ) = [C^γ ℓ^{1−γ}]^{1−1/σ}/(1 − 1/σ)`, O&R p. 115. -/
noncomputable def labourUtility (σ γ C ℓ : ℝ) : ℝ :=
  (C ^ γ * ℓ ^ (1 - γ)) ^ (1 - σ⁻¹) / (1 - σ⁻¹)

/-- Marginal utility of consumption `u_C = γ C^{γ(1−1/σ)−1} ℓ^{(1−γ)(1−1/σ)}`, O&R (2.72). -/
noncomputable def labourMUC (σ γ C ℓ : ℝ) : ℝ :=
  γ * C ^ (γ * (1 - σ⁻¹) - 1) * ℓ ^ ((1 - γ) * (1 - σ⁻¹))

/-- Marginal utility of leisure `u_ℓ = (1 − γ) C^{γ(1−1/σ)} ℓ^{(1−γ)(1−1/σ)−1}`, O&R (2.73). -/
noncomputable def labourMUL (σ γ C ℓ : ℝ) : ℝ :=
  (1 - γ) * C ^ (γ * (1 - σ⁻¹)) * ℓ ^ ((1 - γ) * (1 - σ⁻¹) - 1)

/-- For positive arguments the utility factorises, `u = C^{γ(1−1/σ)} ℓ^{(1−γ)(1−1/σ)}/(1 − 1/σ)`. -/
theorem labourUtility_eq {σ γ C ℓ : ℝ} (hC : 0 < C) (hℓ : 0 < ℓ) :
    labourUtility σ γ C ℓ =
      C ^ (γ * (1 - σ⁻¹)) * ℓ ^ ((1 - γ) * (1 - σ⁻¹)) / (1 - σ⁻¹) := by
  unfold labourUtility
  rw [Real.mul_rpow (Real.rpow_nonneg hC.le _) (Real.rpow_nonneg hℓ.le _),
    ← Real.rpow_mul hC.le, ← Real.rpow_mul hℓ.le]

/-- `u_C` is the partial derivative of `u` in `C`, O&R p. 115 (for `C, ℓ > 0`, `σ ≠ 1`). -/
theorem labourUtility_hasDerivAt_C {σ γ C ℓ : ℝ} (hσ1 : σ ≠ 1) (hC : 0 < C) (hℓ : 0 < ℓ) :
    HasDerivAt (fun x => labourUtility σ γ x ℓ) (labourMUC σ γ C ℓ) C := by
  have hp : 1 - σ⁻¹ ≠ 0 := by
    intro h
    have : σ⁻¹ = 1 := by linarith
    exact hσ1 (by simpa using congrArg (·⁻¹) this)
  have h := ((Real.hasDerivAt_rpow_const (p := γ * (1 - σ⁻¹)) (Or.inl hC.ne')).mul_const
    (ℓ ^ ((1 - γ) * (1 - σ⁻¹)))).div_const (1 - σ⁻¹)
  have hev : (fun x => labourUtility σ γ x ℓ) =ᶠ[𝓝 C]
      fun x => x ^ (γ * (1 - σ⁻¹)) * ℓ ^ ((1 - γ) * (1 - σ⁻¹)) / (1 - σ⁻¹) := by
    filter_upwards [lt_mem_nhds hC] with x hx
    exact labourUtility_eq hx hℓ
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  unfold labourMUC
  rw [div_eq_iff hp]
  ring

/-- `u_ℓ` is the partial derivative of `u` in leisure `ℓ`, O&R p. 115. -/
theorem labourUtility_hasDerivAt_leisure {σ γ C ℓ : ℝ} (hσ1 : σ ≠ 1) (hC : 0 < C)
    (hℓ : 0 < ℓ) : HasDerivAt (fun y => labourUtility σ γ C y) (labourMUL σ γ C ℓ) ℓ := by
  have hp : 1 - σ⁻¹ ≠ 0 := by
    intro h
    have : σ⁻¹ = 1 := by linarith
    exact hσ1 (by simpa using congrArg (·⁻¹) this)
  have h := ((Real.hasDerivAt_rpow_const (p := (1 - γ) * (1 - σ⁻¹)) (Or.inl hℓ.ne')).const_mul
    (C ^ (γ * (1 - σ⁻¹)))).div_const (1 - σ⁻¹)
  have hev : (fun y => labourUtility σ γ C y) =ᶠ[𝓝 ℓ]
      fun y => C ^ (γ * (1 - σ⁻¹)) * y ^ ((1 - γ) * (1 - σ⁻¹)) / (1 - σ⁻¹) := by
    filter_upwards [lt_mem_nhds hℓ] with y hy
    exact labourUtility_eq hC hy
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  unfold labourMUL
  rw [div_eq_iff hp]
  ring

/-- **Intratemporal first-order condition**, O&R (2.73) and p. 115: with `0 < γ < 1`, wage
`w > 0` and `C, ℓ > 0`, `u_ℓ(C, ℓ) = u_C(C, ℓ) w` holds if and only if
`L̄ − L = ℓ = (1 − γ)C/(γw)`. -/
theorem labour_intratemporal_iff {σ γ C ℓ w : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hw : 0 < w)
    (hC : 0 < C) (hℓ : 0 < ℓ) :
    labourMUL σ γ C ℓ = labourMUC σ γ C ℓ * w ↔ ℓ = (1 - γ) * C / (γ * w) := by
  have hM : 0 < labourMUC σ γ C ℓ := by unfold labourMUC; positivity
  have h1γ : (1 : ℝ) - γ ≠ 0 := by linarith
  have key : labourMUL σ γ C ℓ = labourMUC σ γ C ℓ * ((1 - γ) * C / (γ * ℓ)) := by
    unfold labourMUL labourMUC
    rw [Real.rpow_sub_one hC.ne', Real.rpow_sub_one hℓ.ne']
    field_simp
  rw [key]
  constructor
  · intro h
    have h2 := mul_left_cancel₀ hM.ne' h
    field_simp at h2 ⊢
    linarith
  · intro h
    congr 1
    rw [h]
    field_simp

/-- **Consumption growth with endogenous labour**, O&R pp. 115: combining the Euler equation
(2.72) `u_C(C_s, ℓ_s) = (1 + r)β u_C(C_{s+1}, ℓ_{s+1})` with the leisure rule
`ℓ = (1 − γ)C/(γw)` gives `C_{s+1} = (w_s/w_{s+1})^{(1−γ)(σ−1)} (1 + r)^σ β^σ C_s`. -/
theorem labour_consumption_growth {σ γ r β C0 C1 ℓ0 ℓ1 w0 w1 : ℝ} (hσ : 0 < σ) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hr : 0 < 1 + r) (hβ : 0 < β) (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hℓ0 : ℓ0 = (1 - γ) * C0 / (γ * w0))
    (hℓ1 : ℓ1 = (1 - γ) * C1 / (γ * w1))
    (heuler : labourMUC σ γ C0 ℓ0 = (1 + r) * β * labourMUC σ γ C1 ℓ1) :
    C1 = (w0 / w1) ^ ((1 - γ) * (σ - 1)) * (1 + r) ^ σ * β ^ σ * C0 := by
  have h1γ : 0 < 1 - γ := by linarith
  subst hℓ0 hℓ1
  unfold labourMUC at heuler
  have hl := congrArg Real.log heuler
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hγ0.ne' (by positivity),
    Real.log_rpow hC0, Real.log_rpow (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_mul h1γ.ne' hC0.ne', Real.log_mul hγ0.ne' hw0.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul hγ0.ne' (by positivity),
    Real.log_rpow hC1,
    Real.log_rpow (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_mul h1γ.ne' hC1.ne', Real.log_mul hγ0.ne' hw1.ne'] at hl
  apply Real.log_injOn_pos (mem_Ioi.2 hC1) (mem_Ioi.2 (by positivity))
  rw [Real.log_mul (by positivity) hC0.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity),
    Real.log_rpow hr, Real.log_rpow hβ, Real.log_div hw0.ne' hw1.ne']
  field_simp at hl
  linear_combination hl

/-- **Rising wages tilt consumption up**, O&R p. 115: if `σ < 1`, `γ < 1`, `β = 1/(1 + r)` and
the real wage rises, `w_{s+1} > w_s`, then the growth equation of `labour_consumption_growth`
gives `C_{s+1} > C_s`: a flat path is no longer optimal. -/
theorem labour_tilt_up_of_wage_growth {σ γ r β C0 C1 w0 w1 : ℝ} (hσ1 : σ < 1)
    (hγ1 : γ < 1) (hr : 0 < 1 + r) (hβ : 0 < β) (hβr : β * (1 + r) = 1)
    (hC0 : 0 < C0) (hw0 : 0 < w0) (hw : w0 < w1)
    (hgrowth : C1 = (w0 / w1) ^ ((1 - γ) * (σ - 1)) * (1 + r) ^ σ * β ^ σ * C0) :
    C0 < C1 := by
  have hk : (1 + r) ^ σ * β ^ σ = 1 := by
    rw [← Real.mul_rpow hr.le hβ.le, mul_comm, hβr, Real.one_rpow]
  have hq : 1 < (w0 / w1) ^ ((1 - γ) * (σ - 1)) :=
    Real.one_lt_rpow_of_pos_of_lt_one_of_neg (div_pos hw0 (by linarith))
      ((div_lt_one (by linarith)).2 hw) (mul_neg_of_pos_of_neg (by linarith) (by linarith))
  rw [hgrowth, mul_assoc _ ((1 + r) ^ σ), hk, mul_one]
  nlinarith

/-! ### Uncertain lifetimes (O&R Chapter 2, Exercise 2, p. 125) -/

/-- Survival weights summed over lifetimes of length `T ≥ s`:
`Σ_T [s ≤ T] φ^T (1 − φ) c = φ^s c` for `0 ≤ φ < 1` (O&R Exercise 2(b), p. 125). -/
theorem hasSum_survival_weights {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (s : ℕ) (c : ℝ) :
    HasSum (fun T => if s ≤ T then φ ^ T * (1 - φ) * c else 0) (φ ^ s * c) := by
  rw [← hasSum_nat_add_iff' s]
  have h0 : ∑ i ∈ range s, (if s ≤ i then φ ^ i * (1 - φ) * c else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [ite_eq_right (by simpa using Finset.mem_range.1 hi)]
  rw [h0, sub_zero]
  have hg := (hasSum_geometric_of_lt_one hφ0 hφ1).mul_left (φ ^ s * (1 - φ) * c)
  have hne : (1 : ℝ) - φ ≠ 0 := by linarith
  convert hg using 1
  · funext n
    rw [ite_eq_left (Nat.le_add_left s n), pow_add]
    ring
  · field_simp

/-- **Expected utility with uncertain lifetimes**, O&R Chapter 2, Exercise 2, p. 125: if the
individual survives each period with probability `0 ≤ φ < 1`, expected utility
`Σ_T φ^T(1 − φ) Σ_{s=0}^{T} a_s` equals `Σ_s φ^s a_s`, where `a_s = β^s u(C_s)`. The interchange of
the two sums is justified by the explicit absolute-summability hypothesis
`Σ φ^s |a_s| < ∞`. -/
theorem uncertain_lifetime_sum {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) {a : ℕ → ℝ}
    (ha : Summable fun s => φ ^ s * |a s|) :
    ∑' T, φ ^ T * (1 - φ) * ∑ s ∈ range (T + 1), a s = ∑' s, φ ^ s * a s := by
  set F : ℕ × ℕ → ℝ := fun p => if p.1 ≤ p.2 then φ ^ p.2 * (1 - φ) * a p.1 else 0 with hF
  have h1φ : 0 ≤ 1 - φ := by linarith
  have habs : ∀ p : ℕ × ℕ, |F p| = if p.1 ≤ p.2 then φ ^ p.2 * (1 - φ) * |a p.1| else 0 := by
    intro p
    simp only [hF]
    split_ifs
    · rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hφ0 _), abs_of_nonneg h1φ]
    · simp
  have hsumabs : Summable fun p => |F p| := by
    rw [summable_prod_of_nonneg (fun p => abs_nonneg (F p))]
    refine ⟨fun s => ?_, ?_⟩
    · simp_rw [habs]
      exact (hasSum_survival_weights hφ0 hφ1 s |a s|).summable
    · simp_rw [habs]
      simpa only [(hasSum_survival_weights hφ0 hφ1 _ _).tsum_eq] using ha
  have hsum : Summable F := hsumabs.of_abs
  have hcomm := hsum.tsum_comm (f := fun s T => F (s, T))
  simp only [hF] at hcomm
  have hL : ∀ T, ∑' s, (if s ≤ T then φ ^ T * (1 - φ) * a s else 0) =
      φ ^ T * (1 - φ) * ∑ s ∈ range (T + 1), a s := by
    intro T
    rw [tsum_eq_sum (s := range (T + 1)), Finset.mul_sum]
    · refine Finset.sum_congr rfl fun s hs => ?_
      rw [ite_eq_left (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))]
    · intro s hs
      rw [ite_eq_right]
      simpa [Nat.lt_succ_iff] using hs
  have hR : ∀ s, ∑' T, (if s ≤ T then φ ^ T * (1 - φ) * a s else 0) = φ ^ s * a s :=
    fun s => (hasSum_survival_weights hφ0 hφ1 s (a s)).tsum_eq
  simp_rw [hL, hR] at hcomm
  exact hcomm

/-- **The survival-adjusted discount factor**, O&R Chapter 2, Exercise 2(b), p. 125: with
survival probability `0 ≤ φ < 1` and `β ≥ 0`,
`E U = Σ_T φ^T(1 − φ) Σ_{s=0}^{T} β^s u(C_s) = Σ_s (φβ)^s u(C_s)`, provided
`Σ (φβ)^s |u(C_s)| < ∞`. -/
theorem expected_utility_uncertain_lifetime {φ β : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hβ : 0 ≤ β)
    (u : ℝ → ℝ) (C : ℕ → ℝ) (hsum : Summable fun s => (φ * β) ^ s * |u (C s)|) :
    ∑' T, φ ^ T * (1 - φ) * ∑ s ∈ range (T + 1), β ^ s * u (C s) =
      ∑' s, (φ * β) ^ s * u (C s) := by
  have ha : Summable fun s => φ ^ s * |β ^ s * u (C s)| := by
    refine hsum.congr fun s => ?_
    rw [abs_mul, abs_of_nonneg (pow_nonneg hβ _), mul_pow, mul_assoc]
  rw [uncertain_lifetime_sum hφ0 hφ1 ha]
  exact tsum_congr fun s => by rw [mul_pow, mul_assoc]

end ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A stochastic current account model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §2.3,
pp. 79–96, Exercises 3 and 4 (pp. 125–126), and Supplement A.3 (p. 722).

Uncertainty uses Mathlib's measure-theoretic conditional expectation. The book's `E_t X` is
`μ[X | ℱ t]` for a filtration `ℱ` on a probability space. Random variables are equal almost
surely (`=ᵐ[μ]`). The stochastic Euler equation (2.28)–(2.29) is a hypothesis throughout, in
conditional-expectation form. Its variational derivation needs differentiation under the
integral and is not formalised. Supplement A.3's dynamic-programming route to it, from the
first-order and envelope conditions, is `euler_of_bellman`.

Contents:
* Hall's random walk (2.31) and the martingale property of consumption (footnote 18):
  `hall_random_walk`, `hall_martingale`, `hall_condExp_future`.
* Certainty equivalence (2.32): `certainty_equivalence`. The book exchanges `E_t` with an
  infinite sum. Here the finite-horizon expected budget identity is exact, and the limit rests
  on explicit expected-transversality and summability hypotheses.
* AR(1) output (2.33)–(2.37): forecasts `output_forecast`, the consumption function
  `consumption_ar1`, the current account `current_account_ar1`, and Deaton's numbers (p. 85).
* Nonstationary output (2.38) and Exercise 4: forecasts, forecast revisions (4b), consumption
  change as revised permanent income (4a), the consumption innovation `(1 + r)/(1 + r − ρ) ε`
  (4c) and the current-account response `−ρ/(1 + r − ρ)` (4d).
* Risky capital (2.40), stated with a conditional covariance (footnote 23).
* Precautionary saving (§2.3.6): `u''' ≥ 0` makes `u'` convex, conditional Jensen, a
  mean-preserving spread raises expected marginal utility, and a two-period comparative static
  (more income risk, lower consumption). Isoelastic `u'''` > 0 (footnote 32).
* Exercise 3: under conditional lognormality, `E_t log C_{t+1} − log C_t = v_t/(2σ)`. The drift
  is constant only when the conditional variance `v_t` is.
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption

open MeasureTheory Filter Topology Finset
open ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue (disc)

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Quadratic period utility, O&R (2.30), p. 81: `u(C) = C − (a₀/2) C²`. -/
noncomputable def quadU (a0 C : ℝ) : ℝ := C - a0 / 2 * C ^ 2

/-- Marginal utility of the quadratic utility (2.30), p. 81: `u'(C) = 1 − a₀ C`. -/
def quadMU (a0 C : ℝ) : ℝ := 1 - a0 * C

/-- O&R p. 81: the marginal utility of (2.30) is `1 − a₀ C`, linear in `C`. -/
theorem hasDerivAt_quadU (a0 c : ℝ) : HasDerivAt (quadU a0) (quadMU a0 c) c := by
  have h := ((hasDerivAt_id c).sub ((hasDerivAt_pow 2 c).const_mul (a0 / 2)))
  have e : quadU a0 = (id - fun y => a0 / 2 * y ^ 2) := by funext y; simp [quadU]
  rw [e]
  convert h using 1
  simp only [quadMU]; norm_num; ring

/-- **Hall's random walk**, O&R (2.31), p. 81. With quadratic utility (2.30), `a₀ ≠ 0` and
`(1 + r) β = 1`, the stochastic Euler equation (2.29) `u'(C_t) = (1 + r) β E_t u'(C_{t+1})`
(taken as a hypothesis in conditional-expectation form; its variational derivation is not
formalised) implies `E_t C_{t+1} = C_t` almost surely. -/
theorem hall_random_walk [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) {C : ℕ → Ω → ℝ} {a0 r β : ℝ} (ha0 : a0 ≠ 0)
    (hrβ : (1 + r) * β = 1) (t : ℕ) (hC : StronglyMeasurable[ℱ t] (C t))
    (hCi : Integrable (C t) μ) (hCi' : Integrable (C (t + 1)) μ)
    (heuler : μ[fun ω => quadMU a0 (C (t + 1) ω) | ℱ t] =ᵐ[μ]
      fun ω => quadMU a0 (C t ω) / ((1 + r) * β)) :
    μ[C (t + 1) | ℱ t] =ᵐ[μ] C t := by
  have hlin : μ[fun ω => quadMU a0 (C (t + 1) ω) | ℱ t] =ᵐ[μ]
      fun ω => 1 - a0 * μ[C (t + 1) | ℱ t] ω := by
    have h1 : (fun ω => quadMU a0 (C (t + 1) ω)) = (fun _ => (1 : ℝ)) - a0 • C (t + 1) := by
      funext ω; simp [quadMU]
    rw [h1]
    filter_upwards [condExp_sub (integrable_const (1 : ℝ)) (hCi'.smul a0) (ℱ t),
      condExp_smul (μ := μ) a0 (C (t + 1)) (ℱ t)] with ω h2 h3
    rw [h2, Pi.sub_apply, h3, condExp_const (ℱ.le t)]
    simp
  have hCt : μ[C t | ℱ t] = C t := condExp_of_stronglyMeasurable (ℱ.le t) hC hCi
  filter_upwards [hlin, heuler] with ω h1 h2
  rw [h1, hrβ, div_one] at h2
  simp only [quadMU] at h2
  have : a0 * μ[C (t + 1) | ℱ t] ω = a0 * C t ω := by linarith
  exact mul_left_cancel₀ ha0 this

/-- **Consumption is a martingale**, O&R (2.31) and footnote 18, p. 81: under the hypotheses of
`hall_random_walk` at every date, and with consumption known at each date, `C` is a martingale
with respect to the information filtration `ℱ`. -/
theorem hall_martingale [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) {C : ℕ → Ω → ℝ} {a0 r β : ℝ} (ha0 : a0 ≠ 0)
    (hrβ : (1 + r) * β = 1) (hC : StronglyAdapted ℱ C) (hCi : ∀ t, Integrable (C t) μ)
    (heuler : ∀ t, μ[fun ω => quadMU a0 (C (t + 1) ω) | ℱ t] =ᵐ[μ]
      fun ω => quadMU a0 (C t ω) / ((1 + r) * β)) :
    Martingale C ℱ μ :=
  martingale_nat hC hCi fun t =>
    (hall_random_walk ℱ ha0 hrβ t (hC t) (hCi t) (hCi (t + 1)) (heuler t)).symm

/-- O&R p. 81: for any `s > t`, `E_t C_s = E_t C_{s−1} = ⋯ = C_t` (law of iterated
expectations applied to Hall's random walk). -/
theorem hall_condExp_future [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) {C : ℕ → Ω → ℝ} {a0 r β : ℝ} (ha0 : a0 ≠ 0)
    (hrβ : (1 + r) * β = 1) (hC : StronglyAdapted ℱ C) (hCi : ∀ t, Integrable (C t) μ)
    (heuler : ∀ t, μ[fun ω => quadMU a0 (C (t + 1) ω) | ℱ t] =ᵐ[μ]
      fun ω => quadMU a0 (C t ω) / ((1 + r) * β)) {t s : ℕ} (hts : t ≤ s) :
    μ[C s | ℱ t] =ᵐ[μ] C t :=
  (hall_martingale ℱ ha0 hrβ hC hCi heuler).2 t s hts

/-- Expected-value budget recursion, O&R p. 81. If net foreign assets obey the current account
identity `B_{s+1} = (1 + r) B_s + Z_s − C_s` in every state (`Z = Y − G − I`) and consumption is a
martingale, then the date-`t` forecasts `b_n = E_t B_{t+n}` satisfy almost surely, for all `n`,
`b_{n+1} = (1 + r) b_n + (E_t Z_{t+n} − C_t)`. -/
theorem condExp_budget_step (ℱ : Filtration ℕ m0) {B Z C : ℕ → Ω → ℝ} {r : ℝ} (t : ℕ)
    (hbud : ∀ s ω, B (s + 1) ω = (1 + r) * B s ω + Z s ω - C s ω)
    (hBi : ∀ s, Integrable (B s) μ) (hZi : ∀ s, Integrable (Z s) μ)
    (hCi : ∀ s, Integrable (C s) μ) (hmart : Martingale C ℱ μ) :
    ∀ᵐ ω ∂μ, ∀ n, μ[B (t + (n + 1)) | ℱ t] ω =
      (1 + r) * μ[B (t + n) | ℱ t] ω + (μ[Z (t + n) | ℱ t] ω - C t ω) := by
  rw [ae_all_iff]
  intro n
  have hf : B (t + (n + 1)) = (1 + r) • B (t + n) + Z (t + n) - C (t + n) := by
    funext ω; simp [← hbud]; rfl
  rw [hf]
  filter_upwards [condExp_sub (((hBi (t + n)).smul (1 + r)).add (hZi (t + n)))
      (hCi (t + n)) (ℱ t),
    condExp_add ((hBi (t + n)).smul (1 + r)) (hZi (t + n)) (ℱ t),
    condExp_smul (μ := μ) (1 + r) (B (t + n)) (ℱ t),
    hmart.2 t (t + n) (Nat.le_add_right t n)] with ω h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, Pi.add_apply, h3, h4]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **Certainty equivalence**, O&R (2.32), p. 81:
`C_t = (r/(1 + r)) [(1 + r) B_t + Σ_{s ≥ t} (1 + r)^{−(s−t)} E_t (Y − G − I)_s]`.
Derived from the martingale property of consumption and the state-by-state current account
identity. The book passes from the almost-sure intertemporal budget constraint to its
expectation by exchanging `E_t` with an infinite sum; here the finite-horizon expectation is
exact and the limit is handled by two explicit hypotheses: the expected discounted terminal
assets vanish (`htvc`, the expected transversality condition) and the discounted net-output
forecasts are summable (`hsum`). Requires `r > 0` (p. 66). -/
theorem certainty_equivalence [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) {B Z C : ℕ → Ω → ℝ} {r : ℝ} (hr : 0 < r)
    (t : ℕ) (hbud : ∀ s ω, B (s + 1) ω = (1 + r) * B s ω + Z s ω - C s ω)
    (hBi : ∀ s, Integrable (B s) μ) (hZi : ∀ s, Integrable (Z s) μ)
    (hCi : ∀ s, Integrable (C s) μ) (hmart : Martingale C ℱ μ)
    (hBt : StronglyMeasurable[ℱ t] (B t))
    (hsum : ∀ᵐ ω ∂μ, Summable fun k => disc r ^ k * μ[Z (t + k) | ℱ t] ω)
    (htvc : ∀ᵐ ω ∂μ, Tendsto (fun n => disc r ^ n * μ[B (t + n) | ℱ t] ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, C t ω =
      r / (1 + r) * ((1 + r) * B t ω + ∑' k, disc r ^ k * μ[Z (t + k) | ℱ t] ω) := by
  have hr1 : 0 < 1 + r := by linarith
  have hB0 : μ[B (t + 0) | ℱ t] = B t := condExp_of_stronglyMeasurable (ℱ.le t) hBt (hBi t)
  filter_upwards [condExp_budget_step ℱ t hbud hBi hZi hCi hmart, hsum, htvc]
    with ω hstep hs htv
  set d := disc r with hd
  set S := ∑' k, d ^ k * μ[Z (t + k) | ℱ t] ω with hS
  have hd1 : (1 + r) * d = 1 := PresentValue.one_add_mul_disc hr1
  have hgeo : HasSum (fun s => d ^ s) ((1 + r) / r) := PresentValue.hasSum_disc_pow hr
  have hN : HasSum (fun s => d ^ (s + 1) * (μ[Z (t + s) | ℱ t] ω - C t ω))
      (d * S - C t ω * d * ((1 + r) / r)) := by
    have := (hs.hasSum.mul_left d).sub (hgeo.mul_left (C t ω * d))
    convert this using 1
    funext s; ring
  have key := (PresentValue.discounted_tendsto_zero_iff hr1 hstep hN.summable).1 htv
  rw [hN.tsum_eq, hB0] at key
  have hdr : d * ((1 + r) / r) = 1 / r := by
    field_simp; linarith
  have : C t ω * (1 / r) = B t ω + d * S := by
    rw [← hdr]; linarith
  field_simp at this
  rw [this, hd, PresentValue.disc]
  field_simp

/-- **Certainty equivalence from the Euler equation**, O&R (2.30)–(2.32), p. 81: combining
`hall_martingale` with `certainty_equivalence`. Quadratic utility, `(1 + r) β = 1`, the Euler
equation (2.29) at every date, the current account identity in every state, and the expected
transversality and summability hypotheses give the consumption function (2.32) almost surely. -/
theorem certainty_equivalence_quadratic [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) {B Z C : ℕ → Ω → ℝ} {a0 r β : ℝ} (hr : 0 < r) (ha0 : a0 ≠ 0)
    (hrβ : (1 + r) * β = 1) (hC : StronglyAdapted ℱ C)
    (heuler : ∀ t, μ[fun ω => quadMU a0 (C (t + 1) ω) | ℱ t] =ᵐ[μ]
      fun ω => quadMU a0 (C t ω) / ((1 + r) * β))
    (t : ℕ) (hbud : ∀ s ω, B (s + 1) ω = (1 + r) * B s ω + Z s ω - C s ω)
    (hBi : ∀ s, Integrable (B s) μ) (hZi : ∀ s, Integrable (Z s) μ)
    (hCi : ∀ s, Integrable (C s) μ) (hBt : StronglyMeasurable[ℱ t] (B t))
    (hsum : ∀ᵐ ω ∂μ, Summable fun k => disc r ^ k * μ[Z (t + k) | ℱ t] ω)
    (htvc : ∀ᵐ ω ∂μ, Tendsto (fun n => disc r ^ n * μ[B (t + n) | ℱ t] ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, C t ω =
      r / (1 + r) * ((1 + r) * B t ω + ∑' k, disc r ^ k * μ[Z (t + k) | ℱ t] ω) :=
  certainty_equivalence ℱ hr t hbud hBi hZi hCi (hall_martingale ℱ ha0 hrβ hC hCi heuler) hBt
    hsum htvc

/-- One-step forecast of an AR(1) deviation, O&R (2.33), p. 82: if
`y_{s+1} = ρ y_s + ε_{s+1}` with `E_s ε_{s+1} = 0` and `y_s` known at `s`, then
`E_s y_{s+1} = ρ y_s`. -/
theorem ar1_condExp_step [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {y ε : ℕ → Ω → ℝ}
    {ρ : ℝ} (s : ℕ) (hy : ∀ ω, y (s + 1) ω = ρ * y s ω + ε (s + 1) ω)
    (hys : StronglyMeasurable[ℱ s] (y s)) (hyi : Integrable (y s) μ)
    (hεi : Integrable (ε (s + 1)) μ) (hε : μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) :
    μ[y (s + 1) | ℱ s] =ᵐ[μ] fun ω => ρ * y s ω := by
  have hf : y (s + 1) = ρ • y s + ε (s + 1) := by funext ω; simp [hy]
  rw [hf]
  filter_upwards [condExp_add (hyi.smul ρ) hεi (ℱ s), condExp_smul (μ := μ) ρ (y s) (ℱ s), hε]
    with ω h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3, condExp_of_stronglyMeasurable (ℱ.le s) hys hyi]
  simp

/-- **AR(1) forecasts**, O&R (2.34), p. 82: if `y_{s+1} = ρ y_s + ε_{s+1}` with
`E_s ε_{s+1} = 0` at every date, then `E_t y_{t+k} = ρ^k y_t` (iterated forward substitution
plus the law of iterated expectations, footnote 20). -/
theorem ar1_forecast [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {y ε : ℕ → Ω → ℝ} {ρ : ℝ}
    (hy : ∀ s ω, y (s + 1) ω = ρ * y s ω + ε (s + 1) ω) (hya : StronglyAdapted ℱ y)
    (hyi : ∀ s, Integrable (y s) μ) (hεi : ∀ s, Integrable (ε s) μ)
    (hε : ∀ s, μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) (t k : ℕ) :
    μ[y (t + k) | ℱ t] =ᵐ[μ] fun ω => ρ ^ k * y t ω := by
  induction k with
  | zero =>
    refine ae_of_all _ fun ω => ?_
    simp [condExp_of_stronglyMeasurable (ℱ.le t) (hya t) (hyi t)]
  | succ k ih =>
    have hstep := ar1_condExp_step ℱ (t + k) (hy (t + k)) (hya (t + k)) (hyi (t + k))
      (hεi (t + k + 1)) (hε (t + k))
    have htow := ℱ.condExp_condExp (μ := μ) (y (t + k + 1)) (Nat.le_add_right t k)
    have hc := condExp_congr_ae (m := ℱ t) hstep
    have hsm : (fun ω => ρ * y (t + k) ω) = ρ • y (t + k) := rfl
    rw [hsm] at hc
    filter_upwards [htow, hc, condExp_smul (μ := μ) ρ (y (t + k)) (ℱ t), ih]
      with ω h1 h2 h3 h4
    change μ[y (t + k + 1) | ℱ t] ω = _
    rw [← h1, h2, h3, Pi.smul_apply, h4, smul_eq_mul, pow_succ]
    ring

/-- **Stationary output forecasts**, O&R (2.33)–(2.34), p. 82: if
`Y_{s+1} − Ȳ = ρ (Y_s − Ȳ) + ε_{s+1}` with `E_s ε_{s+1} = 0`, then
`E_t Y_{t+k} = Ȳ + ρ^k (Y_t − Ȳ)` almost surely. -/
theorem output_forecast [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {Y ε : ℕ → Ω → ℝ}
    {ρ Ybar : ℝ} (hY : ∀ s ω, Y (s + 1) ω - Ybar = ρ * (Y s ω - Ybar) + ε (s + 1) ω)
    (hYa : StronglyAdapted ℱ Y) (hYi : ∀ s, Integrable (Y s) μ)
    (hεi : ∀ s, Integrable (ε s) μ) (hε : ∀ s, μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) (t k : ℕ) :
    μ[Y (t + k) | ℱ t] =ᵐ[μ] fun ω => Ybar + ρ ^ k * (Y t ω - Ybar) := by
  have hya : StronglyAdapted ℱ (fun s => Y s - fun _ => Ybar) :=
    fun s => (hYa s).sub stronglyMeasurable_const
  have hyi : ∀ s, Integrable ((fun s => Y s - fun _ => Ybar) s) μ :=
    fun s => (hYi s).sub (integrable_const Ybar)
  have h := ar1_forecast ℱ (y := fun s => Y s - fun _ => Ybar) (fun s ω => hY s ω) hya hyi hεi
    hε t k
  filter_upwards [h, condExp_sub (hYi (t + k)) (integrable_const Ybar) (ℱ t)] with ω h1 h2
  rw [h2, Pi.sub_apply, condExp_const (ℱ.le t)] at h1
  simp only [Pi.sub_apply] at h1
  linarith

/-- Moving-average form of an AR(1), finite-horizon version of O&R (2.36), p. 83:
`y_{s+n} = ρ^n y_s + Σ_{k<n} ρ^{n−1−k} ε_{s+k+1}` (a pathwise identity). -/
theorem ar1_moving_average {y ε : ℕ → Ω → ℝ} {ρ : ℝ}
    (hy : ∀ s ω, y (s + 1) ω = ρ * y s ω + ε (s + 1) ω) (s n : ℕ) (ω : Ω) :
    y (s + n) ω = ρ ^ n * y s ω + ∑ k ∈ range n, ρ ^ (n - 1 - k) * ε (s + k + 1) ω := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, hy, ih, sum_range_succ, mul_add, mul_sum, pow_succ]
    have : ∑ k ∈ range n, ρ * (ρ ^ (n - 1 - k) * ε (s + k + 1) ω) =
        ∑ k ∈ range n, ρ ^ (n + 1 - 1 - k) * ε (s + k + 1) ω := by
      refine sum_congr rfl fun k hk => ?_
      have hk' : k < n := mem_range.1 hk
      rw [← mul_assoc, ← pow_succ']
      congr 2
      omega
    rw [this]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    ring

/-- Present value of AR(1) forecasts, used in O&R (2.35), p. 83:
`Σ_{k ≥ 0} (1 + r)^{−k} ρ^k = (1 + r)/(1 + r − ρ)` whenever `|ρ| < 1 + r`. -/
theorem hasSum_disc_mul_pow {r ρ : ℝ} (hρ : |ρ| < 1 + r) :
    HasSum (fun k => disc r ^ k * ρ ^ k) ((1 + r) / (1 + r - ρ)) := by
  have hr1 : 0 < 1 + r := lt_of_le_of_lt (abs_nonneg ρ) hρ
  have habs : |disc r * ρ| < 1 := by
    rw [abs_mul, abs_of_pos (PresentValue.disc_pos hr1), PresentValue.disc,
      inv_mul_lt_iff₀ hr1, mul_one]
    exact hρ
  have h := hasSum_geometric_of_abs_lt_one habs
  have hne : 1 + r - ρ ≠ 0 := by
    have := neg_abs_le ρ; have := le_abs_self ρ; intro h; linarith
  convert h using 1
  · funext k; rw [mul_pow]
  · rw [PresentValue.disc]; field_simp

/-- The denominator of O&R (2.35), p. 83, is nonzero: `1 + r − ρ ≠ 0` whenever `|ρ| < 1 + r`. -/
theorem one_add_sub_ne_zero {r ρ : ℝ} (hρ : |ρ| < 1 + r) : 1 + r - ρ ≠ 0 := by
  have := le_abs_self ρ; intro h; linarith

/-- **Consumption with AR(1) output**, O&R (2.35), p. 83: with `G = I = 0`, output following
(2.33), and consumption given by the certainty-equivalence rule (2.32) (hypothesis `hCE`,
supplied by `certainty_equivalence`), `C_t = r B_t + Ȳ + r (Y_t − Ȳ)/(1 + r − ρ)` almost surely.
The book's `0 ≤ ρ ≤ 1` is replaced by the weaker `|ρ| < 1 + r`, which is what the present value
needs. -/
theorem consumption_ar1 [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {B Y ε C : ℕ → Ω → ℝ}
    {r ρ Ybar : ℝ} (hr : 0 < r) (hρ : |ρ| < 1 + r)
    (hY : ∀ s ω, Y (s + 1) ω - Ybar = ρ * (Y s ω - Ybar) + ε (s + 1) ω)
    (hYa : StronglyAdapted ℱ Y) (hYi : ∀ s, Integrable (Y s) μ)
    (hεi : ∀ s, Integrable (ε s) μ) (hε : ∀ s, μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) (t : ℕ)
    (hCE : ∀ᵐ ω ∂μ, C t ω =
      r / (1 + r) * ((1 + r) * B t ω + ∑' k, disc r ^ k * μ[Y (t + k) | ℱ t] ω)) :
    ∀ᵐ ω ∂μ, C t ω = r * B t ω + Ybar + r * (Y t ω - Ybar) / (1 + r - ρ) := by
  have hf : ∀ᵐ ω ∂μ, ∀ k, μ[Y (t + k) | ℱ t] ω = Ybar + ρ ^ k * (Y t ω - Ybar) :=
    ae_all_iff.2 fun k => output_forecast ℱ hY hYa hYi hεi hε t k
  filter_upwards [hCE, hf] with ω h1 h2
  have hsum : HasSum (fun k => disc r ^ k * μ[Y (t + k) | ℱ t] ω)
      (Ybar * ((1 + r) / r) + (Y t ω - Ybar) * ((1 + r) / (1 + r - ρ))) := by
    have := ((PresentValue.hasSum_disc_pow hr).mul_left Ybar).add
      ((hasSum_disc_mul_pow hρ).mul_left (Y t ω - Ybar))
    convert this using 1
    funext k; rw [h2]; ring
  have hne := one_add_sub_ne_zero hρ
  have hr1 : 1 + r ≠ 0 := by linarith
  rw [h1, hsum.tsum_eq]
  field_simp
  ring

/-- Consumption in terms of the innovation, O&R p. 83: substituting
`Y_t − Ȳ = ρ (Y_{t−1} − Ȳ) + ε_t` into (2.35) gives
`C_t = r B_t + Ȳ + (rρ/(1 + r − ρ)) (Y_{t−1} − Ȳ) + (r/(1 + r − ρ)) ε_t`. -/
theorem consumption_innovation_form {r ρ B Ybar Yt Yprev e C : ℝ} (hne : 1 + r - ρ ≠ 0)
    (hC : C = r * B + Ybar + r * (Yt - Ybar) / (1 + r - ρ))
    (hY : Yt - Ybar = ρ * (Yprev - Ybar) + e) :
    C = r * B + Ybar + r * ρ / (1 + r - ρ) * (Yprev - Ybar) + r / (1 + r - ρ) * e := by
  rw [hC, hY]
  field_simp
  ring

/-- **The current account with AR(1) output**, O&R (2.37), p. 83: from (2.35) and the current
account identity `CA_t = r B_t + Y_t − C_t`,
`CA_t = ρ ((1 − ρ)/(1 + r − ρ)) (Y_{t−1} − Ȳ) + ((1 − ρ)/(1 + r − ρ)) ε_t`. -/
theorem current_account_ar1 {r ρ B Ybar Yt Yprev e C : ℝ} (hne : 1 + r - ρ ≠ 0)
    (hC : C = r * B + Ybar + r * (Yt - Ybar) / (1 + r - ρ))
    (hY : Yt - Ybar = ρ * (Yprev - Ybar) + e) :
    r * B + Yt - C =
      ρ * ((1 - ρ) / (1 + r - ρ)) * (Yprev - Ybar) + (1 - ρ) / (1 + r - ρ) * e := by
  have hYt : Yt = Ybar + (ρ * (Yprev - Ybar) + e) := by linarith
  rw [hC, hYt]
  field_simp
  ring

/-- Almost-sure form of O&R (2.37), p. 83: under the hypotheses of `consumption_ar1` at date
`t + 1`, `CA_{t+1} = r B_{t+1} + Y_{t+1} − C_{t+1}` equals
`ρ ((1 − ρ)/(1 + r − ρ)) (Y_t − Ȳ) + ((1 − ρ)/(1 + r − ρ)) ε_{t+1}` almost surely. -/
theorem current_account_ar1_ae [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {B Y ε C : ℕ → Ω → ℝ} {r ρ Ybar : ℝ} (hr : 0 < r) (hρ : |ρ| < 1 + r)
    (hY : ∀ s ω, Y (s + 1) ω - Ybar = ρ * (Y s ω - Ybar) + ε (s + 1) ω)
    (hYa : StronglyAdapted ℱ Y) (hYi : ∀ s, Integrable (Y s) μ)
    (hεi : ∀ s, Integrable (ε s) μ) (hε : ∀ s, μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) (t : ℕ)
    (hCE : ∀ᵐ ω ∂μ, C (t + 1) ω = r / (1 + r) *
      ((1 + r) * B (t + 1) ω + ∑' k, disc r ^ k * μ[Y (t + 1 + k) | ℱ (t + 1)] ω)) :
    ∀ᵐ ω ∂μ, r * B (t + 1) ω + Y (t + 1) ω - C (t + 1) ω =
      ρ * ((1 - ρ) / (1 + r - ρ)) * (Y t ω - Ybar) + (1 - ρ) / (1 + r - ρ) * ε (t + 1) ω := by
  filter_upwards [consumption_ar1 ℱ hr hρ hY hYa hYi hεi hε (t + 1) hCE] with ω h
  exact current_account_ar1 (one_add_sub_ne_zero hρ) h (hY t ω)

/-- O&R p. 83: a temporary shock (`0 ≤ ρ < 1`, `r > 0`) raises the current account,
`(1 − ρ)/(1 + r − ρ) > 0`, and raises consumption less than one for one,
`r/(1 + r − ρ) < 1`. -/
theorem temporary_shock_effects {r ρ : ℝ} (hr : 0 < r) (hρ1 : ρ < 1) :
    0 < (1 - ρ) / (1 + r - ρ) ∧ r / (1 + r - ρ) < 1 := by
  have h : 0 < 1 + r - ρ := by linarith
  refine ⟨div_pos (by linarith) h, ?_⟩
  rw [div_lt_one h]
  linarith

/-- O&R p. 83: a permanent shock (`ρ = 1`) has no current account effect, and consumption moves
one for one with output (`r > 0`). -/
theorem permanent_shock_effects {r : ℝ} (hr : 0 < r) :
    (1 : ℝ) * ((1 - 1) / (1 + r - 1)) = 0 ∧ (1 - 1 : ℝ) / (1 + r - 1) = 0 ∧
      r / (1 + r - 1) = 1 := by
  refine ⟨by simp, by simp, ?_⟩
  rw [add_sub_cancel_left]
  exact div_self hr.ne'

/-- The predictable part of the current account, O&R p. 84: with
`E_{t−1} Y_{t+k} = Ȳ + ρ^{k+1} (Y_{t−1} − Ȳ)`,
`E_{t−1} Y_t − (r/(1 + r)) Σ_{k ≥ 0} (1 + r)^{−k} E_{t−1} Y_{t+k}
  = ρ ((1 − ρ)/(1 + r − ρ)) (Y_{t−1} − Ȳ)`. -/
theorem expected_current_account {r ρ Ybar y : ℝ} (hr : 0 < r) (hρ : |ρ| < 1 + r) :
    (Ybar + ρ * y) - r / (1 + r) * ∑' k, disc r ^ k * (Ybar + ρ ^ (k + 1) * y) =
      ρ * ((1 - ρ) / (1 + r - ρ)) * y := by
  have hsum : HasSum (fun k => disc r ^ k * (Ybar + ρ ^ (k + 1) * y))
      (Ybar * ((1 + r) / r) + ρ * y * ((1 + r) / (1 + r - ρ))) := by
    have := ((PresentValue.hasSum_disc_pow hr).mul_left Ybar).add
      ((hasSum_disc_mul_pow hρ).mul_left (ρ * y))
    convert this using 1
    funext k; ring
  have hne := one_add_sub_ne_zero hρ
  have hr1 : 1 + r ≠ 0 := by linarith
  rw [hsum.tsum_eq]
  field_simp
  ring

/-- **Deaton's paradox numerics**, O&R p. 85: at `ρ = 0.96` and `r = 0.04` the consumption
response `r/(1 + r − ρ)` to an output shock is one half. -/
theorem deaton_consumption_response : (0.04 : ℝ) / (1 + 0.04 - 0.96) = 0.5 := by norm_num

/-- **Nonstationary output forecasts**, O&R (2.38), p. 84: if output growth
`D_{s+1} = Y_{s+1} − Y_s` follows `D_{s+1} = ρ D_s + ε_{s+1}` with `E_s ε_{s+1} = 0`, then
`E_t Y_{t+k} = Y_t + (ρ + ρ² + ⋯ + ρ^k) D_t`. -/
theorem nonstationary_forecast [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {Y D ε : ℕ → Ω → ℝ} {ρ : ℝ} (hY : ∀ s ω, Y (s + 1) ω = Y s ω + D (s + 1) ω)
    (hD : ∀ s ω, D (s + 1) ω = ρ * D s ω + ε (s + 1) ω) (hYa : StronglyAdapted ℱ Y)
    (hDa : StronglyAdapted ℱ D) (hYi : ∀ s, Integrable (Y s) μ)
    (hDi : ∀ s, Integrable (D s) μ) (hεi : ∀ s, Integrable (ε s) μ)
    (hε : ∀ s, μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) (t k : ℕ) :
    μ[Y (t + k) | ℱ t] =ᵐ[μ] fun ω => Y t ω + (∑ j ∈ range k, ρ ^ (j + 1)) * D t ω := by
  induction k with
  | zero =>
    refine ae_of_all _ fun ω => ?_
    simp [condExp_of_stronglyMeasurable (ℱ.le t) (hYa t) (hYi t)]
  | succ k ih =>
    have hf : Y (t + (k + 1)) = Y (t + k) + D (t + (k + 1)) := by
      funext ω; exact hY (t + k) ω
    rw [hf]
    filter_upwards [condExp_add (hYi (t + k)) (hDi (t + (k + 1))) (ℱ t), ih,
      ar1_forecast ℱ hD hDa hDi hεi hε t (k + 1)] with ω h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, sum_range_succ]
    ring

/-- **Forecast revisions**, O&R Exercise 4(b), p. 126: under (2.38), for `s = t + 1 + k > t`,
`(E_{t+1} − E_t) Y_s = (1 + ρ + ⋯ + ρ^{s−(t+1)}) ε_{t+1}`. This is also the claim of p. 84
that an output surprise raises `Y_{t+k}` by `(1 + ρ + ⋯ + ρ^k) ε`. -/
theorem nonstationary_revision [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {Y D ε : ℕ → Ω → ℝ} {ρ : ℝ} (hY : ∀ s ω, Y (s + 1) ω = Y s ω + D (s + 1) ω)
    (hD : ∀ s ω, D (s + 1) ω = ρ * D s ω + ε (s + 1) ω) (hYa : StronglyAdapted ℱ Y)
    (hDa : StronglyAdapted ℱ D) (hYi : ∀ s, Integrable (Y s) μ)
    (hDi : ∀ s, Integrable (D s) μ) (hεi : ∀ s, Integrable (ε s) μ)
    (hε : ∀ s, μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) (t k : ℕ) :
    μ[Y (t + 1 + k) | ℱ (t + 1)] - μ[Y (t + 1 + k) | ℱ t] =ᵐ[μ]
      fun ω => (∑ j ∈ range (k + 1), ρ ^ j) * ε (t + 1) ω := by
  have h1 := nonstationary_forecast ℱ hY hD hYa hDa hYi hDi hεi hε (t + 1) k
  have h0 : μ[Y (t + 1 + k) | ℱ t] =ᵐ[μ]
      fun ω => Y t ω + (∑ j ∈ range (k + 1), ρ ^ (j + 1)) * D t ω := by
    rw [show t + 1 + k = t + (k + 1) by omega]
    exact nonstationary_forecast ℱ hY hD hYa hDa hYi hDi hεi hε t (k + 1)
  filter_upwards [h1, h0] with ω e1 e0
  rw [Pi.sub_apply, e1, e0, hY t ω, hD t ω]
  have hH : ∑ j ∈ range (k + 1), ρ ^ j = ∑ j ∈ range k, ρ ^ (j + 1) + 1 := by
    rw [sum_range_succ']; simp
  have hG : ∑ j ∈ range (k + 1), ρ ^ (j + 1) = ρ * ∑ j ∈ range (k + 1), ρ ^ j := by
    rw [mul_sum]; exact sum_congr rfl fun j _ => pow_succ' ρ j
  rw [hG, hH]
  ring

/-- Closed form of the revision weight in Exercise 4(b), p. 126:
`1 + ρ + ⋯ + ρ^{n−1} = (1 − ρ^n)/(1 − ρ)` for `ρ ≠ 1`. -/
theorem revision_weight_closed_form {ρ : ℝ} (hρ : ρ ≠ 1) (n : ℕ) :
    ∑ j ∈ range n, ρ ^ j = (1 - ρ ^ n) / (1 - ρ) := by
  rw [geom_sum_eq hρ, ← neg_div_neg_eq, neg_sub, neg_sub]

/-- **Consumption change as revised permanent income**, O&R Exercise 4(a), p. 125. With
`G = I = 0`, suppose (2.32) holds at `t` and at `t + 1`, written with the date-`t` forecasts
`F₀ k = E_t Y_{t+1+k}` and date-`t+1` forecasts `F₁ k = E_{t+1} Y_{t+1+k}` (the date-`t` sum split
as `Y_t + (1 + r)^{-1} Σ_k (1 + r)^{-k} F₀ k`, using that `Y_t` is known at `t`), and that the
current account identity `B_{t+1} = (1 + r) B_t + Y_t − C_t` holds. Then
`C_{t+1} − C_t = (r/(1 + r)) Σ_k (1 + r)^{-k} (E_{t+1} − E_t) Y_{t+1+k}`.
The interchange of the difference with the infinite sum is justified by the two summability
hypotheses. -/
theorem consumption_change_revisions {r C0 C1 B0 B1 Y0 : ℝ} {F0 F1 : ℕ → ℝ} (hr : 0 < r)
    (h0 : Summable fun k => disc r ^ k * F0 k) (h1 : Summable fun k => disc r ^ k * F1 k)
    (hC0 : C0 = r / (1 + r) * ((1 + r) * B0 + (Y0 + disc r * ∑' k, disc r ^ k * F0 k)))
    (hC1 : C1 = r / (1 + r) * ((1 + r) * B1 + ∑' k, disc r ^ k * F1 k))
    (hB : B1 = (1 + r) * B0 + Y0 - C0) :
    C1 - C0 = r / (1 + r) * ∑' k, disc r ^ k * (F1 k - F0 k) := by
  have hsub : ∑' k, disc r ^ k * (F1 k - F0 k) =
      ∑' k, disc r ^ k * F1 k - ∑' k, disc r ^ k * F0 k := by
    rw [← h1.tsum_sub h0]; congr 1; funext k; ring
  have hr1 : 1 + r ≠ 0 := by linarith
  rw [hsub, hC1, hB, hC0, PresentValue.disc]
  field_simp
  ring

/-- Present value of the revision weights, used in O&R Exercise 4(c), p. 126: for `ρ ≠ 1` and
`|ρ| < 1 + r`, `Σ_{k ≥ 0} (1 + r)^{-k} (1 + ρ + ⋯ + ρ^k) = (1 + r)²/(r (1 + r − ρ))`. -/
theorem hasSum_revision_weights {r ρ : ℝ} (hr : 0 < r) (hρ : |ρ| < 1 + r) (hρ1 : ρ ≠ 1) :
    HasSum (fun k => disc r ^ k * ∑ j ∈ range (k + 1), ρ ^ j)
      ((1 + r) ^ 2 / (r * (1 + r - ρ))) := by
  have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  have h := ((hasSum_disc_mul_pow hρ).mul_left (ρ / (ρ - 1))).sub
    ((PresentValue.hasSum_disc_pow hr).mul_left (1 / (ρ - 1)))
  have hne := one_add_sub_ne_zero hρ
  convert h using 1
  · funext k
    rw [geom_sum_eq hρ1]
    field_simp
    ring
  · field_simp
    ring

/-- **Consumption innovation via forecast revisions**, O&R Exercise 4(c), p. 126: combining
Exercise 4(a) with the revisions of Exercise 4(b),
`(r/(1 + r)) Σ_k (1 + r)^{-k} (1 + ρ + ⋯ + ρ^k) ε = ((1 + r)/(1 + r − ρ)) ε`. -/
theorem consumption_innovation_from_revisions {r ρ : ℝ} (hr : 0 < r) (hρ : |ρ| < 1 + r)
    (hρ1 : ρ ≠ 1) (e : ℝ) :
    r / (1 + r) * ∑' k, disc r ^ k * ((∑ j ∈ range (k + 1), ρ ^ j) * e) =
      (1 + r) / (1 + r - ρ) * e := by
  have h := (hasSum_revision_weights hr hρ hρ1).mul_right e
  have hr1 : 1 + r ≠ 0 := by linarith
  have hne := one_add_sub_ne_zero hρ
  rw [show (fun k => disc r ^ k * ((∑ j ∈ range (k + 1), ρ ^ j) * e)) =
    fun k => disc r ^ k * (∑ j ∈ range (k + 1), ρ ^ j) * e by funext k; ring, h.tsum_eq]
  field_simp

/-- **Consumption with nonstationary output**, O&R (2.38) with (2.32), p. 84: if output growth
`D` follows `D_{s+1} = ρ D_s + ε_{s+1}` and consumption obeys (2.32) with `G = I = 0`, then
`C_t = r B_t + Y_t + (ρ/(1 + r − ρ)) D_t` almost surely (`ρ ≠ 1`, `|ρ| < 1 + r`). -/
theorem consumption_nonstationary [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {B Y D ε C : ℕ → Ω → ℝ} {r ρ : ℝ} (hr : 0 < r) (hρ : |ρ| < 1 + r) (hρ1 : ρ ≠ 1)
    (hY : ∀ s ω, Y (s + 1) ω = Y s ω + D (s + 1) ω)
    (hD : ∀ s ω, D (s + 1) ω = ρ * D s ω + ε (s + 1) ω) (hYa : StronglyAdapted ℱ Y)
    (hDa : StronglyAdapted ℱ D) (hYi : ∀ s, Integrable (Y s) μ)
    (hDi : ∀ s, Integrable (D s) μ) (hεi : ∀ s, Integrable (ε s) μ)
    (hε : ∀ s, μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) (t : ℕ)
    (hCE : ∀ᵐ ω ∂μ, C t ω =
      r / (1 + r) * ((1 + r) * B t ω + ∑' k, disc r ^ k * μ[Y (t + k) | ℱ t] ω)) :
    ∀ᵐ ω ∂μ, C t ω = r * B t ω + Y t ω + ρ / (1 + r - ρ) * D t ω := by
  have hf : ∀ᵐ ω ∂μ, ∀ k, μ[Y (t + k) | ℱ t] ω =
      Y t ω + (∑ j ∈ range k, ρ ^ (j + 1)) * D t ω :=
    ae_all_iff.2 fun k => nonstationary_forecast ℱ hY hD hYa hDa hYi hDi hεi hε t k
  have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  have hne := one_add_sub_ne_zero hρ
  have hr1 : 1 + r ≠ 0 := by linarith
  filter_upwards [hCE, hf] with ω h1 h2
  have hsum : HasSum (fun k => disc r ^ k * μ[Y (t + k) | ℱ t] ω)
      (Y t ω * ((1 + r) / r) + ρ * D t ω / (ρ - 1) * ((1 + r) / (1 + r - ρ)) -
        ρ * D t ω / (ρ - 1) * ((1 + r) / r)) := by
    have := (((PresentValue.hasSum_disc_pow hr).mul_left (Y t ω)).add
      ((hasSum_disc_mul_pow hρ).mul_left (ρ * D t ω / (ρ - 1)))).sub
      ((PresentValue.hasSum_disc_pow hr).mul_left (ρ * D t ω / (ρ - 1)))
    convert this using 1
    funext k
    rw [h2]
    have hg : ∑ j ∈ range k, ρ ^ (j + 1) = ρ * ((ρ ^ k - 1) / (ρ - 1)) := by
      rw [← geom_sum_eq hρ1, mul_sum]; exact sum_congr rfl fun j _ => pow_succ' ρ j
    rw [hg]
    field_simp
    ring
  rw [h1, hsum.tsum_eq]
  field_simp
  ring

/-- **Consumption innovation with nonstationary output**, O&R Exercise 4(c), p. 126: with the
consumption rule of `consumption_nonstationary` at `t` and `t + 1` and the current account
identity, `C_{t+1} − C_t = ((1 + r)/(1 + r − ρ)) ε_{t+1}`. For `0 < ρ < 1` the coefficient exceeds
one (`consumption_more_volatile`). -/
theorem consumption_innovation_nonstationary {r ρ B0 B1 Y0 Y1 D0 D1 C0 C1 e : ℝ}
    (hne : 1 + r - ρ ≠ 0)
    (hC0 : C0 = r * B0 + Y0 + ρ / (1 + r - ρ) * D0)
    (hC1 : C1 = r * B1 + Y1 + ρ / (1 + r - ρ) * D1)
    (hB : B1 = (1 + r) * B0 + Y0 - C0) (hY : Y1 = Y0 + D1) (hD : D1 = ρ * D0 + e) :
    C1 - C0 = (1 + r) / (1 + r - ρ) * e := by
  rw [hC1, hB, hY, hD, hC0]
  field_simp
  ring

/-- Almost-sure form of Exercise 4(c), p. 126: under the hypotheses of
`consumption_nonstationary` at dates `t` and `t + 1`, and the current account identity
`B_{t+1} = (1 + r) B_t + Y_t − C_t`, `C_{t+1} − C_t = ((1 + r)/(1 + r − ρ)) ε_{t+1}` a.s. -/
theorem consumption_innovation_nonstationary_ae [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) {B Y D ε C : ℕ → Ω → ℝ} {r ρ : ℝ} (hr : 0 < r) (hρ : |ρ| < 1 + r)
    (hρ1 : ρ ≠ 1) (hY : ∀ s ω, Y (s + 1) ω = Y s ω + D (s + 1) ω)
    (hD : ∀ s ω, D (s + 1) ω = ρ * D s ω + ε (s + 1) ω) (hYa : StronglyAdapted ℱ Y)
    (hDa : StronglyAdapted ℱ D) (hYi : ∀ s, Integrable (Y s) μ)
    (hDi : ∀ s, Integrable (D s) μ) (hεi : ∀ s, Integrable (ε s) μ)
    (hε : ∀ s, μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) (t : ℕ)
    (hB : ∀ ω, B (t + 1) ω = (1 + r) * B t ω + Y t ω - C t ω)
    (hCE : ∀ s, ∀ᵐ ω ∂μ, C s ω =
      r / (1 + r) * ((1 + r) * B s ω + ∑' k, disc r ^ k * μ[Y (s + k) | ℱ s] ω)) :
    ∀ᵐ ω ∂μ, C (t + 1) ω - C t ω = (1 + r) / (1 + r - ρ) * ε (t + 1) ω := by
  filter_upwards [consumption_nonstationary ℱ hr hρ hρ1 hY hD hYa hDa hYi hDi hεi hε t (hCE t),
    consumption_nonstationary ℱ hr hρ hρ1 hY hD hYa hDa hYi hDi hεi hε (t + 1) (hCE (t + 1))]
    with ω h0 h1
  exact consumption_innovation_nonstationary (one_add_sub_ne_zero hρ) h0 h1 (hB ω) (hY t ω)
    (hD t ω)

/-- **Current account with nonstationary output**, O&R Exercise 4(d), p. 126, and the claim at the
end of §2.3.3, p. 84. With the consumption rule `C_s = r B_s + Y_s + (ρ/(1 + r − ρ)) D_s` at `t` and
`t + 1`, `CA_s = r B_s + Y_s − C_s` satisfies `CA_t = −(ρ/(1 + r − ρ)) D_t` and
`CA_{t+1} = ρ CA_t − (ρ/(1 + r − ρ)) ε_{t+1}`: the response to an innovation is
`−ρ/(1 + r − ρ)`. -/
theorem current_account_nonstationary {r ρ B0 B1 Y0 Y1 D0 D1 C0 C1 e : ℝ}
    (hC0 : C0 = r * B0 + Y0 + ρ / (1 + r - ρ) * D0)
    (hC1 : C1 = r * B1 + Y1 + ρ / (1 + r - ρ) * D1) (hD : D1 = ρ * D0 + e) :
    r * B0 + Y0 - C0 = -(ρ / (1 + r - ρ)) * D0 ∧
      r * B1 + Y1 - C1 = ρ * (r * B0 + Y0 - C0) - ρ / (1 + r - ρ) * e := by
  constructor
  · rw [hC0]; ring
  · rw [hC1, hC0, hD]; ring

/-- Signs in O&R Exercise 4(c)–(d), p. 126: for `0 < ρ` and `|ρ| < 1 + r`, a positive output
innovation produces a current account deficit (`−ρ/(1 + r − ρ) < 0`) and a consumption innovation
larger than the output innovation (`(1 + r)/(1 + r − ρ) > 1`). -/
theorem consumption_more_volatile {r ρ : ℝ} (hρ0 : 0 < ρ) (hρ : |ρ| < 1 + r) :
    -(ρ / (1 + r - ρ)) < 0 ∧ 1 < (1 + r) / (1 + r - ρ) := by
  have h : 0 < 1 + r - ρ := by have := le_abs_self ρ; linarith
  refine ⟨neg_neg_of_pos (div_pos hρ0 h), ?_⟩
  rw [one_lt_div h]
  linarith

/-- Conditional covariance, O&R footnote 23, p. 86:
`Cov(X, Y | m) = E[XY | m] − E[X | m] E[Y | m]`. With `m = ℱ t` this is the book's `Cov_t`. -/
noncomputable def condCov (μ : Measure Ω) (m : MeasurableSpace Ω) (X Y : Ω → ℝ) : Ω → ℝ :=
  μ[X * Y | m] - μ[X | m] * μ[Y | m]

/-- O&R footnote 23, p. 86: `E(XY) = E(X) E(Y) + Cov(X, Y)`, in conditional form. -/
theorem condExp_mul_eq_add_condCov (m : MeasurableSpace Ω) (X Y : Ω → ℝ) :
    μ[X * Y | m] = μ[X | m] * μ[Y | m] + condCov μ m X Y := by
  simp [condCov]

/-- O&R footnote 23, p. 86: adding a constant does not change a covariance,
`Cov(a₀ + X, Y) = Cov(X, Y)` (conditional version, almost surely). -/
theorem condCov_const_add [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (a0 : ℝ) {X Y : Ω → ℝ} (hX : Integrable X μ) (hY : Integrable Y μ)
    (hXY : Integrable (X * Y) μ) :
    condCov μ m (fun ω => a0 + X ω) Y =ᵐ[μ] condCov μ m X Y := by
  have h1 : (fun ω => a0 + X ω) * Y = a0 • Y + X * Y := by
    funext ω; simp; ring
  have h2 : (fun ω => a0 + X ω) = (fun _ => a0) + X := rfl
  unfold condCov
  rw [h1, h2]
  filter_upwards [condExp_add (hY.smul a0) hXY m, condExp_smul (μ := μ) a0 Y m,
    condExp_add (integrable_const a0) hX m] with ω e1 e2 e3
  simp only [Pi.sub_apply, Pi.mul_apply]
  rw [e1, e3, Pi.add_apply, e2, Pi.add_apply, condExp_const hm]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **Risky capital**, O&R (2.40), p. 86. Let `m` be the date-`t` information, `u'(C_t)` known
at `t` and nonzero, `W = u'(C_{t+1})`, `R = A_{t+1} F'(K_{t+1})`, and `M = u'(C_{t+1})/u'(C_t)`.
Given the bond Euler equation (2.29) `E_t u'(C_{t+1}) = u'(C_t)/((1 + r) β)` and the capital
Euler equation `u'(C_t) = E_t{[1 + R] β u'(C_{t+1})}` (both taken as hypotheses), and
`(1 + r) β = 1`, we get `E_t R = r − Cov_t(R, M)`. -/
theorem risky_capital_return {m : MeasurableSpace Ω} {up : ℝ → ℝ} {Ct Ct1 R : Ω → ℝ} {r β : ℝ}
    (hrβ : (1 + r) * β = 1)
    (hpos : ∀ ω, up (Ct ω) ≠ 0) (hmeas : StronglyMeasurable[m] fun ω => up (Ct ω))
    (hW : Integrable (fun ω => up (Ct1 ω)) μ)
    (hRW : Integrable (fun ω => R ω * up (Ct1 ω)) μ)
    (hM : Integrable (fun ω => up (Ct1 ω) / up (Ct ω)) μ)
    (hRM : Integrable (fun ω => R ω * (up (Ct1 ω) / up (Ct ω))) μ)
    (hbond : μ[fun ω => up (Ct1 ω) | m] =ᵐ[μ] fun ω => up (Ct ω) / ((1 + r) * β))
    (hcap : μ[fun ω => (1 + R ω) * (β * up (Ct1 ω)) | m] =ᵐ[μ] fun ω => up (Ct ω)) :
    μ[R | m] =ᵐ[μ] fun ω => r - condCov μ m R (fun ω => up (Ct1 ω) / up (Ct ω)) ω := by
  have hβ : β ≠ 0 := by rintro rfl; simp at hrβ
  set W : Ω → ℝ := fun ω => up (Ct1 ω) with hWdef
  set q : Ω → ℝ := fun ω => (up (Ct ω))⁻¹ with hqdef
  have hq : StronglyMeasurable[m] q := hmeas.inv₀
  have hMq : (fun ω => up (Ct1 ω) / up (Ct ω)) = q * W := by
    funext ω; simp [hqdef, hWdef, div_eq_inv_mul]
  have hRMq : R * (fun ω => up (Ct1 ω) / up (Ct ω)) = q * (R * W) := by
    funext ω; simp [hqdef, hWdef, div_eq_inv_mul]; ring
  have hcapf : (fun ω => (1 + R ω) * (β * up (Ct1 ω))) = β • W + β • (R * W) := by
    funext ω; simp [hWdef]; ring
  rw [hcapf] at hcap
  have hRW' : Integrable (R * W) μ := hRW
  have eM := condExp_mul_of_stronglyMeasurable_left hq (hMq ▸ hM) hW
  have eRM := condExp_mul_of_stronglyMeasurable_left hq (hRMq ▸ hRM) hRW'
  unfold condCov
  rw [hRMq, hMq]
  filter_upwards [eM, eRM, hbond, hcap, condExp_add (hW.smul β) (hRW'.smul β) m,
    condExp_smul (μ := μ) β W m, condExp_smul (μ := μ) β (R * W) m]
    with ω h1 h2 h3 h4 h5 h6 h7
  rw [h5, Pi.add_apply, h6, h7] at h4
  simp only [Pi.smul_apply, smul_eq_mul] at h4
  simp only [Pi.sub_apply, Pi.mul_apply]
  rw [h1, h2, Pi.mul_apply, Pi.mul_apply]
  have h3' : μ[W | m] ω = up (Ct ω) := by rw [h3, hrβ, div_one]
  rw [h3'] at h4 ⊢
  have hp := hpos ω
  have hRWv : μ[R * W | m] ω = up (Ct ω) / β - up (Ct ω) := by
    field_simp; linarith
  rw [hRWv]
  simp only [hqdef]
  have hr : r = 1 / β - 1 := by field_simp; linarith
  rw [hr]
  field_simp
  ring

/-- O&R §2.3.6, p. 94: if `u''' ≥ 0` on an open convex set then marginal utility `u'` is convex
there (`u''` is the derivative of `u'` and `u'''` that of `u''`). -/
theorem convexOn_of_third_deriv_nonneg {D : Set ℝ} (hD : Convex ℝ D) (hDo : IsOpen D)
    {up upp uppp : ℝ → ℝ} (h2 : ∀ x ∈ D, HasDerivAt up (upp x) x)
    (h3 : ∀ x ∈ D, HasDerivAt upp (uppp x) x) (h3nn : ∀ x ∈ D, 0 ≤ uppp x) :
    ConvexOn ℝ D up := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (f' := upp) (f'' := uppp) hD
    (fun x hx => (h2 x hx).continuousAt.continuousWithinAt) (fun x hx => ?_)
    (fun x hx => ?_) (fun x hx => ?_)
  · rw [hDo.interior_eq] at hx ⊢; exact (h2 x hx).hasDerivWithinAt
  · rw [hDo.interior_eq] at hx ⊢; exact (h3 x hx).hasDerivWithinAt
  · rw [hDo.interior_eq] at hx; exact h3nn x hx

/-- **Isoelastic prudence**, O&R footnote 32, p. 95: for `u'(C) = C^{−1/σ}` with `σ > 0` and
`C > 0`, `u''(C) = −(1/σ) C^{−1/σ−1}` and `u'''(C) = (1/σ)(1 + 1/σ) C^{−1/σ−2} > 0`. -/
theorem crra_third_derivative {σ C : ℝ} (hσ : 0 < σ) (hC : 0 < C) :
    HasDerivAt (fun c : ℝ => c ^ (-1 / σ)) (-1 / σ * C ^ (-1 / σ - 1)) C ∧
      HasDerivAt (fun c : ℝ => -1 / σ * c ^ (-1 / σ - 1))
        (1 / σ * (1 + 1 / σ) * C ^ (-1 / σ - 2)) C ∧
      0 < 1 / σ * (1 + 1 / σ) * C ^ (-1 / σ - 2) := by
  refine ⟨Real.hasDerivAt_rpow_const (Or.inl hC.ne'), ?_, ?_⟩
  · have h := (Real.hasDerivAt_rpow_const (p := -1 / σ - 1) (Or.inl hC.ne')).const_mul (-1 / σ)
    convert h using 1
    rw [show -1 / σ - 1 - 1 = -1 / σ - 2 by ring]
    ring
  · have := Real.rpow_pos_of_pos hC (-1 / σ - 2)
    positivity

/-- O&R §2.3.6 and footnote 32, pp. 94–95: isoelastic marginal utility `C^{−1/σ}` is convex on
`C > 0`. -/
theorem crra_marginal_utility_convex {σ : ℝ} (hσ : 0 < σ) :
    ConvexOn ℝ (Set.Ioi 0) fun c : ℝ => c ^ (-1 / σ) :=
  convexOn_of_third_deriv_nonneg (convex_Ioi 0) isOpen_Ioi
    (fun _ hx => (crra_third_derivative hσ hx).1) (fun _ hx => (crra_third_derivative hσ hx).2.1)
    (fun _ hx => (crra_third_derivative hσ hx).2.2.le)

/-- **Jensen and precautionary saving**, O&R §2.3.6, p. 94: if marginal utility is convex (and
continuous) on a closed convex set containing next period's consumption, then
`E_t u'(C_{t+1}) ≥ u'(E_t C_{t+1})` almost surely (conditional Jensen). -/
theorem condExp_marginal_utility_ge [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m0) {up : ℝ → ℝ} {s : Set ℝ} (hconv : ConvexOn ℝ s up) (hcont : ContinuousOn up s)
    (hs : IsClosed s) {C : Ω → ℝ} (hCs : ∀ᵐ ω ∂μ, C ω ∈ s) (hC : Integrable C μ)
    (hupC : Integrable (up ∘ C) μ) :
    up ∘ μ[C | m] ≤ᵐ[μ] μ[up ∘ C | m] :=
  hconv.map_condExp_le hm hcont.lowerSemicontinuousOn hCs hs hC hupC

/-- **A mean-preserving spread raises expected marginal utility**, O&R §2.3.6, p. 94. If
`C' = C + η` where `C` is known given the information `m` and `E[η | m] = 0` (a mean-preserving
spread in the sense of added noise), and `u'` is convex and continuous on a closed convex set
containing `C'`, then `E u'(C) ≤ E u'(C + η)`. -/
theorem mps_raises_expected_marginal_utility [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m0) {up : ℝ → ℝ} {s : Set ℝ} (hconv : ConvexOn ℝ s up) (hcont : ContinuousOn up s)
    (hs : IsClosed s) {C η : Ω → ℝ} (hCm : StronglyMeasurable[m] C) (hη : μ[η | m] =ᵐ[μ] 0)
    (hCs : ∀ᵐ ω ∂μ, C ω + η ω ∈ s) (hC : Integrable C μ) (hηi : Integrable η μ)
    (hupC : Integrable (up ∘ C) μ) (hupCη : Integrable (up ∘ (C + η)) μ) :
    ∫ ω, up (C ω) ∂μ ≤ ∫ ω, up (C ω + η ω) ∂μ := by
  have hJ := condExp_marginal_utility_ge (C := C + η) hm hconv hcont hs hCs (hC.add hηi) hupCη
  have hmean : μ[C + η | m] =ᵐ[μ] C := by
    filter_upwards [condExp_add hC hηi m, hη] with ω h1 h2
    rw [h1, Pi.add_apply, h2, condExp_of_stronglyMeasurable hm hCm hC]
    simp
  have hle : up ∘ C ≤ᵐ[μ] μ[up ∘ (C + η) | m] := by
    filter_upwards [hJ, hmean] with ω h1 h2
    simpa [h2] using h1
  calc ∫ ω, up (C ω) ∂μ ≤ ∫ ω, μ[up ∘ (C + η) | m] ω ∂μ :=
        integral_mono_ae hupC integrable_condExp hle
    _ = ∫ ω, up (C ω + η ω) ∂μ := by rw [integral_condExp hm]; rfl

/-- **Precautionary saving in a two-period model**, O&R §2.3.6, pp. 94–95. Wealth `W` is split
into consumption `c` today and savings, so tomorrow's consumption is `(1 + r)(W − c) + Y` with
random income `Y`. Let `c` solve the Euler equation (2.29) under income `Y`, and `c'` solve it
under the riskier income `Y + η` with `E[η | m] = 0` and `Y` known given `m` (a mean-preserving
spread). If `u'` is strictly decreasing (`u'' < 0`), convex (`u''' ≥ 0`) and continuous, then
`c' ≤ c`: more income risk means more saving. The Euler equations are hypotheses. -/
theorem precautionary_saving_two_period [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m0) {up : ℝ → ℝ} (hanti : StrictAnti up) (hconv : ConvexOn ℝ Set.univ up)
    (hcont : Continuous up) {r β W c c' : ℝ} (hr1 : 0 < 1 + r) (hβ : 0 < β) {Y η : Ω → ℝ}
    (hYm : StronglyMeasurable[m] Y) (hη : μ[η | m] =ᵐ[μ] 0) (hYi : Integrable Y μ)
    (hηi : Integrable η μ)
    (hi : Integrable (fun ω => up ((1 + r) * (W - c) + Y ω)) μ)
    (hi' : Integrable (fun ω => up ((1 + r) * (W - c') + Y ω)) μ)
    (hi'' : Integrable (fun ω => up ((1 + r) * (W - c') + Y ω + η ω)) μ)
    (heuler : up c = (1 + r) * β * ∫ ω, up ((1 + r) * (W - c) + Y ω) ∂μ)
    (heuler' : up c' = (1 + r) * β * ∫ ω, up ((1 + r) * (W - c') + Y ω + η ω) ∂μ) :
    c' ≤ c := by
  by_contra hcc
  push Not at hcc
  have h1 : up c' < up c := hanti hcc
  have hmps := mps_raises_expected_marginal_utility (μ := μ) hm hconv hcont.continuousOn
    isClosed_univ (C := fun ω => (1 + r) * (W - c') + Y ω) (η := η)
    (stronglyMeasurable_const.add hYm) hη (ae_of_all _ fun _ => Set.mem_univ _)
    ((integrable_const _).add hYi) hηi hi' hi''
  have hmono : ∫ ω, up ((1 + r) * (W - c) + Y ω) ∂μ ≤
      ∫ ω, up ((1 + r) * (W - c') + Y ω) ∂μ := by
    refine integral_mono hi hi' fun ω => hanti.antitone ?_
    have : (1 + r) * (W - c') ≤ (1 + r) * (W - c) :=
      mul_le_mul_of_nonneg_left (by linarith) hr1.le
    linarith
  have hk : 0 < (1 + r) * β := mul_pos hr1 hβ
  have : up c ≤ up c' := by
    rw [heuler, heuler']
    exact mul_le_mul_of_nonneg_left (hmono.trans hmps) hk.le
  linarith

/-- **Hall's random walk under lognormality**, O&R Exercise 3, p. 125. With isoelastic marginal
utility `u'(C) = C^{−1/σ}`, `(1 + r) β = 1`, and `log C_{t+1}` conditionally normal given the
date-`t` information `m` with conditional mean `μ_t` and variance `v_t` (hypotheses: the
conditional moment generating function `E_t exp(θ log C_{t+1}) = exp(θ μ_t + θ² v_t / 2)` and
`E_t log C_{t+1} = μ_t`), the Euler equation (2.29) gives
`E_t log C_{t+1} − log C_t = v_t/(2σ)`.
The book's "constant drift" requires, in addition, a constant conditional variance `v_t`. -/
theorem lognormal_consumption_drift {m : MeasurableSpace Ω} {Ct Ct1 mean var : Ω → ℝ}
    {σ r β : ℝ} (hσ : 0 < σ) (hrβ : (1 + r) * β = 1) (hCt : ∀ ω, 0 < Ct ω)
    (hCt1 : ∀ ω, 0 < Ct1 ω)
    (heuler : μ[fun ω => Ct1 ω ^ (-1 / σ) | m] =ᵐ[μ] fun ω => Ct ω ^ (-1 / σ) / ((1 + r) * β))
    (hmgf : ∀ θ : ℝ, μ[fun ω => Real.exp (θ * Real.log (Ct1 ω)) | m] =ᵐ[μ]
      fun ω => Real.exp (θ * mean ω + θ ^ 2 * var ω / 2))
    (hmean : μ[fun ω => Real.log (Ct1 ω) | m] =ᵐ[μ] mean) :
    μ[fun ω => Real.log (Ct1 ω) | m] - (fun ω => Real.log (Ct ω)) =ᵐ[μ]
      fun ω => var ω / (2 * σ) := by
  have hf : (fun ω => Ct1 ω ^ (-1 / σ)) =
      fun ω => Real.exp (-1 / σ * Real.log (Ct1 ω)) := by
    funext ω; rw [Real.rpow_def_of_pos (hCt1 ω), mul_comm]
  rw [hf] at heuler
  filter_upwards [heuler, hmgf (-1 / σ), hmean] with ω h1 h2 h3
  rw [h1, hrβ, div_one, Real.rpow_def_of_pos (hCt ω)] at h2
  have h4 := Real.exp_injective h2
  rw [Pi.sub_apply, h3]
  field_simp at h4 ⊢
  linarith

/-- **Random walk with constant drift**, O&R Exercise 3, p. 125: if in addition the conditional
variance is a constant `v` and `log C_t` is known at `t`, then
`E_t [log C_{t+1} − log C_t − v/(2σ)] = 0`, i.e. `log C` is a random walk (martingale) with drift
`v/(2σ)`. -/
theorem lognormal_random_walk_drift [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m0) {Ct Ct1 mean : Ω → ℝ} {σ r β v : ℝ} (hσ : 0 < σ) (hrβ : (1 + r) * β = 1)
    (hCt : ∀ ω, 0 < Ct ω) (hCt1 : ∀ ω, 0 < Ct1 ω)
    (hLm : StronglyMeasurable[m] fun ω => Real.log (Ct ω))
    (hL : Integrable (fun ω => Real.log (Ct ω)) μ)
    (hL1 : Integrable (fun ω => Real.log (Ct1 ω)) μ)
    (heuler : μ[fun ω => Ct1 ω ^ (-1 / σ) | m] =ᵐ[μ] fun ω => Ct ω ^ (-1 / σ) / ((1 + r) * β))
    (hmgf : ∀ θ : ℝ, μ[fun ω => Real.exp (θ * Real.log (Ct1 ω)) | m] =ᵐ[μ]
      fun ω => Real.exp (θ * mean ω + θ ^ 2 * v / 2))
    (hmean : μ[fun ω => Real.log (Ct1 ω) | m] =ᵐ[μ] mean) :
    μ[fun ω => Real.log (Ct1 ω) - Real.log (Ct ω) - v / (2 * σ) | m] =ᵐ[μ] 0 := by
  have hd := lognormal_consumption_drift (var := fun _ => v) hσ hrβ hCt hCt1 heuler hmgf hmean
  have hf : (fun ω => Real.log (Ct1 ω) - Real.log (Ct ω) - v / (2 * σ)) =
      (fun ω => Real.log (Ct1 ω)) - (fun ω => Real.log (Ct ω)) - fun _ => v / (2 * σ) := rfl
  rw [hf]
  filter_upwards [condExp_sub (hL1.sub hL) (integrable_const (v / (2 * σ))) m,
    condExp_sub hL1 hL m, hd] with ω h1 h2 h3
  rw [h1, Pi.sub_apply, h2, condExp_const hm, condExp_of_stronglyMeasurable hm hLm hL]
  simp only [Pi.sub_apply] at h3 ⊢
  rw [h3]
  simp

/-- **Stochastic Euler equation from dynamic programming**, O&R Supplement A.3, p. 722: the
first-order condition of the stochastic Bellman equation,
`u'(C_t) = (1 + r) β E_t J'_{t+1}(W_{t+1})`, and the envelope condition
`u'(C_{t+1}) = J'_{t+1}(W_{t+1})` (both hypotheses; `J'` may depend on the date-`t+1` state) give
the stochastic Euler equation (2.29), `u'(C_t) = (1 + r) β E_t u'(C_{t+1})`. -/
theorem euler_of_bellman {m : MeasurableSpace Ω} {up : ℝ → ℝ} {Jp : Ω → ℝ → ℝ}
    {Ct Ct1 W1 : Ω → ℝ} {r β : ℝ}
    (hfoc : (fun ω => up (Ct ω)) =ᵐ[μ] fun ω => (1 + r) * β * μ[fun ω => Jp ω (W1 ω) | m] ω)
    (henv : ∀ᵐ ω ∂μ, up (Ct1 ω) = Jp ω (W1 ω)) :
    (fun ω => up (Ct ω)) =ᵐ[μ] fun ω => (1 + r) * β * μ[fun ω => up (Ct1 ω) | m] ω := by
  filter_upwards [hfoc, condExp_congr_ae (m := m) henv] with ω h1 h2
  rw [h1, h2]

end ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The present-value test of the current account

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §2.3.5,
pp. 90–93 (equations (2.42)–(2.45), footnotes 28–29), with Exercises 5 and 6, p. 126.

Net output is `Z = Y − I − G`. Equation (2.42) says `CA_t = Z_t − E_t Z̃_t`, with
`E_t Z̃_t = (r/(1+r)) Σ_{s≥t} (1+r)^{-(s-t)} E_t Z_s`; Campbell's form (2.43) is
`CA_t = −Σ_{s>t} (1+r)^{-(s-t)} E_t ΔZ_s`.

Contents.
* Deterministic summation by parts (Exercise 6): the finite-horizon identity
  `campbell_finite_horizon`, the infinite version `campbell_deterministic` (under absolute
  summability of the present value), and `campbell_of_tail`, which needs only the book's tail
  condition `(1+r)^{-T} Z_T → 0` and summable changes.
* Stochastic version, with Mathlib's conditional expectation `μ[·|ℱ t]` for `E_t`:
  `campbell_eq_43` derives (2.43) from (2.42). The forecasts are summed pathwise, as in the book,
  so no interchange of `E_t` and `Σ` is needed there. Where an interchange is needed (Exercise 5,
  footnote 29), it is proved from Mathlib's `condExp_tsum` under the standing assumption
  `Σ_s (1+r)^{-s} E|Z_{t+s}| < ∞` (the stochastic form of the growth condition on p. 66).
* Exercise 5 (Campbell's residual test): `condExp_residual_eq_zero` (forward direction),
  `campbell_of_residual` and `campbell_iff_residual` (converse, corrected).
  **Correction.** The book says (2.43) holds *if and only if*
  `CA_{t+1} − ΔZ_{t+1} − (1+r) CA_t` is uncorrelated with date-`t` information. The "if"
  direction is false without a no-bubble condition `lim_n (1+r)^{-n} E_t CA_{t+n} = 0`. The
  counterexample `residual_orthogonality_insufficient` has `Z = 0` and `CA_t = (1+r)^t`. The
  corrected iff is `campbell_iff_residual`.
* Footnote 29: `condExp_coarser_info` (tower property) and `campbell_coarser_information`:
  (2.43) survives conditioning on any coarser information set for which `CA_t` is measurable.
* The VAR forecast (2.44)–(2.45): the matrix geometric series of footnote 28
  (`tsum_pow_succ_eq_mul_inv`, with the sufficient row-sum condition
  `summable_disc_smul_pow`), iterated forecasts `E_t x_{t+k} = Ψ^k x_t` (`condExp_var_pow`),
  the predicted current account (2.45) (`var_predicted_current_account`), and the tested
  restriction `CA_t = ĈA_t` (`var_null_restriction`).
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest

open MeasureTheory Filter Topology Finset
open scoped Matrix
open ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue

/-! ## Deterministic summation by parts -/

/-- `1 − 1/(1 + r) = r/(1 + r)`, the annuity factor of O&R (2.42), p. 90. -/
theorem one_sub_disc_eq {r : ℝ} (hr : 0 < 1 + r) : 1 - disc r = r / (1 + r) := by
  unfold disc
  field_simp
  ring

/-- Finite-horizon summation by parts behind O&R (2.43), p. 90 (Exercise 6, p. 126):
`Σ_{s<T} (1+r)^{-(s+1)} ΔZ_{s+1} = (1+r)^{-T} Z_T − Z_0 + (1 − 1/(1+r)) Σ_{s<T} (1+r)^{-s} Z_s`. -/
theorem sum_disc_diff_eq (r : ℝ) (Z : ℕ → ℝ) (T : ℕ) :
    ∑ s ∈ range T, disc r ^ (s + 1) * (Z (s + 1) - Z s) =
      disc r ^ T * Z T - Z 0 + (1 - disc r) * ∑ s ∈ range T, disc r ^ s * Z s := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    ring

/-- Finite-horizon Campbell identity, O&R (2.43), p. 90: net output less its truncated
annuity value equals minus the discounted sum of future changes plus the terminal term
`(1+r)^{-T} Z_T`. -/
theorem campbell_finite_horizon (r : ℝ) (Z : ℕ → ℝ) (T : ℕ) :
    Z 0 - (1 - disc r) * ∑ s ∈ range T, disc r ^ s * Z s =
      -∑ s ∈ range T, disc r ^ (s + 1) * (Z (s + 1) - Z s) + disc r ^ T * Z T := by
  rw [sum_disc_diff_eq]
  ring

/-- The tail condition `(1+r)^{-T} Z_T → 0` needed for O&R (2.43), p. 90, holds whenever the
present value of `Z` converges absolutely. -/
theorem tail_tendsto_zero {r : ℝ} {Z : ℕ → ℝ} (hZ : Summable fun s => disc r ^ s * Z s) :
    Tendsto (fun T => disc r ^ T * Z T) atTop (𝓝 0) :=
  hZ.tendsto_atTop_zero

/-- If the present value of `Z` converges, so does the discounted sum of its changes, the
right-hand side of O&R (2.43), p. 90. -/
theorem summable_disc_diff {r : ℝ} {Z : ℕ → ℝ} (hZ : Summable fun s => disc r ^ s * Z s) :
    Summable fun s => disc r ^ (s + 1) * (Z (s + 1) - Z s) := by
  have h1 : Summable fun s => disc r ^ (s + 1) * Z (s + 1) :=
    (summable_nat_add_iff 1).2 hZ
  have h2 : Summable fun s => disc r * (disc r ^ s * Z s) := hZ.mul_left _
  refine (h1.sub h2).congr fun s => ?_
  ring

/-- Deterministic Campbell identity, O&R (2.43), p. 90 (Exercise 6, p. 126): if the present
value of `Z` converges and `r > 0`, then `Z_0 − Z̃ = −Σ_{s≥0} (1+r)^{-(s+1)} (Z_{s+1} − Z_s)`,
where `Z̃` is the permanent value (2.42). -/
theorem campbell_deterministic {r : ℝ} (hr : 0 < r) {Z : ℕ → ℝ}
    (hZ : Summable fun s => disc r ^ s * Z s) :
    Z 0 - permanent r Z = -∑' s, disc r ^ (s + 1) * (Z (s + 1) - Z s) := by
  have hr1 : 0 < 1 + r := by linarith
  have h1 : Summable fun s => disc r ^ (s + 1) * Z (s + 1) :=
    (summable_nat_add_iff 1).2 hZ
  have h2 : Summable fun s => disc r * (disc r ^ s * Z s) := hZ.mul_left _
  have e1 : ∑' s, disc r ^ (s + 1) * Z (s + 1) = pv r Z - Z 0 := by
    unfold pv
    rw [hZ.tsum_eq_zero_add]
    simp
  have e2 : ∑' s, disc r * (disc r ^ s * Z s) = disc r * pv r Z := by
    unfold pv
    exact tsum_mul_left
  have e3 : ∑' s, disc r ^ (s + 1) * (Z (s + 1) - Z s) =
      ∑' s, disc r ^ (s + 1) * Z (s + 1) - ∑' s, disc r * (disc r ^ s * Z s) := by
    rw [← h1.tsum_sub h2]
    exact tsum_congr fun s => by ring
  rw [e3, e1, e2]
  unfold permanent
  rw [← one_sub_disc_eq hr1]
  ring

/-- O&R (2.43), p. 90, derived under the book's tail condition only: if the discounted changes
are summable and `(1+r)^{-T} Z_T → 0`, the truncated permanent values converge and
`Z_0 − lim_T (r/(1+r)) Σ_{s<T} (1+r)^{-s} Z_s = −Σ (1+r)^{-(s+1)} ΔZ_{s+1}`. (The limit may be
only conditionally convergent, so it is stated with partial sums.) -/
theorem campbell_of_tail {r : ℝ} (hr : 0 < 1 + r) {Z : ℕ → ℝ}
    (hD : Summable fun s => disc r ^ (s + 1) * (Z (s + 1) - Z s))
    (htail : Tendsto (fun T => disc r ^ T * Z T) atTop (𝓝 0)) :
    Tendsto (fun T => Z 0 - r / (1 + r) * ∑ s ∈ range T, disc r ^ s * Z s) atTop
      (𝓝 (-∑' s, disc r ^ (s + 1) * (Z (s + 1) - Z s))) := by
  have h := (hD.hasSum.tendsto_sum_nat.neg).add htail
  rw [add_zero] at h
  refine h.congr fun T => ?_
  rw [← one_sub_disc_eq hr, campbell_finite_horizon]

/-! ## The stochastic version: conditional expectations -/

namespace Stochastic

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Conditional expected permanent net output `E_t Z̃_t = (r/(1+r)) Σ_{s≥0} (1+r)^{-s} E_t Z_{t+s}`,
O&R (2.42), p. 90, taken as the sum of the conditional forecasts (as the book writes it). -/
noncomputable def forecastPermanent (μ : Measure Ω) (ℱ : Filtration ℕ m0) (r : ℝ)
    (Z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => r / (1 + r) * ∑' s, disc r ^ s * μ[Z (t + s) | ℱ t] ω

/-- The right-hand side of O&R (2.43), p. 90, without its minus sign:
`Σ_{s≥0} (1+r)^{-(s+1)} E_t ΔZ_{t+s+1}`. -/
noncomputable def campbellPV (μ : Measure Ω) (ℱ : Filtration ℕ m0) (r : ℝ)
    (Z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' s, disc r ^ (s + 1) * μ[Z (t + s + 1) - Z (t + s) | ℱ t] ω

/-- The Campbell residual of Exercise 5, p. 126:
`e_{t+1} = CA_{t+1} − ΔZ_{t+1} − (1+r) CA_t`. -/
noncomputable def campbellResidual (r : ℝ) (CA Z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  CA (t + 1) - (Z (t + 1) - Z t) - (1 + r) • CA t

/-- Technical lemma for O&R (2.43), p. 90: summable `L¹` norms give a finite sum of
lower integrals (the hypothesis of Mathlib's `condExp_tsum`). -/
theorem tsum_lintegral_ne_top {f : ℕ → Ω → ℝ} (hf : ∀ s, Integrable (f s) μ)
    (hs : Summable fun s => ∫ ω, |f s ω| ∂μ) : ∑' s, ∫⁻ ω, ‖f s ω‖ₑ ∂μ ≠ ⊤ := by
  have h (s : ℕ) : ∫⁻ ω, ‖f s ω‖ₑ ∂μ = ‖∫ ω, |f s ω| ∂μ‖ₑ := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hf s), Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (integral_nonneg fun ω => abs_nonneg _)]
    rfl
  rw [funext h]
  exact tsum_enorm_ne_top_iff_summable_norm.2 hs.abs

/-- Technical lemma for O&R (2.43), p. 90: summable `L¹` norms give almost-sure absolute
summability of the random series. -/
theorem ae_summable_of_integral {f : ℕ → Ω → ℝ} (hf : ∀ s, Integrable (f s) μ)
    (hs : Summable fun s => ∫ ω, |f s ω| ∂μ) : ∀ᵐ ω ∂μ, Summable fun s => f s ω := by
  have h : ∑' s, eLpNorm (f s) 1 μ ≠ ⊤ := by
    rw [show (fun s => eLpNorm (f s) 1 μ) = fun s => ∫⁻ ω, ‖f s ω‖ₑ ∂μ from
      funext fun s => eLpNorm_one_eq_lintegral_enorm (hf s).1]
    exact tsum_lintegral_ne_top hf hs
  filter_upwards [summable_norm_of_tsum_eLpNorm_ne_top le_rfl h] with ω hω
  exact hω.of_norm

/-- Interchange of conditional expectation and an infinite sum, needed to take `E_t` of the
present value in O&R (2.43), p. 90, and footnote 29, p. 92: valid when the `L¹` norms are
summable. -/
theorem condExp_tsum_of_integral (m : MeasurableSpace Ω) {f : ℕ → Ω → ℝ}
    (hf : ∀ s, Integrable (f s) μ) (hs : Summable fun s => ∫ ω, |f s ω| ∂μ) :
    μ[fun ω => ∑' s, f s ω | m] =ᵐ[μ] fun ω => ∑' s, μ[f s | m] ω :=
  condExp_tsum (fun s => (hf s).1) (tsum_lintegral_ne_top hf hs)

/-- The `L¹` norm of a discounted conditional forecast is at most the discounted `L¹` norm of the
variable (conditional Jensen), O&R (2.42), p. 90. -/
theorem integral_abs_mul_condExp_le (m : MeasurableSpace Ω) {c : ℝ} (hc : 0 ≤ c)
    (X : Ω → ℝ) : ∫ ω, |c * μ[X | m] ω| ∂μ ≤ c * ∫ ω, |X ω| ∂μ := by
  simp_rw [abs_mul, abs_of_nonneg hc, integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_abs_condExp_le X) hc

/-- Under the standing assumption that net output has a discounted-summable `L¹` norm
(the stochastic form of O&R's growth condition, p. 66), the discounted forecasts of the changes
`ΔZ` have summable `L¹` norms, for any information set `m`. Used for O&R (2.43), p. 90. -/
theorem summable_integral_diff_forecast {r : ℝ} (hr : 0 < 1 + r) {Z : ℕ → Ω → ℝ}
    (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ) (t : ℕ)
    (m : MeasurableSpace Ω) :
    Summable fun s => ∫ ω, |disc r ^ (s + 1) * μ[Z (t + s + 1) - Z (t + s) | m] ω| ∂μ := by
  have hd := (disc_pos hr).le
  have hB : Summable fun s => disc r ^ (s + 1) * ∫ ω, |Z (t + s + 1) ω| ∂μ +
      disc r * (disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ) :=
    ((summable_nat_add_iff 1).2 (hS t)).add ((hS t).mul_left _)
  refine Summable.of_nonneg_of_le (fun s => integral_nonneg fun ω => abs_nonneg _)
    (fun s => ?_) hB
  refine (integral_abs_mul_condExp_le m (pow_nonneg hd _) _).trans ?_
  have hsub : ∫ ω, |(Z (t + s + 1) - Z (t + s)) ω| ∂μ ≤
      ∫ ω, |Z (t + s + 1) ω| ∂μ + ∫ ω, |Z (t + s) ω| ∂μ := by
    rw [← integral_add (hZ _).abs (hZ _).abs]
    refine integral_mono ((hZ _).sub (hZ _)).abs ((hZ _).abs.add (hZ _).abs) fun ω => ?_
    exact abs_sub _ _
  calc disc r ^ (s + 1) * ∫ ω, |(Z (t + s + 1) - Z (t + s)) ω| ∂μ
      ≤ disc r ^ (s + 1) * (∫ ω, |Z (t + s + 1) ω| ∂μ + ∫ ω, |Z (t + s) ω| ∂μ) :=
        mul_le_mul_of_nonneg_left hsub (pow_nonneg hd _)
    _ = _ := by ring

/-- The realised discounted changes in net output have summable `L¹` norms under the standing
discounted-`L¹` assumption; this makes the random present value of footnote 29, p. 92,
well defined and integrable. -/
theorem summable_integral_diff {r : ℝ} (hr : 0 < 1 + r) {Z : ℕ → Ω → ℝ}
    (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ) (t : ℕ) :
    Summable fun s => ∫ ω, |disc r ^ (s + 1) * (Z (t + s + 1) - Z (t + s)) ω| ∂μ := by
  have hd := (disc_pos hr).le
  have hB : Summable fun s => disc r ^ (s + 1) * ∫ ω, |Z (t + s + 1) ω| ∂μ +
      disc r * (disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ) :=
    ((summable_nat_add_iff 1).2 (hS t)).add ((hS t).mul_left _)
  refine Summable.of_nonneg_of_le (fun s => integral_nonneg fun ω => abs_nonneg _)
    (fun s => ?_) hB
  simp_rw [abs_mul, abs_of_nonneg (pow_nonneg hd _), integral_const_mul]
  have hsub : ∫ ω, |(Z (t + s + 1) - Z (t + s)) ω| ∂μ ≤
      ∫ ω, |Z (t + s + 1) ω| ∂μ + ∫ ω, |Z (t + s) ω| ∂μ := by
    rw [← integral_add (hZ _).abs (hZ _).abs]
    refine integral_mono ((hZ _).sub (hZ _)).abs ((hZ _).abs.add (hZ _).abs) fun ω => ?_
    exact abs_sub _ _
  calc disc r ^ (s + 1) * ∫ ω, |(Z (t + s + 1) - Z (t + s)) ω| ∂μ
      ≤ disc r ^ (s + 1) * (∫ ω, |Z (t + s + 1) ω| ∂μ + ∫ ω, |Z (t + s) ω| ∂μ) :=
        mul_le_mul_of_nonneg_left hsub (pow_nonneg hd _)
    _ = _ := by ring

/-- Under the standing discounted-`L¹` assumption on net output (O&R's growth condition, p. 66),
the conditional forecasts in O&R (2.42), p. 90, are almost surely discount-summable. -/
theorem ae_summable_forecast {r : ℝ} (hr : 0 < 1 + r) {ℱ : Filtration ℕ m0}
    {Z : ℕ → Ω → ℝ} (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ)
    (t : ℕ) : ∀ᵐ ω ∂μ, Summable fun s => disc r ^ s * μ[Z (t + s) | ℱ t] ω :=
  ae_summable_of_integral (f := fun s ω => disc r ^ s * μ[Z (t + s) | ℱ t] ω)
    (fun _ => integrable_condExp.const_mul _)
    (Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => abs_nonneg _)
      (fun _ => integral_abs_mul_condExp_le _ (pow_nonneg (disc_pos hr).le _) _) (hS t))

/-- The forecast of a change is the change in forecasts, `E_t ΔZ_s = E_t Z_s − E_t Z_{s−1}`
(linearity of conditional expectation), simultaneously for all horizons almost surely; used in
Exercise 6, p. 126. -/
theorem ae_condExp_diff {ℱ : Filtration ℕ m0} {Z : ℕ → Ω → ℝ}
    (hZ : ∀ t, Integrable (Z t) μ) (t : ℕ) :
    ∀ᵐ ω ∂μ, ∀ s, μ[Z (t + s + 1) - Z (t + s) | ℱ t] ω =
      μ[Z (t + s + 1) | ℱ t] ω - μ[Z (t + s) | ℱ t] ω :=
  ae_all_iff.2 fun _ => condExp_sub (hZ _) (hZ _) _

/-- **Exercise 6, p. 126: derivation of O&R (2.43), p. 90.** If the current account obeys the
permanent-income form (2.42), `CA_t = Z_t − E_t Z̃_t`, with `Z_t` known at `t` and the forecasts
discount-summable, then `CA_t = −Σ_{s>t} (1+r)^{-(s-t)} E_t ΔZ_s` almost surely. -/
theorem campbell_eq_43 [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) {ℱ : Filtration ℕ m0}
    {Z CA : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ) {t : ℕ}
    (hZt : StronglyMeasurable[ℱ t] (Z t))
    (hsum : ∀ᵐ ω ∂μ, Summable fun s => disc r ^ s * μ[Z (t + s) | ℱ t] ω)
    (h42 : CA t =ᵐ[μ] fun ω => Z t ω - forecastPermanent μ ℱ r Z t ω) :
    CA t =ᵐ[μ] fun ω => -campbellPV μ ℱ r Z t ω := by
  have hself : μ[Z t | ℱ t] = Z t := condExp_of_stronglyMeasurable (ℱ.le t) hZt (hZ t)
  filter_upwards [h42, hsum, ae_condExp_diff (ℱ := ℱ) hZ t] with ω h1 h2 h3
  rw [h1]
  have key := campbell_deterministic hr h2
  simp only [add_zero, hself] at key
  unfold permanent pv at key
  unfold forecastPermanent campbellPV
  simp only [h3]
  exact key

/-- Linearity of conditional expectation applied to the Campbell residual of Exercise 5, p. 126:
`E[e_{u+1} | m] = E[CA_{u+1} | m] − E[ΔZ_{u+1} | m] − (1+r) E[CA_u | m]`. -/
theorem condExp_residual_ae {r : ℝ} {Z CA : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ)
    (hCA : ∀ t, Integrable (CA t) μ) (m : MeasurableSpace Ω) (u : ℕ) :
    μ[campbellResidual r CA Z u | m] =ᵐ[μ]
      μ[CA (u + 1) | m] - μ[Z (u + 1) - Z u | m] - (1 + r) • μ[CA u | m] := by
  unfold campbellResidual
  refine (condExp_sub ((hCA _).sub ((hZ _).sub (hZ _))) ((hCA _).smul (1 + r)) _).trans ?_
  exact EventuallyEq.sub (condExp_sub (hCA _) ((hZ _).sub (hZ _)) _) (condExp_smul _ _ _)

/-- If the Campbell residual is unpredictable at every date, O&R Exercise 5, p. 126, then the
date-`t` forecasts `V_n = E_t CA_{t+n}` obey `(1+r) V_n = −E_t ΔZ_{t+n+1} + V_{n+1}` for all `n`,
almost surely (law of iterated expectations). -/
theorem ae_forecast_recursion [IsProbabilityMeasure μ] {r : ℝ} {ℱ : Filtration ℕ m0}
    {Z CA : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ) (hCA : ∀ t, Integrable (CA t) μ)
    (hres : ∀ t, μ[campbellResidual r CA Z t | ℱ t] =ᵐ[μ] 0) (t : ℕ) :
    ∀ᵐ ω ∂μ, ∀ n, (1 + r) * μ[CA (t + n) | ℱ t] ω =
      -μ[Z (t + n + 1) - Z (t + n) | ℱ t] ω + μ[CA (t + n + 1) | ℱ t] ω := by
  refine ae_all_iff.2 fun n => ?_
  have h0 : μ[campbellResidual r CA Z (t + n) | ℱ t] =ᵐ[μ] 0 := by
    have htow := condExp_condExp_of_le (μ := μ) (f := campbellResidual r CA Z (t + n))
      (ℱ.mono (Nat.le_add_right t n)) (ℱ.le (t + n))
    refine htow.symm.trans ?_
    refine (condExp_congr_ae (hres (t + n))).trans ?_
    rw [condExp_zero]
  filter_upwards [h0, condExp_residual_ae (r := r) hZ hCA (ℱ t) (t + n)] with ω h0 hlin
  rw [h0] at hlin
  simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hlin
  linarith

/-- Under the standing discounted-`L¹` assumption, the discounted forecasts of future changes in
O&R (2.43), p. 90, are almost surely summable. -/
theorem ae_summable_diff_forecast {r : ℝ} (hr : 0 < 1 + r) {ℱ : Filtration ℕ m0}
    {Z : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ) (t : ℕ) :
    ∀ᵐ ω ∂μ, Summable fun s => disc r ^ (s + 1) * μ[Z (t + s + 1) - Z (t + s) | ℱ t] ω :=
  ae_summable_of_integral (f := fun s ω => disc r ^ (s + 1) * μ[Z (t + s + 1) - Z (t + s) | ℱ t] ω)
    (fun _ => integrable_condExp.const_mul _) (summable_integral_diff_forecast hr hZ hS t (ℱ t))

/-- **Exercise 5, p. 126, forward direction.** If O&R (2.43), p. 90, holds at every date, the
Campbell residual `e_{t+1} = CA_{t+1} − ΔZ_{t+1} − (1+r) CA_t` has zero conditional expectation
given date-`t` information, hence is uncorrelated with every date-`t` variable. -/
theorem condExp_residual_eq_zero [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < 1 + r)
    {ℱ : Filtration ℕ m0} {Z CA : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ)
    (hCA : ∀ t, Integrable (CA t) μ) (hCAad : ∀ t, StronglyMeasurable[ℱ t] (CA t))
    (h43 : ∀ t, CA t =ᵐ[μ] fun ω => -campbellPV μ ℱ r Z t ω) (t : ℕ) :
    μ[campbellResidual r CA Z t | ℱ t] =ᵐ[μ] 0 := by
  have e : ∀ s, t + 1 + s = t + s + 1 := fun s => Nat.add_right_comm t 1 s
  have hself : μ[CA t | ℱ t] = CA t := condExp_of_stronglyMeasurable (ℱ.le t) (hCAad t) (hCA t)
  -- `E_t CA_{t+1}` by the interchange of `E_t` and the sum, then the tower property
  have hT := condExp_tsum_of_integral (ℱ t)
    (f := fun s ω => disc r ^ (s + 1) * μ[Z (t + 1 + s + 1) - Z (t + 1 + s) | ℱ (t + 1)] ω)
    (fun _ => integrable_condExp.const_mul _) (summable_integral_diff_forecast hr hZ hS _ _)
  have hTow : ∀ᵐ ω ∂μ, ∀ s,
      μ[fun ω => disc r ^ (s + 1) * μ[Z (t + 1 + s + 1) - Z (t + 1 + s) | ℱ (t + 1)] ω | ℱ t] ω
        = disc r ^ (s + 1) * μ[Z (t + (s + 1) + 1) - Z (t + (s + 1)) | ℱ t] ω := by
    refine ae_all_iff.2 fun s => ?_
    have a := condExp_smul (μ := μ) (disc r ^ (s + 1))
      (μ[Z (t + 1 + s + 1) - Z (t + 1 + s) | ℱ (t + 1)]) (ℱ t)
    have b := condExp_condExp_of_le (μ := μ) (f := Z (t + 1 + s + 1) - Z (t + 1 + s))
      (ℱ.mono (Nat.le_succ t)) (ℱ.le (t + 1))
    filter_upwards [a, b] with ω ha hb
    have ha' : μ[fun ω => disc r ^ (s + 1) * μ[Z (t + 1 + s + 1) - Z (t + 1 + s) | ℱ (t + 1)] ω
        | ℱ t] ω = disc r ^ (s + 1) *
          μ[μ[Z (t + 1 + s + 1) - Z (t + 1 + s) | ℱ (t + 1)] | ℱ t] ω := ha
    rw [ha', hb, e s]
    rfl
  have hE1 : ∀ᵐ ω ∂μ, μ[CA (t + 1) | ℱ t] ω =
      -∑' s, disc r ^ (s + 1) * μ[Z (t + (s + 1) + 1) - Z (t + (s + 1)) | ℱ t] ω := by
    have h1 := (condExp_congr_ae (m := ℱ t) (h43 (t + 1))).trans
      (condExp_neg (μ := μ) (campbellPV μ ℱ r Z (t + 1)) (ℱ t))
    filter_upwards [h1, hT, hTow] with ω h1 h2 h3
    rw [h1, Pi.neg_apply]
    unfold campbellPV
    rw [h2, tsum_congr h3]
  filter_upwards [condExp_residual_ae (r := r) hZ hCA (ℱ t) t, hE1, h43 t,
    ae_summable_diff_forecast hr (ℱ := ℱ) hZ hS t] with ω hlin hE1 h43t hsum
  rw [hlin]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hself]
  rw [hE1, h43t]
  unfold campbellPV
  rw [hsum.tsum_eq_zero_add]
  have hd := one_add_mul_disc hr
  have hmul : (1 + r) * ∑' s, disc r ^ (s + 1 + 1) *
      μ[Z (t + (s + 1) + 1) - Z (t + (s + 1)) | ℱ t] ω =
        ∑' s, disc r ^ (s + 1) * μ[Z (t + (s + 1) + 1) - Z (t + (s + 1)) | ℱ t] ω := by
    rw [← tsum_mul_left]
    refine tsum_congr fun s => ?_
    rw [pow_succ, ← mul_assoc, ← mul_assoc, mul_comm (1 + r), mul_assoc _ (1 + r), hd, mul_one]
  rw [← hmul]
  simp only [add_zero, zero_add, pow_one]
  linear_combination (μ[Z (t + 1) - Z t | ℱ t] ω) * hd

/-- Exercise 5, p. 126, the key step: once the Campbell residual is unpredictable, O&R (2.43),
p. 90, holds at date `t` exactly when the no-bubble condition
`(1+r)^{-n} E_t CA_{t+n} → 0` holds (almost surely, pathwise in `ω`). -/
theorem ae_campbell_iff_noBubble [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < 1 + r)
    {ℱ : Filtration ℕ m0} {Z CA : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ)
    (hCA : ∀ t, Integrable (CA t) μ) (hCAad : ∀ t, StronglyMeasurable[ℱ t] (CA t))
    (hres : ∀ t, μ[campbellResidual r CA Z t | ℱ t] =ᵐ[μ] 0) (t : ℕ) :
    ∀ᵐ ω ∂μ, (CA t ω = -campbellPV μ ℱ r Z t ω ↔
      Tendsto (fun n => disc r ^ n * μ[CA (t + n) | ℱ t] ω) atTop (𝓝 0)) := by
  have hself : μ[CA t | ℱ t] = CA t := condExp_of_stronglyMeasurable (ℱ.le t) (hCAad t) (hCA t)
  filter_upwards [ae_forecast_recursion hZ hCA hres t,
    ae_summable_diff_forecast hr (ℱ := ℱ) hZ hS t] with ω hrec hsum
  set V : ℕ → ℝ := fun n => μ[CA (t + n) | ℱ t] ω with hV
  set D : ℕ → ℝ := fun k => -μ[Z (t + (k - 1) + 1) - Z (t + (k - 1)) | ℱ t] ω with hD
  have h : ∀ s, (1 + r) * V s = D (s + 1) + V (s + 1) := by
    intro s
    simp only [hV, hD, add_tsub_cancel_right]
    exact hrec s
  have hs : Summable fun s => disc r ^ (s + 1) * D (s + 1) := by
    refine hsum.neg.congr fun s => ?_
    simp only [hD, add_tsub_cancel_right]
    ring
  have hV0 : V 0 = CA t ω := by simp only [hV, add_zero, hself]
  have hsumD : ∑' s, disc r ^ (s + 1) * D (s + 1) = -campbellPV μ ℱ r Z t ω := by
    unfold campbellPV
    rw [← tsum_neg]
    refine tsum_congr fun s => ?_
    simp only [hD, add_tsub_cancel_right]
    ring
  rw [← hV0, ← hsumD]
  exact forward_solution_iff hr h hs

/-- **Exercise 5, p. 126, converse direction (corrected).** If the Campbell residual
`CA_{t+1} − ΔZ_{t+1} − (1+r) CA_t` is unpredictable at every date AND the no-bubble condition
`(1+r)^{-n} E_t CA_{t+n} → 0` holds, then O&R (2.43), p. 90, holds at `t`. The book states the
converse without the no-bubble condition; see `residual_orthogonality_insufficient`. -/
theorem campbell_of_residual [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < 1 + r)
    {ℱ : Filtration ℕ m0} {Z CA : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ)
    (hCA : ∀ t, Integrable (CA t) μ) (hCAad : ∀ t, StronglyMeasurable[ℱ t] (CA t))
    (hres : ∀ t, μ[campbellResidual r CA Z t | ℱ t] =ᵐ[μ] 0) (t : ℕ)
    (hnb : ∀ᵐ ω ∂μ, Tendsto (fun n => disc r ^ n * μ[CA (t + n) | ℱ t] ω) atTop (𝓝 0)) :
    CA t =ᵐ[μ] fun ω => -campbellPV μ ℱ r Z t ω := by
  filter_upwards [ae_campbell_iff_noBubble hr hZ hS hCA hCAad hres t, hnb] with ω h1 h2
  exact h1.2 h2

/-- **Exercise 5, p. 126 (corrected iff).** Given integrable, adapted `CA` and net output with
discount-summable `L¹` norms, O&R (2.43), p. 90, holds at every date if and only if the Campbell
residual `CA_{t+1} − ΔZ_{t+1} − (1+r) CA_t` is unpredictable from date-`t` information at every
date and the no-bubble condition `lim_n (1+r)^{-n} E_t CA_{t+n} = 0` holds at every date. -/
theorem campbell_iff_residual [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < 1 + r)
    {ℱ : Filtration ℕ m0} {Z CA : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ)
    (hCA : ∀ t, Integrable (CA t) μ) (hCAad : ∀ t, StronglyMeasurable[ℱ t] (CA t)) :
    (∀ t, CA t =ᵐ[μ] fun ω => -campbellPV μ ℱ r Z t ω) ↔
      (∀ t, μ[campbellResidual r CA Z t | ℱ t] =ᵐ[μ] 0) ∧
        ∀ t, ∀ᵐ ω ∂μ, Tendsto (fun n => disc r ^ n * μ[CA (t + n) | ℱ t] ω) atTop (𝓝 0) := by
  constructor
  · intro h43
    have hres := condExp_residual_eq_zero hr hZ hS hCA hCAad h43
    refine ⟨hres, fun t => ?_⟩
    filter_upwards [ae_campbell_iff_noBubble hr hZ hS hCA hCAad hres t, h43 t] with ω h1 h2
    exact h1.1 h2
  · rintro ⟨hres, hnb⟩ t
    exact campbell_of_residual hr hZ hS hCA hCAad hres t (hnb t)

/-- **The no-bubble condition cannot be dropped from Exercise 5, p. 126.** With zero net output
and the explosive current account `CA_t = (1+r)^t` (integrable and adapted), the Campbell residual
is identically zero, yet O&R (2.43), p. 90, fails at date 0 (it would force `CA_0 = 0`). -/
theorem residual_orthogonality_insufficient [IsProbabilityMeasure μ] (r : ℝ)
    (ℱ : Filtration ℕ m0) :
    ∃ Z CA : ℕ → Ω → ℝ, (∀ t, Integrable (Z t) μ) ∧ (∀ t, Integrable (CA t) μ) ∧
      (∀ t, StronglyMeasurable[ℱ t] (CA t)) ∧
      (∀ t, μ[campbellResidual r CA Z t | ℱ t] =ᵐ[μ] 0) ∧
      ¬ (CA 0 =ᵐ[μ] fun ω => -campbellPV μ ℱ r Z 0 ω) := by
  refine ⟨fun _ _ => 0, fun t _ => (1 + r) ^ t, fun _ => integrable_const _,
    fun _ => integrable_const _, fun _ => stronglyMeasurable_const, fun t => ?_, ?_⟩
  · have h0 : campbellResidual r (fun t (_ : Ω) => (1 + r) ^ t) (fun _ (_ : Ω) => (0 : ℝ)) t
        = 0 := by
      funext ω
      simp only [campbellResidual, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        pow_succ]
      ring
    rw [h0, condExp_zero]
  · intro h
    have hc : campbellPV μ ℱ r (fun _ _ => 0) 0 = 0 := by
      funext ω
      simp [campbellPV, condExp_zero]
    obtain ⟨ω, hω⟩ := h.exists
    simp [hc] at hω

/-! ### Footnote 29: coarser information sets -/

/-- **O&R footnote 29, p. 92 (tower property).** If `CA = −E[PV | 𝓘]` for the full information
set `𝓘`, and `CA` is measurable with respect to a coarser `𝓖 ⊆ 𝓘`, then also `CA = −E[PV | 𝓖]`:
the econometrician's smaller information set gives the same prediction. -/
theorem condExp_coarser_info [IsProbabilityMeasure μ] {𝓖 𝓘 : MeasurableSpace Ω}
    (h𝓖 : 𝓖 ≤ 𝓘) (h𝓘 : 𝓘 ≤ m0) {CA PV : Ω → ℝ} (hCA : CA =ᵐ[μ] -μ[PV | 𝓘])
    (hCAm : StronglyMeasurable[𝓖] CA) : CA =ᵐ[μ] -μ[PV | 𝓖] := by
  have hint : Integrable CA μ := integrable_condExp.neg.congr hCA.symm
  have hself : μ[CA | 𝓖] = CA := condExp_of_stronglyMeasurable (h𝓖.trans h𝓘) hCAm hint
  have h := (condExp_congr_ae (m := 𝓖) hCA).trans
    ((condExp_neg (μ[PV | 𝓘]) 𝓖).trans (condExp_condExp_of_le h𝓖 h𝓘).neg)
  rwa [hself] at h

/-- The realised present value of future net-output changes,
`Σ_{s≥0} (1+r)^{-(s+1)} ΔZ_{t+s+1}`, the random variable inside the expectation of O&R
footnote 29, p. 92. -/
noncomputable def pvChanges (r : ℝ) (Z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' s, disc r ^ (s + 1) * (Z (t + s + 1) - Z (t + s)) ω

/-- The sum of conditional forecasts of future changes equals the conditional expectation of
their realised present value, for any information set `m` (O&R (2.43), p. 90, and footnote 29,
p. 92): the interchange `Σ E[·|m] = E[Σ ·|m]`, proved under the standing `L¹` assumption. -/
theorem forecastSum_ae_eq_condExp {r : ℝ} (hr : 0 < 1 + r) {Z : ℕ → Ω → ℝ}
    (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ) (t : ℕ)
    (m : MeasurableSpace Ω) :
    (fun ω => ∑' s, disc r ^ (s + 1) * μ[Z (t + s + 1) - Z (t + s) | m] ω) =ᵐ[μ]
      μ[pvChanges r Z t | m] := by
  have hT := condExp_tsum_of_integral m
    (f := fun s ω => disc r ^ (s + 1) * (Z (t + s + 1) - Z (t + s)) ω)
    (fun _ => ((hZ _).sub (hZ _)).const_mul _) (summable_integral_diff hr hZ hS t)
  have hsm : ∀ᵐ ω ∂μ, ∀ s,
      μ[fun ω => disc r ^ (s + 1) * (Z (t + s + 1) - Z (t + s)) ω | m] ω =
        disc r ^ (s + 1) * μ[Z (t + s + 1) - Z (t + s) | m] ω :=
    ae_all_iff.2 fun s => condExp_smul (μ := μ) (disc r ^ (s + 1)) (Z (t + s + 1) - Z (t + s)) m
  filter_upwards [hT, hsm] with ω h1 h2
  unfold pvChanges
  rw [h1, tsum_congr h2]

/-- **O&R footnote 29, p. 92, for the model.** If O&R (2.43), p. 90, holds with respect to the
consumers' information `ℱ t`, then it holds with respect to any coarser information set
`𝓖 ⊆ ℱ t` (for example the econometrician's VAR information `(ΔZ_t, CA_t)`) for which `CA_t` is
measurable: `CA_t = −Σ_{s>t} (1+r)^{-(s-t)} E[ΔZ_s | 𝓖]`. -/
theorem campbell_coarser_information [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < 1 + r)
    {ℱ : Filtration ℕ m0} {Z CA : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ) {t : ℕ}
    (h43 : CA t =ᵐ[μ] fun ω => -campbellPV μ ℱ r Z t ω) {𝓖 : MeasurableSpace Ω}
    (h𝓖 : 𝓖 ≤ ℱ t) (hCAm : StronglyMeasurable[𝓖] (CA t)) :
    CA t =ᵐ[μ] fun ω => -∑' s, disc r ^ (s + 1) * μ[Z (t + s + 1) - Z (t + s) | 𝓖] ω := by
  have h1 : CA t =ᵐ[μ] -μ[pvChanges r Z t | ℱ t] := by
    filter_upwards [h43, forecastSum_ae_eq_condExp hr hZ hS t (ℱ t)] with ω h1 h2
    rw [h1, Pi.neg_apply, ← h2]
    rfl
  have h2 := condExp_coarser_info h𝓖 (ℱ.le t) h1 hCAm
  filter_upwards [h2, forecastSum_ae_eq_condExp hr hZ hS t 𝓖] with ω h2 h3
  rw [h2, Pi.neg_apply, ← h3]

/-! ### The VAR forecast (2.44)–(2.45) -/

/-- The matrix geometric series of O&R footnote 28, p. 91: if `Σ_k A^k` converges then
`Σ_{k≥1} A^k = A (I − A)^{-1}`. -/
theorem tsum_pow_succ_eq_mul_inv {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : Summable fun k => A ^ k) :
    ∑' k, A ^ (k + 1) = A * (1 - A)⁻¹ := by
  rw [Matrix.inv_eq_left_inv hA.tsum_pow_mul_one_sub, ← hA.tsum_mul_left]
  simp only [pow_succ']

/-- A sufficient condition for the matrix geometric series of O&R footnote 28, p. 91, to
converge: every absolute row sum of `A` is below one (the `ℓ∞` operator norm `‖A‖ < 1`). -/
theorem summable_pow_of_rowSum_lt_one {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (h : ∀ i, ∑ j, |A i j| < 1) : Summable fun k => A ^ k := by
  let _ := Matrix.linftyOpNormedRing (n := n) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := n) (α := ℝ)
  have : CompleteSpace (Matrix n n ℝ) := FiniteDimensional.complete ℝ _
  have hA : ‖A‖ < 1 := by
    rw [Matrix.linfty_opNorm_def]
    have : (Finset.univ.sup fun i : n => ∑ j : n, ‖A i j‖₊) < 1 := by
      rw [Finset.sup_lt_iff (by simp)]
      intro i _
      rw [← NNReal.coe_lt_coe, NNReal.coe_sum]
      simpa [coe_nnnorm, Real.norm_eq_abs] using h i
    exact_mod_cast this
  exact summable_geometric_of_norm_lt_one hA

/-- With `Ψ` scaled by `1/(1+r)`, the summability of `Σ_k (Ψ/(1+r))^k` in O&R footnote 28,
p. 91, holds when every absolute row sum of the VAR matrix `Ψ` is below `1 + r`. -/
theorem summable_disc_smul_pow {n : Type*} [Fintype n] [DecidableEq n] {r : ℝ}
    (hr : 0 < 1 + r) {Ψ : Matrix n n ℝ} (h : ∀ i, ∑ j, |Ψ i j| < 1 + r) :
    Summable fun k => (disc r • Ψ) ^ k := by
  refine summable_pow_of_rowSum_lt_one fun i => ?_
  have hd := disc_pos hr
  simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hd, ← Finset.mul_sum]
  calc disc r * ∑ j, |Ψ i j| < disc r * (1 + r) := mul_lt_mul_of_pos_left (h i) hd
    _ = 1 := by rw [mul_comm, one_add_mul_disc hr]

/-- Iterated VAR forecasts, O&R p. 91: if `E_t x_{t+1} = Ψ x_t` at every date (the VAR (2.44)
with unpredictable errors) and `x_t` is known at `t`, then `E_t x_{t+k} = Ψ^k x_t` (law of
iterated expectations and linearity). -/
theorem condExp_var_pow [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {x : ℕ → Ω → Fin 2 → ℝ} {Ψ : Matrix (Fin 2) (Fin 2) ℝ} (hx : ∀ t, Integrable (x t) μ)
    (hvar : ∀ t, μ[x (t + 1) | ℱ t] =ᵐ[μ] fun ω => Ψ *ᵥ x t ω) {t : ℕ}
    (hxt : StronglyMeasurable[ℱ t] (x t)) (k : ℕ) :
    μ[x (t + k) | ℱ t] =ᵐ[μ] fun ω => (Ψ ^ k) *ᵥ x t ω := by
  induction k with
  | zero =>
    have h := condExp_of_stronglyMeasurable (μ := μ) (ℱ.le t) hxt (hx t)
    refine Eventually.of_forall fun ω => ?_
    simp only [add_zero, h, pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    let T : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin Ψ)
    have htow := condExp_condExp_of_le (μ := μ) (f := x (t + k + 1))
      (ℱ.mono (Nat.le_add_right t k)) (ℱ.le (t + k))
    have h1 := condExp_congr_ae (m := ℱ t) (hvar (t + k))
    have h2 := T.comp_condExp_comm (μ := μ) (m := ℱ t) (hx (t + k))
    have hT : (fun ω => Ψ *ᵥ x (t + k) ω) = T ∘ x (t + k) := by
      funext ω
      simp [T]
    rw [hT] at h1
    filter_upwards [htow, h1, h2, ih] with ω a b c d
    change μ[x (t + k + 1) | ℱ t] ω = _
    rw [← a, b, ← c, Function.comp_apply, d]
    simp [T, pow_succ', Matrix.mulVec_mulVec]

/-- The component forecast `E_t ΔZ_{t+k}`: the conditional expectation of the first coordinate
of `x_{t+k}` is the first coordinate of `E_t x_{t+k}` (premultiplication by `[1 0]`, p. 91). -/
theorem condExp_coord {m : MeasurableSpace Ω} {X : Ω → Fin 2 → ℝ}
    (hX : Integrable X μ) (i : Fin 2) :
    μ[fun ω => X ω i | m] =ᵐ[μ] fun ω => μ[X | m] ω i := by
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp_condExp_comm
    (μ := μ) (m := m) hX
  exact h.symm

/-- **O&R (2.45), p. 91, deterministic core.** For `A = Ψ/(1+r)` with convergent geometric
series, `−Σ_{s≥1} (1+r)^{-s} [1 0] Ψ^s v = −[1 0] (Ψ/(1+r)) (I − Ψ/(1+r))^{-1} v`. -/
theorem var_forecast_sum {r : ℝ} {Ψ : Matrix (Fin 2) (Fin 2) ℝ}
    (hsum : Summable fun k => (disc r • Ψ) ^ k) (v : Fin 2 → ℝ) :
    -∑' s, disc r ^ (s + 1) * ((Ψ ^ (s + 1)) *ᵥ v) 0 =
      -(((disc r • Ψ) * (1 - disc r • Ψ)⁻¹) *ᵥ v) 0 := by
  let L : Matrix (Fin 2) (Fin 2) ℝ →+ ℝ :=
    { toFun := fun B => (B *ᵥ v) 0
      map_zero' := by simp
      map_add' := fun B C => by simp [Matrix.add_mulVec] }
  have hL : Continuous L :=
    (continuous_apply 0).comp (continuous_id.matrix_mulVec continuous_const)
  have hs : Summable fun k => (disc r • Ψ) ^ (k + 1) := (summable_nat_add_iff 1).2 hsum
  rw [← tsum_pow_succ_eq_mul_inv hsum]
  have e : (((∑' k, (disc r • Ψ) ^ (k + 1)) *ᵥ v) 0) = L (∑' k, (disc r • Ψ) ^ (k + 1)) := rfl
  rw [e, hs.map_tsum L hL]
  congr 1
  refine tsum_congr fun s => ?_
  simp [L, smul_pow, Matrix.smul_mulVec]

/-- **O&R (2.45), p. 91.** Under the VAR (2.44) with `E_t x_{t+1} = Ψ x_t`, `x_t = (ΔZ_t, CA_t)`
known at `t`, and a convergent series `Σ_k (Ψ/(1+r))^k`, the model's predicted current account
`−Σ_{s>t} (1+r)^{-(s-t)} E_t ΔZ_s` equals `−[1 0] (Ψ/(1+r)) (I − Ψ/(1+r))^{-1} x_t` a.s. -/
theorem var_predicted_current_account [IsProbabilityMeasure μ] {r : ℝ}
    {ℱ : Filtration ℕ m0} {x : ℕ → Ω → Fin 2 → ℝ} {Ψ : Matrix (Fin 2) (Fin 2) ℝ}
    (hx : ∀ t, Integrable (x t) μ) (hvar : ∀ t, μ[x (t + 1) | ℱ t] =ᵐ[μ] fun ω => Ψ *ᵥ x t ω)
    {t : ℕ} (hxt : StronglyMeasurable[ℱ t] (x t)) (hsum : Summable fun k => (disc r • Ψ) ^ k) :
    (fun ω => -∑' s, disc r ^ (s + 1) * μ[fun ω' => x (t + s + 1) ω' 0 | ℱ t] ω) =ᵐ[μ]
      fun ω => -(((disc r • Ψ) * (1 - disc r • Ψ)⁻¹) *ᵥ x t ω) 0 := by
  have h1 : ∀ᵐ ω ∂μ, ∀ s, μ[fun ω' => x (t + s + 1) ω' 0 | ℱ t] ω = μ[x (t + s + 1) | ℱ t] ω 0 :=
    ae_all_iff.2 fun s => condExp_coord (hx _) 0
  have h2 : ∀ᵐ ω ∂μ, ∀ s, μ[x (t + (s + 1)) | ℱ t] ω = (Ψ ^ (s + 1)) *ᵥ x t ω :=
    ae_all_iff.2 fun s => condExp_var_pow hx hvar hxt (s + 1)
  filter_upwards [h1, h2] with ω h1 h2
  rw [← var_forecast_sum hsum]
  congr 2
  funext s
  rw [h1 s]
  exact congrArg (fun w => disc r ^ (s + 1) * w 0) (h2 s)

/-- **The restriction tested on p. 92.** If, in addition, the current account is the second VAR
coordinate and satisfies O&R (2.43), p. 90, with the VAR forecasts, then
`CA_t = [Φ_ΔZ Φ_CA] x_t` with `[Φ_ΔZ Φ_CA] = −[1 0] (Ψ/(1+r)) (I − Ψ/(1+r))^{-1}`, i.e. the
predicted and actual current accounts coincide almost surely. -/
theorem var_null_restriction [IsProbabilityMeasure μ] {r : ℝ}
    {ℱ : Filtration ℕ m0} {x : ℕ → Ω → Fin 2 → ℝ} {Ψ : Matrix (Fin 2) (Fin 2) ℝ}
    (hx : ∀ t, Integrable (x t) μ) (hvar : ∀ t, μ[x (t + 1) | ℱ t] =ᵐ[μ] fun ω => Ψ *ᵥ x t ω)
    {t : ℕ} (hxt : StronglyMeasurable[ℱ t] (x t)) (hsum : Summable fun k => (disc r • Ψ) ^ k)
    (h43 : (fun ω => x t ω 1) =ᵐ[μ]
      fun ω => -∑' s, disc r ^ (s + 1) * μ[fun ω' => x (t + s + 1) ω' 0 | ℱ t] ω) :
    (fun ω => x t ω 1) =ᵐ[μ] fun ω => -(((disc r • Ψ) * (1 - disc r • Ψ)⁻¹) *ᵥ x t ω) 0 :=
  h43.trans (var_predicted_current_account hx hvar hxt hsum)

end Stochastic

end ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Consumer durables and the current account

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§2.4, pp. 96–99. Date 0 stands for the book's date `t`. The consumer values
nondurables `C_s` and the end-of-period durables stock `D_s` by
`Σ β^s [γ log C_s + (1 − γ) log D_s]` (O&R (2.46)). Durables cost `p_s`,
depreciate at rate `δ`, and yield services in the period they are bought, so the
finance constraint is
`B_{s+1} − B_s = r B_s + Y_s − C_s − p_s[D_s − (1 − δ) D_{s−1}] − I_s − G_s`,
with `I_s = K_{s+1} − K_s`. The initial stock `D_{−1}` is the number `Dm`
(`prevStock`).

* **Euler equations** (p. 97): one-period perturbations of bonds and of durables
  that leave the finance constraint intact elsewhere have zero utility
  derivative at an optimum (`consumption_euler_of_isLocalMax`,
  `durable_euler_of_isLocalMax`).
* **User cost** (2.47): `(1 − γ)C_s/(γ D_s) = p_s − (1 − δ)p_{s+1}/(1 + r_{s+1}) = ι_s`.
* **Intertemporal budget constraint** (2.48), constant `r`: the combined stock
  `A_s = (1 + r)B_s + (1 − δ)p_s D_{s−1}` of bonds and resale value of durables
  obeys `A_{s+1} = (1 + r)(A_s + Z_s − C_s − ι_s D_s)` with `Z = Y − G − I`, so
  transversality on `A` is equivalent to
  `PV(C + ιD) = (1 + r)B_0 + (1 − δ)p_0 D_{−1} + PV(Y − G − I)` (`durables_ibc_iff`).
* **Consumption functions** (2.49) with `β(1 + r) = 1`.
* **Constant durables price** (2.50) and the lumpiness of durables purchases (p. 98).
* **The modified fundamental current-account equation** (2.51):
  `CA = (Y − Ỹ) − (I − Ĩ) − (G − G̃) + (ι − p)ΔD`, with `ι → p` as `δ → 1`.
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.Durables

open Filter Topology PresentValue FundamentalCurrentAccount

/-- The durables stock held at the start of date `s`, i.e. `D_{s−1}` (O&R p. 96); at date 0 it is
the initial stock `Dm = D_{t−1}`. -/
def prevStock (Dm : ℝ) (D : ℕ → ℝ) : ℕ → ℝ
  | 0 => Dm
  | s + 1 => D s

/-- The user cost of durables with a constant interest rate, O&R (2.47), p. 97:
`ι_s = p_s − (1 − δ) p_{s+1}/(1 + r)`. -/
noncomputable def userCost (r δ : ℝ) (p : ℕ → ℝ) (s : ℕ) : ℝ :=
  p s - (1 - δ) * p (s + 1) / (1 + r)

/-- Bonds plus the resale value of the depreciated durables stock at the start of date `s`,
`A_s = (1 + r) B_s + (1 − δ) p_s D_{s−1}`: the right side of O&R (2.48) at date `s`. -/
noncomputable def durableAssets (r δ Dm : ℝ) (B D p : ℕ → ℝ) (s : ℕ) : ℝ :=
  (1 + r) * B s + (1 - δ) * p s * prevStock Dm D s

/-- Durables-inclusive wealth `W^D = (1 + r)B_0 + (1 − δ)p_0 D_{−1} + PV(Y − G − I)`, the right side
of O&R (2.48), p. 97, built on the lifetime wealth of O&R (2.19). -/
noncomputable def durableWealth (r δ B0 p0 Dm : ℝ) (Y G I : ℕ → ℝ) : ℝ :=
  wealth r B0 Y G I + (1 - δ) * p0 * Dm

/-! ### Euler equations and the user cost -/

/-- **The durables perturbation is feasible**, O&R p. 97: buying `ε` more durables at date `s`
(paid out of nondurables) and selling the depreciated extra `(1 − δ)ε` at `s + 1` (spent on
nondurables) leaves total outlays `C + p[D − (1 − δ)D_{−1}]` unchanged at both dates, so the
bond path, and hence the finance constraint, is unaffected. -/
theorem durable_perturbation_feasible (Cs Cs1 Ds Ds1 Dprev ps ps1 δ ε : ℝ) :
    (Cs - ps * ε) + ps * ((Ds + ε) - (1 - δ) * Dprev) = Cs + ps * (Ds - (1 - δ) * Dprev) ∧
      (Cs1 + (1 - δ) * ps1 * ε) + ps1 * (Ds1 - (1 - δ) * (Ds + ε)) =
        Cs1 + ps1 * (Ds1 - (1 - δ) * Ds) := by
  constructor <;> ring

/-- **Utility derivative of the durables perturbation**, O&R p. 97: the utility terms of (2.46)
that the perturbation of `durable_perturbation_feasible` changes,
`γ log(C_s − p_s ε) + (1 − γ) log(D_s + ε) + βγ log(C_{s+1} + (1 − δ)p_{s+1} ε)`, have derivative
`(1 − γ)/D_s + β(1 − δ)γ p_{s+1}/C_{s+1} − γ p_s/C_s` at `ε = 0`. -/
theorem hasDerivAt_durable_perturbation {γ β δ Cs Cs1 Ds ps ps1 : ℝ} (hCs : Cs ≠ 0)
    (hCs1 : Cs1 ≠ 0) (hDs : Ds ≠ 0) :
    HasDerivAt (fun ε => γ * Real.log (Cs - ps * ε) + (1 - γ) * Real.log (Ds + ε) +
        β * (γ * Real.log (Cs1 + (1 - δ) * ps1 * ε)))
      ((1 - γ) / Ds + β * (1 - δ) * γ * ps1 / Cs1 - γ * ps / Cs) 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => Cs - ps * ε) (-ps) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul ps).const_sub Cs
    simpa using this
  have h2 : HasDerivAt (fun ε : ℝ => Ds + ε) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add Ds
  have h3 : HasDerivAt (fun ε : ℝ => Cs1 + (1 - δ) * ps1 * ε) ((1 - δ) * ps1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul ((1 - δ) * ps1)).const_add Cs1
  have l1 := (h1.log (by simpa using hCs)).const_mul γ
  have l2 := (h2.log (by simpa using hDs)).const_mul (1 - γ)
  have l3 := ((h3.log (by simpa using hCs1)).const_mul γ).const_mul β
  have := HasDerivAt.add (HasDerivAt.add l1 l2) l3
  refine this.congr_deriv ?_
  simp only [mul_zero, sub_zero, add_zero]
  field_simp
  ring

/-- **Durables Euler equation**, O&R p. 97: if the durables perturbation cannot raise utility
(local maximum at `ε = 0`; positive consumption and stock make the logs well defined), then
`γ p_s/C_s = (1 − γ)/D_s + β(1 − δ)γ p_{s+1}/C_{s+1}`. -/
theorem durable_euler_of_isLocalMax {γ β δ Cs Cs1 Ds ps ps1 : ℝ} (hCs : 0 < Cs)
    (hCs1 : 0 < Cs1) (hDs : 0 < Ds)
    (hmax : IsLocalMax (fun ε => γ * Real.log (Cs - ps * ε) + (1 - γ) * Real.log (Ds + ε) +
        β * (γ * Real.log (Cs1 + (1 - δ) * ps1 * ε))) 0) :
    γ * ps / Cs = (1 - γ) / Ds + β * (1 - δ) * γ * ps1 / Cs1 := by
  have := hmax.hasDerivAt_eq_zero
    (hasDerivAt_durable_perturbation (γ := γ) (β := β) (δ := δ) (ps := ps) (ps1 := ps1)
      hCs.ne' hCs1.ne' hDs.ne')
  linarith

/-- **Utility derivative of the bond perturbation**, O&R p. 97: lending `ε` more at date `s` and
consuming the proceeds `(1 + r_{s+1})ε` at `s + 1` changes utility by
`γ log(C_s − ε) + βγ log(C_{s+1} + (1 + r_{s+1})ε)`, with derivative
`βγ(1 + r_{s+1})/C_{s+1} − γ/C_s` at `ε = 0`. -/
theorem hasDerivAt_bond_perturbation {γ β r1 Cs Cs1 : ℝ} (hCs : Cs ≠ 0) (hCs1 : Cs1 ≠ 0) :
    HasDerivAt (fun ε => γ * Real.log (Cs - ε) + β * (γ * Real.log (Cs1 + (1 + r1) * ε)))
      (β * γ * (1 + r1) / Cs1 - γ / Cs) 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => Cs - ε) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub Cs
  have h3 : HasDerivAt (fun ε : ℝ => Cs1 + (1 + r1) * ε) (1 + r1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 + r1)).const_add Cs1
  have l1 := (h1.log (by simpa using hCs)).const_mul γ
  have l3 := ((h3.log (by simpa using hCs1)).const_mul γ).const_mul β
  refine (HasDerivAt.add l1 l3).congr_deriv ?_
  simp only [mul_zero, sub_zero, add_zero]
  field_simp
  ring

/-- **Nondurables Euler equation**, O&R p. 97: at an optimum of the bond perturbation, with
`γ > 0` and positive consumption, `C_{s+1} = (1 + r_{s+1}) β C_s`. -/
theorem consumption_euler_of_isLocalMax {γ β r1 Cs Cs1 : ℝ} (hγ : 0 < γ) (hCs : 0 < Cs)
    (hCs1 : 0 < Cs1)
    (hmax : IsLocalMax
      (fun ε => γ * Real.log (Cs - ε) + β * (γ * Real.log (Cs1 + (1 + r1) * ε))) 0) :
    Cs1 = (1 + r1) * β * Cs := by
  have h := hmax.hasDerivAt_eq_zero
    (hasDerivAt_bond_perturbation (γ := γ) (β := β) (r1 := r1) hCs.ne' hCs1.ne')
  have e : β * γ * (1 + r1) / Cs1 = γ / Cs := by linarith
  field_simp at e
  rw [← e]
  ring

/-- **The user cost of durables**, O&R (2.47), p. 97, with variable interest rates: combining
the two Euler equations (eliminating `C_{s+1}`),
`(1 − γ) C_s/(γ D_s) = p_s − (1 − δ) p_{s+1}/(1 + r_{s+1})`. Requires `γ ≠ 0`, `β ≠ 0`,
`1 + r_{s+1} ≠ 0` and nonzero consumption and stock. -/
theorem user_cost_of_euler {γ β δ r1 Cs Cs1 Ds ps ps1 : ℝ} (hγ : γ ≠ 0) (hβ : β ≠ 0)
    (hr : 1 + r1 ≠ 0) (hCs : Cs ≠ 0) (hDs : Ds ≠ 0)
    (hC : Cs1 = (1 + r1) * β * Cs)
    (hD : γ * ps / Cs = (1 - γ) / Ds + β * (1 - δ) * γ * ps1 / Cs1) :
    (1 - γ) * Cs / (γ * Ds) = ps - (1 - δ) * ps1 / (1 + r1) := by
  subst hC
  field_simp at hD ⊢
  linear_combination (-1 : ℝ) * hD

/-- The constant-rate user cost is the (2.47) expression with `r_{s+1} = r`. -/
theorem user_cost_of_euler_const {γ β δ r Ds : ℝ} {C p : ℕ → ℝ} {s : ℕ} (hγ : γ ≠ 0)
    (hβ : β ≠ 0) (hr : 1 + r ≠ 0) (hCs : C s ≠ 0) (hDs : Ds ≠ 0)
    (hC : C (s + 1) = (1 + r) * β * C s)
    (hD : γ * p s / C s = (1 - γ) / Ds + β * (1 - δ) * γ * p (s + 1) / C (s + 1)) :
    (1 - γ) * C s / (γ * Ds) = userCost r δ p s :=
  user_cost_of_euler hγ hβ hr hCs hDs hC hD

/-! ### The intertemporal budget constraint with durables -/

/-- **Law of motion of bonds plus durables**, O&R p. 97: the finance constraint of p. 96 with a
constant rate implies `A_{s+1} = (1 + r)A_s + (1 + r)(Y_s − G_s − I_s − C_s − ι_s D_s)`. -/
theorem durableAssets_succ {r δ Dm : ℝ} (hr : 1 + r ≠ 0) {B C D p Y G I : ℕ → ℝ}
    (hB : ∀ s, B (s + 1) = (1 + r) * B s + Y s - G s - I s - C s -
      p s * (D s - (1 - δ) * prevStock Dm D s)) (s : ℕ) :
    durableAssets r δ Dm B D p (s + 1) = (1 + r) * durableAssets r δ Dm B D p s +
      (1 + r) * (Y s - G s - I s - (C s + userCost r δ p s * D s)) := by
  unfold durableAssets userCost
  rw [hB s]
  simp only [prevStock]
  field_simp
  ring

/-- **The intertemporal budget constraint with durables**, O&R (2.48), p. 97 (constant `r`, as in
the book): given the finance constraint and summable present values, the transversality
condition `(1 + r)^{-n} A_n → 0` on bonds plus durables holds iff
`Σ (1 + r)^{-s}(C_s + ι_s D_s) = (1 + r)B_0 + (1 − δ)p_0 D_{−1} + Σ (1 + r)^{-s}(Y − G − I)_s`. -/
theorem durables_ibc_iff {r δ Dm : ℝ} (hr : 0 < 1 + r) {B C D p Y G I : ℕ → ℝ}
    (hB : ∀ s, B (s + 1) = (1 + r) * B s + Y s - G s - I s - C s -
      p s * (D s - (1 - δ) * prevStock Dm D s))
    (hZ : Summable fun s => disc r ^ s * (Y s - G s - I s))
    (hX : Summable fun s => disc r ^ s * (C s + userCost r δ p s * D s)) :
    Tendsto (fun n => disc r ^ n * durableAssets r δ Dm B D p n) atTop (𝓝 0) ↔
      pv r (fun s => C s + userCost r δ p s * D s) =
        (1 + r) * B 0 + (1 - δ) * p 0 * Dm + pv r (fun s => Y s - G s - I s) := by
  have key : ∀ s, disc r ^ (s + 1) * ((1 + r) * (Y s - G s - I s -
      (C s + userCost r δ p s * D s))) = disc r ^ s * (Y s - G s - I s) -
        disc r ^ s * (C s + userCost r δ p s * D s) := by
    intro s
    have := one_add_mul_disc hr
    rw [pow_succ]
    linear_combination (disc r ^ s * (Y s - G s - I s - (C s + userCost r δ p s * D s))) * this
  have hs : Summable fun s => disc r ^ (s + 1) * ((1 + r) * (Y s - G s - I s -
      (C s + userCost r δ p s * D s))) := by
    simp_rw [key]
    exact hZ.sub hX
  rw [discounted_tendsto_zero_iff hr (durableAssets_succ hr.ne' hB) hs]
  simp_rw [key]
  rw [hZ.tsum_sub hX]
  unfold pv durableAssets
  simp only [prevStock]
  constructor <;> intro e <;> linarith

/-- **Transversality on bonds and on durables**, O&R p. 97: if `(1 + r)^{-n} B_n → 0` and
`(1 + r)^{-n} p_n D_{n−1} → 0`, the combined condition of `durables_ibc_iff` holds. -/
theorem durableAssets_transversality {r δ Dm : ℝ} {B D p : ℕ → ℝ}
    (hB : Tendsto (fun n => disc r ^ n * B n) atTop (𝓝 0))
    (hpD : Tendsto (fun n => disc r ^ n * (p n * prevStock Dm D n)) atTop (𝓝 0)) :
    Tendsto (fun n => disc r ^ n * durableAssets r δ Dm B D p n) atTop (𝓝 0) := by
  have := (hB.const_mul (1 + r)).add (hpD.const_mul (1 - δ))
  simp only [mul_zero, add_zero] at this
  refine this.congr (fun n => ?_)
  unfold durableAssets
  ring

/-! ### Consumption functions with `β = 1/(1 + r)` -/

/-- **Flat nondurables consumption**, O&R p. 98: with `β(1 + r) = 1` the Euler equation
`C_{s+1} = (1 + r)βC_s` makes nondurables consumption constant. -/
theorem flat_nondurables {r β : ℝ} {C : ℕ → ℝ} (hβ : β * (1 + r) = 1)
    (hE : ∀ s, C (s + 1) = (1 + r) * β * C s) (s : ℕ) : C s = C 0 := by
  induction s with
  | zero => rfl
  | succ n ih =>
    rw [hE n, ih]
    linear_combination C 0 * hβ

/-- **Nondurables consumption function**, O&R (2.49), p. 98: with flat nondurables consumption, the
user-cost relation `γ ι_s D_s = (1 − γ)C_s` of (2.47), and the budget constraint (2.48)
`PV(C + ιD) = W^D`, nondurables consumption is `C_t = γ r W^D/(1 + r)`. -/
theorem nondurables_consumption {r γ δ WD : ℝ} (hr : 0 < r) (hγ : γ ≠ 0) {C D p : ℕ → ℝ}
    (hflat : ∀ s, C s = C 0) (hι : ∀ s, γ * (userCost r δ p s * D s) = (1 - γ) * C s)
    (hibc : pv r (fun s => C s + userCost r δ p s * D s) = WD) :
    C 0 = γ * r / (1 + r) * WD := by
  have e : ∀ s, C s + userCost r δ p s * D s = C 0 / γ := by
    intro s
    have := hι s
    rw [hflat s] at this ⊢
    field_simp
    linear_combination this
  simp_rw [e, pv_const hr] at hibc
  rw [← hibc]
  have : (1 : ℝ) + r ≠ 0 := by linarith
  field_simp

/-- **Durables consumption function**, O&R (2.49), p. 98: under the hypotheses of
`nondurables_consumption`, and with a nonzero user cost, the durables stock at every date is
`D_s = (1 − γ) r W^D/(ι_s (1 + r))`; the book states it at `s = t`. -/
theorem durables_consumption {r γ δ WD : ℝ} (hr : 0 < r) (hγ : γ ≠ 0) {C D p : ℕ → ℝ}
    (hflat : ∀ s, C s = C 0) (hι : ∀ s, γ * (userCost r δ p s * D s) = (1 - γ) * C s)
    (hibc : pv r (fun s => C s + userCost r δ p s * D s) = WD) (s : ℕ)
    (hιs : userCost r δ p s ≠ 0) :
    D s = (1 - γ) * r * WD / (userCost r δ p s * (1 + r)) := by
  have hC := nondurables_consumption hr hγ hflat hι hibc
  have h := hι s
  rw [hflat s, hC] at h
  have : (1 : ℝ) + r ≠ 0 := by linarith
  field_simp
  field_simp at h
  linear_combination h

/-! ### A constant price of durables -/

/-- **Constant user cost**, O&R (2.50), p. 98: with a constant durables price `p`,
`ι = p(r + δ)/(1 + r)`. -/
theorem userCost_const {r δ p0 : ℝ} (hr : 1 + r ≠ 0) {p : ℕ → ℝ} (hp : ∀ s, p s = p0) (s : ℕ) :
    userCost r δ p s = p0 * (r + δ) / (1 + r) := by
  unfold userCost
  rw [hp s, hp (s + 1)]
  field_simp
  ring

/-- **The durables price and the consumption ratio**, O&R (2.50), p. 98: with a constant price
the user-cost relation `(1 − γ)C = γ ι D` gives `p = ((1 + r)/(r + δ))((1 − γ)/γ)(C/D)`
(for `r + δ ≠ 0`, `γ ≠ 0`, `D ≠ 0`). -/
theorem price_of_consumption_ratio {r δ γ p C D : ℝ} (hr : 1 + r ≠ 0) (hrδ : r + δ ≠ 0)
    (hγ : γ ≠ 0) (hD : D ≠ 0) (hι : γ * (p * (r + δ) / (1 + r) * D) = (1 - γ) * C) :
    p = (1 + r) / (r + δ) * ((1 - γ) / γ) * (C / D) := by
  field_simp
  field_simp at hι
  linear_combination hι

/-- **A constant durables stock**, O&R p. 98: with constant `p`, flat nondurables consumption
and the user-cost relation, and `p(r + δ) ≠ 0`, the durables stock is constant: the consumer
smooths the service flow. -/
theorem durables_stock_const {r δ γ p0 : ℝ} (hr : 1 + r ≠ 0) (hγ : γ ≠ 0)
    (hpι : p0 * (r + δ) ≠ 0) {C D p : ℕ → ℝ} (hp : ∀ s, p s = p0) (hflat : ∀ s, C s = C 0)
    (hι : ∀ s, γ * (userCost r δ p s * D s) = (1 - γ) * C s) (s : ℕ) : D s = D 0 := by
  have hs := hι s
  have h0 := hι 0
  rw [userCost_const hr hp, hflat s] at hs
  rw [userCost_const hr hp] at h0
  have hc : p0 * (r + δ) / (1 + r) ≠ 0 := div_ne_zero hpι hr
  have : γ * (p0 * (r + δ) / (1 + r)) * D s = γ * (p0 * (r + δ) / (1 + r)) * D 0 := by
    linear_combination hs - h0
  exact mul_left_cancel₀ (mul_ne_zero hγ hc) this

/-- **Durables expenditure after date `t` is replacement only**, O&R p. 98: under the hypotheses
of `durables_stock_const`, spending on durables at every date after `t` is `p δ D_t`, while the
date-`t` purchase is `p(D_t − (1 − δ)D_{t−1})`. Expenditures are not smoothed. -/
theorem durables_purchases_after_t {r δ γ p0 Dm : ℝ} (hr : 1 + r ≠ 0) (hγ : γ ≠ 0)
    (hpι : p0 * (r + δ) ≠ 0) {C D p : ℕ → ℝ} (hp : ∀ s, p s = p0) (hflat : ∀ s, C s = C 0)
    (hι : ∀ s, γ * (userCost r δ p s * D s) = (1 - γ) * C s) (s : ℕ) :
    p (s + 1) * (D (s + 1) - (1 - δ) * prevStock Dm D (s + 1)) = p0 * δ * D 0 := by
  simp only [prevStock]
  rw [hp, durables_stock_const hr hγ hpι hp hflat hι (s + 1),
    durables_stock_const hr hγ hpι hp hflat hι s]
  ring

/-- **Lump-sum durables purchases**, O&R p. 98: with constant `r` and `p` and no depreciation
(`δ = 0`, `p r ≠ 0`), all durables are bought at date `t`; purchases at every later date are
zero. -/
theorem durables_lump_sum {r γ p0 Dm : ℝ} (hr : 1 + r ≠ 0) (hγ : γ ≠ 0) (hpr : p0 * r ≠ 0)
    {C D p : ℕ → ℝ} (hp : ∀ s, p s = p0) (hflat : ∀ s, C s = C 0)
    (hι : ∀ s, γ * (userCost r 0 p s * D s) = (1 - γ) * C s) (s : ℕ) :
    p (s + 1) * (D (s + 1) - prevStock Dm D (s + 1)) = 0 := by
  have h := durables_purchases_after_t (Dm := Dm) hr hγ (by simpa using hpr) hp hflat hι s
  simpa using h

/-! ### The modified fundamental current-account equation -/

/-- The date-`t` current account with durables, O&R p. 98:
`CA_t = rB_t + Y_t − C_t − G_t − I_t − p[D_t − (1 − δ)D_{t−1}]`. -/
def currentAccountDurables (r δ B0 C0 p D0 Dm : ℝ) (Y G I : ℕ → ℝ) : ℝ :=
  currentAccount r B0 C0 Y G I - p * (D0 - (1 - δ) * Dm)

/-- **The modified fundamental current-account equation**, O&R (2.51), p. 99: with a constant
durables price `p`, nondurables consumption `C_t = γ r W^D/(1 + r)` from (2.49), and the
user-cost relation `(1 − γ)C_t = γ ι D_t` with `ι = p(r + δ)/(1 + r)` from (2.50),
`CA_t = (Y_t − Ỹ) − (I_t − Ĩ) − (G_t − G̃) + (ι − p)(D_t − D_{t−1})`. -/
theorem durables_current_account {r δ γ B0 C0 p D0 Dm : ℝ} (hr : 0 < r) (hγ : γ ≠ 0)
    {Y G I : ℕ → ℝ} (hY : Summable fun s => disc r ^ s * Y s)
    (hG : Summable fun s => disc r ^ s * G s) (hI : Summable fun s => disc r ^ s * I s)
    (hC : C0 = γ * r / (1 + r) * durableWealth r δ B0 p Dm Y G I)
    (hι : γ * (p * (r + δ) / (1 + r) * D0) = (1 - γ) * C0) :
    currentAccountDurables r δ B0 C0 p D0 Dm Y G I =
      (Y 0 - permanent r Y) - (I 0 - permanent r I) - (G 0 - permanent r G) +
        (p * (r + δ) / (1 + r) - p) * (D0 - Dm) := by
  have h0 := fundamental_current_account hr hY hG hI
    (C0 := r / (1 + r) * wealth r B0 Y G I) (B0 := B0) rfl
  have split : currentAccount r B0 C0 Y G I =
      currentAccount r B0 (r / (1 + r) * wealth r B0 Y G I) Y G I +
        (r / (1 + r) * wealth r B0 Y G I - C0) := by
    unfold currentAccount; ring
  rw [currentAccountDurables, split, h0]
  unfold durableWealth at hC
  have hr1 : (1 : ℝ) + r ≠ 0 := by linarith
  have e : γ * (r / (1 + r) * wealth r B0 Y G I - C0 - p * (D0 - (1 - δ) * Dm) -
      (p * (r + δ) / (1 + r) - p) * (D0 - Dm)) = 0 := by
    rw [hC] at hι ⊢
    field_simp at hι ⊢
    linear_combination (-γ) * hι
  have := (mul_eq_zero.1 e).resolve_left hγ
  linear_combination this

/-- **Full depreciation removes the durables term**, O&R p. 99: at `δ = 1` the user cost equals
the price, `ι_s = p_s`, for any price path. -/
theorem userCost_full_depreciation (r : ℝ) (p : ℕ → ℝ) (s : ℕ) : userCost r 1 p s = p s := by
  simp [userCost]

/-- **`ι → p` as `δ → 1`**, O&R p. 99: with a constant price, the user cost `p(r + δ)/(1 + r)`
tends to `p` as the depreciation rate tends to one. -/
theorem userCost_tendsto_price {r : ℝ} (hr : 1 + r ≠ 0) (p : ℝ) :
    Tendsto (fun δ : ℝ => p * (r + δ) / (1 + r)) (𝓝 1) (𝓝 p) := by
  have hc : Continuous fun δ : ℝ => p * (r + δ) / (1 + r) := by fun_prop
  have := hc.tendsto 1
  have e : p * (r + 1) / (1 + r) = p := by field_simp; ring
  rwa [e] at this

/-- **With full depreciation (2.51) reduces to (2.18)**, O&R p. 99: at `δ = 1` durables behave
like nondurables and the current account obeys the fundamental equation of O&R (2.18). -/
theorem durables_current_account_full_depreciation {r γ B0 C0 p D0 Dm : ℝ} (hr : 0 < r)
    (hγ : γ ≠ 0) {Y G I : ℕ → ℝ} (hY : Summable fun s => disc r ^ s * Y s)
    (hG : Summable fun s => disc r ^ s * G s) (hI : Summable fun s => disc r ^ s * I s)
    (hC : C0 = γ * r / (1 + r) * durableWealth r 1 B0 p Dm Y G I)
    (hι : γ * (p * (r + 1) / (1 + r) * D0) = (1 - γ) * C0) :
    currentAccountDurables r 1 B0 C0 p D0 Dm Y G I =
      (Y 0 - permanent r Y) - (I 0 - permanent r I) - (G 0 - permanent r G) := by
  rw [durables_current_account hr hγ hY hG hI hC hι]
  have : (1 : ℝ) + r ≠ 0 := by linarith
  have e : p * (r + 1) / (1 + r) - p = 0 := by field_simp; ring
  rw [e]
  ring

end ObstfeldRogoff.SmallOpenEconomyDynamics.Durables

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Firms, the labour market, and financial and human wealth

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §2.5.1,
pp. 99–105, footnotes 35–38, and Appendix 2B.1, pp. 121–123. Date 0 stands for the
book's date `t`; sequences are indexed from date 0.

* The consumer holds bonds `B` and firm shares `x`. The bond and share Euler equations give
  the arbitrage condition (2.53), `1 + r = (d_{s+1} + V_{s+1})/V_s`: `share_arbitrage_iff`.
  With it the finance constraint (2.52) becomes the financial-wealth accumulation equation
  `Q_{s+1} − Q_s = rQ_s + w_sL − C_s − G_s` for any share holdings, not only `x = 1`
  (`wealth_accumulation`), and the intertemporal budget constraint (2.55) is equivalent to
  the transversality condition on `Q` (`ibc_iff_transversality`).
* (2.56)–(2.57): the share price is the present value of dividends iff there is no bubble
  (`share_price_eq_pv_dividends_iff`, reusing `PresentValue.forward_solution_iff`).
* (2.58): the firm's first-order conditions `A_sF_L = w_s` (`labor_foc`) and
  `A_{s+1}F_K = r` (`capital_foc`), derived from optimality against one-date perturbations
  of the plan. Euler's theorem `F = K F_K + L F_L` is proved from degree-one homogeneity and
  differentiability (`euler_homogeneous`).
* (2.59): the firm's value equals next period's capital. The present value of dividends is
  `K_{t+1}` (`tendsto_pv_capital_dividends`), and more precisely
  `(1 + r)^{-n}V_n → V_0 − K_1`, so `V_0 = K_1` iff there is no bubble
  (`firm_value_eq_capital_iff`); then `V_s = K_{s+1}` at every date.
* (2.60)–(2.61) and the saving and current-account equations of pp. 104–105.
* Footnote 36 (Modigliani–Miller): firm borrowing leaves equity plus debt, and the consumer's
  wealth, unchanged (`modigliani_miller`, `modigliani_miller_consumer_wealth`).
* Appendix 2B.1: the iterated asset Euler equation (2.78) and the equivalence of its limit
  condition with (2.57). The book's argument that a positive limit cannot be an equilibrium
  is informal; we prove only that a positive limit means the price exceeds fundamentals and
  that nonnegative prices (free disposal, footnote 54) exclude a negative limit.
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth

open PresentValue Filter Topology Finset

/-! ## The consumer: arbitrage and financial wealth -/

/-- **Arbitrage between bonds and shares**, O&R (2.53), p. 101: given the bond Euler equation
`u'(C_s) = β(1 + r)u'(C_{s+1})` with `β > 0` and `u'(C_{s+1}) > 0`, the share Euler equation
`V_s u'(C_s) = (V_{s+1} + d_{s+1})βu'(C_{s+1})` holds iff `(1 + r)V_s = d_{s+1} + V_{s+1}`. -/
theorem share_arbitrage_iff {r β u u' V V' d' : ℝ} (hβ : 0 < β) (hu' : 0 < u')
    (hbond : u = β * (1 + r) * u') :
    V * u = (V' + d') * β * u' ↔ (1 + r) * V = d' + V' := by
  have hne : β * u' ≠ 0 := (mul_pos hβ hu').ne'
  rw [hbond]
  constructor
  · intro h
    apply mul_left_cancel₀ hne
    linear_combination h
  · intro h
    linear_combination β * u' * h

/-- The ex post return identity O&R (2.54), p. 101: under the arbitrage condition (2.53)
dated `s − 1`, dividends plus capital gains on `x_s` shares equal `rV_{s−1}x_s`. -/
theorem dividend_capital_gain_eq {r Vp Vs ds xs : ℝ} (harb : (1 + r) * Vp = ds + Vs) :
    ds * xs + (Vs - Vp) * xs = r * Vp * xs := by
  linear_combination -xs * harb

/-- **Financial-wealth accumulation**, O&R p. 101: if the finance constraint (2.52) holds at
date `s` and the arbitrage condition (2.53) held between `s − 1` and `s`, then financial wealth
`Q_{s+1} = B_{s+1} + V_s x_{s+1}` obeys `Q_{s+1} − Q_s = rQ_s + w_sL − C_s − G_s`, for arbitrary
share holdings `x_s, x_{s+1}`. -/
theorem wealth_accumulation {r Bs Bs1 Vp Vs xs xs1 ds wLs Cs Gs : ℝ}
    (h52 : Bs1 - Bs + Vs * xs1 - Vp * xs =
      r * Bs + ds * xs + (Vs - Vp) * xs + wLs - Cs - Gs)
    (harb : (1 + r) * Vp = ds + Vs) :
    (Bs1 + Vs * xs1) - (Bs + Vp * xs) = r * (Bs + Vp * xs) + wLs - Cs - Gs := by
  linear_combination h52 - xs * harb

/-- Initial financial wealth, O&R p. 101: at the initial date the finance constraint (2.52)
reads `Q_{t+1} = (1 + r)B_t + d_t x_t + V_t x_t + w_tL − C_t − G_t`; no arbitrage condition is
used, since an unanticipated shock may have occurred between `t − 1` and `t`. -/
theorem initial_financial_wealth {r B0 B1 Vm V0 x0 x1 d0 wL0 C0 G0 : ℝ}
    (h52 : B1 - B0 + V0 * x1 - Vm * x0 =
      r * B0 + d0 * x0 + (V0 - Vm) * x0 + wL0 - C0 - G0) :
    B1 + V0 * x1 = (1 + r) * B0 + d0 * x0 + V0 * x0 + wL0 - C0 - G0 := by
  linear_combination h52

/-- **The consumer's intertemporal budget constraint**, O&R (2.55), pp. 101–102. Let `Q (s+1)`
be financial wealth at the end of date `s`, `H_s = w_sL − G_s` after-tax labour income and
`W₀ = (1 + r)B_t + d_t x_t + V_t x_t`. If `Q_1 = W₀ + H_0 − C_0` and
`Q_{s+2} = (1 + r)Q_{s+1} + H_{s+1} − C_{s+1}`, then the transversality condition
`(1 + r)^{-T} Q_{T+1} → 0` holds iff `PV(C) = W₀ + PV(H)`. -/
theorem ibc_iff_transversality {r W0 : ℝ} (hr : 0 < 1 + r) {Q C H : ℕ → ℝ}
    (hQ1 : Q 1 = W0 + (H 0 - C 0))
    (hQ : ∀ s, Q (s + 2) = (1 + r) * Q (s + 1) + (H (s + 1) - C (s + 1)))
    (hC : Summable fun s => disc r ^ s * C s) (hH : Summable fun s => disc r ^ s * H s) :
    Tendsto (fun T => disc r ^ T * Q (T + 1)) atTop (𝓝 0) ↔ pv r C = W0 + pv r H := by
  have hHC : Summable fun s => disc r ^ s * (H s - C s) := by
    simpa [mul_sub] using hH.sub hC
  have hs : Summable fun s => disc r ^ (s + 1) * (H (s + 1) - C (s + 1)) :=
    (summable_nat_add_iff 1).mpr hHC
  rw [discounted_tendsto_zero_iff hr (A := fun s => Q (s + 1))
    (N := fun s => H (s + 1) - C (s + 1)) hQ hs]
  have hsplit : ∑' s, disc r ^ s * (H s - C s) =
      (H 0 - C 0) + ∑' s, disc r ^ (s + 1) * (H (s + 1) - C (s + 1)) := by
    rw [hHC.tsum_eq_zero_add]
    simp
  have hpv : ∑' s, disc r ^ s * (H s - C s) = pv r H - pv r C := by
    have := pv_sub hH hC
    unfold pv at this ⊢
    exact this
  rw [hQ1]
  constructor <;> intro e <;> linarith

/-- **The share price is the present value of dividends iff there is no bubble**,
O&R (2.56)–(2.57), p. 102, stated from the consumer's two Euler equations: with the bond Euler
equation `u'(C_s) = β(1 + r)u'(C_{s+1})` and the share Euler equation at every date,
`V_0 = Σ_{s≥1} (1 + r)^{-s} d_s` iff `(1 + r)^{-T} V_T → 0`. -/
theorem share_price_eq_pv_dividends_iff {r β : ℝ} (hr : 0 < 1 + r) (hβ : 0 < β)
    {u V d : ℕ → ℝ} (hu : ∀ s, 0 < u s)
    (hbond : ∀ s, u s = β * (1 + r) * u (s + 1))
    (hshare : ∀ s, V s * u s = (V (s + 1) + d (s + 1)) * β * u (s + 1))
    (hsum : Summable fun s => disc r ^ (s + 1) * d (s + 1)) :
    V 0 = ∑' s, disc r ^ (s + 1) * d (s + 1) ↔
      Tendsto (fun n => disc r ^ n * V n) atTop (𝓝 0) :=
  forward_solution_iff hr
    (fun s => (share_arbitrage_iff hβ (hu (s + 1)) (hbond s)).1 (hshare s)) hsum

/-! ## The firm -/

/-- The firm's dividend at date `s`, O&R p. 102: output less wages less investment,
`d_s = A_sF(K_s, L_s) − w_sL_s − (K_{s+1} − K_s)`. -/
def firmDividend (A w : ℕ → ℝ) (F : ℝ × ℝ → ℝ) (K L : ℕ → ℝ) (s : ℕ) : ℝ :=
  A s * F (K s, L s) - w s * L s - (K (s + 1) - K s)

/-- The firm's cum-dividend value `d_t + V_t = Σ_{s≥t} (1 + r)^{-(s-t)} d_s`, O&R p. 103, the
objective of the firm's hiring and investment decisions. -/
noncomputable def firmValue (r : ℝ) (A w : ℕ → ℝ) (F : ℝ × ℝ → ℝ) (K L : ℕ → ℝ) : ℝ :=
  ∑' s, disc r ^ s * firmDividend A w F K L s

/-- **The labour first-order condition** `A_sF_L(K_s, L_s) = w_s`, O&R p. 103, for every date
`s ≥ t`. Hypotheses: the plan's discounted dividends are summable, `F` has partial derivative
`F_L` in labour at `(K_s, L_s)`, and no change in date-`s` hiring raises the firm's value. -/
theorem labor_foc {r : ℝ} (hr : 0 < 1 + r) {A w K L : ℕ → ℝ} {F : ℝ × ℝ → ℝ}
    (hsum : Summable fun n => disc r ^ n * firmDividend A w F K L n) (s : ℕ) {FL : ℝ}
    (hFL : HasDerivAt (fun l => F (K s, l)) FL (L s))
    (hopt : ∀ l, firmValue r A w F K (Function.update L s l) ≤ firmValue r A w F K L) :
    A s * FL = w s := by
  set φ : ℝ → ℝ := fun l =>
    disc r ^ s * (A s * (F (K s, l) - F (K s, L s)) - w s * (l - L s)) with hφdef
  have hval : ∀ l, firmValue r A w F K (Function.update L s l) =
      firmValue r A w F K L + φ l := by
    intro l
    have hpt : (fun n => disc r ^ n * firmDividend A w F K (Function.update L s l) n) =
        fun n => disc r ^ n * firmDividend A w F K L n + if n = s then φ l else 0 := by
      funext n
      by_cases hn : n = s
      · subst hn
        simp [firmDividend, hφdef]
        ring
      · simp [firmDividend, hn]
    unfold firmValue
    rw [hpt, hsum.tsum_add (hasSum_ite_eq s (φ l)).summable, tsum_ite_eq]
  have hmax : IsLocalMax φ (L s) := by
    refine Filter.Eventually.of_forall fun l => ?_
    have h1 := hopt l
    rw [hval l] at h1
    simp [hφdef]
    linarith
  have hderiv : HasDerivAt φ (disc r ^ s * (A s * FL - w s * 1)) (L s) := by
    have h1 : HasDerivAt (fun l => A s * (F (K s, l) - F (K s, L s))) (A s * FL) (L s) :=
      HasDerivAt.const_mul (A s) (HasDerivAt.sub_const (F (K s, L s)) hFL)
    have h2 : HasDerivAt (fun l : ℝ => w s * (l - L s)) (w s * 1) (L s) :=
      HasDerivAt.const_mul (w s) (HasDerivAt.sub_const (L s) (hasDerivAt_id (L s)))
    exact HasDerivAt.const_mul (disc r ^ s) (HasDerivAt.sub h1 h2)
  have h0 := hmax.hasDerivAt_eq_zero hderiv
  have hd : disc r ^ s ≠ 0 := pow_ne_zero _ (disc_pos hr).ne'
  have := (mul_eq_zero.1 h0).resolve_left hd
  linarith

/-- **The capital first-order condition** `A_{s+1}F_K(K_{s+1}, L_{s+1}) = r`, O&R p. 103, for
every date after the first (capital `K_t` is predetermined). Hypotheses: the plan's
discounted dividends are summable, `F` has partial derivative `F_K` in capital at
`(K_{s+1}, L_{s+1})`, and no change in the capital stock chosen for date `s + 1` raises the
firm's value. -/
theorem capital_foc {r : ℝ} (hr : 0 < 1 + r) {A w K L : ℕ → ℝ} {F : ℝ × ℝ → ℝ}
    (hsum : Summable fun n => disc r ^ n * firmDividend A w F K L n) (s : ℕ) {FK : ℝ}
    (hFK : HasDerivAt (fun k => F (k, L (s + 1))) FK (K (s + 1)))
    (hopt : ∀ k, firmValue r A w F (Function.update K (s + 1) k) L ≤ firmValue r A w F K L) :
    A (s + 1) * FK = r := by
  set a : ℝ → ℝ := fun k => disc r ^ s * (-(k - K (s + 1))) with hadef
  set b : ℝ → ℝ := fun k => disc r ^ (s + 1) *
    (A (s + 1) * (F (k, L (s + 1)) - F (K (s + 1), L (s + 1))) + (k - K (s + 1))) with hbdef
  have hval : ∀ k, firmValue r A w F (Function.update K (s + 1) k) L =
      firmValue r A w F K L + a k + b k := by
    intro k
    have hpt : (fun n => disc r ^ n * firmDividend A w F (Function.update K (s + 1) k) L n) =
        fun n => (disc r ^ n * firmDividend A w F K L n + if n = s then a k else 0) +
          if n = s + 1 then b k else 0 := by
      funext n
      simp only [firmDividend, Function.update_apply, hadef, hbdef]
      by_cases h1 : n = s
      · subst h1
        simp
        ring
      · by_cases h2 : n = s + 1
        · subst h2
          simp
          ring
        · have h3 : n + 1 ≠ s + 1 := fun h => h1 (by omega)
          simp [h1, h2]
    unfold firmValue
    rw [hpt, (hsum.add (hasSum_ite_eq s (a k)).summable).tsum_add
      (hasSum_ite_eq (s + 1) (b k)).summable, hsum.tsum_add (hasSum_ite_eq s (a k)).summable,
      tsum_ite_eq, tsum_ite_eq]
  have hmax : IsLocalMax (fun k => a k + b k) (K (s + 1)) := by
    refine Filter.Eventually.of_forall fun k => ?_
    have h1 := hopt k
    rw [hval k] at h1
    simp [hadef, hbdef]
    linarith
  have hderiv : HasDerivAt (fun k => a k + b k)
      (disc r ^ s * (-1) + disc r ^ (s + 1) * (A (s + 1) * FK + 1)) (K (s + 1)) := by
    have ha : HasDerivAt a (disc r ^ s * (-1)) (K (s + 1)) :=
      HasDerivAt.const_mul (disc r ^ s)
        (HasDerivAt.neg (HasDerivAt.sub_const (K (s + 1)) (hasDerivAt_id (K (s + 1)))))
    have hb : HasDerivAt b (disc r ^ (s + 1) * (A (s + 1) * FK + 1)) (K (s + 1)) :=
      HasDerivAt.const_mul (disc r ^ (s + 1))
        (HasDerivAt.add
          (HasDerivAt.const_mul (A (s + 1))
            (HasDerivAt.sub_const (F (K (s + 1), L (s + 1))) hFK))
          (HasDerivAt.sub_const (K (s + 1)) (hasDerivAt_id (K (s + 1)))))
    exact HasDerivAt.add ha hb
  have h0 := hmax.hasDerivAt_eq_zero hderiv
  have hd : disc r ^ s ≠ 0 := pow_ne_zero _ (disc_pos hr).ne'
  have h1 : disc r * (A (s + 1) * FK + 1) = 1 := by
    have : disc r ^ s * (disc r * (A (s + 1) * FK + 1) - 1) = 0 := by
      rw [pow_succ] at h0
      linear_combination h0
    have := (mul_eq_zero.1 this).resolve_left hd
    linarith
  have h2 := one_add_mul_disc hr
  have : A (s + 1) * FK + 1 = 1 + r := by
    linear_combination (1 + r) * h1 - (A (s + 1) * FK + 1) * h2
  linarith

/-- **Euler's theorem for constant returns**, O&R p. 103 (via §1.5.1): if `F` is homogeneous
of degree one, `F(λK, λL) = λF(K, L)` for `λ > 0`, and differentiable at `(K, L)` with
derivative `D`, then `F(K, L) = K F_K + L F_L`, where `F_K = D(1, 0)` and `F_L = D(0, 1)`. -/
theorem euler_homogeneous {F : ℝ × ℝ → ℝ} {D : ℝ × ℝ →L[ℝ] ℝ} {K L : ℝ}
    (hF : HasFDerivAt F D (K, L))
    (hhom : ∀ c : ℝ, 0 < c → F (c * K, c * L) = c * F (K, L)) :
    F (K, L) = K * D (1, 0) + L * D (0, 1) := by
  have hγ : HasDerivAt (fun c : ℝ => c • ((K, L) : ℝ × ℝ)) ((1 : ℝ) • ((K, L) : ℝ × ℝ)) 1 :=
    HasDerivAt.smul_const (hasDerivAt_id (1 : ℝ)) ((K, L) : ℝ × ℝ)
  have hF' : HasFDerivAt F D ((fun c : ℝ => c • ((K, L) : ℝ × ℝ)) 1) := by
    simpa using hF
  have h1 := hF'.comp_hasDerivAt (1 : ℝ) hγ
  have h2 : HasDerivAt (fun c : ℝ => c * F (K, L)) (1 * F (K, L)) 1 :=
    HasDerivAt.mul_const (hasDerivAt_id (1 : ℝ)) (F (K, L))
  have hev : (fun c : ℝ => c * F (K, L)) =ᶠ[𝓝 1]
      (F ∘ fun c : ℝ => c • ((K, L) : ℝ × ℝ)) := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with c hc
    simp [hhom c hc]
  have h3 := h1.unique (h2.congr_of_eventuallyEq hev.symm)
  have hKL : ((K, L) : ℝ × ℝ) = K • ((1, 0) : ℝ × ℝ) + L • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  have hD : D (K, L) = K * D (1, 0) + L * D (0, 1) := by
    rw [hKL, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [one_smul] at h3
  linarith

/-- The Fréchet derivative's value `D(1, 0)` is the partial derivative `F_K` of O&R (2.58),
so `euler_homogeneous` and `capital_foc` refer to the same number. -/
theorem hasDerivAt_capital_partial {F : ℝ × ℝ → ℝ} {D : ℝ × ℝ →L[ℝ] ℝ} {K L : ℝ}
    (hF : HasFDerivAt F D (K, L)) : HasDerivAt (fun k => F (k, L)) (D (1, 0)) K := by
  have hc : HasDerivAt (fun k : ℝ => ((k, L) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) K :=
    HasDerivAt.prodMk (hasDerivAt_id K) (hasDerivAt_const K L)
  exact hF.comp_hasDerivAt K hc

/-- The Fréchet derivative's value `D(0, 1)` is the partial derivative `F_L` of O&R (2.58). -/
theorem hasDerivAt_labor_partial {F : ℝ × ℝ → ℝ} {D : ℝ × ℝ →L[ℝ] ℝ} {K L : ℝ}
    (hF : HasFDerivAt F D (K, L)) : HasDerivAt (fun l => F (K, l)) (D (0, 1)) L := by
  have hc : HasDerivAt (fun l : ℝ => ((K, l) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) L :=
    HasDerivAt.prodMk (hasDerivAt_const L K) (hasDerivAt_id L)
  exact hF.comp_hasDerivAt L hc

/-- **Dividends under the first-order conditions**, O&R p. 104: with Euler's theorem
`F = KF_K + LF_L` and `AF_K = r`, `AF_L = w`, the dividend is
`d_s = rK_s − (K_{s+1} − K_s) = (1 + r)K_s − K_{s+1}`. -/
theorem dividend_eq_of_foc {r A w F FK FL K L K' : ℝ} (heuler : F = K * FK + L * FL)
    (hK : A * FK = r) (hL : A * FL = w) :
    A * F - w * L - (K' - K) = (1 + r) * K - K' := by
  rw [heuler]
  linear_combination K * hK + L * hL

/-- **The present value of dividends is next period's capital**, O&R (2.59), p. 104: if
`d_{s+1} = (1 + r)K_{s+1} − K_{s+2}` and `(1 + r)^{-n}K_{n+1} → 0`, the partial sums of
`Σ_{s≥1} (1 + r)^{-s} d_s` converge to `K_1`. (The telescoping partial sums converge without
any summability hypothesis.) -/
theorem tendsto_pv_capital_dividends {r : ℝ} (hr : 0 < 1 + r) {K d : ℕ → ℝ}
    (hd : ∀ s, d (s + 1) = (1 + r) * K (s + 1) - K (s + 2))
    (hK : Tendsto (fun n => disc r ^ n * K (n + 1)) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ s ∈ range n, disc r ^ (s + 1) * d (s + 1)) atTop (𝓝 (K 1)) := by
  have hc := one_add_mul_disc hr
  have hpart : ∀ n, ∑ s ∈ range n, disc r ^ (s + 1) * d (s + 1) =
      K 1 - disc r ^ n * K (n + 1) := by
    intro n
    have : ∀ s ∈ range n, disc r ^ (s + 1) * d (s + 1) =
        disc r ^ s * K (s + 1) - disc r ^ (s + 1) * K (s + 1 + 1) := by
      intro s _
      rw [hd s, pow_succ]
      linear_combination disc r ^ s * K (s + 1) * hc
    rw [sum_congr rfl this, sum_range_sub' (fun s => disc r ^ s * K (s + 1))]
    simp
  simp_rw [hpart]
  simpa using tendsto_const_nhds.sub hK

/-- O&R (2.59) with an explicit summability hypothesis: the present value of dividends
`Σ_{s≥1} (1 + r)^{-s} d_s` equals `K_1`. -/
theorem pv_capital_dividends {r : ℝ} (hr : 0 < 1 + r) {K d : ℕ → ℝ}
    (hd : ∀ s, d (s + 1) = (1 + r) * K (s + 1) - K (s + 2))
    (hK : Tendsto (fun n => disc r ^ n * K (n + 1)) atTop (𝓝 0))
    (hsum : Summable fun s => disc r ^ (s + 1) * d (s + 1)) :
    ∑' s, disc r ^ (s + 1) * d (s + 1) = K 1 :=
  tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat (tendsto_pv_capital_dividends hr hd hK)

/-- **The firm's bubble term**, O&R pp. 102–104: under the arbitrage condition (2.53) and
dividends `d_{s+1} = (1 + r)K_{s+1} − K_{s+2}`, the gap `V_s − K_{s+1}` grows at exactly the
rate of interest: `V_s − K_{s+1} = (1 + r)^s (V_0 − K_1)`. -/
theorem firm_value_sub_capital {r : ℝ} {V K d : ℕ → ℝ}
    (harb : ∀ s, (1 + r) * V s = d (s + 1) + V (s + 1))
    (hd : ∀ s, d (s + 1) = (1 + r) * K (s + 1) - K (s + 2)) (s : ℕ) :
    V s - K (s + 1) = (1 + r) ^ s * (V 0 - K 1) := by
  induction s with
  | zero => simp
  | succ n ih =>
    have h1 := harb n
    rw [hd n] at h1
    rw [pow_succ]
    linear_combination -h1 + (1 + r) * ih

/-- The discounted firm value converges to the gap between price and capital:
`(1 + r)^{-n}V_n → V_0 − K_1`, given `(1 + r)^{-n}K_{n+1} → 0`. -/
theorem tendsto_firm_bubble {r : ℝ} (hr : 0 < 1 + r) {V K d : ℕ → ℝ}
    (harb : ∀ s, (1 + r) * V s = d (s + 1) + V (s + 1))
    (hd : ∀ s, d (s + 1) = (1 + r) * K (s + 1) - K (s + 2))
    (hK : Tendsto (fun n => disc r ^ n * K (n + 1)) atTop (𝓝 0)) :
    Tendsto (fun n => disc r ^ n * V n) atTop (𝓝 (V 0 - K 1)) := by
  have hc := one_add_mul_disc hr
  have heq : ∀ n, disc r ^ n * V n = (V 0 - K 1) + disc r ^ n * K (n + 1) := by
    intro n
    have h := firm_value_sub_capital harb hd n
    have hp : disc r ^ n * (1 + r) ^ n = 1 := by rw [← mul_pow, mul_comm, hc, one_pow]
    linear_combination disc r ^ n * h + (V 0 - K 1) * hp
  simp_rw [heq]
  simpa using tendsto_const_nhds.add hK

/-- **The firm's value equals its capital**, O&R (2.59), p. 104: given (2.53), the dividend
formula implied by the first-order conditions, and `(1 + r)^{-n}K_{n+1} → 0`, the firm's
ex-dividend value is `V_0 = K_1` iff the no-bubble condition (2.57) holds. -/
theorem firm_value_eq_capital_iff {r : ℝ} (hr : 0 < 1 + r) {V K d : ℕ → ℝ}
    (harb : ∀ s, (1 + r) * V s = d (s + 1) + V (s + 1))
    (hd : ∀ s, d (s + 1) = (1 + r) * K (s + 1) - K (s + 2))
    (hK : Tendsto (fun n => disc r ^ n * K (n + 1)) atTop (𝓝 0)) :
    V 0 = K 1 ↔ Tendsto (fun n => disc r ^ n * V n) atTop (𝓝 0) := by
  have h := tendsto_firm_bubble hr harb hd hK
  constructor
  · intro e
    simpa [e] using h
  · intro e
    have := tendsto_nhds_unique h e
    linarith

/-- O&R (2.59) at every date: without a bubble, `V_s = K_{s+1}` for all `s`. -/
theorem firm_value_eq_capital {r : ℝ} (hr : 0 < 1 + r) {V K d : ℕ → ℝ}
    (harb : ∀ s, (1 + r) * V s = d (s + 1) + V (s + 1))
    (hd : ∀ s, d (s + 1) = (1 + r) * K (s + 1) - K (s + 2))
    (hK : Tendsto (fun n => disc r ^ n * K (n + 1)) atTop (𝓝 0))
    (hnb : Tendsto (fun n => disc r ^ n * V n) atTop (𝓝 0)) (s : ℕ) :
    V s = K (s + 1) := by
  have h0 := (firm_value_eq_capital_iff hr harb hd hK).2 hnb
  have := firm_value_sub_capital harb hd s
  rw [h0, sub_self, mul_zero] at this
  linarith

/-! ## Financial and human wealth -/

/-- **Financial wealth is net foreign assets plus capital**, O&R p. 104: with `x = 1` and
`V_s = K_{s+1}`, `Q_{s+1} = B_{s+1} + V_s x_{s+1} = B_{s+1} + K_{s+1}`. -/
theorem financial_wealth_eq_bonds_add_capital {B1 V0 K1 : ℝ} (hV : V0 = K1) :
    B1 + V0 * 1 = B1 + K1 := by
  rw [hV, mul_one]

/-- **The budget constraint in financial and human wealth**, O&R (2.60) with footnote 38,
p. 104: if `PV(C) = (1 + r)B_t + d_t + V_t + PV(wL − G)` (the constraint (2.55) with `x = 1`),
`d_t = Y_t − w_tL − (K_{t+1} − K_t)` and `V_t = K_{t+1}`, then
`PV(C) = (1 + r)B_t + K_t + (Y_t − w_tL) + PV(wL − G)`. -/
theorem ibc_financial_human_wealth {r B0 K0 K1 Y0 wL0 d0 V0 : ℝ} {C H : ℕ → ℝ}
    (hibc : pv r C = (1 + r) * B0 + d0 + V0 + pv r H)
    (hd0 : d0 = Y0 - wL0 - (K1 - K0)) (hV0 : V0 = K1) :
    pv r C = (1 + r) * B0 + K0 + (Y0 - wL0) + pv r H := by
  rw [hibc, hd0, hV0]
  ring

/-- **O&R (2.60)**, p. 104: if in addition the ex post return to capital between `t − 1` and
`t` was `r`, i.e. `Y_t − w_tL = rK_t`, then `PV(C) = (1 + r)Q_t + PV(wL − G)` with
`Q_t = B_t + K_t`. -/
theorem ibc_financial_human_wealth_expost {r B0 K0 K1 Y0 wL0 d0 V0 : ℝ} {C H : ℕ → ℝ}
    (hibc : pv r C = (1 + r) * B0 + d0 + V0 + pv r H)
    (hd0 : d0 = Y0 - wL0 - (K1 - K0)) (hV0 : V0 = K1) (hY : Y0 - wL0 = r * K0) :
    pv r C = (1 + r) * (B0 + K0) + pv r H := by
  rw [ibc_financial_human_wealth hibc hd0 hV0, hY]
  ring

/-- **The consumption function in financial and human wealth**, O&R (2.61), p. 104: with
`β = 1/(1 + r)` consumption is flat; if the constant level `C̄` satisfies
`PV(C̄) = (1 + r)Q_t + PV(H)`, then
`C̄ = rQ_t + (r/(1 + r)) Σ (1 + r)^{-(s-t)} H_s = rQ_t + H̃`. -/
theorem consumption_financial_human {r Q0 Cbar : ℝ} (hr : 0 < r) {H : ℕ → ℝ}
    (hibc : pv r (fun _ => Cbar) = (1 + r) * Q0 + pv r H) :
    Cbar = r * Q0 + permanent r H := by
  rw [pv_const hr] at hibc
  unfold permanent
  have h1 : (1 : ℝ) + r ≠ 0 := by linarith
  have h2 : Cbar = r / (1 + r) * ((1 + r) / r * Cbar) := by field_simp
  rw [h2, hibc]
  field_simp

/-- National saving in financial wealth, O&R p. 104: with `Y_t = rK_t + w_tL` (from
Euler's theorem plus the first-order conditions), saving `S_t = Y_t + rB_t − C_t − G_t` equals
`rQ_t + w_tL − G_t − C_t` with `Q_t = B_t + K_t`. -/
theorem saving_eq_financial {r B0 K0 Y0 wL0 C0 G0 : ℝ} (hY : Y0 = r * K0 + wL0) :
    Y0 + r * B0 - C0 - G0 = r * (B0 + K0) + wL0 - G0 - C0 := by
  rw [hY]
  ring

/-- **The permanent-income saving function**, O&R p. 105: if `S_t = rQ_t + w_tL_t − G_t − C_t`
and consumption follows (2.61), `C_t = rQ_t + (wL − G)~`, then
`S_t = [w_tL_t − (wL)~_t] − (G_t − G̃_t)`. -/
theorem saving_permanent {r Q0 S0 C0 : ℝ} {wL G : ℕ → ℝ}
    (hwL : Summable fun s => disc r ^ s * wL s) (hG : Summable fun s => disc r ^ s * G s)
    (hS : S0 = r * Q0 + wL 0 - G 0 - C0)
    (hC : C0 = r * Q0 + permanent r (fun s => wL s - G s)) :
    S0 = (wL 0 - permanent r wL) - (G 0 - permanent r G) := by
  rw [hS, hC, permanent_sub hwL hG]
  ring

/-- **The current account in terms of labour income**, O&R p. 104: with `CA_t = S_t − I_t`
and the saving function above, `CA_t = [w_tL_t − (wL)~_t] − (G_t − G̃_t) − I_t`. -/
theorem current_account_permanent {r Q0 S0 C0 I0 : ℝ} {wL G : ℕ → ℝ}
    (hwL : Summable fun s => disc r ^ s * wL s) (hG : Summable fun s => disc r ^ s * G s)
    (hS : S0 = r * Q0 + wL 0 - G 0 - C0)
    (hC : C0 = r * Q0 + permanent r (fun s => wL s - G s)) :
    S0 - I0 = (wL 0 - permanent r wL) - (G 0 - permanent r G) - I0 := by
  rw [saving_permanent hwL hG hS hC]

/-! ## Modigliani–Miller (footnote 36) -/

/-- **Modigliani–Miller**, O&R footnote 36, p. 102. Let the firm issue one-period debt
`D_{s+1}` at the end of date `s`, repaying `(1 + r)D_s` at date `s`, so equity holders receive
`d'_s = d_s + D_{s+1} − (1 + r)D_s`. If the unlevered value `V` and the equity value `V'` both
satisfy the arbitrage condition (2.53) with their dividends and the no-bubble condition
(2.57), and the firm's debt satisfies `(1 + r)^{-n}D_{n+1} → 0`, then equity plus debt equals
the unlevered value at every date: `V'_s + D_{s+1} = V_s`. -/
theorem modigliani_miller {r : ℝ} (hr : 0 < 1 + r) {V V' d d' D : ℕ → ℝ}
    (harb : ∀ s, (1 + r) * V s = d (s + 1) + V (s + 1))
    (harb' : ∀ s, (1 + r) * V' s = d' (s + 1) + V' (s + 1))
    (hd' : ∀ s, d' s = d s + D (s + 1) - (1 + r) * D s)
    (hnb : Tendsto (fun n => disc r ^ n * V n) atTop (𝓝 0))
    (hnb' : Tendsto (fun n => disc r ^ n * V' n) atTop (𝓝 0))
    (hD : Tendsto (fun n => disc r ^ n * D (n + 1)) atTop (𝓝 0)) (s : ℕ) :
    V' s + D (s + 1) = V s := by
  have hc := one_add_mul_disc hr
  set Δ : ℕ → ℝ := fun n => V n - (V' n + D (n + 1)) with hΔ
  have hstep : ∀ n, Δ (n + 1) = (1 + r) * Δ n := by
    intro n
    simp only [hΔ]
    have h1 := harb n
    have h2 := harb' n
    rw [hd' (n + 1)] at h2
    linear_combination -h1 + h2
  have hconst : ∀ n, disc r ^ n * Δ n = Δ 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hstep n, pow_succ, ← ih]
      linear_combination disc r ^ n * Δ n * hc
  have hlim : Tendsto (fun n => disc r ^ n * Δ n) atTop (𝓝 0) := by
    have := hnb.sub (hnb'.add hD)
    simp only [sub_self, add_zero] at this
    refine this.congr fun n => ?_
    simp only [hΔ]
    ring
  simp_rw [hconst] at hlim
  have h0 : Δ 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  have hd : disc r ^ s ≠ 0 := pow_ne_zero _ (disc_pos hr).ne'
  have hs : Δ s = 0 := by
    have := hconst s
    rw [h0] at this
    exact (mul_eq_zero.1 this).resolve_left hd
  simp only [hΔ] at hs
  linarith

/-- **Modigliani–Miller for the consumer**, O&R footnote 36: a consumer holding all shares and
the firm's maturing debt receives `d'_t + V'_t + (1 + r)D_t = d_t + V_t` at date `t` when
`V'_t + D_{t+1} = V_t`, so the initial wealth in (2.55) is unchanged by the firm's financing. -/
theorem modigliani_miller_consumer_wealth {r d0 d0' V0 V0' D0 D1 : ℝ}
    (hd' : d0' = d0 + D1 - (1 + r) * D0) (hV : V0' + D1 = V0) :
    d0' + V0' + (1 + r) * D0 = d0 + V0 := by
  rw [hd']
  linarith

/-! ## Appendix 2B.1: ruling out asset-price bubbles -/

/-- **The iterated asset Euler equation**, O&R Appendix 2B.1, p. 122: iterating
`V_s u'(C_s) = β(d_{s+1} + V_{s+1})u'(C_{s+1})` gives
`V_0 u'(C_0) = Σ_{s<n} β^{s+1}u'(C_{s+1})d_{s+1} + β^n u'(C_n)V_n`. -/
theorem iterated_asset_euler {β : ℝ} {u V d : ℕ → ℝ}
    (h : ∀ s, V s * u s = β * (d (s + 1) + V (s + 1)) * u (s + 1)) (n : ℕ) :
    V 0 * u 0 = ∑ s ∈ range n, β ^ (s + 1) * u (s + 1) * d (s + 1) + β ^ n * u n * V n := by
  induction n with
  | zero => simp [mul_comm]
  | succ n ih =>
    rw [sum_range_succ, ih, pow_succ]
    linear_combination β ^ n * h n

/-- **O&R (2.78)**, p. 122: if the discounted utility value of dividends is summable, the
limit `lim β^T u'(C_T)V_T` exists and
`V_0 u'(C_0) = Σ_{s≥1} β^s u'(C_s)d_s + lim β^T u'(C_T)V_T`. -/
theorem tendsto_iterated_asset_euler {β : ℝ} {u V d : ℕ → ℝ}
    (h : ∀ s, V s * u s = β * (d (s + 1) + V (s + 1)) * u (s + 1))
    (hsum : Summable fun s => β ^ (s + 1) * u (s + 1) * d (s + 1)) :
    Tendsto (fun n => β ^ n * u n * V n) atTop
      (𝓝 (V 0 * u 0 - ∑' s, β ^ (s + 1) * u (s + 1) * d (s + 1))) := by
  have heq : ∀ n, β ^ n * u n * V n =
      V 0 * u 0 - ∑ s ∈ range n, β ^ (s + 1) * u (s + 1) * d (s + 1) := by
    intro n
    linarith [iterated_asset_euler h n]
  simp_rw [heq]
  exact tendsto_const_nhds.sub hsum.hasSum.tendsto_sum_nat

/-- Discounted marginal utility under the bond Euler equation, O&R p. 123:
`u'(C_s) = β(1 + r)u'(C_{s+1})` for all `s` implies `β^T u'(C_T) = u'(C_0)(1 + r)^{-T}`. -/
theorem discounted_marginal_utility {r β : ℝ} (hr : 0 < 1 + r) {u : ℕ → ℝ}
    (hbond : ∀ s, u s = β * (1 + r) * u (s + 1)) (n : ℕ) :
    β ^ n * u n = u 0 * disc r ^ n := by
  have hc := one_add_mul_disc hr
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : β * u (n + 1) = disc r * u n := by
      rw [hbond n]
      linear_combination -(β * u (n + 1)) * hc
    rw [pow_succ, pow_succ, mul_assoc, h1]
    linear_combination disc r * ih

/-- **The utility-weighted no-bubble condition is (2.57)**, O&R p. 123: under the bond Euler
equation and `u'(C_0) > 0`, `β^T u'(C_T)V_T → 0` iff `(1 + r)^{-T}V_T → 0`. -/
theorem utility_bubble_iff {r β : ℝ} (hr : 0 < 1 + r) {u V : ℕ → ℝ} (hu0 : 0 < u 0)
    (hbond : ∀ s, u s = β * (1 + r) * u (s + 1)) :
    Tendsto (fun n => β ^ n * u n * V n) atTop (𝓝 0) ↔
      Tendsto (fun n => disc r ^ n * V n) atTop (𝓝 0) := by
  have heq : (fun n => β ^ n * u n * V n) = fun n => u 0 * (disc r ^ n * V n) := by
    funext n
    rw [discounted_marginal_utility hr hbond n]
    ring
  rw [heq]
  constructor
  · intro h
    have := h.const_mul (u 0)⁻¹
    simp only [mul_zero, ← mul_assoc, inv_mul_cancel₀ hu0.ne', one_mul] at this
    exact this
  · intro h
    simpa using h.const_mul (u 0)

/-- A **positive bubble term means the price exceeds fundamentals**, O&R p. 123: under (2.53),
`lim (1 + r)^{-T}V_T > 0` iff `V_0 > Σ_{s≥1} (1 + r)^{-s} d_s`. This is the provable content of
the book's informal argument that such a path cannot be an equilibrium. -/
theorem bubble_pos_iff_price_gt_pv {r : ℝ} (hr : 0 < 1 + r) {V d : ℕ → ℝ}
    (harb : ∀ s, (1 + r) * V s = d (s + 1) + V (s + 1))
    (hsum : Summable fun s => disc r ^ (s + 1) * d (s + 1)) {b : ℝ}
    (hb : Tendsto (fun n => disc r ^ n * V n) atTop (𝓝 b)) :
    0 < b ↔ ∑' s, disc r ^ (s + 1) * d (s + 1) < V 0 := by
  have := tendsto_nhds_unique hb (tendsto_bubble hr harb hsum)
  rw [this, sub_pos]

/-- **Free disposal excludes a negative bubble**, O&R footnote 54, p. 123: if the asset price
is never negative, any limit of `(1 + r)^{-T}V_T` is nonnegative, so
`V_0 ≥ Σ_{s≥1} (1 + r)^{-s} d_s`. -/
theorem price_ge_pv_of_nonneg {r : ℝ} (hr : 0 < 1 + r) {V d : ℕ → ℝ}
    (harb : ∀ s, (1 + r) * V s = d (s + 1) + V (s + 1))
    (hsum : Summable fun s => disc r ^ (s + 1) * d (s + 1)) (hV : ∀ s, 0 ≤ V s) :
    ∑' s, disc r ^ (s + 1) * d (s + 1) ≤ V 0 := by
  have h := tendsto_bubble hr harb hsum
  have : 0 ≤ V 0 - ∑' s, disc r ^ (s + 1) * d (s + 1) :=
    ge_of_tendsto' h fun n => mul_nonneg (pow_nonneg (disc_pos hr).le n) (hV n)
  linarith

end ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Solving systems of linear difference equations

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Supplement C to Chapter 2, pp. 726–741.

Time is discrete and indexed by `ℕ` (except for the backward solution SC(4), whose sum
runs to the infinite past and is therefore stated on `ℤ`). The book's scalar equation
SC(1), `z_t = a z_{t-1} + m_t`, is written `z (t+1) = a * z t + m (t+1)`.

* C.1 (scalar): particular solution SC(6), capital example SC(7), backward solution SC(4),
  forward solution SC(9), general solution SC(10), uniqueness of the bubble-free solution
  (under transversality, a growth bound, or boundedness) and the asset-price example.
* C.2 (2 × 2): characteristic roots SC(14), eigenvectors SC(15)–(16), decoupling SC(17),
  steady state SC(18), saddle-path existence and uniqueness SC(19)–(21), and the
  polynomial-factorisation form SC(22).
* C.3: the companion-matrix reduction of a second-order scalar equation.

The stochastic versions SC(11)–(12) and C.2.5 are not formalised (no probability here).
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations

open Filter Topology

/-! ## C.1 First-order scalar equations -/

/-- O&R SC(1), p. 726: `z` solves the first-order linear difference equation
`z_t = a z_{t-1} + m_t`, written forward one period on `ℕ`. -/
def ScalarSolves (a : ℝ) (m z : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, z (t + 1) = a * z t + m (t + 1)

/-- A real sequence is bounded (the book's "non-explosive"), O&R p. 730. -/
def SeqBounded (z : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ t : ℕ, |z t| ≤ M

/-- O&R SC(5), p. 727 (general solution, on `ℕ`): any two solutions of SC(1) with the same
forcing differ by a homogeneous term `b₀ aᵗ`, with `b₀` the difference of initial values. -/
theorem scalar_general_solution {a : ℝ} {m z w : ℕ → ℝ} (hz : ScalarSolves a m z)
    (hw : ScalarSolves a m w) (t : ℕ) : z t = w t + (z 0 - w 0) * a ^ t := by
  induction t with
  | zero => simp
  | succ n ih => rw [hz n, hw n, ih, pow_succ]; ring

/-- O&R p. 727 fn 11: the homogeneous equation `z_t = a z_{t-1}` has solutions `z₀ aᵗ`. -/
theorem scalar_homogeneous_solution {a : ℝ} {z : ℕ → ℝ} (hz : ScalarSolves a (fun _ => 0) z)
    (t : ℕ) : z t = z 0 * a ^ t := by
  have h0 : ScalarSolves a (fun _ => 0) (fun _ => 0) := fun _ => by ring
  simpa using scalar_general_solution hz h0 t

/-- O&R SC(5), p. 727: adding a homogeneous term `b₀ aᵗ` to a solution gives a solution. -/
theorem scalar_add_homogeneous {a : ℝ} {m z : ℕ → ℝ} (hz : ScalarSolves a m z) (b₀ : ℝ) :
    ScalarSolves a m (fun t => z t + b₀ * a ^ t) := by
  intro t; simp only; rw [hz t, pow_succ]; ring

/-- O&R SC(6), p. 728 (particular solution): a solution of SC(1) with initial value `z₀`
satisfies `z_t = ∑_{s=1}^t a^{t-s} m_s + aᵗ z₀`. Valid for every `a` (the book's remark that
SC(6) holds also for `|a| ≥ 1`). -/
theorem scalar_particular_solution {a : ℝ} {m z : ℕ → ℝ} (hz : ScalarSolves a m z) (t : ℕ) :
    z t = ∑ s ∈ Finset.Icc 1 t, a ^ (t - s) * m s + a ^ t * z 0 := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [hz n, ih, Finset.sum_Icc_succ_top (by omega), Nat.sub_self, pow_zero, one_mul,
      mul_add, Finset.mul_sum, pow_succ]
    have hs : ∀ s ∈ Finset.Icc 1 n, a * (a ^ (n - s) * m s) = a ^ (n + 1 - s) * m s := by
      intro s hs
      rw [Finset.mem_Icc] at hs
      rw [show n + 1 - s = n - s + 1 by omega, pow_succ]; ring
    rw [Finset.sum_congr rfl hs]; ring

/-- O&R SC(6), p. 728 (converse): the formula `∑_{s=1}^t a^{t-s} m_s + aᵗ c` solves SC(1). -/
theorem scalar_particular_solves (a c : ℝ) (m : ℕ → ℝ) :
    ScalarSolves a m (fun t => ∑ s ∈ Finset.Icc 1 t, a ^ (t - s) * m s + a ^ t * c) := by
  intro n
  simp only
  rw [Finset.sum_Icc_succ_top (by omega), Nat.sub_self, pow_zero, one_mul, mul_add,
    Finset.mul_sum, pow_succ]
  have hs : ∀ s ∈ Finset.Icc 1 n, a * (a ^ (n - s) * m s) = a ^ (n + 1 - s) * m s := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    rw [show n + 1 - s = n - s + 1 by omega, pow_succ]; ring
  rw [Finset.sum_congr rfl hs]; ring

/-- O&R SC(7), p. 728 (capital accumulation example): if `K_t = (1-δ) K_{t-1} + I_t` then
`K_t = ∑_{s=1}^t (1-δ)^{t-s} I_s + (1-δ)ᵗ K₀`. -/
theorem capital_accumulation_solution (δ : ℝ) {I K : ℕ → ℝ}
    (hK : ∀ t : ℕ, K (t + 1) = (1 - δ) * K t + I (t + 1)) (t : ℕ) :
    K t = ∑ s ∈ Finset.Icc 1 t, (1 - δ) ^ (t - s) * I s + (1 - δ) ^ t * K 0 :=
  scalar_particular_solution hK t

/-- O&R C.1.1, p. 726: with a stable root `|a| < 1` and bounded forcing `|m_t| ≤ M`, every
solution of SC(1) stays bounded, by `max |z₀| (M / (1 - |a|))`. -/
theorem scalar_stable_bounded {a M : ℝ} {m z : ℕ → ℝ} (hz : ScalarSolves a m z)
    (ha : |a| < 1) (hm : ∀ t, |m t| ≤ M) (t : ℕ) : |z t| ≤ max |z 0| (M / (1 - |a|)) := by
  have hpos : 0 < 1 - |a| := by linarith
  induction t with
  | zero => exact le_max_left _ _
  | succ n ih =>
    set B := max |z 0| (M / (1 - |a|))
    have hB : M ≤ (1 - |a|) * B := by
      have := le_max_right |z 0| (M / (1 - |a|))
      rw [div_le_iff₀ hpos] at this; linarith
    rw [hz n]
    calc |a * z n + m (n + 1)| ≤ |a| * |z n| + |m (n + 1)| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |a| * B + M := by
          gcongr
          exact hm _
      _ ≤ B := by linarith

/-- O&R SC(4), p. 727 (backward solution, on `ℤ`): `z_t = ∑_{s ≤ t} a^{t-s} m_s`, written
as `∑_{k ≥ 0} aᵏ m_{t-k}`. -/
noncomputable def backwardSolution (a : ℝ) (m : ℤ → ℝ) (t : ℤ) : ℝ :=
  ∑' k : ℕ, a ^ k * m (t - k)

/-- O&R SC(4), p. 727: for `|a| < 1` and bounded forcing, the backward solution solves
`z_t = a z_{t-1} + m_t` at every date `t ∈ ℤ`. -/
theorem scalar_backward_solution {a M : ℝ} {m : ℤ → ℝ} (ha : |a| < 1)
    (hm : ∀ t, |m t| ≤ M) (t : ℤ) :
    backwardSolution a m t = a * backwardSolution a m (t - 1) + m t := by
  have hsum : ∀ u : ℤ, Summable (fun k : ℕ => a ^ k * m (u - k)) := by
    intro u
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_left M) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_comm (M)]
    exact mul_le_mul_of_nonneg_left (hm _) (pow_nonneg (abs_nonneg a) k)
  unfold backwardSolution
  rw [(hsum t).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero]
  have : ∀ k : ℕ, a ^ (k + 1) * m (t - ((k + 1 : ℕ) : ℤ)) = a * (a ^ k * m (t - 1 - k)) := by
    intro k; rw [pow_succ]; push_cast; rw [show t - (k + 1) = t - 1 - k by ring]; ring
  simp only [this]; ring

/-- O&R SC(4)–(5), p. 727: for `|a| < 1` the backward solution is the only bounded solution
on `ℤ` (the homogeneous term `b₀ aᵗ` explodes as `t → -∞` unless `b₀ = 0`). -/
theorem scalar_backward_unique {a B : ℝ} {m z : ℤ → ℝ} (ha : |a| < 1)
    (hm : ∀ t, |m t| ≤ B) (hz : ∀ t, z t = a * z (t - 1) + m t)
    (hzb : ∀ t, |z t| ≤ B) (t : ℤ) : z t = backwardSolution a m t := by
  set w := backwardSolution a m
  have hw : ∀ t, w t = a * w (t - 1) + m t := scalar_backward_solution ha hm
  have hwb : ∀ t, |w t| ≤ B / (1 - |a|) := by
    intro u
    rw [← Real.norm_eq_abs, div_eq_mul_inv]
    refine tsum_of_norm_bounded (f := fun k : ℕ => a ^ k * m (u - k))
      ((hasSum_geometric_of_lt_one (abs_nonneg a) ha).mul_left B) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hm _) (pow_nonneg (abs_nonneg a) k)
  have hiter : ∀ n : ℕ, ∀ u : ℤ, z u - w u = a ^ n * (z (u - n) - w (u - n)) := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ k ih =>
      intro u
      rw [ih u, hz (u - k), hw (u - k)]
      push_cast
      rw [show u - k - 1 = u - (k + 1) by ring, pow_succ]; ring
  set C := B + B / (1 - |a|)
  have hbd : ∀ n : ℕ, |z t - w t| ≤ C * |a| ^ n := by
    intro n
    rw [hiter n t, abs_mul, abs_pow, mul_comm C]
    gcongr
    calc |z (t - n) - w (t - n)| ≤ |z (t - n)| + |w (t - n)| := abs_sub _ _
      _ ≤ C := add_le_add (hzb _) (hwb _)
  have hlim : Tendsto (fun n : ℕ => C * |a| ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).const_mul C
  have h0 : |z t - w t| ≤ 0 := ge_of_tendsto' hlim hbd
  have : z t - w t = 0 := abs_nonpos_iff.mp h0
  linarith

/-- O&R p. 730: if `|b₀| |a|ᵗ ≤ K gᵗ` for every `t` with `0 ≤ g < |a|`, then `b₀ = 0`.
This is the mechanism by which a non-explosiveness condition kills the bubble term. -/
theorem bubble_coeff_eq_zero {a b g K : ℝ} (hg : 0 ≤ g) (hga : g < |a|)
    (hb : ∀ t : ℕ, |b| * |a| ^ t ≤ K * g ^ t) : b = 0 := by
  have ha : 0 < |a| := lt_of_le_of_lt hg hga
  have hr0 : 0 ≤ g / |a| := div_nonneg hg ha.le
  have hr1 : g / |a| < 1 := (div_lt_one ha).mpr hga
  have hbd : ∀ t : ℕ, |b| ≤ K * (g / |a|) ^ t := by
    intro t
    have hpos : 0 < |a| ^ t := pow_pos ha t
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ hpos]
    exact hb t
  have hlim : Tendsto (fun t : ℕ => K * (g / |a|) ^ t) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul K
  have : |b| ≤ 0 := ge_of_tendsto' hlim hbd
  exact abs_nonpos_iff.mp this

/-- O&R SC(9), p. 729 (forward solution): `z_t = -∑_{s ≥ t+1} (1/a)^{s-t} m_s`, written as
`-∑_{k ≥ 0} (1/a)^{k+1} m_{t+1+k}`. -/
noncomputable def forwardSolution (a : ℝ) (m : ℕ → ℝ) (t : ℕ) : ℝ :=
  -∑' k : ℕ, (1 / a) ^ (k + 1) * m (t + 1 + k)

/-- O&R p. 729 fn 13: under the growth hypothesis `|m_t| ≤ M gᵗ` with `0 ≤ g < |a|`, each term
of the forward sum SC(9) is dominated by a geometric term with ratio `g / |a| < 1`. -/
theorem forward_term_bound {a g M : ℝ} {m : ℕ → ℝ} (hg : 0 ≤ g) (hga : g < |a|)
    (hm : ∀ t, |m t| ≤ M * g ^ t) (t k : ℕ) :
    |(1 / a) ^ (k + 1) * m (t + 1 + k)| ≤ M * g ^ (t + 1) / |a| * (g / |a|) ^ k := by
  have ha : 0 < |a| := lt_of_le_of_lt hg hga
  rw [abs_mul, abs_pow, abs_div, abs_one]
  calc (1 / |a|) ^ (k + 1) * |m (t + 1 + k)| ≤ (1 / |a|) ^ (k + 1) * (M * g ^ (t + 1 + k)) :=
        mul_le_mul_of_nonneg_left (hm _) (pow_nonneg (by positivity) _)
    _ = M * g ^ (t + 1) / |a| * (g / |a|) ^ k := by
        rw [div_pow, div_pow, pow_add, pow_succ]; field_simp; ring

/-- O&R p. 729 fn 13: under the growth hypothesis the forward sum SC(9) converges. -/
theorem forward_summable {a g M : ℝ} {m : ℕ → ℝ} (hg : 0 ≤ g) (hga : g < |a|)
    (hm : ∀ t, |m t| ≤ M * g ^ t) (t : ℕ) :
    Summable (fun k : ℕ => (1 / a) ^ (k + 1) * m (t + 1 + k)) := by
  have ha : 0 < |a| := lt_of_le_of_lt hg hga
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (div_nonneg hg ha.le)
    ((div_lt_one ha).mpr hga)).mul_left (M * g ^ (t + 1) / |a|)) (fun k => ?_)
  rw [Real.norm_eq_abs]
  exact forward_term_bound hg hga hm t k

/-- O&R SC(9), p. 729: under the growth hypothesis `|m_t| ≤ M gᵗ`, `0 ≤ g < |a|`, the forward
solution grows no faster than `gᵗ`: `|z_t| ≤ (M g / (|a| - g)) gᵗ`. -/
theorem forward_growth_bound {a g M : ℝ} {m : ℕ → ℝ} (hg : 0 ≤ g) (hga : g < |a|)
    (hm : ∀ t, |m t| ≤ M * g ^ t) (t : ℕ) :
    |forwardSolution a m t| ≤ M * g / (|a| - g) * g ^ t := by
  have ha : 0 < |a| := lt_of_le_of_lt hg hga
  have hr1 : g / |a| < 1 := (div_lt_one ha).mpr hga
  have hsub : 0 < |a| - g := by linarith
  unfold forwardSolution
  rw [abs_neg, ← Real.norm_eq_abs]
  have h := tsum_of_norm_bounded (f := fun k : ℕ => (1 / a) ^ (k + 1) * m (t + 1 + k))
    ((hasSum_geometric_of_lt_one (div_nonneg hg ha.le) hr1).mul_left (M * g ^ (t + 1) / |a|))
    (fun k => by rw [Real.norm_eq_abs]; exact forward_term_bound hg hga hm t k)
  refine h.trans (le_of_eq ?_)
  have h1 : 1 - g / |a| = (|a| - g) / |a| := by field_simp
  rw [h1, pow_succ]; field_simp

/-- O&R SC(9), p. 729: the forward solution solves SC(1) when `|a| > g ≥ 0` and the forcing
satisfies the growth hypothesis of fn 13. -/
theorem scalar_forward_solution {a g M : ℝ} {m : ℕ → ℝ} (hg : 0 ≤ g) (hga : g < |a|)
    (hm : ∀ t, |m t| ≤ M * g ^ t) : ScalarSolves a m (forwardSolution a m) := by
  have ha : a ≠ 0 := abs_pos.mp (lt_of_le_of_lt hg hga)
  intro t
  have e : ∀ k : ℕ, a * ((1 / a) ^ (k + 1) * m (t + 1 + k)) = (1 / a) ^ k * m (t + 1 + k) := by
    intro k; rw [pow_succ]; field_simp
  have hs : Summable (fun k : ℕ => (1 / a) ^ k * m (t + 1 + k)) := by
    simpa only [e] using (forward_summable hg hga hm t).mul_left a
  have hS : a * ∑' k : ℕ, (1 / a) ^ (k + 1) * m (t + 1 + k)
      = m (t + 1) + ∑' k : ℕ, (1 / a) ^ (k + 1) * m (t + 1 + 1 + k) := by
    rw [← tsum_mul_left]
    simp only [e]
    rw [hs.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, add_zero]
    congr 1
    exact tsum_congr (fun k => by rw [show t + 1 + (k + 1) = t + 1 + 1 + k by ring])
  unfold forwardSolution
  linarith

/-- O&R p. 730: a sequence growing no faster than `hᵗ` with `0 ≤ h < |a|` satisfies the
transversality (no-bubble) condition `z_T / a^T → 0`. -/
theorem transversality_of_growth {a h C : ℝ} {x : ℕ → ℝ} (hh : 0 ≤ h) (hha : h < |a|)
    (hx : ∀ t, |x t| ≤ C * h ^ t) : Tendsto (fun T : ℕ => x T / a ^ T) atTop (𝓝 0) := by
  have ha : 0 < |a| := lt_of_le_of_lt hh hha
  have hlim : Tendsto (fun T : ℕ => C * (h / |a|) ^ T) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hh ha.le)
      ((div_lt_one ha).mpr hha)).const_mul C
  refine squeeze_zero_norm (fun T => ?_) hlim
  rw [Real.norm_eq_abs, abs_div, abs_pow, div_pow, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (hx T) (pow_nonneg ha.le T)

/-- O&R SC(10), p. 730 (general solution for `|a| > 1`): every solution of SC(1) equals the
forward solution plus a bubble term `b₀ aᵗ`, with `b₀ = z₀ - (forward solution)₀`. -/
theorem scalar_forward_general_solution {a g M : ℝ} {m z : ℕ → ℝ} (hg : 0 ≤ g) (hga : g < |a|)
    (hm : ∀ t, |m t| ≤ M * g ^ t) (hz : ScalarSolves a m z) (t : ℕ) :
    z t = forwardSolution a m t + (z 0 - forwardSolution a m 0) * a ^ t :=
  scalar_general_solution hz (scalar_forward_solution hg hga hm) t

/-- O&R p. 730 (bubble-free uniqueness): under the growth hypothesis on `m`, a solution of SC(1)
satisfying the transversality condition `z_T / a^T → 0` is the forward solution SC(9),
i.e. `b₀ = 0` in SC(10). -/
theorem scalar_forward_unique_of_transversality {a g M : ℝ} {m z : ℕ → ℝ} (hg : 0 ≤ g)
    (hga : g < |a|) (hm : ∀ t, |m t| ≤ M * g ^ t) (hz : ScalarSolves a m z)
    (htv : Tendsto (fun T : ℕ => z T / a ^ T) atTop (𝓝 0)) (t : ℕ) :
    z t = forwardSolution a m t := by
  have ha : a ≠ 0 := abs_pos.mp (lt_of_le_of_lt hg hga)
  obtain ⟨b, hb_def⟩ : ∃ b, z 0 - forwardSolution a m 0 = b := ⟨_, rfl⟩
  have hf : Tendsto (fun T : ℕ => forwardSolution a m T / a ^ T + b) atTop (𝓝 (0 + b)) :=
    (transversality_of_growth hg hga (forward_growth_bound hg hga hm)).add_const b
  have heq : (fun T : ℕ => z T / a ^ T) = fun T => forwardSolution a m T / a ^ T + b := by
    funext T
    rw [scalar_forward_general_solution hg hga hm hz T, hb_def]
    field_simp
  rw [heq] at htv
  have hb : b = 0 := by simpa using tendsto_nhds_unique hf htv
  rw [scalar_forward_general_solution hg hga hm hz t, hb_def, hb, zero_mul, add_zero]

/-- O&R p. 730: under the growth hypothesis on `m`, the only solution of SC(1) that grows more
slowly than `|a|ᵗ` (here `|z_t| ≤ C hᵗ` with `0 ≤ h < |a|`) is the forward solution SC(9). -/
theorem scalar_forward_unique_of_growth {a g h M C : ℝ} {m z : ℕ → ℝ} (hg : 0 ≤ g)
    (hga : g < |a|) (hm : ∀ t, |m t| ≤ M * g ^ t) (hz : ScalarSolves a m z) (hh : 0 ≤ h)
    (hha : h < |a|) (hzC : ∀ t, |z t| ≤ C * h ^ t) (t : ℕ) : z t = forwardSolution a m t :=
  scalar_forward_unique_of_transversality hg hga hm hz (transversality_of_growth hh hha hzC) t

/-- O&R p. 730: with `|a| > 1` and bounded forcing, the forward solution SC(9) is the unique
bounded solution of SC(1). -/
theorem scalar_forward_unique_of_bounded {a M : ℝ} {m z : ℕ → ℝ} (ha : 1 < |a|)
    (hm : ∀ t, |m t| ≤ M) (hz : ScalarSolves a m z) (hzb : SeqBounded z) (t : ℕ) :
    z t = forwardSolution a m t := by
  obtain ⟨B, hB⟩ := hzb
  exact scalar_forward_unique_of_growth zero_le_one ha (fun s => by simpa using hm s) hz
    zero_le_one ha (fun s => by simpa using hB s) t

/-- O&R SC(9), p. 729: with `|a| > 1` and bounded forcing `|m_t| ≤ M`, the forward solution is
bounded, by `M / (|a| - 1)`. -/
theorem forward_bounded {a M : ℝ} {m : ℕ → ℝ} (ha : 1 < |a|) (hm : ∀ t, |m t| ≤ M) (t : ℕ) :
    |forwardSolution a m t| ≤ M / (|a| - 1) := by
  simpa using forward_growth_bound zero_le_one ha (fun s => by simpa using hm s) t

/-- O&R p. 730: with `|a| > 1` and bounded forcing, any nonzero bubble coefficient `b₀ ≠ 0`
in the general solution SC(10) makes the solution explode (it is unbounded). -/
theorem forward_plus_bubble_unbounded {a M b₀ : ℝ} {m : ℕ → ℝ} (ha : 1 < |a|)
    (hm : ∀ t, |m t| ≤ M) (hb₀ : b₀ ≠ 0) :
    ¬ SeqBounded (fun t => forwardSolution a m t + b₀ * a ^ t) := by
  intro hbd
  have hsol := scalar_add_homogeneous
    (scalar_forward_solution zero_le_one ha (fun s => by simpa using hm s)) b₀
  have h0 := scalar_forward_unique_of_bounded ha hm hsol hbd 0
  simp only [pow_zero, mul_one, add_eq_left] at h0
  exact hb₀ h0

/-- O&R p. 730 (asset-price example): if the ex-dividend value obeys
`V_t = (1+r) V_{t-1} - d_t` with `r > 0`, bounded dividends, and the no-bubble condition
`(1/(1+r))^T V_T → 0`, then `V_t = ∑_{s ≥ t+1} (1/(1+r))^{s-t} d_s`. -/
theorem asset_value_no_bubble {r M : ℝ} {d V : ℕ → ℝ} (hr : 0 < r) (hd : ∀ t, |d t| ≤ M)
    (hV : ∀ t, V (t + 1) = (1 + r) * V t - d (t + 1))
    (hnb : Tendsto (fun T : ℕ => (1 / (1 + r)) ^ T * V T) atTop (𝓝 0)) (t : ℕ) :
    V t = ∑' k : ℕ, (1 / (1 + r)) ^ (k + 1) * d (t + 1 + k) := by
  have ha : 1 < |1 + r| := by rw [abs_of_pos (by linarith)]; linarith
  have hsol : ScalarSolves (1 + r) (fun s => -d s) V := fun s => by rw [hV s]; ring
  have htv : Tendsto (fun T : ℕ => V T / (1 + r) ^ T) atTop (𝓝 0) := by
    refine hnb.congr (fun T => ?_)
    rw [div_pow, one_pow]; field_simp
  have h := scalar_forward_unique_of_transversality zero_le_one ha
    (fun s => by simpa using hd s) hsol htv t
  rw [h]
  unfold forwardSolution
  simp only [mul_neg, tsum_neg, neg_neg]

/-! ## C.2 First-order 2 × 2 systems

The system SC(13) is `z_t = A z_{t-1} + m_t` with `A = [[a₁₁, a₁₂], [a₂₁, a₂₂]]`, written in
components and forward one period. Throughout, `ω₁, ω₂` are real characteristic roots, given
through `ω₁ + ω₂ = tr A` and `ω₁ ω₂ = det A`, and the eigenvector of `ω_i` is `(e_i, 1)`. -/

/-- O&R SC(13), p. 732: `(z₁, z₂)` solves the 2 × 2 system `z_t = A z_{t-1} + m_t`. -/
def SystemSolves (a₁₁ a₁₂ a₂₁ a₂₂ : ℝ) (m₁ m₂ z₁ z₂ : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, z₁ (t + 1) = a₁₁ * z₁ t + a₁₂ * z₂ t + m₁ (t + 1) ∧
    z₂ (t + 1) = a₂₁ * z₁ t + a₂₂ * z₂ t + m₂ (t + 1)

/-- O&R SC(14), p. 733: if `ω₁ + ω₂ = tr A` and `ω₁ ω₂ = det A` then the characteristic
polynomial factors: `det (A - ω I) = (ω - ω₁)(ω - ω₂)`. -/
theorem charpoly_factor {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} (hsum : ω₁ + ω₂ = a₁₁ + a₂₂)
    (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) (ω : ℝ) :
    Matrix.det !![a₁₁ - ω, a₁₂; a₂₁, a₂₂ - ω] = (ω - ω₁) * (ω - ω₂) := by
  rw [Matrix.det_fin_two_of]
  linear_combination ω * hsum - hprod

/-- O&R SC(14), p. 733: under the same hypotheses `tr A = ω₁ + ω₂` and `det A = ω₁ ω₂`
in matrix form. -/
theorem trace_det_eq_roots {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} (hsum : ω₁ + ω₂ = a₁₁ + a₂₂)
    (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) :
    Matrix.trace !![a₁₁, a₁₂; a₂₁, a₂₂] = ω₁ + ω₂ ∧
      Matrix.det !![a₁₁, a₁₂; a₂₁, a₂₂] = ω₁ * ω₂ := by
  rw [Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  exact ⟨hsum.symm, hprod.symm⟩

/-- O&R SC(14), p. 733 (the derivation): two distinct roots of
`ω² - (tr A) ω + det A = 0` have sum `tr A` and product `det A`. -/
theorem vieta_of_distinct_roots {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} (hne : ω₁ ≠ ω₂)
    (h₁ : ω₁ ^ 2 - (a₁₁ + a₂₂) * ω₁ + (a₁₁ * a₂₂ - a₁₂ * a₂₁) = 0)
    (h₂ : ω₂ ^ 2 - (a₁₁ + a₂₂) * ω₂ + (a₁₁ * a₂₂ - a₁₂ * a₂₁) = 0) :
    ω₁ + ω₂ = a₁₁ + a₂₂ ∧ ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁ := by
  have hsub : (ω₁ - ω₂) * (ω₁ + ω₂ - (a₁₁ + a₂₂)) = 0 := by linear_combination h₁ - h₂
  have hsum : ω₁ + ω₂ = a₁₁ + a₂₂ := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · linarith
  refine ⟨hsum, ?_⟩
  linear_combination ω₁ * hsum - h₁

/-- O&R p. 733 and fn 15: the characteristic roots are real and distinct when
`(tr A)² > 4 det A`; they are `(tr A ± √((tr A)² - 4 det A)) / 2`. -/
theorem exists_distinct_real_roots {a₁₁ a₁₂ a₂₁ a₂₂ : ℝ}
    (hdisc : 4 * (a₁₁ * a₂₂ - a₁₂ * a₂₁) < (a₁₁ + a₂₂) ^ 2) :
    ∃ ω₁ ω₂ : ℝ, ω₂ < ω₁ ∧ ω₁ + ω₂ = a₁₁ + a₂₂ ∧ ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁ := by
  set Δ := (a₁₁ + a₂₂) ^ 2 - 4 * (a₁₁ * a₂₂ - a₁₂ * a₂₁)
  have hΔ : 0 < Δ := by simp only [Δ]; linarith
  have hsq : Real.sqrt Δ ^ 2 = Δ := Real.sq_sqrt hΔ.le
  have hpos : 0 < Real.sqrt Δ := Real.sqrt_pos.mpr hΔ
  refine ⟨((a₁₁ + a₂₂) + Real.sqrt Δ) / 2, ((a₁₁ + a₂₂) - Real.sqrt Δ) / 2, by linarith,
    by ring, ?_⟩
  linear_combination (-1 / 4 : ℝ) * hsq

/-- O&R p. 736: if `1 - tr A + det A < 0` (the characteristic polynomial is negative at 1)
then the roots are real and distinct, `(tr A)² > 4 det A`. -/
theorem discriminant_pos_of_charpoly_one_neg {a₁₁ a₁₂ a₂₁ a₂₂ : ℝ}
    (h : 1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁) < 0) :
    4 * (a₁₁ * a₂₂ - a₁₂ * a₂₁) < (a₁₁ + a₂₂) ^ 2 := by
  nlinarith [sq_nonneg (a₁₁ + a₂₂ - 2)]

/-- O&R SC(18), p. 734 and SC(14): `1 - tr A + det A = (1 - ω₁)(1 - ω₂)`. -/
theorem one_sub_trace_add_det {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} (hsum : ω₁ + ω₂ = a₁₁ + a₂₂)
    (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) :
    1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁) = (1 - ω₁) * (1 - ω₂) := by
  linear_combination hsum - hprod

/-- O&R p. 736 (the `q`-model argument, generalised): if `det A > 0` and
`1 - tr A + det A < 0`, the larger root exceeds one and the smaller lies in `(0, 1)`:
`0 < ω₂ < 1 < ω₁`. -/
theorem saddle_roots_of_charpoly_one_neg {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} (hle : ω₂ ≤ ω₁)
    (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (hdet : 0 < a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (h1 : 1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁) < 0) :
    0 < ω₂ ∧ ω₂ < 1 ∧ 1 < ω₁ := by
  rw [one_sub_trace_add_det hsum hprod] at h1
  have h21 : ω₂ < 1 ∧ 1 < ω₁ := by
    rcases lt_or_ge ω₂ 1 with h | h
    · refine ⟨h, ?_⟩
      by_contra hc
      push Not at hc
      nlinarith
    · nlinarith
  refine ⟨?_, h21⟩
  rw [← hprod] at hdet
  by_contra hc
  push Not at hc
  nlinarith

/-- O&R SC(14), p. 733: each `ω_i` with the stated sum and product is a root of the
characteristic equation `ω² - (tr A) ω + det A = 0`. -/
theorem charpoly_root {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} (hsum : ω₁ + ω₂ = a₁₁ + a₂₂)
    (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) :
    ω₁ ^ 2 - (a₁₁ + a₂₂) * ω₁ + (a₁₁ * a₂₂ - a₁₂ * a₂₁) = 0 ∧
      ω₂ ^ 2 - (a₁₁ + a₂₂) * ω₂ + (a₁₁ * a₂₂ - a₁₂ * a₂₁) = 0 := by
  constructor
  · linear_combination ω₁ * hsum - hprod
  · linear_combination ω₂ * hsum - hprod

/-- O&R SC(15), p. 733: for a root `ω` and `a₂₁ ≠ 0`, `e = (ω - a₂₂)/a₂₁` makes `(e, 1)` an
eigenvector: `a₁₁ e + a₁₂ = ω e` and `a₂₁ e + a₂₂ = ω`. -/
theorem eigvec_eq {a₁₁ a₁₂ a₂₁ a₂₂ ω e : ℝ} (ha₂₁ : a₂₁ ≠ 0)
    (hroot : ω ^ 2 - (a₁₁ + a₂₂) * ω + (a₁₁ * a₂₂ - a₁₂ * a₂₁) = 0)
    (he : e = (ω - a₂₂) / a₂₁) : a₁₁ * e + a₁₂ = ω * e ∧ a₂₁ * e + a₂₂ = ω := by
  subst he
  constructor
  · field_simp; linear_combination -hroot
  · field_simp; ring

/-- O&R SC(15), p. 733 (second form): if moreover `ω ≠ a₁₁` then also `e = a₁₂/(ω - a₁₁)`.
(The book's second expression needs `ω ≠ a₁₁`, which holds when `a₁₂ ≠ 0`; see
`root_ne_a11`.) -/
theorem eigvec_alt_form {a₁₁ a₁₂ a₂₁ a₂₂ ω e : ℝ} (ha₂₁ : a₂₁ ≠ 0)
    (hroot : ω ^ 2 - (a₁₁ + a₂₂) * ω + (a₁₁ * a₂₂ - a₁₂ * a₂₁) = 0)
    (he : e = (ω - a₂₂) / a₂₁) (hω : ω ≠ a₁₁) : e = a₁₂ / (ω - a₁₁) := by
  have h := (eigvec_eq ha₂₁ hroot he).1
  have hω' : ω - a₁₁ ≠ 0 := sub_ne_zero.mpr hω
  field_simp
  linear_combination -h

/-- O&R SC(15), p. 733: if `a₁₂ ≠ 0` and `a₂₁ ≠ 0`, no characteristic root equals `a₁₁`, so
both forms of SC(15) are defined. -/
theorem root_ne_a11 {a₁₁ a₁₂ a₂₁ a₂₂ ω : ℝ} (ha₁₂ : a₁₂ ≠ 0) (ha₂₁ : a₂₁ ≠ 0)
    (hroot : ω ^ 2 - (a₁₁ + a₂₂) * ω + (a₁₁ * a₂₂ - a₁₂ * a₂₁) = 0) : ω ≠ a₁₁ := by
  intro h
  subst h
  have : a₁₂ * a₂₁ = 0 := by linear_combination -hroot
  rcases mul_eq_zero.mp this with h | h
  · exact ha₁₂ h
  · exact ha₂₁ h

/-- O&R p. 733: distinct roots give distinct eigenvector slopes, `e₁ ≠ e₂`. -/
theorem eigvec_distinct {a₂₁ a₂₂ ω₁ ω₂ e₁ e₂ : ℝ} (ha₂₁ : a₂₁ ≠ 0) (hne : ω₁ ≠ ω₂)
    (he₁ : e₁ = (ω₁ - a₂₂) / a₂₁) (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁) : e₁ ≠ e₂ := by
  intro h
  apply hne
  rw [he₁, he₂] at h
  field_simp at h
  linarith

/-- O&R SC(16), p. 733: `E = [[e₁, e₂], [1, 1]]` has inverse `(e₁ - e₂)⁻¹ [[1, -e₂], [-1, e₁]]`
when `e₁ ≠ e₂`. -/
theorem eigvec_matrix_inverse {e₁ e₂ : ℝ} (he : e₁ ≠ e₂) :
    !![e₁, e₂; 1, 1] * ((e₁ - e₂)⁻¹ • !![1, -e₂; -1, e₁]) = 1 ∧
      ((e₁ - e₂)⁻¹ • !![1, -e₂; -1, e₁]) * !![e₁, e₂; 1, 1] = 1 := by
  have h : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr he
  constructor <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- O&R p. 734: `A E = E Ω` with `Ω = diag(ω₁, ω₂)`, for the eigenvectors of SC(15). -/
theorem eigvec_diagonalizes {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ e₁ e₂ : ℝ} (ha₂₁ : a₂₁ ≠ 0)
    (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (he₁ : e₁ = (ω₁ - a₂₂) / a₂₁) (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁) :
    !![a₁₁, a₁₂; a₂₁, a₂₂] * !![e₁, e₂; 1, 1] = !![e₁, e₂; 1, 1] * !![ω₁, 0; 0, ω₂] := by
  obtain ⟨r₁, r₂⟩ := charpoly_root hsum hprod
  obtain ⟨p₁, q₁⟩ := eigvec_eq ha₂₁ r₁ he₁
  obtain ⟨p₂, q₂⟩ := eigvec_eq ha₂₁ r₂ he₂
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    linarith

/-- O&R SC(18), p. 734: with constant forcing `(m₁, m₂)` and `1 - tr A + det A ≠ 0`, the
steady state `z̄₁ = ((1-a₂₂) m₁ + a₁₂ m₂)/(1 - tr A + det A)`,
`z̄₂ = (a₂₁ m₁ + (1-a₁₁) m₂)/(1 - tr A + det A)` is a fixed point of the system. -/
theorem steady_state {a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ : ℝ}
    (hD : 1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁) ≠ 0) :
    let z₁ := ((1 - a₂₂) * m₁ + a₁₂ * m₂) / (1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁))
    let z₂ := (a₂₁ * m₁ + (1 - a₁₁) * m₂) / (1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁))
    z₁ = a₁₁ * z₁ + a₁₂ * z₂ + m₁ ∧ z₂ = a₂₁ * z₁ + a₂₂ * z₂ + m₂ := by
  intro z₁ z₂
  have e₁ : z₁ * (1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁)) = (1 - a₂₂) * m₁ + a₁₂ * m₂ :=
    div_mul_cancel₀ _ hD
  have e₂ : z₂ * (1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁)) = a₂₁ * m₁ + (1 - a₁₁) * m₂ :=
    div_mul_cancel₀ _ hD
  constructor
  · apply mul_right_cancel₀ hD
    linear_combination (1 - a₁₁) * e₁ - a₁₂ * e₂
  · apply mul_right_cancel₀ hD
    linear_combination (1 - a₂₂) * e₂ - a₂₁ * e₁

/-- O&R SC(18), p. 734: when `1 - tr A + det A ≠ 0` the steady state is unique. -/
theorem steady_state_unique {a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ x₁ x₂ : ℝ}
    (hD : 1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁) ≠ 0)
    (h₁ : x₁ = a₁₁ * x₁ + a₁₂ * x₂ + m₁) (h₂ : x₂ = a₂₁ * x₁ + a₂₂ * x₂ + m₂) :
    x₁ = ((1 - a₂₂) * m₁ + a₁₂ * m₂) / (1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁)) ∧
      x₂ = (a₂₁ * m₁ + (1 - a₁₁) * m₂) / (1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁)) := by
  constructor
  · rw [eq_div_iff hD]; linear_combination (1 - a₂₂) * h₁ + a₁₂ * h₂
  · rw [eq_div_iff hD]; linear_combination a₂₁ * h₁ + (1 - a₁₁) * h₂

/-- O&R p. 736: with a saddle configuration `|ω₁| > 1 > |ω₂|`, no root equals one, so
`1 - tr A + det A ≠ 0` and the steady state SC(18) exists. -/
theorem charpoly_one_ne_zero_of_saddle {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ}
    (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (hω₁ : 1 < |ω₁|) (hω₂ : |ω₂| < 1) :
    1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁) ≠ 0 := by
  rw [one_sub_trace_add_det hsum hprod]
  refine mul_ne_zero (fun h => ?_) (fun h => ?_)
  · have : ω₁ = 1 := by linarith
    rw [this, abs_one] at hω₁; exact lt_irrefl _ hω₁
  · have : ω₂ = 1 := by linarith
    rw [this, abs_one] at hω₂; exact lt_irrefl _ hω₂

/-- O&R SC(17), p. 734 (decoupling, before dividing by `e₁ - e₂`): if `(z₁, z₂)` solves the
system then `z₁ - e₂ z₂` solves the scalar equation with root `ω₁` and forcing `m₁ - e₂ m₂`,
and `e₁ z₂ - z₁` solves the one with root `ω₂` and forcing `e₁ m₂ - m₁`. -/
theorem decouple {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ e₁ e₂ : ℝ} {m₁ m₂ z₁ z₂ : ℕ → ℝ} (ha₂₁ : a₂₁ ≠ 0)
    (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (he₁ : e₁ = (ω₁ - a₂₂) / a₂₁) (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁)
    (hz : SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ z₁ z₂) :
    ScalarSolves ω₁ (fun t => m₁ t - e₂ * m₂ t) (fun t => z₁ t - e₂ * z₂ t) ∧
      ScalarSolves ω₂ (fun t => e₁ * m₂ t - m₁ t) (fun t => e₁ * z₂ t - z₁ t) := by
  obtain ⟨r₁, r₂⟩ := charpoly_root hsum hprod
  obtain ⟨p₁, q₁⟩ := eigvec_eq ha₂₁ r₁ he₁
  obtain ⟨p₂, q₂⟩ := eigvec_eq ha₂₁ r₂ he₂
  constructor
  · intro t
    obtain ⟨h₁, h₂⟩ := hz t
    simp only
    rw [h₁, h₂]
    linear_combination (-z₁ t) * q₂ - z₁ t * hsum + z₂ t * p₂ + z₂ t * e₂ * hsum
  · intro t
    obtain ⟨h₁, h₂⟩ := hz t
    simp only
    rw [h₁, h₂]
    linear_combination z₁ t * q₁ + z₁ t * hsum - z₂ t * p₁ - z₂ t * e₁ * hsum

/-- O&R SC(17), p. 734 (dividing by `e₁ - e₂`): scaling a solution of SC(1) and its forcing
by a constant gives a solution. -/
theorem scalar_const_mul {a c : ℝ} {m z : ℕ → ℝ} (hz : ScalarSolves a m z) :
    ScalarSolves a (fun t => c * m t) (fun t => c * z t) := by
  intro t; simp only; rw [hz t]; ring

/-- O&R SC(17), p. 734 (the book's form): the transformed variables `z' = E⁻¹ z`, i.e.
`z'₁ = (z₁ - e₂ z₂)/(e₁ - e₂)` and `z'₂ = (e₁ z₂ - z₁)/(e₁ - e₂)`, obey the decoupled equations
`z'₁ₜ = ω₁ z'₁ₜ₋₁ + (m₁ₜ - e₂ m₂ₜ)/(e₁ - e₂)` and
`z'₂ₜ = ω₂ z'₂ₜ₋₁ + (e₁ m₂ₜ - m₁ₜ)/(e₁ - e₂)`. -/
theorem decoupled_system {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ e₁ e₂ : ℝ} {m₁ m₂ z₁ z₂ : ℕ → ℝ}
    (ha₂₁ : a₂₁ ≠ 0) (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (he₁ : e₁ = (ω₁ - a₂₂) / a₂₁) (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁)
    (hz : SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ z₁ z₂) :
    ScalarSolves ω₁ (fun t => (m₁ t - e₂ * m₂ t) / (e₁ - e₂))
        (fun t => (z₁ t - e₂ * z₂ t) / (e₁ - e₂)) ∧
      ScalarSolves ω₂ (fun t => (e₁ * m₂ t - m₁ t) / (e₁ - e₂))
        (fun t => (e₁ * z₂ t - z₁ t) / (e₁ - e₂)) := by
  obtain ⟨h₁, h₂⟩ := decouple ha₂₁ hsum hprod he₁ he₂ hz
  exact ⟨by simpa only [div_eq_inv_mul] using scalar_const_mul (c := (e₁ - e₂)⁻¹) h₁,
    by simpa only [div_eq_inv_mul] using scalar_const_mul (c := (e₁ - e₂)⁻¹) h₂⟩

/-- O&R p. 734 (`z = E z'`): the original variables are recovered from the decoupled ones as
`z₁ = e₁ z'₁ + e₂ z'₂` and `z₂ = z'₁ + z'₂`, when `e₁ ≠ e₂`. -/
theorem decoupled_reconstruct {e₁ e₂ x₁ x₂ : ℝ} (he : e₁ ≠ e₂) :
    x₁ = e₁ * ((x₁ - e₂ * x₂) / (e₁ - e₂)) + e₂ * ((e₁ * x₂ - x₁) / (e₁ - e₂)) ∧
      x₂ = (x₁ - e₂ * x₂) / (e₁ - e₂) + (e₁ * x₂ - x₁) / (e₁ - e₂) := by
  have h : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr he
  constructor <;> (field_simp; ring)

/-- O&R p. 737 (`z = E z'`, converse of SC(17)): solutions `y₁, y₂` of the two decoupled
scalar equations (unscaled forcings `m₁ - e₂ m₂` and `e₁ m₂ - m₁`) recombine into a solution
`z₁ = (e₁ y₁ + e₂ y₂)/(e₁ - e₂)`, `z₂ = (y₁ + y₂)/(e₁ - e₂)` of the system. -/
theorem recouple {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ e₁ e₂ : ℝ} {m₁ m₂ y₁ y₂ : ℕ → ℝ} (ha₂₁ : a₂₁ ≠ 0)
    (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) (hne : ω₁ ≠ ω₂)
    (he₁ : e₁ = (ω₁ - a₂₂) / a₂₁) (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁)
    (hy₁ : ScalarSolves ω₁ (fun t => m₁ t - e₂ * m₂ t) y₁)
    (hy₂ : ScalarSolves ω₂ (fun t => e₁ * m₂ t - m₁ t) y₂) :
    SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ (fun t => (e₁ * y₁ t + e₂ * y₂ t) / (e₁ - e₂))
      (fun t => (y₁ t + y₂ t) / (e₁ - e₂)) := by
  obtain ⟨r₁, r₂⟩ := charpoly_root hsum hprod
  obtain ⟨p₁, q₁⟩ := eigvec_eq ha₂₁ r₁ he₁
  obtain ⟨p₂, q₂⟩ := eigvec_eq ha₂₁ r₂ he₂
  have hd : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr (eigvec_distinct ha₂₁ hne he₁ he₂)
  intro t
  constructor
  · simp only
    rw [div_eq_iff hd, add_mul, add_mul, mul_assoc a₁₁, div_mul_cancel₀ _ hd, mul_assoc a₁₂,
      div_mul_cancel₀ _ hd, hy₁ t, hy₂ t]
    linear_combination (-y₁ t) * p₁ - y₂ t * p₂
  · simp only
    rw [div_eq_iff hd, add_mul, add_mul, mul_assoc a₂₁, div_mul_cancel₀ _ hd, mul_assoc a₂₂,
      div_mul_cancel₀ _ hd, hy₁ t, hy₂ t]
    linear_combination (-y₁ t) * q₁ - y₂ t * q₂

/-- O&R p. 737 (`z = E z'`): bounded sequences are closed under linear combinations, so
boundedness passes between original and decoupled variables. -/
theorem seqBounded_lin_comb {x y : ℕ → ℝ} (hx : SeqBounded x) (hy : SeqBounded y) (c d : ℝ) :
    SeqBounded (fun t => c * x t + d * y t) := by
  obtain ⟨A, hA⟩ := hx
  obtain ⟨B, hB⟩ := hy
  refine ⟨|c| * A + |d| * B, fun t => ?_⟩
  calc |c * x t + d * y t| ≤ |c * x t| + |d * y t| := abs_add_le _ _
    _ = |c| * |x t| + |d| * |y t| := by rw [abs_mul, abs_mul]
    _ ≤ |c| * A + |d| * B := by gcongr <;> simp [hA, hB]

/-- O&R SC(19)–(21), pp. 735–738 (saddle-path uniqueness): if `|ω₁| > 1`, two bounded
solutions of the system with the same forcing and the same initial value of the predetermined
variable `z₂` coincide. Hence the unstable coefficient `b₁₀` must vanish. (No condition on `ω₂`
is needed for uniqueness; `|ω₂| < 1` is needed only for existence, `saddle_path_exists`.) -/
theorem saddle_path_unique {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ e₁ e₂ : ℝ} {m₁ m₂ z₁ z₂ w₁ w₂ : ℕ → ℝ}
    (ha₂₁ : a₂₁ ≠ 0) (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (hne : ω₁ ≠ ω₂) (he₁ : e₁ = (ω₁ - a₂₂) / a₂₁) (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁)
    (hω₁ : 1 < |ω₁|) (hz : SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ z₁ z₂)
    (hw : SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ w₁ w₂) (hz₁ : SeqBounded z₁)
    (hz₂ : SeqBounded z₂) (hw₁ : SeqBounded w₁) (hw₂ : SeqBounded w₂) (h0 : z₂ 0 = w₂ 0)
    (t : ℕ) : z₁ t = w₁ t ∧ z₂ t = w₂ t := by
  obtain ⟨dz₁, dz₂⟩ := decouple ha₂₁ hsum hprod he₁ he₂ hz
  obtain ⟨dw₁, dw₂⟩ := decouple ha₂₁ hsum hprod he₁ he₂ hw
  have hd : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr (eigvec_distinct ha₂₁ hne he₁ he₂)
  set y₁ : ℕ → ℝ := fun t => (z₁ t - e₂ * z₂ t) - (w₁ t - e₂ * w₂ t)
  set y₂ : ℕ → ℝ := fun t => (e₁ * z₂ t - z₁ t) - (e₁ * w₂ t - w₁ t)
  have hy₁ : ScalarSolves ω₁ (fun _ => 0) y₁ := by
    intro s
    have a := dz₁ s
    have b := dw₁ s
    simp only [y₁] at a b ⊢
    linear_combination a - b
  have hy₂ : ScalarSolves ω₂ (fun _ => 0) y₂ := by
    intro s
    have a := dz₂ s
    have b := dw₂ s
    simp only [y₂] at a b ⊢
    linear_combination a - b
  have hy₁b : SeqBounded y₁ := by
    have h := seqBounded_lin_comb (seqBounded_lin_comb (seqBounded_lin_comb hz₁ hz₂ 1 (-e₂))
      (seqBounded_lin_comb hw₁ hw₂ 1 (-e₂)) 1 (-1)) hz₁ 1 0
    convert h using 2 with s
    simp only [y₁]; ring
  obtain ⟨K, hK⟩ := hy₁b
  have hy₁0 : y₁ 0 = 0 := by
    refine bubble_coeff_eq_zero zero_le_one hω₁ (K := K) (fun s => ?_)
    rw [← abs_pow, ← abs_mul, one_pow, mul_one, ← scalar_homogeneous_solution hy₁ s]
    exact hK s
  have hy₁t : ∀ s, y₁ s = 0 := fun s => by
    rw [scalar_homogeneous_solution hy₁ s, hy₁0, zero_mul]
  have hy₂0 : y₂ 0 = 0 := by
    have := hy₁0
    simp only [y₁, y₂] at this ⊢
    rw [h0] at this ⊢
    linarith
  have hy₂t : ∀ s, y₂ s = 0 := fun s => by
    rw [scalar_homogeneous_solution hy₂ s, hy₂0, zero_mul]
  have a := hy₁t t
  have b := hy₂t t
  simp only [y₁, y₂] at a b
  have h2 : (e₁ - e₂) * (z₂ t - w₂ t) = 0 := by linear_combination a + b
  have h2' : z₂ t = w₂ t := by
    have := (mul_eq_zero.mp h2).resolve_left hd
    linarith
  refine ⟨?_, h2'⟩
  rw [h2'] at a
  linarith

/-- O&R SC(20)–(21), pp. 737–738 (saddle-path existence, time-varying forcing): if
`|ω₁| > 1 > |ω₂|` and the forcing is bounded, then for every initial value `z₂₀` of the
predetermined variable there is a bounded solution of the system with `z₂ 0 = z₂₀`. It is built
by solving the unstable decoupled equation forward (SC(9), `b₁₀ = 0`) and the stable one
backward from the initial condition (SC(6)); by `saddle_path_unique` it is the only one. -/
theorem saddle_path_exists {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ e₁ e₂ M₁ M₂ : ℝ} {m₁ m₂ : ℕ → ℝ}
    (ha₂₁ : a₂₁ ≠ 0) (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (hne : ω₁ ≠ ω₂) (he₁ : e₁ = (ω₁ - a₂₂) / a₂₁) (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁)
    (hω₁ : 1 < |ω₁|) (hω₂ : |ω₂| < 1) (hm₁ : ∀ t, |m₁ t| ≤ M₁) (hm₂ : ∀ t, |m₂ t| ≤ M₂)
    (z₂₀ : ℝ) :
    ∃ z₁ z₂ : ℕ → ℝ, SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ z₁ z₂ ∧ SeqBounded z₁ ∧
      SeqBounded z₂ ∧ z₂ 0 = z₂₀ := by
  have hd : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr (eigvec_distinct ha₂₁ hne he₁ he₂)
  have hmb₁ : SeqBounded m₁ := ⟨M₁, hm₁⟩
  have hmb₂ : SeqBounded m₂ := ⟨M₂, hm₂⟩
  obtain ⟨N₁, hN₁⟩ := seqBounded_lin_comb hmb₁ hmb₂ 1 (-e₂)
  obtain ⟨N₂, hN₂⟩ := seqBounded_lin_comb hmb₂ hmb₁ e₁ (-1)
  have hn₁ : ∀ t, |m₁ t - e₂ * m₂ t| ≤ N₁ := fun t => by
    have := hN₁ t; simp only at this
    rwa [show 1 * m₁ t + -e₂ * m₂ t = m₁ t - e₂ * m₂ t by ring] at this
  have hn₂ : ∀ t, |e₁ * m₂ t - m₁ t| ≤ N₂ := fun t => by
    have := hN₂ t; simp only at this
    rwa [show e₁ * m₂ t + -1 * m₁ t = e₁ * m₂ t - m₁ t by ring] at this
  set y₁ := forwardSolution ω₁ (fun t => m₁ t - e₂ * m₂ t)
  have hy₁ : ScalarSolves ω₁ (fun t => m₁ t - e₂ * m₂ t) y₁ :=
    scalar_forward_solution zero_le_one hω₁ (fun s => by simpa using hn₁ s)
  set c := (e₁ - e₂) * z₂₀ - y₁ 0
  set y₂ : ℕ → ℝ := fun t =>
    ∑ s ∈ Finset.Icc 1 t, ω₂ ^ (t - s) * (e₁ * m₂ s - m₁ s) + ω₂ ^ t * c
  have hy₂ : ScalarSolves ω₂ (fun t => e₁ * m₂ t - m₁ t) y₂ := scalar_particular_solves ω₂ c _
  have hy₁b : SeqBounded y₁ := ⟨_, forward_bounded hω₁ hn₁⟩
  have hy₂b : SeqBounded y₂ := ⟨_, scalar_stable_bounded hy₂ hω₂ hn₂⟩
  refine ⟨fun t => (e₁ * y₁ t + e₂ * y₂ t) / (e₁ - e₂), fun t => (y₁ t + y₂ t) / (e₁ - e₂),
    recouple ha₂₁ hsum hprod hne he₁ he₂ hy₁ hy₂, ?_, ?_, ?_⟩
  · have h := seqBounded_lin_comb hy₁b hy₂b (e₁ / (e₁ - e₂)) (e₂ / (e₁ - e₂))
    convert h using 2 with t
    field_simp
  · have h := seqBounded_lin_comb hy₁b hy₂b (1 / (e₁ - e₂)) (1 / (e₁ - e₂))
    convert h using 2 with t
    field_simp
  · simp only [y₂, c]
    simp
    field_simp

/-- O&R SC(19), p. 736 (saddle path with constant forcing): let `|ω₁| > 1 > |ω₂|` and let
`(z̄₁, z̄₂)` be a steady state (SC(18)). Then the path
`z₁ₜ - z̄₁ = e₂ (z₂₀ - z̄₂) ω₂ᵗ`, `z₂ₜ - z̄₂ = (z₂₀ - z̄₂) ω₂ᵗ` solves the system, is bounded,
starts at `z₂₀`, lies on the saddle path `z₁ - z̄₁ = e₂ (z₂ - z̄₂)` and converges to the
steady state. -/
theorem saddle_path_constant_solves {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ e₂ m₁ m₂ x₁ x₂ : ℝ}
    (ha₂₁ : a₂₁ ≠ 0) (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁) (hω₂ : |ω₂| < 1)
    (hss₁ : x₁ = a₁₁ * x₁ + a₁₂ * x₂ + m₁) (hss₂ : x₂ = a₂₁ * x₁ + a₂₂ * x₂ + m₂) (z₂₀ : ℝ) :
    SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ (fun _ => m₁) (fun _ => m₂)
        (fun t => x₁ + e₂ * (z₂₀ - x₂) * ω₂ ^ t) (fun t => x₂ + (z₂₀ - x₂) * ω₂ ^ t) ∧
      SeqBounded (fun t => x₁ + e₂ * (z₂₀ - x₂) * ω₂ ^ t) ∧
      SeqBounded (fun t => x₂ + (z₂₀ - x₂) * ω₂ ^ t) ∧
      (∀ t : ℕ, (x₁ + e₂ * (z₂₀ - x₂) * ω₂ ^ t) - x₁ = e₂ * ((x₂ + (z₂₀ - x₂) * ω₂ ^ t) - x₂)) ∧
      Tendsto (fun t => x₁ + e₂ * (z₂₀ - x₂) * ω₂ ^ t) atTop (𝓝 x₁) ∧
      Tendsto (fun t => x₂ + (z₂₀ - x₂) * ω₂ ^ t) atTop (𝓝 x₂) := by
  obtain ⟨_, r₂⟩ := charpoly_root hsum hprod
  obtain ⟨p₂, q₂⟩ := eigvec_eq ha₂₁ r₂ he₂
  have hpow : ∀ t : ℕ, |ω₂ ^ t| ≤ 1 := fun t => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hω₂.le
  have hlim : Tendsto (fun t : ℕ => ω₂ ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_iff.mpr hω₂
  have hone : SeqBounded (fun _ => (1 : ℝ)) := ⟨1, fun _ => by simp⟩
  have hpb : SeqBounded (fun t => ω₂ ^ t) := ⟨1, hpow⟩
  refine ⟨fun t => ⟨?_, ?_⟩, ?_, ?_, fun t => by ring, ?_, ?_⟩
  · simp only; rw [pow_succ]
    linear_combination hss₁ - (z₂₀ - x₂) * ω₂ ^ t * p₂
  · simp only; rw [pow_succ]
    linear_combination hss₂ - (z₂₀ - x₂) * ω₂ ^ t * q₂
  · convert seqBounded_lin_comb hone hpb x₁ (e₂ * (z₂₀ - x₂)) using 2 with t; ring
  · convert seqBounded_lin_comb hone hpb x₂ (z₂₀ - x₂) using 2 with t; ring
  · simpa using (hlim.const_mul (e₂ * (z₂₀ - x₂))).const_add x₁
  · simpa using (hlim.const_mul (z₂₀ - x₂)).const_add x₂

/-- O&R SC(19), p. 736 (uniqueness of the saddle path, constant forcing): if
`|ω₁| > 1 > |ω₂|` and `(z̄₁, z̄₂)` is a steady state, every bounded solution with
`z₂ 0 = z₂₀` is `z₁ₜ = z̄₁ + e₂ (z₂₀ - z̄₂) ω₂ᵗ`, `z₂ₜ = z̄₂ + (z₂₀ - z̄₂) ω₂ᵗ`. -/
theorem saddle_path_constant_unique {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ e₁ e₂ m₁ m₂ x₁ x₂ z₂₀ : ℝ}
    {z₁ z₂ : ℕ → ℝ} (ha₂₁ : a₂₁ ≠ 0) (hsum : ω₁ + ω₂ = a₁₁ + a₂₂)
    (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) (hne : ω₁ ≠ ω₂) (he₁ : e₁ = (ω₁ - a₂₂) / a₂₁)
    (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁) (hω₁ : 1 < |ω₁|) (hω₂ : |ω₂| < 1)
    (hss₁ : x₁ = a₁₁ * x₁ + a₁₂ * x₂ + m₁) (hss₂ : x₂ = a₂₁ * x₁ + a₂₂ * x₂ + m₂)
    (hz : SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ (fun _ => m₁) (fun _ => m₂) z₁ z₂)
    (hz₁ : SeqBounded z₁) (hz₂ : SeqBounded z₂) (h0 : z₂ 0 = z₂₀) (t : ℕ) :
    z₁ t = x₁ + e₂ * (z₂₀ - x₂) * ω₂ ^ t ∧ z₂ t = x₂ + (z₂₀ - x₂) * ω₂ ^ t := by
  obtain ⟨hp, hp₁, hp₂, -, -, -⟩ :=
    saddle_path_constant_solves ha₂₁ hsum hprod he₂ hω₂ hss₁ hss₂ z₂₀
  exact saddle_path_unique ha₂₁ hsum hprod hne he₁ he₂ hω₁ hz hp hz₁ hz₂ hp₁ hp₂
    (by simp [h0]) t

/-! ### C.2.4 The polynomial-factorisation method -/

/-- O&R p. 739 (C.2.4): the lag polynomial factors through the characteristic roots,
`1 - (tr A) L + (det A) L² = (1 - ω₁ L)(1 - ω₂ L)`. -/
theorem lag_polynomial_factor {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} (hsum : ω₁ + ω₂ = a₁₁ + a₂₂)
    (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) (L : ℝ) :
    1 - (a₁₁ + a₂₂) * L + (a₁₁ * a₂₂ - a₁₂ * a₂₁) * L ^ 2 = (1 - ω₁ * L) * (1 - ω₂ * L) := by
  linear_combination L * hsum - L ^ 2 * hprod

/-- O&R SC(22), p. 739 (lead operator `L⁻¹`): a shifted bounded sequence is bounded. -/
theorem seqBounded_shift {x : ℕ → ℝ} (hx : SeqBounded x) (j : ℕ) :
    SeqBounded (fun t => x (t + j)) := by
  obtain ⟨B, hB⟩ := hx
  exact ⟨B, fun t => hB (t + j)⟩

/-- O&R SC(22), p. 739, first row (polynomial-factorisation form): if `|ω₁| > 1`, the forcing
is bounded and `(z₁, z₂)` is a solution with `z₁` bounded, then
`z₁ₜ = ω₂ z₁ₜ₋₁ - (1/ω₁) ∑_{s ≥ t} (1/ω₁)^{s-t} [m₁ₛ₊₁ - a₂₂ m₁ₛ + a₁₂ m₂ₛ]`,
written here at date `t + 1`. -/
theorem polynomial_factorization_row1 {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} {m₁ m₂ z₁ z₂ : ℕ → ℝ}
    (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) (hω₁ : 1 < |ω₁|)
    (hm₁ : SeqBounded m₁) (hm₂ : SeqBounded m₂)
    (hz : SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ z₁ z₂) (hz₁ : SeqBounded z₁) (t : ℕ) :
    z₁ (t + 1) = ω₂ * z₁ t -
      ∑' k : ℕ, (1 / ω₁) ^ (k + 1) * (m₁ (t + 2 + k) - a₂₂ * m₁ (t + 1 + k) +
        a₁₂ * m₂ (t + 1 + k)) := by
  set n : ℕ → ℝ := fun s => m₁ (s + 1) - a₂₂ * m₁ s + a₁₂ * m₂ s
  set u : ℕ → ℝ := fun s => z₁ (s + 1) - ω₂ * z₁ s
  have hu : ScalarSolves ω₁ n u := by
    intro s
    obtain ⟨A, -⟩ := hz (s + 1)
    obtain ⟨C, B⟩ := hz s
    simp only [u, n]
    linear_combination A + a₁₂ * B - a₂₂ * C - z₁ (s + 1) * hsum + z₁ s * hprod
  obtain ⟨N, hN⟩ : SeqBounded n := by
    convert seqBounded_lin_comb (seqBounded_lin_comb (seqBounded_shift hm₁ 1) hm₁ 1 (-a₂₂))
      hm₂ 1 a₁₂ using 2 with s
    simp only [n]; ring
  have hub : SeqBounded u := by
    convert seqBounded_lin_comb (seqBounded_shift hz₁ 1) hz₁ 1 (-ω₂) using 2 with s
    simp only [u]; ring
  have h := scalar_forward_unique_of_bounded hω₁ hN hu hub t
  simp only [u, forwardSolution, n] at h
  have e : ∀ k : ℕ, t + 1 + k + 1 = t + 2 + k := fun k => by ring
  simp only [e] at h
  linarith

/-- O&R SC(22), p. 739, second row: under the same hypotheses with `z₂` bounded,
`z₂ₜ = ω₂ z₂ₜ₋₁ - (1/ω₁) ∑_{s ≥ t} (1/ω₁)^{s-t} [a₂₁ m₁ₛ + m₂ₛ₊₁ - a₁₁ m₂ₛ]`,
written here at date `t + 1`. -/
theorem polynomial_factorization_row2 {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} {m₁ m₂ z₁ z₂ : ℕ → ℝ}
    (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) (hω₁ : 1 < |ω₁|)
    (hm₁ : SeqBounded m₁) (hm₂ : SeqBounded m₂)
    (hz : SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ z₁ z₂) (hz₂ : SeqBounded z₂) (t : ℕ) :
    z₂ (t + 1) = ω₂ * z₂ t -
      ∑' k : ℕ, (1 / ω₁) ^ (k + 1) * (a₂₁ * m₁ (t + 1 + k) + m₂ (t + 2 + k) -
        a₁₁ * m₂ (t + 1 + k)) := by
  set n : ℕ → ℝ := fun s => a₂₁ * m₁ s + m₂ (s + 1) - a₁₁ * m₂ s
  set u : ℕ → ℝ := fun s => z₂ (s + 1) - ω₂ * z₂ s
  have hu : ScalarSolves ω₁ n u := by
    intro s
    obtain ⟨-, A⟩ := hz (s + 1)
    obtain ⟨C, B⟩ := hz s
    simp only [u, n]
    linear_combination A + a₂₁ * C - a₁₁ * B - z₂ (s + 1) * hsum + z₂ s * hprod
  obtain ⟨N, hN⟩ : SeqBounded n := by
    convert seqBounded_lin_comb (seqBounded_lin_comb hm₁ (seqBounded_shift hm₂ 1) a₂₁ 1)
      hm₂ 1 (-a₁₁) using 2 with s
    simp only [n]; ring
  have hub : SeqBounded u := by
    convert seqBounded_lin_comb (seqBounded_shift hz₂ 1) hz₂ 1 (-ω₂) using 2 with s
    simp only [u]; ring
  have h := scalar_forward_unique_of_bounded hω₁ hN hu hub t
  simp only [u, forwardSolution, n] at h
  have e : ∀ k : ℕ, t + 1 + k + 1 = t + 2 + k := fun k => by ring
  simp only [e] at h
  linarith

/-! ## C.3 Higher-order equations -/

/-- O&R C.3, p. 741: a second-order equation `z_t = a₁ z_{t-1} + a₂ z_{t-2} + m_t` becomes
the first-order system with companion matrix `[[a₁, a₂], [1, 0]]` for `(z_t, z'_t) =
(z_t, z_{t-1})` and forcing `(m_t, 0)`; here `z₁ t = z (t+1)`, `z₂ t = z t`. -/
theorem companion_of_second_order {a₁ a₂ : ℝ} {m z : ℕ → ℝ}
    (hz : ∀ t, z (t + 2) = a₁ * z (t + 1) + a₂ * z t + m (t + 2)) :
    SystemSolves a₁ a₂ 1 0 (fun t => m (t + 1)) (fun _ => 0) (fun t => z (t + 1)) z := by
  intro t
  exact ⟨by simpa using hz t, by ring⟩

/-- O&R C.3, p. 741 (converse): the second component of a solution of the companion system
solves the second-order scalar equation. -/
theorem second_order_of_companion {a₁ a₂ : ℝ} {m₁ z₁ z₂ : ℕ → ℝ}
    (hz : SystemSolves a₁ a₂ 1 0 m₁ (fun _ => 0) z₁ z₂) (t : ℕ) :
    z₂ (t + 2) = a₁ * z₂ (t + 1) + a₂ * z₂ t + m₁ (t + 1) := by
  have h1 := (hz t).1
  have h2 := (hz t).2
  have h3 := (hz (t + 1)).2
  simp only [one_mul, zero_mul, add_zero] at h2 h3
  rw [h3, h1, ← h2]

/-- O&R C.3, p. 741: the companion matrix has `tr = a₁` and `det = -a₂`, so with roots
`ω₁ + ω₂ = a₁`, `ω₁ ω₂ = -a₂` the lag polynomial factors as
`1 - a₁ L - a₂ L² = (1 - ω₁ L)(1 - ω₂ L)` (as in C.2.4). -/
theorem companion_lag_polynomial {a₁ a₂ ω₁ ω₂ : ℝ} (hsum : ω₁ + ω₂ = a₁)
    (hprod : ω₁ * ω₂ = -a₂) (L : ℝ) :
    Matrix.trace !![a₁, a₂; 1, 0] = a₁ ∧ Matrix.det !![a₁, a₂; 1, 0] = -a₂ ∧
      1 - a₁ * L - a₂ * L ^ 2 = (1 - ω₁ * L) * (1 - ω₂ * L) := by
  rw [Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  refine ⟨by ring, by ring, ?_⟩
  linear_combination L * hsum - L ^ 2 * hprod

end ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Investment with adjustment costs: Tobin's q

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §2.5.2,
pp. 105–114, Appendix 2B.2, p. 124, Exercise 9, pp. 126–127, and the worked example of
Supplement C to Chapter 2, pp. 736–737.

A firm with capital `K_s` pays the installation cost `χ I_s² / (2 K_s)` (2.62). The
first-order conditions are the investment equation (2.63), `I_s = (q_s − 1) K_s / χ`, and the
investment Euler equation (2.64),
`(1 + r) q_s = A_{s+1} F_K(K_{s+1}, L_{s+1}) + (χ/2)(I_{s+1}/K_{s+1})² + q_{s+1}`.

Contents.
* `forward_iterate`, `hasSum_of_tail`, `tail_of_hasSum`: the forward solution of any recursion
  `(1 + r) x_t = y_{t+1} + x_{t+1}`; applied to (2.64) this is (2.65), `q_forward_solution`.
* **Index typo in (2.65) (repeated on p. 124).** The book prints the summand as
  `A_{s+1} F_K(K_{s+1}, L_{s+1}) + (χ/2)(I_{s+1}/K_{s+1})²` with weight `(1 + r)^{-(s-t)}` and
  `s` running from `t + 1`. Iterating (2.64) gives the subscripts `s`, not `s + 1`. The printed
  sum is in fact `q_{t+1}`, not `q_t`: `book_formula_sums_to_next_q`.
* Appendix 2B.2: `q_t − PV_t = lim (1 + r)^{-T} q_{t+T}` (`bubble_identity`), so a positive
  bubble term means `q_t` exceeds the present value of marginal earnings.
* The exact dynamics (2.66)–(2.67), the steady state `q̄ = 1`, `A F_K(K̄, L) = r`, and its
  uniqueness.
* The linearisation (2.68)–(2.69), the slope of the `Δq = 0` locus, and the saddle-point
  theorem: the characteristic roots satisfy `ω₁ > 1 > ω₂ > 0`, the saddle path
  `K_t − K̄ = (K_0 − K̄) ω₂^t`, `q_t − 1 = (χ (ω₂ − 1)/K̄)(K_0 − K̄) ω₂^t` solves the linear
  system and converges, and it is the unique bounded solution from `K_0`.
* Marginal q equals average q (Hayashi), (2.70), and the rate-of-return form of (2.64).
* Exercise 9: the simplified model with cost `χ I² / 2`, its first-order conditions and steady
  state, and the failure of marginal = average q.
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ

open Filter Topology Finset

/-! ## Forward solution of a first-order recursion -/

/-- **Finite-horizon forward iteration**, as used for O&R (2.65), p. 107: if
`(1 + r) x_t = y_{t+1} + x_{t+1}` for all `t`, then
`x_t = Σ_{s<T} (1 + r)^{-(s+1)} y_{t+s+1} + (1 + r)^{-T} x_{t+T}`. -/
theorem forward_iterate {r : ℝ} (hr : 1 + r ≠ 0) {x y : ℕ → ℝ}
    (h : ∀ t, (1 + r) * x t = y (t + 1) + x (t + 1)) (t T : ℕ) :
    x t = ∑ s ∈ range T, (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1) + (1 + r)⁻¹ ^ T * x (t + T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, ih]
    have hx : x (t + T) = (1 + r)⁻¹ * (y (t + T + 1) + x (t + T + 1)) := by
      rw [← h (t + T)]; field_simp
    rw [hx, show t + (T + 1) = t + T + 1 by ring]
    ring

/-- A convergent present value forces the no-bubble condition: if the discounted `y` sum to
`x_t` then `(1 + r)^{-T} x_{t+T} → 0` (O&R p. 107). -/
theorem tail_of_hasSum {r : ℝ} (hr : 1 + r ≠ 0) {x y : ℕ → ℝ}
    (h : ∀ t, (1 + r) * x t = y (t + 1) + x (t + 1)) (t : ℕ)
    (hs : HasSum (fun s => (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1)) (x t)) :
    Tendsto (fun T => (1 + r)⁻¹ ^ T * x (t + T)) atTop (𝓝 0) := by
  have h1 := (tendsto_const_nhds (x := x t)).sub hs.tendsto_sum_nat
  rw [sub_self] at h1
  refine h1.congr fun T => ?_
  rw [forward_iterate hr h t T]; ring

/-- **Forward solution under no bubbles**, O&R (2.65), p. 107: with a summable present value
and `(1 + r)^{-T} x_{t+T} → 0`, `x_t = Σ_{s ≥ 0} (1 + r)^{-(s+1)} y_{t+s+1}`. -/
theorem hasSum_of_tail {r : ℝ} (hr : 1 + r ≠ 0) {x y : ℕ → ℝ}
    (h : ∀ t, (1 + r) * x t = y (t + 1) + x (t + 1)) (t : ℕ)
    (hsum : Summable fun s => (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1))
    (htail : Tendsto (fun T => (1 + r)⁻¹ ^ T * x (t + T)) atTop (𝓝 0)) :
    HasSum (fun s => (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1)) (x t) := by
  have hp : Tendsto (fun T => ∑ s ∈ range T, (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1)) atTop
      (𝓝 (x t)) := by
    have h1 := (tendsto_const_nhds (x := x t)).sub htail
    rw [sub_zero] at h1
    refine h1.congr fun T => ?_
    rw [forward_iterate hr h t T]; ring
  have heq := tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hp
  rw [← heq]; exact hsum.hasSum

/-- **Bubble identity**, O&R Appendix 2B.2, p. 124: with a summable present value the
discounted terminal value converges, and its limit is exactly `x_t` minus the present value. -/
theorem bubble_identity {r : ℝ} (hr : 1 + r ≠ 0) {x y : ℕ → ℝ}
    (h : ∀ t, (1 + r) * x t = y (t + 1) + x (t + 1)) (t : ℕ)
    (hsum : Summable fun s => (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1)) :
    Tendsto (fun T => (1 + r)⁻¹ ^ T * x (t + T)) atTop
      (𝓝 (x t - ∑' s, (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1))) := by
  refine ((tendsto_const_nhds (x := x t)).sub hsum.hasSum.tendsto_sum_nat).congr fun T => ?_
  rw [forward_iterate hr h t T]; ring

/-- **A positive bubble overvalues the asset**, O&R Appendix 2B.2, p. 124: if the discounted
terminal value tends to `b > 0`, then `x_t` exceeds the present value, by exactly `b`. -/
theorem bubble_overvalues {r : ℝ} (hr : 1 + r ≠ 0) {x y : ℕ → ℝ}
    (h : ∀ t, (1 + r) * x t = y (t + 1) + x (t + 1)) (t : ℕ)
    (hsum : Summable fun s => (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1)) {b : ℝ}
    (hb : Tendsto (fun T => (1 + r)⁻¹ ^ T * x (t + T)) atTop (𝓝 b)) (hbpos : 0 < b) :
    x t - ∑' s, (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1) = b ∧
      ∑' s, (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1) < x t := by
  have := tendsto_nhds_unique (bubble_identity hr h t hsum) hb
  exact ⟨this, by linarith⟩

/-! ## The q model: first-order conditions and the forward solution (2.65) -/

/-- The date-`s` marginal earnings of installed capital in O&R (2.64)–(2.65):
`A_s F_K(K_s, L_s) + (χ/2)(I_s/K_s)²`, the marginal product plus the marginal saving in
installation costs. `FK` is the marginal product of capital. -/
noncomputable def marginalEarnings (A : ℕ → ℝ) (FK : ℝ → ℝ → ℝ) (K L I : ℕ → ℝ) (χ : ℝ)
    (s : ℕ) : ℝ :=
  A s * FK (K s) (L s) + χ / 2 * (I s / K s) ^ 2

/-- **Investment first-order condition**, O&R p. 106: the derivative of the date-`s` terms of
the Lagrangian that involve `I_s`, `−(χ/2) I²/K − I + q I`, is `−χ I/K − 1 + q`. -/
theorem hasDerivAt_lagrangian_investment (χ K q I : ℝ) :
    HasDerivAt (fun i : ℝ => -(χ / 2) * (i ^ 2 / K) - i + q * i) (-(χ * I / K) - 1 + q) I := by
  have h1 : HasDerivAt (fun i : ℝ => i ^ 2) (2 * I) I := by
    simpa using hasDerivAt_pow 2 I
  have h2 := ((h1.div_const K).const_mul (-(χ / 2))).sub (hasDerivAt_id I)
  have h3 := h2.add ((hasDerivAt_id I).const_mul q)
  convert h3 using 1
  · funext i; simp only [Pi.add_apply, Pi.sub_apply, id]
  · field_simp

/-- **Tobin's investment equation**, O&R (2.63), p. 107: with `χ ≠ 0` and `K ≠ 0`, the
investment first-order condition `−χ I/K − 1 + q = 0` holds iff `I = (q − 1) K / χ`. -/
theorem investment_foc_iff {χ K q I : ℝ} (hχ : χ ≠ 0) (hK : K ≠ 0) :
    -(χ * I / K) - 1 + q = 0 ↔ I = (q - 1) / χ * K := by
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    rw [h]; field_simp; ring

/-- **Capital first-order condition**, O&R p. 107: the terms of the Lagrangian involving
`K_{s+1}` are `−q_s K_{s+1}` plus the discounted date-`(s+1)` profit and constraint terms.
If `F(·, L_{s+1})` has derivative `FK` at `K ≠ 0`, their derivative is
`−q_s + (A F_K + (χ/2)(I_{s+1}/K)² + q_{s+1})/(1 + r)`. -/
theorem hasDerivAt_lagrangian_capital {F : ℝ → ℝ} {FK K : ℝ} (hF : HasDerivAt F FK K)
    (hK : K ≠ 0) (r A χ w L I q0 q1 K2 : ℝ) :
    HasDerivAt
      (fun k : ℝ => -q0 * k +
        (1 + r)⁻¹ * (A * F k - χ / 2 * (I ^ 2 / k) - w * L - I - q1 * (K2 - k - I)))
      (-q0 + (1 + r)⁻¹ * (A * FK + χ / 2 * (I / K) ^ 2 + q1)) K := by
  have hinv : HasDerivAt (fun k : ℝ => k⁻¹) (-(K ^ 2)⁻¹) K := hasDerivAt_inv hK
  have hc : HasDerivAt (fun k : ℝ => I ^ 2 / k) (I ^ 2 * -(K ^ 2)⁻¹) K := by
    simpa [div_eq_mul_inv] using hinv.const_mul (I ^ 2)
  have hlin : HasDerivAt (fun k : ℝ => q1 * (K2 - k - I)) (q1 * (-1)) K := by
    have : HasDerivAt (fun k : ℝ => K2 - k - I) (-1) K := by
      simpa using ((hasDerivAt_id K).const_sub K2).sub_const I
    exact this.const_mul q1
  have hin := ((((hF.const_mul A).sub (hc.const_mul (χ / 2))).sub_const (w * L)).sub_const
    I).sub hlin
  have h := ((hasDerivAt_id K).const_mul (-q0)).add (hin.const_mul (1 + r)⁻¹)
  convert h using 1
  · ext k; simp
  · field_simp; ring

/-- **Investment Euler equation**, O&R (2.64), p. 107: the capital first-order condition
equals zero iff `(1 + r) q_s = A F_K + (χ/2)(I_{s+1}/K_{s+1})² + q_{s+1}` (for `r ≠ -1`). -/
theorem capital_foc_iff {r FKval X q0 q1 : ℝ} (hr : 1 + r ≠ 0) :
    -q0 + (1 + r)⁻¹ * (FKval + X + q1) = 0 ↔ (1 + r) * q0 = FKval + X + q1 := by
  constructor
  · intro h; field_simp at h; linarith
  · intro h; rw [← h]; field_simp; ring

/-- **Forward solution for q**, O&R (2.65), p. 107, in corrected form: given the investment
Euler equation (2.64) at every date and a summable present value of marginal earnings, `q_t`
equals `Σ_{s ≥ t+1} (1 + r)^{-(s-t)} [A_s F_K(K_s, L_s) + (χ/2)(I_s/K_s)²]` iff the no-bubble
condition `lim (1 + r)^{-T} q_{t+T} = 0` holds. -/
theorem q_forward_solution {r χ : ℝ} (hr : 1 + r ≠ 0) {A : ℕ → ℝ} {FK : ℝ → ℝ → ℝ}
    {K L I q : ℕ → ℝ}
    (heuler : ∀ s, (1 + r) * q s = marginalEarnings A FK K L I χ (s + 1) + q (s + 1)) (t : ℕ)
    (hsum : Summable fun s => (1 + r)⁻¹ ^ (s + 1) * marginalEarnings A FK K L I χ (t + s + 1)) :
    HasSum (fun s => (1 + r)⁻¹ ^ (s + 1) * marginalEarnings A FK K L I χ (t + s + 1)) (q t) ↔
      Tendsto (fun T => (1 + r)⁻¹ ^ T * q (t + T)) atTop (𝓝 0) :=
  ⟨tail_of_hasSum hr heuler t, hasSum_of_tail hr heuler t hsum⟩

/-- **The printed (2.65) sums to `q_{t+1}`**, O&R p. 107 and p. 124. The book's summand, for
`s = t + 1 + n`, is `(1 + r)^{-(s-t)} X_{s+1} = (1 + r)^{-(n+1)} X_{t+n+2}` where `X` is
`marginalEarnings`. Under (2.64), summability and no bubbles, that series sums to `q_{t+1}`,
not `q_t`: the printed formula has its subscripts shifted by one. -/
theorem book_formula_sums_to_next_q {r χ : ℝ} (hr : 1 + r ≠ 0) {A : ℕ → ℝ}
    {FK : ℝ → ℝ → ℝ} {K L I q : ℕ → ℝ}
    (heuler : ∀ s, (1 + r) * q s = marginalEarnings A FK K L I χ (s + 1) + q (s + 1)) (t : ℕ)
    (hsum : Summable fun n => (1 + r)⁻¹ ^ (n + 1) * marginalEarnings A FK K L I χ (t + n + 2))
    (htail : Tendsto (fun T => (1 + r)⁻¹ ^ T * q (t + 1 + T)) atTop (𝓝 0)) :
    HasSum (fun n => (1 + r)⁻¹ ^ (n + 1) * marginalEarnings A FK K L I χ (t + n + 2))
      (q (t + 1)) := by
  have hf : (fun n => (1 + r)⁻¹ ^ (n + 1) * marginalEarnings A FK K L I χ (t + n + 2)) =
      fun n => (1 + r)⁻¹ ^ (n + 1) * marginalEarnings A FK K L I χ (t + 1 + n + 1) := by
    ext n; congr 2; ring
  rw [hf] at hsum ⊢
  exact hasSum_of_tail hr heuler (t + 1) hsum htail

/-- **The printed (2.65) is correct only by coincidence**: under the hypotheses of
`book_formula_sums_to_next_q`, the printed sum equals `q_t` iff `q_{t+1} = q_t`. -/
theorem book_formula_eq_q_iff {r χ : ℝ} (hr : 1 + r ≠ 0) {A : ℕ → ℝ}
    {FK : ℝ → ℝ → ℝ} {K L I q : ℕ → ℝ}
    (heuler : ∀ s, (1 + r) * q s = marginalEarnings A FK K L I χ (s + 1) + q (s + 1)) (t : ℕ)
    (hsum : Summable fun n => (1 + r)⁻¹ ^ (n + 1) * marginalEarnings A FK K L I χ (t + n + 2))
    (htail : Tendsto (fun T => (1 + r)⁻¹ ^ T * q (t + 1 + T)) atTop (𝓝 0)) :
    ∑' n, (1 + r)⁻¹ ^ (n + 1) * marginalEarnings A FK K L I χ (t + n + 2) = q t ↔
      q (t + 1) = q t := by
  rw [(book_formula_sums_to_next_q hr heuler t hsum htail).tsum_eq]

/-! ## Exact dynamics (2.66)–(2.67) and the steady state -/

/-- **Exact q dynamics**, O&R (2.66)–(2.67), p. 108, with constant `A` and `L`. From capital
accumulation, the investment equation (2.63) at `t` and `t + 1`, and the Euler equation (2.64)
at `t`: `K_{t+1} − K_t = ((q_t − 1)/χ) K_t` and
`q_{t+1} − q_t = r q_t − A F_K[K_t (1 + (q_t − 1)/χ), L] − (q_{t+1} − 1)²/(2χ)`. -/
theorem exact_dynamics {r χ A L : ℝ} (hχ : χ ≠ 0) {FK : ℝ → ℝ → ℝ} {K I q : ℕ → ℝ} {t : ℕ}
    (hK1 : K (t + 1) ≠ 0) (hacc : K (t + 1) = K t + I t)
    (hinv : ∀ s, I s = (q s - 1) / χ * K s)
    (heuler : (1 + r) * q t = A * FK (K (t + 1)) L + χ / 2 * (I (t + 1) / K (t + 1)) ^ 2
      + q (t + 1)) :
    K (t + 1) - K t = (q t - 1) / χ * K t ∧
      q (t + 1) - q t = r * q t - A * FK (K t * (1 + (q t - 1) / χ)) L
        - (q (t + 1) - 1) ^ 2 / (2 * χ) := by
  have hk : K (t + 1) = K t * (1 + (q t - 1) / χ) := by rw [hacc, hinv t]; ring
  refine ⟨by rw [hacc, hinv t]; ring, ?_⟩
  rw [← hk]
  have hI : I (t + 1) / K (t + 1) = (q (t + 1) - 1) / χ := by
    rw [hinv (t + 1)]; field_simp
  rw [hI] at heuler
  field_simp
  field_simp at heuler
  linear_combination (-1) * heuler

/-- **Steady state of the q model**, O&R p. 108: with `χ ≠ 0` and `K̄ ≠ 0`, `(q̄, K̄)` is a
rest point of (2.66)–(2.67) iff `q̄ = 1` and `A F_K(K̄, L) = r`. -/
theorem steady_state_iff {r χ A L qb Kb : ℝ} (hχ : χ ≠ 0) (hK : Kb ≠ 0) {FK : ℝ → ℝ → ℝ} :
    ((qb - 1) / χ * Kb = 0 ∧
      r * qb - A * FK (Kb * (1 + (qb - 1) / χ)) L - (qb - 1) ^ 2 / (2 * χ) = 0) ↔
      (qb = 1 ∧ A * FK Kb L = r) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hq : qb = 1 := by
      rcases mul_eq_zero.1 h1 with h | h
      · rcases div_eq_zero_iff.1 h with h | h
        · linarith
        · exact absurd h hχ
      · exact absurd h hK
    subst hq
    refine ⟨rfl, ?_⟩
    simp at h2; linarith
  · rintro ⟨rfl, h⟩
    simp [h]

/-- **Uniqueness of the steady state**, O&R p. 108: if `A > 0` and `F_K(·, L)` is strictly
decreasing on `K > 0`, at most one `K̄ > 0` satisfies `A F_K(K̄, L) = r`. -/
theorem steady_state_unique {r A L : ℝ} (hA : 0 < A) {FK : ℝ → ℝ → ℝ}
    (hdec : StrictAntiOn (fun k => FK k L) (Set.Ioi 0)) {K1 K2 : ℝ} (h1 : 0 < K1)
    (h2 : 0 < K2) (e1 : A * FK K1 L = r) (e2 : A * FK K2 L = r) : K1 = K2 := by
  have : FK K1 L = FK K2 L := by
    have := e1.trans e2.symm
    exact mul_left_cancel₀ hA.ne' this
  exact hdec.injOn h1 h2 this

/-- **The `ΔK = 0` schedule is `q = 1`**, O&R p. 108 and footnote 43: for `K ≠ 0` and
`χ ≠ 0`, capital is stationary under (2.66) iff `q = 1`, globally (not only near `K̄`). -/
theorem capital_stationary_iff {χ K q : ℝ} (hχ : χ ≠ 0) (hK : K ≠ 0) :
    (q - 1) / χ * K = 0 ↔ q = 1 := by
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · rcases div_eq_zero_iff.1 h with h | h
      · linarith
      · exact absurd h hχ
    · exact absurd h hK
  · rintro rfl; simp

/-! ## Linearisation (2.68)–(2.69) -/

/-- **Linearised capital equation**, O&R (2.68), p. 108: the right side of (2.66),
`((q − 1)/χ) K̄`, has derivative `K̄/χ` in `q` at `q̄ = 1`. -/
theorem hasDerivAt_capital_dynamics_q (χ Kb : ℝ) :
    HasDerivAt (fun q : ℝ => (q - 1) / χ * Kb) (Kb / χ) 1 := by
  have := (((hasDerivAt_id (1 : ℝ)).sub_const 1).div_const χ).mul_const Kb
  convert this using 1
  · funext q; simp
  · ring

/-- **Linearised capital equation**, O&R (2.68), p. 108: at `q = 1` the right side of (2.66)
does not depend on `K`, so its derivative in `K` is `0`. -/
theorem hasDerivAt_capital_dynamics_K (χ Kb : ℝ) :
    HasDerivAt (fun k : ℝ => ((1 : ℝ) - 1) / χ * k) 0 Kb := by
  simpa using hasDerivAt_const Kb (0 : ℝ)

/-- **Linearised q equation, `q` coefficient**, O&R (2.69), p. 108: if `F_K(·, L)` has
derivative `F_KK` at `K̄`, then `q ↦ r q − A F_K(K̄(1 + (q − 1)/χ), L)` has derivative
`r − A K̄ F_KK/χ` at `q = 1`. -/
theorem hasDerivAt_q_dynamics_q {FK : ℝ → ℝ → ℝ} {L Kb FKK : ℝ}
    (hF : HasDerivAt (fun k => FK k L) FKK Kb) (r A χ : ℝ) :
    HasDerivAt (fun q : ℝ => r * q - A * FK (Kb * (1 + (q - 1) / χ)) L)
      (r - A * Kb * FKK / χ) 1 := by
  have hin : HasDerivAt (fun q : ℝ => Kb * (1 + (q - 1) / χ)) (Kb * (1 / χ)) 1 := by
    have := ((((hasDerivAt_id (1 : ℝ)).sub_const 1).div_const χ).const_add 1).const_mul Kb
    simpa using this
  have hF' : HasDerivAt (fun k => FK k L) FKK (Kb * (1 + ((1 : ℝ) - 1) / χ)) := by
    simpa using hF
  have hc := hF'.comp (1 : ℝ) hin
  have h := ((hasDerivAt_id (1 : ℝ)).const_mul r).sub (hc.const_mul A)
  convert h using 1
  · funext q; simp only [Pi.sub_apply, id, Function.comp]
  · field_simp

/-- **Linearised q equation, `K` coefficient**, O&R (2.69), p. 108: at `q = 1` the map
`K ↦ r − A F_K(K, L)` has derivative `−A F_KK` at `K̄`. -/
theorem hasDerivAt_q_dynamics_K {FK : ℝ → ℝ → ℝ} {L Kb FKK : ℝ}
    (hF : HasDerivAt (fun k => FK k L) FKK Kb) (r A χ : ℝ) :
    HasDerivAt (fun k : ℝ => r * 1 - A * FK (k * (1 + ((1 : ℝ) - 1) / χ)) L) (-(A * FKK)) Kb := by
  have h := (hF.const_mul A).const_sub (r * 1)
  convert h using 1
  funext k; simp

/-- **The quadratic term drops out of (2.69)**, O&R p. 108: `(q' − 1)²/(2χ)` has zero
derivative at `q' = 1`. -/
theorem hasDerivAt_q_dynamics_quadratic (χ : ℝ) :
    HasDerivAt (fun q' : ℝ => (q' - 1) ^ 2 / (2 * χ)) 0 1 := by
  have := (((hasDerivAt_id (1 : ℝ)).sub_const 1).pow 2).div_const (2 * χ)
  simpa using this

/-- **Slope of the `Δq = 0` schedule**, O&R p. 109: with `A > 0`, `F_KK < 0`, `r > 0`,
`K̄ > 0`, `χ > 0`, the linearised locus
`0 = (r − A K̄ F_KK/χ)(q − 1) − A F_KK (K − K̄)` is the line through `(K̄, 1)` with slope
`A F_KK / (r − A K̄ F_KK/χ)`, and that slope is negative. -/
theorem dq_locus {r χ A Kb FKK : ℝ} (hr : 0 < r) (hχ : 0 < χ) (hA : 0 < A) (hKb : 0 < Kb)
    (hFKK : FKK < 0) :
    (∀ K q : ℝ, (r - A * Kb * FKK / χ) * (q - 1) - A * FKK * (K - Kb) = 0 ↔
      q - 1 = A * FKK / (r - A * Kb * FKK / χ) * (K - Kb)) ∧
      A * FKK / (r - A * Kb * FKK / χ) < 0 := by
  have hD : 0 < r - A * Kb * FKK / χ := by
    have : A * Kb * FKK / χ < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hA hKb) hFKK) hχ
    linarith
  set D := r - A * Kb * FKK / χ with hDd
  refine ⟨fun K q => ?_, div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hA hFKK) hD⟩
  constructor
  · intro h
    rw [div_mul_eq_mul_div, eq_div_iff hD.ne']
    linarith
  · intro h
    rw [h, div_mul_eq_mul_div, mul_div_assoc', mul_div_cancel_left₀ _ hD.ne']
    ring

/-! ## The saddle-point theorem (O&R p. 109; Supplement C, pp. 736–737) -/

/-- The matrix of the linear system (2.68)–(2.69) in the variables `(q_t − q̄, K_t − K̄)`, as
in O&R Supplement C, p. 736, with `a = A F_KK(K̄, L)`. -/
noncomputable def qMatrix (r χ Kb a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + r - Kb * a / χ, -a; Kb / χ, 1]

/-- **Determinant and trace of the q system**, O&R Supplement C, p. 736: `det = 1 + r` and
`trace = 2 + r − A K̄ F_KK/χ`. -/
theorem qMatrix_det_trace {r χ Kb a : ℝ} (hχ : χ ≠ 0) :
    (qMatrix r χ Kb a).det = 1 + r ∧ (qMatrix r χ Kb a).trace = 2 + r - Kb * a / χ := by
  refine ⟨?_, ?_⟩
  · rw [qMatrix, Matrix.det_fin_two_of]; field_simp; ring
  · rw [qMatrix, Matrix.trace_fin_two_of]; ring

/-- The characteristic polynomial of the q system, `ω² − (2 + r + x) ω + (1 + r)`, where
`x = −A K̄ F_KK/χ` (O&R Supplement C, p. 736). -/
def qCharPoly (r x ω : ℝ) : ℝ := ω ^ 2 - (2 + r + x) * ω + (1 + r)

/-- The discriminant `(2 + r + x)² − 4(1 + r)` of `qCharPoly` (O&R p. 736). -/
def qDisc (r x : ℝ) : ℝ := (2 + r + x) ^ 2 - 4 * (1 + r)

/-- The stable root `ω₂ = ((2 + r + x) − √disc)/2` (O&R p. 736). -/
noncomputable def omegaStable (r x : ℝ) : ℝ := ((2 + r + x) - √(qDisc r x)) / 2

/-- The unstable root `ω₁ = ((2 + r + x) + √disc)/2` (O&R p. 736). -/
noncomputable def omegaUnstable (r x : ℝ) : ℝ := ((2 + r + x) + √(qDisc r x)) / 2

/-- The discriminant equals `(r + x)² + 4x`, so it is positive when `x > 0`: the roots are
real and distinct (O&R p. 736). -/
theorem qDisc_eq (r x : ℝ) : qDisc r x = (r + x) ^ 2 + 4 * x := by
  unfold qDisc; ring

/-- **Both roots solve the characteristic equation**, and `ω₁ + ω₂ = trace`,
`ω₁ ω₂ = 1 + r = det` (O&R p. 736, eq. (14) of Supplement C), when `x ≥ 0`. -/
theorem omega_roots {r x : ℝ} (hx : 0 ≤ x) :
    qCharPoly r x (omegaStable r x) = 0 ∧ qCharPoly r x (omegaUnstable r x) = 0 ∧
      omegaUnstable r x + omegaStable r x = 2 + r + x ∧
      omegaUnstable r x * omegaStable r x = 1 + r := by
  have hD : 0 ≤ qDisc r x := by rw [qDisc_eq]; positivity
  have hs : √(qDisc r x) ^ 2 = (2 + r + x) ^ 2 - 4 * (1 + r) := Real.sq_sqrt hD
  unfold qCharPoly omegaStable omegaUnstable
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination hs / 4
  · linear_combination hs / 4
  · ring
  · linear_combination (-1 / 4 : ℝ) * hs

/-- **Saddle-point root configuration**, O&R Supplement C, p. 736: if `1 + r > 0` and
`x = −A K̄ F_KK/χ > 0`, then `0 < ω₂ < 1 < ω₁`. (The book assumes Cobb–Douglas, where
`x = (1 − α) r / χ`; only `x > 0`, i.e. `F_KK < 0`, is needed.) -/
theorem omega_saddle {r x : ℝ} (hr : 0 < 1 + r) (hx : 0 < x) :
    0 < omegaStable r x ∧ omegaStable r x < 1 ∧ 1 < omegaUnstable r x := by
  have hD : 0 < qDisc r x := by rw [qDisc_eq]; positivity
  have hlt : (r + x) ^ 2 < qDisc r x := by rw [qDisc_eq]; linarith
  have h1 : r + x < √(qDisc r x) := Real.lt_sqrt_of_sq_lt hlt
  have h2 : -(r + x) < √(qDisc r x) := Real.lt_sqrt_of_sq_lt (by rw [neg_sq]; exact hlt)
  have h3 : √(qDisc r x) < 2 + r + x := by
    rw [Real.sqrt_lt' (by linarith)]
    unfold qDisc; linarith
  unfold omegaStable omegaUnstable
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **Cobb–Douglas curvature**, O&R p. 736: with `F(K, L) = K^α L^{1−α}`, `K > 0`, the
marginal product `F_K = α K^{α−1} L^{1−α}` has derivative `F_KK = α(α − 1) K^{α−2} L^{1−α}`,
and if `A F_K(K̄, L) = r` then `−A K̄ F_KK(K̄, L) = (1 − α) r`. -/
theorem cobbDouglas_curvature {α A L Kb r : ℝ} (hKb : 0 < Kb)
    (hss : A * (α * Kb ^ (α - 1) * L ^ (1 - α)) = r) :
    HasDerivAt (fun k : ℝ => α * k ^ (α - 1) * L ^ (1 - α))
        (α * ((α - 1) * Kb ^ (α - 2)) * L ^ (1 - α)) Kb ∧
      -(A * Kb * (α * ((α - 1) * Kb ^ (α - 2)) * L ^ (1 - α))) = (1 - α) * r := by
  refine ⟨?_, ?_⟩
  · have := ((Real.hasDerivAt_rpow_const (p := α - 1) (Or.inl hKb.ne')).const_mul α).mul_const
      (L ^ (1 - α))
    convert this using 2
    ring_nf
  · have h : Kb ^ (α - 1) = Kb ^ (α - 2) * Kb := by
      rw [← Real.rpow_add_one hKb.ne']; ring_nf
    rw [← hss, h]; ring

/-- The linear system (2.68)–(2.69) in deviations `p_t = q_t − 1`, `k_t = K_t − K̄`, with
`a = A F_KK(K̄, L)` (O&R p. 108; Supplement C, p. 736):
`p_{t+1} = (1 + r − K̄ a/χ) p_t − a k_t` and `k_{t+1} = k_t + (K̄/χ) p_t`. -/
def IsLinearQPath (r χ Kb a : ℝ) (p k : ℕ → ℝ) : Prop :=
  ∀ t, p (t + 1) = (1 + r - Kb * a / χ) * p t - a * k t ∧ k (t + 1) = k t + Kb / χ * p t

/-- **The saddle path solves the linear system**, O&R Supplement C, p. 737: for any root `ω`
of the characteristic polynomial (with `x = −K̄ a/χ`), `k_t = k_0 ω^t` and
`p_t = (χ (ω − 1)/K̄) k_0 ω^t` satisfy (2.68)–(2.69). -/
theorem saddle_path_solves {r χ Kb a ω k0 : ℝ} (hχ : χ ≠ 0) (hKb : Kb ≠ 0)
    (hω : qCharPoly r (-(Kb * a / χ)) ω = 0) :
    IsLinearQPath r χ Kb a (fun t => χ * (ω - 1) / Kb * k0 * ω ^ t) (fun t => k0 * ω ^ t) := by
  intro t
  unfold qCharPoly at hω
  refine ⟨?_, ?_⟩
  · have h' : ω ^ 2 - (2 + r) * ω + (1 + r) = -(Kb * a / χ) * ω := by
      linear_combination hω
    dsimp only
    rw [pow_succ]
    linear_combination (norm := skip) (χ / Kb * k0 * ω ^ t) * h'
    field_simp
    ring
  · simp only [pow_succ]
    field_simp
    ring

/-- **The saddle path converges to the steady state**, O&R p. 737: with `0 < ω₂ < 1`, both
`K_t − K̄` and `q_t − 1` tend to zero along the saddle path. -/
theorem saddle_path_tendsto {χ Kb ω k0 : ℝ} (h0 : 0 < ω) (h1 : ω < 1) :
    Tendsto (fun t : ℕ => k0 * ω ^ t) atTop (𝓝 0) ∧
      Tendsto (fun t : ℕ => χ * (ω - 1) / Kb * k0 * ω ^ t) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1
  refine ⟨?_, ?_⟩
  · simpa using hp.const_mul k0
  · simpa using hp.const_mul (χ * (ω - 1) / Kb * k0)

/-- **`q > 1` exactly when capital starts below its steady state**, O&R p. 737 and p. 110:
along the saddle path with `χ > 0`, `K̄ > 0`, `0 < ω₂ < 1`, `q_t − 1 > 0` iff `K_0 < K̄`. -/
theorem saddle_q_above_one_iff {χ Kb ω k0 : ℝ} (hχ : 0 < χ) (hKb : 0 < Kb) (h0 : 0 < ω)
    (h1 : ω < 1) (t : ℕ) :
    0 < χ * (ω - 1) / Kb * k0 * ω ^ t ↔ k0 < 0 := by
  have hc : χ * (ω - 1) / Kb < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hχ (by linarith)) hKb
  have hpow : 0 < ω ^ t := pow_pos h0 t
  constructor
  · intro h
    by_contra hk
    push Not at hk
    have : χ * (ω - 1) / Kb * k0 * ω ^ t ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc.le hk) hpow.le
    linarith
  · intro hk
    exact mul_pos (mul_pos_of_neg_of_neg hc hk) hpow

/-- **Monotone convergence along the saddle path**, O&R p. 110: if `K_0 < K̄` then capital
rises strictly and `q` falls strictly toward `1` (with `χ > 0`, `K̄ > 0`, `0 < ω₂ < 1`). -/
theorem saddle_monotone {χ Kb ω k0 : ℝ} (hχ : 0 < χ) (hKb : 0 < Kb) (h0 : 0 < ω) (h1 : ω < 1)
    (hk : k0 < 0) :
    StrictMono (fun t : ℕ => k0 * ω ^ t) ∧
      StrictAnti (fun t : ℕ => χ * (ω - 1) / Kb * k0 * ω ^ t) := by
  have hc : χ * (ω - 1) / Kb < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hχ (by linarith)) hKb
  have ha := pow_right_strictAnti₀ h0 h1
  refine ⟨fun m n hmn => ?_, fun m n hmn => ?_⟩
  · exact mul_lt_mul_of_neg_left (ha hmn) hk
  · simp only
    rw [mul_assoc, mul_assoc]
    exact mul_lt_mul_of_neg_left (mul_lt_mul_of_neg_left (ha hmn) hk) hc

/-- **Uniqueness of the saddle path**, O&R p. 109 ("there is one and only one value of `q_t`
that places the firm on the stable adjustment path"). With `1 + r > 0`, `χ > 0`, `K̄ > 0` and
`a = A F_KK(K̄, L) < 0`, every bounded solution of the linear system (2.68)–(2.69) with
`K_0 − K̄ = k_0` is the saddle path `k_t = k_0 ω₂^t`, `p_t = (χ (ω₂ − 1)/K̄) k_0 ω₂^t`. -/
theorem saddle_path_unique {r χ Kb a : ℝ} (hr : 0 < 1 + r) (hχ : 0 < χ) (hKb : 0 < Kb)
    (ha : a < 0) {p k : ℕ → ℝ} (hsys : IsLinearQPath r χ Kb a p k) {B : ℝ}
    (hB : ∀ t, |p t| ≤ B ∧ |k t| ≤ B) (t : ℕ) :
    k t = k 0 * omegaStable r (-(Kb * a / χ)) ^ t ∧
      p t = χ * (omegaStable r (-(Kb * a / χ)) - 1) / Kb * k 0 *
        omegaStable r (-(Kb * a / χ)) ^ t := by
  set x := -(Kb * a / χ) with hxd
  have hx : 0 < x := by
    rw [hxd, neg_pos]; exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hKb ha) hχ
  obtain ⟨hr1, hr2, hsum, hprod⟩ := omega_roots hx.le
  obtain ⟨_, _, hω1⟩ := omega_saddle hr hx
  set ω1 := omegaUnstable r x
  set ω2 := omegaStable r x
  have hax : a = -(x * χ / Kb) := by rw [hxd]; field_simp
  clear_value x ω1 ω2
  -- the unstable combination `u_t = (ω₁ − 1) p_t − a k_t` grows by the factor `ω₁`
  have hu : ∀ t, (ω1 - 1) * p (t + 1) - a * k (t + 1) = ω1 * ((ω1 - 1) * p t - a * k t) := by
    intro t
    obtain ⟨hp, hk⟩ := hsys t
    unfold qCharPoly at hr2
    rw [hp, hk, show 1 + r - Kb * a / χ = 1 + r + x by rw [hxd]; ring]
    have : Kb / χ * a = -x := by rw [hxd]; field_simp
    linear_combination (-(p t)) * hr2 - p t * this
  have hupow : ∀ t, (ω1 - 1) * p t - a * k t = ω1 ^ t * ((ω1 - 1) * p 0 - a * k 0) := by
    intro t
    induction t with
    | zero => simp
    | succ n ih => rw [hu n, ih, pow_succ]; ring
  -- boundedness forces `u_0 = 0`
  have hu0 : (ω1 - 1) * p 0 - a * k 0 = 0 := by
    by_contra hne
    set u0 := (ω1 - 1) * p 0 - a * k 0
    have hpos : 0 < |u0| := abs_pos.2 hne
    set M := ((ω1 - 1) + |a|) * B
    have hev := (tendsto_pow_atTop_atTop_of_one_lt hω1).eventually_gt_atTop (M / |u0|)
    obtain ⟨n, hn⟩ := hev.exists
    have hbound : |(ω1 - 1) * p n - a * k n| ≤ M := by
      obtain ⟨hpB, hkB⟩ := hB n
      calc |(ω1 - 1) * p n - a * k n| ≤ |(ω1 - 1) * p n| + |a * k n| := abs_sub _ _
        _ = (ω1 - 1) * |p n| + |a| * |k n| := by
          rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < ω1 - 1)]
        _ ≤ (ω1 - 1) * B + |a| * B := by gcongr
        _ = M := by ring
    rw [hupow n, abs_mul, abs_of_pos (pow_pos (by linarith) n)] at hbound
    rw [div_lt_iff₀ hpos] at hn
    linarith
  -- hence `p_0 = c k_0` with `c = χ (ω₂ − 1)/K̄`
  have hp0 : p 0 = χ * (ω2 - 1) / Kb * k 0 := by
    have hω1ne : ω1 - 1 ≠ 0 := by linarith
    have hc : (ω1 - 1) * (χ * (ω2 - 1) / Kb) = a := by
      rw [hax]; field_simp
      linear_combination hprod - hsum
    have : (ω1 - 1) * p 0 = (ω1 - 1) * (χ * (ω2 - 1) / Kb * k 0) := by
      rw [← mul_assoc, hc]; linarith
    exact mul_left_cancel₀ hω1ne this
  -- the linear system is deterministic forward: induction
  have hr1' : qCharPoly r (-(Kb * a / χ)) ω2 = 0 := by rw [← hxd]; exact hr1
  have hsol := saddle_path_solves (k0 := k 0) hχ.ne' hKb.ne' hr1'
  induction t with
  | zero => simp [hp0]
  | succ n ih =>
    obtain ⟨hpn, hkn⟩ := hsys n
    obtain ⟨hps, hks⟩ := hsol n
    refine ⟨?_, ?_⟩
    · rw [hkn, ih.1, ih.2]; exact hks.symm
    · rw [hpn, ih.1, ih.2]; exact hps.symm

/-! ## Marginal q equals average q (Hayashi), (2.70) -/

/-- **Euler's theorem for a linearly homogeneous function**, used for O&R (2.70), p. 112: if
`F` is differentiable at `v` with derivative `DF` and `F(λ v) = λ F(v)` for all `λ > 0`, then
`F(v) = DF(v)`; for `v = (K, L)` this is `F = F_K K + F_L L`. -/
theorem euler_of_homogeneous {F : ℝ × ℝ → ℝ} {DF : ℝ × ℝ →L[ℝ] ℝ} {v : ℝ × ℝ}
    (hF : HasFDerivAt F DF v) (hhom : ∀ l : ℝ, 0 < l → F (l • v) = l * F v) :
    F v = DF (1, 0) * v.1 + DF (0, 1) * v.2 := by
  have hray : HasDerivAt (fun l : ℝ => l • v) ((1 : ℝ) • v) 1 :=
    (hasDerivAt_id (1 : ℝ)).smul_const v
  have hF1 : HasFDerivAt F DF ((1 : ℝ) • v) := by rwa [one_smul]
  have h1 : HasDerivAt (fun l : ℝ => F (l • v)) (DF ((1 : ℝ) • v)) 1 :=
    hF1.comp_hasDerivAt (1 : ℝ) hray
  have h2 : HasDerivAt (fun l : ℝ => l * F v) (F v) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (F v)
  have hev : (fun l : ℝ => F (l • v)) =ᶠ[𝓝 1] fun l => l * F v := by
    filter_upwards [Ioi_mem_nhds (zero_lt_one' ℝ)] with l hl using hhom l hl
  have h3 := h2.congr_of_eventuallyEq hev
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [h3.unique h1, one_smul]
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- The firm's date-`s` dividend in O&R (2.62), p. 106:
`A_s F(K_s, L_s) − (χ/2)(I_s²/K_s) − w_s L_s − I_s`. -/
noncomputable def dividend (A w : ℕ → ℝ) (F : ℝ → ℝ → ℝ) (K L I : ℕ → ℝ) (χ : ℝ) (s : ℕ) : ℝ :=
  A s * F (K s) (L s) - χ / 2 * (I s ^ 2 / K s) - w s * L s - I s

/-- **The one-step Hayashi identity**, O&R p. 112: under capital accumulation, the investment
equation (2.63) in the form `q_s = 1 + χ I_s/K_s`, the Euler equation (2.64), Euler's theorem
`F = F_K K + F_L L` and the labour first-order condition `A F_L = w`,
`(1 + r) q_t K_{t+1} = d_{t+1} + q_{t+1} K_{t+2}`. -/
theorem hayashi_step {r χ : ℝ} {A w : ℕ → ℝ} {F FK FL : ℝ → ℝ → ℝ} {K L I q : ℕ → ℝ}
    (hK : ∀ s, K s ≠ 0) (hacc : ∀ s, K (s + 1) = K s + I s)
    (hinv : ∀ s, q s = 1 + χ * (I s / K s))
    (heuler : ∀ s, (1 + r) * q s = marginalEarnings A FK K L I χ (s + 1) + q (s + 1))
    (heul : ∀ s, F (K s) (L s) = FK (K s) (L s) * K s + FL (K s) (L s) * L s)
    (hlab : ∀ s, A s * FL (K s) (L s) = w s) (t : ℕ) :
    (1 + r) * (q t * K (t + 1)) = dividend A w F K L I χ (t + 1) + q (t + 1) * K (t + 1 + 1) := by
  have he := heuler t
  unfold marginalEarnings at he
  unfold dividend
  have hk := hK (t + 1)
  rw [show (1 + r) * (q t * K (t + 1)) = ((1 + r) * q t) * K (t + 1) by ring, he,
    hacc (t + 1), heul (t + 1), ← hlab (t + 1), hinv (t + 1)]
  field_simp
  ring

/-- **Marginal q equals average q**, O&R (2.70), p. 112 (Hayashi 1982): under the hypotheses
of `hayashi_step` and summable discounted dividends, `q_t K_{t+1} = V_t`, the present value
`Σ_{s ≥ t+1} (1 + r)^{-(s-t)} d_s` of future dividends, iff the no-bubble condition
`(1 + r)^{-T} q_{t+T} K_{t+T+1} → 0` holds. -/
theorem marginal_q_eq_average_q {r χ : ℝ} (hr : 1 + r ≠ 0) {A w : ℕ → ℝ}
    {F FK FL : ℝ → ℝ → ℝ} {K L I q : ℕ → ℝ}
    (hK : ∀ s, K s ≠ 0) (hacc : ∀ s, K (s + 1) = K s + I s)
    (hinv : ∀ s, q s = 1 + χ * (I s / K s))
    (heuler : ∀ s, (1 + r) * q s = marginalEarnings A FK K L I χ (s + 1) + q (s + 1))
    (heul : ∀ s, F (K s) (L s) = FK (K s) (L s) * K s + FL (K s) (L s) * L s)
    (hlab : ∀ s, A s * FL (K s) (L s) = w s) (t : ℕ)
    (hsum : Summable fun s => (1 + r)⁻¹ ^ (s + 1) * dividend A w F K L I χ (t + s + 1)) :
    HasSum (fun s => (1 + r)⁻¹ ^ (s + 1) * dividend A w F K L I χ (t + s + 1))
        (q t * K (t + 1)) ↔
      Tendsto (fun T => (1 + r)⁻¹ ^ T * (q (t + T) * K (t + T + 1))) atTop (𝓝 0) := by
  have h := hayashi_step hK hacc hinv heuler heul hlab
  exact ⟨tail_of_hasSum (x := fun s => q s * K (s + 1)) hr h t,
    hasSum_of_tail (x := fun s => q s * K (s + 1)) hr h t hsum⟩

/-- **Rate-of-return form of the Euler equation**, O&R p. 113: with `q_t ≠ 0` and
`K_{t+1} ≠ 0`, (2.64) with (2.63) and capital accumulation gives
`r = [A F_K − (χ/2)(I_{t+1}/K_{t+1})² − I_{t+1}/K_{t+1} + q_{t+1} K_{t+2}/K_{t+1} − q_t]/q_t`. -/
theorem rate_of_return_form {r χ : ℝ} {A : ℕ → ℝ} {FK : ℝ → ℝ → ℝ} {K L I q : ℕ → ℝ}
    {t : ℕ} (hq : q t ≠ 0) (hK : K (t + 1) ≠ 0) (hacc : K (t + 1 + 1) = K (t + 1) + I (t + 1))
    (hinv : q (t + 1) = 1 + χ * (I (t + 1) / K (t + 1)))
    (heuler : (1 + r) * q t = marginalEarnings A FK K L I χ (t + 1) + q (t + 1)) :
    r = (A (t + 1) * FK (K (t + 1)) (L (t + 1)) - χ / 2 * (I (t + 1) / K (t + 1)) ^ 2
      - I (t + 1) / K (t + 1) + q (t + 1) * K (t + 1 + 1) / K (t + 1) - q t) / q t := by
  unfold marginalEarnings at heuler
  rw [eq_div_iff hq, hacc, hinv]
  rw [hinv] at heuler
  field_simp
  field_simp at heuler
  linear_combination heuler

/-! ## Exercise 9: the simplified q model with cost `χ I²/2` (pp. 126–127) -/

/-- **Exercise 9(a), investment**, O&R p. 127: the derivative in `I` of the date-`s` terms
`A F(K) − I − χ I²/2 − q (K' − K − I)` is `−1 − χ I + q`. -/
theorem ex9_hasDerivAt_investment (AF χ q K K' I : ℝ) :
    HasDerivAt (fun i : ℝ => AF - i - χ * i ^ 2 / 2 - q * (K' - K - i)) (-1 - χ * I + q) I := by
  have h1 : HasDerivAt (fun i : ℝ => i ^ 2) (2 * I) I := by simpa using hasDerivAt_pow 2 I
  have hl : HasDerivAt (fun i : ℝ => K' - K - i) (-1) I := by
    simpa using (hasDerivAt_id I).const_sub (K' - K)
  have h := (((hasDerivAt_id I).const_sub AF).sub ((h1.const_mul χ).div_const 2)).sub
    (hl.const_mul q)
  convert h using 1
  · funext i; simp
  · ring

/-- **Exercise 9(a), capital**, O&R p. 127: if `F` has derivative `F'` at `K`, the derivative in
`K_{s+1}` of `−q_s K_{s+1} + (A F(K_{s+1}) − I − χ I²/2 − q_{s+1}(K_{s+2} − K_{s+1} − I))/(1 + r)`
is `−q_s + (A F'(K_{s+1}) + q_{s+1})/(1 + r)`. -/
theorem ex9_hasDerivAt_capital {F : ℝ → ℝ} {F' K : ℝ} (hF : HasDerivAt F F' K)
    (r A χ I q0 q1 K2 : ℝ) :
    HasDerivAt
      (fun k : ℝ => -q0 * k + (1 + r)⁻¹ * (A * F k - I - χ * I ^ 2 / 2 - q1 * (K2 - k - I)))
      (-q0 + (1 + r)⁻¹ * (A * F' + q1)) K := by
  have hl : HasDerivAt (fun k : ℝ => K2 - k - I) (-1) K := by
    simpa using ((hasDerivAt_id K).const_sub K2).sub_const I
  have h := ((hasDerivAt_id K).const_mul (-q0)).add
    (((((hF.const_mul A).sub_const I).sub_const (χ * I ^ 2 / 2)).sub (hl.const_mul q1)).const_mul
      (1 + r)⁻¹)
  convert h using 1
  · funext k; simp
  · ring

/-- **Exercise 9(b)**, O&R p. 127: the first-order conditions `−1 − χ I_t + q_t = 0` and
`(1 + r) q_t = A_{t+1} F'(K_{t+1}) + q_{t+1}` with `K_{t+1} = K_t + I_t` imply
`K_{t+1} − K_t = (q_t − 1)/χ` and `q_{t+1} − q_t = r q_t − A_{t+1} F'(K_t + (q_t − 1)/χ)`. -/
theorem ex9_system {r χ : ℝ} (hχ : χ ≠ 0) {A : ℕ → ℝ} {F' : ℝ → ℝ} {K I q : ℕ → ℝ} {t : ℕ}
    (hfoc : -1 - χ * I t + q t = 0) (hacc : K (t + 1) = K t + I t)
    (heuler : (1 + r) * q t = A (t + 1) * F' (K (t + 1)) + q (t + 1)) :
    K (t + 1) - K t = (q t - 1) / χ ∧
      q (t + 1) - q t = r * q t - A (t + 1) * F' (K t + (q t - 1) / χ) := by
  have hI : I t = (q t - 1) / χ := by field_simp; linarith
  have hk : K (t + 1) = K t + (q t - 1) / χ := by rw [hacc, hI]
  refine ⟨by rw [hk]; ring, ?_⟩
  rw [← hk]; linarith

/-- **Exercise 9(c)**, O&R p. 127: for any `χ ≠ 0`, `(q̄, K̄)` is a rest point of the
Exercise 9 system iff `q̄ = 1` and `A F'(K̄) = r`; the steady state does not depend on the
adjustment-cost parameter `χ`. -/
theorem ex9_steady_state_iff {r χ A qb Kb : ℝ} (hχ : χ ≠ 0) {F' : ℝ → ℝ} :
    ((qb - 1) / χ = 0 ∧ r * qb - A * F' (Kb + (qb - 1) / χ) = 0) ↔ (qb = 1 ∧ A * F' Kb = r) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hq : qb = 1 := by
      rcases div_eq_zero_iff.1 h1 with h | h
      · linarith
      · exact absurd h hχ
    subst hq
    refine ⟨rfl, ?_⟩
    simp at h2; linarith
  · rintro ⟨rfl, h⟩
    simp [h]

/-- **The text's cost is homogeneous of degree one**, O&R (2.62), p. 106 and footnote 45:
`χ (λI)²/(2 λK) = λ χ I²/(2K)` for `λ ≠ 0`. -/
theorem text_cost_homogeneous (χ I K l : ℝ) (hl : l ≠ 0) :
    χ * (l * I) ^ 2 / (2 * (l * K)) = l * (χ * I ^ 2 / (2 * K)) := by
  by_cases hK : K = 0
  · simp [hK]
  · field_simp

/-- **Exercise 9(f): the cost `χ I²/2` is not homogeneous of degree one** in `(I, K)`, O&R
p. 127: doubling `(I, K) = (1, 1)` multiplies the cost by `4`, not `2` (for `χ ≠ 0`). -/
theorem ex9_cost_not_homogeneous {χ : ℝ} (hχ : χ ≠ 0) :
    χ * (2 * (1 : ℝ)) ^ 2 / 2 ≠ 2 * (χ * (1 : ℝ) ^ 2 / 2) := by
  intro h
  apply hχ
  linarith

/-- The Exercise 9 dividend `A_s F(K_s) − I_s − χ I_s²/2` (O&R p. 127). -/
noncomputable def ex9Dividend (A : ℕ → ℝ) (F : ℝ → ℝ) (K I : ℕ → ℝ) (χ : ℝ) (s : ℕ) : ℝ :=
  A s * F (K s) - I s - χ * I s ^ 2 / 2

/-- **Exercise 9(f), one-step identity**, O&R p. 127: in the Exercise 9 model, even with a
linear technology (`F'(K) K = F(K)`, the analogue of Euler's theorem when `L` is fixed), the
Hayashi recursion picks up an extra term:
`(1 + r) q_t K_{t+1} = (d_{t+1} − χ I_{t+1}²/2) + q_{t+1} K_{t+2}`. -/
theorem ex9_step {r χ : ℝ} {A : ℕ → ℝ} {F F' : ℝ → ℝ} {K I q : ℕ → ℝ}
    (hacc : ∀ s, K (s + 1) = K s + I s) (hfoc : ∀ s, -1 - χ * I s + q s = 0)
    (heuler : ∀ s, (1 + r) * q s = A (s + 1) * F' (K (s + 1)) + q (s + 1))
    (hlin : ∀ s, F' (K s) * K s = F (K s)) (t : ℕ) :
    (1 + r) * (q t * K (t + 1)) =
      (ex9Dividend A F K I χ (t + 1) - χ * I (t + 1) ^ 2 / 2) + q (t + 1) * K (t + 1 + 1) := by
  unfold ex9Dividend
  rw [hacc (t + 1), ← hlin (t + 1)]
  have hq : q (t + 1) = 1 + χ * I (t + 1) := by linarith [hfoc (t + 1)]
  rw [show (1 + r) * (q t * K (t + 1)) = ((1 + r) * q t) * K (t + 1) by ring, heuler t, hq]
  ring

/-- **Exercise 9(f): marginal q falls short of average q**, O&R p. 127. Under the hypotheses of
`ex9_step`, summable discounted dividends `V_t` and installation costs, and the no-bubble
condition on `q_s K_{s+1}`, `V_t − q_t K_{t+1} = Σ_{s ≥ t+1} (1 + r)^{-(s-t)} χ I_s²/2`. With
`r > −1`, `χ > 0` and some future `I_s ≠ 0`, this gap is strictly positive. -/
theorem ex9_average_q_gap {r χ : ℝ} (hr : 0 < 1 + r) (hχ : 0 < χ) {A : ℕ → ℝ}
    {F F' : ℝ → ℝ} {K I q : ℕ → ℝ}
    (hacc : ∀ s, K (s + 1) = K s + I s) (hfoc : ∀ s, -1 - χ * I s + q s = 0)
    (heuler : ∀ s, (1 + r) * q s = A (s + 1) * F' (K (s + 1)) + q (s + 1))
    (hlin : ∀ s, F' (K s) * K s = F (K s)) (t : ℕ) {V : ℝ}
    (hV : HasSum (fun s => (1 + r)⁻¹ ^ (s + 1) * ex9Dividend A F K I χ (t + s + 1)) V)
    (hc : Summable fun s => (1 + r)⁻¹ ^ (s + 1) * (χ * I (t + s + 1) ^ 2 / 2))
    (htail : Tendsto (fun T => (1 + r)⁻¹ ^ T * (q (t + T) * K (t + T + 1))) atTop (𝓝 0)) :
    V - q t * K (t + 1) = ∑' s, (1 + r)⁻¹ ^ (s + 1) * (χ * I (t + s + 1) ^ 2 / 2) ∧
      ((∃ n, I (t + n + 1) ≠ 0) → q t * K (t + 1) < V) := by
  have h := ex9_step (r := r) hacc hfoc heuler hlin
  have hsum : Summable fun s => (1 + r)⁻¹ ^ (s + 1) *
      (ex9Dividend A F K I χ (t + s + 1) - χ * I (t + s + 1) ^ 2 / 2) := by
    have := hV.summable.sub hc
    refine this.congr fun s => ?_
    ring
  have hq := hasSum_of_tail (x := fun s => q s * K (s + 1))
    (y := fun s => ex9Dividend A F K I χ s - χ * I s ^ 2 / 2) hr.ne' h t hsum htail
  have hdiff := hV.sub hq
  have hgap : V - q t * K (t + 1) = ∑' s, (1 + r)⁻¹ ^ (s + 1) * (χ * I (t + s + 1) ^ 2 / 2) := by
    refine (HasSum.tsum_eq ?_).symm
    refine hdiff.congr_fun fun s => ?_
    ring
  refine ⟨hgap, fun ⟨n, hn⟩ => ?_⟩
  have hb : 0 < (1 + r)⁻¹ := inv_pos.2 hr
  have hpos : 0 < ∑' s, (1 + r)⁻¹ ^ (s + 1) * (χ * I (t + s + 1) ^ 2 / 2) := by
    refine hc.tsum_pos (fun s => by positivity) n ?_
    have : 0 < I (t + n + 1) ^ 2 := by positivity
    positivity
  linarith

/-- **Exercise 9(f): an explicit counterexample**, O&R p. 127. Take `r = 1`, `A = 2`,
`F(K) = K`, `χ = 1`, `q_s = 2`, `I_s = 1`, `K_s = s + 1`. All first-order conditions and the
no-bubble condition hold, yet `q_0 K_1 = 4` differs from average q times capital:
`V_0 − q_0 K_1 = Σ 2^{-(s+1)}/2 = 1/2 > 0`. -/
theorem ex9_counterexample :
    let K : ℕ → ℝ := fun s => s + 1
    let I : ℕ → ℝ := fun _ => 1
    let q : ℕ → ℝ := fun _ => 2
    let A : ℕ → ℝ := fun _ => 2
    (∀ s, K (s + 1) = K s + I s) ∧ (∀ s, -1 - 1 * I s + q s = 0) ∧
      (∀ s, (1 + 1) * q s = A (s + 1) * (fun _ => (1 : ℝ)) (K (s + 1)) + q (s + 1)) ∧
      (∀ s, (fun _ => (1 : ℝ)) (K s) * K s = id (K s)) ∧
      Tendsto (fun T => (1 + 1 : ℝ)⁻¹ ^ T * (q (0 + T) * K (0 + T + 1))) atTop (𝓝 0) ∧
      ∃ V : ℝ, HasSum (fun s => (1 + 1 : ℝ)⁻¹ ^ (s + 1) * ex9Dividend A id K I 1 (0 + s + 1)) V ∧
        V - q 0 * K 1 = 1 / 2 := by
  intro K I q A
  have hhalf : (1 + 1 : ℝ)⁻¹ = 1 / 2 := by norm_num
  have hg := summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hn := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := 1 / 2) (by norm_num)
  have hVs : Summable fun s => (1 + 1 : ℝ)⁻¹ ^ (s + 1) * ex9Dividend A id K I 1 (0 + s + 1) := by
    refine (hn.add (hg.mul_left (5 / 4))).congr fun s => ?_
    simp only [ex9Dividend, K, I, A, id, hhalf]
    push_cast
    ring
  have hc : Summable fun s => (1 + 1 : ℝ)⁻¹ ^ (s + 1) * (1 * I (0 + s + 1) ^ 2 / 2) := by
    refine (hg.mul_left (1 / 4)).congr fun s => ?_
    simp only [I, hhalf]
    ring
  have htail : Tendsto (fun T => (1 + 1 : ℝ)⁻¹ ^ T * (q (0 + T) * K (0 + T + 1))) atTop
      (𝓝 0) := by
    have h1 := tendsto_self_mul_const_pow_of_lt_one (r := 1 / 2) (by norm_num) (by norm_num)
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)
    have h3 := (h1.const_mul 2).add (h2.const_mul 4)
    simp only [mul_zero, add_zero] at h3
    refine h3.congr fun T => ?_
    simp only [q, K, hhalf]
    push_cast
    ring
  have hacc : ∀ s, K (s + 1) = K s + I s := fun s => by simp only [K, I]; push_cast; ring
  have hfoc : ∀ s, -1 - 1 * I s + q s = 0 := fun s => by simp only [I, q]; norm_num
  have heul : ∀ s, (1 + 1) * q s = A (s + 1) * (fun _ => (1 : ℝ)) (K (s + 1)) + q (s + 1) :=
    fun s => by simp only [A, q]; norm_num
  have hlin : ∀ s, (fun _ => (1 : ℝ)) (K s) * K s = id (K s) := fun s => by simp
  refine ⟨hacc, hfoc, heul, hlin, htail, _, hVs.hasSum, ?_⟩
  obtain ⟨hgap, -⟩ := ex9_average_q_gap (r := 1) (χ := 1) (by norm_num) (by norm_num)
    (A := A) (F := id) (F' := fun _ => 1) hacc hfoc heul hlin 0 hVs.hasSum hc htail
  rw [hgap]
  have : HasSum (fun s => (1 + 1 : ℝ)⁻¹ ^ (s + 1) * (1 * I (0 + s + 1) ^ 2 / 2)) (1 / 2) := by
    have := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (1 / 4)
    convert this using 1
    · funext s; simp only [I, hhalf]; ring
    · norm_num
  exact this.tsum_eq

end ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Trend productivity growth and the debt–output ratio

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Appendix 2A, pp. 116–120, and Supplement B (steady-state condition), pp. 722–726.

Output is `Y = A K^α` with `0 < α < 1` and productivity growing so that output
grows at rate `g`, with `0 < g < r`. Investment is `I = (αg/r)Y` and government
spending is `G = ςY`, so net output `Y − I − G = nY` with
`n = 1 − αg/r − ς`. Consumption grows at the gross rate
`γ = (1 + r)^σ β^σ = 1 − ϑ`.

* **The current account (2.74)**: `CA_t = −ϑB_t − ((g + ϑ)/(r − g)) n Y_t`, from the
  tilted fundamental equation (2.20).
* **The debt–output ratio (2.75)** `b = B/Y` obeys the linear difference equation
  `b_{s+1} = (γ/(1 + g)) b_s − ((1 + g − γ)/((1 + g)(r − g))) n`. Its fixed point is
  **(2.76)** `b̄ = −n/(r − g)`. The ratio converges to `b̄` if `γ < 1 + g` and diverges
  from it if `γ > 1 + g`.
* **Below `b̄` consumption would be negative** (p. 119): `C/Y = (r + ϑ)(b − b̄)`.
* **The book's numbers** (p. 119): `r = 0.08`, `g = 0.05`, `α = 0.4`, `ς = 0.3` give
  `b̄ = −15` and a steady-state trade surplus of 45 percent of GDP.
* **The world interest rate (2.77)** `1 + r = (1 + g*)^{1/σ}/β` in a world growing at
  `g*`. With `β = 0.96`, `σ = 1`, `r = 0.08`, this gives `g* = 0.0368`. A fraction
  `(g − g*)/(1 + g) ≈ 1.26%` of the gap to `b̄` closes each year, and the half-life
  is 55 years (p. 120).
* **Supplement B**: with an endogenous discount factor `β(C)`, a steady state
  requires `β(C̄)(1 + r) = 1`. With constant `β` this forces `β(1 + r) = 1`.
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth

open PresentValue FundamentalCurrentAccount Filter Topology

/-! ### Technology (O&R pp. 116–117) -/

/-- With the marginal product of capital equal to `r`, `αY = rK`: the capital–output ratio is
`α/r` (O&R p. 116). -/
theorem capital_output {α A K r : ℝ} (hK : 0 < K) (hmpk : α * A * K ^ (α - 1) = r) :
    α * (A * K ^ α) = r * K := by
  rw [← hmpk, Real.rpow_sub hK, Real.rpow_one]
  field_simp

/-- **Investment is a constant share of output**, O&R p. 117: if capital grows at rate `g`
(`K_{s+1} = (1 + g)K_s`) and `αY_s = rK_s`, then `I_s = K_{s+1} − K_s = (αg/r)Y_s`. -/
theorem investment_share {α g r K K' Y : ℝ} (hr : r ≠ 0) (hK' : K' = (1 + g) * K)
    (hY : α * Y = r * K) : K' - K = α * g / r * Y := by
  rw [hK', show α * g / r * Y = g * (α * Y) / r by ring, hY]
  field_simp
  ring

/-- **Capital grows at the rate of output growth**: if `αA_sK_s^{α−1} = r` at both dates and
`A_{s+1} = (1 + g)^{1−α}A_s`, then `K_{s+1} = (1 + g)K_s` (O&R p. 116). -/
theorem capital_growth {α g r A A' K K' : ℝ} (hα : α < 1) (hg : -1 < g) (hK : 0 < K)
    (hK' : 0 < K') (hA : 0 < A) (hαpos : 0 < α) (hmpk : α * A * K ^ (α - 1) = r)
    (hmpk' : α * A' * K' ^ (α - 1) = r) (hA' : A' = (1 + g) ^ (1 - α) * A) :
    K' = (1 + g) * K := by
  have h1g : 0 < 1 + g := by linarith
  have hne : α - 1 ≠ 0 := by linarith
  -- both sides have the same (α − 1)-th power
  have e : K' ^ (α - 1) = ((1 + g) * K) ^ (α - 1) := by
    rw [Real.mul_rpow h1g.le hK.le]
    have hpow : (1 + g) ^ (α - 1) * (1 + g) ^ (1 - α) = 1 := by
      rw [← Real.rpow_add h1g, show α - 1 + (1 - α) = 0 by ring, Real.rpow_zero]
    have h2 : α * A * ((1 + g) ^ (1 - α) * K' ^ (α - 1)) = α * A * K ^ (α - 1) := by
      rw [hmpk, ← hmpk', hA']; ring
    have h3 : (1 + g) ^ (1 - α) * K' ^ (α - 1) = K ^ (α - 1) := by
      have hαA : α * A ≠ 0 := (mul_pos hαpos hA).ne'
      exact mul_left_cancel₀ hαA (by linarith [h2])
    calc K' ^ (α - 1) = (1 + g) ^ (α - 1) * ((1 + g) ^ (1 - α) * K' ^ (α - 1)) := by
          rw [← mul_assoc, hpow, one_mul]
      _ = (1 + g) ^ (α - 1) * K ^ (α - 1) := by rw [h3]
  have := congrArg (fun x : ℝ => x ^ (α - 1)⁻¹) e
  rwa [← Real.rpow_mul hK'.le, ← Real.rpow_mul (mul_pos h1g hK).le, mul_inv_cancel₀ hne,
    Real.rpow_one, Real.rpow_one] at this

/-! ### The current account and the debt–output ratio -/

/-- **The current account with trend growth**, O&R (2.74), p. 117. Output grows at rate `g < r`,
investment is `(αg/r)Y` and government spending `ςY`. If consumption follows the tilted rule
(2.16), then `CA₀ = −ϑB₀ − ((g + ϑ)/(r − g)) (1 − αg/r − ς) Y₀`. -/
theorem current_account_trend {r g α ς ϑ B0 Y0 C0 : ℝ} (hr : 0 < r) (hg : -1 < g) (hgr : g < r)
    (hC : C0 = (r + ϑ) / (1 + r) *
      wealth r B0 (fun s => (1 + g) ^ s * Y0) (fun s => ς * ((1 + g) ^ s * Y0))
        (fun s => α * g / r * ((1 + g) ^ s * Y0))) :
    currentAccount r B0 C0 (fun s => (1 + g) ^ s * Y0) (fun s => ς * ((1 + g) ^ s * Y0))
        (fun s => α * g / r * ((1 + g) ^ s * Y0)) =
      -ϑ * B0 - (g + ϑ) / (r - g) * (1 - α * g / r - ς) * Y0 := by
  have hr1 : (1 : ℝ) + r ≠ 0 := by linarith
  have hrg : r - g ≠ 0 := by linarith
  have hrne : r ≠ 0 := hr.ne'
  have hnet : (fun s : ℕ => (1 + g) ^ s * Y0 - ς * ((1 + g) ^ s * Y0) -
      α * g / r * ((1 + g) ^ s * Y0)) = fun s => (1 + g) ^ s * ((1 - α * g / r - ς) * Y0) := by
    funext s; ring
  have hW : wealth r B0 (fun s => (1 + g) ^ s * Y0) (fun s => ς * ((1 + g) ^ s * Y0))
      (fun s => α * g / r * ((1 + g) ^ s * Y0)) =
      (1 + r) * B0 + (1 + r) / (r - g) * ((1 - α * g / r - ς) * Y0) := by
    unfold wealth
    rw [hnet, pv_geometric hg hgr]
  unfold currentAccount
  rw [hC, hW]
  simp only [pow_zero, one_mul]
  field_simp
  ring

/-- **The debt–output ratio difference equation**, O&R (2.75), p. 117: if at every date
`B_{s+1} − B_s = −ϑB_s − ((g + ϑ)/(r − g)) n Y_s` (eq. (2.74) applied at date `s`) and
`Y_{s+1} = (1 + g)Y_s`, then with `γ = 1 − ϑ`,
`B_{s+1}/Y_{s+1} = (γ/(1 + g)) B_s/Y_s − ((1 + g − γ)/((1 + g)(r − g))) n`. -/
theorem debt_ratio_recursion {r g ϑ n : ℝ} (hg : -1 < g) (hgr : g < r) {B Y : ℕ → ℝ}
    (hY0 : ∀ s, 0 < Y s) (hY : ∀ s, Y (s + 1) = (1 + g) * Y s)
    (hCA : ∀ s, B (s + 1) - B s = -ϑ * B s - (g + ϑ) / (r - g) * n * Y s) (s : ℕ) :
    B (s + 1) / Y (s + 1) =
      (1 - ϑ) / (1 + g) * (B s / Y s) - (1 + g - (1 - ϑ)) / ((1 + g) * (r - g)) * n := by
  have h1g : (1 : ℝ) + g ≠ 0 := by linarith
  have hrg : r - g ≠ 0 := by linarith
  have hYs := (hY0 s).ne'
  have hB : B (s + 1) = (1 - ϑ) * B s - (g + ϑ) / (r - g) * n * Y s := by linarith [hCA s]
  rw [hB, hY s]
  field_simp
  ring

/-- **The steady-state debt–output ratio**, O&R (2.76), p. 117: `b̄ = −(1 − ς − αg/r)/(r − g)` is a
fixed point of (2.75), and the only one when `γ ≠ 1 + g`. -/
theorem steady_debt_ratio {r g γ n b : ℝ} (hg : -1 < g) (hgr : g < r) (hγ : γ ≠ 1 + g) :
    b = γ / (1 + g) * b - (1 + g - γ) / ((1 + g) * (r - g)) * n ↔ b = -n / (r - g) := by
  have h1g : (1 : ℝ) + g ≠ 0 := by linarith
  have hrg : r - g ≠ 0 := by linarith
  have hγ' : 1 + g - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  constructor
  · intro h
    field_simp at h ⊢
    have : (1 + g - γ) * (b * (r - g) + n) = 0 := by linear_combination h
    have := (mul_eq_zero.1 this).resolve_left hγ'
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- **Deviations from the steady state decay geometrically**: if `b` obeys (2.75), then
`b_s − b̄ = (γ/(1 + g))^s (b₀ − b̄)` (O&R p. 120 and Figure 2.12). -/
theorem debt_ratio_deviation {r g γ n : ℝ} (hg : -1 < g) (hgr : g < r) {b : ℕ → ℝ}
    (hb : ∀ s, b (s + 1) = γ / (1 + g) * b s - (1 + g - γ) / ((1 + g) * (r - g)) * n)
    (s : ℕ) : b s - (-n / (r - g)) = (γ / (1 + g)) ^ s * (b 0 - (-n / (r - g))) := by
  have h1g : (1 : ℝ) + g ≠ 0 := by linarith
  have hrg : r - g ≠ 0 := by linarith
  induction s with
  | zero => simp
  | succ s ih =>
    rw [hb s, pow_succ]
    have e : γ / (1 + g) * b s - (1 + g - γ) / ((1 + g) * (r - g)) * n - -n / (r - g) =
        γ / (1 + g) * (b s - -n / (r - g)) := by
      field_simp
      ring
    rw [e, ih]
    ring

/-- **Stability** (O&R p. 117): if `0 ≤ γ < 1 + g`, the debt–output ratio converges to `b̄` from
any initial value. -/
theorem debt_ratio_tendsto {r g γ n : ℝ} (hg : -1 < g) (hgr : g < r) (hγ0 : 0 ≤ γ)
    (hγ : γ < 1 + g) {b : ℕ → ℝ}
    (hb : ∀ s, b (s + 1) = γ / (1 + g) * b s - (1 + g - γ) / ((1 + g) * (r - g)) * n) :
    Tendsto b atTop (𝓝 (-n / (r - g))) := by
  have h1g : (0 : ℝ) < 1 + g := by linarith
  have hq0 : 0 ≤ γ / (1 + g) := div_nonneg hγ0 h1g.le
  have hq1 : γ / (1 + g) < 1 := (div_lt_one h1g).2 hγ
  have hdev : Tendsto (fun s => (γ / (1 + g)) ^ s * (b 0 - -n / (r - g))) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (b 0 - -n / (r - g))
  have e : b = fun s => -n / (r - g) + (γ / (1 + g)) ^ s * (b 0 - -n / (r - g)) := by
    funext s
    linarith [debt_ratio_deviation hg hgr hb s]
  rw [e]
  simpa using tendsto_const_nhds.add hdev

/-- **Instability** (O&R p. 119): if `γ > 1 + g`, any initial ratio other than `b̄` diverges from
it. -/
theorem debt_ratio_diverges {r g γ n : ℝ} (hg : -1 < g) (hgr : g < r) (hγ : 1 + g < γ)
    {b : ℕ → ℝ}
    (hb : ∀ s, b (s + 1) = γ / (1 + g) * b s - (1 + g - γ) / ((1 + g) * (r - g)) * n)
    (h0 : b 0 ≠ -n / (r - g)) :
    Tendsto (fun s => |b s - (-n / (r - g))|) atTop atTop := by
  have h1g : (0 : ℝ) < 1 + g := by linarith
  have hq1 : 1 < γ / (1 + g) := (one_lt_div h1g).2 hγ
  have hd : 0 < |b 0 - -n / (r - g)| := abs_pos.2 (sub_ne_zero.2 h0)
  have e : (fun s => |b s - (-n / (r - g))|) =
      fun s => (γ / (1 + g)) ^ s * |b 0 - -n / (r - g)| := by
    funext s
    rw [debt_ratio_deviation hg hgr hb s, abs_mul, abs_pow,
      abs_of_pos (by linarith : (0 : ℝ) < γ / (1 + g))]
  rw [e]
  exact (tendsto_pow_atTop_atTop_of_one_lt hq1).atTop_mul_const hd

/-- **Knife edge** (O&R p. 119): if `γ = 1 + g`, the debt–output ratio stays at its initial
value. -/
theorem debt_ratio_constant {r g n : ℝ} (hg : -1 < g) {b : ℕ → ℝ}
    (hb : ∀ s, b (s + 1) = (1 + g) / (1 + g) * b s -
      (1 + g - (1 + g)) / ((1 + g) * (r - g)) * n) (s : ℕ) : b s = b 0 := by
  have h1g : (1 : ℝ) + g ≠ 0 := by linarith
  induction s with
  | zero => rfl
  | succ s ih => rw [hb s, div_self h1g, sub_self, zero_div, zero_mul, sub_zero, one_mul, ih]

/-- **Consumption–output ratio**, O&R p. 118: under (2.16) with net output `nY` growing at `g`,
`C/Y = (r + ϑ)[B/Y + n/(r − g)] = (r + ϑ)(b − b̄)`. -/
theorem consumption_output_ratio {r g α ς ϑ B0 Y0 C0 : ℝ} (hr : 0 < r) (hg : -1 < g)
    (hgr : g < r) (hY0 : 0 < Y0)
    (hC : C0 = (r + ϑ) / (1 + r) *
      wealth r B0 (fun s => (1 + g) ^ s * Y0) (fun s => ς * ((1 + g) ^ s * Y0))
        (fun s => α * g / r * ((1 + g) ^ s * Y0))) :
    C0 / Y0 = (r + ϑ) * (B0 / Y0 - (-(1 - α * g / r - ς) / (r - g))) := by
  have hr1 : (1 : ℝ) + r ≠ 0 := by linarith
  have hrg : r - g ≠ 0 := by linarith
  have hnet : (fun s : ℕ => (1 + g) ^ s * Y0 - ς * ((1 + g) ^ s * Y0) -
      α * g / r * ((1 + g) ^ s * Y0)) = fun s => (1 + g) ^ s * ((1 - α * g / r - ς) * Y0) := by
    funext s; ring
  rw [hC]
  unfold wealth
  rw [hnet, pv_geometric hg hgr]
  have := hY0.ne'
  field_simp
  ring

/-- **Debt below `b̄` is infeasible**, O&R p. 119: if `r + ϑ > 0` (i.e. `γ < 1 + r`), an
asset–output ratio below `b̄` would require negative consumption. -/
theorem consumption_neg_below_steady {r g α ς ϑ B0 Y0 C0 : ℝ} (hr : 0 < r) (hg : -1 < g)
    (hgr : g < r) (hY0 : 0 < Y0) (hrϑ : 0 < r + ϑ)
    (hC : C0 = (r + ϑ) / (1 + r) *
      wealth r B0 (fun s => (1 + g) ^ s * Y0) (fun s => ς * ((1 + g) ^ s * Y0))
        (fun s => α * g / r * ((1 + g) ^ s * Y0)))
    (hbelow : B0 / Y0 < -(1 - α * g / r - ς) / (r - g)) : C0 < 0 := by
  have h := consumption_output_ratio hr hg hgr hY0 hC
  have hneg : C0 / Y0 < 0 := by rw [h]; exact mul_neg_of_pos_of_neg hrϑ (by linarith)
  by_contra hc
  push Not at hc
  linarith [div_nonneg hc hY0.le]

/-- The steady-state ratio is minus the present value of net output relative to current output:
`−b̄ = (1/((1 + r)Y_t)) Σ ((1 + g)/(1 + r))^{s−t} n Y_t = n/(r − g)` (O&R p. 118). -/
theorem steady_ratio_eq_pv {r g n Y0 : ℝ} (hg : -1 < g) (hgr : g < r) (hY0 : 0 < Y0) :
    pv r (fun s => (1 + g) ^ s * (n * Y0)) / ((1 + r) * Y0) = n / (r - g) := by
  rw [pv_geometric hg hgr]
  have : (1 : ℝ) + r ≠ 0 := by linarith
  have : r - g ≠ 0 := by linarith
  have := hY0.ne'
  field_simp

/-- **The consumption–output ratio vanishes** (O&R p. 118): if consumption grows at gross rate
`γ < 1 + g`, then `C_s/Y_s → 0`. -/
theorem consumption_output_tendsto_zero {g γ C0 Y0 : ℝ} (hg : -1 < g) (hγ0 : 0 ≤ γ)
    (hγ : γ < 1 + g) (hY0 : 0 < Y0) :
    Tendsto (fun s : ℕ => γ ^ s * C0 / ((1 + g) ^ s * Y0)) atTop (𝓝 0) := by
  have h1g : (0 : ℝ) < 1 + g := by linarith
  have hq0 : 0 ≤ γ / (1 + g) := div_nonneg hγ0 h1g.le
  have hq1 : γ / (1 + g) < 1 := (div_lt_one h1g).2 hγ
  have e : (fun s : ℕ => γ ^ s * C0 / ((1 + g) ^ s * Y0)) =
      fun s => (γ / (1 + g)) ^ s * (C0 / Y0) := by
    funext s
    rw [div_pow]
    have := hY0.ne'
    have : (1 + g) ^ s ≠ 0 := pow_ne_zero _ h1g.ne'
    field_simp
  rw [e]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (C0 / Y0)

/-! ### The book's numbers (O&R pp. 119–120) -/

/-- **The steady-state debt–output ratio is −15**, O&R p. 119: `r = 0.08`, `g = 0.05`, `α = 0.4`,
`ς = 0.3`. -/
theorem numerical_steady_ratio :
    -(1 - (0.4 : ℝ) * 0.05 / 0.08 - 0.3) / (0.08 - 0.05) = -15 := by norm_num

/-- **The steady-state trade surplus is 45 percent of GDP**, O&R p. 119: `TB/Y = −(r − g) b̄`. -/
theorem numerical_trade_surplus : -((0.08 : ℝ) - 0.05) * (-15) = 0.45 := by norm_num

/-- In a steady state with a constant asset–output ratio, `CA = gB` and the trade balance is
`TB = CA − rB = −(r − g)B` (O&R p. 119). -/
theorem steady_trade_balance {r g B : ℝ} : g * B - r * B = -(r - g) * B := by ring

/-- **The world interest rate**, O&R (2.77), p. 119: if the world is a closed economy growing at
`g*`, consumption grows at the rate of output, `(1 + r)^σ β^σ = 1 + g*`, so
`1 + r = (1 + g*)^{1/σ}/β`. -/
theorem world_interest_rate {r β σ gs : ℝ} (hr : 0 < 1 + r) (hβ : 0 < β) (hσ : 0 < σ)
    (h : (1 + r) ^ σ * β ^ σ = 1 + gs) :
    1 + r = (1 + gs) ^ (1 / σ) / β := by
  rw [← h, ← Real.mul_rpow hr.le hβ.le, ← Real.rpow_mul (mul_pos hr hβ).le,
    mul_one_div_cancel hσ.ne', Real.rpow_one]
  field_simp

/-- **World growth `g* = 3.68%`**, O&R p. 119: with `β = 0.96`, `σ = 1` and `r = 0.08`,
`1 + g* = β(1 + r)`. -/
theorem numerical_world_growth : (0.96 : ℝ) * (1 + 0.08) - 1 = 0.0368 := by norm_num

/-- **Convergence at the world growth rate**, O&R p. 120: with `γ = 1 + g*`, each period closes the
fraction `1 − (1 + g*)/(1 + g) = (g − g*)/(1 + g)` of the gap to `b̄`. -/
theorem fraction_closed {g gs : ℝ} (hg : -1 < g) : 1 - (1 + gs) / (1 + g) = (g - gs) / (1 + g) := by
  have : (1 : ℝ) + g ≠ 0 := by linarith
  field_simp
  ring

/-- **1.26 percent a year**, O&R p. 120: with `g = 0.05` and `g* = 0.0368` the fraction closed each
year is `0.0132/1.05 ≈ 0.01257`. -/
theorem numerical_fraction_closed :
    (0.0125 : ℝ) < (0.05 - 0.0368) / (1 + 0.05) ∧
      ((0.05 : ℝ) - 0.0368) / (1 + 0.05) < 0.0126 := by
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; norm_num
  · rw [div_lt_iff₀ (by norm_num)]; norm_num

/-- **A half-life of 55 years**, O&R p. 120: after 54 years more than half the gap remains, after 55
years less than half. -/
theorem numerical_half_life :
    (1 / 2 : ℝ) < ((1 + 0.0368) / (1 + 0.05)) ^ 54 ∧
      ((1 + 0.0368) / (1 + 0.05)) ^ 55 < (1 / 2 : ℝ) := by
  norm_num

/-! ### Supplement B: endogenous discounting (O&R pp. 722–726) -/

/-- **The Uzawa steady-state condition**, O&R SB(3)–(4), p. 724: if the marginal value of wealth
obeys `J'(W_t) = β(C_t)(1 + r) J'(W_{t+1})` and wealth is constant with `J'(W̄) ≠ 0`, then
`β(C̄)(1 + r) = 1`. -/
theorem uzawa_steady_state {βC r dJ : ℝ} (hdJ : dJ ≠ 0) (h : dJ = βC * (1 + r) * dJ) :
    βC * (1 + r) = 1 := by
  have : (βC * (1 + r) - 1) * dJ = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_right hdJ
  linarith

end ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth

set_option linter.style.longLine false
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Economy
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Economy.mk
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Economy.r
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Economy.r_pos
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Paths
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Paths.mk
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Paths.B
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Paths.Y
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Paths.C
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Paths.G
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Paths.I
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Economy.ca
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Economy.Flow
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Economy.flow_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.disc
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.disc_pos
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.disc_lt_one
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.one_add_mul_disc
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.discounted_telescope
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.tendsto_discounted
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.discounted_tendsto_zero_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.noPonzi_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.forward_telescope
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.forward_solution_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.tendsto_bubble
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.hasSum_disc_pow
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.sum_range_disc_pow
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.pv
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.permanent
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.pv_const
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.pv_permanent
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.pv_add
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.pv_sub
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.pv_smul
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.permanent_add
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.permanent_sub
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.permanent_const
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.pv_eq_head_add
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.summable_of_growth
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.pv_geometric
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.varDisc
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.varDisc_zero
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.varDisc_succ
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.varDisc_pos
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.varDisc_sub_succ
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.varDisc_telescope
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.varDisc_tendsto_zero_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.hasSum_rate_mul_varDisc
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.rate_mul_varDisc_zero_rates
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.tradeBalance
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.shiftPaths
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.residual
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.flow_iff_recursion
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.flow_shiftPaths
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.finite_identity
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.finite_ibc
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.flow_iff_finite_ibc
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.tendsto_terminal
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.transversality_iff_ibc
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.noPonzi_iff_ibc_le
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.terminal_pos_iff_ibc_lt
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.debt_limit
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.debt_limit_debtor
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.pv_tradeBalance
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.ibc_iff_trade_surplus
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.transversality_iff_trade_surplus
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.steady_ratio_trade_balance
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.output_claim_value
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.steady_ratio_burden
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.steady_ratio_transversality
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.naive_path
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.naive_tendsto_atTop
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.naive_tendsto_atBot
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.naive_limit_zero_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.naive_transversality_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.ex1_recursion
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.ex1_path
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.ex1_discounted_tb
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.ex1_ibc
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.ex1_transversality
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.ex1_not_summable
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.ex1_consumption
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.ex1_debt_unbounded
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint.ex1_eventually_infeasible
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.concave_le_tangent'
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.strictConcave_lt_tangent
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.lifetimeUtility
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.Admissible
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.IsOptimal
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.euler_iterate
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.discounted_marginal_utility
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.tsum_eq_add_of_eqOn_compl
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.isOptimal_of_euler
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.lifetimeUtility_lt_of_euler
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.pv_eq_of_optimal
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.euler_of_optimal
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.deriv_lt_of_strictConcave'
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.tilt_up
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.tilt_down
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.flat_of_beta_mul
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.continuation_optimal
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality.strotz_mrs_differ
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount.wealth
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount.currentAccount
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount.flat_consumption_level
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount.annuity_wealth
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount.fundamental_current_account
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount.fundamental_current_account_of_flat
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount.permanent_shock_no_ca
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount.temporary_shock_ca
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount.geometric_consumption_level
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount.tilted_current_account
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount.tilted_current_account_of_growth
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount.tilt_term_neg_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount.variable_rate_current_account
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount.variable_rate_current_account_flat
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.finite_horizon_consumption
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.finite_horizon_tendsto
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.wealth_unchanged_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.annuity_wealth_constant
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crra
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crraMU
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crraGrowth
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crraTilt
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crra_hasDerivAt
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crra_strictConcaveOn
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crra_euler_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crra_euler_path_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crraGrowth_eq
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crra_consumption_function
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crra_isOptimal
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crra_no_optimum
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.one_lt_sigma_of_one_le_tilt
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crra_consumption_strictAnti_beta
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.log_isOptimal
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.beta_mul_crraGrowth_rpow
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crraGrowth_rpow_neg_inv
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crraTheta
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crraValue
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crra_bellman_fixed_point
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crra_bellman_strict_max
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crra_bellman_isGreatest
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.crra_policy_formula
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.labourUtility
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.labourMUC
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.labourMUL
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.labourUtility_eq
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.labourUtility_hasDerivAt_C
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.labourUtility_hasDerivAt_leisure
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.labour_intratemporal_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.labour_consumption_growth
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.labour_tilt_up_of_wage_growth
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.hasSum_survival_weights
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.uncertain_lifetime_sum
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions.expected_utility_uncertain_lifetime
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.quadU
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.quadMU
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.hasDerivAt_quadU
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.hall_random_walk
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.hall_martingale
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.hall_condExp_future
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.condExp_budget_step
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.certainty_equivalence
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.certainty_equivalence_quadratic
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.ar1_condExp_step
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.ar1_forecast
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.output_forecast
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.ar1_moving_average
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.hasSum_disc_mul_pow
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.one_add_sub_ne_zero
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.consumption_ar1
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.consumption_innovation_form
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.current_account_ar1
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.current_account_ar1_ae
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.temporary_shock_effects
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.permanent_shock_effects
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.expected_current_account
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.deaton_consumption_response
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.nonstationary_forecast
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.nonstationary_revision
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.revision_weight_closed_form
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.consumption_change_revisions
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.hasSum_revision_weights
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.consumption_innovation_from_revisions
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.consumption_nonstationary
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.consumption_innovation_nonstationary
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.consumption_innovation_nonstationary_ae
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.current_account_nonstationary
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.consumption_more_volatile
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.condCov
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.condExp_mul_eq_add_condCov
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.condCov_const_add
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.risky_capital_return
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.convexOn_of_third_deriv_nonneg
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.crra_third_derivative
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.crra_marginal_utility_convex
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.condExp_marginal_utility_ge
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.mps_raises_expected_marginal_utility
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.precautionary_saving_two_period
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.lognormal_consumption_drift
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.lognormal_random_walk_drift
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption.euler_of_bellman
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.one_sub_disc_eq
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.sum_disc_diff_eq
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.campbell_finite_horizon
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.tail_tendsto_zero
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.summable_disc_diff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.campbell_deterministic
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.campbell_of_tail
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.forecastPermanent
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.campbellPV
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.campbellResidual
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.tsum_lintegral_ne_top
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.ae_summable_of_integral
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.condExp_tsum_of_integral
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.integral_abs_mul_condExp_le
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.summable_integral_diff_forecast
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.summable_integral_diff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.ae_summable_forecast
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.ae_condExp_diff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.campbell_eq_43
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.condExp_residual_ae
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.ae_forecast_recursion
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.ae_summable_diff_forecast
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.condExp_residual_eq_zero
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.ae_campbell_iff_noBubble
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.campbell_of_residual
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.campbell_iff_residual
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.residual_orthogonality_insufficient
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.condExp_coarser_info
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.pvChanges
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.forecastSum_ae_eq_condExp
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.campbell_coarser_information
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.tsum_pow_succ_eq_mul_inv
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.summable_pow_of_rowSum_lt_one
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.summable_disc_smul_pow
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.condExp_var_pow
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.condExp_coord
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.var_forecast_sum
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.var_predicted_current_account
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest.Stochastic.var_null_restriction
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.prevStock
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.userCost
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.durableAssets
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.durableWealth
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.durable_perturbation_feasible
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.hasDerivAt_durable_perturbation
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.durable_euler_of_isLocalMax
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.hasDerivAt_bond_perturbation
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.consumption_euler_of_isLocalMax
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.user_cost_of_euler
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.user_cost_of_euler_const
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.durableAssets_succ
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.durables_ibc_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.durableAssets_transversality
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.flat_nondurables
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.nondurables_consumption
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.durables_consumption
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.userCost_const
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.price_of_consumption_ratio
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.durables_stock_const
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.durables_purchases_after_t
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.durables_lump_sum
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.currentAccountDurables
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.durables_current_account
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.userCost_full_depreciation
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.userCost_tendsto_price
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Durables.durables_current_account_full_depreciation
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.share_arbitrage_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.dividend_capital_gain_eq
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.wealth_accumulation
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.initial_financial_wealth
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.ibc_iff_transversality
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.share_price_eq_pv_dividends_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.firmDividend
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.firmValue
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.labor_foc
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.capital_foc
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.euler_homogeneous
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.hasDerivAt_capital_partial
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.hasDerivAt_labor_partial
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.dividend_eq_of_foc
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.tendsto_pv_capital_dividends
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.pv_capital_dividends
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.firm_value_sub_capital
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.tendsto_firm_bubble
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.firm_value_eq_capital_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.firm_value_eq_capital
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.financial_wealth_eq_bonds_add_capital
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.ibc_financial_human_wealth
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.ibc_financial_human_wealth_expost
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.consumption_financial_human
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.saving_eq_financial
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.saving_permanent
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.current_account_permanent
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.modigliani_miller
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.modigliani_miller_consumer_wealth
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.iterated_asset_euler
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.tendsto_iterated_asset_euler
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.discounted_marginal_utility
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.utility_bubble_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.bubble_pos_iff_price_gt_pv
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth.price_ge_pv_of_nonneg
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.ScalarSolves
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.SeqBounded
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.scalar_general_solution
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.scalar_homogeneous_solution
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.scalar_add_homogeneous
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.scalar_particular_solution
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.scalar_particular_solves
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.capital_accumulation_solution
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.scalar_stable_bounded
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.backwardSolution
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.scalar_backward_solution
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.scalar_backward_unique
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.bubble_coeff_eq_zero
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.forwardSolution
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.forward_term_bound
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.forward_summable
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.forward_growth_bound
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.scalar_forward_solution
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.transversality_of_growth
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.scalar_forward_general_solution
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.scalar_forward_unique_of_transversality
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.scalar_forward_unique_of_growth
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.scalar_forward_unique_of_bounded
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.forward_bounded
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.forward_plus_bubble_unbounded
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.asset_value_no_bubble
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.SystemSolves
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.charpoly_factor
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.trace_det_eq_roots
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.vieta_of_distinct_roots
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.exists_distinct_real_roots
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.discriminant_pos_of_charpoly_one_neg
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.one_sub_trace_add_det
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.saddle_roots_of_charpoly_one_neg
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.charpoly_root
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.eigvec_eq
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.eigvec_alt_form
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.root_ne_a11
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.eigvec_distinct
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.eigvec_matrix_inverse
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.eigvec_diagonalizes
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.steady_state
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.steady_state_unique
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.charpoly_one_ne_zero_of_saddle
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.decouple
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.scalar_const_mul
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.decoupled_system
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.decoupled_reconstruct
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.recouple
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.seqBounded_lin_comb
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.saddle_path_unique
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.saddle_path_exists
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.saddle_path_constant_solves
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.saddle_path_constant_unique
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.lag_polynomial_factor
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.seqBounded_shift
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.polynomial_factorization_row1
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.polynomial_factorization_row2
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.companion_of_second_order
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.second_order_of_companion
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations.companion_lag_polynomial
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.forward_iterate
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.tail_of_hasSum
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.hasSum_of_tail
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.bubble_identity
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.bubble_overvalues
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.marginalEarnings
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.hasDerivAt_lagrangian_investment
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.investment_foc_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.hasDerivAt_lagrangian_capital
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.capital_foc_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.q_forward_solution
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.book_formula_sums_to_next_q
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.book_formula_eq_q_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.exact_dynamics
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.steady_state_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.steady_state_unique
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.capital_stationary_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.hasDerivAt_capital_dynamics_q
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.hasDerivAt_capital_dynamics_K
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.hasDerivAt_q_dynamics_q
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.hasDerivAt_q_dynamics_K
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.hasDerivAt_q_dynamics_quadratic
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.dq_locus
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.qMatrix
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.qMatrix_det_trace
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.qCharPoly
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.qDisc
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.omegaStable
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.omegaUnstable
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.qDisc_eq
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.omega_roots
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.omega_saddle
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.cobbDouglas_curvature
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.IsLinearQPath
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.saddle_path_solves
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.saddle_path_tendsto
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.saddle_q_above_one_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.saddle_monotone
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.saddle_path_unique
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.euler_of_homogeneous
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.dividend
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.hayashi_step
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.marginal_q_eq_average_q
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.rate_of_return_form
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.ex9_hasDerivAt_investment
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.ex9_hasDerivAt_capital
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.ex9_system
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.ex9_steady_state_iff
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.text_cost_homogeneous
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.ex9_cost_not_homogeneous
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.ex9Dividend
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.ex9_step
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.ex9_average_q_gap
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ.ex9_counterexample
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.capital_output
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.investment_share
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.capital_growth
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.current_account_trend
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.debt_ratio_recursion
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.steady_debt_ratio
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.debt_ratio_deviation
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.debt_ratio_tendsto
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.debt_ratio_diverges
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.debt_ratio_constant
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.consumption_output_ratio
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.consumption_neg_below_steady
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.steady_ratio_eq_pv
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.consumption_output_tendsto_zero
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.numerical_steady_ratio
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.numerical_trade_surplus
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.steady_trade_balance
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.world_interest_rate
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.numerical_world_growth
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.fraction_closed
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.numerical_fraction_closed
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.numerical_half_life
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth.uzawa_steady_state
