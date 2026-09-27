/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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
