/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue

/-!
# Constant-returns production: intensive form, zero profit, factor-price frontier

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.2.1,
pp. 204–206, eqs. (1)–(7), and footnote 19 (p. 220).

A constant-returns technology `Y = A F(K, L)` is described by its intensive form
`f(k) = F(k, 1)`, with marginal product `f′`. We assume (the book leaves this implicit)
that `f` is continuous on `[0, ∞)` with `f(0) ≥ 0`, differentiable on `(0, ∞)` with a
continuous, strictly decreasing, positive derivative `f′`, and Inada-type range conditions
(`f′` takes arbitrarily large values near zero and arbitrarily small positive values).

Results:
* the intensive form `F(K, L) = L f(K/L)` of a degree-one homogeneous `F`;
* the strict tangent-line inequality (strict concavity) proved from the mean value theorem;
* positive, strictly increasing marginal product of labour `f − f′k`;
* the zero-profit conditions (7) and "maximum CRS profit is zero":
  `A F(K, L) ≤ rK + wL` with equality iff `K/L = k(r)` (the tool behind fn. 19);
* existence and uniqueness of the capital–labour ratio `k(A, r)` with `A f′(k) = r` (IVT);
* the factor-price frontier (6) `w(r, A) = A f(k) − rk`, with the exact envelope derivatives
  `∂w/∂r = −k` and `∂w/∂A = f(k)`, and `∂k/∂r = 1/(A f″(k))`;
* the wage–rental ratio `ω(k) = (f − f′k)/f′` is a strictly increasing bijection of `(0, ∞)`,
  which is what makes the nontraded-sector equilibrium unique (T1 of §4.2.1).
-/

namespace ObstfeldRogoff.RealExchangeRate.CRSProduction

open Filter Topology Set

/-- Intensive form of a constant-returns technology, O&R §4.2.1, p. 205: `f(k) = F(k, 1)`
with marginal product `fp = f′`. The regularity, concavity and Inada-type hypotheses the
book uses implicitly are made explicit here. -/
structure IntensiveTech where
  f : ℝ → ℝ
  fp : ℝ → ℝ
  f_cont : ContinuousOn f (Ici 0)
  hasDeriv : ∀ k, 0 < k → HasDerivAt f (fp k) k
  fp_strictAnti : StrictAntiOn fp (Ioi 0)
  fp_cont : ContinuousOn fp (Ioi 0)
  fp_pos : ∀ k, 0 < k → 0 < fp k
  f_zero_nonneg : 0 ≤ f 0
  inada_zero : ∀ c : ℝ, ∃ k, 0 < k ∧ c < fp k
  inada_infty : ∀ c : ℝ, 0 < c → ∃ k, 0 < k ∧ fp k < c

/-- Intensive form of a constant-returns function, O&R §4.2.1, p. 205: if `F` is homogeneous
of degree one then `F(K, L) = L F(K/L, 1)` for `L > 0`. -/
theorem crs_intensive_form (F : ℝ → ℝ → ℝ) (hF : ∀ t K L : ℝ, 0 < t → F (t * K) (t * L) = t * F K L)
    {K L : ℝ} (hL : 0 < L) : F K L = L * F (K / L) 1 := by
  have := hF L (K / L) 1 hL
  rwa [mul_div_cancel₀ K hL.ne', mul_one] at this

/-- Squeeze criterion for a derivative (used for the envelope theorems in O&R §4.2):
if `(y − x) a(y) ≤ φ(y) − φ(x) ≤ (y − x) b(y)` near `x` and `a, b → c`, then `φ′(x) = c`. -/
theorem hasDerivAt_of_between {φ a b : ℝ → ℝ} {x c : ℝ} (ha : Tendsto a (𝓝[≠] x) (𝓝 c))
    (hb : Tendsto b (𝓝[≠] x) (𝓝 c))
    (h : ∀ᶠ y in 𝓝[≠] x, (y - x) * a y ≤ φ y - φ x ∧ φ y - φ x ≤ (y - x) * b y) :
    HasDerivAt φ c x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hmin : Tendsto (fun y => min (a y) (b y)) (𝓝[≠] x) (𝓝 (min c c)) := ha.min hb
  have hmax : Tendsto (fun y => max (a y) (b y)) (𝓝[≠] x) (𝓝 (max c c)) := ha.max hb
  rw [min_self] at hmin; rw [max_self] at hmax
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hmin hmax ?_ ?_
  · filter_upwards [h, self_mem_nhdsWithin] with y hy hne
    rw [slope_def_field]
    rcases lt_or_gt_of_ne (show y ≠ x from hne) with hlt | hgt
    · have hn : y - x < 0 := by linarith
      rw [le_div_iff_of_neg hn]
      exact le_trans hy.2 (by nlinarith [min_le_right (a y) (b y)])
    · have hp : 0 < y - x := by linarith
      rw [le_div_iff₀ hp]
      exact le_trans (by nlinarith [min_le_left (a y) (b y)]) hy.1
  · filter_upwards [h, self_mem_nhdsWithin] with y hy hne
    rw [slope_def_field]
    rcases lt_or_gt_of_ne (show y ≠ x from hne) with hlt | hgt
    · have hn : y - x < 0 := by linarith
      rw [div_le_iff_of_neg hn]
      exact le_trans (by nlinarith [le_max_left (a y) (b y)]) hy.1
    · have hp : 0 < y - x := by linarith
      rw [div_le_iff₀ hp]
      exact le_trans hy.2 (by nlinarith [le_max_right (a y) (b y)])

namespace IntensiveTech

variable (T : IntensiveTech)

/-- Marginal product of labour in intensive form, O&R (3), p. 205: `f(k) − f′(k)k`. -/
def mpl (k : ℝ) : ℝ := T.f k - T.fp k * k

/-- Strict tangent-line inequality (strict concavity of `f`), used implicitly in O&R §4.2.1:
for `x ≥ 0`, `k > 0`, `x ≠ k`, `f(x) < f(k) + f′(k)(x − k)`. Proved by the mean value
theorem from the strictly decreasing derivative. -/
theorem tangent_lt {x k : ℝ} (hx : 0 ≤ x) (hk : 0 < k) (hxk : x ≠ k) :
    T.f x < T.f k + T.fp k * (x - k) := by
  rcases lt_or_gt_of_ne hxk with h | h
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope T.f T.fp h
      (T.f_cont.mono fun y hy => le_trans hx hy.1)
      (fun y hy => T.hasDeriv y (lt_of_le_of_lt hx hy.1))
    have hc0 : 0 < c := lt_of_le_of_lt hx hc.1
    have hlt : T.fp k < T.fp c := T.fp_strictAnti hc0 hk hc.2
    rw [hcs, lt_div_iff₀ (by linarith)] at hlt
    nlinarith
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope T.f T.fp h
      (T.f_cont.mono fun y hy => le_trans hk.le hy.1)
      (fun y hy => T.hasDeriv y (lt_trans hk hy.1))
    have hc0 : 0 < c := lt_trans hk hc.1
    have hlt : T.fp c < T.fp k := T.fp_strictAnti hk hc0 hc.1
    rw [hcs, div_lt_iff₀ (by linarith)] at hlt
    nlinarith

/-- Weak tangent-line inequality, O&R §4.2.1: `f(x) ≤ f(k) + f′(k)(x − k)` for `x ≥ 0`,
`k > 0`. -/
theorem tangent_le {x k : ℝ} (hx : 0 ≤ x) (hk : 0 < k) :
    T.f x ≤ T.f k + T.fp k * (x - k) := by
  rcases eq_or_ne x k with h | h
  · subst h; simp
  · exact (T.tangent_lt hx hk h).le

/-- The marginal product of labour is positive, O&R (3), p. 205: `f(k) − f′(k)k > 0`. -/
theorem mpl_pos {k : ℝ} (hk : 0 < k) : 0 < T.mpl k := by
  have := T.tangent_lt le_rfl hk hk.ne
  unfold mpl
  linarith [T.f_zero_nonneg]

/-- Output per worker is positive, O&R §4.2.1: `f(k) > 0` for `k > 0`. -/
theorem f_pos {k : ℝ} (hk : 0 < k) : 0 < T.f k := by
  have h1 := T.mpl_pos hk
  have h2 := T.fp_pos k hk
  unfold mpl at h1
  nlinarith

/-- The marginal product of labour is strictly increasing in capital intensity,
O&R §4.2.1, p. 206 (the MPL schedule argument). -/
theorem mpl_strictMonoOn : StrictMonoOn T.mpl (Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have h1 := T.tangent_lt ha'.le hb' hab.ne
  have h2 : T.fp b < T.fp a := T.fp_strictAnti ha hb hab
  unfold mpl
  nlinarith

/-- Zero-profit condition, O&R (7), p. 208: if `A f′(k) = r` (2) and `A(f(k) − f′(k)k) = w`
(3), then `A f(k) = rk + w`. -/
theorem zero_profit {A r w k : ℝ} (hr : A * T.fp k = r) (hw : A * T.mpl k = w) :
    A * T.f k = r * k + w := by
  rw [← hr, ← hw]; unfold mpl; ring

/-- Maximum profit under constant returns is zero, O&R §4.2.1 and fn. 19, p. 220: at the
factor prices `r = A f′(k)`, `w = A(f(k) − f′(k)k)`, every input bundle `K ≥ 0`, `L > 0`
satisfies `A F(K, L) = A L f(K/L) ≤ rK + wL`. -/
theorem crs_profit_le {A r w k K L : ℝ} (hA : 0 < A) (hk : 0 < k) (hr : A * T.fp k = r)
    (hw : A * T.mpl k = w) (hK : 0 ≤ K) (hL : 0 < L) :
    A * (L * T.f (K / L)) ≤ r * K + w * L := by
  have ht := T.tangent_le (div_nonneg hK hL.le) hk
  have hAL : 0 < A * L := mul_pos hA hL
  have := mul_le_mul_of_nonneg_left ht hAL.le
  rw [← hr, ← hw]; unfold mpl
  have hKL : L * (K / L) = K := mul_div_cancel₀ K hL.ne'
  calc A * (L * T.f (K / L)) = A * L * T.f (K / L) := by ring
    _ ≤ A * L * (T.f k + T.fp k * (K / L - k)) := this
    _ = A * T.f k * L + A * T.fp k * (L * (K / L)) - A * T.fp k * k * L := by ring
    _ = A * T.fp k * K + A * (T.f k - T.fp k * k) * L := by rw [hKL]; ring

/-- Equality case of zero maximum profit, O&R fn. 19, p. 220: `A L f(K/L) = rK + wL` iff the
capital–labour ratio is the optimal one, `K/L = k`. -/
theorem crs_profit_eq_iff {A r w k K L : ℝ} (hA : 0 < A) (hk : 0 < k) (hr : A * T.fp k = r)
    (hw : A * T.mpl k = w) (hK : 0 ≤ K) (hL : 0 < L) :
    A * (L * T.f (K / L)) = r * K + w * L ↔ K / L = k := by
  constructor
  · intro heq
    by_contra hne
    have ht := T.tangent_lt (div_nonneg hK hL.le) hk hne
    have hAL : 0 < A * L := mul_pos hA hL
    have := mul_lt_mul_of_pos_left ht hAL
    have hKL : L * (K / L) = K := mul_div_cancel₀ K hL.ne'
    rw [← hr, ← hw] at heq; unfold mpl at heq
    have e2 : A * L * (T.f k + T.fp k * (K / L - k))
        = A * T.fp k * K + A * (T.f k - T.fp k * k) * L := by
      calc A * L * (T.f k + T.fp k * (K / L - k))
          = A * T.f k * L + A * T.fp k * (L * (K / L)) - A * T.fp k * k * L := by ring
        _ = _ := by rw [hKL]; ring
    nlinarith
  · intro h
    rw [h, ← hr, ← hw, ← h]; unfold mpl
    have hKL : L * (K / L) = K := mul_div_cancel₀ K hL.ne'
    calc A * (L * T.f (K / L)) = A * T.f (K / L) * L := by ring
      _ = A * T.fp (K / L) * (L * (K / L)) + A * (T.f (K / L) - T.fp (K / L) * (K / L)) * L := by
        ring
      _ = _ := by rw [hKL]

/-- Existence and uniqueness of the capital–labour ratio, O&R (2), p. 205 and p. 206
(`k_T = f′⁻¹(r/A_T)`): for every `x > 0` there is exactly one `k > 0` with `f′(k) = x`
(intermediate value theorem plus the Inada-type range conditions). -/
theorem existsUnique_fp_eq {x : ℝ} (hx : 0 < x) : ∃! k, 0 < k ∧ T.fp k = x := by
  obtain ⟨a, ha, hax⟩ := T.inada_zero x
  obtain ⟨b, hb, hbx⟩ := T.inada_infty x hx
  have hab : a ≤ b := by
    by_contra h
    push Not at h
    have := T.fp_strictAnti hb ha h
    linarith
  have hcont : ContinuousOn T.fp (Icc a b) := T.fp_cont.mono fun y hy => lt_of_lt_of_le ha hy.1
  obtain ⟨c, hc, hcx⟩ := intermediate_value_Icc' hab hcont ⟨hbx.le, hax.le⟩
  refine ⟨c, ⟨lt_of_lt_of_le ha hc.1, hcx⟩, ?_⟩
  rintro y ⟨hy, hyx⟩
  exact (T.fp_strictAnti.eq_iff_eq (show y ∈ Ioi (0 : ℝ) from hy)
    (show c ∈ Ioi (0 : ℝ) from lt_of_lt_of_le ha hc.1)).1 (hyx.trans hcx.symm) |>.symm

/-- The inverse of the marginal product, O&R p. 206: `kinv x = f′⁻¹(x)` for `x > 0`
(an arbitrary junk value otherwise). -/
noncomputable def kinv (x : ℝ) : ℝ :=
  Classical.epsilon fun k => 0 < k ∧ T.fp k = x

/-- Defining property of `f′⁻¹`, O&R p. 206: `f′⁻¹(x) > 0` and `f′(f′⁻¹(x)) = x`. -/
theorem kinv_spec {x : ℝ} (hx : 0 < x) : 0 < T.kinv x ∧ T.fp (T.kinv x) = x := by
  have h : ∃ k, 0 < k ∧ T.fp k = x := (T.existsUnique_fp_eq hx).exists
  exact Classical.epsilon_spec h

/-- `f′⁻¹` is continuous on `(0, ∞)`, O&R p. 206 (needed for the envelope derivatives). -/
theorem kinv_continuousAt {x : ℝ} (hx : 0 < x) : ContinuousAt T.kinv x := by
  obtain ⟨k0pos, hk0⟩ := T.kinv_spec hx
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · set a' := max a (T.kinv x / 2) with ha'
    have ha'pos : 0 < a' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have ha'lt : a' < T.kinv x := max_lt ha (by linarith)
    have hfa : x < T.fp a' := by
      rw [← hk0]; exact T.fp_strictAnti ha'pos k0pos ha'lt
    filter_upwards [Ioi_mem_nhds hx, gt_mem_nhds hfa] with y hy hyl
    obtain ⟨hky, hfy⟩ := T.kinv_spec (show (0 : ℝ) < y from hy)
    have : T.fp (T.kinv y) < T.fp a' := by rw [hfy]; exact hyl
    have := (T.fp_strictAnti.lt_iff_gt (show T.kinv y ∈ Ioi (0 : ℝ) from hky)
      (show a' ∈ Ioi (0 : ℝ) from ha'pos)).1 this
    exact lt_of_le_of_lt (le_max_left _ _) this
  · have hbpos : 0 < b := lt_trans k0pos hb
    have hfb : T.fp b < x := by rw [← hk0]; exact T.fp_strictAnti k0pos hbpos hb
    filter_upwards [Ioi_mem_nhds hx, lt_mem_nhds hfb] with y hy hyl
    obtain ⟨hky, hfy⟩ := T.kinv_spec (show (0 : ℝ) < y from hy)
    have : T.fp b < T.fp (T.kinv y) := by rw [hfy]; exact hyl
    exact (T.fp_strictAnti.lt_iff_gt (show b ∈ Ioi (0 : ℝ) from hbpos)
      (show T.kinv y ∈ Ioi (0 : ℝ) from hky)).1 this

/-- The optimal capital–labour ratio, O&R (2), p. 206: `k(A, r) = f′⁻¹(r/A)`. -/
noncomputable def kstar (A r : ℝ) : ℝ := T.kinv (r / A)

/-- First-order condition (2), O&R p. 205: `k(A, r) > 0` and `A f′(k(A, r)) = r`. -/
theorem kstar_foc {A r : ℝ} (hA : 0 < A) (hr : 0 < r) :
    0 < T.kstar A r ∧ A * T.fp (T.kstar A r) = r := by
  obtain ⟨h1, h2⟩ := T.kinv_spec (div_pos hr hA)
  refine ⟨h1, ?_⟩
  unfold kstar; rw [h2]; field_simp

/-- Uniqueness of the optimal capital–labour ratio, O&R (2), p. 206: any `k > 0` with
`A f′(k) = r` equals `k(A, r)`. -/
theorem kstar_unique {A r k : ℝ} (hA : 0 < A) (hr : 0 < r) (hk : 0 < k)
    (hfoc : A * T.fp k = r) : k = T.kstar A r := by
  obtain ⟨h1, h2⟩ := T.kstar_foc hA hr
  have := (T.existsUnique_fp_eq (div_pos hr hA)).unique (y₁ := k) (y₂ := T.kstar A r)
    ⟨hk, (eq_div_iff hA.ne').2 (by rw [mul_comm]; exact hfoc)⟩
    ⟨h1, (eq_div_iff hA.ne').2 (by rw [mul_comm]; exact h2)⟩
  exact this

/-- A higher interest rate lowers the capital–labour ratio, O&R p. 206
(`∂k_T/∂r < 0`, monotone form). -/
theorem kstar_strictAntiOn_r {A : ℝ} (hA : 0 < A) : StrictAntiOn (T.kstar A) (Ioi 0) := by
  intro r1 hr1 r2 hr2 h
  obtain ⟨k1, e1⟩ := T.kstar_foc hA hr1
  obtain ⟨k2, e2⟩ := T.kstar_foc hA hr2
  have : T.fp (T.kstar A r1) < T.fp (T.kstar A r2) := by
    have := mul_lt_mul_of_pos_left (show r1 / A < r2 / A from div_lt_div_of_pos_right h hA) hA
    rw [mul_div_cancel₀ _ hA.ne', mul_div_cancel₀ _ hA.ne'] at this
    nlinarith
  exact (T.fp_strictAnti.lt_iff_gt (show T.kstar A r1 ∈ Ioi (0 : ℝ) from k1)
    (show T.kstar A r2 ∈ Ioi (0 : ℝ) from k2)).1 this

/-- Continuity of `k(A, r)` in `r`, O&R p. 206. -/
theorem kstar_continuousAt_r {A r : ℝ} (hA : 0 < A) (hr : 0 < r) :
    ContinuousAt (T.kstar A) r :=
  ContinuousAt.comp (f := fun y => y / A) (T.kinv_continuousAt (div_pos hr hA))
    (continuousAt_id.div_const A)

/-- Continuity of `k(A, r)` in `A`, O&R p. 206. -/
theorem kstar_continuousAt_A {A r : ℝ} (hA : 0 < A) (hr : 0 < r) :
    ContinuousAt (fun a => T.kstar a r) A :=
  ContinuousAt.comp (f := fun a => r / a) (T.kinv_continuousAt (div_pos hr hA))
    (continuousAt_const.div continuousAt_id hA.ne')

/-- Derivative of the capital–labour ratio, O&R p. 206: if `f′` has derivative `f″(k) ≠ 0` at
`k = k(A, r)` then `∂k/∂r = 1/(A f″(k))`. -/
theorem kstar_hasDerivAt_r {A r fpp : ℝ} (hA : 0 < A) (hr : 0 < r)
    (hfpp : HasDerivAt T.fp fpp (T.kstar A r)) (hne : fpp ≠ 0) :
    HasDerivAt (T.kstar A) (A * fpp)⁻¹ r := by
  refine HasDerivAt.of_local_left_inverse (f := fun k => A * T.fp k)
    (T.kstar_continuousAt_r hA hr) (hfpp.const_mul A) (mul_ne_zero hA.ne' hne) ?_
  filter_upwards [Ioi_mem_nhds hr] with y hy
  exact (T.kstar_foc hA hy).2

/-- The wage from the factor-price frontier, O&R (3) and (6), p. 206:
`w(r, A) = A(f(k) − f′(k)k)` at `k = k(A, r)`. -/
noncomputable def wage (A r : ℝ) : ℝ := A * T.mpl (T.kstar A r)

/-- Factor-price frontier (6), O&R p. 206: `w(r, A) = A f(k(A, r)) − r k(A, r)`. -/
theorem wage_frontier {A r : ℝ} (hA : 0 < A) (hr : 0 < r) :
    T.wage A r = A * T.f (T.kstar A r) - r * T.kstar A r := by
  have := (T.kstar_foc hA hr).2
  unfold wage mpl; linear_combination (-T.kstar A r) * this

/-- The wage is positive, O&R (3), p. 205. -/
theorem wage_pos {A r : ℝ} (hA : 0 < A) (hr : 0 < r) : 0 < T.wage A r :=
  mul_pos hA (T.mpl_pos (T.kstar_foc hA hr).1)

/-- The frontier wage is the maximum of `A f(k) − rk` over `k ≥ 0`, O&R (6) with fn. 19:
the envelope characterisation behind `∂w/∂r = −k` and `∂w/∂A = f(k)`. -/
theorem wage_isMax {A r k : ℝ} (hA : 0 < A) (hr : 0 < r) (hk : 0 ≤ k) :
    A * T.f k - r * k ≤ T.wage A r := by
  obtain ⟨h1, h2⟩ := T.kstar_foc hA hr
  have := T.crs_profit_le hA h1 h2 rfl hk one_pos
  simp only [div_one, one_mul, mul_one] at this
  unfold wage; linarith

/-- Slope of the factor-price frontier, O&R p. 206: `∂w(r, A)/∂r = −k(A, r)` (exact, via the
envelope theorem). -/
theorem wage_hasDerivAt_r {A r : ℝ} (hA : 0 < A) (hr : 0 < r) :
    HasDerivAt (T.wage A) (-T.kstar A r) r := by
  have hk : Tendsto (fun y => -T.kstar A y) (𝓝[≠] r) (𝓝 (-T.kstar A r)) :=
    ((T.kstar_continuousAt_r hA hr).tendsto.neg).mono_left nhdsWithin_le_nhds
  refine hasDerivAt_of_between tendsto_const_nhds hk ?_
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hr)] with y hy
  have hy' : (0 : ℝ) < y := hy
  have e1 := T.wage_frontier hA hr
  have e2 := T.wage_frontier hA hy'
  have i1 := T.wage_isMax hA hy' (T.kstar_foc hA hr).1.le
  have i2 := T.wage_isMax hA hr (T.kstar_foc hA hy').1.le
  constructor <;> nlinarith

/-- Productivity raises the frontier wage, O&R p. 208: `∂w(r, A)/∂A = f(k(A, r))` (exact,
envelope theorem). -/
theorem wage_hasDerivAt_A {A r : ℝ} (hA : 0 < A) (hr : 0 < r) :
    HasDerivAt (fun a => T.wage a r) (T.f (T.kstar A r)) A := by
  have hfk : ContinuousAt T.f (T.kstar A r) :=
    (T.hasDeriv _ (T.kstar_foc hA hr).1).continuousAt
  have hk : Tendsto (fun a => T.f (T.kstar a r)) (𝓝[≠] A) (𝓝 (T.f (T.kstar A r))) :=
    ((ContinuousAt.comp (f := fun a => T.kstar a r) hfk
      (T.kstar_continuousAt_A hA hr)).tendsto).mono_left nhdsWithin_le_nhds
  refine hasDerivAt_of_between tendsto_const_nhds hk ?_
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hA)] with y hy
  have hy' : (0 : ℝ) < y := hy
  have e1 := T.wage_frontier hA hr
  have e2 := T.wage_frontier hy' hr
  have i1 := T.wage_isMax hy' hr (T.kstar_foc hA hr).1.le
  have i2 := T.wage_isMax hA hr (T.kstar_foc hy' hr).1.le
  constructor <;> nlinarith

/-- Total differential of the factor-price frontier along a path, O&R (6) and (8), pp. 206–208:
if productivity `A(t)` and the interest rate `R(t)` are differentiable at `x`, then
`d w(R(t), A(t))/dt = A′ f(k) − R′ k` at `k = k(A(x), R(x))` (exact envelope theorem). -/
theorem wage_path_hasDerivAt {A R : ℝ → ℝ} {A' R' x : ℝ} (hA : HasDerivAt A A' x)
    (hR : HasDerivAt R R' x) (hA0 : 0 < A x) (hR0 : 0 < R x) :
    HasDerivAt (fun y => T.wage (A y) (R y))
      (A' * T.f (T.kstar (A x) (R x)) - R' * T.kstar (A x) (R x)) x := by
  set k0 := T.kstar (A x) (R x) with hk0def
  have hk0 := (T.kstar_foc hA0 hR0).1
  have hkc : ContinuousAt (fun y => T.kstar (A y) (R y)) x :=
    ContinuousAt.comp (f := fun y => R y / A y) (T.kinv_continuousAt (div_pos hR0 hA0))
      (hR.continuousAt.div hA.continuousAt hA0.ne')
  have hfk : ContinuousAt (fun y => T.f (T.kstar (A y) (R y))) x :=
    ContinuousAt.comp (f := fun y => T.kstar (A y) (R y))
      (T.hasDeriv _ hk0).continuousAt hkc
  have sA := hasDerivAt_iff_tendsto_slope.1 hA
  have sR := hasDerivAt_iff_tendsto_slope.1 hR
  have ha : Tendsto (fun y => slope A x y * T.f k0 - slope R x y * k0) (𝓝[≠] x)
      (𝓝 (A' * T.f k0 - R' * k0)) :=
    (sA.mul tendsto_const_nhds).sub (sR.mul tendsto_const_nhds)
  have hb : Tendsto (fun y => slope A x y * T.f (T.kstar (A y) (R y))
      - slope R x y * T.kstar (A y) (R y)) (𝓝[≠] x) (𝓝 (A' * T.f k0 - R' * k0)) :=
    (sA.mul (hfk.tendsto.mono_left nhdsWithin_le_nhds)).sub
      (sR.mul (hkc.tendsto.mono_left nhdsWithin_le_nhds))
  refine hasDerivAt_of_between ha hb ?_
  have eA : ∀ᶠ y in 𝓝[≠] x, 0 < A y :=
    nhdsWithin_le_nhds (hA.continuousAt.eventually (Ioi_mem_nhds hA0))
  have eR : ∀ᶠ y in 𝓝[≠] x, 0 < R y :=
    nhdsWithin_le_nhds (hR.continuousAt.eventually (Ioi_mem_nhds hR0))
  filter_upwards [eA, eR, self_mem_nhdsWithin] with y hAy hRy hne
  have hyx : y - x ≠ 0 := sub_ne_zero.2 hne
  have dA : (y - x) * slope A x y = A y - A x := by
    rw [slope_def_field]; field_simp
  have dR : (y - x) * slope R x y = R y - R x := by
    rw [slope_def_field]; field_simp
  have hky := (T.kstar_foc hAy hRy).1
  have e1 := T.wage_frontier hA0 hR0
  have e2 := T.wage_frontier hAy hRy
  have i1 := T.wage_isMax hAy hRy hk0.le
  have i2 := T.wage_isMax hA0 hR0 hky.le
  constructor
  · have : (y - x) * (slope A x y * T.f k0 - slope R x y * k0)
        = (A y - A x) * T.f k0 - (R y - R x) * k0 := by
      rw [← dA, ← dR]; ring
    rw [this]; rw [← hk0def] at e1; nlinarith
  · have : (y - x) * (slope A x y * T.f (T.kstar (A y) (R y))
        - slope R x y * T.kstar (A y) (R y))
        = (A y - A x) * T.f (T.kstar (A y) (R y)) - (R y - R x) * T.kstar (A y) (R y) := by
      rw [← dA, ← dR]; ring
    rw [this]; rw [← hk0def] at e1; nlinarith

/-- The frontier wage is strictly decreasing in `r`, O&R (6), p. 206. -/
theorem wage_strictAntiOn_r {A : ℝ} (hA : 0 < A) : StrictAntiOn (T.wage A) (Ioi 0) := by
  intro r1 hr1 r2 hr2 h
  have hr1' : (0 : ℝ) < r1 := hr1
  have hr2' : (0 : ℝ) < r2 := hr2
  have e2 := T.wage_frontier hA hr2'
  have hk2 := (T.kstar_foc hA hr2').1
  have i := T.wage_isMax hA hr1' hk2.le
  nlinarith

/-- The frontier wage is strictly increasing in `A`, O&R p. 208. -/
theorem wage_strictMonoOn_A {r : ℝ} (hr : 0 < r) : StrictMonoOn (fun a => T.wage a r) (Ioi 0) := by
  intro a1 ha1 a2 ha2 h
  have ha1' : (0 : ℝ) < a1 := ha1
  have ha2' : (0 : ℝ) < a2 := ha2
  have e1 := T.wage_frontier ha1' hr
  have hk1 := (T.kstar_foc ha1' hr).1
  have hf := T.f_pos hk1
  have i := T.wage_isMax ha2' hr hk1.le
  simp only
  nlinarith

/-- Wage–rental ratio in intensive form, O&R (4)/(5), p. 206: `ω(k) = (f(k) − f′(k)k)/f′(k)`,
equal to `g/g′ − k`. -/
noncomputable def wageRental (k : ℝ) : ℝ := T.mpl k / T.fp k

/-- The wage–rental ratio is strictly increasing, O&R p. 206 (why MPK and MPL cross once in
Figure 4.2): `ω = MPL/MPK` is a positive increasing function over a positive decreasing one. -/
theorem wageRental_strictMonoOn : StrictMonoOn T.wageRental (Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have h1 := T.mpl_strictMonoOn ha hb hab
  have h2 : T.fp b < T.fp a := T.fp_strictAnti ha hb hab
  have hma := T.mpl_pos ha'
  have hfa := T.fp_pos a ha'
  have hfb := T.fp_pos b hb'
  unfold wageRental
  rw [div_lt_div_iff₀ hfa hfb]
  nlinarith

/-- The wage–rental ratio is continuous on `(0, ∞)`, O&R §4.2.1. -/
theorem wageRental_continuousOn : ContinuousOn T.wageRental (Ioi 0) := by
  intro k hk
  have hk' : (0 : ℝ) < k := hk
  have hf : ContinuousAt T.f k := (T.hasDeriv k hk').continuousAt
  have hfp : ContinuousAt T.fp k := T.fp_cont.continuousAt (Ioi_mem_nhds hk')
  exact ((hf.sub (hfp.mul continuousAt_id)).div hfp (T.fp_pos k hk').ne').continuousWithinAt

/-- The wage–rental ratio takes every positive value exactly once, O&R p. 206: for each
`c > 0` there is a unique `k > 0` with `ω(k) = c` (IVT; the range follows from the Inada-type
conditions, since `ω ≤ f/f′ → 0` at zero and `ω ≥ MPL(1)/f′ → ∞`). -/
theorem existsUnique_wageRental_eq {c : ℝ} (hc : 0 < c) : ∃! k, 0 < k ∧ T.wageRental k = c := by
  -- a point where ω < c
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.1
    (T.f_cont (0 : ℝ) (le_refl (0 : ℝ))) 1 one_pos
  set M := T.f 0 + 1 with hM
  have hMpos : 0 < M := by linarith [T.f_zero_nonneg]
  obtain ⟨k1, hk1, hk1f⟩ := T.inada_zero (M / c)
  set a := min k1 (δ / 2) with ha
  have hapos : 0 < a := lt_min hk1 (by linarith)
  have hfa : M / c ≤ T.fp a := by
    rcases eq_or_lt_of_le (min_le_left k1 (δ / 2)) with h | h
    · rw [← ha] at h; rw [h]; exact hk1f.le
    · exact le_trans hk1f.le (T.fp_strictAnti hapos hk1 h).le
  have hfaM : T.f a < M := by
    have hd : dist a 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hapos]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have := hδf (show a ∈ Ici (0 : ℝ) from hapos.le) hd
    rw [Real.dist_eq] at this
    have := (abs_lt.1 this).2
    linarith
  have hωa : T.wageRental a < c := by
    have hfpa := T.fp_pos a hapos
    unfold wageRental
    rw [div_lt_iff₀ hfpa]
    have : M ≤ c * T.fp a := by
      have := mul_le_mul_of_nonneg_left hfa hc.le
      rwa [mul_div_cancel₀ M hc.ne'] at this
    have : T.mpl a ≤ T.f a := by
      unfold mpl; nlinarith [T.fp_pos a hapos]
    linarith
  -- a point where ω > c
  have hm1 := T.mpl_pos one_pos
  obtain ⟨k2, hk2, hk2f⟩ := T.inada_infty (T.mpl 1 / (c + 1)) (div_pos hm1 (by linarith))
  set b := max k2 1 with hb
  have hbpos : 0 < b := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfb : T.fp b < T.mpl 1 / (c + 1) := by
    rcases eq_or_lt_of_le (le_max_left k2 1) with h | h
    · rw [← hb] at h; rw [← h]; exact hk2f
    · exact lt_trans (T.fp_strictAnti hk2 hbpos h) hk2f
  have hmb : T.mpl 1 ≤ T.mpl b := by
    rcases eq_or_lt_of_le (le_max_right k2 1) with h | h
    · rw [← hb] at h; rw [← h]
    · exact (T.mpl_strictMonoOn (Set.mem_Ioi.2 one_pos) hbpos h).le
  have hωb : c < T.wageRental b := by
    have hfpb := T.fp_pos b hbpos
    unfold wageRental
    rw [lt_div_iff₀ hfpb]
    have : (c + 1) * T.fp b < T.mpl 1 := by
      rw [lt_div_iff₀ (by linarith)] at hfb; linarith
    nlinarith
  have hab : a ≤ b := by
    by_contra h
    push Not at h
    have := T.wageRental_strictMonoOn hbpos hapos h
    linarith
  have hcont : ContinuousOn T.wageRental (Icc a b) :=
    T.wageRental_continuousOn.mono fun y hy => lt_of_lt_of_le hapos hy.1
  obtain ⟨k, hk, hkc⟩ := intermediate_value_Icc hab hcont ⟨hωa.le, hωb.le⟩
  have hkpos : 0 < k := lt_of_lt_of_le hapos hk.1
  refine ⟨k, ⟨hkpos, hkc⟩, ?_⟩
  rintro y ⟨hy, hyc⟩
  exact (T.wageRental_strictMonoOn.injOn (show y ∈ Ioi (0 : ℝ) from hy)
    (show k ∈ Ioi (0 : ℝ) from hkpos)) (hyc.trans hkc.symm)

/-- Inverse of the wage–rental ratio, O&R (4)/(5), p. 206: the unique `k > 0` with `ω(k) = c`
(an arbitrary junk value for `c ≤ 0`). -/
noncomputable def wrInv (c : ℝ) : ℝ :=
  Classical.epsilon fun k => 0 < k ∧ T.wageRental k = c

/-- Defining property of `ω⁻¹`, O&R p. 206. -/
theorem wrInv_spec {c : ℝ} (hc : 0 < c) : 0 < T.wrInv c ∧ T.wageRental (T.wrInv c) = c := by
  have h : ∃ k, 0 < k ∧ T.wageRental k = c := (T.existsUnique_wageRental_eq hc).exists
  exact Classical.epsilon_spec h

/-- `ω⁻¹` is continuous on `(0, ∞)`, O&R p. 206. -/
theorem wrInv_continuousAt {c : ℝ} (hc : 0 < c) : ContinuousAt T.wrInv c := by
  obtain ⟨k0pos, hk0⟩ := T.wrInv_spec hc
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · set a' := max a (T.wrInv c / 2) with ha'
    have ha'pos : 0 < a' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have ha'lt : a' < T.wrInv c := max_lt ha (by linarith)
    have hfa : T.wageRental a' < c := by
      rw [← hk0]; exact T.wageRental_strictMonoOn ha'pos k0pos ha'lt
    filter_upwards [Ioi_mem_nhds hc, lt_mem_nhds hfa] with y hy hyl
    obtain ⟨hky, hfy⟩ := T.wrInv_spec (show (0 : ℝ) < y from hy)
    have : T.wageRental a' < T.wageRental (T.wrInv y) := by rw [hfy]; exact hyl
    have := (T.wageRental_strictMonoOn.lt_iff_lt (show a' ∈ Ioi (0 : ℝ) from ha'pos)
      (show T.wrInv y ∈ Ioi (0 : ℝ) from hky)).1 this
    exact lt_of_le_of_lt (le_max_left _ _) this
  · have hbpos : 0 < b := lt_trans k0pos hb
    have hfb : c < T.wageRental b := by
      rw [← hk0]; exact T.wageRental_strictMonoOn k0pos hbpos hb
    filter_upwards [Ioi_mem_nhds hc, gt_mem_nhds hfb] with y hy hyl
    obtain ⟨hky, hfy⟩ := T.wrInv_spec (show (0 : ℝ) < y from hy)
    have : T.wageRental (T.wrInv y) < T.wageRental b := by rw [hfy]; exact hyl
    exact (T.wageRental_strictMonoOn.lt_iff_lt (show T.wrInv y ∈ Ioi (0 : ℝ) from hky)
      (show b ∈ Ioi (0 : ℝ) from hbpos)).1 this

/-- `ω⁻¹` is strictly increasing, O&R p. 208 (a higher wage–rental ratio raises `k_N`). -/
theorem wrInv_strictMonoOn : StrictMonoOn T.wrInv (Ioi 0) := by
  intro c1 hc1 c2 hc2 h
  obtain ⟨k1, e1⟩ := T.wrInv_spec (show (0 : ℝ) < c1 from hc1)
  obtain ⟨k2, e2⟩ := T.wrInv_spec (show (0 : ℝ) < c2 from hc2)
  exact (T.wageRental_strictMonoOn.lt_iff_lt (show T.wrInv c1 ∈ Ioi (0 : ℝ) from k1)
    (show T.wrInv c2 ∈ Ioi (0 : ℝ) from k2)).1 (by rw [e1, e2]; exact h)

end IntensiveTech

end ObstfeldRogoff.RealExchangeRate.CRSProduction
