import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Monotone.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Traded and nontraded goods: the consumer price index

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§4.1, pp. 199–202. With Cobb–Douglas preferences over a traded and a nontraded
good, the consumer price index is `P = P_T^γ P_N^{1−γ}` for `0 < γ < 1`. With the
traded good as numeraire, `P = p^{1−γ}` where `p = P_N/P_T` is the relative price
of nontradables.
-/

namespace ObstfeldRogoff.RealExchangeRate

/-- Cobb–Douglas weights on traded and nontraded consumption, `0 < γ < 1`. -/
structure CobbDouglasIndex where
  γ : ℝ
  γ_pos : 0 < γ
  γ_lt_one : γ < 1

namespace CobbDouglasIndex

/-- The consumer price index `P = P_T^γ P_N^{1−γ}` (O&R §4.1). -/
noncomputable def price (c : CobbDouglasIndex) (PT PN : ℝ) : ℝ := PT ^ c.γ * PN ^ (1 - c.γ)

/-- The price index is homogeneous of degree one in nominal prices. -/
theorem price_homogeneous (c : CobbDouglasIndex) {PT PN t : ℝ} (hT : 0 ≤ PT) (hN : 0 ≤ PN)
    (ht : 0 ≤ t) : c.price (t * PT) (t * PN) = t * c.price PT PN := by
  unfold price
  rw [Real.mul_rpow ht hT, Real.mul_rpow ht hN]
  have : t ^ c.γ * t ^ (1 - c.γ) = t := by
    rw [← Real.rpow_add_of_nonneg ht c.γ_pos.le (by linarith [c.γ_lt_one]), add_sub_cancel,
      Real.rpow_one]
  calc t ^ c.γ * PT ^ c.γ * (t ^ (1 - c.γ) * PN ^ (1 - c.γ))
      = (t ^ c.γ * t ^ (1 - c.γ)) * (PT ^ c.γ * PN ^ (1 - c.γ)) := by ring
    _ = t * (PT ^ c.γ * PN ^ (1 - c.γ)) := by rw [this]

/-- With the traded good as numeraire, the price index is `p^{1−γ}` (O&R §4.1). -/
theorem price_numeraire (c : CobbDouglasIndex) (p : ℝ) : c.price 1 p = p ^ (1 - c.γ) := by
  simp [price]

end CobbDouglasIndex

end ObstfeldRogoff.RealExchangeRate

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# International price levels and the real exchange rate

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.1,
pp. 199–202, and the Harrod–Balassa–Samuelson price-level ratio, pp. 211–212.

* The real exchange rate between countries 1 and 2 is the ratio of their price
  levels in a common currency, `P₁/(𝓔P₂*)`. Absolute PPP says it equals one,
  relative PPP that it is constant.
* Footnote 1: `P₁ = 𝓔P₂*` holds iff the two price levels are equal once country 2's
  is converted into country 1's currency.
* With Cobb–Douglas price indices and the traded good as numeraire, the
  price-level ratio is `P/P* = (p/p*)^{1−γ}`. In logs,
  `log(P/P*) = (1 − γ)(log p − log p*)`: countries with a higher relative price of
  nontradables have higher price levels.
-/

namespace ObstfeldRogoff.RealExchangeRate.PriceLevels

/-- The real exchange rate `P₁/(𝓔P₂*)`: country 1's price level relative to country 2's, both in
country 1's currency (O&R p. 200). -/
noncomputable def realExchangeRate (P1 E P2 : ℝ) : ℝ := P1 / (E * P2)

/-- **Absolute PPP** (O&R p. 200): the real exchange rate is one iff `P₁ = 𝓔P₂*`, i.e. iff the
two price levels are equal in a common currency (footnote 1). -/
theorem absolute_ppp_iff {P1 E P2 : ℝ} (hEP : E * P2 ≠ 0) :
    realExchangeRate P1 E P2 = 1 ↔ P1 = E * P2 := by
  unfold realExchangeRate
  exact div_eq_one_iff_eq hEP

/-- **Relative PPP** (O&R p. 201): if absolute PPP holds up to a constant factor `k` at every date,
the real exchange rate is constant. -/
theorem relative_ppp_const {P1 E P2 : ℕ → ℝ} {k : ℝ} (hEP : ∀ t, E t * P2 t ≠ 0)
    (h : ∀ t, P1 t = k * (E t * P2 t)) (t s : ℕ) :
    realExchangeRate (P1 t) (E t) (P2 t) = realExchangeRate (P1 s) (E s) (P2 s) := by
  unfold realExchangeRate
  rw [h t, h s, mul_div_cancel_right₀ _ (hEP t), mul_div_cancel_right₀ _ (hEP s)]

/-- **The law of one price for the traded good implies PPP for traded-goods prices**: if the traded
good sells for `P_T = 𝓔P_T*`, then its price is one in either country's traded-goods units. -/
theorem lop_ratio {PT E PTs : ℝ} (hEP : E * PTs ≠ 0) (hlop : PT = E * PTs) :
    realExchangeRate PT E PTs = 1 :=
  (absolute_ppp_iff hEP).2 hlop

/-- **The price-level ratio with nontradables**, O&R p. 211: with Cobb–Douglas indices, common
weights `γ` and the traded good priced at one in both countries, `P/P* = (p/p*)^{1−γ}`. -/
theorem price_level_ratio (c : CobbDouglasIndex) {p ps : ℝ} (hp : 0 ≤ p) (hps : 0 ≤ ps) :
    c.price 1 p / c.price 1 ps = (p / ps) ^ (1 - c.γ) := by
  rw [c.price_numeraire, c.price_numeraire, Real.div_rpow hp hps]

/-- **The price-level ratio in logs**, O&R p. 212: `log(P/P*) = (1 − γ)(log p − log p*)`. -/
theorem log_price_level_ratio (c : CobbDouglasIndex) {p ps : ℝ} (hp : 0 < p) (hps : 0 < ps) :
    Real.log (c.price 1 p / c.price 1 ps) = (1 - c.γ) * (Real.log p - Real.log ps) := by
  rw [price_level_ratio c hp.le hps.le, Real.log_rpow (div_pos hp hps), Real.log_div hp.ne' hps.ne']

/-- **Higher relative price of nontradables, higher price level** (O&R pp. 211–212): with common
weights and traded goods priced alike, `P > P*` iff `p > p*`. -/
theorem price_level_gt_iff (c : CobbDouglasIndex) {p ps : ℝ} (hp : 0 < p) (hps : 0 < ps) :
    c.price 1 ps < c.price 1 p ↔ ps < p := by
  rw [c.price_numeraire, c.price_numeraire]
  exact Real.rpow_lt_rpow_iff hps.le hp.le (by linarith [c.γ_lt_one])

end ObstfeldRogoff.RealExchangeRate.PriceLevels

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The price of nontraded goods and the Harrod–Balassa–Samuelson effect

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.2.1–4.2.3,
pp. 204–212, eqs. (2)–(9).

A small open economy produces tradables `Y_T = A_T F(K_T, L_T)` and nontradables
`Y_N = A_N G(K_N, L_N)` with constant returns, faces the world interest rate `r`, and has
labour mobile between sectors. Tradables are the numeraire and `p` is the relative price of
nontradables. The supply-side equilibrium is a solution `(k_T, w, k_N, p)` of (2)–(5).

Results:
* T1 (p. 206): for `r, A_T, A_N > 0` the equilibrium exists and is unique, so `p` depends only
  on `r`, the productivities and technology — never on demand;
* T2 (p. 208): a rise in `A_T` raises `p` and `k_N`; a rise in `A_N` leaves `k_N` and `pA_N`
  unchanged;
* Shephard's lemma for the nontraded unit cost `pA_N = c(r, w)` along any path (exact
  envelope theorem);
* T3 (pp. 208–209): the log-linearisations (8), (9) and the interest-rate formula, as EXACT
  derivatives of logs along arbitrary differentiable paths `(r(t), A_T(t), A_N(t))`, with the
  sector shares evaluated at the current equilibrium; `μ_KN − μ_KT = μ_LT − μ_LN`;
* T4 (p. 208): the Balassa–Samuelson sign claim is corrected — `μ_LN/μ_LT ≥ 1` and faster
  productivity growth in tradables raise `p` only if in addition `Â_T ≥ 0`; an explicit
  counterexample shows the book's version fails otherwise;
* T5 (p. 209): a rise in `r` lowers `p` iff `μ_LN > μ_LT` strictly (at `μ_LN = μ_LT`, `p̂ = 0`);
* T6 (pp. 211–212): with the Cobb–Douglas index `P = p^{1−γ}` (`CobbDouglasIndex`), the exact
  HBS relation `P̂ − P̂* = (1 − γ)(p̂ − p̂*)` with each country's own shares, and the book's
  formula under an explicit common-shares hypothesis (true for Cobb–Douglas technologies).
-/

namespace ObstfeldRogoff.RealExchangeRate.BalassaSamuelson

open Filter Topology Set CRSProduction

variable (F G : IntensiveTech)

/-- Supply-side equilibrium, O&R (2)–(5), p. 205: `k_T, k_N > 0`, `A_T f′(k_T) = r`,
`A_T(f − f′k_T) = w`, `pA_N g′(k_N) = r`, `pA_N(g − g′k_N) = w`. -/
def IsSupplyEqm (r AT AN kT w kN p : ℝ) : Prop :=
  0 < kT ∧ 0 < kN ∧ AT * F.fp kT = r ∧ AT * F.mpl kT = w ∧ p * AN * G.fp kN = r ∧
    p * AN * G.mpl kN = w

/-- Capital intensity of nontradables given factor prices, O&R (4)/(5), p. 206: the unique
`k_N > 0` with `g/g′ − k_N = w/r`. -/
noncomputable def kN (r w : ℝ) : ℝ := G.wrInv (w / r)

/-- Unit cost of nontradables at unit productivity, O&R (4), p. 206: `c(r, w) = r/g′(k_N)`,
which equals `pA_N` in equilibrium. -/
noncomputable def unitCost (r w : ℝ) : ℝ := r / G.fp (kN G r w)

/-- Equilibrium relative price of nontradables, O&R p. 206: `p(r, A_T, A_N) = c(r, w)/A_N`
with `w = w(r, A_T)` from the frontier (6). -/
noncomputable def eqmPrice (r AT AN : ℝ) : ℝ := unitCost G r (F.wage AT r) / AN

/-- Labour's share in tradables, O&R p. 208: `μ_LT = wL_T/Y_T = w/(A_T f(k_T))`. -/
noncomputable def muLT (r AT : ℝ) : ℝ := F.wage AT r / (AT * F.f (F.kstar AT r))

/-- Capital's share in tradables, O&R p. 209: `μ_KT = rK_T/Y_T = rk_T/(A_T f(k_T))`. -/
noncomputable def muKT (r AT : ℝ) : ℝ := r * F.kstar AT r / (AT * F.f (F.kstar AT r))

/-- Labour's share in nontradables, O&R p. 208: `μ_LN = wL_N/(pY_N) = w/(pA_N g(k_N))`
(independent of `A_N`). -/
noncomputable def muLN (r AT : ℝ) : ℝ :=
  F.wage AT r / (unitCost G r (F.wage AT r) * G.f (kN G r (F.wage AT r)))

/-- Capital's share in nontradables, O&R p. 209: `μ_KN = rK_N/(pY_N)`. -/
noncomputable def muKN (r AT : ℝ) : ℝ :=
  r * kN G r (F.wage AT r) / (unitCost G r (F.wage AT r) * G.f (kN G r (F.wage AT r)))

/-- Nontraded capital intensity solves the wage–rental condition, O&R (4)/(5), p. 206. -/
theorem kN_spec {r w : ℝ} (hr : 0 < r) (hw : 0 < w) :
    0 < kN G r w ∧ G.wageRental (kN G r w) = w / r :=
  G.wrInv_spec (div_pos hw hr)

/-- The nontraded unit cost satisfies the nontraded first-order conditions (4) and (5),
O&R p. 205, with `pA_N = c(r, w)`. -/
theorem unitCost_foc {r w : ℝ} (hr : 0 < r) (hw : 0 < w) :
    0 < unitCost G r w ∧ unitCost G r w * G.fp (kN G r w) = r ∧
      unitCost G r w * G.mpl (kN G r w) = w := by
  obtain ⟨hk, hω⟩ := kN_spec G hr hw
  have hfp := G.fp_pos _ hk
  refine ⟨div_pos hr hfp, div_mul_cancel₀ r hfp.ne', ?_⟩
  unfold IntensiveTech.wageRental at hω
  unfold unitCost
  rw [div_eq_div_iff hfp.ne' hr.ne'] at hω
  field_simp
  linarith

/-- Unit cost is the minimum cost of a unit of output, O&R (7) with fn. 19: for every
`k ≥ 0`, `c(r, w) g(k) ≤ rk + w`. -/
theorem unitCost_le {r w k : ℝ} (hr : 0 < r) (hw : 0 < w) (hk : 0 ≤ k) :
    unitCost G r w * G.f k ≤ r * k + w := by
  obtain ⟨h0, h1, h2⟩ := unitCost_foc G hr hw
  have := G.crs_profit_le h0 (kN_spec G hr hw).1 h1 h2 hk one_pos
  simpa using this

/-- Zero profit in nontradables, O&R (7), p. 208: `pA_N g(k_N) = rk_N + w`. -/
theorem unitCost_zero_profit {r w : ℝ} (hr : 0 < r) (hw : 0 < w) :
    unitCost G r w * G.f (kN G r w) = r * kN G r w + w := by
  obtain ⟨_, h1, h2⟩ := unitCost_foc G hr hw
  exact G.zero_profit h1 h2

/-- Shephard's lemma along a path, used for O&R (9) and p. 209: if `R(t)` and `W(t)` are
differentiable at `x` then `d c(R, W)/dt = (R′ k_N + W′)/g(k_N)` (exact envelope theorem;
`k_N/g` and `1/g` are the unit input requirements). -/
theorem unitCost_path_hasDerivAt {R W : ℝ → ℝ} {R' W' x : ℝ} (hR : HasDerivAt R R' x)
    (hW : HasDerivAt W W' x) (hR0 : 0 < R x) (hW0 : 0 < W x) :
    HasDerivAt (fun y => unitCost G (R y) (W y))
      ((R' * kN G (R x) (W x) + W') / G.f (kN G (R x) (W x))) x := by
  set k0 := kN G (R x) (W x) with hk0def
  have hk0 := (kN_spec G hR0 hW0).1
  have hg0 := G.f_pos hk0
  have hkc : ContinuousAt (fun y => kN G (R y) (W y)) x :=
    ContinuousAt.comp (f := fun y => W y / R y) (G.wrInv_continuousAt (div_pos hW0 hR0))
      (hW.continuousAt.div hR.continuousAt hR0.ne')
  have hgk : ContinuousAt (fun y => G.f (kN G (R y) (W y))) x :=
    ContinuousAt.comp (f := fun y => kN G (R y) (W y)) (G.hasDeriv _ hk0).continuousAt hkc
  have sR := hasDerivAt_iff_tendsto_slope.1 hR
  have sW := hasDerivAt_iff_tendsto_slope.1 hW
  have ha : Tendsto (fun y => (slope R x y * kN G (R y) (W y) + slope W x y) /
      G.f (kN G (R y) (W y))) (𝓝[≠] x) (𝓝 ((R' * k0 + W') / G.f k0)) :=
    ((sR.mul (hkc.tendsto.mono_left nhdsWithin_le_nhds)).add sW).div
      (hgk.tendsto.mono_left nhdsWithin_le_nhds) hg0.ne'
  have hb : Tendsto (fun y => (slope R x y * k0 + slope W x y) / G.f k0) (𝓝[≠] x)
      (𝓝 ((R' * k0 + W') / G.f k0)) :=
    ((sR.mul tendsto_const_nhds).add sW).div_const _
  refine hasDerivAt_of_between ha hb ?_
  have eR : ∀ᶠ y in 𝓝[≠] x, 0 < R y :=
    nhdsWithin_le_nhds (hR.continuousAt.eventually (Ioi_mem_nhds hR0))
  have eW : ∀ᶠ y in 𝓝[≠] x, 0 < W y :=
    nhdsWithin_le_nhds (hW.continuousAt.eventually (Ioi_mem_nhds hW0))
  filter_upwards [eR, eW, self_mem_nhdsWithin] with y hRy hWy hne
  have hyx : y - x ≠ 0 := sub_ne_zero.2 hne
  have dR : (y - x) * slope R x y = R y - R x := by
    rw [slope_def_field]; field_simp
  have dW : (y - x) * slope W x y = W y - W x := by
    rw [slope_def_field]; field_simp
  have hky := (kN_spec G hRy hWy).1
  have hgy := G.f_pos hky
  have z0 := unitCost_zero_profit G hR0 hW0
  have zy := unitCost_zero_profit G hRy hWy
  have i0 := unitCost_le G hR0 hW0 hky.le
  have iy := unitCost_le G hRy hWy hk0.le
  rw [← hk0def] at z0
  constructor
  · have e : (y - x) * ((slope R x y * kN G (R y) (W y) + slope W x y) /
        G.f (kN G (R y) (W y)))
        = ((R y - R x) * kN G (R y) (W y) + (W y - W x)) / G.f (kN G (R y) (W y)) := by
      rw [← dR, ← dW]; ring
    rw [e, div_le_iff₀ hgy]
    have : (unitCost G (R y) (W y) - unitCost G (R x) (W x)) * G.f (kN G (R y) (W y))
        = unitCost G (R y) (W y) * G.f (kN G (R y) (W y))
          - unitCost G (R x) (W x) * G.f (kN G (R y) (W y)) := by ring
    rw [this]; linarith
  · have e : (y - x) * ((slope R x y * k0 + slope W x y) / G.f k0)
        = ((R y - R x) * k0 + (W y - W x)) / G.f k0 := by
      rw [← dR, ← dW]; ring
    rw [e, le_div_iff₀ hg0]
    have : (unitCost G (R y) (W y) - unitCost G (R x) (W x)) * G.f k0
        = unitCost G (R y) (W y) * G.f k0 - unitCost G (R x) (W x) * G.f k0 := by ring
    rw [this]; linarith

/-- T1 existence, O&R p. 206: `(k_T(r, A_T), w(r, A_T), k_N, p(r, A_T, A_N))` solves the
supply-side system (2)–(5). -/
theorem supplyEqm_exists {r AT AN : ℝ} (hr : 0 < r) (hAT : 0 < AT) (hAN : 0 < AN) :
    IsSupplyEqm F G r AT AN (F.kstar AT r) (F.wage AT r) (kN G r (F.wage AT r))
      (eqmPrice F G r AT AN) := by
  obtain ⟨hkT, hfocT⟩ := F.kstar_foc hAT hr
  have hw := F.wage_pos hAT hr
  obtain ⟨hc, h1, h2⟩ := unitCost_foc G hr hw
  have hpA : eqmPrice F G r AT AN * AN = unitCost G r (F.wage AT r) := by
    unfold eqmPrice; field_simp
  exact ⟨hkT, (kN_spec G hr hw).1, hfocT, rfl, by rw [hpA]; exact h1, by rw [hpA]; exact h2⟩

/-- T1 uniqueness, O&R p. 206: every solution of (2)–(5) is the one above. In particular the
relative price `p` is pinned down by `r`, `A_T`, `A_N` and technology alone: demand plays no
role. -/
theorem supplyEqm_unique {r AT AN kT w k p : ℝ} (hr : 0 < r) (hAT : 0 < AT)
    (h : IsSupplyEqm F G r AT AN kT w k p) :
    kT = F.kstar AT r ∧ w = F.wage AT r ∧ k = kN G r w ∧ p = eqmPrice F G r AT AN := by
  obtain ⟨hkT, hk, h2, h3, h4, h5⟩ := h
  have ekT : kT = F.kstar AT r := F.kstar_unique hAT hr hkT h2
  have ew : w = F.wage AT r := by rw [← h3, ekT]; rfl
  have hw : 0 < w := ew ▸ F.wage_pos hAT hr
  have hfp := G.fp_pos k hk
  have hpA : p * AN ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h4; linarith
  have hω : G.wageRental k = w / r := by
    unfold IntensiveTech.wageRental
    rw [← h4, ← h5, mul_div_mul_left _ _ hpA]
  have ek : k = kN G r w := by
    obtain ⟨h1', h2'⟩ := kN_spec G hr hw
    exact (G.existsUnique_wageRental_eq (div_pos hw hr)).unique ⟨hk, hω⟩ ⟨h1', h2'⟩
  refine ⟨ekT, ew, ek, ?_⟩
  have hAN : AN ≠ 0 := by intro h0; apply hpA; rw [h0, mul_zero]
  unfold eqmPrice unitCost
  rw [← ew, ← ek]
  field_simp
  linarith

/-- T1, O&R p. 206: for `r, A_T, A_N > 0` the supply-side system (2)–(5) has exactly one
solution `(k_T, w, k_N, p)`. -/
theorem supplyEqm_existsUnique {r AT AN : ℝ} (hr : 0 < r) (hAT : 0 < AT) (hAN : 0 < AN) :
    ∃! x : ℝ × ℝ × ℝ × ℝ, IsSupplyEqm F G r AT AN x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  refine ⟨(F.kstar AT r, F.wage AT r, kN G r (F.wage AT r), eqmPrice F G r AT AN),
    supplyEqm_exists F G hr hAT hAN, ?_⟩
  rintro ⟨a, b, c, d⟩ hx
  obtain ⟨e1, e2, e3, e4⟩ := supplyEqm_unique F G hr hAT hx
  simp only at e1 e2 e3 e4
  subst e1 e2 e3 e4
  rfl

/-- The equilibrium price of nontradables is positive, O&R p. 206. -/
theorem eqmPrice_pos {r AT AN : ℝ} (hr : 0 < r) (hAT : 0 < AT) (hAN : 0 < AN) :
    0 < eqmPrice F G r AT AN :=
  div_pos (unitCost_foc G hr (F.wage_pos hAT hr)).1 hAN

/-- A higher wage raises the nontraded capital intensity, O&R p. 206 (MPL schedule). -/
theorem kN_strictMonoOn_w {r : ℝ} (hr : 0 < r) : StrictMonoOn (kN G r) (Ioi 0) := by
  intro w1 hw1 w2 hw2 h
  exact G.wrInv_strictMonoOn (div_pos (show (0 : ℝ) < w1 from hw1) hr)
    (div_pos (show (0 : ℝ) < w2 from hw2) hr) (div_lt_div_of_pos_right h hr)

/-- A higher wage raises the nontraded unit cost, O&R p. 208. -/
theorem unitCost_strictMonoOn_w {r : ℝ} (hr : 0 < r) : StrictMonoOn (unitCost G r) (Ioi 0) := by
  intro w1 hw1 w2 hw2 h
  have hk := kN_strictMonoOn_w G hr hw1 hw2 h
  have hk1 := (kN_spec G hr (show (0 : ℝ) < w1 from hw1)).1
  have hk2 := (kN_spec G hr (show (0 : ℝ) < w2 from hw2)).1
  have hfp := G.fp_strictAnti hk1 hk2 hk
  exact div_lt_div_of_pos_left hr (G.fp_pos _ hk2) hfp

/-- T2, O&R p. 208: a rise in tradables productivity `A_T` raises the equilibrium relative
price of nontradables. -/
theorem eqmPrice_strictMonoOn_AT {r AN : ℝ} (hr : 0 < r) (hAN : 0 < AN) :
    StrictMonoOn (fun a => eqmPrice F G r a AN) (Ioi 0) := by
  intro a1 ha1 a2 ha2 h
  have hw := F.wage_strictMonoOn_A hr ha1 ha2 h
  exact div_lt_div_of_pos_right (unitCost_strictMonoOn_w G hr
    (F.wage_pos (show (0 : ℝ) < a1 from ha1) hr) (F.wage_pos (show (0 : ℝ) < a2 from ha2) hr)
    hw) hAN

/-- T2, O&R p. 208: a rise in `A_T` raises the capital intensity of nontradables. -/
theorem eqm_kN_strictMonoOn_AT {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (fun a => kN G r (F.wage a r)) (Ioi 0) := by
  intro a1 ha1 a2 ha2 h
  exact kN_strictMonoOn_w G hr (F.wage_pos (show (0 : ℝ) < a1 from ha1) hr)
    (F.wage_pos (show (0 : ℝ) < a2 from ha2) hr) (F.wage_strictMonoOn_A hr ha1 ha2 h)

/-- T2, O&R p. 208: a change in nontradables productivity `A_N` leaves `k_N` unchanged and
moves `p` in exact inverse proportion (`pA_N` constant). -/
theorem eqm_AN_neutral {r AT AN AN' kT w k p kT' w' k' p' : ℝ} (hr : 0 < r) (hAT : 0 < AT)
    (h : IsSupplyEqm F G r AT AN kT w k p) (h' : IsSupplyEqm F G r AT AN' kT' w' k' p') :
    k = k' ∧ p * AN = p' * AN' := by
  obtain ⟨_, e2, e3, _⟩ := supplyEqm_unique F G hr hAT h
  obtain ⟨_, e2', e3', _⟩ := supplyEqm_unique F G hr hAT h'
  have ek : k = k' := by rw [e3, e3', e2, e2']
  refine ⟨ek, ?_⟩
  obtain ⟨_, hk, _, _, h4, _⟩ := h
  obtain ⟨_, _, _, _, h4', _⟩ := h'
  have hfp := G.fp_pos k hk
  rw [← ek] at h4'
  have : p * AN * G.fp k = p' * AN' * G.fp k := h4.trans h4'.symm
  exact mul_right_cancel₀ hfp.ne' this

/-- The factor shares in tradables sum to one, O&R p. 209: `μ_KT = 1 − μ_LT`. -/
theorem muKT_add_muLT {r AT : ℝ} (hr : 0 < r) (hAT : 0 < AT) :
    muKT F r AT + muLT F r AT = 1 := by
  obtain ⟨hk, h1⟩ := F.kstar_foc hAT hr
  have z := F.zero_profit h1 rfl
  have hY : 0 < AT * F.f (F.kstar AT r) := mul_pos hAT (F.f_pos hk)
  unfold muKT muLT
  rw [← add_div, div_eq_one_iff_eq hY.ne']
  unfold IntensiveTech.wage; linarith

/-- The factor shares in nontradables sum to one, O&R p. 209: `μ_KN = 1 − μ_LN`. -/
theorem muKN_add_muLN {r AT : ℝ} (hr : 0 < r) (hAT : 0 < AT) :
    muKN F G r AT + muLN F G r AT = 1 := by
  have hw := F.wage_pos hAT hr
  have z := unitCost_zero_profit G hr hw
  have hY : 0 < unitCost G r (F.wage AT r) * G.f (kN G r (F.wage AT r)) :=
    mul_pos (unitCost_foc G hr hw).1 (G.f_pos (kN_spec G hr hw).1)
  unfold muKN muLN
  rw [← add_div, div_eq_one_iff_eq hY.ne']
  linarith

/-- O&R p. 209: `μ_KN − μ_KT = μ_LT − μ_LN`. -/
theorem muKN_sub_muKT {r AT : ℝ} (hr : 0 < r) (hAT : 0 < AT) :
    muKN F G r AT - muKT F r AT = muLT F r AT - muLN F G r AT := by
  have h1 := muKT_add_muLT F hr hAT
  have h2 := muKN_add_muLN F G hr hAT
  linarith

/-- Labour's share in tradables is positive, O&R p. 208. -/
theorem muLT_pos {r AT : ℝ} (hr : 0 < r) (hAT : 0 < AT) : 0 < muLT F r AT :=
  div_pos (F.wage_pos hAT hr) (mul_pos hAT (F.f_pos (F.kstar_foc hAT hr).1))

/-- Labour's share in nontradables is positive, O&R p. 208. -/
theorem muLN_pos {r AT : ℝ} (hr : 0 < r) (hAT : 0 < AT) : 0 < muLN F G r AT := by
  have hw := F.wage_pos hAT hr
  exact div_pos hw (mul_pos (unitCost_foc G hr hw).1 (G.f_pos (kN_spec G hr hw).1))

/-- Ratio of labour shares, O&R p. 208: `μ_LN/μ_LT = Y_T/L_T ÷ pY_N/L_N`, i.e.
`A_T f(k_T)/(pA_N g(k_N))`. -/
theorem muLN_div_muLT {r AT : ℝ} (hr : 0 < r) (hAT : 0 < AT) :
    muLN F G r AT / muLT F r AT = AT * F.f (F.kstar AT r) /
      (unitCost G r (F.wage AT r) * G.f (kN G r (F.wage AT r))) := by
  have hw := F.wage_pos hAT hr
  have hf := F.f_pos (F.kstar_foc hAT hr).1
  have hc := (unitCost_foc G hr hw).1
  have hg := G.f_pos (kN_spec G hr hw).1
  unfold muLN muLT
  field_simp

/-- T3, O&R (8), p. 208, and its interest-rate analogue: along any differentiable path of
`(A_T(t), r(t))` the wage satisfies, exactly,
`ŵ = Â_T/μ_LT − (μ_KT/μ_LT) r̂` (hats are logarithmic derivatives). With `r` constant this is
(8), `Â_T = μ_LT ŵ`. -/
theorem logWage_path_hasDerivAt {AT R : ℝ → ℝ} {AT' R' t : ℝ} (hA : HasDerivAt AT AT' t)
    (hR : HasDerivAt R R' t) (hA0 : 0 < AT t) (hR0 : 0 < R t) :
    HasDerivAt (fun s => Real.log (F.wage (AT s) (R s)))
      (1 / muLT F (R t) (AT t) * (AT' / AT t)
        - muKT F (R t) (AT t) / muLT F (R t) (AT t) * (R' / R t)) t := by
  have hw := F.wage_pos hA0 hR0
  have hk := (F.kstar_foc hA0 hR0).1
  have hf := F.f_pos hk
  refine ((F.wage_path_hasDerivAt hA hR hA0 hR0).log hw.ne').congr_deriv ?_
  unfold muLT muKT
  field_simp

/-- T3, O&R (9) and p. 209 combined: along any differentiable path of `(r(t), A_T(t), A_N(t))`
the equilibrium relative price of nontradables satisfies, exactly,
`p̂ = (μ_LN/μ_LT) Â_T − Â_N + ((μ_LT − μ_LN)/μ_LT) r̂`. -/
theorem logPrice_path_hasDerivAt {R AT AN : ℝ → ℝ} {R' AT' AN' t : ℝ}
    (hR : HasDerivAt R R' t) (hA : HasDerivAt AT AT' t) (hN : HasDerivAt AN AN' t)
    (hR0 : 0 < R t) (hA0 : 0 < AT t) (hN0 : 0 < AN t) :
    HasDerivAt (fun s => Real.log (eqmPrice F G (R s) (AT s) (AN s)))
      (muLN F G (R t) (AT t) / muLT F (R t) (AT t) * (AT' / AT t) - AN' / AN t
        + (muLT F (R t) (AT t) - muLN F G (R t) (AT t)) / muLT F (R t) (AT t) * (R' / R t))
      t := by
  have hw := F.wage_pos hA0 hR0
  have hk := (F.kstar_foc hA0 hR0).1
  have hf := F.f_pos hk
  have hW := F.wage_path_hasDerivAt hA hR hA0 hR0
  have hC := unitCost_path_hasDerivAt G hR hW hR0 hw
  have hP := hC.div hN hN0.ne'
  have hp := eqmPrice_pos F G hR0 hA0 hN0
  refine (hP.log hp.ne').congr_deriv ?_
  obtain ⟨hc, _, _⟩ := unitCost_foc G hR0 hw
  have hkn := (kN_spec G hR0 hw).1
  have hg := G.f_pos hkn
  have hY := mul_pos hc hg
  have z1 := F.zero_profit (w := F.wage (AT t) (R t)) (F.kstar_foc hA0 hR0).2 rfl
  have z2 := unitCost_zero_profit G hR0 hw
  have hr1 := muLN_div_muLT F G hR0 hA0
  have hr2 : (muLT F (R t) (AT t) - muLN F G (R t) (AT t)) / muLT F (R t) (AT t)
      = R t * (kN G (R t) (F.wage (AT t) (R t)) - F.kstar (AT t) (R t))
        / (unitCost G (R t) (F.wage (AT t) (R t)) * G.f (kN G (R t) (F.wage (AT t) (R t)))) := by
    rw [sub_div, div_self (muLT_pos F hR0 hA0).ne', hr1, eq_div_iff hY.ne', sub_mul,
      div_mul_cancel₀ _ hY.ne']
    linarith
  rw [hr1, hr2]
  simp only [Pi.div_apply]
  field_simp
  ring

/-- T3 with the interest rate fixed, O&R (9), p. 208: `p̂ = (μ_LN/μ_LT) Â_T − Â_N`. -/
theorem logPrice_hat_eq9 {r : ℝ} {AT AN : ℝ → ℝ} {AT' AN' t : ℝ} (hA : HasDerivAt AT AT' t)
    (hN : HasDerivAt AN AN' t) (hr : 0 < r) (hA0 : 0 < AT t) (hN0 : 0 < AN t) :
    HasDerivAt (fun s => Real.log (eqmPrice F G r (AT s) (AN s)))
      (muLN F G r (AT t) / muLT F r (AT t) * (AT' / AT t) - AN' / AN t) t := by
  have := logPrice_path_hasDerivAt F G (hasDerivAt_const t r) hA hN hr hA0 hN0
  simpa using this

/-- T3 with productivities fixed, O&R p. 209: `p̂ = ((μ_LT − μ_LN)/μ_LT) r̂`. -/
theorem logPrice_hat_r {AT AN : ℝ} {R : ℝ → ℝ} {R' t : ℝ} (hR : HasDerivAt R R' t)
    (hR0 : 0 < R t) (hA0 : 0 < AT) (hN0 : 0 < AN) :
    HasDerivAt (fun s => Real.log (eqmPrice F G (R s) AT AN))
      ((muLT F (R t) AT - muLN F G (R t) AT) / muLT F (R t) AT * (R' / R t)) t := by
  have := logPrice_path_hasDerivAt F G hR (hasDerivAt_const t AT) (hasDerivAt_const t AN)
    hR0 hA0 hN0
  simpa using this

/-- T4, corrected Balassa–Samuelson inequality, O&R p. 208: if `μ_LN/μ_LT ≥ 1` AND `Â_T ≥ 0`,
then `p̂ = (μ_LN/μ_LT)Â_T − Â_N ≥ Â_T − Â_N`. -/
theorem bs_price_growth_ge {μLT μLN AT AN : ℝ} (hT : 0 < μLT) (hle : μLT ≤ μLN)
    (hA : 0 ≤ AT) : AT - AN ≤ μLN / μLT * AT - AN := by
  have : 1 ≤ μLN / μLT := (one_le_div hT).2 hle
  nlinarith

/-- T4, corrected Balassa–Samuelson theorem, O&R p. 208: with `μ_LN ≥ μ_LT`, `Â_T ≥ 0` and
faster productivity growth in tradables (`Â_T > Â_N`), the price of nontradables rises. -/
theorem bs_price_rises {μLT μLN AT AN : ℝ} (hT : 0 < μLT) (hle : μLT ≤ μLN) (hA : 0 ≤ AT)
    (hfaster : AN < AT) : 0 < μLN / μLT * AT - AN := by
  have := bs_price_growth_ge hT hle hA (AN := AN)
  linarith

/-- T4 counterexample, O&R p. 208: the book's claim (only `μ_LN/μ_LT ≥ 1` and `Â_T > Â_N`)
is false: with `μ_LT = 1/4`, `μ_LN = 1/2`, `Â_T = −1`, `Â_N = −3/2` the price falls,
`p̂ = −1/2`. -/
theorem bs_sign_counterexample :
    ∃ μLT μLN AT AN : ℝ, 0 < μLT ∧ μLT ≤ μLN ∧ μLN < 1 ∧ AN < AT ∧ μLN / μLT * AT - AN < 0 :=
  ⟨1 / 4, 1 / 2, -1, -3 / 2, by norm_num⟩

/-- T4 for the model's exact derivative, O&R (9), p. 208: at an equilibrium with
`μ_LN ≥ μ_LT`, non-negative tradables productivity growth and `Â_T > Â_N` (constant `r`),
the relative price of nontradables is strictly rising. -/
theorem eqm_logPrice_deriv_pos {r : ℝ} {AT AN : ℝ → ℝ} {AT' AN' t D : ℝ}
    (hA : HasDerivAt AT AT' t) (hN : HasDerivAt AN AN' t) (hr : 0 < r) (hA0 : 0 < AT t)
    (hN0 : 0 < AN t) (hle : muLT F r (AT t) ≤ muLN F G r (AT t)) (hA' : 0 ≤ AT')
    (hfaster : AN' / AN t < AT' / AT t)
    (hD : HasDerivAt (fun s => Real.log (eqmPrice F G r (AT s) (AN s))) D t) : 0 < D := by
  rw [hD.unique (logPrice_hat_eq9 F G hA hN hr hA0 hN0)]
  exact bs_price_rises (muLT_pos F hr hA0) hle (div_nonneg hA' hA0.le) hfaster

/-- T5, O&R p. 209: a rise in `r` lowers `p` when nontradables are STRICTLY more labour
intensive, `μ_LN > μ_LT`. -/
theorem price_falls_with_r {μLT μLN rhat : ℝ} (hT : 0 < μLT) (hlt : μLT < μLN)
    (hr : 0 < rhat) : (μLT - μLN) / μLT * rhat < 0 :=
  mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith) hT) hr

/-- T5 boundary case, O&R p. 209: at `μ_LN = μ_LT` (allowed by the book's `≥`) a rise in `r`
leaves `p` unchanged, so "lowers" needs the strict inequality. -/
theorem price_r_boundary {μ rhat : ℝ} : (μ - μ) / μ * rhat = 0 := by simp

/-- T5 as an equivalence, O&R p. 209: the interest-rate elasticity of `p` is negative iff
`μ_LN > μ_LT`. -/
theorem r_elasticity_neg_iff {μLT μLN : ℝ} (hT : 0 < μLT) :
    (μLT - μLN) / μLT < 0 ↔ μLT < μLN := by
  rw [div_neg_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, _⟩)
    · linarith
    · linarith
  · intro h; exact Or.inr ⟨by linarith, hT⟩

/-- Real exchange rate with a Cobb–Douglas index, O&R p. 211: with `P = p^{1−γ}`,
`log(P/P*) = (1 − γ)(log p − log p*)` (uses `CobbDouglasIndex.price_numeraire`). -/
theorem hbs_log_ratio (c : CobbDouglasIndex) {p ps : ℝ} (hp : 0 < p) (hps : 0 < ps) :
    Real.log (c.price 1 p / c.price 1 ps) = (1 - c.γ) * (Real.log p - Real.log ps) := by
  rw [c.price_numeraire, c.price_numeraire, Real.log_div (Real.rpow_pos_of_pos hp _).ne'
    (Real.rpow_pos_of_pos hps _).ne', Real.log_rpow hp, Real.log_rpow hps]
  ring

/-- T6, exact Harrod–Balassa–Samuelson relation, O&R p. 212: two countries with the same
technologies `F`, `G`, the same world interest rate and Cobb–Douglas price indices; along
differentiable productivity paths,
`P̂ − P̂* = (1 − γ)[(μ_LN/μ_LT)Â_T − Â_N − ((μ*_LN/μ*_LT)Â*_T − Â*_N)]`,
each country's shares evaluated at its own equilibrium. -/
theorem hbs_path_hasDerivAt (c : CobbDouglasIndex) {r : ℝ} {AT AN ATs ANs : ℝ → ℝ}
    {AT' AN' ATs' ANs' t : ℝ} (hA : HasDerivAt AT AT' t) (hN : HasDerivAt AN AN' t)
    (hAs : HasDerivAt ATs ATs' t) (hNs : HasDerivAt ANs ANs' t) (hr : 0 < r)
    (hA0 : 0 < AT t) (hN0 : 0 < AN t) (hAs0 : 0 < ATs t) (hNs0 : 0 < ANs t) :
    HasDerivAt (fun s => Real.log (c.price 1 (eqmPrice F G r (AT s) (AN s)) /
        c.price 1 (eqmPrice F G r (ATs s) (ANs s))))
      ((1 - c.γ) * ((muLN F G r (AT t) / muLT F r (AT t) * (AT' / AT t) - AN' / AN t)
        - (muLN F G r (ATs t) / muLT F r (ATs t) * (ATs' / ATs t) - ANs' / ANs t))) t := by
  have h := ((logPrice_hat_eq9 F G hA hN hr hA0 hN0).sub
    (logPrice_hat_eq9 F G hAs hNs hr hAs0 hNs0)).const_mul (1 - c.γ)
  refine h.congr_of_eventuallyEq ?_
  have e1 := hA.continuousAt.eventually (Ioi_mem_nhds hA0)
  have e2 := hN.continuousAt.eventually (Ioi_mem_nhds hN0)
  have e3 := hAs.continuousAt.eventually (Ioi_mem_nhds hAs0)
  have e4 := hNs.continuousAt.eventually (Ioi_mem_nhds hNs0)
  filter_upwards [e1, e2, e3, e4] with s h1 h2 h3 h4
  exact hbs_log_ratio c (eqmPrice_pos F G hr h1 h2) (eqmPrice_pos F G hr h3 h4)

/-- T6, the book's HBS formula, O&R p. 212, under the (implicit) hypothesis that both
countries have the same ratio `μ_LN/μ_LT = ρ`:
`P̂ − P̂* = (1 − γ)[ρ(Â_T − Â*_T) − (Â_N − Â*_N)]`. -/
theorem hbs_common_shares (c : CobbDouglasIndex) {r ρ : ℝ} {AT AN ATs ANs : ℝ → ℝ}
    {AT' AN' ATs' ANs' t : ℝ} (hA : HasDerivAt AT AT' t) (hN : HasDerivAt AN AN' t)
    (hAs : HasDerivAt ATs ATs' t) (hNs : HasDerivAt ANs ANs' t) (hr : 0 < r)
    (hA0 : 0 < AT t) (hN0 : 0 < AN t) (hAs0 : 0 < ATs t) (hNs0 : 0 < ANs t)
    (hρ : muLN F G r (AT t) / muLT F r (AT t) = ρ)
    (hρs : muLN F G r (ATs t) / muLT F r (ATs t) = ρ) :
    HasDerivAt (fun s => Real.log (c.price 1 (eqmPrice F G r (AT s) (AN s)) /
        c.price 1 (eqmPrice F G r (ATs s) (ANs s))))
      ((1 - c.γ) * (ρ * (AT' / AT t - ATs' / ATs t) - (AN' / AN t - ANs' / ANs t))) t := by
  refine (hbs_path_hasDerivAt F G c hA hN hAs hNs hr hA0 hN0 hAs0 hNs0).congr_deriv ?_
  rw [hρ, hρs]; ring

/-- T6 sign, O&R p. 212, corrected as in T4: with common ratio `ρ ≥ 1`, a non-negative
tradables growth advantage `Â_T − Â*_T ≥ 0` exceeding the nontradables advantage, Home's price
level rises relative to Foreign's (`P̂ − P̂* > 0`). The counterexample of
`bs_sign_counterexample` (with differences) shows `Â_T − Â*_T ≥ 0` cannot be dropped. -/
theorem hbs_sign (c : CobbDouglasIndex) {ρ dAT dAN : ℝ} (hρ : 1 ≤ ρ) (hdA : 0 ≤ dAT)
    (hfaster : dAN < dAT) : 0 < (1 - c.γ) * (ρ * dAT - dAN) := by
  have h1 : 0 < 1 - c.γ := by linarith [c.γ_lt_one]
  have h2 : 0 < ρ * dAT - dAN := by nlinarith
  exact mul_pos h1 h2

/-- Why common shares are natural, O&R p. 212: with a Cobb–Douglas intensive technology
`f(k) = k^α`, `f′(k) = αk^{α−1}`, labour's share `(f − f′k)/f` equals `1 − α` at every `k > 0`,
hence at every equilibrium, whatever the productivity levels. -/
theorem cobbDouglas_labourShare {α k : ℝ} (hk : 0 < k) :
    (k ^ α - α * k ^ (α - 1) * k) / k ^ α = 1 - α := by
  have hkα : 0 < k ^ α := Real.rpow_pos_of_pos hk α
  rw [Real.rpow_sub_one hk.ne']
  field_simp

end ObstfeldRogoff.RealExchangeRate.BalassaSamuelson

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Extensions of the Balassa–Samuelson model: more factors, immobile capital, exercises

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.2.4,
pp. 214–216, and Chapter 4 Exercises 1, 2 and 6, pp. 264–266.

* T7 (§4.2.4): with a third factor (skilled labour) and two tradables sharing the capital
  share `μ_KT`, the tradables zero-profit conditions (a linear system in `ŵ_L, ŵ_S`) have the
  unique solution `ŵ_L = ŵ_S = Â_T/(1 − μ_KT)` when the two tradables differ in skill
  intensity (nonsingular system), so `p̂ = [(μ_LN + μ_SN)/(1 − μ_KT)]Â_T − Â_N`. With
  internationally immobile capital and two tradables, `r̂ = ŵ = Â_T` provided `μ_K1 ≠ μ_K2`
  (and the solution is not unique when `μ_K1 = μ_K2`), so `p̂ = Â_T − Â_N`. These are stated
  as the linear systems the book derives from total differentials.
* Exercise 1: with labour-augmenting progress `F(K_T, E_T L_T)` the wage is exactly
  `w = E_T w₀(r)`, so `ŵ = Ê_T` replaces `Â_T/μ_LT`, `p̂ = μ_LN Ê_T − Â_N`, and the
  labour-reallocation bracket of (18) is unchanged.
* Exercise 2: a rise in `r` lowers `k_T`, `w` and `k_N`; `p` falls iff `μ_LN > μ_LT`.
* Exercise 6: optimal schooling `T* = α/(r + π)`, the relative wage
  `h/w = A⁻¹ e^α ((r + π)/α)^α`, `∂ log w/∂α = log(α/(r + π))` (so `w` rises with `α` iff
  `α > r + π`), `w` increasing in `A`, decreasing in `r` and `π`, and `p` increasing in `w`.
-/

namespace ObstfeldRogoff.RealExchangeRate.BSExtensions

open Filter Topology Set CRSProduction BalassaSamuelson

/-- T7 three factors, O&R §4.2.4, p. 215: when both tradables have capital share `μ_KT`,
`(ŵ_L, ŵ_S) = (Â_T/(1 − μ_KT), Â_T/(1 − μ_KT))` solves the tradables zero-profit system
`Â_T = μ_Li ŵ_L + μ_Si ŵ_S` (`i = 1, 2`, with `p̂_T = r̂ = 0`). -/
theorem threeFactor_solves {μL1 μS1 μL2 μS2 μKT AT : ℝ} (h1 : μL1 + μS1 = 1 - μKT)
    (h2 : μL2 + μS2 = 1 - μKT) (hK : μKT < 1) :
    AT = μL1 * (AT / (1 - μKT)) + μS1 * (AT / (1 - μKT)) ∧
      AT = μL2 * (AT / (1 - μKT)) + μS2 * (AT / (1 - μKT)) := by
  have hne : 1 - μKT ≠ 0 := by linarith
  constructor
  · rw [← add_mul, h1]; field_simp
  · rw [← add_mul, h2]; field_simp

/-- T7 three factors, uniqueness, O&R §4.2.4, p. 215: if the system is nonsingular
(`μ_L1 μ_S2 − μ_S1 μ_L2 ≠ 0`, i.e. the tradables differ in skill intensity), every solution
has `ŵ_L = ŵ_S = Â_T/(1 − μ_KT)`. -/
theorem threeFactor_unique {μL1 μS1 μL2 μS2 μKT AT wL wS : ℝ} (h1 : μL1 + μS1 = 1 - μKT)
    (h2 : μL2 + μS2 = 1 - μKT) (hK : μKT < 1) (hdet : μL1 * μS2 - μS1 * μL2 ≠ 0)
    (e1 : AT = μL1 * wL + μS1 * wS) (e2 : AT = μL2 * wL + μS2 * wS) :
    wL = AT / (1 - μKT) ∧ wS = AT / (1 - μKT) := by
  obtain ⟨c1, c2⟩ := threeFactor_solves (AT := AT) h1 h2 hK
  set c := AT / (1 - μKT)
  have u : (wL - c) * (μL1 * μS2 - μS1 * μL2) = 0 := by
    linear_combination μS2 * c1 - μS1 * c2 - μS2 * e1 + μS1 * e2
  have v : (wS - c) * (μL1 * μS2 - μS1 * μL2) = 0 := by
    linear_combination μL2 * e1 - μL2 * c1 - μL1 * e2 + μL1 * c2
  exact ⟨sub_eq_zero.1 ((mul_eq_zero.1 u).resolve_right hdet),
    sub_eq_zero.1 ((mul_eq_zero.1 v).resolve_right hdet)⟩

/-- T7 three factors, the price of nontradables, O&R §4.2.4, p. 215: substituting into the
nontradables zero-profit condition `p̂ + Â_N = μ_LN ŵ_L + μ_SN ŵ_S` gives
`p̂ = [(μ_LN + μ_SN)/(1 − μ_KT)] Â_T − Â_N`. -/
theorem threeFactor_price {μL1 μS1 μL2 μS2 μKT μLN μSN AT AN wL wS phat : ℝ}
    (h1 : μL1 + μS1 = 1 - μKT) (h2 : μL2 + μS2 = 1 - μKT) (hK : μKT < 1)
    (hdet : μL1 * μS2 - μS1 * μL2 ≠ 0) (e1 : AT = μL1 * wL + μS1 * wS)
    (e2 : AT = μL2 * wL + μS2 * wS) (eN : phat + AN = μLN * wL + μSN * wS) :
    phat = (μLN + μSN) / (1 - μKT) * AT - AN := by
  obtain ⟨hL, hS⟩ := threeFactor_unique h1 h2 hK hdet e1 e2
  rw [hL, hS] at eN
  have hne : 1 - μKT ≠ 0 := by linarith
  field_simp
  field_simp at eN
  linarith

/-- T7 three factors, Harrod–Balassa–Samuelson sign, O&R §4.2.4, p. 215, corrected as in
T4: if `(μ_LN + μ_SN)/(1 − μ_KT) ≥ 1`, `Â_T ≥ 0` and `Â_T > Â_N`, then `p̂ > 0`. -/
theorem threeFactor_hbs {μKT μLN μSN AT AN : ℝ} (hK : μKT < 1)
    (hle : 1 - μKT ≤ μLN + μSN) (hA : 0 ≤ AT) (hfaster : AN < AT) :
    0 < (μLN + μSN) / (1 - μKT) * AT - AN :=
  bs_price_rises (by linarith) hle hA hfaster

/-- T7 immobile capital, O&R §4.2.4, p. 216: with two tradables sharing productivity growth
`Â_T`, `Â_T = μ_Ki r̂ + μ_Li ŵ` (`μ_Ki + μ_Li = 1`) and `μ_K1 ≠ μ_K2`, the unique solution is
`r̂ = ŵ = Â_T`. -/
theorem immobileCapital_unique {μK1 μL1 μK2 μL2 AT rhat what : ℝ} (h1 : μK1 + μL1 = 1)
    (h2 : μK2 + μL2 = 1) (hne : μK1 ≠ μK2) (e1 : AT = μK1 * rhat + μL1 * what)
    (e2 : AT = μK2 * rhat + μL2 * what) : rhat = AT ∧ what = AT := by
  have huv : (μK1 - μK2) * (rhat - what) = 0 := by
    linear_combination e2 - e1 - what * (h1 - h2)
  have hrw : rhat = what := sub_eq_zero.1 ((mul_eq_zero.1 huv).resolve_left (sub_ne_zero.2 hne))
  have : what = AT := by
    rw [hrw] at e1; linear_combination -e1 - what * h1
  exact ⟨hrw.trans this, this⟩

/-- T7 immobile capital, degenerate case, O&R §4.2.4, p. 216 ("except in degenerate cases"):
if `μ_K1 = μ_K2 = μ_K` the system has other solutions, e.g. `(Â_T + μ_L, Â_T − μ_K)`. -/
theorem immobileCapital_degenerate {μK μL AT : ℝ} (h : μK + μL = 1) :
    AT = μK * (AT + μL) + μL * (AT - μK) := by
  linear_combination (-AT) * h

/-- T7 immobile capital, the price of nontradables, O&R §4.2.4, p. 216:
`p̂ = μ_KN r̂ + μ_LN ŵ − Â_N = Â_T − Â_N`. -/
theorem immobileCapital_price {μK1 μL1 μK2 μL2 μKN μLN AT AN rhat what phat : ℝ}
    (h1 : μK1 + μL1 = 1) (h2 : μK2 + μL2 = 1) (hN : μKN + μLN = 1) (hne : μK1 ≠ μK2)
    (e1 : AT = μK1 * rhat + μL1 * what) (e2 : AT = μK2 * rhat + μL2 * what)
    (eN : phat + AN = μKN * rhat + μLN * what) : phat = AT - AN := by
  obtain ⟨hr, hw⟩ := immobileCapital_unique h1 h2 hne e1 e2
  rw [hr, hw] at eN
  linear_combination eN + AT * hN

/-- Exercise 1, O&R p. 264: with labour-augmenting technology `Y_T = F(K_T, E_T L_T)` the
tradables sector earns zero maximum profit at the wage `w = E_T w₀(r)`, `w₀(r) = w(r, 1)`:
`E L f(K/(E L)) ≤ rK + E w₀ L` for all `K ≥ 0`, `L > 0`, with equality iff capital per
efficiency unit is `k(1, r)`. -/
theorem ex1_zero_max_profit (F : IntensiveTech) {E r K L : ℝ} (hE : 0 < E) (hr : 0 < r)
    (hK : 0 ≤ K) (hL : 0 < L) :
    E * L * F.f (K / (E * L)) ≤ r * K + E * F.wage 1 r * L ∧
      (E * L * F.f (K / (E * L)) = r * K + E * F.wage 1 r * L ↔
        K / (E * L) = F.kstar 1 r) := by
  obtain ⟨hk, hfoc⟩ := F.kstar_foc one_pos hr
  have hw : 1 * F.mpl (F.kstar 1 r) = F.wage 1 r := rfl
  have hEL : 0 < E * L := mul_pos hE hL
  have e : r * K + E * F.wage 1 r * L = r * K + F.wage 1 r * (E * L) := by ring
  have e' : E * L * F.f (K / (E * L)) = 1 * ((E * L) * F.f (K / (E * L))) := by ring
  rw [e, e']
  exact ⟨F.crs_profit_le one_pos hk hfoc hw hK hEL, F.crs_profit_eq_iff one_pos hk hfoc hw hK hEL⟩

/-- Exercise 1, O&R p. 264: along a path of labour-augmenting progress `E_T(t)`, the wage
`w = E_T w₀(r)` grows at exactly `ŵ = Ê_T` (replacing `Â_T/μ_LT` of (8)). -/
theorem ex1_wage_hat (F : IntensiveTech) {E : ℝ → ℝ} {E' t r : ℝ} (hE : HasDerivAt E E' t)
    (hE0 : 0 < E t) (hr : 0 < r) :
    HasDerivAt (fun s => Real.log (E s * F.wage 1 r)) (E' / E t) t := by
  have hw := F.wage_pos one_pos hr
  refine ((hE.mul_const (F.wage 1 r)).log (mul_pos hE0 hw).ne').congr_deriv ?_
  field_simp

/-- Exercise 1 and O&R (9), p. 208: for any differentiable wage path `W(t)`, the nontraded
price `p = c(r, W)/A_N` satisfies `p̂ = μ_LN ŵ − Â_N` exactly, with
`μ_LN = W/(c g(k_N))`. With `W = E_T w₀(r)` this gives `p̂ = μ_LN Ê_T − Â_N`. -/
theorem priceN_wage_path (G : IntensiveTech) {r : ℝ} {W AN : ℝ → ℝ} {W' AN' t : ℝ}
    (hW : HasDerivAt W W' t) (hN : HasDerivAt AN AN' t) (hr : 0 < r) (hW0 : 0 < W t)
    (hN0 : 0 < AN t) :
    HasDerivAt (fun s => Real.log (unitCost G r (W s) / AN s))
      (W t / (unitCost G r (W t) * G.f (kN G r (W t))) * (W' / W t) - AN' / AN t) t := by
  have hC := unitCost_path_hasDerivAt G (hasDerivAt_const t r) hW hr hW0
  obtain ⟨hc, _, _⟩ := unitCost_foc G hr hW0
  have hg := G.f_pos (kN_spec G hr hW0).1
  refine ((hC.div hN hN0.ne').log (div_pos hc hN0).ne').congr_deriv ?_
  simp only [Pi.div_apply]
  field_simp
  ring

/-- Exercise 1 with O&R (17)–(18), §4.3.2, pp. 224–225: the steady-state labour movement into
nontradables. From `L̂_N = Ĉ_N − α k̂_N`, `Ĉ_N = Ẑ − (γθ + 1 − γ)p̂`, `Ẑ = ψ_L ŵ` and Cobb–Douglas
nontradables `p̂ = (1 − α)ŵ`, `k̂_N = ŵ`, one gets
`L̂_N = {ψ_L − (1 − α)(γθ + 1 − γ) − α} ŵ`. With Hicks-neutral progress `ŵ = Â_T/μ_LT`; with
labour-augmenting progress `ŵ = Ê_T`: the bracket, hence the sign condition for a labour
exodus from tradables, is the same. -/
theorem ex1_labour_reallocation {α γ θ ψL what phat Zhat CNhat kNhat LNhat : ℝ}
    (hL : LNhat = CNhat - α * kNhat) (hC : CNhat = Zhat - (γ * θ + 1 - γ) * phat)
    (hZ : Zhat = ψL * what) (hp : phat = (1 - α) * what) (hk : kNhat = what) :
    LNhat = (ψL - (1 - α) * (γ * θ + 1 - γ) - α) * what := by
  rw [hL, hC, hZ, hp, hk]; ring

/-- Exercise 2, O&R p. 265: a rise in the world interest rate lowers the tradables capital
intensity `k_T`, the wage `w`, and the nontradables capital intensity `k_N`. -/
theorem ex2_rise_in_r (F G : IntensiveTech) {AT r1 r2 : ℝ} (hAT : 0 < AT) (hr1 : 0 < r1)
    (h : r1 < r2) :
    F.kstar AT r2 < F.kstar AT r1 ∧ F.wage AT r2 < F.wage AT r1 ∧
      kN G r2 (F.wage AT r2) < kN G r1 (F.wage AT r1) := by
  have hr2 : 0 < r2 := lt_trans hr1 h
  have hk := F.kstar_strictAntiOn_r hAT (show r1 ∈ Ioi (0 : ℝ) from hr1)
    (show r2 ∈ Ioi (0 : ℝ) from hr2) h
  have hw := F.wage_strictAntiOn_r hAT (show r1 ∈ Ioi (0 : ℝ) from hr1)
    (show r2 ∈ Ioi (0 : ℝ) from hr2) h
  have hw1 := F.wage_pos hAT hr1
  have hw2 := F.wage_pos hAT hr2
  refine ⟨hk, hw, ?_⟩
  have hratio : F.wage AT r2 / r2 < F.wage AT r1 / r1 := by
    rw [div_lt_div_iff₀ hr2 hr1]; nlinarith
  exact G.wrInv_strictMonoOn (div_pos hw2 hr2) (div_pos hw1 hr1) hratio

/-- Exercise 2, O&R p. 265 (and p. 209): the equilibrium relative price of nontradables is
locally decreasing in `r` — its derivative is negative — iff `μ_LN > μ_LT`. -/
theorem ex2_price_falls_iff (F G : IntensiveTech) {AT AN r D : ℝ} (hr : 0 < r) (hAT : 0 < AT)
    (hAN : 0 < AN) (hD : HasDerivAt (fun ρ => Real.log (eqmPrice F G ρ AT AN)) D r) :
    D < 0 ↔ muLT F r AT < muLN F G r AT := by
  have h := logPrice_hat_r F G (R := id) (hasDerivAt_id r) hr hAT hAN
  rw [hD.unique h, ← r_elasticity_neg_iff (muLT_pos F hr hAT)]
  simp only [id]
  have : 0 < 1 / r := by positivity
  constructor <;> intro h <;> nlinarith

/-- Exercise 6(a), O&R p. 266: lifetime earnings of the educated, discounted at `ρ = r + π`,
`∫_T^∞ e^{−ρt} A T^α h dt = e^{−ρT} A T^α h/ρ`. -/
theorem ex6_lifetime_earnings {ρ A α h T : ℝ} (hρ : 0 < ρ) :
    ∫ t in Ioi T, Real.exp (-ρ * t) * (A * T ^ α * h) =
      Real.exp (-ρ * T) * (A * T ^ α * h) / ρ := by
  rw [MeasureTheory.integral_mul_const, integral_exp_mul_Ioi (by linarith) T]
  field_simp

/-- Exercise 6(b), O&R p. 266: the first-order condition for schooling. The log of the
educated earnings factor `e^{−ρT}T^α` has derivative `α/T − ρ`, which vanishes iff
`T = α/ρ`. -/
theorem ex6_foc {ρ α T : ℝ} (hT : 0 < T) (hρ : 0 < ρ) :
    HasDerivAt (fun x => -ρ * x + α * Real.log x) (-ρ + α / T) T ∧
      (-ρ + α / T = 0 ↔ T = α / ρ) := by
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (fun x => -ρ * x) (-ρ) T := by
      simpa using (hasDerivAt_id T).const_mul (-ρ)
    have h2 := (Real.hasDerivAt_log hT.ne').const_mul α
    exact (h1.add h2).congr_deriv (by field_simp)
  · constructor
    · intro h; field_simp at h ⊢; linarith
    · intro h
      have hα : α ≠ 0 := by intro h0; rw [h0, zero_div] at h; linarith
      rw [h, div_div_eq_mul_div, mul_div_cancel_left₀ ρ hα]; ring

/-- Exercise 6(b), O&R p. 266: `T* = α/(r + π)` is the unique optimal schooling length —
for every other `T > 0`, the value `e^{−ρT}AT^αh/ρ − w/ρ` is strictly smaller. -/
theorem ex6_optimal_schooling {ρ α A h w T : ℝ} (hρ : 0 < ρ) (hα : 0 < α) (hAh : 0 < A * h)
    (hT : 0 < T) (hne : T ≠ α / ρ) :
    Real.exp (-ρ * T) * A * T ^ α * h / ρ - w / ρ <
      Real.exp (-ρ * (α / ρ)) * A * (α / ρ) ^ α * h / ρ - w / ρ := by
  have hTs : 0 < α / ρ := div_pos hα hρ
  have key : Real.exp (-ρ * T) * T ^ α < Real.exp (-ρ * (α / ρ)) * (α / ρ) ^ α := by
    rw [Real.rpow_def_of_pos hT, Real.rpow_def_of_pos hTs, ← Real.exp_add, ← Real.exp_add,
      Real.exp_lt_exp]
    have hx : 0 < ρ * T / α := div_pos (mul_pos hρ hT) hα
    have hx1 : ρ * T / α ≠ 1 := by
      intro h1; apply hne; field_simp at h1 ⊢; linarith
    have hlog := Real.log_lt_sub_one_of_pos hx hx1
    have hsplit : Real.log (ρ * T / α) = Real.log T - Real.log (α / ρ) := by
      rw [← Real.log_div hT.ne' hTs.ne']; congr 1; field_simp
    rw [hsplit] at hlog
    have : α * (Real.log T - Real.log (α / ρ)) < α * (ρ * T / α - 1) :=
      mul_lt_mul_of_pos_left hlog hα
    have e : α * (ρ * T / α - 1) = ρ * T - α := by field_simp
    have e2 : -ρ * (α / ρ) = -α := by field_simp
    rw [e2]; nlinarith
  have := mul_lt_mul_of_pos_right key hAh
  have hdiv := div_lt_div_of_pos_right this hρ
  have r1 : Real.exp (-ρ * T) * A * T ^ α * h / ρ = Real.exp (-ρ * T) * T ^ α * (A * h) / ρ := by
    ring
  have r2 : Real.exp (-ρ * (α / ρ)) * A * (α / ρ) ^ α * h / ρ
      = Real.exp (-ρ * (α / ρ)) * (α / ρ) ^ α * (A * h) / ρ := by ring
  rw [r1, r2]; linarith

/-- Exercise 6(c), O&R p. 266: if the educated and the uneducated are indifferent,
`e^{−ρT*}AT*^α h/ρ = w/ρ` at `T* = α/ρ`, then `h/w = A⁻¹ e^α (ρ/α)^α`. -/
theorem ex6_relative_wage {ρ α A h w : ℝ} (hρ : 0 < ρ) (hα : 0 < α) (hA : 0 < A) (hw : 0 < w)
    (hindiff : Real.exp (-ρ * (α / ρ)) * A * (α / ρ) ^ α * h / ρ = w / ρ) :
    h / w = A⁻¹ * Real.exp α * (ρ / α) ^ α := by
  have e2 : -ρ * (α / ρ) = -α := by field_simp
  rw [e2, div_left_inj' hρ.ne', Real.div_rpow hα.le hρ.le] at hindiff
  rw [Real.div_rpow hρ.le hα.le]
  have hαα : 0 < α ^ α := Real.rpow_pos_of_pos hα α
  have hρα : 0 < ρ ^ α := Real.rpow_pos_of_pos hρ α
  have hexp : Real.exp (-α) * Real.exp α = 1 := by rw [← Real.exp_add]; simp
  rw [div_eq_iff hw.ne', ← hindiff]
  field_simp
  linear_combination (-h) * hexp

/-- The unskilled wage implied by Exercise 6(c), O&R p. 266:
`w = h A e^{−α} (α/ρ)^α` with `ρ = r + π`. -/
noncomputable def skillWage (h A α ρ : ℝ) : ℝ := h * A * Real.exp (-α) * (α / ρ) ^ α

/-- Exercise 6(d), O&R p. 266: `∂ log w/∂α = log(α/(r + π))`. -/
theorem ex6_dlogw_dalpha {h A α ρ : ℝ} (hh : 0 < h) (hA : 0 < A) (hα : 0 < α) (hρ : 0 < ρ) :
    HasDerivAt (fun a => Real.log (skillWage h A a ρ)) (Real.log (α / ρ)) α := by
  have hg : HasDerivAt (fun a => Real.log h + Real.log A + -a + a * (Real.log a - Real.log ρ))
      (0 + 0 + -1 + (1 * (Real.log α - Real.log ρ) + α * α⁻¹)) α := by
    have h1 : HasDerivAt (fun a : ℝ => Real.log h) 0 α := hasDerivAt_const α _
    have h2 : HasDerivAt (fun a : ℝ => Real.log A) 0 α := hasDerivAt_const α _
    have h3 : HasDerivAt (fun a : ℝ => -a) (-1) α := (hasDerivAt_id α).neg
    have h4 : HasDerivAt (fun a : ℝ => Real.log a - Real.log ρ) α⁻¹ α :=
      (Real.hasDerivAt_log hα.ne').sub_const (Real.log ρ)
    exact ((h1.add h2).add h3).add ((hasDerivAt_id α).mul h4)
  have hv : (0 : ℝ) + 0 + -1 + (1 * (Real.log α - Real.log ρ) + α * α⁻¹)
      = Real.log (α / ρ) := by
    rw [Real.log_div hα.ne' hρ.ne']; field_simp; ring
  rw [hv] at hg
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hα] with a ha
  have ha' : (0 : ℝ) < a := ha
  unfold skillWage
  rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos (div_pos ha' hρ) a).ne',
    Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul hh.ne' hA.ne',
    Real.log_exp, Real.log_rpow (div_pos ha' hρ), Real.log_div ha'.ne' hρ.ne']

/-- Exercise 6(d), O&R p. 266: the unskilled wage rises with the schooling elasticity `α`
exactly when `α > r + π` (the book's "you may assume" condition is also necessary). -/
theorem ex6_w_increasing_in_alpha_iff {α ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ) :
    0 < Real.log (α / ρ) ↔ ρ < α := by
  rw [Real.log_pos_iff (div_pos hα hρ).le, one_lt_div hρ]

/-- Exercise 6(d), O&R p. 266: the unskilled wage is strictly increasing in schooling
productivity `A`. -/
theorem ex6_w_strictMono_A {h α ρ : ℝ} (hh : 0 < h) (hα : 0 < α) (hρ : 0 < ρ) :
    StrictMono fun A => skillWage h A α ρ := by
  intro A1 A2 hA
  unfold skillWage
  have : 0 < h * Real.exp (-α) * (α / ρ) ^ α :=
    mul_pos (mul_pos hh (Real.exp_pos _)) (Real.rpow_pos_of_pos (div_pos hα hρ) α)
  nlinarith

/-- Exercise 6(d), O&R p. 266: the unskilled wage is strictly decreasing in the death
probability `π` (through `ρ = r + π`). -/
theorem ex6_w_strictAnti_pi {h A α r : ℝ} (hh : 0 < h) (hA : 0 < A) (hα : 0 < α) (hr : 0 < r) :
    StrictAntiOn (fun π => skillWage h A α (r + π)) (Ici 0) := by
  intro π1 hπ1 π2 hπ2 hlt
  have hπ1' : (0 : ℝ) ≤ π1 := hπ1
  have hρ1 : 0 < r + π1 := by linarith
  have hρ2 : 0 < r + π2 := by linarith
  have hq : α / (r + π2) < α / (r + π1) := div_lt_div_of_pos_left hα hρ1 (by linarith)
  have hpow := Real.rpow_lt_rpow (div_pos hα hρ2).le hq hα
  unfold skillWage
  have : 0 < h * A * Real.exp (-α) := mul_pos (mul_pos hh hA) (Real.exp_pos _)
  exact mul_lt_mul_of_pos_left hpow this

/-- Exercise 6(d), O&R p. 266: with the skilled wage given by a tradables factor-price
frontier `h = h(r)` (O&R (6), strictly decreasing), the unskilled wage is strictly decreasing
in `r`. -/
theorem ex6_w_strictAnti_r (T : IntensiveTech) {AS A α π : ℝ} (hAS : 0 < AS) (hA : 0 < A)
    (hα : 0 < α) (hπ : 0 ≤ π) :
    StrictAntiOn (fun r => skillWage (T.wage AS r) A α (r + π)) (Ioi 0) := by
  intro r1 hr1 r2 hr2 hlt
  have hr1' : (0 : ℝ) < r1 := hr1
  have hr2' : (0 : ℝ) < r2 := hr2
  have hh := T.wage_strictAntiOn_r hAS hr1 hr2 hlt
  have hh2 := T.wage_pos hAS hr2'
  have hq : α / (r2 + π) < α / (r1 + π) := div_lt_div_of_pos_left hα (by linarith) (by linarith)
  have hpow := Real.rpow_lt_rpow (div_pos hα (by linarith)).le hq hα
  have hp2 : 0 < (α / (r2 + π)) ^ α := Real.rpow_pos_of_pos (div_pos hα (by linarith)) α
  have hc : 0 < A * Real.exp (-α) := mul_pos hA (Real.exp_pos _)
  unfold skillWage
  dsimp only
  have e : ∀ x y : ℝ, x * A * Real.exp (-α) * y = (A * Real.exp (-α)) * (x * y) := by
    intros; ring
  rw [e, e]
  apply mul_lt_mul_of_pos_left _ hc
  exact mul_lt_mul hh hpow.le hp2 (T.wage_pos hAS hr1').le

/-- Exercise 6(e), O&R p. 266: given `r`, the relative price of nontradables is strictly
increasing in the unskilled wage, so it is higher where `w` is higher (high `A`, low `π`, or
high `α` when `α > r + π`). -/
theorem ex6e_price_increasing_in_w (G : IntensiveTech) {r AN w1 w2 : ℝ} (hr : 0 < r)
    (hAN : 0 < AN) (hw1 : 0 < w1) (hlt : w1 < w2) :
    unitCost G r w1 / AN < unitCost G r w2 / AN :=
  div_lt_div_of_pos_right (unitCost_strictMonoOn_w G hr hw1
    (show w2 ∈ Ioi (0 : ℝ) from lt_trans hw1 hlt) hlt) hAN

end ObstfeldRogoff.RealExchangeRate.BSExtensions

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The long run: GDP and GNP with traded and nontraded goods

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.3.1,
pp. 216–220, footnotes 18–19. The world interest rate fixes the capital–labour
ratios `k_T`, `k_N` and the wage `w`, so each sector's output is its factor payments:
`Y_T = (rk_T + w)L_T` and `pY_N = (rk_N + w)L_N`. Labour is `L = L_T + L_N`, capital
is `K = k_T L_T + k_N L_N`, and national wealth is `Q = B + K`.

* **The GDP line** (O&R (4.10)): `Y_T = −[(rk_T + w)/(rk_N + w)] pY_N + (rk_T + w)L`. It is
  steeper than the GNP line iff tradables are capital-intensive, `k_T > k_N`.
* **The GNP line** (O&R (4.11)): in a steady state `C_T + pC_N = wL + rQ`, and with
  nontradables clearing, `Y_T − C_T = −rB` (footnote 18).
* **Wealth and the trade balance** (p. 220): with `k_T > k_N`, a rise in wealth that
  shifts labour into nontradables raises foreign assets by more than the rise in
  wealth, so the trade surplus falls by more than `r dQ`.
* **Gains from capital mobility** (footnote 19): any allocation of the economy's own
  capital `Q` and labour yields output worth at most `wL + rQ`, the GNP line. This
  follows from CRS profit maximisation in each sector.
-/

namespace ObstfeldRogoff.RealExchangeRate.LongRunGDPGNP

/-- **The GDP line**, O&R (4.10), p. 218: sectoral outputs equal factor payments and labour is fully
employed, so `Y_T = −[(rk_T + w)/(rk_N + w)] pY_N + (rk_T + w)L`. -/
theorem gdp_line {r w kT kN LT LN L YT pYN : ℝ} (hN : 0 < r * kN + w)
    (hT : YT = (r * kT + w) * LT) (hNp : pYN = (r * kN + w) * LN) (hL : LT + LN = L) :
    YT = -((r * kT + w) / (r * kN + w)) * pYN + (r * kT + w) * L := by
  rw [hT, hNp, ← hL]
  field_simp
  ring

/-- **Slope of the GDP line** (O&R p. 218): its slope magnitude `(rk_T + w)/(rk_N + w)` exceeds
one iff tradables are the capital-intensive sector. -/
theorem gdp_slope_gt_one_iff {r w kT kN : ℝ} (hr : 0 < r) (hN : 0 < r * kN + w) :
    1 < (r * kT + w) / (r * kN + w) ↔ kN < kT := by
  rw [one_lt_div hN]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **GDP equals factor income** (O&R p. 219): `Y_T + pY_N = rK + wL` with
`K = k_T L_T + k_N L_N`. -/
theorem gdp_eq_factor_income {r w kT kN LT LN YT pYN : ℝ}
    (hT : YT = (r * kT + w) * LT) (hNp : pYN = (r * kN + w) * LN) :
    YT + pYN = r * (kT * LT + kN * LN) + w * (LT + LN) := by
  rw [hT, hNp]; ring

/-- **The trade balance in the long run**, O&R footnote 18, p. 219: in a steady state with the GNP
line `C_T + pC_N = wL + rQ` (4.11), nontradables clearing `Y_N = C_N`, and `Q = B + K`, the trade
surplus pays the interest on foreign debt: `Y_T − C_T = −rB`. -/
theorem trade_balance_long_run {r w L Q B K YT pYN CT pCN : ℝ}
    (hgnp : CT + pCN = w * L + r * Q) (hgdp : YT + pYN = r * K + w * L) (hclear : pCN = pYN)
    (hQ : Q = B + K) : YT - CT = -(r * B) := by
  rw [hQ] at hgnp
  linarith

/-- **Foreign assets respond more than one-for-one to wealth**, O&R p. 220: capital is
`K = k_T L + (k_N − k_T)L_N` at fixed ratios, so with `Q = B + K` a change in wealth `dQ` and in
nontradables employment `dL_N` changes foreign assets by `dB = dQ − (k_N − k_T)dL_N`. -/
theorem foreign_asset_change {kT kN L dQ dLN : ℝ} :
    dQ - ((kT * L + (kN - kT) * dLN) - kT * L) = dQ - (kN - kT) * dLN := by ring

/-- **A rise in wealth raises foreign assets by more than itself** (O&R p. 220): if tradables are
capital-intensive (`k_T > k_N`) and the rise in wealth draws labour into nontradables (`dL_N > 0`),
then `dB > dQ`, and the trade surplus `Y_T − C_T = −rB` falls by more than `r dQ`. -/
theorem wealth_rise_trade_balance {r kT kN dQ dLN : ℝ} (hr : 0 < r) (hk : kN < kT)
    (hL : 0 < dLN) :
    dQ < dQ - (kN - kT) * dLN ∧ -(r * (dQ - (kN - kT) * dLN)) < -(r * dQ) := by
  have h : 0 < (kT - kN) * dLN := mul_pos (by linarith) hL
  constructor
  · nlinarith
  · nlinarith

/-- **Tradables output falls as labour moves to nontradables** (O&R p. 220):
`dY_T = −(rk_T + w)dL_N < 0` at fixed factor prices. -/
theorem tradables_output_falls {r w kT dLN : ℝ} (hT : 0 < r * kT + w) (hL : 0 < dLN) :
    -((r * kT + w) * dLN) < 0 := by
  have := mul_pos hT hL
  linarith

/-- **Gains from capital mobility**, O&R footnote 19, p. 219: if in each sector output never
exceeds factor payments at the world factor prices (CRS profit maximisation), then any use of the
economy's own capital `Q = K_T + K_N` and labour `L = L_T + L_N` yields output worth at most
`wL + rQ`: the autarky frontier lies weakly inside the GNP line. -/
theorem autarky_frontier_inside_gnp {r w KT KN LT LN YT pYN Q L : ℝ}
    (hT : YT ≤ r * KT + w * LT) (hN : pYN ≤ r * KN + w * LN) (hQ : KT + KN = Q)
    (hL : LT + LN = L) : YT + pYN ≤ w * L + r * Q := by
  rw [← hQ, ← hL]
  linarith

/-- **The frontiers touch only at the optimal ratios** (footnote 19): output equals `wL + rQ` iff
both sectors earn exactly their factor payments. -/
theorem autarky_frontier_eq_gnp_iff {r w KT KN LT LN YT pYN Q L : ℝ}
    (hT : YT ≤ r * KT + w * LT) (hN : pYN ≤ r * KN + w * LN) (hQ : KT + KN = Q)
    (hL : LT + LN = L) :
    YT + pYN = w * L + r * Q ↔ YT = r * KT + w * LT ∧ pYN = r * KN + w * LN := by
  rw [← hQ, ← hL]
  constructor
  · intro h; constructor <;> linarith
  · rintro ⟨h1, h2⟩; rw [h1, h2]; ring

end ObstfeldRogoff.RealExchangeRate.LongRunGDPGNP

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Productivity growth and employment in nontradables

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.3.2,
pp. 220–225. Nontradables are produced with `Y_N = A_N K_N^α L_N^{1−α}` and consumed
at home, and consumers have CES preferences over traded and nontraded goods.
Growth rates are written `x̂ = dx/x`.

* **Employment in nontradables** (O&R (4.12)): with `Y_N = C_N` and `A_N` fixed,
  `L̂_N = Ĉ_N − αk̂_N`.
* **Demand for nontradables** (O&R (4.17)): at `p = 1` the log-derivative of CES
  demand with respect to `p` is `−[γθ + (1 − γ)]`, and wealth `Z = wL + rQ` grows at
  `Ẑ = ψ_L ŵ` with `ψ_L = wL/(wL + rQ)`.
* **The employment effect of tradables productivity** (O&R (4.18)):
  `L̂_N = {ψ_L − (1 − α)[γθ + 1 − γ] − α} Â_T/μ_LT`. With unit elasticity (`θ = 1`) this is
  `(ψ_L − 1)Â_T/μ_LT`, negative when the country has positive wealth (`ψ_L < 1` iff
  `Q > 0`).
-/

namespace ObstfeldRogoff.RealExchangeRate.ManufacturingEmployment

/-- **Employment in nontradables**, O&R (4.12), p. 221: `Y_N = A_N k_N^α L_N` (CRS), so with `A_N`
fixed `Ŷ_N = αk̂_N + L̂_N`; market clearing `Ŷ_N = Ĉ_N` gives `L̂_N = Ĉ_N − αk̂_N`. -/
theorem employment_growth {α hatY hatC hatk hatL : ℝ} (hprod : hatY = α * hatk + hatL)
    (hclear : hatY = hatC) : hatL = hatC - α * hatk := by linarith

/-- The CES demand for nontradables `C_N = p^{−θ}(1 − γ)Z/(γ + (1 − γ)p^{1−θ})`, O&R (4.16). -/
noncomputable def cesDemandN (γ θ Z p : ℝ) : ℝ :=
  p ^ (-θ) * (1 - γ) * Z / (γ + (1 - γ) * p ^ (1 - θ))

/-- **The price elasticity of nontradables demand at `p = 1`**, O&R (4.17), p. 223: the
log-derivative of `C_N` with respect to `p` at `p = 1` is `−[γθ + (1 − γ)]`. -/
theorem hasDerivAt_log_cesDemandN {γ θ Z : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hZ : 0 < Z) :
    HasDerivAt (fun p => Real.log (cesDemandN γ θ Z p)) (-(γ * θ + (1 - γ))) 1 := by
  have h1 : HasDerivAt (fun p : ℝ => p ^ (-θ)) (-θ * 1 ^ (-θ - 1)) 1 :=
    Real.hasDerivAt_rpow_const (Or.inl one_ne_zero)
  have h2 : HasDerivAt (fun p : ℝ => p ^ (1 - θ)) ((1 - θ) * 1 ^ (1 - θ - 1)) 1 :=
    Real.hasDerivAt_rpow_const (Or.inl one_ne_zero)
  have hden : HasDerivAt (fun p : ℝ => γ + (1 - γ) * p ^ (1 - θ))
      ((1 - γ) * ((1 - θ) * 1 ^ (1 - θ - 1))) 1 := (h2.const_mul (1 - γ)).const_add γ
  have hnum : HasDerivAt (fun p : ℝ => p ^ (-θ) * (1 - γ) * Z)
      (-θ * 1 ^ (-θ - 1) * (1 - γ) * Z) 1 := (h1.mul_const (1 - γ)).mul_const Z
  have hden1 : γ + (1 - γ) * (1 : ℝ) ^ (1 - θ) ≠ 0 := by simp
  have hC := hnum.div hden hden1
  have hC1 : cesDemandN γ θ Z 1 ≠ 0 := by
    unfold cesDemandN
    simp only [Real.one_rpow, one_mul, mul_one]
    have : (0 : ℝ) < 1 - γ := by linarith
    positivity
  have := hC.log hC1
  unfold cesDemandN at this ⊢
  refine this.congr_deriv ?_
  have : (0 : ℝ) < 1 - γ := by linarith
  simp only [Pi.div_apply, Real.one_rpow, one_mul, mul_one]
  field_simp
  ring

/-- **Wealth growth**, O&R p. 224: with `Z = wL + rQ` and `r`, `L`, `Q` fixed,
`Ẑ = ψ_L ŵ` where `ψ_L = wL/(wL + rQ)`. -/
theorem wealth_growth {w L r Q dw : ℝ} (hw : w ≠ 0) :
    (dw * L) / (w * L + r * Q) = (w * L / (w * L + r * Q)) * (dw / w) := by
  field_simp

/-- **The employment effect of tradables productivity**, O&R (4.18), p. 224: combining
`L̂_N = Ĉ_N − αk̂_N` (4.12), `Ĉ_N = Ẑ − [γθ + 1 − γ]p̂` (4.17), `Ẑ = ψ_L ŵ`, and the supply side
`ŵ = k̂_N = Â_T/μ_LT`, `p̂ = (1 − α)Â_T/μ_LT`, gives
`L̂_N = {ψ_L − (1 − α)[γθ + 1 − γ] − α} Â_T/μ_LT`. -/
theorem employment_effect {α γ θ ψ μ hatA hatL hatC hatZ hatw hatp hatk : ℝ}
    (h12 : hatL = hatC - α * hatk) (h17 : hatC = hatZ - (γ * θ + (1 - γ)) * hatp)
    (hZ : hatZ = ψ * hatw) (hw : hatw = hatA / μ) (hk : hatk = hatA / μ)
    (hp : hatp = (1 - α) * hatA / μ) :
    hatL = (ψ - (1 - α) * (γ * θ + 1 - γ) - α) * hatA / μ := by
  rw [h12, h17, hZ, hw, hk, hp]
  ring

/-- **Unit elasticity** (O&R p. 224): with `θ = 1` the bracket in (4.18) reduces to `ψ_L − 1`. -/
theorem employment_effect_unit {α γ ψ μ hatA : ℝ} :
    (ψ - (1 - α) * (γ * 1 + 1 - γ) - α) * hatA / μ = (ψ - 1) * hatA / μ := by ring

/-- **The labour share of wealth is below one iff wealth is positive** (O&R p. 224): with
`wL > 0` and `r > 0`, `ψ_L = wL/(wL + rQ) < 1` iff `Q > 0`. -/
theorem psi_lt_one_iff {w L r Q : ℝ} (hr : 0 < r) (hden : 0 < w * L + r * Q) :
    w * L / (w * L + r * Q) < 1 ↔ 0 < Q := by
  rw [div_lt_one hden]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Productivity growth in tradables shrinks nontradables employment** (O&R p. 224): with unit
elasticity, positive wealth and `Â_T > 0`, `L̂_N = (ψ_L − 1)Â_T/μ_LT < 0`. -/
theorem employment_falls {ψ μ hatA : ℝ} (hψ : ψ < 1) (hμ : 0 < μ) (hA : 0 < hatA) :
    (ψ - 1) * hatA / μ < 0 :=
  div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hA) hμ

end ObstfeldRogoff.RealExchangeRate.ManufacturingEmployment

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The CES consumption index and the consumption-based price index

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.3.2
(pp. 222–223, eqs. (13)–(16), footnotes 13 and 22) and §4.4.1.1 (pp. 226–228, eqs. (20)–(22),
footnotes 25–26), plus Exercise 8(a) (p. 267).

The CES index (13) is
`Ω(C_T, C_N) = [γ^{1/θ} C_T^{(θ−1)/θ} + (1−γ)^{1/θ} C_N^{(θ−1)/θ}]^{θ/(θ−1)}`
with `0 < γ < 1`, `θ > 0`, `θ ≠ 1`. With the traded good as numeraire and `p` the relative
price of nontradables, spending is `Z = C_T + p C_N` (14). We prove:

* the demand functions (16) exhaust the budget and satisfy the relative demand (15);
* the value of the index at the demands (16) is `Z/P` with
  `P = [γ + (1−γ) p^{1−θ}]^{1/(1−θ)}` (20), i.e. (21), and (22);
* **duality**: every bundle with `C_T + p C_N = Z` has `Ω ≤ Z/P` (a tangent-line argument
  based on Bernoulli's inequality, one case for each sign of `(θ−1)/θ`), so `P` is the
  minimum expenditure buying one unit of `Ω` (the definition on p. 227);
* `P` is strictly increasing in `p` and `d log P / d log p = 1 − γ` at `p = 1` (fn 26);
* the Cobb–Douglas limits as `θ → 1`: `P → p^{1−γ}` (p. 228) and
  `Ω → C_T^γ C_N^{1−γ}/(γ^γ (1−γ)^{1−γ})` (fn 22), both from the power-mean limit;
* the elasticity of substitution is `θ` (fn 22) and the Cobb–Douglas MRS (fn 13);
* Exercise 8(a): the Cobb–Douglas price index `p^γ/(γ^γ (1−γ)^{1−γ})`.

Zero consumption of a good: for `θ < 1` both goods are essential and the book's index is `0`
when either argument is `0`, but Lean's `0 ^ y = 0` (for `y ≠ 0`) gives a junk value there,
so the duality theorem requires strictly positive consumption when `θ < 1`.
-/

namespace ObstfeldRogoff.RealExchangeRate.CESIndex

open Real Filter Topology Set

/-- The CES consumption index (13), O&R p. 222:
`[γ^{1/θ} C_T^{(θ−1)/θ} + (1−γ)^{1/θ} C_N^{(θ−1)/θ}]^{θ/(θ−1)}`. -/
noncomputable def cesIndex (γ θ CT CN : ℝ) : ℝ :=
  (γ ^ (1 / θ) * CT ^ ((θ - 1) / θ) + (1 - γ) ^ (1 / θ) * CN ^ ((θ - 1) / θ)) ^ (θ / (θ - 1))

/-- The common denominator `γ + (1−γ) p^{1−θ}` of the demand functions (16), O&R p. 223. -/
noncomputable def cesDenom (γ θ p : ℝ) : ℝ := γ + (1 - γ) * p ^ (1 - θ)

/-- The consumption-based price index (20), O&R p. 227:
`P = [γ + (1−γ) p^{1−θ}]^{1/(1−θ)}`. -/
noncomputable def cesPrice (γ θ p : ℝ) : ℝ := (γ + (1 - γ) * p ^ (1 - θ)) ^ (1 / (1 - θ))

/-- Demand for tradables (16), O&R p. 223: `C_T = γZ/(γ + (1−γ)p^{1−θ})`. -/
noncomputable def cesDemandT (γ θ p Z : ℝ) : ℝ := γ * Z / cesDenom γ θ p

/-- Demand for nontradables (16), O&R p. 223: `C_N = p^{−θ}(1−γ)Z/(γ + (1−γ)p^{1−θ})`. -/
noncomputable def cesDemandN (γ θ p Z : ℝ) : ℝ := p ^ (-θ) * (1 - γ) * Z / cesDenom γ θ p

/-- The denominator of (16) is positive, O&R p. 223. -/
theorem cesDenom_pos {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p) :
    0 < cesDenom γ θ p := by
  unfold cesDenom
  have := rpow_pos_of_pos hp (1 - θ)
  nlinarith

/-- The price index is the `1/(1−θ)` power of the denominator of (16), O&R (20), p. 227. -/
theorem cesPrice_eq_denom_rpow (γ θ p : ℝ) :
    cesPrice γ θ p = cesDenom γ θ p ^ (1 / (1 - θ)) := rfl

/-- The price index is positive, O&R (20), p. 227. -/
theorem cesPrice_pos {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p) :
    0 < cesPrice γ θ p :=
  rpow_pos_of_pos (cesDenom_pos hγ0 hγ1 hp) _

/-- `P^{1−θ} = γ + (1−γ)p^{1−θ}`, O&R (20), p. 227. -/
theorem cesPrice_rpow_one_sub {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p)
    (hθ1 : θ ≠ 1) : cesPrice γ θ p ^ (1 - θ) = γ + (1 - γ) * p ^ (1 - θ) := by
  have h1 : (1 - θ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ1)
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  unfold cesDenom at hD
  rw [cesPrice, ← rpow_mul hD.le, one_div_mul_cancel h1, rpow_one]

/-- The demands (16) exhaust spending, `C_T + p C_N = Z` (14), O&R p. 223. -/
theorem cesDemand_budget {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p) (Z : ℝ) :
    cesDemandT γ θ p Z + p * cesDemandN γ θ p Z = Z := by
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  have hpp : p * p ^ (-θ) = p ^ (1 - θ) := by
    rw [sub_eq_add_neg, rpow_add hp, rpow_one]
  unfold cesDemandT cesDemandN
  field_simp
  unfold cesDenom
  linear_combination (1 - γ) * Z * hpp

/-- Relative demand (15), O&R p. 222: `γ C_N / ((1−γ) C_T) = p^{−θ}` at the demands (16). -/
theorem cesDemand_ratio {γ θ p Z : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p) (hZ : Z ≠ 0) :
    γ * cesDemandN γ θ p Z / ((1 - γ) * cesDemandT γ θ p Z) = p ^ (-θ) := by
  have hD := (cesDenom_pos (θ := θ) hγ0 hγ1 hp).ne'
  have h1 : (1 - γ) ≠ 0 := by linarith
  unfold cesDemandT cesDemandN
  field_simp

/-- The demand (16) for tradables as `γ · (Z/D)`, O&R p. 223. -/
theorem cesDemandT_eq (γ θ p Z : ℝ) :
    cesDemandT γ θ p Z = γ * (Z / cesDenom γ θ p) := by
  unfold cesDemandT; ring

/-- The demand (16) for nontradables as `(1−γ) p^{−θ} · (Z/D)`, O&R p. 223. -/
theorem cesDemandN_eq (γ θ p Z : ℝ) :
    cesDemandN γ θ p Z = (1 - γ) * p ^ (-θ) * (Z / cesDenom γ θ p) := by
  unfold cesDemandN; ring

/-- (21), O&R p. 228: the CES index evaluated at the optimal demands (16) equals `Z/P`, with `P`
the price index (20). -/
theorem cesIndex_demand {γ θ p Z : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ) (hθ1 : θ ≠ 1)
    (hp : 0 < p) (hZ : 0 < Z) :
    cesIndex γ θ (cesDemandT γ θ p Z) (cesDemandN γ θ p Z) = Z / cesPrice γ θ p := by
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hθm : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have hθm' : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ1)
  have h1γ : 0 < 1 - γ := by linarith
  set D := cesDenom γ θ p with hDdef
  have hm : 0 < Z / D := div_pos hZ hD
  set m := Z / D with hmdef
  set ρ := (θ - 1) / θ with hρ
  have hT : γ ^ (1 / θ) * (γ * m) ^ ρ = γ * m ^ ρ := by
    rw [mul_rpow hγ0.le hm.le, ← mul_assoc, ← rpow_add hγ0]
    have : 1 / θ + ρ = 1 := by rw [hρ]; field_simp; ring
    rw [this, rpow_one]
  have hN : (1 - γ) ^ (1 / θ) * ((1 - γ) * p ^ (-θ) * m) ^ ρ
      = (1 - γ) * p ^ (1 - θ) * m ^ ρ := by
    rw [mul_rpow (by positivity) hm.le, mul_rpow h1γ.le (by positivity), ← rpow_mul hp.le,
      ← mul_assoc, ← mul_assoc, ← rpow_add h1γ]
    have e1 : 1 / θ + ρ = 1 := by rw [hρ]; field_simp; ring
    have e2 : -θ * ρ = 1 - θ := by rw [hρ]; field_simp; ring
    rw [e1, e2, rpow_one]
  unfold cesIndex
  rw [cesDemandT_eq, cesDemandN_eq, ← hmdef, hT, hN]
  have hsum : γ * m ^ ρ + (1 - γ) * p ^ (1 - θ) * m ^ ρ = D * m ^ ρ := by
    rw [hDdef, cesDenom]; ring
  rw [hsum, mul_rpow hD.le (by positivity), ← rpow_mul hm.le]
  have e3 : ρ * (θ / (θ - 1)) = 1 := by rw [hρ]; field_simp
  rw [e3, rpow_one, cesPrice_eq_denom_rpow, ← hDdef, div_eq_mul_inv Z, ← rpow_neg hD.le]
  have e4 : D ^ (-(1 / (1 - θ))) = D ^ (θ / (θ - 1)) / D := by
    rw [← rpow_sub_one hD.ne']
    congr 1
    field_simp
    ring
  rw [e4, hmdef]
  field_simp

/-- (22), O&R p. 228: the demands (16) written as `C_T = γ P^θ C` and
`C_N = (1−γ)(p/P)^{−θ} C` with real consumption `C = Z/P`. -/
theorem cesDemand_eq_price_form {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1)
    (hp : 0 < p) (Z : ℝ) :
    cesDemandT γ θ p Z = γ * cesPrice γ θ p ^ θ * (Z / cesPrice γ θ p) ∧
    cesDemandN γ θ p Z = (1 - γ) * (p / cesPrice γ θ p) ^ (-θ) * (Z / cesPrice γ θ p) := by
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  have hP := cesPrice_pos (θ := θ) hγ0 hγ1 hp
  have hθm' : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ1)
  have key : cesPrice γ θ p ^ θ / cesPrice γ θ p = (cesDenom γ θ p)⁻¹ := by
    rw [← rpow_sub_one hP.ne', cesPrice_eq_denom_rpow, ← rpow_mul hD.le, ← rpow_neg_one]
    congr 1
    field_simp
    ring
  constructor
  · rw [cesDemandT_eq]
    calc γ * (Z / cesDenom γ θ p) = γ * (cesPrice γ θ p ^ θ / cesPrice γ θ p) * Z := by
          rw [key]; ring
      _ = _ := by ring
  · rw [cesDemandN_eq, div_rpow hp.le hP.le, rpow_neg hP.le, div_inv_eq_mul]
    calc (1 - γ) * p ^ (-θ) * (Z / cesDenom γ θ p)
        = (1 - γ) * p ^ (-θ) * (cesPrice γ θ p ^ θ / cesPrice γ θ p) * Z := by
          rw [key]; ring
      _ = _ := by ring

/-- Tangent-line (Bernoulli) bound for a concave power, used for the duality in §4.4.1.1
(O&R p. 227): for `0 ≤ ρ ≤ 1`, `x ≥ 0`, `a > 0`, `x^ρ ≤ a^ρ + ρ a^{ρ−1}(x − a)`. -/
theorem ces_rpow_le_tangent {ρ x a : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hx : 0 ≤ x) (ha : 0 < a) :
    x ^ ρ ≤ a ^ ρ + ρ * a ^ (ρ - 1) * (x - a) := by
  have hs : -1 ≤ x / a - 1 := by have := div_nonneg hx ha.le; linarith
  have hb := rpow_one_add_le_one_add_mul_self hs hρ0 hρ1
  rw [add_sub_cancel, div_rpow hx ha.le] at hb
  have haρ := rpow_pos_of_pos ha ρ
  rw [div_le_iff₀ haρ] at hb
  rw [rpow_sub_one ha.ne']
  calc x ^ ρ ≤ (1 + ρ * (x / a - 1)) * a ^ ρ := hb
    _ = a ^ ρ + ρ * (a ^ ρ / a) * (x - a) := by field_simp

/-- Tangent-line (Bernoulli) bound for a convex negative power, used for the duality in §4.4.1.1
(O&R p. 227): for `ρ ≤ 0`, `x, a > 0`, `a^ρ + ρ a^{ρ−1}(x − a) ≤ x^ρ`. -/
theorem ces_tangent_le_rpow {ρ x a : ℝ} (hρ : ρ ≤ 0) (hx : 0 < x) (ha : 0 < a) :
    a ^ ρ + ρ * a ^ (ρ - 1) * (x - a) ≤ x ^ ρ := by
  set y := x / a with hy
  have hy0 : 0 < y := div_pos hx ha
  have hs : -1 ≤ 1 / y - 1 := by have := one_div_pos.mpr hy0; linarith
  have hb := one_add_mul_self_le_rpow_one_add hs (p := 1 - ρ) (by linarith)
  rw [add_sub_cancel, one_div, inv_rpow hy0.le, ← rpow_neg hy0.le, neg_sub] at hb
  -- hb : 1 + (1 - ρ) * (1 / y - 1) ≤ y ^ (ρ - 1)
  have hyρ : y ^ ρ = y * y ^ (ρ - 1) := by
    rw [rpow_sub_one hy0.ne']; field_simp
  have h1 : 1 + ρ * (y - 1) ≤ y ^ ρ := by
    rw [hyρ]
    have := mul_le_mul_of_nonneg_left hb hy0.le
    calc 1 + ρ * (y - 1) = y * (1 + (1 - ρ) * (y⁻¹ - 1)) := by field_simp; ring
      _ ≤ _ := this
  have haρ := rpow_pos_of_pos ha ρ
  have hxy : x ^ ρ = y ^ ρ * a ^ ρ := by
    rw [hy, div_rpow hx.le ha.le]; field_simp
  rw [hxy, rpow_sub_one ha.ne']
  calc a ^ ρ + ρ * (a ^ ρ / a) * (x - a) = (1 + ρ * (y - 1)) * a ^ ρ := by
        rw [hy]; field_simp
    _ ≤ y ^ ρ * a ^ ρ := mul_le_mul_of_nonneg_right h1 haρ.le

/-- First-order conditions behind (15)–(16), O&R p. 222: at the demands (16) the marginal
contributions `γ^{1/θ} C_T^{−1/θ}` and `(1−γ)^{1/θ} C_N^{−1/θ}` to the inner CES sum are in the
price ratio `1 : p` (both equal to `(Z/D)^{−1/θ}` times `1`, resp. `p`). -/
theorem cesDemand_foc {γ θ p Z : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hp : 0 < p) (hZ : 0 < Z) :
    γ ^ (1 / θ) * cesDemandT γ θ p Z ^ ((θ - 1) / θ - 1)
      = (Z / cesDenom γ θ p) ^ ((θ - 1) / θ - 1) ∧
    (1 - γ) ^ (1 / θ) * cesDemandN γ θ p Z ^ ((θ - 1) / θ - 1)
      = p * (Z / cesDenom γ θ p) ^ ((θ - 1) / θ - 1) := by
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  have hm : 0 < Z / cesDenom γ θ p := div_pos hZ hD
  have h1γ : 0 < 1 - γ := by linarith
  have e1 : 1 / θ + ((θ - 1) / θ - 1) = 0 := by field_simp; ring
  have e2 : -θ * ((θ - 1) / θ - 1) = 1 := by field_simp; ring
  constructor
  · rw [cesDemandT_eq, mul_rpow hγ0.le hm.le, ← mul_assoc, ← rpow_add hγ0, e1, rpow_zero,
      one_mul]
  · rw [cesDemandN_eq, mul_rpow (by positivity) hm.le, mul_rpow h1γ.le (by positivity),
      ← rpow_mul hp.le, ← mul_assoc, ← mul_assoc, ← rpow_add h1γ, e1, e2, rpow_zero, rpow_one,
      one_mul]

/-- **Duality (T13)**, O&R §4.4.1.1, pp. 227–228: every bundle `C_T, C_N ≥ 0` costing
`Z = C_T + p C_N > 0` yields at most `Z/P` units of the CES index (13), `P` the price index
(20); equality holds at the demands (16) (`cesIndex_demand`). For `θ < 1` both goods must be
consumed in strictly positive amounts (otherwise Lean's `0 ^ y = 0` is a junk value, see the
module docstring). Proof: tangent-line bounds for `x ↦ x^{(θ−1)/θ}` at the optimum, whose
gradient is proportional to prices (`cesDemand_foc`). -/
theorem cesIndex_le_div_price {γ θ p CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hp : 0 < p) (hCT : 0 ≤ CT) (hCN : 0 ≤ CN)
    (hint : θ < 1 → 0 < CT ∧ 0 < CN) (hZ : 0 < CT + p * CN) :
    cesIndex γ θ CT CN ≤ (CT + p * CN) / cesPrice γ θ p := by
  set Z := CT + p * CN with hZdef
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  have hm : 0 < Z / cesDenom γ θ p := div_pos hZ hD
  have h1γ : 0 < 1 - γ := by linarith
  set xT := cesDemandT γ θ p Z with hxT
  set xN := cesDemandN γ θ p Z with hxN
  have hxT0 : 0 < xT := by rw [hxT, cesDemandT_eq]; positivity
  have hxN0 : 0 < xN := by rw [hxN, cesDemandN_eq]; exact mul_pos (by positivity) hm
  have hbud : xT + p * xN = Z := cesDemand_budget hγ0 hγ1 hp Z
  obtain ⟨hgT, hgN⟩ := cesDemand_foc (θ := θ) hγ0 hγ1 hθ hp hZ
  rw [← hxT] at hgT
  rw [← hxN] at hgN
  set ρ := (θ - 1) / θ with hρ
  set g := (Z / cesDenom γ θ p) ^ (ρ - 1) with hg
  have hval := cesIndex_demand hγ0 hγ1 hθ hθ1 hp hZ
  rw [← hxT, ← hxN] at hval
  unfold cesIndex at hval ⊢
  rw [← hρ] at hval ⊢
  rw [← hval]
  have ha := rpow_pos_of_pos hγ0 (1 / θ)
  have hb := rpow_pos_of_pos h1γ (1 / θ)
  set Astar := γ ^ (1 / θ) * xT ^ ρ + (1 - γ) ^ (1 / θ) * xN ^ ρ with hAstar
  set A := γ ^ (1 / θ) * CT ^ ρ + (1 - γ) ^ (1 / θ) * CN ^ ρ with hA
  have hlin : γ ^ (1 / θ) * (xT ^ ρ + ρ * xT ^ (ρ - 1) * (CT - xT))
      + (1 - γ) ^ (1 / θ) * (xN ^ ρ + ρ * xN ^ (ρ - 1) * (CN - xN)) = Astar := by
    have : γ ^ (1 / θ) * (xT ^ ρ + ρ * xT ^ (ρ - 1) * (CT - xT))
        + (1 - γ) ^ (1 / θ) * (xN ^ ρ + ρ * xN ^ (ρ - 1) * (CN - xN))
        = Astar + ρ * g * ((CT + p * CN) - (xT + p * xN)) := by
      rw [hAstar]
      linear_combination (ρ * (CT - xT)) * hgT + (ρ * (CN - xN)) * hgN
    rw [this, hbud, hZdef, sub_self, mul_zero, add_zero]
  rcases lt_or_gt_of_ne hθ1 with hlt | hgt
  · -- θ < 1: the power `ρ` is negative and the outer exponent is negative
    obtain ⟨hCT', hCN'⟩ := hint hlt
    have hρneg : ρ ≤ 0 := by rw [hρ]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hθ.le
    have t1 := ces_tangent_le_rpow hρneg hCT' hxT0
    have t2 := ces_tangent_le_rpow hρneg hCN' hxN0
    have key : Astar ≤ A := by
      rw [← hlin, hA]
      exact add_le_add (mul_le_mul_of_nonneg_left t1 ha.le) (mul_le_mul_of_nonneg_left t2 hb.le)
    have hApos : 0 < Astar := by rw [hAstar]; positivity
    exact rpow_le_rpow_of_nonpos hApos key
      (div_nonpos_of_nonneg_of_nonpos hθ.le (by linarith))
  · -- θ > 1: the power `ρ` lies in `(0, 1)` and the outer exponent is positive
    have hρ0 : 0 ≤ ρ := by rw [hρ]; exact div_nonneg (by linarith) hθ.le
    have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one hθ]; linarith
    have t1 := ces_rpow_le_tangent hρ0 hρ1 hCT hxT0
    have t2 := ces_rpow_le_tangent hρ0 hρ1 hCN hxN0
    have key : A ≤ Astar := by
      rw [← hlin, hA]
      exact add_le_add (mul_le_mul_of_nonneg_left t1 ha.le) (mul_le_mul_of_nonneg_left t2 hb.le)
    have hA0 : 0 ≤ A := by rw [hA]; positivity
    exact rpow_le_rpow hA0 key (div_nonneg hθ.le (by linarith))

/-- The price index is the minimum cost of one unit of real consumption, the definition of
O&R p. 227: any interior bundle with `Ω(C_T, C_N) = 1` costs at least `P`, and the demands (16)
at spending `Z = P` deliver `Ω = 1` at cost exactly `P`. -/
theorem cesPrice_isLeast_cost {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hp : 0 < p) :
    (∀ CT CN : ℝ, 0 < CT → 0 < CN → cesIndex γ θ CT CN = 1 → cesPrice γ θ p ≤ CT + p * CN) ∧
    cesIndex γ θ (cesDemandT γ θ p (cesPrice γ θ p)) (cesDemandN γ θ p (cesPrice γ θ p)) = 1 ∧
    cesDemandT γ θ p (cesPrice γ θ p) + p * cesDemandN γ θ p (cesPrice γ θ p)
      = cesPrice γ θ p := by
  have hP := cesPrice_pos (θ := θ) hγ0 hγ1 hp
  refine ⟨fun CT CN hCT hCN h1 => ?_, ?_, cesDemand_budget hγ0 hγ1 hp _⟩
  · have hZ : 0 < CT + p * CN := by positivity
    have := cesIndex_le_div_price hγ0 hγ1 hθ hθ1 hp hCT.le hCN.le (fun _ => ⟨hCT, hCN⟩) hZ
    rw [h1, le_div_iff₀ hP, one_mul] at this
    exact this
  · rw [cesIndex_demand hγ0 hγ1 hθ hθ1 hp hP, div_self hP.ne']

/-- "Of course, `P` is an increasing function of `p`", O&R p. 227: the CES price index (20) is
strictly increasing in the relative price of nontradables on `p > 0`, for every `θ ≠ 1`. -/
theorem cesPrice_strictMonoOn {γ θ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1) :
    StrictMonoOn (cesPrice γ θ) (Ioi 0) := by
  intro a ha b hb hab
  simp only [mem_Ioi] at ha hb
  have h1γ : 0 < 1 - γ := by linarith
  rw [cesPrice_eq_denom_rpow, cesPrice_eq_denom_rpow]
  have hDa := cesDenom_pos (θ := θ) hγ0 hγ1 ha
  have hDb := cesDenom_pos (θ := θ) hγ0 hγ1 hb
  rcases lt_or_gt_of_ne hθ1 with hlt | hgt
  · have hpow : a ^ (1 - θ) < b ^ (1 - θ) := rpow_lt_rpow ha.le hab (by linarith)
    have hD : cesDenom γ θ a < cesDenom γ θ b := by
      unfold cesDenom; nlinarith
    exact rpow_lt_rpow hDa.le hD (by apply one_div_pos.mpr; linarith)
  · have hpow : b ^ (1 - θ) < a ^ (1 - θ) := rpow_lt_rpow_of_neg ha hab (by linarith)
    have hD : cesDenom γ θ b < cesDenom γ θ a := by
      unfold cesDenom; nlinarith
    exact rpow_lt_rpow_of_neg hDb hD (by apply one_div_neg.mpr; linarith)

/-- Footnote 26, O&R p. 228: starting from `p = 1`, (20) implies `P̂ = (1−γ) p̂` for every
`θ ≠ 1`, stated exactly as `d log P / dp = 1 − γ` at `p = 1` (where `p̂ = dp/p = dp`). -/
theorem cesPrice_logDeriv_at_one {γ θ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1) :
    HasDerivAt (fun p => Real.log (cesPrice γ θ p)) (1 - γ) 1 := by
  have hθm' : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ1)
  have hin : HasDerivAt (fun p : ℝ => γ + (1 - γ) * p ^ (1 - θ))
      ((1 - γ) * ((1 - θ) * (1 : ℝ) ^ (1 - θ - 1))) 1 :=
    ((hasDerivAt_rpow_const (Or.inl one_ne_zero)).const_mul (1 - γ)).const_add γ
  have hlog := (hin.log (by simp)).const_mul (1 / (1 - θ))
  have hev : (fun p => Real.log (cesPrice γ θ p))
      =ᶠ[𝓝 1] fun p => 1 / (1 - θ) * Real.log (γ + (1 - γ) * p ^ (1 - θ)) := by
    filter_upwards [Ioi_mem_nhds one_pos] with p hp
    have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
    unfold cesDenom at hD
    rw [cesPrice, Real.log_rpow hD]
  refine (hlog.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [one_rpow, mul_one]
  field_simp
  ring

/-- Power-mean limit behind footnotes 22 and 26, O&R pp. 222–228: for weights `w, 1 − w > 0` and
`a, b > 0`, `(w a^ρ + (1−w) b^ρ)^{1/ρ} → a^w b^{1−w}` as `ρ → 0`. -/
theorem ces_powerMean_tendsto {w a b : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (ha : 0 < a)
    (hb : 0 < b) :
    Tendsto (fun ρ : ℝ => (w * a ^ ρ + (1 - w) * b ^ ρ) ^ (1 / ρ)) (𝓝[≠] 0)
      (𝓝 (a ^ w * b ^ (1 - w))) := by
  have h1w : 0 < 1 - w := by linarith
  set f : ℝ → ℝ := fun ρ => Real.log (w * a ^ ρ + (1 - w) * b ^ ρ) with hf
  have hin : HasDerivAt (fun ρ : ℝ => w * a ^ ρ + (1 - w) * b ^ ρ)
      (w * (a ^ (0 : ℝ) * Real.log a) + (1 - w) * (b ^ (0 : ℝ) * Real.log b)) 0 :=
    ((hasStrictDerivAt_const_rpow ha 0).hasDerivAt.const_mul w).add
      ((hasStrictDerivAt_const_rpow hb 0).hasDerivAt.const_mul (1 - w))
  have hder := hin.log (by simp)
  simp only [rpow_zero, one_mul, mul_one, add_sub_cancel, div_one] at hder
  have hslope := (Real.continuous_exp.tendsto _).comp (hasDerivAt_iff_tendsto_slope.mp hder)
  have hlim : Real.exp (w * Real.log a + (1 - w) * Real.log b) = a ^ w * b ^ (1 - w) := by
    rw [rpow_def_of_pos ha, rpow_def_of_pos hb, ← Real.exp_add]; ring_nf
  rw [hlim] at hslope
  refine hslope.congr' ?_
  filter_upwards with ρ
  have hpos : 0 < w * a ^ ρ + (1 - w) * b ^ ρ := by positivity
  rw [Function.comp_apply, slope_def_field, rpow_def_of_pos hpos]
  simp only [rpow_zero, mul_one, add_sub_cancel, Real.log_one, sub_zero]
  ring_nf

/-- `θ ↦ 1 − θ` maps a punctured neighbourhood of `1` into one of `0` (for the `θ → 1` limit of
the price index (20), O&R p. 228). -/
theorem ces_tendsto_one_sub_punctured :
    Tendsto (fun θ : ℝ => 1 - θ) (𝓝[≠] 1) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have : Tendsto (fun θ : ℝ => 1 - θ) (𝓝 1) (𝓝 (1 - 1)) :=
      tendsto_const_nhds.sub tendsto_id
    rw [sub_self] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact sub_ne_zero.mpr (Ne.symm hθ)

/-- Cobb–Douglas limit of the price index, O&R p. 228 (and fn 26): as `θ → 1`,
`P = [γ + (1−γ)p^{1−θ}]^{1/(1−θ)} → p^{1−γ}`. -/
theorem cesPrice_tendsto_cobbDouglas {γ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p) :
    Tendsto (fun θ => cesPrice γ θ p) (𝓝[≠] 1) (𝓝 (p ^ (1 - γ))) := by
  have h := (ces_powerMean_tendsto hγ0 hγ1 one_pos hp).comp ces_tendsto_one_sub_punctured
  rw [one_rpow, one_mul] at h
  refine h.congr' ?_
  filter_upwards with θ
  simp [cesPrice]

/-- The Cobb–Douglas limit of (20) is the `CobbDouglasIndex` price of `RealExchangeRate.Model`
with the traded good as numeraire, which justifies the Cobb–Douglas index used in §4.2.3
(O&R p. 228). -/
theorem cesPrice_tendsto_model (c : CobbDouglasIndex) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun θ => cesPrice c.γ θ p) (𝓝[≠] 1) (𝓝 (c.price 1 p)) := by
  rw [CobbDouglasIndex.price_numeraire]
  exact cesPrice_tendsto_cobbDouglas c.γ_pos c.γ_lt_one hp

/-- Footnote 22, O&R pp. 222–223: as `θ → 1` the CES index (13) converges to the Cobb–Douglas
function `C_T^γ C_N^{1−γ} / (γ^γ (1−γ)^{1−γ})` (for `C_T, C_N > 0`). -/
theorem cesIndex_tendsto_cobbDouglas {γ CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hCT : 0 < CT)
    (hCN : 0 < CN) :
    Tendsto (fun θ => cesIndex γ θ CT CN) (𝓝[≠] 1)
      (𝓝 (CT ^ γ * CN ^ (1 - γ) / (γ ^ γ * (1 - γ) ^ (1 - γ)))) := by
  have h1γ : 0 < 1 - γ := by linarith
  have hρ : Tendsto (fun θ : ℝ => (θ - 1) / θ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun θ : ℝ => (θ - 1) / θ) (𝓝 1) (𝓝 ((1 - 1) / 1)) :=
        (tendsto_id.sub tendsto_const_nhds).div tendsto_id one_ne_zero
      rw [sub_self, zero_div] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with θ hθ hθ0
      exact div_ne_zero (sub_ne_zero.mpr hθ) (ne_of_gt hθ0)
  have h := (ces_powerMean_tendsto hγ0 hγ1 (div_pos hCT hγ0) (div_pos hCN h1γ)).comp hρ
  have hval : (CT / γ) ^ γ * (CN / (1 - γ)) ^ (1 - γ)
      = CT ^ γ * CN ^ (1 - γ) / (γ ^ γ * (1 - γ) ^ (1 - γ)) := by
    rw [div_rpow hCT.le hγ0.le, div_rpow hCN.le h1γ.le]; field_simp
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with θ hθ0
  have hθ0' : θ ≠ 0 := ne_of_gt hθ0
  simp only [Function.comp_apply, cesIndex]
  have e1 : 1 / θ = 1 - (θ - 1) / θ := by field_simp; ring
  have eT : γ * (CT / γ) ^ ((θ - 1) / θ) = γ ^ (1 / θ) * CT ^ ((θ - 1) / θ) := by
    rw [e1, rpow_sub hγ0, rpow_one, div_rpow hCT.le hγ0.le]
    have := rpow_pos_of_pos hγ0 ((θ - 1) / θ)
    field_simp
  have eN : (1 - γ) * (CN / (1 - γ)) ^ ((θ - 1) / θ)
      = (1 - γ) ^ (1 / θ) * CN ^ ((θ - 1) / θ) := by
    rw [e1, rpow_sub h1γ, rpow_one, div_rpow hCN.le h1γ.le]
    have := rpow_pos_of_pos h1γ ((θ - 1) / θ)
    field_simp
  rw [eT, eN, one_div_div]

/-- Footnote 22, O&R p. 222: `θ` is the elasticity of substitution,
`d log(C_T/C_N) / d log p = θ`, along the demands (16) (for any spending level `Z ≠ 0`), stated
exactly with `p = e^x`. -/
theorem cesDemand_elasticity {γ θ Z : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hZ : Z ≠ 0) (x : ℝ) :
    HasDerivAt
      (fun x => Real.log (cesDemandT γ θ (Real.exp x) Z / cesDemandN γ θ (Real.exp x) Z)) θ x := by
  have h1γ : 0 < 1 - γ := by linarith
  have hfun : (fun x => Real.log (cesDemandT γ θ (Real.exp x) Z / cesDemandN γ θ (Real.exp x) Z))
      = fun x => Real.log γ - Real.log (1 - γ) + θ * x := by
    funext x
    have hD := (cesDenom_pos (θ := θ) hγ0 hγ1 (Real.exp_pos x)).ne'
    have hq := rpow_pos_of_pos (Real.exp_pos x) (-θ)
    have hratio : cesDemandT γ θ (Real.exp x) Z / cesDemandN γ θ (Real.exp x) Z
        = γ / ((1 - γ) * Real.exp x ^ (-θ)) := by
      unfold cesDemandT cesDemandN
      field_simp
    rw [hratio, Real.log_div hγ0.ne' (by positivity), Real.log_mul h1γ.ne' hq.ne',
      Real.log_rpow (Real.exp_pos x), Real.log_exp]
    ring
  rw [hfun]
  have := ((hasDerivAt_id x).const_mul θ).const_add (Real.log γ - Real.log (1 - γ))
  simpa using this

/-- Footnote 13, O&R p. 217: with `u(C_T, C_N) = G(C_T^γ C_N^{1−γ})`, `G` differentiable with
`G' ≠ 0`, the marginal rate of substitution is `(∂u/∂C_N)/(∂u/∂C_T) = ((1−γ)/γ)(C_T/C_N)`,
which depends only on the consumption ratio (homotheticity). -/
theorem cobbDouglas_mrs {γ CT CN g : ℝ} {G : ℝ → ℝ} (hCT : 0 < CT) (hCN : 0 < CN)
    (hG : HasDerivAt G g (CT ^ γ * CN ^ (1 - γ))) (hg : g ≠ 0) (hγ : γ ≠ 0) :
    ∃ uN uT : ℝ, HasDerivAt (fun c => G (CT ^ γ * c ^ (1 - γ))) uN CN ∧
      HasDerivAt (fun c => G (c ^ γ * CN ^ (1 - γ))) uT CT ∧
      uN / uT = (1 - γ) / γ * (CT / CN) := by
  have hN : HasDerivAt (fun c : ℝ => CT ^ γ * c ^ (1 - γ))
      (CT ^ γ * ((1 - γ) * CN ^ (1 - γ - 1))) CN :=
    (hasDerivAt_rpow_const (Or.inl hCN.ne')).const_mul _
  have hT : HasDerivAt (fun c : ℝ => c ^ γ * CN ^ (1 - γ))
      (γ * CT ^ (γ - 1) * CN ^ (1 - γ)) CT :=
    (hasDerivAt_rpow_const (Or.inl hCT.ne')).mul_const _
  refine ⟨_, _, hG.comp CN hN, hG.comp CT hT, ?_⟩
  rw [rpow_sub_one hCN.ne', rpow_sub_one hCT.ne']
  have := rpow_pos_of_pos hCT γ
  have := rpow_pos_of_pos hCN (1 - γ)
  field_simp

/-- Exercise 8(a), O&R p. 267: with `C = X^γ M^{1−γ}`, `X` the export good priced at `p` in
terms of imports, the consumption-based price index in import units is
`P = p^γ / (γ^γ (1−γ)^{1−γ})`: every bundle with `C = 1` costs at least `P`, and
`X = γP/p`, `M = (1−γ)P` gives `C = 1` at cost exactly `P`. (The exponent `γ` sits on the
export price because the export good carries the weight `γ`.) -/
theorem cobbDouglas_price_exercise8a {γ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p) :
    (∀ X M : ℝ, 0 < X → 0 < M → X ^ γ * M ^ (1 - γ) = 1 →
      p ^ γ / (γ ^ γ * (1 - γ) ^ (1 - γ)) ≤ p * X + M) ∧
    (γ * (p ^ γ / (γ ^ γ * (1 - γ) ^ (1 - γ))) / p) ^ γ
        * ((1 - γ) * (p ^ γ / (γ ^ γ * (1 - γ) ^ (1 - γ)))) ^ (1 - γ) = 1 ∧
    p * (γ * (p ^ γ / (γ ^ γ * (1 - γ) ^ (1 - γ))) / p)
        + (1 - γ) * (p ^ γ / (γ ^ γ * (1 - γ) ^ (1 - γ)))
      = p ^ γ / (γ ^ γ * (1 - γ) ^ (1 - γ)) := by
  have h1γ : 0 < 1 - γ := by linarith
  have hgγ := rpow_pos_of_pos hγ0 γ
  have hg1 := rpow_pos_of_pos h1γ (1 - γ)
  have hpγ := rpow_pos_of_pos hp γ
  refine ⟨fun X M hX hM hC => ?_, ?_, by field_simp; ring⟩
  · have ham := geom_mean_le_arith_mean2_weighted hγ0.le h1γ.le
      (div_pos (mul_pos hp hX) hγ0).le (div_pos hM h1γ).le (by ring : γ + (1 - γ) = 1)
    rw [div_rpow (mul_pos hp hX).le hγ0.le, mul_rpow hp.le hX.le,
      div_rpow hM.le h1γ.le] at ham
    have e : p ^ γ * X ^ γ / γ ^ γ * (M ^ (1 - γ) / (1 - γ) ^ (1 - γ))
        = p ^ γ / (γ ^ γ * (1 - γ) ^ (1 - γ)) * (X ^ γ * M ^ (1 - γ)) := by
      field_simp
    rw [e, hC, mul_one] at ham
    calc _ ≤ γ * (p * X / γ) + (1 - γ) * (M / (1 - γ)) := ham
      _ = p * X + M := by field_simp
  · set P := p ^ γ / (γ ^ γ * (1 - γ) ^ (1 - γ)) with hP
    have hP0 : 0 < P := by positivity
    rw [mul_div_right_comm, mul_rpow (div_pos hγ0 hp).le hP0.le, mul_rpow h1γ.le hP0.le,
      div_rpow hγ0.le hp.le]
    have e : γ ^ γ / p ^ γ * P ^ γ * ((1 - γ) ^ (1 - γ) * P ^ (1 - γ))
        = γ ^ γ * (1 - γ) ^ (1 - γ) / p ^ γ * (P ^ γ * P ^ (1 - γ)) := by ring
    rw [e, ← rpow_add hP0, add_sub_cancel, rpow_one, hP]
    field_simp

end ObstfeldRogoff.RealExchangeRate.CESIndex

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Consumption dynamics, the price level and the consumption-based real interest rate

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.4
(pp. 225–235, eqs. (24)–(36), footnote 30) and Exercises 3 and 4 (p. 265).

Time is indexed relative to the planning date: index `s` stands for date `t + s`, so `P 0` is
`P_t`. The world interest rate `r` on tradables is constant, `1 + r > 0`, and
`d = (1+r)⁻¹` is the tradables discount factor. We prove:

* the consumption-based real rate (25), `1 + r^C_{s+1} = (1+r)P_s/P_{s+1}`, the Euler
  equation (26), and the telescoping formula `R^C_{t,s} = P_s/((1+r)^{s−t} P_t)`;
* the real-consumption budget (27) from (24), with explicit summability;
* the isoelastic consumption function (28) and its price-level form (29), and the p. 232 claim
  that future prices `P_s` have no wealth effect;
* the national budget (30), deriving footnote 30's capital-value formula from
  `K_{s+1} = K_s + I_s` and an **explicit transversality condition** `(1+r)^{−T} K_T → 0`,
  and the tradables-only budget (32);
* the Euler equations (33), (34), the tradables consumption function (35), the current account
  (36), and the p. 235 claim that a rising price index with `σ > θ` raises initial tradables
  consumption above its constant-`P` level (and lowers it when `σ < θ`);
* Exercise 3 (the real-consumption versions of the budget, the consumption function and the
  current account) and Exercise 4 (a) and (b).

Present values carry explicit `Summable` hypotheses; nothing relies on the junk value of `tsum`.
-/

namespace ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics

open Real Filter Topology Finset
open ObstfeldRogoff.RealExchangeRate.CESIndex

/-- The gross consumption-based real interest rate (25), O&R p. 230:
`1 + r^C_{s+1} = (1+r) P_s / P_{s+1}`. -/
noncomputable def grossRealRate (r : ℝ) (P : ℕ → ℝ) (s : ℕ) : ℝ := (1 + r) * P s / P (s + 1)

/-- The market discount factor for real consumption, O&R p. 231:
`R^C_{t,t+n} = ∏_{v=t+1}^{t+n} (1 + r^C_v)⁻¹`, with `R^C_{t,t} = 1`. -/
noncomputable def realDiscount (r : ℝ) (P : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ v ∈ Finset.range n, (grossRealRate r P v)⁻¹

/-- `R^C_{t,t} = 1`, O&R p. 231. -/
theorem realDiscount_zero (r : ℝ) (P : ℕ → ℝ) : realDiscount r P 0 = 1 := by
  simp [realDiscount]

/-- The consumption-based real rate is positive for positive prices and `1 + r > 0`,
O&R (25), p. 230. -/
theorem grossRealRate_pos {r : ℝ} {P : ℕ → ℝ} (hr : 0 < 1 + r) (hP : ∀ s, 0 < P s) (s : ℕ) :
    0 < grossRealRate r P s := by
  unfold grossRealRate
  have := hP s; have := hP (s + 1); positivity

/-- Telescoping of the real discount factor, O&R p. 230:
`R^C_{t,t+n} = P_{t+n} / ((1+r)^n P_t)`. -/
theorem realDiscount_eq {r : ℝ} {P : ℕ → ℝ} (hr : 1 + r ≠ 0) (hP : ∀ s, P s ≠ 0) (n : ℕ) :
    realDiscount r P n = ((1 + r)⁻¹) ^ n * (P n / P 0) := by
  induction n with
  | zero => simp [realDiscount, hP 0]
  | succ n ih =>
    unfold realDiscount at ih ⊢
    rw [prod_range_succ, ih, grossRealRate]
    have := hP n; have := hP (n + 1); have := hP 0
    field_simp
    linear_combination (-(1 + r)⁻¹ ^ n) * (mul_inv_cancel₀ hr)

/-- The real discount factor is positive, O&R p. 231. -/
theorem realDiscount_pos {r : ℝ} {P : ℕ → ℝ} (hr : 0 < 1 + r) (hP : ∀ s, 0 < P s) (n : ℕ) :
    0 < realDiscount r P n :=
  prod_pos fun v _ => inv_pos.mpr (grossRealRate_pos hr hP v)

/-- The Euler equation (26), O&R p. 230: `u′(C_s)/P_s = (1+r)β u′(C_{s+1})/P_{s+1}` is
equivalent to `u′(C_s) = (1 + r^C_{s+1}) β u′(C_{s+1})`. -/
theorem euler_real_rate {r β u0 u1 : ℝ} {P : ℕ → ℝ} {s : ℕ} (hP0 : P s ≠ 0)
    (hP1 : P (s + 1) ≠ 0) :
    u0 / P s = (1 + r) * β * (u1 / P (s + 1)) ↔ u0 = grossRealRate r P s * β * u1 := by
  unfold grossRealRate
  constructor
  · intro h
    rw [div_eq_iff hP0] at h
    rw [h]; field_simp
  · intro h
    rw [h]; field_simp

/-- The real-consumption budget (27) from (24), O&R pp. 229–231: if
`∑ (1+r)^{−s} P_s C_s = (1+r)Q_t + ∑ (1+r)^{−s} Y_s` (with `Y_s = w_s L_s − G_s` and both series
summable), then the real series are summable and
`∑ R^C_{t,s} C_s = (1+r)Q_t/P_t + ∑ R^C_{t,s} Y_s/P_s`. -/
theorem real_budget {r Q : ℝ} {P C Y : ℕ → ℝ} (hr : 0 < 1 + r) (hP : ∀ s, 0 < P s)
    (hC : Summable fun s => ((1 + r)⁻¹) ^ s * (P s * C s))
    (hY : Summable fun s => ((1 + r)⁻¹) ^ s * Y s)
    (h24 : ∑' s, ((1 + r)⁻¹) ^ s * (P s * C s) = (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * Y s) :
    Summable (fun s => realDiscount r P s * C s) ∧
    Summable (fun s => realDiscount r P s * (Y s / P s)) ∧
    ∑' s, realDiscount r P s * C s
      = (1 + r) * Q / P 0 + ∑' s, realDiscount r P s * (Y s / P s) := by
  have hP' : ∀ s, P s ≠ 0 := fun s => (hP s).ne'
  have eC : (fun s => realDiscount r P s * C s)
      = fun s => (P 0)⁻¹ * (((1 + r)⁻¹) ^ s * (P s * C s)) := by
    funext s; rw [realDiscount_eq hr.ne' hP']; field_simp
  have eY : (fun s => realDiscount r P s * (Y s / P s))
      = fun s => (P 0)⁻¹ * (((1 + r)⁻¹) ^ s * Y s) := by
    funext s; rw [realDiscount_eq hr.ne' hP']; have := hP' s; field_simp
  refine ⟨eC ▸ hC.mul_left _, eY ▸ hY.mul_left _, ?_⟩
  rw [eC, eY, tsum_mul_left, tsum_mul_left, h24]
  field_simp

/-- Iterating the isoelastic Euler equation (33), O&R p. 231 (as in §2.2.2):
`C_s = (R^C_{t,s})^{−σ} β^{σ(s−t)} C_t`. -/
theorem consumption_path_of_euler {r σ β : ℝ} {P C : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s)
    (hE : ∀ s, C (s + 1) = grossRealRate r P s ^ σ * β ^ σ * C s) (n : ℕ) :
    C n = realDiscount r P n ^ (-σ) * (β ^ σ) ^ n * C 0 := by
  induction n with
  | zero => simp [realDiscount_zero]
  | succ n ih =>
    have hg := grossRealRate_pos hr hP n
    have hR := realDiscount_pos hr hP n
    have hstep : realDiscount r P (n + 1) = realDiscount r P n * (grossRealRate r P n)⁻¹ := by
      unfold realDiscount; rw [prod_range_succ]
    rw [hE n, ih, hstep, mul_rpow hR.le (inv_pos.mpr hg).le, inv_rpow hg.le, rpow_neg hg.le,
      inv_inv, pow_succ]
    ring

/-- The isoelastic consumption function (28), O&R p. 231, for any real wealth `W` on the
right of the budget: if `C_s = (R^C_{t,s})^{−σ} β^{σ(s−t)} C_t` and `∑ R^C_{t,s} C_s = W`, with
`∑ (R^C_{t,s})^{1−σ} β^{σ(s−t)}` summable, then `C_t = W / ∑ (R^C_{t,s})^{1−σ} β^{σ(s−t)}`. -/
theorem consumption_of_budget {r σ β W : ℝ} {P C : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hβ : 0 < β)
    (hpath : ∀ n, C n = realDiscount r P n ^ (-σ) * (β ^ σ) ^ n * C 0)
    (hsum : Summable fun n => realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n)
    (hW : ∑' n, realDiscount r P n * C n = W) :
    C 0 = W / ∑' n, realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n := by
  have hterm : ∀ n, realDiscount r P n * C n
      = realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n * C 0 := by
    intro n
    have hR := realDiscount_pos hr hP n
    rw [hpath n, sub_eq_add_neg, rpow_add hR, rpow_one]
    ring
  have hden : 0 < ∑' n, realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n := by
    refine hsum.tsum_pos (fun n => ?_) 0 ?_
    · have := realDiscount_pos hr hP n; positivity
    · have := realDiscount_pos hr hP 0; positivity
  rw [← hW, tsum_congr hterm, tsum_mul_right]
  field_simp

/-- The consumption function (28), O&R p. 231: combining (24) with the isoelastic Euler
equation (33), `C_t = [(1+r)Q_t/P_t + ∑ R^C_{t,s}(w_sL_s − G_s)/P_s] /
∑ (R^C_{t,s})^{1−σ} β^{σ(s−t)}`. -/
theorem consumption_function {r σ β Q : ℝ} {P C Y : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hβ : 0 < β)
    (hE : ∀ s, C (s + 1) = grossRealRate r P s ^ σ * β ^ σ * C s)
    (hC : Summable fun s => ((1 + r)⁻¹) ^ s * (P s * C s))
    (hY : Summable fun s => ((1 + r)⁻¹) ^ s * Y s)
    (hsum : Summable fun n => realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n)
    (h24 : ∑' s, ((1 + r)⁻¹) ^ s * (P s * C s) = (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * Y s) :
    C 0 = ((1 + r) * Q / P 0 + ∑' s, realDiscount r P s * (Y s / P s))
      / ∑' n, realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n :=
  consumption_of_budget hr hP hβ (consumption_path_of_euler hr hP hE) hsum
    (real_budget hr hP hC hY h24).2.2

/-- The consumption function in price-level form (29), O&R p. 232:
`C_t = [(1+r)Q_t + ∑ (1+r)^{−(s−t)}(w_sL_s − G_s)] /
(P_t ∑ [(1+r)^{s−t} P_t/P_s]^{σ−1} β^{σ(s−t)})`. -/
theorem consumption_function_price_form {r σ β Q : ℝ} {P C Y : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hβ : 0 < β)
    (hE : ∀ s, C (s + 1) = grossRealRate r P s ^ σ * β ^ σ * C s)
    (hC : Summable fun s => ((1 + r)⁻¹) ^ s * (P s * C s))
    (hY : Summable fun s => ((1 + r)⁻¹) ^ s * Y s)
    (hsum : Summable fun n => ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n)
    (h24 : ∑' s, ((1 + r)⁻¹) ^ s * (P s * C s) = (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * Y s) :
    C 0 = ((1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * Y s)
      / (P 0 * ∑' n, ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n) := by
  have hP' : ∀ s, P s ≠ 0 := fun s => (hP s).ne'
  have eR : ∀ n, realDiscount r P n ^ (1 - σ) = ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) := by
    intro n
    have hx : 0 < (1 + r) ^ n * (P 0 / P n) := by have := hP n; have := hP 0; positivity
    have e : realDiscount r P n = ((1 + r) ^ n * (P 0 / P n))⁻¹ := by
      rw [realDiscount_eq hr.ne' hP', inv_pow]; have := hP' n; have := hP' 0; field_simp
    rw [e, inv_rpow hx.le, ← rpow_neg hx.le, neg_sub]
  have hsum' : Summable fun n => realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n := by
    simp_rw [eR]; exact hsum
  have h := consumption_function hr hP hβ hE hC hY hsum' h24
  simp_rw [eR] at h
  have eY : (fun s => realDiscount r P s * (Y s / P s))
      = fun s => (P 0)⁻¹ * (((1 + r)⁻¹) ^ s * Y s) := by
    funext s; rw [realDiscount_eq hr.ne' hP']; have := hP' s; field_simp
  rw [h, eY, tsum_mul_left]
  have := hP 0
  field_simp

/-- No wealth effect of future price levels, O&R p. 232: the real wealth in the numerator of
(28), `(1+r)Q_t/P_t + ∑ R^C_{t,s} Y_s/P_s`, depends on the price path only through `P_t`. -/
theorem real_wealth_independent_of_future_prices {r Q : ℝ} {P P' Y : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hP' : ∀ s, 0 < P' s) (h0 : P 0 = P' 0) :
    (1 + r) * Q / P 0 + ∑' s, realDiscount r P s * (Y s / P s)
      = (1 + r) * Q / P' 0 + ∑' s, realDiscount r P' s * (Y s / P' s) := by
  have e : ∀ (P : ℕ → ℝ), (∀ s, 0 < P s) → (fun s => realDiscount r P s * (Y s / P s))
      = fun s => (P 0)⁻¹ * (((1 + r)⁻¹) ^ s * Y s) := by
    intro P hP
    funext s
    rw [realDiscount_eq hr.ne' (fun s => (hP s).ne')]
    have := (hP s).ne'; have := (hP 0).ne'
    field_simp
  rw [e P hP, e P' hP', h0]

/-- Footnote 30, O&R pp. 232–233: with `K_{s+1} = K_s + I_s`, the finite-horizon value of
capital telescopes, `∑_{s<T} (1+r)^{−(s+1)}(rK_s − I_s) = K_t − (1+r)^{−T} K_{t+T}`. -/
theorem capital_partial_sum {r : ℝ} {K I : ℕ → ℝ} (hr : 1 + r ≠ 0)
    (hK : ∀ s, K (s + 1) = K s + I s) (T : ℕ) :
    ∑ s ∈ range T, ((1 + r)⁻¹) ^ (s + 1) * (r * K s - I s)
      = K 0 - ((1 + r)⁻¹) ^ T * K T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, ih, show I T = K (T + 1) - K T by rw [hK T]; ring, pow_succ]
    linear_combination (((1 + r)⁻¹) ^ T * K T) * (inv_mul_cancel₀ hr)

/-- Footnote 30, O&R pp. 232–233: the capital stock equals the present value of future capital
income less investment, `K_t = ∑_{s≥t} (1+r)^{−(s−t+1)}(rK_s − I_s)`. The book leaves implicit
the **transversality condition** `(1+r)^{−T} K_T → 0`, which is assumed here, together with
summability of the series. -/
theorem capital_eq_present_value {r : ℝ} {K I : ℕ → ℝ} (hr : 1 + r ≠ 0)
    (hK : ∀ s, K (s + 1) = K s + I s)
    (hTV : Tendsto (fun T => ((1 + r)⁻¹) ^ T * K T) atTop (𝓝 0))
    (hS : Summable fun s => ((1 + r)⁻¹) ^ (s + 1) * (r * K s - I s)) :
    ∑' s, ((1 + r)⁻¹) ^ (s + 1) * (r * K s - I s) = K 0 := by
  refine (hS.hasSum_iff_tendsto_nat.mpr ?_).tsum_eq
  have h : Tendsto (fun T => K 0 - ((1 + r)⁻¹) ^ T * K T) atTop (𝓝 (K 0 - 0)) :=
    tendsto_const_nhds.sub hTV
  rw [sub_zero] at h
  exact h.congr fun T => (capital_partial_sum hr hK T).symm

/-- The national budget constraint (30), O&R p. 233: from (24) with `Q_t = B_t + K_t`, the
zero-profit identity `Y_T + pY_N = rK + wL`, `K_{s+1} = K_s + I_s` and transversality,
`∑ (1+r)^{−(s−t)} P_s C_s = (1+r)B_t + ∑ (1+r)^{−(s−t)}(Y_T + pY_N − I − G)`. -/
theorem national_budget {r B0 : ℝ} {PC w L G YT p YN K I : ℕ → ℝ} (hr : 1 + r ≠ 0)
    (hK : ∀ s, K (s + 1) = K s + I s)
    (hTV : Tendsto (fun T => ((1 + r)⁻¹) ^ T * K T) atTop (𝓝 0))
    (hS : Summable fun s => ((1 + r)⁻¹) ^ (s + 1) * (r * K s - I s))
    (hY : Summable fun s => ((1 + r)⁻¹) ^ s * (w s * L s - G s))
    (hGDP : ∀ s, YT s + p s * YN s = r * K s + w s * L s)
    (h24 : ∑' s, ((1 + r)⁻¹) ^ s * PC s
      = (1 + r) * (B0 + K 0) + ∑' s, ((1 + r)⁻¹) ^ s * (w s * L s - G s)) :
    Summable (fun s => ((1 + r)⁻¹) ^ s * (YT s + p s * YN s - I s - G s)) ∧
    ∑' s, ((1 + r)⁻¹) ^ s * PC s
      = (1 + r) * B0 + ∑' s, ((1 + r)⁻¹) ^ s * (YT s + p s * YN s - I s - G s) := by
  have e : (fun s => ((1 + r)⁻¹) ^ s * (YT s + p s * YN s - I s - G s))
      = fun s => (1 + r) * (((1 + r)⁻¹) ^ (s + 1) * (r * K s - I s))
          + ((1 + r)⁻¹) ^ s * (w s * L s - G s) := by
    funext s
    rw [pow_succ]
    linear_combination (((1 + r)⁻¹) ^ s) * hGDP s
      + (-(((1 + r)⁻¹) ^ s * (r * K s - I s))) * (mul_inv_cancel₀ hr)
  refine ⟨e ▸ (hS.mul_left _).add hY, ?_⟩
  rw [e, (hS.mul_left _).tsum_add hY, tsum_mul_left, capital_eq_present_value hr hK hTV hS, h24]
  ring

/-- The tradables-only intertemporal budget (32), O&R p. 233: with `PC = C_T + pC_N`
((14), (21)), nontradables market clearing (31) `C_N + G_N = Y_N` and `G = G_T + pG_N`, the
national budget (30) becomes `∑ (1+r)^{−(s−t)}(C_T + I + G_T) = (1+r)B_t + ∑ (1+r)^{−(s−t)} Y_T`.
-/
theorem tradables_budget {r B0 : ℝ} {P C CT CN p YT YN I G GT GN : ℕ → ℝ}
    (hPC : ∀ s, P s * C s = CT s + p s * CN s) (hN : ∀ s, CN s + GN s = YN s)
    (hG : ∀ s, G s = GT s + p s * GN s)
    (hA : Summable fun s => ((1 + r)⁻¹) ^ s * (P s * C s))
    (hB : Summable fun s => ((1 + r)⁻¹) ^ s * (YT s + p s * YN s - I s - G s))
    (hYT : Summable fun s => ((1 + r)⁻¹) ^ s * YT s)
    (h30 : ∑' s, ((1 + r)⁻¹) ^ s * (P s * C s)
      = (1 + r) * B0 + ∑' s, ((1 + r)⁻¹) ^ s * (YT s + p s * YN s - I s - G s)) :
    Summable (fun s => ((1 + r)⁻¹) ^ s * (CT s + I s + GT s)) ∧
    ∑' s, ((1 + r)⁻¹) ^ s * (CT s + I s + GT s)
      = (1 + r) * B0 + ∑' s, ((1 + r)⁻¹) ^ s * YT s := by
  have e : (fun s => ((1 + r)⁻¹) ^ s * (CT s + I s + GT s))
      = fun s => ((1 + r)⁻¹) ^ s * (P s * C s)
          - ((1 + r)⁻¹) ^ s * (YT s + p s * YN s - I s - G s) + ((1 + r)⁻¹) ^ s * YT s := by
    funext s
    linear_combination (-((1 + r)⁻¹) ^ s) * hPC s + (-(((1 + r)⁻¹) ^ s * p s)) * hN s
      + (-((1 + r)⁻¹) ^ s) * hG s
  refine ⟨e ▸ (hA.sub hB).add hYT, ?_⟩
  rw [e, (hA.sub hB).tsum_add hYT, hA.tsum_sub hB, h30]
  ring

/-- The isoelastic Euler equation (33), O&R p. 234: with `u′(C) = C^{−1/σ}`, the Euler equation
(26) `C_s^{−1/σ} = (1 + r^C_{s+1}) β C_{s+1}^{−1/σ}` is equivalent to
`C_{s+1} = [(1+r)P_s/P_{s+1}]^σ β^σ C_s` (for positive consumption). -/
theorem euler_isoelastic {r σ β : ℝ} {P C : ℕ → ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hβ : 0 < β) (hC : ∀ s, 0 < C s) (s : ℕ) :
    C s ^ (-1 / σ) = grossRealRate r P s * β * C (s + 1) ^ (-1 / σ) ↔
      C (s + 1) = grossRealRate r P s ^ σ * β ^ σ * C s := by
  have hg := grossRealRate_pos hr hP s
  have h0 := hC s
  have h1 := hC (s + 1)
  have e : -1 / σ * -σ = 1 := by field_simp
  have hinv : ∀ x : ℝ, 0 < x → (x ^ (-1 / σ)) ^ (-σ) = x := by
    intro x hx; rw [← rpow_mul hx.le, e, rpow_one]
  constructor
  · intro h
    have h' := congrArg (fun x => x ^ (-σ)) h
    rw [hinv _ h0, mul_rpow (by positivity) (by positivity), hinv _ h1,
      mul_rpow hg.le hβ.le, rpow_neg hg.le, rpow_neg hβ.le] at h'
    rw [h']
    have := rpow_pos_of_pos hg σ
    have := rpow_pos_of_pos hβ σ
    field_simp
  · intro h
    rw [h, mul_rpow (by positivity) h0.le, mul_rpow (by positivity) (by positivity),
      ← rpow_mul hg.le, ← rpow_mul hβ.le]
    have e2 : σ * (-1 / σ) = -1 := by field_simp
    rw [e2, rpow_neg_one, rpow_neg_one]
    field_simp

/-- The Euler equation for tradables (34), O&R p. 234: combining (33) with the CES demand
(22) `C_T = γ P^θ C`, `C_{T,s+1} = (P_s/P_{s+1})^{σ−θ} (1+r)^σ β^σ C_{T,s}`. -/
theorem euler_tradables {r σ θ β γ : ℝ} {P C CT : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hβ : 0 < β)
    (hE : ∀ s, C (s + 1) = grossRealRate r P s ^ σ * β ^ σ * C s)
    (h22 : ∀ s, CT s = γ * P s ^ θ * C s) (s : ℕ) :
    CT (s + 1) = (P s / P (s + 1)) ^ (σ - θ) * ((1 + r) ^ σ * β ^ σ) * CT s := by
  have h0 := hP s
  have h1 := hP (s + 1)
  rw [h22, h22, hE, grossRealRate, mul_div_assoc, mul_rpow hr.le (by positivity),
    rpow_sub (by positivity), div_rpow h0.le h1.le, div_rpow h0.le h1.le]
  have := rpow_pos_of_pos h0 θ
  have := rpow_pos_of_pos h1 θ
  have := rpow_pos_of_pos h1 σ
  field_simp

/-- Iterating the tradables Euler equation (34), O&R p. 234:
`C_{T,s} = [(1+r)^σ β^σ]^{s−t} (P_t/P_s)^{σ−θ} C_{T,t}`. -/
theorem tradables_consumption_path {r σ θ β : ℝ} {P CT : ℕ → ℝ} (hP : ∀ s, 0 < P s)
    (h34 : ∀ s, CT (s + 1) = (P s / P (s + 1)) ^ (σ - θ) * ((1 + r) ^ σ * β ^ σ) * CT s)
    (n : ℕ) : CT n = ((1 + r) ^ σ * β ^ σ) ^ n * (P 0 / P n) ^ (σ - θ) * CT 0 := by
  induction n with
  | zero => simp [(hP 0).ne']
  | succ n ih =>
    have h0 := hP 0; have hn := hP n; have hn1 := hP (n + 1)
    have e : (P 0 / P (n + 1)) ^ (σ - θ)
        = (P 0 / P n) ^ (σ - θ) * (P n / P (n + 1)) ^ (σ - θ) := by
      rw [← mul_rpow (by positivity) (by positivity)]
      congr 1
      field_simp
    rw [h34, ih, e, pow_succ]
    ring

/-- The tradables consumption function (35), O&R p. 234: iterating (34) and substituting in the
tradables budget `∑ (1+r)^{−(s−t)} C_{T,s} = W` (the book's
`W = (1+r)B_t + ∑ (1+r)^{−(s−t)}(Y_T − I − G_T)` from (32)),
`C_{T,t} = W / ∑ [(1+r)^{σ−1}β^σ]^{s−t} (P_t/P_s)^{σ−θ}`. -/
theorem tradables_consumption_function {r σ θ β W : ℝ} {P CT : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hβ : 0 < β)
    (h34 : ∀ s, CT (s + 1) = (P s / P (s + 1)) ^ (σ - θ) * ((1 + r) ^ σ * β ^ σ) * CT s)
    (hsum : Summable fun s => ((1 + r) ^ (σ - 1) * β ^ σ) ^ s * (P 0 / P s) ^ (σ - θ))
    (hW : ∑' s, ((1 + r)⁻¹) ^ s * CT s = W) :
    CT 0 = W / ∑' s, ((1 + r) ^ (σ - 1) * β ^ σ) ^ s * (P 0 / P s) ^ (σ - θ) := by
  have hpath := tradables_consumption_path hP h34
  have hd : (1 + r)⁻¹ * ((1 + r) ^ σ * β ^ σ) = (1 + r) ^ (σ - 1) * β ^ σ := by
    rw [rpow_sub_one hr.ne']; ring
  have hterm : ∀ n, ((1 + r)⁻¹) ^ n * CT n
      = ((1 + r) ^ (σ - 1) * β ^ σ) ^ n * (P 0 / P n) ^ (σ - θ) * CT 0 := by
    intro n
    rw [hpath n, ← hd, mul_pow]
    ring
  have hden : 0 < ∑' s, ((1 + r) ^ (σ - 1) * β ^ σ) ^ s * (P 0 / P s) ^ (σ - θ) := by
    refine hsum.tsum_pos (fun n => ?_) 0 ?_
    · have := hP n; have := hP 0; positivity
    · have := hP 0; positivity
  rw [← hW, tsum_congr hterm, tsum_mul_right]
  field_simp

/-- The current account (36), O&R p. 234: `CA_t = B_{t+1} − B_t = rB_t + Y_T + pY_N − C_T − pC_N
− I − G` reduces to `rB_t + Y_T − C_T − I − G_T` under (31) and `G = G_T + pG_N`. -/
theorem current_account_tradables {r B0 B1 YT p YN CT CN I G GT GN : ℝ}
    (hCA : B1 - B0 = r * B0 + YT + p * YN - CT - p * CN - I - G) (hN : CN + GN = YN)
    (hG : G = GT + p * GN) :
    B1 - B0 = r * B0 + YT - CT - I - GT := by
  rw [hCA, hG, ← hN]; ring

/-- The p. 235 claim, O&R: if the price index rises over time (`P_t ≤ P_s` for all `s`, strictly
for some `s`) and `σ > θ`, initial tradables consumption from (35) strictly exceeds its
constant-`P` level `W / ∑ x^{s−t}`, `x = (1+r)^{σ−1}β^σ` (for positive wealth `W`). -/
theorem tradables_consumption_gt_constant_price {σ θ x W : ℝ} {P : ℕ → ℝ} {s0 : ℕ}
    (hσθ : θ < σ) (hx : 0 < x) (hW : 0 < W) (hP : ∀ s, 0 < P s) (hmono : ∀ s, P 0 ≤ P s)
    (hstrict : P 0 < P s0) (hsumP : Summable fun s => x ^ s * (P 0 / P s) ^ (σ - θ))
    (hgeo : Summable fun s : ℕ => x ^ s) :
    W / ∑' s : ℕ, x ^ s < W / ∑' s, x ^ s * (P 0 / P s) ^ (σ - θ) := by
  have hle : ∀ s, x ^ s * (P 0 / P s) ^ (σ - θ) ≤ x ^ s := by
    intro s
    have h := rpow_le_one (div_pos (hP 0) (hP s)).le ((div_le_one (hP s)).mpr (hmono s))
      (sub_nonneg.mpr hσθ.le)
    have := pow_pos hx s
    nlinarith
  have hlt : x ^ s0 * (P 0 / P s0) ^ (σ - θ) < x ^ s0 := by
    have h := rpow_lt_one (div_pos (hP 0) (hP s0)).le ((div_lt_one (hP s0)).mpr hstrict)
      (sub_pos.mpr hσθ)
    have := pow_pos hx s0
    nlinarith
  have hden : 0 < ∑' s, x ^ s * (P 0 / P s) ^ (σ - θ) := by
    refine hsumP.tsum_pos (fun n => ?_) 0 ?_
    · have := hP n; have := hP 0; positivity
    · have := hP 0; positivity
  exact div_lt_div_of_pos_left hW hden (hsumP.tsum_lt_tsum hle hlt hgeo)

/-- The p. 235 converse, O&R: if the price index rises over time and `θ > σ`, "the
intratemporal substitution effect wins out": initial tradables consumption from (35) is strictly
below its constant-`P` level. -/
theorem tradables_consumption_lt_constant_price {σ θ x W : ℝ} {P : ℕ → ℝ} {s0 : ℕ}
    (hσθ : σ < θ) (hx : 0 < x) (hW : 0 < W) (hP : ∀ s, 0 < P s) (hmono : ∀ s, P 0 ≤ P s)
    (hstrict : P 0 < P s0) (hsumP : Summable fun s => x ^ s * (P 0 / P s) ^ (σ - θ))
    (hgeo : Summable fun s : ℕ => x ^ s) :
    W / ∑' s, x ^ s * (P 0 / P s) ^ (σ - θ) < W / ∑' s : ℕ, x ^ s := by
  have hle : ∀ s, x ^ s ≤ x ^ s * (P 0 / P s) ^ (σ - θ) := by
    intro s
    have h := one_le_rpow_of_pos_of_le_one_of_nonpos (div_pos (hP 0) (hP s))
      ((div_le_one (hP s)).mpr (hmono s)) (sub_nonpos.mpr hσθ.le)
    have := pow_pos hx s
    nlinarith
  have hlt : x ^ s0 < x ^ s0 * (P 0 / P s0) ^ (σ - θ) := by
    have h := one_lt_rpow_of_pos_of_lt_one_of_neg (div_pos (hP 0) (hP s0))
      ((div_lt_one (hP s0)).mpr hstrict) (sub_neg.mpr hσθ)
    have := pow_pos hx s0
    nlinarith
  have hden : 0 < ∑' s : ℕ, x ^ s :=
    hgeo.tsum_pos (fun n => (pow_pos hx n).le) 0 (by simp)
  exact div_lt_div_of_pos_left hW hden (hgeo.tsum_lt_tsum hle hlt hsumP)

/-- Exercise 3, O&R p. 265 (identity): with `1 + r^C_t = (1+r)P_{t−1}/P_t`,
`(1 + r^C_t) B_t / P_{t−1} = (1+r) B_t / P_t`. -/
theorem ex3_gross_rate_identity {r Pm P0 B : ℝ} (hPm : Pm ≠ 0) (hP0 : P0 ≠ 0) :
    (1 + r) * Pm / P0 * B / Pm = (1 + r) * B / P0 := by
  field_simp

/-- Exercise 3, O&R p. 265: retracing (27) from the national budget (30) instead of (24),
`∑ R^C_{t,s} C_s = (1 + r^C_t)B_t/P_{t−1} + ∑ R^C_{t,s}(Y_T + pY_N − I − G)_s/P_s`, where
`X_s = Y_{T,s} + p_sY_{N,s} − I_s − G_s` and `Pm = P_{t−1}`. -/
theorem ex3_alternative_budget {r B0 Pm : ℝ} {P C X : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hPm : 0 < Pm)
    (hC : Summable fun s => ((1 + r)⁻¹) ^ s * (P s * C s))
    (hX : Summable fun s => ((1 + r)⁻¹) ^ s * X s)
    (h30 : ∑' s, ((1 + r)⁻¹) ^ s * (P s * C s) = (1 + r) * B0 + ∑' s, ((1 + r)⁻¹) ^ s * X s) :
    ∑' s, realDiscount r P s * C s
      = (1 + r) * Pm / P 0 * B0 / Pm + ∑' s, realDiscount r P s * (X s / P s) := by
  rw [ex3_gross_rate_identity hPm.ne' (hP 0).ne']
  exact (real_budget hr hP hC hX h30).2.2

/-- Exercise 3, O&R p. 265: the alternative consumption function parallel to Chapter 2's
(25), `C_t = [(1 + r^C_t)B_t/P_{t−1} + ∑ R^C_{t,s} X_s/P_s] / ∑ β^{σ(s−t)} (R^C_{t,s})^{1−σ}`. -/
theorem ex3_alternative_consumption {r σ β B0 Pm : ℝ} {P C X : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hPm : 0 < Pm) (hβ : 0 < β)
    (hE : ∀ s, C (s + 1) = grossRealRate r P s ^ σ * β ^ σ * C s)
    (hC : Summable fun s => ((1 + r)⁻¹) ^ s * (P s * C s))
    (hX : Summable fun s => ((1 + r)⁻¹) ^ s * X s)
    (hsum : Summable fun n => realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n)
    (h30 : ∑' s, ((1 + r)⁻¹) ^ s * (P s * C s) = (1 + r) * B0 + ∑' s, ((1 + r)⁻¹) ^ s * X s) :
    C 0 = ((1 + r) * Pm / P 0 * B0 / Pm + ∑' s, realDiscount r P s * (X s / P s))
      / ∑' n, realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n :=
  consumption_of_budget hr hP hβ (consumption_path_of_euler hr hP hE) hsum
    (ex3_alternative_budget hr hP hPm hC hX h30)

/-- Exercise 3, O&R p. 265: the current account in real-consumption units, parallel to
Chapter 2's (26): from `B_{t+1} − B_t = rB_t + X_t − P_tC_t`,
`B_{t+1}/P_t − B_t/P_{t−1} = r^C_t B_t/P_{t−1} + X_t/P_t − C_t`. -/
theorem ex3_real_current_account {r B0 B1 X C0 P0 Pm : ℝ} (hP0 : P0 ≠ 0) (hPm : Pm ≠ 0)
    (hCA : B1 - B0 = r * B0 + X - P0 * C0) :
    B1 / P0 - B0 / Pm = ((1 + r) * Pm / P0 - 1) * (B0 / Pm) + X / P0 - C0 := by
  have hB1 : B1 = (1 + r) * B0 + X - P0 * C0 := by linarith
  rw [hB1]
  field_simp
  ring

/-- `P(p)/p` is the CES price index with the weights swapped, evaluated at `1/p`
(used in Exercise 4, O&R p. 265):
`[γ + (1−γ)p^{1−θ}]^{1/(1−θ)}/p = [(1−γ) + γ (1/p)^{1−θ}]^{1/(1−θ)}`. -/
theorem ex4_price_div_eq {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1) (hp : 0 < p) :
    cesPrice γ θ p / p = cesPrice (1 - γ) θ p⁻¹ := by
  have hθm' : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ1)
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  unfold cesDenom at hD
  have hq := rpow_pos_of_pos hp (1 - θ)
  have hpe : p = (p ^ (1 - θ)) ^ (1 / (1 - θ)) := by
    rw [← rpow_mul hp.le, mul_one_div_cancel hθm', rpow_one]
  unfold cesPrice
  calc (γ + (1 - γ) * p ^ (1 - θ)) ^ (1 / (1 - θ)) / p
      = (γ + (1 - γ) * p ^ (1 - θ)) ^ (1 / (1 - θ)) / (p ^ (1 - θ)) ^ (1 / (1 - θ)) := by
        rw [← hpe]
    _ = ((γ + (1 - γ) * p ^ (1 - θ)) / p ^ (1 - θ)) ^ (1 / (1 - θ)) :=
        (div_rpow hD.le hq.le _).symm
    _ = _ := by
        rw [inv_rpow hp.le]
        congr 1
        field_simp
        ring

/-- `p/P(p)` is strictly increasing in `p` (used in Exercise 4, O&R p. 265): real consumption
per unit of nontradables, `C/C_N = (p/P)^θ/(1−γ)` by (22), rises with `p`. -/
theorem ex4_ratio_strictMonoOn {γ θ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1) :
    StrictMonoOn (fun p => p / cesPrice γ θ p) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have h1γ0 : 0 < 1 - γ := by linarith
  have h1γ1 : 1 - γ < 1 := by linarith
  have ea : a / cesPrice γ θ a = (cesPrice (1 - γ) θ a⁻¹)⁻¹ := by
    rw [← ex4_price_div_eq hγ0 hγ1 hθ1 ha, inv_div]
  have eb : b / cesPrice γ θ b = (cesPrice (1 - γ) θ b⁻¹)⁻¹ := by
    rw [← ex4_price_div_eq hγ0 hγ1 hθ1 hb, inv_div]
  simp only
  rw [ea, eb]
  have hlt : cesPrice (1 - γ) θ b⁻¹ < cesPrice (1 - γ) θ a⁻¹ :=
    cesPrice_strictMonoOn h1γ0 h1γ1 hθ1 (inv_pos.mpr hb) (inv_pos.mpr ha)
      (inv_strictAnti₀ ha hab)
  exact (inv_lt_inv₀ (cesPrice_pos h1γ0 h1γ1 (inv_pos.mpr ha))
    (cesPrice_pos h1γ0 h1γ1 (inv_pos.mpr hb))).mpr hlt

/-- The quantity `(p/P)^θ P^σ`, proportional (by (22)) to `P^σ C / C_N`, which the Euler
equation (33) with `β(1+r) = 1` holds constant (Exercise 4, O&R p. 265). -/
noncomputable def ex4Invariant (γ θ σ p : ℝ) : ℝ := (p / cesPrice γ θ p) ^ θ * cesPrice γ θ p ^ σ

/-- The Exercise 4 invariant is strictly increasing in `p` for `θ, σ > 0` (O&R p. 265). -/
theorem ex4Invariant_strictMonoOn {γ θ σ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hσ : 0 < σ) : StrictMonoOn (ex4Invariant γ θ σ) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have hPa := cesPrice_pos (θ := θ) hγ0 hγ1 ha'
  have hPb := cesPrice_pos (θ := θ) hγ0 hγ1 hb'
  have h1 : (a / cesPrice γ θ a) ^ θ < (b / cesPrice γ θ b) ^ θ :=
    rpow_lt_rpow (div_pos ha' hPa).le (ex4_ratio_strictMonoOn hγ0 hγ1 hθ1 ha hb hab) hθ
  have h2 : cesPrice γ θ a ^ σ < cesPrice γ θ b ^ σ :=
    rpow_lt_rpow hPa.le (cesPrice_strictMonoOn hγ0 hγ1 hθ1 ha hb hab) hσ
  unfold ex4Invariant
  have := rpow_pos_of_pos hPa σ
  have := rpow_pos_of_pos (div_pos hb' hPb) θ
  calc (a / cesPrice γ θ a) ^ θ * cesPrice γ θ a ^ σ
      < (b / cesPrice γ θ b) ^ θ * cesPrice γ θ a ^ σ := by gcongr
    _ < (b / cesPrice γ θ b) ^ θ * cesPrice γ θ b ^ σ := by gcongr

/-- Exercise 4, O&R p. 265: along an equilibrium path with nontradable supply `N_s = C_{N,s}`,
the demand (22) `C_N = (1−γ)(p/P)^{−θ}C` and the Euler equation (33) with `β(1+r) = 1` imply
that `N_s (p_s/P_s)^θ P_s^σ` is constant over time. -/
theorem ex4_invariant_step {γ θ σ β r : ℝ} {p C N : ℕ → ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hr : 0 < 1 + r) (hβ : 0 < β) (hβr : β * (1 + r) = 1) (hp : ∀ s, 0 < p s)
    (h22N : ∀ s, N s = (1 - γ) * (p s / cesPrice γ θ (p s)) ^ (-θ) * C s)
    (hE : ∀ s, C (s + 1) = grossRealRate r (fun s => cesPrice γ θ (p s)) s ^ σ * β ^ σ * C s)
    (s : ℕ) : N (s + 1) * ex4Invariant γ θ σ (p (s + 1)) = N s * ex4Invariant γ θ σ (p s) := by
  have hP : ∀ s, 0 < cesPrice γ θ (p s) := fun s => cesPrice_pos hγ0 hγ1 (hp s)
  have key : ∀ s, N s * ex4Invariant γ θ σ (p s) = (1 - γ) * (C s * cesPrice γ θ (p s) ^ σ) := by
    intro s
    have hx := div_pos (hp s) (hP s)
    rw [h22N s, ex4Invariant, rpow_neg hx.le]
    have := rpow_pos_of_pos hx θ
    field_simp
  rw [key, key, hE, grossRealRate, mul_div_assoc,
    mul_rpow hr.le (div_pos (hP s) (hP (s + 1))).le, div_rpow (hP s).le (hP (s + 1)).le]
  have e1 : (1 + r) ^ σ * β ^ σ = 1 := by
    rw [← mul_rpow hr.le hβ.le, mul_comm, hβr, one_rpow]
  have := rpow_pos_of_pos (hP (s + 1)) σ
  field_simp
  linear_combination (C s * cesPrice γ θ (p s) ^ σ * (1 - γ)) * e1

/-- Exercise 4(a), O&R p. 265: with `β(1+r) = 1` and a constant net endowment of nontradables
`Y_N − G_N = N̄ > 0`, equilibrium (22) + (33) forces the relative price `p`, real consumption
`C` and tradables consumption `C_T` to be constant over time. -/
theorem ex4a_constant {γ θ σ β r Nbar : ℝ} {p C CT : ℕ → ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hβr : β * (1 + r) = 1) (hNbar : 0 < Nbar) (hp : ∀ s, 0 < p s)
    (h22T : ∀ s, CT s = γ * cesPrice γ θ (p s) ^ θ * C s)
    (h22N : ∀ s, Nbar = (1 - γ) * (p s / cesPrice γ θ (p s)) ^ (-θ) * C s)
    (hE : ∀ s, C (s + 1) = grossRealRate r (fun s => cesPrice γ θ (p s)) s ^ σ * β ^ σ * C s)
    (s : ℕ) : p s = p 0 ∧ C s = C 0 ∧ CT s = CT 0 := by
  have hinv : ∀ s, ex4Invariant γ θ σ (p s) = ex4Invariant γ θ σ (p 0) := by
    intro s
    induction s with
    | zero => rfl
    | succ n ih =>
      have h := ex4_invariant_step (N := fun _ => Nbar) hγ0 hγ1 hr hβ hβr hp h22N hE n
      rw [← ih]
      exact mul_left_cancel₀ hNbar.ne' h
  have hps : p s = p 0 :=
    (ex4Invariant_strictMonoOn hγ0 hγ1 hθ hθ1 hσ).injOn (hp s) (hp 0) (hinv s)
  have hCs : C s = C 0 := by
    have h := (h22N s).symm.trans (h22N 0)
    rw [hps] at h
    have hx := div_pos (hp 0) (cesPrice_pos (θ := θ) hγ0 hγ1 (hp 0))
    have : 0 < (1 - γ) * (p 0 / cesPrice γ θ (p 0)) ^ (-θ) :=
      mul_pos (by linarith) (rpow_pos_of_pos hx _)
    exact mul_left_cancel₀ this.ne' h
  refine ⟨hps, hCs, ?_⟩
  rw [h22T s, h22T 0, hps, hCs]

/-- Exercise 4(a), O&R p. 265: the constant level of tradables consumption is
`C_T = [r/(1+r)] [(1+r)B_t + ∑ (1+r)^{−(s−t)}(Y_T − I − G_T)_s]`, exactly the tradables
analogue of Chapter 2's consumption function (10) (for `r > 0`). -/
theorem ex4a_level {r B0 cbar : ℝ} {X : ℕ → ℝ} (hr : 0 < r)
    (h32 : ∑' s : ℕ, ((1 + r)⁻¹) ^ s * cbar = (1 + r) * B0 + ∑' s, ((1 + r)⁻¹) ^ s * X s) :
    cbar = r / (1 + r) * ((1 + r) * B0 + ∑' s, ((1 + r)⁻¹) ^ s * X s) := by
  have hd0 : 0 ≤ (1 + r)⁻¹ := inv_nonneg.mpr (by linarith)
  have hd1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  rw [← h32, tsum_mul_right, tsum_geometric_of_lt_one hd0 hd1]
  have : (1 : ℝ) + r ≠ 0 := by linarith
  have : r ≠ 0 := hr.ne'
  field_simp
  simp [this]

/-- Exercise 4(b), O&R p. 265: suppose it becomes known that the nontradable net supply rises
permanently from `N₁` to `N₂ > N₁` after date `t + T` (index `T`). With `β(1+r) = 1`:
the relative price is constant except between `T` and `T+1`, where it falls, as does `P`;
tradables consumption jumps by the factor `(P_T/P_{T+1})^{σ−θ}`, upward iff `σ > θ`. -/
theorem ex4b_step {γ θ σ β r N1 N2 : ℝ} {T : ℕ} {p C CT N : ℕ → ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hβr : β * (1 + r) = 1) (hN1 : 0 < N1) (hN12 : N1 < N2) (hp : ∀ s, 0 < p s)
    (hC : ∀ s, 0 < C s) (hN : ∀ s, N s = if s ≤ T then N1 else N2)
    (h22T : ∀ s, CT s = γ * cesPrice γ θ (p s) ^ θ * C s)
    (h22N : ∀ s, N s = (1 - γ) * (p s / cesPrice γ θ (p s)) ^ (-θ) * C s)
    (hE : ∀ s, C (s + 1) = grossRealRate r (fun s => cesPrice γ θ (p s)) s ^ σ * β ^ σ * C s) :
    (∀ s, s ≠ T → p (s + 1) = p s) ∧ p (T + 1) < p T ∧
    cesPrice γ θ (p (T + 1)) < cesPrice γ θ (p T) ∧
    CT (T + 1) = (cesPrice γ θ (p T) / cesPrice γ θ (p (T + 1))) ^ (σ - θ) * CT T ∧
    (θ < σ → CT T < CT (T + 1)) ∧ (σ < θ → CT (T + 1) < CT T) := by
  have hmono := ex4Invariant_strictMonoOn hγ0 hγ1 hθ hθ1 hσ
  have hstep := ex4_invariant_step hγ0 hγ1 hr hβ hβr hp h22N hE
  have hI : ∀ s, 0 < ex4Invariant γ θ σ (p s) := by
    intro s
    have hP := cesPrice_pos (θ := θ) hγ0 hγ1 (hp s)
    unfold ex4Invariant
    have := rpow_pos_of_pos (div_pos (hp s) hP) θ
    have := rpow_pos_of_pos hP σ
    positivity
  have hflat : ∀ s, s ≠ T → p (s + 1) = p s := by
    intro s hs
    have hNs : N (s + 1) = N s := by
      rw [hN, hN]
      rcases lt_or_gt_of_ne hs with h | h
      · simp [show s ≤ T by omega, show s + 1 ≤ T by omega]
      · simp [show ¬ s ≤ T by omega, show ¬ s + 1 ≤ T by omega]
    have hNpos : 0 < N s := by rw [hN]; split_ifs <;> linarith
    have h := hstep s
    rw [hNs] at h
    exact hmono.injOn (hp (s + 1)) (hp s) (mul_left_cancel₀ hNpos.ne' h)
  have hdrop : p (T + 1) < p T := by
    have h := hstep T
    have hNT : N T = N1 := by rw [hN]; simp
    have hNT1 : N (T + 1) = N2 := by rw [hN]; simp
    rw [hNT, hNT1] at h
    have hlt : ex4Invariant γ θ σ (p (T + 1)) < ex4Invariant γ θ σ (p T) := by
      have h1 := hI T
      have h2 := hI (T + 1)
      nlinarith
    exact (hmono.lt_iff_lt (hp (T + 1)) (hp T)).mp hlt
  have hPdrop := cesPrice_strictMonoOn hγ0 hγ1 hθ1 (hp (T + 1)) (hp T) hdrop
  have hPpos : ∀ s, 0 < cesPrice γ θ (p s) := fun s => cesPrice_pos hγ0 hγ1 (hp s)
  have e1 : (1 + r) ^ σ * β ^ σ = 1 := by
    rw [← mul_rpow hr.le hβ.le, mul_comm, hβr, one_rpow]
  have hjump : CT (T + 1)
      = (cesPrice γ θ (p T) / cesPrice γ θ (p (T + 1))) ^ (σ - θ) * CT T := by
    have h := euler_tradables (P := fun s => cesPrice γ θ (p s)) hr hPpos hβ hE h22T T
    rw [h, e1, mul_one]
  have hbase : 1 < cesPrice γ θ (p T) / cesPrice γ θ (p (T + 1)) :=
    (one_lt_div (hPpos (T + 1))).mpr hPdrop
  have hCT : 0 < CT T := by
    rw [h22T]; have := rpow_pos_of_pos (hPpos T) θ; have := hC T; positivity
  refine ⟨hflat, hdrop, hPdrop, hjump, fun h => ?_, fun h => ?_⟩
  · rw [hjump]
    have := one_lt_rpow hbase (sub_pos.mpr h)
    nlinarith
  · rw [hjump]
    have := rpow_lt_one_of_one_lt_of_neg hbase (sub_neg.mpr h)
    nlinarith

/-- Exercise 4(b), O&R p. 265: starting from a zero-current-account steady state with constant
tradable net output `X̄ = Y_T − I − G_T`, if the new tradables consumption path never falls below
its date-`t` level and strictly exceeds it at some date (the case `σ > θ` of `ex4b_step`), the
date-`t` current account (36), `rB_t + X̄ − C_{T,t}`, is in surplus. -/
theorem ex4b_current_account_surplus {r B0 Xbar : ℝ} {c : ℕ → ℝ} {T : ℕ} (hr : 0 < r)
    (hge : ∀ s, c 0 ≤ c s) (hlt : c 0 < c T)
    (hc : Summable fun s => ((1 + r)⁻¹) ^ s * c s)
    (h32 : ∑' s, ((1 + r)⁻¹) ^ s * c s = (1 + r) * B0 + ∑' s : ℕ, ((1 + r)⁻¹) ^ s * Xbar) :
    0 < r * B0 + Xbar - c 0 := by
  have hd0 : 0 ≤ (1 + r)⁻¹ := inv_nonneg.mpr (by linarith)
  have hd1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hdpos : 0 < (1 + r)⁻¹ := inv_pos.mpr (by linarith)
  have hgeo := summable_geometric_of_lt_one hd0 hd1
  have hlt' : ∑' s : ℕ, ((1 + r)⁻¹) ^ s * c 0 < ∑' s, ((1 + r)⁻¹) ^ s * c s :=
    (hgeo.mul_right _).tsum_lt_tsum
      (fun s => mul_le_mul_of_nonneg_left (hge s) (pow_nonneg hd0 s))
      (mul_lt_mul_of_pos_left hlt (pow_pos hdpos T)) hc
  rw [h32, tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one hd0 hd1] at hlt'
  have e : (1 - (1 + r)⁻¹)⁻¹ = (1 + r) / r := by
    have : (1 : ℝ) + r ≠ 0 := by linarith
    have : r ≠ 0 := hr.ne'
    field_simp
    simp [this]
  rw [e] at hlt'
  have h1r : 0 < (1 + r) / r := div_pos (by linarith) hr
  have : (1 + r) / r * c 0 < (1 + r) / r * (r * B0 + Xbar) := by
    have : (1 + r) * B0 = (1 + r) / r * (r * B0) := by field_simp
    nlinarith
  nlinarith [(mul_lt_mul_iff_right₀ h1r).mp this]

end ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Endogenous labour supply: leisure as a nontraded good

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, Appendix 4A
(pp. 258–260, eqs. (67)–(68)) and Exercise 5 (p. 265).

Leisure `L̄ − L` plays the role of the nontraded good, with the wage `w` (in tradables) as its
price, so the CES price index is `P = [γ + (1−γ) w^{1−θ}]^{1/(1−θ)}`. We prove:

* `w^{1−θ} = (P^{1−θ} − γ)/(1−γ)` and the leisure demand `L̄ − L = C_T ((1−γ)/γ) w^{−θ}` implied
  by (22);
* the rewritten labour income `wL − G_T = wL̄ − (P^{1−θ}/γ − 1) C_T − G_T`;
* (67): solving the tradables budget with endogenous labour supply and the Euler equation (34)
  gives `C_{T,t} = γ P_t^θ C_t` with `C_t` the consumption function (29) evaluated at full income
  `wL̄ − G_T`, i.e. (67) is (22); and the form (68);
* Exercise 5: the same formula (67) derived instead from (29), (22) and (33).
-/

namespace ObstfeldRogoff.RealExchangeRate.EndogenousLabour

open Real Filter Topology
open ObstfeldRogoff.RealExchangeRate.CESIndex ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics

/-- Appendix 4A, O&R p. 258: with leisure priced at the wage, the price index
`P = [γ + (1−γ) w^{1−θ}]^{1/(1−θ)}` satisfies `w^{1−θ} = (P^{1−θ} − γ)/(1−γ)`. -/
theorem wage_rpow_eq {γ θ w : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1) (hw : 0 < w) :
    w ^ (1 - θ) = (cesPrice γ θ w ^ (1 - θ) - γ) / (1 - γ) := by
  rw [cesPrice_rpow_one_sub hγ0 hγ1 hw hθ1]
  have : (1 - γ) ≠ 0 := by linarith
  field_simp
  ring

/-- Appendix 4A, O&R p. 258: the implication of (22) for leisure. If `C_T = γ P^θ C` and
leisure demand is `L̄ − L = (1−γ)(w/P)^{−θ} C`, then `L̄ − L = C_T ((1−γ)/γ) w^{−θ}`. -/
theorem leisure_demand {γ θ w P C CT Lbar L : ℝ} (hγ0 : 0 < γ) (hw : 0 < w) (hP : 0 < P)
    (h22T : CT = γ * P ^ θ * C) (h22N : Lbar - L = (1 - γ) * (w / P) ^ (-θ) * C) :
    Lbar - L = CT * ((1 - γ) / γ) * w ^ (-θ) := by
  rw [h22N, h22T, div_rpow hw.le hP.le, rpow_neg hP.le, rpow_neg hw.le]
  have := rpow_pos_of_pos hP θ
  have := rpow_pos_of_pos hw θ
  field_simp

/-- Appendix 4A, O&R p. 258: using the leisure demand and `w^{1−θ} = (P^{1−θ} − γ)/(1−γ)`,
labour income net of government spending is `wL − G_T = wL̄ − (P^{1−θ}/γ − 1) C_T − G_T`. -/
theorem labour_income_rewrite {γ θ w CT Lbar L GT : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hθ1 : θ ≠ 1) (hw : 0 < w) (hleis : Lbar - L = CT * ((1 - γ) / γ) * w ^ (-θ)) :
    w * L - GT = w * Lbar - (cesPrice γ θ w ^ (1 - θ) / γ - 1) * CT - GT := by
  have hww : w * w ^ (-θ) = w ^ (1 - θ) := by
    rw [sub_eq_add_neg, rpow_add hw, rpow_one]
  have hL : w * L = w * Lbar - CT * ((1 - γ) / γ) * (w * w ^ (-θ)) := by
    have : L = Lbar - CT * ((1 - γ) / γ) * w ^ (-θ) := by linarith
    rw [this]; ring
  rw [hL, hww, wage_rpow_eq hγ0 hγ1 hθ1 hw]
  have : (1 - γ) ≠ 0 := by linarith
  field_simp

/-- Appendix 4A, eq. (67), O&R pp. 258–259: with leisure as the nontraded good, the tradables
budget `∑ (1+r)^{−(s−t)} C_{T,s} = (1+r)Q_t + ∑ (1+r)^{−(s−t)}(w_sL_s − G_{T,s})`, the leisure
demand implied by (22), the Euler equation (34) and `P_s = [γ + (1−γ)w_s^{1−θ}]^{1/(1−θ)}` give
`C_{T,t} = γ P_t^θ · [(1+r)Q_t + ∑ (1+r)^{−(s−t)}(w_sL̄ − G_{T,s})] /
(P_t ∑ [(1+r)^{s−t} P_t/P_s]^{σ−1} β^{σ(s−t)})`, i.e. `γ P_t^θ C_t` with `C_t` the consumption
function (29) at full income `wL̄ − G_T`: (67) is the same as (22). -/
theorem tradables_consumption_67 {γ θ σ β r Q Lbar : ℝ} {w L GT CT P : ℕ → ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hw : ∀ s, 0 < w s) (hPdef : ∀ s, P s = cesPrice γ θ (w s))
    (hleis : ∀ s, Lbar - L s = CT s * ((1 - γ) / γ) * w s ^ (-θ))
    (h34 : ∀ s, CT (s + 1) = (P s / P (s + 1)) ^ (σ - θ) * ((1 + r) ^ σ * β ^ σ) * CT s)
    (hCT : Summable fun s => ((1 + r)⁻¹) ^ s * CT s)
    (hY : Summable fun s => ((1 + r)⁻¹) ^ s * (w s * L s - GT s))
    (hYbar : Summable fun s => ((1 + r)⁻¹) ^ s * (w s * Lbar - GT s))
    (hD : Summable fun n => ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n)
    (hbud : ∑' s, ((1 + r)⁻¹) ^ s * CT s
      = (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (w s * L s - GT s)) :
    CT 0 = γ * P 0 ^ θ * (((1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (w s * Lbar - GT s))
      / (P 0 * ∑' n, ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n)) := by
  have hP : ∀ s, 0 < P s := fun s => by rw [hPdef]; exact cesPrice_pos hγ0 hγ1 (hw s)
  have hrw : ∀ s, w s * L s - GT s
      = (w s * Lbar - GT s) - (P s ^ (1 - θ) / γ - 1) * CT s := by
    intro s
    rw [hPdef, labour_income_rewrite hγ0 hγ1 hθ1 (hw s) (hleis s)]
    ring
  -- the budget with leisure valued at the wage
  have eA : (fun s => ((1 + r)⁻¹) ^ s * (P s ^ (1 - θ) / γ * CT s))
      = fun s => ((1 + r)⁻¹) ^ s * CT s + ((1 + r)⁻¹) ^ s * (w s * Lbar - GT s)
          - ((1 + r)⁻¹) ^ s * (w s * L s - GT s) := by
    funext s
    rw [hrw s]
    ring
  have hA : ∑' s, ((1 + r)⁻¹) ^ s * (P s ^ (1 - θ) / γ * CT s)
      = (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (w s * Lbar - GT s) := by
    rw [eA, (hCT.add hYbar).tsum_sub hY, hCT.tsum_add hYbar, hbud]
    ring
  -- each term of the left side, using the Euler equation (34)
  have hpath := tradables_consumption_path hP h34
  have hterm : ∀ n, ((1 + r)⁻¹) ^ n * (P n ^ (1 - θ) / γ * CT n)
      = P 0 ^ (1 - θ) / γ * (((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n) * CT 0 := by
    intro n
    have h0 := hP 0
    have hn := hP n
    have hu : 0 < P 0 / P n := div_pos h0 hn
    have ha : 0 < (1 + r) ^ n := pow_pos hr n
    have e1 : P n ^ (1 - θ) = P 0 ^ (1 - θ) / (P 0 / P n) ^ (1 - θ) := by
      rw [div_rpow h0.le hn.le]
      have := rpow_pos_of_pos h0 (1 - θ)
      have := rpow_pos_of_pos hn (1 - θ)
      field_simp
    have e2 : (P 0 / P n) ^ (σ - 1) = (P 0 / P n) ^ (σ - θ) / (P 0 / P n) ^ (1 - θ) := by
      rw [← rpow_sub hu]; ring_nf
    have e3 : ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1)
        = ((1 + r) ^ n) ^ σ / (1 + r) ^ n * (P 0 / P n) ^ (σ - 1) := by
      rw [mul_rpow ha.le hu.le, rpow_sub_one ha.ne']
    have e4 : ((1 + r) ^ σ * β ^ σ) ^ n = ((1 + r) ^ n) ^ σ * (β ^ σ) ^ n := by
      rw [mul_pow, rpow_pow_comm hr.le]
    rw [hpath n, e1, e3, e2, e4, inv_pow]
    have := rpow_pos_of_pos hu (1 - θ)
    field_simp
  have hden : 0 < ∑' n, ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n := by
    refine hD.tsum_pos (fun n => ?_) 0 ?_
    · have := hP n; have := hP 0; positivity
    · have := hP 0; positivity
  rw [tsum_congr hterm, tsum_mul_right, tsum_mul_left] at hA
  rw [← hA]
  set D := ∑' n, ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n with hDdef
  have h0 := hP 0
  have e5 : P 0 ^ (1 - θ) = P 0 / P 0 ^ θ := by rw [rpow_sub h0, rpow_one]
  rw [e5]
  have := rpow_pos_of_pos h0 θ
  field_simp

/-- Appendix 4A, eq. (68), O&R p. 259: with the wage given by the factor-price frontier
`w_s = w(r, A_s)` and `P_s = P[w(r, A_s)]`, equilibrium tradables consumption is
`C_{T,t} = γ {1/P[w(r,A_t)]}^{1−θ} [(1+r)Q_t + ∑ (1+r)^{−(s−t)}(w(r,A_s)L̄ − G_{T,s})] /
∑ {(1+r)^{s−t} P[w(r,A_t)]/P[w(r,A_s)]}^{σ−1} β^{σ(s−t)}`. -/
theorem tradables_consumption_68 {γ θ σ β r Q Lbar : ℝ} {wf : ℝ → ℝ → ℝ}
    {A L GT CT P : ℕ → ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hw : ∀ s, 0 < wf r (A s)) (hPdef : ∀ s, P s = cesPrice γ θ (wf r (A s)))
    (hleis : ∀ s, Lbar - L s = CT s * ((1 - γ) / γ) * wf r (A s) ^ (-θ))
    (h34 : ∀ s, CT (s + 1) = (P s / P (s + 1)) ^ (σ - θ) * ((1 + r) ^ σ * β ^ σ) * CT s)
    (hCT : Summable fun s => ((1 + r)⁻¹) ^ s * CT s)
    (hY : Summable fun s => ((1 + r)⁻¹) ^ s * (wf r (A s) * L s - GT s))
    (hYbar : Summable fun s => ((1 + r)⁻¹) ^ s * (wf r (A s) * Lbar - GT s))
    (hD : Summable fun n => ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n)
    (hbud : ∑' s, ((1 + r)⁻¹) ^ s * CT s
      = (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (wf r (A s) * L s - GT s)) :
    CT 0 = γ * (1 / P 0) ^ (1 - θ)
      * (((1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (wf r (A s) * Lbar - GT s))
        / ∑' n, ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n) := by
  rw [tradables_consumption_67 (w := fun s => wf r (A s)) hγ0 hγ1 hθ1 hr hβ hw hPdef hleis h34
    hCT hY hYbar hD hbud]
  have h0 : 0 < P 0 := by rw [hPdef]; exact cesPrice_pos hγ0 hγ1 (hw 0)
  set W := (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (wf r (A s) * Lbar - GT s) with hWdef
  set D := ∑' n, ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n with hDdef
  rw [one_div, inv_rpow h0.le, ← rpow_neg h0.le, neg_sub, rpow_sub_one h0.ne']
  field_simp

/-- Exercise 5, O&R p. 265: an alternative derivation of (67) from (29), (22) and (33). With
spending `P_sC_s = C_{T,s} + w_s(L̄ − L_s)` (leisure bought at the wage), the tradables budget
becomes the real-consumption budget (24) at full income `w_sL̄ − G_{T,s}`; the isoelastic Euler
equation (33) then gives `C_t` by (29), and (22) gives `C_{T,t} = γ P_t^θ C_t`, which is (67). -/
theorem exercise5_tradables_consumption {γ θ σ β r Q Lbar : ℝ} {w L GT CT C P : ℕ → ℝ}
    (hr : 0 < 1 + r) (hβ : 0 < β) (hP : ∀ s, 0 < P s)
    (hPC : ∀ s, P s * C s = CT s + w s * (Lbar - L s))
    (hE : ∀ s, C (s + 1) = grossRealRate r P s ^ σ * β ^ σ * C s)
    (h22 : ∀ s, CT s = γ * P s ^ θ * C s)
    (hCT : Summable fun s => ((1 + r)⁻¹) ^ s * CT s)
    (hY : Summable fun s => ((1 + r)⁻¹) ^ s * (w s * L s - GT s))
    (hYbar : Summable fun s => ((1 + r)⁻¹) ^ s * (w s * Lbar - GT s))
    (hD : Summable fun n => ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n)
    (hbud : ∑' s, ((1 + r)⁻¹) ^ s * CT s
      = (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (w s * L s - GT s)) :
    CT 0 = γ * P 0 ^ θ * (((1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (w s * Lbar - GT s))
      / (P 0 * ∑' n, ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n)) := by
  have e : (fun s => ((1 + r)⁻¹) ^ s * (P s * C s))
      = fun s => ((1 + r)⁻¹) ^ s * CT s + ((1 + r)⁻¹) ^ s * (w s * Lbar - GT s)
          - ((1 + r)⁻¹) ^ s * (w s * L s - GT s) := by
    funext s
    rw [hPC s]
    ring
  have hPCs : Summable fun s => ((1 + r)⁻¹) ^ s * (P s * C s) := e ▸ (hCT.add hYbar).sub hY
  have h24 : ∑' s, ((1 + r)⁻¹) ^ s * (P s * C s)
      = (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (w s * Lbar - GT s) := by
    rw [e, (hCT.add hYbar).tsum_sub hY, hCT.tsum_add hYbar, hbud]
    ring
  rw [h22 0, consumption_function_price_form hr hP hβ hE hPCs hYbar hD h24]

end ObstfeldRogoff.RealExchangeRate.EndogenousLabour

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Costly capital mobility and short-run relative price adjustment

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Appendix 4B, pp. 260–264. Capital is freely mobile into tradables but costly to
install in nontradables. Output there is `Y_N = A_N K_N^α L_N^{1−α}`. Preferences
have unit elasticities (`σ = θ = 1`) and `β(1 + r) = 1`, so tradables consumption
`C̄_T` is constant. Demand for nontradables in tradables units is
`D = (1 − γ)C̄_T/γ + G̃_N`.

* **Short-run equilibrium** (O&R (73)–(74)). With the labour first-order condition
  (69) and market clearing, employment in nontradables is `L_N = (1 − α)D/w`,
  independent of the capital stock. The relative price is
  `p = w^{1−α}D^α/((1 − α)^{1−α} A_N K_N^α)`, strictly decreasing in `K_N`.
* **The q dynamics** (O&R (75)). The value marginal product of capital is `αD/K`.
  The steady state is `q̄ = 1`, `K̄_N = αD/r`, with `K̄/L̄ = αw/((1 − α)r)`.
* **Saddle-point stability** (p. 263, Figure 4.15). The linearised system
  `x_{t+1} = (I + J)x_t` has `J = [[0, K̄/χ], [r/K̄, r(1 + 1/χ)]]`, and `I + J` has exactly
  one eigenvalue inside the unit circle for every `r, χ > 0`: one stable root in
  `(−1, 1)` and one unstable root above `1`.
-/

namespace ObstfeldRogoff.RealExchangeRate.CostlyCapital

/-- **Employment in nontradables**, O&R (74), p. 262: with the labour first-order condition
`w L^α = (1 − α) p A K^α` (equivalent to (69)) and market clearing `D = p A K^α L^{1−α}`,
employment is `L = (1 − α)D/w`, independent of `K`. -/
theorem employment_nontradables {α w p A K L D : ℝ} (hL : 0 < L)
    (hfoc : w * L ^ α = (1 - α) * p * A * K ^ α) (hclear : D = p * A * K ^ α * L ^ (1 - α))
    (hw : w ≠ 0) :
    L = (1 - α) * D / w := by
  have hLL : L ^ α * L ^ (1 - α) = L := by
    rw [← Real.rpow_add hL, add_sub_cancel, Real.rpow_one]
  rw [eq_div_iff hw, hclear]
  calc L * w = (w * L ^ α) * L ^ (1 - α) := by rw [mul_assoc, hLL]; ring
    _ = (1 - α) * (p * A * K ^ α * L ^ (1 - α)) := by rw [hfoc]; ring

/-- **The short-run relative price of nontradables**, O&R (73), p. 261:
`p = w^{1−α}D^α/((1 − α)^{1−α} A K^α)`. -/
theorem price_nontradables {α w p A K L D : ℝ} (hα1 : α < 1) (hw : 0 < w) (hA : 0 < A)
    (hK : 0 < K) (hL : 0 < L) (hD : 0 < D)
    (hfoc : w * L ^ α = (1 - α) * p * A * K ^ α) (hclear : D = p * A * K ^ α * L ^ (1 - α)) :
    p = w ^ (1 - α) * D ^ α / ((1 - α) ^ (1 - α) * A * K ^ α) := by
  have hL' := employment_nontradables hL hfoc hclear hw.ne'
  have h1a : 0 < 1 - α := by linarith
  have hKa : 0 < K ^ α := Real.rpow_pos_of_pos hK α
  have hp : p = w * L ^ α / ((1 - α) * A * K ^ α) := by
    rw [eq_div_iff (by positivity)]
    linarith [hfoc]
  rw [hp, hL', Real.div_rpow (by positivity) hw.le, Real.mul_rpow h1a.le hD.le]
  have hwa : 0 < w ^ α := Real.rpow_pos_of_pos hw α
  have h1aa : 0 < (1 - α) ^ α := Real.rpow_pos_of_pos h1a α
  have hw' : w ^ (1 - α) = w / w ^ α := by rw [Real.rpow_sub hw, Real.rpow_one]
  have h1' : (1 - α) ^ (1 - α) = (1 - α) / (1 - α) ^ α := by
    rw [Real.rpow_sub h1a, Real.rpow_one]
  rw [hw', h1']
  field_simp

/-- **The relative price falls as nontradables capital accumulates** (O&R p. 263, lower panel of
Figure 4.15): at given `w`, `D` and `A`, the price (73) is strictly decreasing in `K`. -/
theorem price_strictAnti_capital {α w A D : ℝ} (hα : 0 < α) (hα1 : α < 1) (hw : 0 < w)
    (hA : 0 < A) (hD : 0 < D) {K K' : ℝ} (hK : 0 < K) (hKK : K < K') :
    w ^ (1 - α) * D ^ α / ((1 - α) ^ (1 - α) * A * K' ^ α) <
      w ^ (1 - α) * D ^ α / ((1 - α) ^ (1 - α) * A * K ^ α) := by
  have h1a : 0 < 1 - α := by linarith
  have hnum : 0 < w ^ (1 - α) * D ^ α := by positivity
  have hc : 0 < (1 - α) ^ (1 - α) * A := by positivity
  have hpow : K ^ α < K' ^ α := Real.rpow_lt_rpow hK.le hKK hα
  apply div_lt_div_of_pos_left hnum (by positivity)
  exact mul_lt_mul_of_pos_left hpow hc

/-- **The value marginal product of capital**, used in O&R (75): with market clearing
`D = p A K^α L^{1−α}`, `p · α A K^{α−1} L^{1−α} = αD/K`. -/
theorem value_marginal_product {α p A K L D : ℝ} (hK : 0 < K)
    (hclear : D = p * A * K ^ α * L ^ (1 - α)) :
    p * (α * A * K ^ (α - 1) * L ^ (1 - α)) = α * D / K := by
  rw [hclear, Real.rpow_sub hK, Real.rpow_one]
  field_simp

/-- The right side of the `q` equation (75) without the second-order term:
`F(q, K) = rq − αD/(K(1 + (q − 1)/χ))`. -/
noncomputable def qDrift (r α D χ q K : ℝ) : ℝ := r * q - α * D / (K * (1 + (q - 1) / χ))

/-- **The steady state**, O&R p. 262: `q̄ = 1` and `K̄ = αD/r` make both `ΔK = (q − 1)K/χ` (70) and
the `q` equation stationary; `q̄ = 1` is forced by (70) and then `K̄ = αD/r` by (75). -/
theorem steady_state_iff {r α D χ K : ℝ} (hr : 0 < r) (hK : 0 < K) :
    qDrift r α D χ 1 K = 0 ↔ K = α * D / r := by
  unfold qDrift
  simp only [sub_self, zero_div, add_zero, mul_one]
  rw [sub_eq_zero, eq_div_iff hr.ne', eq_div_iff hK.ne']
  constructor <;> intro h <;> linarith

/-- **The steady-state capital–labour ratio**, O&R p. 262: `K̄/L̄ = αw/((1 − α)r)`, so the value
marginal product of capital is back to `r`. -/
theorem steady_capital_labour {r α D w : ℝ} (hr : 0 < r) (hα1 : α < 1) (hw : 0 < w)
    (hD : 0 < D) :
    (α * D / r) / ((1 - α) * D / w) = α * w / ((1 - α) * r) := by
  have h1a : (1 - α) ≠ 0 := by linarith
  field_simp

/-- **Linearisation in `q`**, O&R p. 262: at the steady state,
`∂F/∂q = r + αD/(χK̄) = r(1 + 1/χ)`. -/
theorem hasDerivAt_qDrift_q {r α D χ : ℝ} (hαD : 0 < α * D) :
    HasDerivAt (fun q => qDrift r α D χ q (α * D / r)) (r * (1 + 1 / χ)) 1 := by
  have hfun : (fun q => qDrift r α D χ q (α * D / r)) =
      fun q => r * q - r / (1 + (q - 1) / χ) := by
    funext q
    unfold qDrift
    rw [← div_div, div_div_cancel₀ hαD.ne']
  rw [hfun]
  have h1 : HasDerivAt (fun q : ℝ => r * q) r 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).const_mul r
  have h3 : HasDerivAt (fun q : ℝ => 1 + (q - 1) / χ) (1 / χ) 1 := by
    have := (((hasDerivAt_id (1 : ℝ)).sub_const 1).div_const χ).const_add 1
    simpa using this
  have h4 : HasDerivAt (fun q : ℝ => r / (1 + (q - 1) / χ))
      ((0 * (1 + (1 - 1) / χ) - r * (1 / χ)) / (1 + (1 - 1) / χ) ^ 2) 1 :=
    (hasDerivAt_const (1 : ℝ) r).div h3 (by simp)
  refine HasDerivAt.congr_deriv (HasDerivAt.sub h1 h4) ?_
  simp
  ring

/-- **Linearisation in `K`**, O&R p. 262: at the steady state, `∂F/∂K = αD/K̄² = r/K̄`. -/
theorem hasDerivAt_qDrift_K {r α D χ : ℝ} (hr : 0 < r) (hαD : 0 < α * D) :
    HasDerivAt (fun K => qDrift r α D χ 1 K) (r / (α * D / r)) (α * D / r) := by
  have hK : 0 < α * D / r := div_pos hαD hr
  have hfun : (fun K => qDrift r α D χ 1 K) = fun K => r - α * D / K := by
    funext K
    simp [qDrift]
  rw [hfun]
  have h2 : HasDerivAt (fun K : ℝ => α * D / K) (-(α * D) / (α * D / r) ^ 2) (α * D / r) := by
    have := (hasDerivAt_inv hK.ne').const_mul (α * D)
    convert this using 1
    · funext K; ring
    · field_simp
  refine HasDerivAt.congr_deriv (HasDerivAt.sub (hasDerivAt_const _ r) h2) ?_
  field_simp
  ring

/-! ### Saddle-point stability of the linearised system -/

/-- The characteristic polynomial of `J = [[0, K̄/χ], [r/K̄, r(1 + 1/χ)]]`:
`μ² − r(1 + 1/χ)μ − r/χ`. It does not depend on `K̄`. -/
noncomputable def charPolyJ (r χ μ : ℝ) : ℝ := μ ^ 2 - r * (1 + 1 / χ) * μ - r / χ

/-- The characteristic polynomial is the determinant of `J − μI` for any `K̄ ≠ 0`. -/
theorem charPolyJ_eq_det {r χ Kb μ : ℝ} (hKb : Kb ≠ 0) :
    charPolyJ r χ μ = (0 - μ) * (r * (1 + 1 / χ) - μ) - (Kb / χ) * (r / Kb) := by
  unfold charPolyJ
  field_simp
  ring

/-- The discriminant of the characteristic polynomial is positive: the roots are real and
distinct. -/
theorem charPolyJ_disc_pos {r χ : ℝ} (hr : 0 < r) (hχ : 0 < χ) :
    0 < (r * (1 + 1 / χ)) ^ 2 + 4 * (r / χ) := by positivity

/-- **The stable root of `J` lies in `(−2, 0)`** (O&R p. 263): the characteristic polynomial is
negative at `0` (`det J = −r/χ < 0`) and positive at `−2` (`4 + 2r + r/χ > 0`), so there is a root
`μ₋ ∈ (−2, 0)`; hence `1 + μ₋ ∈ (−1, 1)` is a stable eigenvalue of `I + J`. -/
theorem stable_root_mem {r χ : ℝ} (hr : 0 < r) (hχ : 0 < χ) :
    charPolyJ r χ 0 < 0 ∧ 0 < charPolyJ r χ (-2) := by
  unfold charPolyJ
  constructor
  · have : 0 < r / χ := div_pos hr hχ
    linarith
  · have : 0 < r / χ := div_pos hr hχ
    have e : r * (1 + 1 / χ) = r + r / χ := by ring
    rw [e]
    nlinarith

/-- The two roots of the characteristic polynomial, `μ = [b ∓ √(b² + 4c)]/2` with
`b = r(1 + 1/χ)`, `c = r/χ`. -/
noncomputable def rootJ (r χ : ℝ) (sgn : ℝ) : ℝ :=
  (r * (1 + 1 / χ) + sgn * Real.sqrt ((r * (1 + 1 / χ)) ^ 2 + 4 * (r / χ))) / 2

theorem rootJ_isRoot {r χ : ℝ} (hr : 0 < r) (hχ : 0 < χ) {sgn : ℝ} (hs : sgn ^ 2 = 1) :
    charPolyJ r χ (rootJ r χ sgn) = 0 := by
  unfold charPolyJ rootJ
  have hd := charPolyJ_disc_pos hr hχ
  have hsq := Real.sq_sqrt hd.le
  nlinarith [hsq, hs]

/-- **Saddle-point stability**, O&R p. 263 and Figure 4.15: for every `r, χ > 0` the eigenvalues
of `I + J` are real, one in `(−1, 1)` (the stable root) and one above `1` (the unstable root). -/
theorem saddle_point {r χ : ℝ} (hr : 0 < r) (hχ : 0 < χ) :
    -1 < 1 + rootJ r χ (-1) ∧ 1 + rootJ r χ (-1) < 1 ∧ 1 < 1 + rootJ r χ 1 := by
  have hd := charPolyJ_disc_pos hr hχ
  set b := r * (1 + 1 / χ) with hb
  set c := r / χ with hc
  have hbpos : 0 < b := by positivity
  have hcpos : 0 < c := div_pos hr hχ
  set s := Real.sqrt (b ^ 2 + 4 * c) with hs
  have hs2 : s ^ 2 = b ^ 2 + 4 * c := Real.sq_sqrt hd.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsb : b < s := by nlinarith
  unfold rootJ
  rw [← hb, ← hc, ← hs]
  refine ⟨?_, ?_, ?_⟩
  · -- (b − s)/2 > −2  ⇔  s < b + 4  ⇔  b² + 4c < (b + 4)², i.e. c < 2b + 4 (true since b = r + c)
    have hbc : b = r + c := by rw [hb, hc]; ring
    have : s < b + 4 := by nlinarith
    linarith
  · linarith
  · linarith

end ObstfeldRogoff.RealExchangeRate.CostlyCapital

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The static Dornbusch–Fischer–Samuelson Ricardian model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.5.1–4.5.3,
pp. 235–243.

A continuum of goods `z ∈ [0,1]`; Home needs `a(z)` units of labour per unit of good `z`,
Foreign `a*(z)`. The relative productivity schedule is `A(z) = a*(z)/a(z)` (41), assumed
continuous, strictly decreasing and positive on `[0,1]`. Equal spending shares (40) are taken
as the primitive: Home's share of world spending is the measure `z̄` of the goods it produces.

* (43): goods-market clearing gives `w/w* = B(z̄; L*/L) = z̄/(1−z̄) · L*/L`;
* T20: a unique cutoff `z̄ ∈ (0,1)` with `A(z̄) = B(z̄; L*/L)` (intermediate value theorem on
  `h(z) = A(z)(1−z)L − zL*`);
* statics: a rise in `L*/L` lowers `z̄` and raises `w/w*`; a uniform fall `a* ↦ a*/ν` lowers
  `w/w*` by less than the factor `ν`;
* (44)–(45) with free trade the price of a good is its lowest unit cost, and real wages in
  terms of every good respond as described on pp. 240–243.

A small imprecision (p. 241): the book says Foreign's real wage falls strictly on every
relocated good `z ∈ (z̄', z̄]`; at the old cutoff good `z = z̄` it is unchanged (there
`wa(z̄) = w*a*(z̄)`), so the fall is strict only on `(z̄', z̄)`.
-/

namespace ObstfeldRogoff.RealExchangeRate.DFSStatic

open Set

/-- Relative Home labour productivity schedule, O&R (41), p. 238: `A(z) = a*(z)/a(z)`. -/
noncomputable def relProductivity (a aS : ℝ → ℝ) (z : ℝ) : ℝ := aS z / a z

/-- O&R (41), p. 238: if Home's requirement `a` is strictly increasing and Foreign's `a*` is
strictly decreasing (both positive), then `A = a*/a` is strictly decreasing. -/
theorem relProductivity_strictAntiOn {a aS : ℝ → ℝ} {s : Set ℝ} (ha : StrictMonoOn a s)
    (haS : StrictAntiOn aS s) (hapos : ∀ z ∈ s, 0 < a z) (haSpos : ∀ z ∈ s, 0 < aS z) :
    StrictAntiOn (relProductivity a aS) s := by
  intro x hx y hy hxy
  unfold relProductivity
  have h1 := ha hx hy hxy
  have h2 := haS hx hy hxy
  have hax := hapos x hx
  have hay := hapos y hy
  have hbx := haSpos x hx
  have hby := haSpos y hy
  rw [div_lt_div_iff₀ hay hax]
  nlinarith

/-- Pattern of specialisation, O&R p. 238: good `z` is cheaper to make in Home,
`w a(z) < w* a*(z)`, iff `w/w* < A(z) = a*(z)/a(z)`. -/
theorem home_cheaper_iff {a aS w wS : ℝ} (ha : 0 < a) (hwS : 0 < wS) :
    a * w < aS * wS ↔ w / wS < aS / a := by
  rw [div_lt_div_iff₀ hwS ha]
  constructor <;> intro h <;> linarith

/-- The relative-wage schedule, O&R (43), p. 240: `B(z; L*/L) = z/(1−z) · (L*/L)`,
written with `lam = L*/L`. -/
noncomputable def relWageSchedule (lam z : ℝ) : ℝ := z / (1 - z) * lam

/-- O&R (42)–(43), pp. 239–240: world spending equals world labour income,
`P(C + C*) = wL + w*L*` (42); with equal spending shares (40), Home's revenue from the goods
`[0, z]` is `z P C + z P C*`. Clearing of the Home-goods market then gives
`w/w* = B(z; L*/L)` (43). -/
theorem relWage_of_market_clearing {P C CS w wS L LS z : ℝ} (hwS : 0 < wS) (hL : 0 < L)
    (hz : z < 1) (h42 : P * (C + CS) = w * L + wS * LS)
    (hclear : w * L = z * (P * C) + z * (P * CS)) :
    w / wS = relWageSchedule (LS / L) z := by
  unfold relWageSchedule
  have h1 : (1 - z) ≠ 0 := by linarith
  have key : w * L * (1 - z) = z * (wS * LS) := by
    have : w * L = z * (w * L + wS * LS) := by rw [← h42]; linarith
    linarith
  field_simp
  linarith

/-- O&R (43), p. 240: `B(·; L*/L)` is strictly increasing on `[0,1)` ("upward-sloping"). -/
theorem relWageSchedule_strictMonoOn {lam : ℝ} (hlam : 0 < lam) :
    StrictMonoOn (relWageSchedule lam) (Ico 0 1) := by
  intro x hx y hy hxy
  unfold relWageSchedule
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hy1 : 0 < 1 - y := by linarith [hy.2]
  have : x / (1 - x) < y / (1 - y) := by
    rw [div_lt_div_iff₀ hx1 hy1]
    nlinarith
  exact mul_lt_mul_of_pos_right this hlam

/-- O&R p. 240 (Figure 4.10): at an interior `z`, `B(z; L*/L)` is strictly increasing in
`L*/L`, so a rise in relative Foreign labour shifts the schedule inward. -/
theorem relWageSchedule_lt_of_lam_lt {lam lam' z : ℝ} (hz : z ∈ Ioo 0 1) (h : lam < lam') :
    relWageSchedule lam z < relWageSchedule lam' z := by
  unfold relWageSchedule
  have : 0 < z / (1 - z) := div_pos hz.1 (by linarith [hz.2])
  exact mul_lt_mul_of_pos_left h this

/-- The cutoff gap used for T20 (O&R p. 240): `h(z) = A(z)(1−z)L − zL*`; on `(0,1)` its zeros
are exactly the intersections `A(z) = B(z; L*/L)`. -/
def cutoffGap (A : ℝ → ℝ) (L LS z : ℝ) : ℝ := A z * (1 - z) * L - z * LS

/-- O&R p. 240: on `(0,1)`, `h(z) = 0` iff `A(z) = B(z; L*/L)`. -/
theorem cutoffGap_eq_zero_iff {A : ℝ → ℝ} {L LS z : ℝ} (hL : 0 < L) (hz : z ∈ Ioo 0 1) :
    cutoffGap A L LS z = 0 ↔ A z = relWageSchedule (LS / L) z := by
  unfold cutoffGap relWageSchedule
  have h1 : (1 - z) ≠ 0 := by linarith [hz.2]
  have hL' : L ≠ 0 := hL.ne'
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    field_simp at h
    linarith

/-- O&R p. 240: with `A` strictly decreasing and positive on `[0,1]`, the cutoff gap `h` is
strictly decreasing on `[0,1]`. -/
theorem cutoffGap_strictAntiOn {A : ℝ → ℝ} {L LS : ℝ} (hA : StrictAntiOn A (Icc 0 1))
    (hpos : ∀ z ∈ Icc (0 : ℝ) 1, 0 < A z) (hL : 0 < L) (hLS : 0 < LS) :
    StrictAntiOn (cutoffGap A L LS) (Icc 0 1) := by
  intro x hx y hy hxy
  unfold cutoffGap
  have hAxy := hA hx hy hxy
  have hAy := hpos y hy
  have hx1 : 0 < 1 - x := by linarith [hy.2]
  have hy1 : 0 ≤ 1 - y := by linarith [hy.2]
  have e1 : A y * (1 - y) ≤ A y * (1 - x) := mul_le_mul_of_nonneg_left (by linarith) hAy.le
  have e2 : A y * (1 - x) < A x * (1 - x) := mul_lt_mul_of_pos_right hAxy hx1
  have e3 : A y * (1 - y) * L < A x * (1 - x) * L := mul_lt_mul_of_pos_right (by linarith) hL
  have e4 : x * LS < y * LS := mul_lt_mul_of_pos_right hxy hLS
  linarith

/-- T20, O&R p. 240 (Figure 4.9): if `A` is continuous, strictly decreasing and positive on
`[0,1]` and `L, L* > 0`, there is a unique cutoff `z̄ ∈ (0,1)` with `A(z̄) = B(z̄; L*/L)`;
the equilibrium relative wage is `w/w* = A(z̄)`. -/
theorem cutoff_exists_unique {A : ℝ → ℝ} {L LS : ℝ} (hAc : ContinuousOn A (Icc 0 1))
    (hA : StrictAntiOn A (Icc 0 1)) (hpos : ∀ z ∈ Icc (0 : ℝ) 1, 0 < A z) (hL : 0 < L)
    (hLS : 0 < LS) : ∃! z, z ∈ Ioo (0 : ℝ) 1 ∧ A z = relWageSchedule (LS / L) z := by
  have hcont : ContinuousOn (cutoffGap A L LS) (Icc 0 1) := by
    unfold cutoffGap
    fun_prop
  have h0 : cutoffGap A L LS 0 = A 0 * L := by unfold cutoffGap; ring
  have h1 : cutoffGap A L LS 1 = -LS := by unfold cutoffGap; ring
  have hA0 : 0 < A 0 := hpos 0 ⟨le_rfl, zero_le_one⟩
  have hmem : (0 : ℝ) ∈ Icc (cutoffGap A L LS 1) (cutoffGap A L LS 0) := by
    rw [h0, h1]
    constructor
    · linarith
    · positivity
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' zero_le_one hcont hmem
  have hzne0 : z ≠ 0 := by
    rintro rfl
    rw [h0] at hz0
    have : 0 < A 0 * L := by positivity
    linarith
  have hzne1 : z ≠ 1 := by
    rintro rfl
    rw [h1] at hz0
    linarith
  have hzI : z ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hz.1 (Ne.symm hzne0), lt_of_le_of_ne hz.2 hzne1⟩
  refine ⟨z, ⟨hzI, (cutoffGap_eq_zero_iff hL hzI).1 hz0⟩, ?_⟩
  rintro y ⟨hyI, hy⟩
  have hy0 : cutoffGap A L LS y = 0 := (cutoffGap_eq_zero_iff hL hyI).2 hy
  exact (cutoffGap_strictAntiOn hA hpos hL hLS).injOn (Ioo_subset_Icc_self hyI) hz
    (by rw [hy0, hz0])

/-- O&R p. 239: with `w/w* = A(z̄)`, a good `z ∈ [0,1]` is (weakly) cheaper at Home,
`w/w* ≤ A(z)`, iff `z ≤ z̄`: Home produces exactly `[0, z̄]`. -/
theorem home_produces_iff {A : ℝ → ℝ} {z zbar : ℝ} (hA : StrictAntiOn A (Icc 0 1))
    (hz : z ∈ Icc (0 : ℝ) 1) (hzbar : zbar ∈ Icc (0 : ℝ) 1) : A zbar ≤ A z ↔ z ≤ zbar :=
  hA.le_iff_ge hzbar hz

/-- Comparative statics, O&R p. 240 (Figure 4.10): a rise in relative Foreign labour supply
`L*/L` (from `lam` to `lam'`) lowers the cutoff and raises the relative Home wage:
`z̄' < z̄` and `w/w* = A(z̄) < A(z̄') = w'/w*'`. -/
theorem labour_rise_statics {A : ℝ → ℝ} {lam lam' z z' : ℝ} (hA : StrictAntiOn A (Icc 0 1))
    (hlam : 0 < lam) (hlam' : lam < lam') (hz : z ∈ Ioo (0 : ℝ) 1) (hz' : z' ∈ Ioo (0 : ℝ) 1)
    (heq : A z = relWageSchedule lam z) (heq' : A z' = relWageSchedule lam' z') :
    z' < z ∧ A z < A z' := by
  have hlt : z' < z := by
    by_contra hcon
    push Not at hcon
    have h1 : A z' ≤ A z := hA.antitoneOn (Ioo_subset_Icc_self hz) (Ioo_subset_Icc_self hz') hcon
    have h2 : relWageSchedule lam z ≤ relWageSchedule lam z' :=
      (relWageSchedule_strictMonoOn hlam).monotoneOn ⟨hz.1.le, hz.2⟩ ⟨hz'.1.le, hz'.2⟩ hcon
    have h3 := relWageSchedule_lt_of_lam_lt hz' hlam'
    linarith
  exact ⟨hlt, hA (Ioo_subset_Icc_self hz') (Ioo_subset_Icc_self hz) hlt⟩

/-- Comparative statics, O&R p. 242: a uniform proportional fall in Foreign unit labour
requirements, `a*(z) ↦ a*(z)/ν` with `ν > 1`, shifts `A` down to `A/ν`. The new cutoff `z̄'`
(solving `A(z̄')/ν = B(z̄'; L*/L)`) satisfies `z̄' < z̄`, and the relative Home wage falls, but by
less than the factor `ν`: `A(z̄)/ν < A(z̄')/ν < A(z̄)`. -/
theorem productivity_rise_statics {A : ℝ → ℝ} {ν lam z z' : ℝ}
    (hA : StrictAntiOn A (Icc 0 1)) (hpos : ∀ z ∈ Icc (0 : ℝ) 1, 0 < A z) (hν : 1 < ν)
    (hlam : 0 < lam) (hz : z ∈ Ioo (0 : ℝ) 1) (hz' : z' ∈ Ioo (0 : ℝ) 1)
    (heq : A z = relWageSchedule lam z) (heq' : A z' / ν = relWageSchedule lam z') :
    z' < z ∧ A z / ν < A z' / ν ∧ A z' / ν < A z := by
  have hν0 : 0 < ν := by linarith
  have hlt : z' < z := by
    by_contra hcon
    push Not at hcon
    have h1 : A z' ≤ A z := hA.antitoneOn (Ioo_subset_Icc_self hz) (Ioo_subset_Icc_self hz') hcon
    have h2 : relWageSchedule lam z ≤ relWageSchedule lam z' :=
      (relWageSchedule_strictMonoOn hlam).monotoneOn ⟨hz.1.le, hz.2⟩ ⟨hz'.1.le, hz'.2⟩ hcon
    have hAz' := hpos z' (Ioo_subset_Icc_self hz')
    have h3 : A z' / ν < A z' := div_lt_self hAz' hν
    linarith
  have hAlt : A z < A z' := hA (Ioo_subset_Icc_self hz') (Ioo_subset_Icc_self hz) hlt
  refine ⟨hlt, div_lt_div_of_pos_right hAlt hν0, ?_⟩
  rw [heq, heq']
  exact relWageSchedule_strictMonoOn hlam ⟨hz'.1.le, hz'.2⟩ ⟨hz.1.le, hz.2⟩ hlt

/-- Free-trade price of a good, O&R (44)–(45), p. 241: with no transport costs the good is
made where it is cheapest, so its price is `min (a w) (a* w*)` (`a`, `aS` are the unit labour
requirements for this good). -/
noncomputable def freeTradePrice (a aS w wS : ℝ) : ℝ := min (a * w) (aS * wS)

/-- O&R (44), p. 241: for a good Home produces (`w/w* ≤ A = a*/a`), `p = a w`. -/
theorem freeTradePrice_home {a aS w wS : ℝ} (ha : 0 < a) (hwS : 0 < wS)
    (h : w / wS ≤ aS / a) : freeTradePrice a aS w wS = a * w := by
  unfold freeTradePrice
  rw [div_le_div_iff₀ hwS ha] at h
  exact min_eq_left (by linarith)

/-- O&R (45), p. 241: for a good Foreign produces (`A = a*/a ≤ w/w*`), `p = a* w*`. -/
theorem freeTradePrice_foreign {a aS w wS : ℝ} (ha : 0 < a) (hwS : 0 < wS)
    (h : aS / a ≤ w / wS) : freeTradePrice a aS w wS = aS * wS := by
  unfold freeTradePrice
  rw [div_le_div_iff₀ ha hwS] at h
  exact min_eq_right (by linarith)

/-- O&R pp. 240–242: Home's real wage in terms of a good, `w/p = max (1/a) ((w/w*)/a*)`. -/
theorem homeRealWage_eq {a aS w wS : ℝ} (ha : 0 < a) (haS : 0 < aS) (hw : 0 < w)
    (hwS : 0 < wS) : w / freeTradePrice a aS w wS = max (1 / a) (w / wS / aS) := by
  unfold freeTradePrice
  rcases le_total (a * w) (aS * wS) with h | h
  · rw [min_eq_left h]
    have : w / wS / aS ≤ 1 / a := by
      rw [div_div, div_le_div_iff₀ (by positivity) ha]
      linarith
    rw [max_eq_left this]
    field_simp
  · rw [min_eq_right h]
    have : 1 / a ≤ w / wS / aS := by
      rw [div_div, div_le_div_iff₀ ha (by positivity)]
      linarith
    rw [max_eq_right this]
    field_simp

/-- O&R pp. 240–242: Foreign's real wage in terms of a good,
`w*/p = max ((w*/w)/a) (1/a*)`. -/
theorem foreignRealWage_eq {a aS w wS : ℝ} (ha : 0 < a) (haS : 0 < aS) (hw : 0 < w)
    (hwS : 0 < wS) : wS / freeTradePrice a aS w wS = max (wS / w / a) (1 / aS) := by
  unfold freeTradePrice
  rcases le_total (a * w) (aS * wS) with h | h
  · rw [min_eq_left h]
    have : 1 / aS ≤ wS / w / a := by
      rw [div_div, div_le_div_iff₀ haS (by positivity)]
      linarith
    rw [max_eq_left this]
    field_simp
  · rw [min_eq_right h]
    have : wS / w / a ≤ 1 / aS := by
      rw [div_div, div_le_div_iff₀ (by positivity) haS]
      linarith
    rw [max_eq_right this]
    field_simp

/-- T21(a), O&R (44), p. 241: after a rise in `L*/L` (so `w'/w*' > w/w*`), Home's real wage
is unchanged in terms of every good Home still produces (`w'/w*' ≤ A = a*/a`). -/
theorem labour_rise_home_realWage_own {a aS w wS w' wS' : ℝ} (ha : 0 < a) (haS : 0 < aS)
    (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w') (hwS' : 0 < wS')
    (hrise : w / wS < w' / wS') (hhome : w' / wS' ≤ aS / a) :
    w' / freeTradePrice a aS w' wS' = w / freeTradePrice a aS w wS := by
  rw [homeRealWage_eq ha haS hw hwS, homeRealWage_eq ha haS hw' hwS']
  have e : aS / a / aS = 1 / a := by field_simp
  have h1 : w' / wS' / aS ≤ 1 / a := by
    rw [← e]; exact div_le_div_of_nonneg_right hhome haS.le
  have h2 : w / wS / aS ≤ 1 / a := by
    rw [← e]; exact div_le_div_of_nonneg_right (by linarith) haS.le
  rw [max_eq_left h1, max_eq_left h2]

/-- T21(b), O&R p. 241: after a rise in `L*/L`, Home's real wage rises strictly in terms of
every good Foreign produces afterwards (`A = a*/a < w'/w*'`): both the goods Foreign kept and
the goods relocated from Home. -/
theorem labour_rise_home_realWage_other {a aS w wS w' wS' : ℝ} (ha : 0 < a) (haS : 0 < aS)
    (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w') (hwS' : 0 < wS')
    (hrise : w / wS < w' / wS') (hforeign : aS / a < w' / wS') :
    w / freeTradePrice a aS w wS < w' / freeTradePrice a aS w' wS' := by
  rw [homeRealWage_eq ha haS hw hwS, homeRealWage_eq ha haS hw' hwS']
  have e : aS / a / aS = 1 / a := by field_simp
  have h1 : 1 / a < w' / wS' / aS := by
    rw [← e]; exact div_lt_div_of_pos_right hforeign haS
  have h2 : w / wS / aS < w' / wS' / aS := div_lt_div_of_pos_right hrise haS
  exact lt_of_lt_of_le (max_lt h1 h2) (le_max_right _ _)

/-- T21(c), O&R p. 241: after a rise in `L*/L`, Foreign's real wage falls strictly in terms of
every good Home still produces (`w'/w*' ≤ A = a*/a`). -/
theorem labour_rise_foreign_realWage_homeGoods {a aS w wS w' wS' : ℝ} (ha : 0 < a)
    (haS : 0 < aS) (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w') (hwS' : 0 < wS')
    (hrise : w / wS < w' / wS') (hhome : w' / wS' ≤ aS / a) :
    wS' / freeTradePrice a aS w' wS' < wS / freeTradePrice a aS w wS := by
  rw [foreignRealWage_eq ha haS hw hwS, foreignRealWage_eq ha haS hw' hwS']
  have hr : wS' / w' < wS / w := by
    rw [div_lt_div_iff₀ hw' hw]; rw [div_lt_div_iff₀ hwS hwS'] at hrise; linarith
  have h1 : 1 / aS ≤ wS' / w' / a := by
    rw [div_le_div_iff₀ hwS' ha] at hhome
    rw [div_div, div_le_div_iff₀ haS (by positivity)]
    linarith
  rw [max_eq_left h1]
  exact lt_of_lt_of_le (div_lt_div_of_pos_right hr ha) (le_max_left _ _)

/-- T21(d), O&R (45), p. 241: after a rise in `L*/L`, Foreign's real wage is unchanged in
terms of the goods Foreign already produced (`A = a*/a ≤ w/w*`). -/
theorem labour_rise_foreign_realWage_own {a aS w wS w' wS' : ℝ} (ha : 0 < a) (haS : 0 < aS)
    (hwS : 0 < wS) (hwS' : 0 < wS')
    (hrise : w / wS < w' / wS') (hforeign : aS / a ≤ w / wS) :
    wS' / freeTradePrice a aS w' wS' = wS / freeTradePrice a aS w wS := by
  rw [freeTradePrice_foreign ha hwS hforeign, freeTradePrice_foreign ha hwS' (by linarith)]
  field_simp

/-- T21(e), O&R p. 242: after a rise in `L*/L`, Foreign's real wage falls strictly in terms of
the relocated goods that Home produced strictly more cheaply before (`w/w* < A`) and Foreign
produces afterwards (`A ≤ w'/w*'`). (At the old cutoff good itself, `w/w* = A`, it is
unchanged: the book's strict inequality on `(z̄', z̄]` fails at `z̄`.) -/
theorem labour_rise_foreign_realWage_relocated {a aS w wS w' wS' : ℝ} (ha : 0 < a)
    (haS : 0 < aS) (hw : 0 < w) (hwS : 0 < wS) (hwS' : 0 < wS')
    (hbefore : w / wS < aS / a) (hafter : aS / a ≤ w' / wS') :
    wS' / freeTradePrice a aS w' wS' < wS / freeTradePrice a aS w wS := by
  rw [freeTradePrice_foreign ha hwS' hafter, freeTradePrice_home ha hwS hbefore.le]
  rw [div_lt_div_iff₀ hwS ha] at hbefore
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- O&R p. 242 ("Show this result"): after the Foreign productivity rise `a* ↦ a*/ν` (with the
relative Home wage falling by less than the factor `ν`, `w/w* ≤ ν · w'/w*'`), Home's real wage
rises weakly in terms of every good. -/
theorem productivity_rise_home_realWage {a aS w wS w' wS' ν : ℝ} (ha : 0 < a)
    (haS : 0 < aS) (hν : 0 < ν) (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w') (hwS' : 0 < wS')
    (hless : w / wS ≤ ν * (w' / wS')) :
    w / freeTradePrice a aS w wS ≤ w' / freeTradePrice a (aS / ν) w' wS' := by
  rw [homeRealWage_eq ha haS hw hwS, homeRealWage_eq ha (by positivity) hw' hwS']
  have e : w' / wS' / (aS / ν) = ν * (w' / wS') / aS := by field_simp
  rw [e]
  exact max_le_max le_rfl (div_le_div_of_nonneg_right hless haS.le)

/-- O&R p. 242: after the Foreign productivity rise `a* ↦ a*/ν`, `ν ≥ 1`, with the relative
Home wage falling (`w'/w*' ≤ w/w*`), Foreign's real wage rises weakly in terms of every good. -/
theorem productivity_rise_foreign_realWage {a aS w wS w' wS' ν : ℝ} (ha : 0 < a)
    (haS : 0 < aS) (hν : 1 ≤ ν) (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w') (hwS' : 0 < wS')
    (hfall : w' / wS' ≤ w / wS) :
    wS / freeTradePrice a aS w wS ≤ wS' / freeTradePrice a (aS / ν) w' wS' := by
  rw [foreignRealWage_eq ha haS hw hwS, foreignRealWage_eq ha (by positivity) hw' hwS']
  have hr : wS / w ≤ wS' / w' := by
    rw [div_le_div_iff₀ hw hw']; rw [div_le_div_iff₀ hwS' hwS] at hfall; linarith
  have e : 1 / (aS / ν) = ν / aS := by field_simp
  rw [e]
  exact max_le_max (div_le_div_of_nonneg_right hr ha.le)
    (div_le_div_of_nonneg_right hν haS.le)

end ObstfeldRogoff.RealExchangeRate.DFSStatic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The current account in the Ricardian model: temporary productivity shocks

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.5.4,
pp. 243–248, and end-of-chapter Exercise 7, p. 266.

Bonds are indexed to the real consumption index. The current-account identities (46)–(47),
the Euler equation (48) (derived here as the first-order condition of the two-period slice of
(37)), the steady-state interest rate `r̄ = (1−β)/β` and steady-state consumption (49) are
exact. The response to a one-period, uniform Foreign productivity rise `a* ↦ a*/ν` is the
book's log-linear system: equations (50)–(54), footnote 37 and the two log-differentiated
cutoff conditions are collected as the hypotheses of `TemporaryShock` (the coefficients `4`,
`A′(1/2)` and `1 − β` are justified by exact derivative lemmas below), and (55)–(59), "half the
annuity value" and the Exercise 7 welfare results are derived from them.

Exercise 7: Home's lifetime-utility change is `dU = −A′(1/2)ν̂/(8 − 2A′(1/2))`, positive iff
`A′(1/2) < 0`; Foreign's is `ν̂/2 + ν̂/(2 − A′(1/2)/2) > 0`.
-/

namespace ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount

open ObstfeldRogoff.RealExchangeRate.DFSStatic

/-- The steady-state world real interest rate, O&R p. 244: `r̄ = (1−β)/β`. -/
noncomputable def steadyRate (β : ℝ) : ℝ := (1 - β) / β

/-- The Home current account, O&R (46), p. 243, in units of the real consumption index:
`CA_t = w_t L / P_t + r_t B_t − C_t` (Foreign's (47) is the same map at starred arguments). -/
noncomputable def currentAccount (w L P r B C : ℝ) : ℝ := w * L / P + r * B - C

/-- O&R (46)–(47), p. 243: if bonds are in zero net supply (`B* = −B`) and world spending
equals world labour income (42), `P(C + C*) = wL + w*L*`, then `CA = −CA*`. -/
theorem currentAccount_home_eq_neg_foreign {w wS L LS P r B BS C CS : ℝ} (hP : P ≠ 0)
    (hB : BS = -B) (h42 : P * (C + CS) = w * L + wS * LS) :
    currentAccount w L P r B C = -currentAccount wS LS P r BS CS := by
  unfold currentAccount
  subst hB
  have : C + CS = (w * L + wS * LS) / P := by
    rw [← h42]; field_simp
  have e : w * L / P + wS * LS / P = C + CS := by rw [this]; ring
  linarith

/-- Euler equation (48), O&R p. 244: substituting (46) into (37), the two terms of `U_t` that
involve `B_{t+1} = b` are `log((1+r_t)B_t + y_t − b) + β log((1+r_{t+1})b − B_{t+2} + y_{t+1})`
(with `y = wL/P`); its derivative in `b` is `−1/C_t + β(1+r_{t+1})/C_{t+1}`. -/
theorem euler_objective_hasDerivAt {β r r' B B'' y y' b : ℝ}
    (hC : 0 < (1 + r) * B + y - b) (hC' : 0 < (1 + r') * b - B'' + y') :
    HasDerivAt
      (fun x => Real.log ((1 + r) * B + y - x) + β * Real.log ((1 + r') * x - B'' + y'))
      (-1 / ((1 + r) * B + y - b) + β * ((1 + r') / ((1 + r') * b - B'' + y'))) b := by
  have h1 : HasDerivAt (fun x => (1 + r) * B + y - x) (-1) b := by
    simpa using (hasDerivAt_id b).const_sub ((1 + r) * B + y)
  have h2 : HasDerivAt (fun x => (1 + r') * x - B'' + y') (1 + r') b := by
    have := ((hasDerivAt_id b).const_mul (1 + r')).sub_const B''
    simpa using this.add_const y'
  exact HasDerivAt.add (h1.log hC.ne') ((h2.log hC'.ne').const_mul β)

/-- Euler equation (48), O&R p. 244: the first-order condition
`−1/C_t + β(1+r_{t+1})/C_{t+1} = 0` holds iff `C_{t+1} = (1 + r_{t+1}) β C_t`. -/
theorem euler_foc_iff {β r' C C' : ℝ} (hC : 0 < C) (hC' : 0 < C') :
    -1 / C + β * ((1 + r') / C') = 0 ↔ C' = (1 + r') * β * C := by
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    have hk : (1 + r') * β ≠ 0 := by
      intro h0; rw [h, h0, zero_mul] at hC'; exact lt_irrefl 0 hC'
    have h1 : 1 + r' ≠ 0 := left_ne_zero_of_mul hk
    have h2 : β ≠ 0 := right_ne_zero_of_mul hk
    rw [h]
    field_simp
    ring

/-- Steady-state interest rate, O&R p. 244: with constant positive consumption, the Euler
equation (48) holds iff `r = r̄ = (1−β)/β`. -/
theorem steady_rate_iff {β r C : ℝ} (hβ : 0 < β) (hC : 0 < C) :
    C = (1 + r) * β * C ↔ r = steadyRate β := by
  unfold steadyRate
  constructor
  · intro h
    have h1 : (1 + r) * β = 1 := by
      have := congrArg (· / C) h
      field_simp at this
      linarith
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Steady-state consumption, O&R (49), p. 244: in a steady state (`B_{t+1} = B_t = B̄`,
`r = r̄`), (46) gives `C̄ = r̄B̄ + w̄L/P̄`, and with `B̄* = −B̄`, `C̄* = −r̄B̄ + w̄*L*/P̄`. -/
theorem steady_consumption {β w wS L LS P B C CS : ℝ}
    (hCA : currentAccount w L P (steadyRate β) B C = 0)
    (hCAS : currentAccount wS LS P (steadyRate β) (-B) CS = 0) :
    C = steadyRate β * B + w * L / P ∧ CS = -(steadyRate β * B) + wS * LS / P := by
  unfold currentAccount at hCA hCAS
  constructor <;> linarith

/-- O&R (50), p. 245: steady-state wages and prices do not depend on the distribution of
wealth, so between two steady states with the same `w̄L/P̄`, (49) gives exactly
`dC̄ = r̄ dB̄`; starting from `B̄₀ = 0`, `Ĉ̄ = dC̄/C̄₀ = r̄ dB̄/C̄₀`. -/
theorem steady_consumption_change {β y B1 C0 C1 : ℝ} (hC0 : C0 = steadyRate β * 0 + y)
    (hC1 : C1 = steadyRate β * B1 + y) :
    (C1 - C0) / C0 = steadyRate β * B1 / C0 := by
  rw [show C1 - C0 = steadyRate β * B1 by rw [hC1, hC0]; ring]

/-- O&R (51), p. 245: the log of the Euler equation (48),
`log C_{t+1} = log(1 + r_{t+1}) + log β + log C_t`. -/
theorem log_euler {β r C C' : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r) (hC : 0 < C)
    (h : C' = (1 + r) * β * C) :
    Real.log C' = Real.log (1 + r) + Real.log β + Real.log C := by
  rw [h, Real.log_mul (by positivity) hC.ne', Real.log_mul hr.ne' hβ.ne']

/-- O&R (51), p. 245: `d log(1+r)` at `r̄` is `dr/(1+r̄)`. -/
theorem log_one_add_rate_hasDerivAt {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (fun r => Real.log (1 + r)) (1 / (1 + steadyRate β)) (steadyRate β) := by
  have hpos : 0 < 1 + steadyRate β := by
    unfold steadyRate
    rw [show 1 + (1 - β) / β = 1 / β by field_simp; ring]
    positivity
  have h := ((hasDerivAt_id (steadyRate β)).const_add 1).log hpos.ne'
  simpa using h

/-- O&R (51), p. 245: `dr/(1+r̄) = (1−β) r̂` with `r̂ = dr/r̄`, because `r̄/(1+r̄) = 1 − β`. -/
theorem steadyRate_div_one_add {β : ℝ} (hβ : 0 < β) :
    steadyRate β / (1 + steadyRate β) = 1 - β := by
  unfold steadyRate
  field_simp
  ring

/-- O&R p. 245: with `L = L*` and `A(1/2) = 1`, the symmetric initial cutoff is `z̄₀ = 1/2`:
it solves `A(z) = B(z; L*/L)`, and by T20 it is the unique cutoff. -/
theorem symmetric_cutoff {A : ℝ → ℝ} {L : ℝ} (hAc : ContinuousOn A (Set.Icc 0 1))
    (hA : StrictAntiOn A (Set.Icc 0 1)) (hpos : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 < A z)
    (hL : 0 < L) (hhalf : A (1 / 2) = 1) {z : ℝ} (hz : z ∈ Set.Ioo (0 : ℝ) 1)
    (heq : A z = relWageSchedule (L / L) z) : z = 1 / 2 := by
  have hsol : A (1 / 2) = relWageSchedule (L / L) (1 / 2) := by
    rw [hhalf, relWageSchedule, div_self hL.ne']; norm_num
  obtain ⟨z0, _, huniq⟩ := cutoff_exists_unique hAc hA hpos hL hL
  rw [huniq z ⟨hz, heq⟩, huniq (1 / 2) ⟨by norm_num, hsol⟩]

/-- O&R p. 247: log-differentiating (43) at the symmetric point (`z = 1/2`, `L = L*`):
`d log(z/(1−z)) = 4 dz`. -/
theorem log_odds_hasDerivAt_half :
    HasDerivAt (fun z => Real.log (z / (1 - z))) 4 (1 / 2) := by
  have h1 : HasDerivAt (fun z : ℝ => 1 - z) (-1) (1 / 2) := by
    simpa using (hasDerivAt_id (1 / 2 : ℝ)).const_sub 1
  have h2 : HasDerivAt (fun z : ℝ => z / (1 - z)) 4 (1 / 2) := by
    have := (hasDerivAt_id' (1 / 2 : ℝ)).div h1 (by norm_num)
    convert this using 1
    norm_num
  have h3 := h2.log (by norm_num)
  convert h3 using 1
  norm_num

/-- O&R p. 247: log-differentiating `w/w* = A(z̄)/ν` at `z̄ = 1/2`, `ν = 1`, with `A(1/2) = 1`:
`d log A(z̄) = A′(1/2) dz̄` and `d log(1/ν) = −ν̂`, so `ŵ − ŵ* = −ν̂ + A′(1/2) dz̄`. -/
theorem log_relProductivity_hasDerivAt_half {A : ℝ → ℝ} {A1 : ℝ}
    (hA : HasDerivAt A A1 (1 / 2)) (hhalf : A (1 / 2) = 1) :
    HasDerivAt (fun z => Real.log (A z)) A1 (1 / 2) ∧
      HasDerivAt (fun ν => Real.log (1 / ν)) (-1) 1 := by
  constructor
  · have h := hA.log (by rw [hhalf]; norm_num)
    rw [hhalf, div_one] at h
    exact h
  · have h := (hasDerivAt_inv (x := (1 : ℝ)) one_ne_zero).log (by norm_num)
    simpa using h

/-- Lifetime utility on the path of §4.5.4.2, O&R (37), p. 244: consumption `c₀` in the shock
period, then the new steady-state level `c̄` forever: `U = log c₀ + Σ_{s≥1} β^s log c̄`. -/
noncomputable def shockPathUtility (β c0 cbar : ℝ) : ℝ :=
  Real.log c0 + ∑' s : ℕ, β ^ (s + 1) * Real.log cbar

/-- O&R Exercise 7, p. 266: `Σ_{s≥1} β^s = β/(1−β) = 1/r̄`, so
`U = log c₀ + (1/r̄) log c̄` and the utility change is exactly
`dU = d log C + d log C̄ / r̄` (log differences). -/
theorem shockPathUtility_eq {β c0 cbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    shockPathUtility β c0 cbar = Real.log c0 + Real.log cbar / steadyRate β := by
  unfold shockPathUtility steadyRate
  have hs : ∑' s : ℕ, β ^ (s + 1) * Real.log cbar = β / (1 - β) * Real.log cbar := by
    simp_rw [pow_succ, mul_assoc]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0.le hβ1]
    have : (1 - β) ≠ 0 := by linarith
    field_simp
  rw [hs]
  have : (1 - β) ≠ 0 := by linarith
  field_simp

/-- The log-linear system of O&R §4.5.4.2, pp. 245–247, for an unexpected one-period Foreign
productivity rise `a* ↦ a*/ν` from the symmetric steady state (`L = L*`, `A(1/2) = 1`,
`z̄₀ = 1/2`, `B̄₀ = 0`). Hats are percentage deviations; `dB` is `dB̄/C̄₀`; `A1 = A′(1/2)`,
`ν = ν̂`. The fields are the book's equations (50)–(54), footnote 37's differential of (46),
and the log-differentials of `w/w* = A(z̄)/ν` and of (43). -/
structure TemporaryShock where
  β : ℝ
  A1 : ℝ
  ν : ℝ
  C : ℝ
  CS : ℝ
  Cbar : ℝ
  CSbar : ℝ
  r : ℝ
  w : ℝ
  wS : ℝ
  P : ℝ
  dz : ℝ
  dB : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  eq50 : Cbar = (1 - β) / β * dB
  eq50S : CSbar = -((1 - β) / β * dB)
  eq51 : Cbar = (1 - β) * r + C
  eq52 : CSbar = (1 - β) * r + CS
  eq53 : (C + CS) / 2 = (w + wS) / 2 - P
  eq54 : P = (w + wS) / 2 - ν / 2
  fn37 : dB = w - P - C
  cutoffA : w - wS = -ν + A1 * dz
  cutoff43 : w - wS = 4 * dz

namespace TemporaryShock

/-- O&R p. 244: `1 + r̄ = 1/β > 0` along the system's discount factor. -/
theorem one_add_steadyRate_pos (s : TemporaryShock) : 0 < 1 + steadyRate s.β := by
  have hβ := s.β_pos
  have hβ1 := s.β_lt_one
  have : 0 < steadyRate s.β := div_pos (by linarith) hβ
  linarith

/-- O&R p. 246: world consumption rises by the percentage increase in world productivity,
`(Ĉ + Ĉ*)/2 = ν̂/2`. -/
theorem world_consumption (s : TemporaryShock) : (s.C + s.CS) / 2 = s.ν / 2 := by
  have := s.eq53; have := s.eq54; linarith

/-- O&R p. 246: adding (51) and (52) with `dC̄ + dC̄* = 0`, `2(1−β) r̂ = −(Ĉ + Ĉ*) = −ν̂`. -/
theorem rate_relation (s : TemporaryShock) : (1 - s.β) * s.r = -s.ν / 2 := by
  have h1 := s.eq50; have h2 := s.eq50S; have h3 := s.eq51; have h4 := s.eq52
  have hw := s.world_consumption
  linarith

/-- O&R (55), p. 246: the world real interest rate falls, `r̂ = −ν̂/(2(1−β))`. -/
theorem eq55 (s : TemporaryShock) : s.r = -s.ν / (2 * (1 - s.β)) := by
  have hb : 2 * (1 - s.β) ≠ 0 := by linarith [s.β_lt_one]
  rw [eq_div_iff hb]
  linear_combination 2 * s.rate_relation

/-- O&R (56), p. 247: `dB̄/C̄₀ = (ŵ − ŵ* + ν̂)/2 − Ĉ`. -/
theorem eq56 (s : TemporaryShock) : s.dB = (s.w - s.wS + s.ν) / 2 - s.C := by
  have := s.fn37; have := s.eq54; linarith

/-- O&R p. 247: combining the two log-differentiated cutoff conditions,
`(4 − A′(1/2)) dz̄ = −ν̂`. -/
theorem cutoff_relation (s : TemporaryShock) : s.dz * (4 - s.A1) = -s.ν := by
  linear_combination s.cutoffA - s.cutoff43

/-- O&R p. 247: the cutoff moves by `dz̄ = −ν̂/(4 − A′(1/2))`. -/
theorem cutoff_change (s : TemporaryShock) (hA : s.A1 ≠ 4) : s.dz = -s.ν / (4 - s.A1) := by
  have h4 : (4 - s.A1) ≠ 0 := sub_ne_zero.mpr (Ne.symm hA)
  rw [eq_div_iff h4]
  exact s.cutoff_relation

/-- O&R (57), p. 247: `ŵ − ŵ* = −ν̂/(1 − A′(1/2)/4)`: Home's relative wage falls, but by less
than `ν̂` when `A′(1/2) < 0`. -/
theorem eq57 (s : TemporaryShock) (hA : s.A1 ≠ 4) :
    s.w - s.wS = -s.ν / (1 - s.A1 / 4) := by
  have h4' : (1 - s.A1 / 4) ≠ 0 := by
    intro h; apply hA; linarith
  rw [eq_div_iff h4']
  linear_combination (1 - s.A1 / 4) * s.cutoff43 + s.cutoff_relation

/-- O&R p. 248 (first display): substituting (51) and (57) into (56),
`dB̄/C̄₀ = −A′(1/2)ν̂/(8 − 2A′(1/2)) − Ĉ̄ + (1−β) r̂`. -/
theorem eq58_pre (s : TemporaryShock) (hA : s.A1 ≠ 4) :
    s.dB = -s.A1 * s.ν / (8 - 2 * s.A1) - s.Cbar + (1 - s.β) * s.r := by
  have h56 := s.eq56
  have h51 := s.eq51
  have h8 : (8 - 2 * s.A1) ≠ 0 := by intro h; apply hA; linarith
  have e : (s.w - s.wS + s.ν) / 2 = -s.A1 * s.ν / (8 - 2 * s.A1) := by
    rw [eq_div_iff h8]
    linear_combination (4 - s.A1) * s.cutoff43 + 4 * s.cutoff_relation
  linarith

/-- O&R p. 248: `(1 + r̄) dB̄/C̄₀ = (ŵ − ŵ*)/2`. -/
theorem bond_relation (s : TemporaryShock) : s.dB * (1 + steadyRate s.β) = (s.w - s.wS) / 2 := by
  have h56 := s.eq56
  have h51 := s.eq51
  have h50 := s.eq50
  have hr := s.rate_relation
  unfold steadyRate
  linarith

/-- O&R (58), p. 248: `dB̄/C̄₀ = −ν̂/((1 + r̄)[2 − A′(1/2)/2])`. -/
theorem eq58 (s : TemporaryShock) (hA : s.A1 ≠ 4) :
    s.dB = -s.ν / ((1 + steadyRate s.β) * (2 - s.A1 / 2)) := by
  have h2 : (2 - s.A1 / 2) ≠ 0 := by intro h; apply hA; linarith
  have hden : (1 + steadyRate s.β) * (2 - s.A1 / 2) ≠ 0 :=
    mul_ne_zero s.one_add_steadyRate_pos.ne' h2
  rw [eq_div_iff hden]
  linear_combination (2 - s.A1 / 2) * s.bond_relation + (1 / 4) * (4 - s.A1) * s.cutoff43 +
    s.cutoff_relation

/-- O&R (58), p. 248: for `ν̂ > 0` and `A′(1/2) < 4` (in particular `A′ < 0`), Home runs a
current-account deficit, and Foreign the matching surplus `dB̄*/C̄₀ = −dB̄/C̄₀ > 0`. -/
theorem current_account_deficit (s : TemporaryShock) (hA : s.A1 < 4) (hν : 0 < s.ν) :
    s.dB < 0 ∧ 0 < -s.dB := by
  rw [s.eq58 hA.ne]
  have hr := s.one_add_steadyRate_pos
  have h2 : 0 < 2 - s.A1 / 2 := by linarith
  have : 0 < s.ν / ((1 + steadyRate s.β) * (2 - s.A1 / 2)) := by positivity
  constructor <;> rw [neg_div] <;> linarith

/-- O&R (59), p. 248: long-run consumption changes
`Ĉ̄* = r̄ν̂/((1 + r̄)[2 − A′(1/2)/2]) = −Ĉ̄`. -/
theorem eq59 (s : TemporaryShock) (hA : s.A1 ≠ 4) :
    s.CSbar = steadyRate s.β * s.ν / ((1 + steadyRate s.β) * (2 - s.A1 / 2)) ∧
      s.CSbar = -s.Cbar := by
  constructor
  · rw [s.eq50S, s.eq58 hA]
    unfold steadyRate
    ring
  · rw [s.eq50S, s.eq50]

/-- O&R p. 248, "half the annuity value": Foreign's long-run consumption gain is half the
annuity value `r̄X/(1+r̄)` of its one-period relative income gain `X = ŵ* − ŵ` (the annuity
value of a one-off gain `X` at date `t` is the constant flow from `t` on with the same
present value). -/
theorem half_annuity (s : TemporaryShock) (hA : s.A1 ≠ 4) :
    s.CSbar = 1 / 2 * (steadyRate s.β / (1 + steadyRate s.β)) * (s.wS - s.w) := by
  rw [(s.eq59 hA).1, show s.wS - s.w = -(s.w - s.wS) by ring, s.eq57 hA,
    show (2 - s.A1 / 2) = 2 * (1 - s.A1 / 4) by ring]
  have h4' : (1 - s.A1 / 4) ≠ 0 := by
    intro h; apply hA; linarith
  have hr := s.one_add_steadyRate_pos.ne'
  field_simp

/-- Home's welfare change, O&R Exercise 7, p. 266: with `U = log C + (1/r̄) log C̄`
(`shockPathUtility_eq`), `dU = Ĉ + Ĉ̄/r̄ = −A′(1/2)ν̂/(8 − 2A′(1/2))`. -/
theorem home_welfare (s : TemporaryShock) (hA : s.A1 ≠ 4) :
    s.C + s.Cbar / steadyRate s.β = -s.A1 * s.ν / (8 - 2 * s.A1) := by
  have hpre := s.eq58_pre hA
  have h51 := s.eq51
  have hβ := s.β_pos
  have hrne : steadyRate s.β ≠ 0 := (div_pos (by linarith [s.β_lt_one]) hβ).ne'
  have e : s.Cbar / steadyRate s.β = s.dB := by
    rw [s.eq50, show (1 - s.β) / s.β = steadyRate s.β from rfl]
    field_simp
  rw [e]
  linarith

/-- O&R Exercise 7, p. 266 (and p. 248): for `ν̂ > 0` and `A′(1/2) < 4`, the temporary Foreign
productivity rise raises Home's lifetime utility iff `A′(1/2) < 0`; in particular it does so
under the book's assumption `A′ < 0`. -/
theorem home_welfare_pos_iff (s : TemporaryShock) (hA : s.A1 < 4) (hν : 0 < s.ν) :
    0 < s.C + s.Cbar / steadyRate s.β ↔ s.A1 < 0 := by
  rw [s.home_welfare hA.ne]
  have h8 : 0 < 8 - 2 * s.A1 := by linarith
  rw [lt_div_iff₀ h8, zero_mul]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Foreign's welfare change, O&R p. 248 and Exercise 7:
`dU* = Ĉ* + Ĉ̄*/r̄ = ν̂/2 + ν̂/(2 − A′(1/2)/2)`. -/
theorem foreign_welfare (s : TemporaryShock) (hA : s.A1 ≠ 4) :
    s.CS + s.CSbar / steadyRate s.β = s.ν / 2 + s.ν / (2 - s.A1 / 2) := by
  have hw := s.world_consumption
  have hH := s.home_welfare hA
  have h2 : (2 - s.A1 / 2) ≠ 0 := by intro h; apply hA; linarith
  have e : s.CSbar / steadyRate s.β = -(s.Cbar / steadyRate s.β) := by
    rw [(s.eq59 hA).2, neg_div]
  have e2 : s.ν / 2 + s.ν / (2 - s.A1 / 2) = s.ν - -s.A1 * s.ν / (8 - 2 * s.A1) := by
    have h4 : (4 - s.A1) ≠ 0 := sub_ne_zero.mpr (Ne.symm hA)
    have h8 : (8 - 2 * s.A1) ≠ 0 := by intro h; apply hA; linarith
    rw [eq_sub_iff_add_eq, div_add_div _ _ two_ne_zero h2,
      div_add_div _ _ (mul_ne_zero two_ne_zero h2) h8,
      div_eq_iff (mul_ne_zero (mul_ne_zero two_ne_zero h2) h8)]
    ring
  rw [e, e2]
  linarith

/-- O&R p. 248: Foreign is better off, `dU* > 0`, for `ν̂ > 0` and `A′(1/2) < 4`. -/
theorem foreign_welfare_pos (s : TemporaryShock) (hA : s.A1 < 4) (hν : 0 < s.ν) :
    0 < s.CS + s.CSbar / steadyRate s.β := by
  rw [s.foreign_welfare hA.ne]
  have h2 : 0 < 2 - s.A1 / 2 := by linarith
  positivity

end TemporaryShock

end ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Transport costs and nontraded goods in the Ricardian model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.5.5,
pp. 249–255.

A fraction `κ ∈ (0,1)` of any good shipped abroad melts in transit. Home produces the goods with
`w/w* < A(z)/(1−κ)`, Foreign those with `w/w* > (1−κ)A(z)`; the goods between the cutoffs
`z^F < z^H` are nontraded. Prices are the cheaper of domestic cost and import (CIF) cost.

* the cutoff ordering `z^F < z^H`, and nontradability of the band `(z^F, z^H)`;
* (64), the cutoff link `(1−κ)A(z^F) = A(z^H)/(1−κ)`, and for `A(z) = e^{1−2z}` (65)–(66);
* the real-exchange-rate formula for `P/P*` (from (60), using interval integrals);
* fn 41 made precise: `B̃` is strictly increasing iff `1 + log(1−κ)(1 + TB·a*(1)/L*) > 0`;
* the transfer effect (p. 255): a higher trade balance lowers `B̃`, so `w/w*` falls and both
  cutoffs move right;
* T26 (p. 254): `p(z)/p*(z) = max(1−κ, min(wa(z)/(w*a*(z)), 1/(1−κ)))` for every good, so it
  rises weakly with `w/w*` for every `z`. The book's four-class partition omits a fifth class
  for large shocks (Home exports that become Foreign exports), where the ratio jumps from `1−κ`
  to `1/(1−κ)`; the conclusion holds regardless;
* the κ > 0 Foreign productivity rise (p. 255, "you can verify"): `w/w*` falls by less than the
  factor `ν`, Home's and Foreign's real wages rise weakly on every good, Home's terms of trade
  improve.
-/

namespace ObstfeldRogoff.RealExchangeRate.DFSTransportCosts

open Set

/-- Home's price of a good with transport costs, O&R p. 250: the cheaper of the domestic cost
`w a` and the import (CIF) cost `w* a*/(1−κ)`. -/
noncomputable def homePrice (κ a aS w wS : ℝ) : ℝ := min (a * w) (aS * wS / (1 - κ))

/-- Foreign's price of a good with transport costs, O&R p. 250: the cheaper of `w a/(1−κ)`
(imported from Home) and the domestic cost `w* a*`. -/
noncomputable def foreignPrice (κ a aS w wS : ℝ) : ℝ := min (a * w / (1 - κ)) (aS * wS)

/-- O&R p. 249: Home's own production is (weakly) cheaper than importing,
`w a ≤ w* a*/(1−κ)`, iff `w/w* ≤ A/(1−κ)` with `A = a*/a`. -/
theorem home_produces_iff {κ a aS w wS : ℝ} (hκ : κ < 1) (ha : 0 < a) (hwS : 0 < wS) :
    a * w ≤ aS * wS / (1 - κ) ↔ w / wS ≤ aS / a / (1 - κ) := by
  have h1 : 0 < 1 - κ := by linarith
  rw [le_div_iff₀ h1, div_div, div_le_div_iff₀ hwS (mul_pos ha h1)]
  constructor <;> intro h <;> linarith

/-- O&R p. 249: Foreign's own production is (weakly) cheaper than importing,
`w* a* ≤ w a/(1−κ)`, iff `(1−κ)A ≤ w/w*`. -/
theorem foreign_produces_iff {κ a aS w wS : ℝ} (hκ : κ < 1) (ha : 0 < a) (hwS : 0 < wS) :
    aS * wS ≤ a * w / (1 - κ) ↔ (1 - κ) * (aS / a) ≤ w / wS := by
  have h1 : 0 < 1 - κ := by linarith
  rw [le_div_iff₀ h1, mul_div_assoc', div_le_div_iff₀ ha hwS]
  constructor <;> intro h <;> linarith

/-- Cutoff ordering, O&R pp. 249–252 (Figure 4.11): with `κ ∈ (0,1)` and `A` strictly decreasing
and positive, the cutoffs defined by `w/w* = A(z^H)/(1−κ)` and `w/w* = (1−κ)A(z^F)` satisfy
the link `(1−κ)A(z^F) = A(z^H)/(1−κ)` (fn 40) and `z^F < z^H`. -/
theorem cutoff_order {A : ℝ → ℝ} {s : Set ℝ} {κ ω zF zH : ℝ} (hA : StrictAntiOn A s)
    (hF : zF ∈ s) (hH : zH ∈ s) (hApos : 0 < A zF) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hωH : ω = A zH / (1 - κ)) (hωF : ω = (1 - κ) * A zF) :
    (1 - κ) * A zF = A zH / (1 - κ) ∧ zF < zH := by
  have h1 : 0 < 1 - κ := by linarith
  have link : (1 - κ) * A zF = A zH / (1 - κ) := by rw [← hωF, hωH]
  refine ⟨link, ?_⟩
  have hAH : A zH = (1 - κ) * ((1 - κ) * A zF) := by
    rw [link]; field_simp
  have hlt : A zH < A zF := by
    rw [hAH]
    have : (1 - κ) * (1 - κ) < 1 := by nlinarith
    nlinarith
  by_contra hcon
  push Not at hcon
  rcases hcon.lt_or_eq with h | h
  · exact absurd (hA hH hF h) (not_lt.mpr hlt.le)
  · rw [h] at hlt; exact lt_irrefl _ hlt

/-- Nontraded band, O&R p. 250: for `z^F < z < z^H`, `(1−κ)A(z) < w/w* < A(z)/(1−κ)`, so each
country produces `z` more cheaply than it could import it. -/
theorem nontraded_band {A : ℝ → ℝ} {s : Set ℝ} {κ ω zF zH z : ℝ} (hA : StrictAntiOn A s)
    (hF : zF ∈ s) (hH : zH ∈ s) (hz : z ∈ s) (hκ1 : κ < 1)
    (hωH : ω = A zH / (1 - κ)) (hωF : ω = (1 - κ) * A zF) (hzF : zF < z) (hzH : z < zH) :
    (1 - κ) * A z < ω ∧ ω < A z / (1 - κ) := by
  have h1 : 0 < 1 - κ := by linarith
  constructor
  · rw [hωF]; exact mul_lt_mul_of_pos_left (hA hF hz hzF) h1
  · rw [hωH]; exact div_lt_div_of_pos_right (hA hz hH hzH) h1

/-- O&R (61)–(64), pp. 251–252: world spending equals world income (61), Home output is
demanded on `[0, z^H]` by Home and on `[0, z^F]` by Foreign (62), `TB = wL − PC` (63), and the
numeraire is good 1 delivered in Foreign, so `w* = 1/a*(1)`. Then
`w/w* = {−(z^H − z^F)TB/(L*/a*(1)) + z^F}(L*/L)/(1 − z^H)` (64). -/
theorem relWage_transport {w wS L LS P PS C CS TB zF zH aS1 : ℝ} (hL : 0 < L)
    (haS1 : 0 < aS1) (hwS : wS = 1 / aS1) (hzH : zH < 1)
    (h61 : P * C + PS * CS = w * L + wS * LS) (h62 : w * L = zH * (P * C) + zF * (PS * CS))
    (h63 : TB = w * L - P * C) (hLS : 0 < LS) :
    w / wS = (-(zH - zF) * TB / (LS / aS1) + zF) * (LS / L) / (1 - zH) := by
  have h1 : (1 - zH) ≠ 0 := by linarith
  have key : w * L * (1 - zH) = -(zH - zF) * TB + zF * (wS * LS) := by
    have hPS : PS * CS = w * L + wS * LS - P * C := by linarith
    rw [hPS] at h62
    have hPC : P * C = w * L - TB := by linarith
    rw [hPC] at h62
    linear_combination h62
  rw [hwS] at key ⊢
  field_simp
  field_simp at key
  linear_combination key

/-- The example productivity schedule of O&R p. 252: `A(z) = exp(1 − 2z)`. -/
noncomputable def expA (z : ℝ) : ℝ := Real.exp (1 - 2 * z)

/-- O&R p. 252: `A(z) = exp(1 − 2z)` is strictly decreasing. -/
theorem expA_strictAnti : StrictAnti expA := by
  intro x y hxy
  unfold expA
  exact Real.exp_lt_exp.mpr (by linarith)

/-- O&R (65), p. 252: for `A(z) = exp(1 − 2z)` (scaled by any `σ > 0`, e.g. `σ = 1/ν` after a
uniform Foreign productivity change), the cutoff link `(1−κ)σA(z^F) = σA(z^H)/(1−κ)` holds iff
`z^H = z^F − log(1−κ)`. -/
theorem cutoff_link_exp {κ σ zF zH : ℝ} (hκ1 : κ < 1) (hσ : 0 < σ) :
    (1 - κ) * (σ * expA zF) = σ * expA zH / (1 - κ) ↔ zH = zF - Real.log (1 - κ) := by
  have h1 : 0 < 1 - κ := by linarith
  have key : (1 - κ) * (σ * expA zF) = σ * expA zH / (1 - κ) ↔
      Real.exp (2 * Real.log (1 - κ) + (1 - 2 * zF)) = Real.exp (1 - 2 * zH) := by
    rw [Real.exp_add, show 2 * Real.log (1 - κ) = Real.log (1 - κ) + Real.log (1 - κ) by ring,
      Real.exp_add, Real.exp_log h1]
    unfold expA
    rw [eq_div_iff h1.ne']
    constructor
    · intro h; nlinarith [h]
    · intro h; rw [← h]; ring
  rw [key, Real.exp_eq_exp]
  constructor <;> intro h <;> linarith

/-- O&R (65), p. 252: the cutoffs are interior (`z^F ≥ 0`, `z^H ≤ 1`) only if the band
`z^H − z^F = −log(1−κ)` has width at most one, i.e. `κ ≤ 1 − e^{−1}`. -/
theorem interior_cutoffs_bound {κ zF zH : ℝ} (hκ1 : κ < 1) (hF : 0 ≤ zF) (hH : zH ≤ 1)
    (h65 : zH = zF - Real.log (1 - κ)) : κ ≤ 1 - Real.exp (-1) := by
  have h1 : 0 < 1 - κ := by linarith
  have : -1 ≤ Real.log (1 - κ) := by linarith
  have := Real.exp_le_exp.mpr this
  rw [Real.exp_log h1] at this
  linarith

/-- O&R (66), p. 252: the schedule `B̃(z) = {log(1−κ)TB/(L*/a*(1)) + z}(L*/L)/[1 + log(1−κ) − z]`,
written with `K = L*/a*(1)` and `lam = L*/L`. -/
noncomputable def Btilde (κ TB K lam z : ℝ) : ℝ :=
  (Real.log (1 - κ) * TB / K + z) * lam / (1 + Real.log (1 - κ) - z)

/-- O&R (66), p. 252: substituting (65), `z^H = z^F − log(1−κ)`, into (64) gives
`w/w* = B̃(z^F)`. -/
theorem relWage_eq_Btilde {κ TB K lam zF zH ω : ℝ}
    (h64 : ω = (-(zH - zF) * TB / K + zF) * lam / (1 - zH))
    (h65 : zH = zF - Real.log (1 - κ)) : ω = Btilde κ TB K lam zF := by
  rw [h64, h65, Btilde, show -(zF - Real.log (1 - κ) - zF) = Real.log (1 - κ) by ring,
    show 1 - (zF - Real.log (1 - κ)) = 1 + Real.log (1 - κ) - zF by ring]

/-- O&R fn 41, p. 252: for `z₁, z₂ < 1 + log(1−κ)` (so that `z^H < 1`), with `c = log(1−κ)`,
`B̃(z₂) − B̃(z₁) = lam (z₂ − z₁)(1 + c(1 + TB/K)) / ((1 + c − z₁)(1 + c − z₂))`. -/
theorem Btilde_sub {κ TB K lam z1 z2 : ℝ} (hK : K ≠ 0) (h1 : z1 < 1 + Real.log (1 - κ))
    (h2 : z2 < 1 + Real.log (1 - κ)) :
    Btilde κ TB K lam z2 - Btilde κ TB K lam z1 =
      lam * (z2 - z1) * (1 + Real.log (1 - κ) * (1 + TB / K)) /
        ((1 + Real.log (1 - κ) - z1) * (1 + Real.log (1 - κ) - z2)) := by
  unfold Btilde
  have d1 : (1 + Real.log (1 - κ) - z1) ≠ 0 := by linarith
  have d2 : (1 + Real.log (1 - κ) - z2) ≠ 0 := by linarith
  field_simp
  ring

/-- O&R fn 41, p. 252 ("κ small enough"), made precise: with `L*/L > 0` and `K = L*/a*(1) > 0`,
`B̃` is strictly increasing on `z < 1 + log(1−κ)` iff
`1 + log(1−κ)(1 + TB·a*(1)/L*) > 0` (here `TB/K = TB·a*(1)/L*`). -/
theorem Btilde_strictMonoOn_iff {κ TB K lam : ℝ} (hK : 0 < K) (hlam : 0 < lam) :
    StrictMonoOn (Btilde κ TB K lam) (Iio (1 + Real.log (1 - κ))) ↔
      0 < 1 + Real.log (1 - κ) * (1 + TB / K) := by
  set c := Real.log (1 - κ) with hc
  constructor
  · intro hmono
    by_contra hcon
    push Not at hcon
    have hz1 : c ∈ Iio (1 + c) := by simp
    have hz2 : c + 1 / 2 ∈ Iio (1 + c) := by simp only [mem_Iio]; linarith
    have hlt := hmono hz1 hz2 (by linarith)
    have hs := Btilde_sub (TB := TB) (lam := lam) hK.ne' (lt_add_of_pos_left c one_pos)
      (show c + 1 / 2 < 1 + c by linarith)
    rw [← hc] at hs
    have hden : 0 < (1 + c - c) * (1 + c - (c + 1 / 2)) := by
      rw [show (1 + c - c) * (1 + c - (c + 1 / 2)) = 1 / 2 by ring]; norm_num
    have hnum : lam * (c + 1 / 2 - c) * (1 + c * (1 + TB / K)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by nlinarith) hcon
    have : lam * (c + 1 / 2 - c) * (1 + c * (1 + TB / K)) /
        ((1 + c - c) * (1 + c - (c + 1 / 2))) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hnum hden.le
    linarith
  · intro hcond x hx y hy hxy
    have hs := Btilde_sub (κ := κ) (TB := TB) (lam := lam) hK.ne' hx hy
    have d1 : 0 < 1 + c - x := by simp only [mem_Iio] at hx; linarith
    have d2 : 0 < 1 + c - y := by simp only [mem_Iio] at hy; linarith
    have hyx : 0 < y - x := by linarith
    have : 0 < lam * (y - x) * (1 + c * (1 + TB / K)) / ((1 + c - x) * (1 + c - y)) := by
      positivity
    linarith

/-- The transfer effect on the schedule, O&R p. 255: with `κ ∈ (0,1)`, a higher Home trade
balance lowers `B̃` at every `z < 1 + log(1−κ)`. -/
theorem Btilde_lt_of_TB_lt {κ TB TB' K lam z : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hK : 0 < K)
    (hlam : 0 < lam) (hz : z < 1 + Real.log (1 - κ)) (hTB : TB < TB') :
    Btilde κ TB' K lam z < Btilde κ TB K lam z := by
  unfold Btilde
  have hc : Real.log (1 - κ) < 0 := Real.log_neg (by linarith) (by linarith)
  have hd : 0 < 1 + Real.log (1 - κ) - z := by linarith
  apply div_lt_div_of_pos_right _ hd
  apply mul_lt_mul_of_pos_right _ hlam
  have : Real.log (1 - κ) * TB' / K < Real.log (1 - κ) * TB / K :=
    div_lt_div_of_pos_right (mul_lt_mul_of_neg_left hTB hc) hK
  linarith

/-- The Keynesian transfer effect, O&R p. 255 (Figure 4.12): for `A(z) = exp(1−2z)`, if the
Home trade balance rises from `TB` to `TB'` and `B̃(·; TB)` is increasing (fn 41's condition),
the equilibrium cutoffs `(1−κ)A(z^F) = B̃(z^F)` move right, `z^F < z^F'` and
`z^H < z^H'` (with `z^H = z^F − log(1−κ)`), and the relative Home wage
`w/w* = (1−κ)A(z^F)` falls. -/
theorem transfer_effect {κ TB TB' K lam zF zF' : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hK : 0 < K)
    (hlam : 0 < lam) (hTB : TB < TB') (hcond : 0 < 1 + Real.log (1 - κ) * (1 + TB / K))
    (hzF : zF < 1 + Real.log (1 - κ)) (hzF' : zF' < 1 + Real.log (1 - κ))
    (heq : (1 - κ) * expA zF = Btilde κ TB K lam zF)
    (heq' : (1 - κ) * expA zF' = Btilde κ TB' K lam zF') :
    zF < zF' ∧ zF - Real.log (1 - κ) < zF' - Real.log (1 - κ) ∧
      (1 - κ) * expA zF' < (1 - κ) * expA zF := by
  have h1 : 0 < 1 - κ := by linarith
  have hmono := (Btilde_strictMonoOn_iff (κ := κ) (TB := TB) hK hlam).2 hcond
  have hlt : zF < zF' := by
    by_contra hcon
    push Not at hcon
    have e1 : expA zF ≤ expA zF' := expA_strictAnti.antitone hcon
    have e2 : Btilde κ TB K lam zF' ≤ Btilde κ TB K lam zF := hmono.monotoneOn hzF' hzF hcon
    have e3 := Btilde_lt_of_TB_lt hκ0 hκ1 hK hlam hzF' hTB
    have e4 : (1 - κ) * expA zF ≤ (1 - κ) * expA zF' := mul_le_mul_of_nonneg_left e1 h1.le
    linarith
  exact ⟨hlt, by linarith, mul_lt_mul_of_pos_left (expA_strictAnti hlt) h1⟩

/-- A rise in relative Foreign labour with transport costs, O&R p. 253 (Figure 4.13): with
`TB = 0`, `A(z) = exp(1−2z)` and `L*/L` rising from `lam` to `lam'`, the cutoff `z^F` falls and
the relative Home wage `w/w* = (1−κ)A(z^F)` rises (`B̃` shifts inward). -/
theorem labour_rise_transport {κ K lam lam' zF zF' : ℝ} (hκ1 : κ < 1) (hK : 0 < K)
    (hlam : 0 < lam) (hlam' : lam < lam') (hzF : zF ∈ Ioo 0 (1 + Real.log (1 - κ)))
    (hzF' : zF' ∈ Ioo 0 (1 + Real.log (1 - κ)))
    (heq : (1 - κ) * expA zF = Btilde κ 0 K lam zF)
    (heq' : (1 - κ) * expA zF' = Btilde κ 0 K lam' zF') :
    zF' < zF ∧ (1 - κ) * expA zF < (1 - κ) * expA zF' := by
  have h1 : 0 < 1 - κ := by linarith
  have hcond : 0 < 1 + Real.log (1 - κ) * (1 + 0 / K) := by
    rw [zero_div, add_zero, mul_one]; linarith [hzF.1, hzF.2]
  have hmono := (Btilde_strictMonoOn_iff (κ := κ) (TB := 0) hK hlam).2 hcond
  have hlt : zF' < zF := by
    by_contra hcon
    push Not at hcon
    have e1 : expA zF' ≤ expA zF := expA_strictAnti.antitone hcon
    have e2 : Btilde κ 0 K lam zF ≤ Btilde κ 0 K lam zF' :=
      hmono.monotoneOn hzF.2 hzF'.2 hcon
    have e3 : Btilde κ 0 K lam zF' < Btilde κ 0 K lam' zF' := by
      unfold Btilde
      have hd : 0 < 1 + Real.log (1 - κ) - zF' := by linarith [hzF'.2]
      rw [mul_zero, zero_div, zero_add]
      exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hlam' hzF'.1) hd
    have e4 : (1 - κ) * expA zF' ≤ (1 - κ) * expA zF := mul_le_mul_of_nonneg_left e1 h1.le
    linarith
  exact ⟨hlt, mul_lt_mul_of_pos_left (expA_strictAnti hlt) h1⟩

/-- A uniform Foreign productivity rise with transport costs, O&R p. 255 ("You can verify"):
with `TB = 0`, `A(z) = exp(1−2z)` and `a* ↦ a*/ν`, `ν > 1` (so `A ↦ A/ν`, and (65) is unchanged
by `cutoff_link_exp`), the new cutoff `z^F'` solving `(1−κ)A(z^F')/ν = B̃(z^F')` satisfies
`z^F' < z^F`, and the relative Home wage falls by less than the factor `ν`:
`ω/ν < ω' < ω` with `ω = (1−κ)A(z^F)`, `ω' = (1−κ)A(z^F')/ν`. -/
theorem productivity_rise_transport {κ K lam ν zF zF' : ℝ} (hκ1 : κ < 1) (hK : 0 < K)
    (hlam : 0 < lam) (hν : 1 < ν) (hzF : zF ∈ Ioo 0 (1 + Real.log (1 - κ)))
    (hzF' : zF' ∈ Ioo 0 (1 + Real.log (1 - κ)))
    (heq : (1 - κ) * expA zF = Btilde κ 0 K lam zF)
    (heq' : (1 - κ) * expA zF' / ν = Btilde κ 0 K lam zF') :
    zF' < zF ∧ (1 - κ) * expA zF / ν < (1 - κ) * expA zF' / ν ∧
      (1 - κ) * expA zF' / ν < (1 - κ) * expA zF := by
  have h1 : 0 < 1 - κ := by linarith
  have hν0 : 0 < ν := by linarith
  have hcond : 0 < 1 + Real.log (1 - κ) * (1 + 0 / K) := by
    rw [zero_div, add_zero, mul_one]; linarith [hzF.1, hzF.2]
  have hmono := (Btilde_strictMonoOn_iff (κ := κ) (TB := 0) hK hlam).2 hcond
  have hlt : zF' < zF := by
    by_contra hcon
    push Not at hcon
    have e1 : expA zF' ≤ expA zF := expA_strictAnti.antitone hcon
    have e2 : Btilde κ 0 K lam zF ≤ Btilde κ 0 K lam zF' :=
      hmono.monotoneOn hzF.2 hzF'.2 hcon
    have hpos : 0 < (1 - κ) * expA zF' := mul_pos h1 (Real.exp_pos _)
    have e3 : (1 - κ) * expA zF' / ν < (1 - κ) * expA zF' := div_lt_self hpos hν
    have e4 : (1 - κ) * expA zF' ≤ (1 - κ) * expA zF := mul_le_mul_of_nonneg_left e1 h1.le
    linarith
  have hA : (1 - κ) * expA zF < (1 - κ) * expA zF' :=
    mul_lt_mul_of_pos_left (expA_strictAnti hlt) h1
  refine ⟨hlt, div_lt_div_of_pos_right hA hν0, ?_⟩
  rw [heq, heq']
  exact hmono hzF'.2 hzF.2 hlt

/-- O&R pp. 250–255: Home's real wage in Home prices with transport costs,
`w/p = max (1/a) ((1−κ)(w/w*)/a*)`. -/
theorem homeRealWage_eq {κ a aS w wS : ℝ} (hκ1 : κ < 1) (ha : 0 < a) (haS : 0 < aS)
    (hw : 0 < w) (hwS : 0 < wS) :
    w / homePrice κ a aS w wS = max (1 / a) ((1 - κ) * (w / wS) / aS) := by
  have h1 : 0 < 1 - κ := by linarith
  unfold homePrice
  have e : w / (aS * wS / (1 - κ)) = (1 - κ) * (w / wS) / aS := by field_simp
  rcases le_total (a * w) (aS * wS / (1 - κ)) with h | h
  · rw [min_eq_left h]
    have : (1 - κ) * (w / wS) / aS ≤ 1 / a := by
      rw [← e, div_le_div_iff₀ (by positivity) ha]
      nlinarith
    rw [max_eq_left this]
    field_simp
  · rw [min_eq_right h, e]
    have : 1 / a ≤ (1 - κ) * (w / wS) / aS := by
      rw [← e, div_le_div_iff₀ ha (by positivity)]
      nlinarith
    rw [max_eq_right this]

/-- O&R pp. 250–255: Foreign's real wage in Foreign prices with transport costs,
`w*/p* = max ((1−κ)(w*/w)/a) (1/a*)`. -/
theorem foreignRealWage_eq {κ a aS w wS : ℝ} (hκ1 : κ < 1) (ha : 0 < a) (haS : 0 < aS)
    (hw : 0 < w) (hwS : 0 < wS) :
    wS / foreignPrice κ a aS w wS = max ((1 - κ) * (wS / w) / a) (1 / aS) := by
  have h1 : 0 < 1 - κ := by linarith
  unfold foreignPrice
  have e : wS / (a * w / (1 - κ)) = (1 - κ) * (wS / w) / a := by field_simp
  rcases le_total (a * w / (1 - κ)) (aS * wS) with h | h
  · rw [min_eq_left h, e]
    have : 1 / aS ≤ (1 - κ) * (wS / w) / a := by
      rw [← e, div_le_div_iff₀ haS (by positivity)]
      nlinarith
    rw [max_eq_left this]
  · rw [min_eq_right h]
    have : (1 - κ) * (wS / w) / a ≤ 1 / aS := by
      rw [← e, div_le_div_iff₀ (by positivity) haS]
      nlinarith
    rw [max_eq_right this]
    field_simp

/-- O&R p. 255: after the Foreign productivity rise `a* ↦ a*/ν` with `w/w* ≤ ν · w'/w*'`
(`productivity_rise_transport`), Home's real wage rises weakly in terms of every good. -/
theorem productivity_rise_home_realWage {κ a aS w wS w' wS' ν : ℝ} (hκ1 : κ < 1)
    (ha : 0 < a) (haS : 0 < aS) (hν : 0 < ν) (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w')
    (hwS' : 0 < wS') (hless : w / wS ≤ ν * (w' / wS')) :
    w / homePrice κ a aS w wS ≤ w' / homePrice κ a (aS / ν) w' wS' := by
  have h1 : 0 < 1 - κ := by linarith
  rw [homeRealWage_eq hκ1 ha haS hw hwS, homeRealWage_eq hκ1 ha (by positivity) hw' hwS']
  have e : (1 - κ) * (w' / wS') / (aS / ν) = (1 - κ) * (ν * (w' / wS')) / aS := by
    field_simp
  rw [e]
  exact max_le_max le_rfl
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hless h1.le) haS.le)

/-- O&R p. 255: after the Foreign productivity rise `a* ↦ a*/ν`, `ν ≥ 1`, with `w/w*` falling,
Foreign's real wage rises weakly in terms of every good. -/
theorem productivity_rise_foreign_realWage {κ a aS w wS w' wS' ν : ℝ} (hκ1 : κ < 1)
    (ha : 0 < a) (haS : 0 < aS) (hν : 1 ≤ ν) (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w')
    (hwS' : 0 < wS') (hfall : w' / wS' ≤ w / wS) :
    wS / foreignPrice κ a aS w wS ≤ wS' / foreignPrice κ a (aS / ν) w' wS' := by
  have h1 : 0 < 1 - κ := by linarith
  rw [foreignRealWage_eq hκ1 ha haS hw hwS, foreignRealWage_eq hκ1 ha (by positivity) hw' hwS']
  have hr : wS / w ≤ wS' / w' := by
    rw [div_le_div_iff₀ hw hw']; rw [div_le_div_iff₀ hwS' hwS] at hfall; linarith
  have e : 1 / (aS / ν) = ν / aS := by field_simp
  rw [e]
  exact max_le_max (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr h1.le) ha.le)
    (div_le_div_of_nonneg_right hν haS.le)

/-- O&R p. 255: Home's terms of trade improve after the Foreign productivity rise: for any good
Home exports (price `w a₁`) and any good Foreign exports (price `w* a*₂`, which becomes
`w*' a*₂/ν`), the relative price of Home's export rises when `w/w* < ν · w'/w*'`. -/
theorem productivity_rise_termsOfTrade {a1 aS2 w wS w' wS' ν : ℝ} (ha1 : 0 < a1)
    (haS2 : 0 < aS2) (hν : 0 < ν) (hwS : 0 < wS) (hwS' : 0 < wS')
    (hless : w / wS < ν * (w' / wS')) :
    a1 * w / (aS2 * wS) < a1 * w' / (aS2 / ν * wS') := by
  have e1 : a1 * w / (aS2 * wS) = a1 / aS2 * (w / wS) := by field_simp
  have e2 : a1 * w' / (aS2 / ν * wS') = a1 / aS2 * (ν * (w' / wS')) := by field_simp
  rw [e1, e2]
  exact mul_lt_mul_of_pos_left hless (div_pos ha1 haS2)

/-- T26 (O&R p. 254), the key formula: for every good, the Home–Foreign price ratio is the
relative Home cost `x = w a/(w* a*)` clamped to `[1−κ, 1/(1−κ)]`:
`p/p* = max (1−κ) (min x (1/(1−κ)))`. (Home exports: `1−κ`; nontraded: `x`; Foreign exports:
`1/(1−κ)`.) -/
theorem priceRatio_eq {κ a aS w wS : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (ha : 0 < a)
    (haS : 0 < aS) (hw : 0 < w) (hwS : 0 < wS) :
    homePrice κ a aS w wS / foreignPrice κ a aS w wS =
      max (1 - κ) (min (a * w / (aS * wS)) (1 / (1 - κ))) := by
  have h1 : 0 < 1 - κ := by linarith
  have hm : 0 < aS * wS := by positivity
  set m := aS * wS with hmdef
  set x := a * w / m with hxdef
  have hx : 0 < x := by positivity
  have hax : a * w = x * m := by rw [hxdef]; field_simp
  have eH : homePrice κ a aS w wS = min x (1 / (1 - κ)) * m := by
    unfold homePrice
    rw [min_mul_of_nonneg _ _ hm.le, hax, ← hmdef]
    congr 1
    ring
  have eF : foreignPrice κ a aS w wS = min (x / (1 - κ)) 1 * m := by
    unfold foreignPrice
    rw [min_mul_of_nonneg _ _ hm.le, hax, ← hmdef]
    congr 1
    · ring
    · ring
  rw [eH, eF, mul_div_mul_right _ _ hm.ne']
  have hq : 1 - κ ≤ 1 / (1 - κ) := by
    rw [le_div_iff₀ h1]; nlinarith
  rcases le_total x (1 - κ) with hx1 | hx1
  · rw [min_eq_left (hx1.trans hq), min_eq_left ((div_le_one h1).2 hx1), max_eq_left hx1]
    field_simp
  · rcases le_total x (1 / (1 - κ)) with hx2 | hx2
    · rw [min_eq_left hx2, min_eq_right ((one_le_div h1).2 hx1), max_eq_right hx1, div_one]
    · rw [min_eq_right hx2, min_eq_right ((one_le_div h1).2 hx1), max_eq_right hq, div_one]

/-- T26, O&R p. 254 (Figure 4.13): whenever the relative Home wage rises (as after a rise in
`L*/L`, `labour_rise_transport`), `p(z)′/p*(z)′ ≥ p(z)/p*(z)` for EVERY good `z`, in
whichever class it falls (including the fifth class the book omits). -/
theorem priceRatio_mono {κ a aS w wS w' wS' : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (ha : 0 < a)
    (haS : 0 < aS) (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w') (hwS' : 0 < wS')
    (hrise : w / wS ≤ w' / wS') :
    homePrice κ a aS w wS / foreignPrice κ a aS w wS ≤
      homePrice κ a aS w' wS' / foreignPrice κ a aS w' wS' := by
  rw [priceRatio_eq hκ0 hκ1 ha haS hw hwS, priceRatio_eq hκ0 hκ1 ha haS hw' hwS']
  have e1 : a * w / (aS * wS) = a / aS * (w / wS) := by field_simp
  have e2 : a * w' / (aS * wS') = a / aS * (w' / wS') := by field_simp
  rw [e1, e2]
  exact max_le_max le_rfl
    (min_le_min_right _ (mul_le_mul_of_nonneg_left hrise (div_pos ha haS).le))

/-- The fifth class omitted by O&R p. 254: a good Home exported before the shock
(`x ≤ 1−κ`) that Foreign exports afterwards (`x' ≥ 1/(1−κ)`); its price ratio jumps from
`1−κ` to `1/(1−κ)`. -/
theorem fifth_class_priceRatio {κ a aS w wS w' wS' : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (ha : 0 < a) (haS : 0 < aS) (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w') (hwS' : 0 < wS')
    (hbefore : a * w / (aS * wS) ≤ 1 - κ) (hafter : 1 / (1 - κ) ≤ a * w' / (aS * wS')) :
    homePrice κ a aS w wS / foreignPrice κ a aS w wS = 1 - κ ∧
      homePrice κ a aS w' wS' / foreignPrice κ a aS w' wS' = 1 / (1 - κ) ∧
      1 - κ < 1 / (1 - κ) := by
  have h1 : 0 < 1 - κ := by linarith
  have hq : 1 - κ < 1 / (1 - κ) := by
    rw [lt_div_iff₀ h1]; nlinarith
  refine ⟨?_, ?_, hq⟩
  · rw [priceRatio_eq hκ0.le hκ1 ha haS hw hwS, min_eq_left (hbefore.trans hq.le),
      max_eq_left hbefore]
  · rw [priceRatio_eq hκ0.le hκ1 ha haS hw' hwS', min_eq_right hafter, max_eq_right hq.le]

/-- O&R p. 254: the fifth class is empty for small shocks: it requires the relative Home wage
to rise by at least the factor `1/(1−κ)²`. -/
theorem fifth_class_requires_large_shock {κ a aS w wS w' wS' : ℝ} (hκ1 : κ < 1)
    (ha : 0 < a) (haS : 0 < aS) (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w') (hwS' : 0 < wS')
    (hbefore : a * w / (aS * wS) ≤ 1 - κ) (hafter : 1 / (1 - κ) ≤ a * w' / (aS * wS')) :
    1 / (1 - κ) ^ 2 ≤ (w' / wS') / (w / wS) := by
  have h1 : 0 < 1 - κ := by linarith
  have hx : 0 < a * w / (aS * wS) := by positivity
  have e : (w' / wS') / (w / wS) = (a * w' / (aS * wS')) / (a * w / (aS * wS)) := by
    field_simp
  rw [e]
  calc 1 / (1 - κ) ^ 2 = (1 / (1 - κ)) / (1 - κ) := by field_simp
    _ ≤ (a * w' / (aS * wS')) / (1 - κ) := div_le_div_of_nonneg_right hafter h1.le
    _ ≤ (a * w' / (aS * wS')) / (a * w / (aS * wS)) :=
        div_le_div_of_nonneg_left (by positivity) hx hbefore

/-- O&R (60), p. 250: `log(x/(1−κ)) = log x − log(1−κ)`, used to write the CIF import prices in
the log price indices. -/
theorem log_cif {κ x : ℝ} (hκ1 : κ < 1) (hx : 0 < x) :
    Real.log (x / (1 - κ)) = Real.log x - Real.log (1 - κ) := by
  have h1 : 0 < 1 - κ := by linarith
  exact Real.log_div hx.ne' h1.ne'

/-- Home's log price index, O&R (60), p. 250, with `f z = log(w a(z))`, `g z = log(w* a*(z))`:
`log P = ∫₀^{z^H} f + ∫_{z^H}^1 (g − log(1−κ))`. -/
noncomputable def logHomePriceIndex (κ zH : ℝ) (f g : ℝ → ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..zH, f z) + ∫ z in zH..1, (g z - Real.log (1 - κ))

/-- Foreign's log price index, O&R (60), p. 250:
`log P* = ∫₀^{z^F} (f − log(1−κ)) + ∫_{z^F}^1 g`. -/
noncomputable def logForeignPriceIndex (κ zF : ℝ) (f g : ℝ → ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..zF, (f z - Real.log (1 - κ))) + ∫ z in zF..1, g z

/-- The real exchange rate, O&R p. 251:
`log(P/P*) = ∫_{z^F}^{z^H} log[w a(z)/(w* a*(z))] dz + [z^F − (1 − z^H)] log(1−κ)`
(for `f, g` integrable on `[0,1]` and `z^F, z^H ∈ [0,1]`). -/
theorem log_realExchangeRate {κ zF zH : ℝ} {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1)
    (hg : IntervalIntegrable g MeasureTheory.volume 0 1)
    (hF : zF ∈ Icc (0 : ℝ) 1) (hH : zH ∈ Icc (0 : ℝ) 1) :
    logHomePriceIndex κ zH f g - logForeignPriceIndex κ zF f g =
      (∫ z in zF..zH, (f z - g z)) + (zF - (1 - zH)) * Real.log (1 - κ) := by
  have sub : ∀ {h : ℝ → ℝ}, IntervalIntegrable h MeasureTheory.volume 0 1 →
      ∀ {x y : ℝ}, x ∈ Icc (0 : ℝ) 1 → y ∈ Icc (0 : ℝ) 1 →
        IntervalIntegrable h MeasureTheory.volume x y := by
    intro h hh x y hx hy
    refine hh.mono_set (uIcc_subset_uIcc ?_ ?_)
    · exact Icc_subset_uIcc hx
    · exact Icc_subset_uIcc hy
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hc : ∀ x y : ℝ, IntervalIntegrable (fun _ : ℝ => Real.log (1 - κ))
      MeasureTheory.volume x y := fun _ _ => intervalIntegrable_const
  unfold logHomePriceIndex logForeignPriceIndex
  rw [intervalIntegral.integral_sub (sub hg hH h1) (hc _ _),
    intervalIntegral.integral_sub (sub hf h0 hF) (hc _ _),
    intervalIntegral.integral_sub (sub hf hF hH) (sub hg hF hH),
    intervalIntegral.integral_const, intervalIntegral.integral_const,
    ← intervalIntegral.integral_interval_sub_left (sub hf h0 hH) (sub hf h0 hF),
    ← intervalIntegral.integral_add_adjacent_intervals (sub hg hF hH) (sub hg hH h1)]
  simp only [smul_eq_mul]
  ring

end ObstfeldRogoff.RealExchangeRate.DFSTransportCosts

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Ricardian price index: cost minimisation and the moving-cutoff derivative

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.5.1, pp. 236–238,
fn 36, p. 246, and §4.5.5.1, p. 251.

* T19 (pp. 237–238): `P = exp ∫₀¹ log p` is the minimum cost of one unit of
  `C = exp ∫₀¹ log c`, attained by the equal-spending demand `c = P/p` (40). The proof uses
  `e^y ≥ 1 + y` pointwise (a hand-rolled Jensen inequality), not Lagrange multipliers.
* (54) (fn 36, p. 246): the derivative of `log P` in `ν` with a moving cutoff; the boundary term
  vanishes because the cutoff good costs the same in both countries.
* T25 (p. 251): holding `w`, `w*`, `z^H` fixed,
  `d log(P/P*)/dz^F = log(1−κ) − log[wa(z^F)/(w*a*(z^F))]`, which is ZERO at the equilibrium
  cutoff `wa(z^F) = (1−κ)w*a*(z^F)`. The book attributes the effect of a rise in `z^F` to the
  explicit term `z^F log(1−κ)`; that term is exactly cancelled, to first order, by the moving
  integration limit. For a discrete rise beyond the equilibrium
  cutoff the book's direction (Foreign's CPI rises relative to Home's) is nevertheless correct,
  as a second-order effect: `log(P/P*)` is maximised in `z^F` at the equilibrium cutoff.
-/

namespace ObstfeldRogoff.RealExchangeRate.DFSPriceIndex

open Set MeasureTheory

/-- T19, O&R pp. 237–238: if prices `p` and quantities `c` are positive on `[0,1]` and the
consumption index is one, `∫₀¹ log c = 0`, then the expenditure `∫₀¹ p c` is at least
`P = exp ∫₀¹ log p`. -/
theorem priceIndex_le_cost {p c : ℝ → ℝ} (hp : ∀ z ∈ Icc (0 : ℝ) 1, 0 < p z)
    (hc : ∀ z ∈ Icc (0 : ℝ) 1, 0 < c z)
    (hpc : IntervalIntegrable (fun z => p z * c z) volume 0 1)
    (hlp : IntervalIntegrable (fun z => Real.log (p z)) volume 0 1)
    (hlc : IntervalIntegrable (fun z => Real.log (c z)) volume 0 1)
    (hC : ∫ z in (0 : ℝ)..1, Real.log (c z) = 0) :
    Real.exp (∫ z in (0 : ℝ)..1, Real.log (p z)) ≤ ∫ z in (0 : ℝ)..1, p z * c z := by
  set I := ∫ z in (0 : ℝ)..1, Real.log (p z) with hI
  set P := Real.exp I with hP
  have hpt : ∀ z ∈ Icc (0 : ℝ) 1,
      P * (1 + Real.log (p z) + Real.log (c z) - I) ≤ p z * c z := by
    intro z hz
    have hpz := hp z hz
    have hcz := hc z hz
    have h1 := Real.add_one_le_exp (Real.log (p z) + Real.log (c z) - I)
    have h2 : Real.exp (Real.log (p z) + Real.log (c z) - I) * P = p z * c z := by
      rw [hP, ← Real.exp_add, sub_add_cancel, Real.exp_add, Real.exp_log hpz, Real.exp_log hcz]
    have hPpos : 0 < P := Real.exp_pos _
    nlinarith
  have hint : IntervalIntegrable (fun z => P * (1 + Real.log (p z) + Real.log (c z) - I))
      volume 0 1 :=
    (((intervalIntegrable_const.add hlp).add hlc).sub intervalIntegrable_const).const_mul P
  have hval : ∫ z in (0 : ℝ)..1, P * (1 + Real.log (p z) + Real.log (c z) - I) = P := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub ((intervalIntegrable_const.add hlp).add hlc)
        intervalIntegrable_const,
      intervalIntegral.integral_add (intervalIntegrable_const.add hlp) hlc,
      intervalIntegral.integral_add intervalIntegrable_const hlp, hC, ← hI]
    simp
  rw [← hval]
  exact intervalIntegral.integral_mono_on zero_le_one hint hpc hpt

/-- T19 and (40), O&R p. 238: the demand `c(z) = P/p(z)` has consumption index one
(`∫₀¹ log c = 0`) and costs exactly `P = exp ∫₀¹ log p`, so it attains the minimum. -/
theorem priceIndex_attained {p : ℝ → ℝ} (hp : ∀ z ∈ Icc (0 : ℝ) 1, 0 < p z)
    (hlp : IntervalIntegrable (fun z => Real.log (p z)) volume 0 1) :
    (∫ z in (0 : ℝ)..1, Real.log (Real.exp (∫ y in (0 : ℝ)..1, Real.log (p y)) / p z)) = 0 ∧
      (∫ z in (0 : ℝ)..1, p z * (Real.exp (∫ y in (0 : ℝ)..1, Real.log (p y)) / p z)) =
        Real.exp (∫ y in (0 : ℝ)..1, Real.log (p y)) := by
  set I := ∫ y in (0 : ℝ)..1, Real.log (p y) with hI
  have hu : ∀ z ∈ uIcc (0 : ℝ) 1, 0 < p z := by
    intro z hz; rw [uIcc_of_le zero_le_one] at hz; exact hp z hz
  constructor
  · have e : EqOn (fun z => Real.log (Real.exp I / p z)) (fun z => I - Real.log (p z))
        (uIcc 0 1) := by
      intro z hz
      simp only
      rw [Real.log_div (Real.exp_pos I).ne' (hu z hz).ne', Real.log_exp]
    rw [intervalIntegral.integral_congr e,
      intervalIntegral.integral_sub intervalIntegrable_const hlp, ← hI]
    simp
  · have e : EqOn (fun z => p z * (Real.exp I / p z)) (fun _ => Real.exp I) (uIcc 0 1) := by
      intro z hz
      simp only
      field_simp [(hu z hz).ne']
    rw [intervalIntegral.integral_congr e]
    simp

/-- O&R p. 238, after (40): with demand `c(z) = (P/p(z)) C`, spending on any interval
`[z₁, z₂]` of goods is `(z₂ − z₁) P C`. -/
theorem expenditure_on_interval {p : ℝ → ℝ} {P C z1 z2 : ℝ}
    (hp : ∀ z ∈ uIcc z1 z2, p z ≠ 0) :
    ∫ z in z1..z2, p z * (P / p z * C) = (z2 - z1) * (P * C) := by
  have e : EqOn (fun z => p z * (P / p z * C)) (fun _ => P * C) (uIcc z1 z2) := by
    intro z hz
    simp only
    field_simp [hp z hz]
  rw [intervalIntegral.integral_congr e]
  simp only [intervalIntegral.integral_const, smul_eq_mul]

/-- O&R (54) and fn 36, p. 246: while Foreign productivity is `ν` times higher,
`log P(ν) = z̄ log w + ∫₀^{z̄} log a + (1 − z̄)(log w* − log ν) + ∫_{z̄}^1 log a*` (with
`p = wa` on `[0, z̄]` and `p = w*a*/ν` on `(z̄, 1]`). If `w(ν)`, `w*(ν)`, `z̄(ν)` are
differentiable at `ν = 1` and the cutoff good costs the same in both countries at `ν = 1`
(`w a(z̄) = w* a*(z̄)`), the moving-limit terms cancel and
`d log P/dν = z̄ ŵ + (1 − z̄)(ŵ* − 1)`, which at `z̄ = 1/2` is (54):
`P̂ = (ŵ + ŵ*)/2 − ν̂/2`. -/
theorem logPriceIndex_hasDerivAt {la laS w wS zb : ℝ → ℝ} {w1 wS1 z1 : ℝ}
    (hla : Continuous la) (hlaS : Continuous laS) (hw : HasDerivAt w w1 1)
    (hwS : HasDerivAt wS wS1 1) (hzb : HasDerivAt zb z1 1) (hw0 : 0 < w 1) (hwS0 : 0 < wS 1)
    (hcut : Real.log (w 1) + la (zb 1) = Real.log (wS 1) + laS (zb 1)) :
    HasDerivAt
      (fun ν => zb ν * Real.log (w ν) + (∫ z in (0 : ℝ)..zb ν, la z) +
        (1 - zb ν) * (Real.log (wS ν) - Real.log ν) + ∫ z in zb ν..1, laS z)
      (zb 1 * (w1 / w 1) + (1 - zb 1) * (wS1 / wS 1 - 1)) 1 := by
  have hA : HasDerivAt (fun ν => ∫ z in (0 : ℝ)..zb ν, la z) (la (zb 1) * z1) 1 :=
    (hla.integral_hasStrictDerivAt 0 (zb 1)).hasDerivAt.comp 1 hzb
  have hB0 : HasDerivAt (fun ν => ∫ z in (0 : ℝ)..zb ν, laS z) (laS (zb 1) * z1) 1 :=
    (hlaS.integral_hasStrictDerivAt 0 (zb 1)).hasDerivAt.comp 1 hzb
  have hBeq : (fun ν => ∫ z in zb ν..1, laS z) =
      fun ν => (∫ z in (0 : ℝ)..1, laS z) - ∫ z in (0 : ℝ)..zb ν, laS z := by
    funext ν
    rw [intervalIntegral.integral_interval_sub_left (hlaS.intervalIntegrable _ _)
      (hlaS.intervalIntegrable _ _)]
  have hB : HasDerivAt (fun ν => ∫ z in zb ν..1, laS z) (-(laS (zb 1) * z1)) 1 := by
    rw [hBeq]
    exact (hB0.const_sub _)
  have hlw : HasDerivAt (fun ν => Real.log (w ν)) (w1 / w 1) 1 := hw.log hw0.ne'
  have hlwS : HasDerivAt (fun ν => Real.log (wS ν)) (wS1 / wS 1) 1 := hwS.log hwS0.ne'
  have hlν : HasDerivAt (fun ν : ℝ => Real.log ν) 1 1 := by
    simpa using Real.hasDerivAt_log (x := (1 : ℝ)) one_ne_zero
  have h1 := hzb.mul hlw
  have h2 := (hzb.const_sub 1).mul (hlwS.sub hlν)
  have htot := ((h1.add hA).add h2).add hB
  convert htot using 1
  simp only [Pi.sub_apply, Real.log_one, sub_zero]
  linear_combination -z1 * hcut

/-- The log real exchange rate as a function of `z^F`, O&R p. 251 (`log_realExchangeRate` in
`DFSTransportCosts`), with `f = log(wa)`, `g = log(w*a*)` and `w`, `w*`, `z^H` held fixed:
`Φ(z^F) = ∫_{z^F}^{z^H} (f − g) + (z^F − (1 − z^H)) log(1−κ)`. -/
noncomputable def logRERInCutoff (κ zH : ℝ) (f g : ℝ → ℝ) (zF : ℝ) : ℝ :=
  (∫ z in zF..zH, (f z - g z)) + (zF - (1 - zH)) * Real.log (1 - κ)

/-- T25, O&R p. 251: for continuous `f, g`,
`dΦ/dz^F = log(1−κ) − (f(z^F) − g(z^F))`: the explicit term contributes `log(1−κ)` and the
moving lower limit contributes `−(f − g)(z^F)`. -/
theorem logRERInCutoff_hasDerivAt {κ zH x : ℝ} {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    HasDerivAt (logRERInCutoff κ zH f g) (Real.log (1 - κ) - (f x - g x)) x := by
  have hc : Continuous fun z => f z - g z := hf.sub hg
  have heq : logRERInCutoff κ zH f g = fun u =>
      (∫ z in (0 : ℝ)..zH, (f z - g z)) - (∫ z in (0 : ℝ)..u, (f z - g z)) +
        (u - (1 - zH)) * Real.log (1 - κ) := by
    funext u
    unfold logRERInCutoff
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  rw [heq]
  have h1 := (hc.integral_hasStrictDerivAt 0 x).hasDerivAt.const_sub
    (∫ z in (0 : ℝ)..zH, (f z - g z))
  have h2 : HasDerivAt (fun u : ℝ => (u - (1 - zH)) * Real.log (1 - κ)) (Real.log (1 - κ)) x := by
    simpa using ((hasDerivAt_id x).sub_const (1 - zH)).mul_const (Real.log (1 - κ))
  convert h1.add h2 using 1
  ring

/-- T25, O&R p. 251 — the book's mechanism fails to first order: at the equilibrium cutoff,
where `w a(z^F) = (1−κ) w* a*(z^F)`, i.e. `f(z^F) = log(1−κ) + g(z^F)`, the derivative of
`log(P/P*)` in `z^F` (holding `w`, `w*`, `z^H` fixed) is exactly zero, although the explicit
term `z^F log(1−κ)` alone would give `log(1−κ) < 0`. -/
theorem logRERInCutoff_deriv_zero_at_cutoff {κ zH x : ℝ} {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hcut : f x = Real.log (1 - κ) + g x) :
    HasDerivAt (logRERInCutoff κ zH f g) 0 x := by
  have h := logRERInCutoff_hasDerivAt (κ := κ) (zH := zH) (x := x) hf hg
  rwa [hcut, show Real.log (1 - κ) - (Real.log (1 - κ) + g x - g x) = 0 by ring] at h

/-- O&R p. 251: with `f = log(wa)`, `g = log(w*a*)`, the integrand of `dΦ/dz^F` is
`log(1−κ) − (f − g) = log[(1−κ) w* a*/(w a)]`, negative exactly for goods Home produces more
cheaply than Foreign can import them (`(1−κ) w* a* < w a`, i.e. goods above the equilibrium
`z^F` when `A` is decreasing). -/
theorem cutoff_integrand_eq {κ a aS w wS : ℝ} (hκ1 : κ < 1) (ha : 0 < a) (haS : 0 < aS)
    (hw : 0 < w) (hwS : 0 < wS) :
    Real.log (1 - κ) - (Real.log (w * a) - Real.log (wS * aS)) =
      Real.log ((1 - κ) * (wS * aS) / (w * a)) ∧
      (Real.log ((1 - κ) * (wS * aS) / (w * a)) < 0 ↔ (1 - κ) * (wS * aS) < w * a) := by
  have h1 : 0 < 1 - κ := by linarith
  have hwa : 0 < w * a := mul_pos hw ha
  have hwsa : 0 < wS * aS := mul_pos hwS haS
  constructor
  · rw [Real.log_div (by positivity) hwa.ne', Real.log_mul h1.ne' hwsa.ne']
    ring
  · rw [Real.log_neg_iff (by positivity), div_lt_one hwa]

/-- O&R p. 251, the discrete version: if the integrand `log(1−κ) − (f − g)` is negative on
`(x₀, x₁)` (goods beyond the equilibrium cutoff `x₀`) and continuous, then moving `z^F` from
`x₀` up to `x₁` strictly lowers `log(P/P*)`: Foreign's CPI rises relative to Home's, as the
book says, but only through the goods newly imported at a CIF premium, not through the explicit
`z^F log(1−κ)` term. -/
theorem logRERInCutoff_decreases {κ zH x0 x1 : ℝ} {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hlt : x0 < x1)
    (hneg : ∀ z ∈ Ioo x0 x1, Real.log (1 - κ) - (f z - g z) < 0) :
    logRERInCutoff κ zH f g x1 < logRERInCutoff κ zH f g x0 := by
  have hc : Continuous fun z => f z - g z := hf.sub hg
  have hdiff : logRERInCutoff κ zH f g x1 - logRERInCutoff κ zH f g x0 =
      ∫ z in x0..x1, (Real.log (1 - κ) - (f z - g z)) := by
    unfold logRERInCutoff
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul,
      ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable x0 x1)
        (hc.intervalIntegrable x1 zH)]
    ring
  have hpos : 0 < ∫ z in x0..x1, -(Real.log (1 - κ) - (f z - g z)) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((continuous_const.sub hc).neg.intervalIntegrable _ _)
      (fun z hz => neg_pos.mpr (hneg z hz)) hlt
  rw [intervalIntegral.integral_neg] at hpos
  linarith

end ObstfeldRogoff.RealExchangeRate.DFSPriceIndex

set_option linter.style.longLine false
#print axioms ObstfeldRogoff.RealExchangeRate.CobbDouglasIndex
#print axioms ObstfeldRogoff.RealExchangeRate.CobbDouglasIndex.mk
#print axioms ObstfeldRogoff.RealExchangeRate.CobbDouglasIndex.γ
#print axioms ObstfeldRogoff.RealExchangeRate.CobbDouglasIndex.γ_pos
#print axioms ObstfeldRogoff.RealExchangeRate.CobbDouglasIndex.γ_lt_one
#print axioms ObstfeldRogoff.RealExchangeRate.CobbDouglasIndex.price
#print axioms ObstfeldRogoff.RealExchangeRate.CobbDouglasIndex.price_homogeneous
#print axioms ObstfeldRogoff.RealExchangeRate.CobbDouglasIndex.price_numeraire
#print axioms ObstfeldRogoff.RealExchangeRate.PriceLevels.realExchangeRate
#print axioms ObstfeldRogoff.RealExchangeRate.PriceLevels.absolute_ppp_iff
#print axioms ObstfeldRogoff.RealExchangeRate.PriceLevels.relative_ppp_const
#print axioms ObstfeldRogoff.RealExchangeRate.PriceLevels.lop_ratio
#print axioms ObstfeldRogoff.RealExchangeRate.PriceLevels.price_level_ratio
#print axioms ObstfeldRogoff.RealExchangeRate.PriceLevels.log_price_level_ratio
#print axioms ObstfeldRogoff.RealExchangeRate.PriceLevels.price_level_gt_iff
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.mk
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.f
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.fp
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.f_cont
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.hasDeriv
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.fp_strictAnti
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.fp_cont
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.fp_pos
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.f_zero_nonneg
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.inada_zero
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.inada_infty
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.crs_intensive_form
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.hasDerivAt_of_between
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.mpl
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.tangent_lt
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.tangent_le
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.mpl_pos
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.f_pos
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.mpl_strictMonoOn
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.zero_profit
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.crs_profit_le
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.crs_profit_eq_iff
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.existsUnique_fp_eq
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.kinv
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.kinv_spec
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.kinv_continuousAt
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.kstar
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.kstar_foc
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.kstar_unique
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.kstar_strictAntiOn_r
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.kstar_continuousAt_r
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.kstar_continuousAt_A
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.kstar_hasDerivAt_r
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.wage
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.wage_frontier
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.wage_pos
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.wage_isMax
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.wage_hasDerivAt_r
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.wage_hasDerivAt_A
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.wage_path_hasDerivAt
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.wage_strictAntiOn_r
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.wage_strictMonoOn_A
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.wageRental
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.wageRental_strictMonoOn
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.wageRental_continuousOn
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.existsUnique_wageRental_eq
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.wrInv
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.wrInv_spec
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.wrInv_continuousAt
#print axioms ObstfeldRogoff.RealExchangeRate.CRSProduction.IntensiveTech.wrInv_strictMonoOn
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.IsSupplyEqm
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.kN
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.unitCost
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.eqmPrice
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.muLT
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.muKT
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.muLN
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.muKN
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.kN_spec
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.unitCost_foc
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.unitCost_le
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.unitCost_zero_profit
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.unitCost_path_hasDerivAt
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.supplyEqm_exists
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.supplyEqm_unique
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.supplyEqm_existsUnique
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.eqmPrice_pos
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.kN_strictMonoOn_w
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.unitCost_strictMonoOn_w
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.eqmPrice_strictMonoOn_AT
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.eqm_kN_strictMonoOn_AT
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.eqm_AN_neutral
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.muKT_add_muLT
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.muKN_add_muLN
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.muKN_sub_muKT
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.muLT_pos
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.muLN_pos
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.muLN_div_muLT
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.logWage_path_hasDerivAt
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.logPrice_path_hasDerivAt
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.logPrice_hat_eq9
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.logPrice_hat_r
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.bs_price_growth_ge
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.bs_price_rises
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.bs_sign_counterexample
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.eqm_logPrice_deriv_pos
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.price_falls_with_r
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.price_r_boundary
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.r_elasticity_neg_iff
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.hbs_log_ratio
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.hbs_path_hasDerivAt
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.hbs_common_shares
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.hbs_sign
#print axioms ObstfeldRogoff.RealExchangeRate.BalassaSamuelson.cobbDouglas_labourShare
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.threeFactor_solves
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.threeFactor_unique
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.threeFactor_price
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.threeFactor_hbs
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.immobileCapital_unique
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.immobileCapital_degenerate
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.immobileCapital_price
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.ex1_zero_max_profit
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.ex1_wage_hat
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.priceN_wage_path
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.ex1_labour_reallocation
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.ex2_rise_in_r
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.ex2_price_falls_iff
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.ex6_lifetime_earnings
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.ex6_foc
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.ex6_optimal_schooling
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.ex6_relative_wage
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.skillWage
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.ex6_dlogw_dalpha
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.ex6_w_increasing_in_alpha_iff
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.ex6_w_strictMono_A
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.ex6_w_strictAnti_pi
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.ex6_w_strictAnti_r
#print axioms ObstfeldRogoff.RealExchangeRate.BSExtensions.ex6e_price_increasing_in_w
#print axioms ObstfeldRogoff.RealExchangeRate.LongRunGDPGNP.gdp_line
#print axioms ObstfeldRogoff.RealExchangeRate.LongRunGDPGNP.gdp_slope_gt_one_iff
#print axioms ObstfeldRogoff.RealExchangeRate.LongRunGDPGNP.gdp_eq_factor_income
#print axioms ObstfeldRogoff.RealExchangeRate.LongRunGDPGNP.trade_balance_long_run
#print axioms ObstfeldRogoff.RealExchangeRate.LongRunGDPGNP.foreign_asset_change
#print axioms ObstfeldRogoff.RealExchangeRate.LongRunGDPGNP.wealth_rise_trade_balance
#print axioms ObstfeldRogoff.RealExchangeRate.LongRunGDPGNP.tradables_output_falls
#print axioms ObstfeldRogoff.RealExchangeRate.LongRunGDPGNP.autarky_frontier_inside_gnp
#print axioms ObstfeldRogoff.RealExchangeRate.LongRunGDPGNP.autarky_frontier_eq_gnp_iff
#print axioms ObstfeldRogoff.RealExchangeRate.ManufacturingEmployment.employment_growth
#print axioms ObstfeldRogoff.RealExchangeRate.ManufacturingEmployment.cesDemandN
#print axioms ObstfeldRogoff.RealExchangeRate.ManufacturingEmployment.hasDerivAt_log_cesDemandN
#print axioms ObstfeldRogoff.RealExchangeRate.ManufacturingEmployment.wealth_growth
#print axioms ObstfeldRogoff.RealExchangeRate.ManufacturingEmployment.employment_effect
#print axioms ObstfeldRogoff.RealExchangeRate.ManufacturingEmployment.employment_effect_unit
#print axioms ObstfeldRogoff.RealExchangeRate.ManufacturingEmployment.psi_lt_one_iff
#print axioms ObstfeldRogoff.RealExchangeRate.ManufacturingEmployment.employment_falls
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesIndex
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesDenom
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesPrice
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesDemandT
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesDemandN
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesDenom_pos
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesPrice_eq_denom_rpow
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesPrice_pos
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesPrice_rpow_one_sub
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesDemand_budget
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesDemand_ratio
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesDemandT_eq
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesDemandN_eq
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesIndex_demand
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesDemand_eq_price_form
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.ces_rpow_le_tangent
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.ces_tangent_le_rpow
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesDemand_foc
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesIndex_le_div_price
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesPrice_isLeast_cost
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesPrice_strictMonoOn
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesPrice_logDeriv_at_one
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.ces_powerMean_tendsto
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.ces_tendsto_one_sub_punctured
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesPrice_tendsto_cobbDouglas
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesPrice_tendsto_model
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesIndex_tendsto_cobbDouglas
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cesDemand_elasticity
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cobbDouglas_mrs
#print axioms ObstfeldRogoff.RealExchangeRate.CESIndex.cobbDouglas_price_exercise8a
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.grossRealRate
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.realDiscount
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.realDiscount_zero
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.grossRealRate_pos
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.realDiscount_eq
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.realDiscount_pos
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.euler_real_rate
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.real_budget
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.consumption_path_of_euler
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.consumption_of_budget
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.consumption_function
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.consumption_function_price_form
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.real_wealth_independent_of_future_prices
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.capital_partial_sum
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.capital_eq_present_value
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.national_budget
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.tradables_budget
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.euler_isoelastic
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.euler_tradables
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.tradables_consumption_path
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.tradables_consumption_function
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.current_account_tradables
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.tradables_consumption_gt_constant_price
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.tradables_consumption_lt_constant_price
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.ex3_gross_rate_identity
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.ex3_alternative_budget
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.ex3_alternative_consumption
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.ex3_real_current_account
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.ex4_price_div_eq
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.ex4_ratio_strictMonoOn
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.ex4Invariant
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.ex4Invariant_strictMonoOn
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.ex4_invariant_step
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.ex4a_constant
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.ex4a_level
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.ex4b_step
#print axioms ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics.ex4b_current_account_surplus
#print axioms ObstfeldRogoff.RealExchangeRate.EndogenousLabour.wage_rpow_eq
#print axioms ObstfeldRogoff.RealExchangeRate.EndogenousLabour.leisure_demand
#print axioms ObstfeldRogoff.RealExchangeRate.EndogenousLabour.labour_income_rewrite
#print axioms ObstfeldRogoff.RealExchangeRate.EndogenousLabour.tradables_consumption_67
#print axioms ObstfeldRogoff.RealExchangeRate.EndogenousLabour.tradables_consumption_68
#print axioms ObstfeldRogoff.RealExchangeRate.EndogenousLabour.exercise5_tradables_consumption
#print axioms ObstfeldRogoff.RealExchangeRate.CostlyCapital.employment_nontradables
#print axioms ObstfeldRogoff.RealExchangeRate.CostlyCapital.price_nontradables
#print axioms ObstfeldRogoff.RealExchangeRate.CostlyCapital.price_strictAnti_capital
#print axioms ObstfeldRogoff.RealExchangeRate.CostlyCapital.value_marginal_product
#print axioms ObstfeldRogoff.RealExchangeRate.CostlyCapital.qDrift
#print axioms ObstfeldRogoff.RealExchangeRate.CostlyCapital.steady_state_iff
#print axioms ObstfeldRogoff.RealExchangeRate.CostlyCapital.steady_capital_labour
#print axioms ObstfeldRogoff.RealExchangeRate.CostlyCapital.hasDerivAt_qDrift_q
#print axioms ObstfeldRogoff.RealExchangeRate.CostlyCapital.hasDerivAt_qDrift_K
#print axioms ObstfeldRogoff.RealExchangeRate.CostlyCapital.charPolyJ
#print axioms ObstfeldRogoff.RealExchangeRate.CostlyCapital.charPolyJ_eq_det
#print axioms ObstfeldRogoff.RealExchangeRate.CostlyCapital.charPolyJ_disc_pos
#print axioms ObstfeldRogoff.RealExchangeRate.CostlyCapital.stable_root_mem
#print axioms ObstfeldRogoff.RealExchangeRate.CostlyCapital.rootJ
#print axioms ObstfeldRogoff.RealExchangeRate.CostlyCapital.rootJ_isRoot
#print axioms ObstfeldRogoff.RealExchangeRate.CostlyCapital.saddle_point
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.relProductivity
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.relProductivity_strictAntiOn
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.home_cheaper_iff
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.relWageSchedule
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.relWage_of_market_clearing
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.relWageSchedule_strictMonoOn
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.relWageSchedule_lt_of_lam_lt
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.cutoffGap
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.cutoffGap_eq_zero_iff
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.cutoffGap_strictAntiOn
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.cutoff_exists_unique
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.home_produces_iff
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.labour_rise_statics
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.productivity_rise_statics
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.freeTradePrice
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.freeTradePrice_home
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.freeTradePrice_foreign
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.homeRealWage_eq
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.foreignRealWage_eq
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.labour_rise_home_realWage_own
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.labour_rise_home_realWage_other
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.labour_rise_foreign_realWage_homeGoods
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.labour_rise_foreign_realWage_own
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.labour_rise_foreign_realWage_relocated
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.productivity_rise_home_realWage
#print axioms ObstfeldRogoff.RealExchangeRate.DFSStatic.productivity_rise_foreign_realWage
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.steadyRate
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.currentAccount
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.currentAccount_home_eq_neg_foreign
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.euler_objective_hasDerivAt
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.euler_foc_iff
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.steady_rate_iff
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.steady_consumption
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.steady_consumption_change
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.log_euler
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.log_one_add_rate_hasDerivAt
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.steadyRate_div_one_add
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.symmetric_cutoff
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.log_odds_hasDerivAt_half
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.log_relProductivity_hasDerivAt_half
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.shockPathUtility
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.shockPathUtility_eq
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.mk
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.β
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.A1
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.ν
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.C
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.CS
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.Cbar
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.CSbar
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.r
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.w
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.wS
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.P
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.dz
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.dB
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.β_pos
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.β_lt_one
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.eq50
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.eq50S
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.eq51
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.eq52
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.eq53
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.eq54
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.fn37
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.cutoffA
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.cutoff43
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.one_add_steadyRate_pos
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.world_consumption
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.rate_relation
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.eq55
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.eq56
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.cutoff_relation
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.cutoff_change
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.eq57
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.eq58_pre
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.bond_relation
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.eq58
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.current_account_deficit
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.eq59
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.half_annuity
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.home_welfare
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.home_welfare_pos_iff
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.foreign_welfare
#print axioms ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount.TemporaryShock.foreign_welfare_pos
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.homePrice
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.foreignPrice
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.home_produces_iff
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.foreign_produces_iff
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.cutoff_order
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.nontraded_band
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.relWage_transport
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.expA
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.expA_strictAnti
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.cutoff_link_exp
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.interior_cutoffs_bound
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.Btilde
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.relWage_eq_Btilde
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.Btilde_sub
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.Btilde_strictMonoOn_iff
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.Btilde_lt_of_TB_lt
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.transfer_effect
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.labour_rise_transport
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.productivity_rise_transport
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.homeRealWage_eq
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.foreignRealWage_eq
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.productivity_rise_home_realWage
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.productivity_rise_foreign_realWage
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.productivity_rise_termsOfTrade
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.priceRatio_eq
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.priceRatio_mono
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.fifth_class_priceRatio
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.fifth_class_requires_large_shock
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.log_cif
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.logHomePriceIndex
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.logForeignPriceIndex
#print axioms ObstfeldRogoff.RealExchangeRate.DFSTransportCosts.log_realExchangeRate
#print axioms ObstfeldRogoff.RealExchangeRate.DFSPriceIndex.priceIndex_le_cost
#print axioms ObstfeldRogoff.RealExchangeRate.DFSPriceIndex.priceIndex_attained
#print axioms ObstfeldRogoff.RealExchangeRate.DFSPriceIndex.expenditure_on_interval
#print axioms ObstfeldRogoff.RealExchangeRate.DFSPriceIndex.logPriceIndex_hasDerivAt
#print axioms ObstfeldRogoff.RealExchangeRate.DFSPriceIndex.logRERInCutoff
#print axioms ObstfeldRogoff.RealExchangeRate.DFSPriceIndex.logRERInCutoff_hasDerivAt
#print axioms ObstfeldRogoff.RealExchangeRate.DFSPriceIndex.logRERInCutoff_deriv_zero_at_cutoff
#print axioms ObstfeldRogoff.RealExchangeRate.DFSPriceIndex.cutoff_integrand_eq
#print axioms ObstfeldRogoff.RealExchangeRate.DFSPriceIndex.logRERInCutoff_decreases
