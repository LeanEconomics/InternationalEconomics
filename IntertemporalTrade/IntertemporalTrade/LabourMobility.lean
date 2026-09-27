/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# International labour movements

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§1.5, pp. 45–51. A small country with no international borrowing or lending
(`K₁ = 0`, exogenous `Y₁`) but free trade in labour services at a given world
wage `w`. Output on date 2 is `F(K₂, L₂)` with constant returns (1.33); the
resident supplies `Lᴴ` inelastically, while employment `L₂` may differ.

Contents:
* constant-returns facts (1.34)–(1.36): Euler's theorem from homogeneity, and the
  intensive-form marginal products `F_K = f'(k)`, `F_L = f(k) − f'(k) k`;
* the first-order conditions (1.37)–(1.38), p. 48;
* the factor-price frontier, p. 48: `k'(w) = −1/(k f''(k)) > 0`, `r'(w) = −1/k(w) < 0`;
* the GNP and GDP lines and the autarky PPF, pp. 49–50, including the gains-from-trade
  inequality (GNP line weakly above the PPF, touching only at `B`);
* the pattern of labour trade, p. 50: `wᴬ > w` implies labour imports, `wᴬ < w` exports;
* comparative statics of the autarky wage, p. 50.

Throughout, the intensive production function `f` is strictly concave and twice
differentiable on `k > 0` (the book's implicit assumptions); the Inada condition of
footnote 23 is replaced by explicit interiority hypotheses.
-/

namespace ObstfeldRogoff.IntertemporalTrade.LabourMobility

open Set Filter Topology

/-! ## Constant returns to scale, O&R (1.33)–(1.36), pp. 46–47 -/

/-- Euler's theorem, O&R (1.34), p. 47 and footnote 21: if `F` is homogeneous of degree one,
`F(ξK, ξL) = ξ F(K, L)` for `ξ > 0`, and differentiable at `(K, L)` with partial derivatives
`F_K`, `F_L`, then `F(K, L) = F_K K + F_L L`. -/
theorem euler_of_homogeneous {F : ℝ → ℝ → ℝ} {K L FK FL : ℝ}
    (hhom : ∀ ξ : ℝ, 0 < ξ → F (ξ * K) (ξ * L) = ξ * F K L)
    (hF : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      (FK • ContinuousLinearMap.fst ℝ ℝ ℝ + FL • ContinuousLinearMap.snd ℝ ℝ ℝ) (K, L)) :
    F K L = FK * K + FL * L := by
  have hpath : HasDerivAt (fun ξ : ℝ => (ξ * K, ξ * L)) (K, L) 1 :=
    (hasDerivAt_mul_const K).prodMk (hasDerivAt_mul_const L)
  have hF' : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      (FK • ContinuousLinearMap.fst ℝ ℝ ℝ + FL • ContinuousLinearMap.snd ℝ ℝ ℝ)
      ((fun ξ : ℝ => (ξ * K, ξ * L)) 1) := by
    simpa using hF
  have h1 := hF'.comp_hasDerivAt (1 : ℝ) hpath
  have hev : (fun ξ : ℝ => F (ξ * K) (ξ * L)) =ᶠ[𝓝 1] fun ξ => ξ * F K L := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with ξ hξ
    exact hhom ξ hξ
  have h2 : HasDerivAt (fun ξ : ℝ => F (ξ * K) (ξ * L)) (F K L) 1 :=
    (hasDerivAt_mul_const (F K L)).congr_of_eventuallyEq hev
  have h := h1.unique h2
  simp at h
  linarith

/-- The constant-returns production function written through its intensive form,
`F(K, L) = L f(K/L)`, O&R p. 47. -/
noncomputable def prod (f : ℝ → ℝ) (K L : ℝ) : ℝ := L * f (K / L)

/-- The intensive-form production function is homogeneous of degree one, O&R p. 46. -/
theorem prod_homogeneous (f : ℝ → ℝ) {K L ξ : ℝ} (hξ : 0 < ξ) :
    prod f (ξ * K) (ξ * L) = ξ * prod f K L := by
  unfold prod
  rw [mul_div_mul_left K L hξ.ne']
  ring

/-- Marginal product of capital, O&R (1.35), p. 47: `F_K(K, L) = f'(k)`, `k = K/L`. -/
theorem hasDerivAt_prod_capital {f : ℝ → ℝ} {f'k K L : ℝ} (hL : 0 < L)
    (hf : HasDerivAt f f'k (K / L)) :
    HasDerivAt (fun K => prod f K L) f'k K := by
  have hdiv : HasDerivAt (fun K : ℝ => K / L) (1 / L) K := (hasDerivAt_id K).div_const L
  have h := (hf.comp K hdiv).const_mul L
  exact h.congr_deriv (by field_simp)

/-- Marginal product of labour, O&R (1.36), p. 47: `F_L(K, L) = f(k) − f'(k) k`, `k = K/L`. -/
theorem hasDerivAt_prod_labour {f : ℝ → ℝ} {f'k K L : ℝ} (hL : 0 < L)
    (hf : HasDerivAt f f'k (K / L)) :
    HasDerivAt (fun L => prod f K L) (f (K / L) - f'k * (K / L)) L := by
  have hdiv : HasDerivAt (fun L : ℝ => K / L) (-(K / L ^ 2)) L := by
    have := (hasDerivAt_inv hL.ne').const_mul K
    convert this using 1
    · ext x
      ring
    · ring
  have h := (hasDerivAt_id L).mul (hf.comp L hdiv)
  exact h.congr_deriv (by simp only [id, Function.comp_apply]; field_simp; ring)

/-- Euler's theorem in intensive form, O&R (1.34)–(1.36), p. 47:
`F(K, L) = f'(k) K + (f(k) − f'(k) k) L` with `k = K/L`. -/
theorem prod_eq_euler (f : ℝ → ℝ) (f'k : ℝ) {K L : ℝ} (hL : 0 < L) :
    prod f K L = f'k * K + (f (K / L) - f'k * (K / L)) * L := by
  unfold prod
  field_simp
  ring

/-! ## The household problem and its first-order conditions, O&R p. 48 -/

/-- Date-2 consumption, O&R p. 48: `C₂ = L₂ f(K₂/L₂) − w (L₂ − Lᴴ) + K₂`. -/
noncomputable def consumption2 (f : ℝ → ℝ) (w LH K2 L2 : ℝ) : ℝ :=
  prod f K2 L2 - w * (L2 - LH) + K2

/-- Lifetime utility after substituting both constraints, O&R p. 48:
`u(Y₁ − K₂) + β u(L₂ f(K₂/L₂) − w (L₂ − Lᴴ) + K₂)`. -/
noncomputable def lifetimeUtility (u f : ℝ → ℝ) (β Y1 w LH K2 L2 : ℝ) : ℝ :=
  u (Y1 - K2) + β * u (consumption2 f w LH K2 L2)

/-- Derivative of lifetime utility with respect to `K₂`, O&R p. 48:
`−u'(C₁) + β u'(C₂)(1 + f'(k₂))`. -/
theorem hasDerivAt_lifetimeUtility_capital {u f : ℝ → ℝ} {u'1 u'2 f'k β Y1 w LH K2 L2 : ℝ}
    (hL : 0 < L2) (hu1 : HasDerivAt u u'1 (Y1 - K2))
    (hu2 : HasDerivAt u u'2 (consumption2 f w LH K2 L2))
    (hf : HasDerivAt f f'k (K2 / L2)) :
    HasDerivAt (fun K => lifetimeUtility u f β Y1 w LH K L2)
      (-u'1 + β * (u'2 * (1 + f'k))) K2 := by
  have hC1 : HasDerivAt (fun K : ℝ => Y1 - K) (-1) K2 := by
    simpa using (hasDerivAt_id K2).const_sub Y1
  have hC2 : HasDerivAt (fun K => consumption2 f w LH K L2) (f'k + 1) K2 :=
    ((hasDerivAt_prod_capital hL hf).sub_const (w * (L2 - LH))).add (hasDerivAt_id K2)
  have h := (hu1.comp (h := fun K : ℝ => Y1 - K) K2 hC1).add
    ((hu2.comp (h := fun K => consumption2 f w LH K L2) K2 hC2).const_mul β)
  exact h.congr_deriv (by ring)

/-- Derivative of lifetime utility with respect to `L₂`, O&R p. 48:
`β u'(C₂)(f(k₂) − f'(k₂) k₂ − w)`. -/
theorem hasDerivAt_lifetimeUtility_labour {u f : ℝ → ℝ} {u'2 f'k β Y1 w LH K2 L2 : ℝ}
    (hL : 0 < L2) (hu2 : HasDerivAt u u'2 (consumption2 f w LH K2 L2))
    (hf : HasDerivAt f f'k (K2 / L2)) :
    HasDerivAt (fun L => lifetimeUtility u f β Y1 w LH K2 L)
      (β * (u'2 * (f (K2 / L2) - f'k * (K2 / L2) - w))) L2 := by
  have hw : HasDerivAt (fun L : ℝ => w * (L - LH)) w L2 := by
    simpa using ((hasDerivAt_id L2).sub_const LH).const_mul w
  have hC2 : HasDerivAt (fun L => consumption2 f w LH K2 L)
      (f (K2 / L2) - f'k * (K2 / L2) - w) L2 :=
    ((hasDerivAt_prod_labour hL hf).sub hw).add_const K2
  have h := (hasDerivAt_const L2 (u (Y1 - K2))).add
    ((hu2.comp (h := fun L => consumption2 f w LH K2 L) L2 hC2).const_mul β)
  exact h.congr_deriv (by ring)

/-- The consumption Euler equation, O&R (1.37), p. 48: at an interior optimum in `K₂`,
`u'(C₁) = β [1 + f'(k₂)] u'(C₂)`. -/
theorem euler_equation {u f : ℝ → ℝ} {u'1 u'2 f'k β Y1 w LH K2 L2 : ℝ}
    (hL : 0 < L2) (hu1 : HasDerivAt u u'1 (Y1 - K2))
    (hu2 : HasDerivAt u u'2 (consumption2 f w LH K2 L2))
    (hf : HasDerivAt f f'k (K2 / L2))
    (hmax : IsLocalMax (fun K => lifetimeUtility u f β Y1 w LH K L2) K2) :
    u'1 = β * (1 + f'k) * u'2 := by
  have h := hmax.hasDerivAt_eq_zero (hasDerivAt_lifetimeUtility_capital hL hu1 hu2 hf)
  linarith

/-- Optimal hiring, O&R (1.38), p. 48: at an interior optimum in `L₂`, with `β u'(C₂) ≠ 0`,
the world wage equals the marginal product of labour, `w = f(k₂) − f'(k₂) k₂`. -/
theorem wage_eq_marginal_product {u f : ℝ → ℝ} {u'2 f'k β Y1 w LH K2 L2 : ℝ}
    (hL : 0 < L2) (hu2 : HasDerivAt u u'2 (consumption2 f w LH K2 L2))
    (hf : HasDerivAt f f'k (K2 / L2)) (hβu : β * u'2 ≠ 0)
    (hmax : IsLocalMax (fun L => lifetimeUtility u f β Y1 w LH K2 L) L2) :
    w = f (K2 / L2) - f'k * (K2 / L2) := by
  have h := hmax.hasDerivAt_eq_zero (hasDerivAt_lifetimeUtility_labour (β := β) (Y1 := Y1)
    hL hu2 hf)
  rw [← mul_assoc] at h
  have := (mul_eq_zero.mp h).resolve_left hβu
  linarith

/-! ## Technology: a strictly concave, twice-differentiable intensive form, O&R pp. 47–48 -/

/-- The intensive production function `f(k) = F(k, 1)` of O&R (1.35), p. 47, with its first
and second derivatives. The book's implicit assumptions are made explicit: `f` is continuous on
`k ≥ 0`, twice differentiable on `k > 0`, and strictly concave there (`f'' < 0`). -/
structure Technology where
  f : ℝ → ℝ
  f' : ℝ → ℝ
  f'' : ℝ → ℝ
  continuousOn_f : ContinuousOn f (Ici 0)
  hasDerivAt_f : ∀ k : ℝ, 0 < k → HasDerivAt f (f' k) k
  hasDerivAt_f' : ∀ k : ℝ, 0 < k → HasDerivAt f' (f'' k) k
  f''_neg : ∀ k : ℝ, 0 < k → f'' k < 0

namespace Technology

variable (T : Technology)

/-- Diminishing marginal product of capital (O&R p. 48): `f'` is strictly decreasing on
`k > 0`. -/
theorem f'_strictAntiOn : StrictAntiOn T.f' (Ioi 0) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioi 0)
    (fun x hx => (T.hasDerivAt_f' x hx).continuousAt.continuousWithinAt) (fun x hx => ?_)
    (fun x hx => T.f''_neg x (by rwa [interior_Ioi] at hx))
  rw [interior_Ioi] at hx ⊢
  exact (T.hasDerivAt_f' x hx).hasDerivWithinAt

/-- Strict concavity as a strict supporting-line inequality (used for O&R pp. 49–50):
for `x ≥ 0`, `y > 0`, `x ≠ y`, `f(x) < f(y) + f'(y)(x − y)`. -/
theorem f_lt_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hxy : x ≠ y) :
    T.f x < T.f y + T.f' y * (x - y) := by
  rcases lt_or_gt_of_ne hxy with h | h
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope T.f T.f' h
      (T.continuousOn_f.mono fun z hz => le_trans hx hz.1)
      (fun z hz => T.hasDerivAt_f z (lt_of_le_of_lt hx hz.1))
    have hc0 : 0 < c := lt_of_le_of_lt hx hc.1
    have hlt : T.f' y < T.f' c := T.f'_strictAntiOn hc0 hy hc.2
    have hyx : 0 < y - x := sub_pos.2 h
    rw [eq_div_iff hyx.ne'] at hcs
    have := mul_lt_mul_of_pos_right hlt hyx
    linarith
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope T.f T.f' h
      (T.continuousOn_f.mono fun z hz => le_trans hy.le hz.1)
      (fun z hz => T.hasDerivAt_f z (lt_trans hy hz.1))
    have hc0 : 0 < c := lt_trans hy hc.1
    have hlt : T.f' c < T.f' y := T.f'_strictAntiOn hy hc0 hc.1
    have hxy' : 0 < x - y := sub_pos.2 h
    rw [eq_div_iff hxy'.ne'] at hcs
    have := mul_lt_mul_of_pos_right hlt hxy'
    linarith

/-- Weak supporting-line inequality: for `x ≥ 0`, `y > 0`, `f(x) ≤ f(y) + f'(y)(x − y)`. -/
theorem f_le_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    T.f x ≤ T.f y + T.f' y * (x - y) := by
  rcases eq_or_ne x y with h | h
  · subst h
    simp
  · exact (T.f_lt_tangent hx hy h).le

/-- The marginal product of labour as a function of the capital-labour ratio,
`k ↦ f(k) − f'(k) k`, O&R (1.36), p. 47 and (1.38), p. 48. -/
def wage (k : ℝ) : ℝ := T.f k - T.f' k * k

/-- Derivative of the wage map, O&R p. 48: `d/dk [f(k) − f'(k) k] = −k f''(k)`. -/
theorem hasDerivAt_wage {k : ℝ} (hk : 0 < k) :
    HasDerivAt T.wage (-(k * T.f'' k)) k := by
  have h := (T.hasDerivAt_f k hk).sub ((T.hasDerivAt_f' k hk).mul (hasDerivAt_id k))
  exact h.congr_deriv (by simp only [id]; ring)

/-- The wage map is strictly increasing on `k > 0` (its derivative `−k f''(k)` is positive),
O&R p. 48; hence (1.38) pins down `k₂` uniquely. -/
theorem wage_strictMonoOn : StrictMonoOn T.wage (Ioi 0) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fun k => -(k * T.f'' k)) (convex_Ioi 0)
    (fun x hx => (T.hasDerivAt_wage hx).continuousAt.continuousWithinAt) (fun x hx => ?_)
    (fun x hx => ?_)
  · rw [interior_Ioi] at hx ⊢
    exact (T.hasDerivAt_wage hx).hasDerivWithinAt
  · rw [interior_Ioi] at hx
    exact neg_pos.2 (mul_neg_of_pos_of_neg hx (T.f''_neg x hx))

/-- The set of world wages attainable on the factor-price frontier, `{f(k) − f'(k) k : k > 0}`
(O&R p. 48). -/
def wageRange : Set ℝ := T.wage '' Ioi 0

/-- The capital-labour ratio `k(w)` solving `w = f(k) − f'(k) k`, O&R p. 48 (the inverse of the
wage map on `k > 0`). -/
noncomputable def kOf (w : ℝ) : ℝ := Function.invFunOn T.wage (Ioi 0) w

/-- The domestic interest rate on the factor-price frontier, `r(w) = f'(k(w))`, O&R p. 48. -/
noncomputable def rOf (w : ℝ) : ℝ := T.f' (T.kOf w)

/-- `k(w) > 0` on the frontier, O&R p. 48. -/
theorem kOf_pos {w : ℝ} (hw : w ∈ T.wageRange) : 0 < T.kOf w :=
  Function.invFunOn_mem hw

/-- `k(w)` solves the optimal-hiring condition (1.38), O&R p. 48: `f(k(w)) − f'(k(w)) k(w) = w`.
-/
theorem wage_kOf {w : ℝ} (hw : w ∈ T.wageRange) : T.wage (T.kOf w) = w :=
  Function.invFunOn_eq hw

/-- `k(·)` inverts the wage map: `k(f(k) − f'(k)k) = k` for `k > 0`, O&R p. 48. -/
theorem kOf_wage {k : ℝ} (hk : 0 < k) : T.kOf (T.wage k) = k :=
  T.wage_strictMonoOn.injOn (T.kOf_pos ⟨k, hk, rfl⟩) hk (T.wage_kOf ⟨k, hk, rfl⟩)

/-- A rise in the world wage raises the optimal capital intensity, O&R p. 48:
`k(w)` is strictly increasing on the frontier. -/
theorem kOf_strictMonoOn : StrictMonoOn T.kOf T.wageRange := by
  intro a ha b hb hab
  rw [← T.wage_kOf ha, ← T.wage_kOf hb] at hab
  exact (T.wage_strictMonoOn.lt_iff_lt (T.kOf_pos ha) (T.kOf_pos hb)).mp hab

/-- The factor-price frontier slopes down, O&R p. 48: `r(w)` is strictly decreasing. -/
theorem rOf_strictAntiOn : StrictAntiOn T.rOf T.wageRange :=
  fun _ ha _ hb hab => T.f'_strictAntiOn (T.kOf_pos ha) (T.kOf_pos hb)
    (T.kOf_strictMonoOn ha hb hab)

/-- `k(w)` is continuous at interior points of the frontier (O&R p. 48). -/
theorem continuousAt_kOf {w : ℝ} (hW : T.wageRange ∈ 𝓝 w) : ContinuousAt T.kOf w :=
  T.kOf_strictMonoOn.continuousAt_of_image_mem_nhds hW
    (mem_of_superset (Ioi_mem_nhds (T.kOf_pos (mem_of_mem_nhds hW)))
      fun k hk => ⟨T.wage k, ⟨k, hk, rfl⟩, T.kOf_wage hk⟩)

/-- Slope of `k(w)`, O&R p. 48: `k'(w) = −1/(k(w) f''(k(w)))`. -/
theorem hasDerivAt_kOf {w : ℝ} (hW : T.wageRange ∈ 𝓝 w) :
    HasDerivAt T.kOf (-1 / (T.kOf w * T.f'' (T.kOf w))) w := by
  have hk := T.kOf_pos (mem_of_mem_nhds hW)
  have hne : -(T.kOf w * T.f'' (T.kOf w)) ≠ 0 :=
    neg_ne_zero.2 (mul_neg_of_pos_of_neg hk (T.f''_neg _ hk)).ne
  have h := HasDerivAt.of_local_left_inverse (T.continuousAt_kOf hW) (T.hasDerivAt_wage hk) hne
    (by filter_upwards [hW] with y hy using T.wage_kOf hy)
  exact h.congr_deriv (by rw [inv_neg, neg_div, one_div])

/-- The slope `k'(w) = −1/(k f''(k))` is positive, O&R p. 48. -/
theorem kOf_slope_pos {w : ℝ} (hw : w ∈ T.wageRange) :
    0 < -1 / (T.kOf w * T.f'' (T.kOf w)) :=
  div_pos_of_neg_of_neg (by norm_num)
    (mul_neg_of_pos_of_neg (T.kOf_pos hw) (T.f''_neg _ (T.kOf_pos hw)))

/-- Slope of the factor-price frontier, O&R p. 48: `r'(w) = f''(k(w)) k'(w) = −1/k(w) < 0`. -/
theorem hasDerivAt_rOf {w : ℝ} (hW : T.wageRange ∈ 𝓝 w) :
    HasDerivAt T.rOf (-1 / T.kOf w) w := by
  have hk := T.kOf_pos (mem_of_mem_nhds hW)
  have hf'' := (T.f''_neg _ hk).ne
  exact ((T.hasDerivAt_f' _ hk).comp w (T.hasDerivAt_kOf hW)).congr_deriv (by field_simp)

/-! ## Zero profits on the factor-price frontier, O&R (1.34) and pp. 49–50 -/

/-- Euler's theorem with factor prices, O&R (1.34)–(1.36): for `L > 0`,
`F(K, L) = f'(k) K + (f(k) − f'(k) k) L`, `k = K/L`. -/
theorem prod_eq_factor_payments {K L : ℝ} (hL : 0 < L) :
    prod T.f K L = T.f' (K / L) * K + T.wage (K / L) * L :=
  prod_eq_euler T.f (T.f' (K / L)) hL

/-- The CRS profit inequality behind the gains from trade, O&R pp. 49–50: at factor prices
`(f'(k*), f(k*) − f'(k*)k*)`, `F(K, L) ≤ f'(k*) K + w(k*) L` for all `K ≥ 0`, `L > 0`. -/
theorem prod_le_factor_payments {ks K L : ℝ} (hks : 0 < ks) (hK : 0 ≤ K) (hL : 0 < L) :
    prod T.f K L ≤ T.f' ks * K + T.wage ks * L := by
  have h := mul_le_mul_of_nonneg_left (T.f_le_tangent (div_nonneg hK hL.le) hks) hL.le
  have he : L * (T.f ks + T.f' ks * (K / L - ks)) = T.f' ks * K + T.wage ks * L := by
    unfold wage
    field_simp
    ring
  unfold prod
  linarith

/-- Strict version of the profit inequality: `F(K, L) < f'(k*) K + w(k*) L` unless
`K = k* L` (O&R p. 50: the GNP line touches the PPF only at `B`). -/
theorem prod_lt_factor_payments {ks K L : ℝ} (hks : 0 < ks) (hK : 0 ≤ K) (hL : 0 < L)
    (hne : K ≠ ks * L) : prod T.f K L < T.f' ks * K + T.wage ks * L := by
  have hne' : K / L ≠ ks := fun h => hne ((div_eq_iff hL.ne').mp h)
  have h := mul_lt_mul_of_pos_left (T.f_lt_tangent (div_nonneg hK hL.le) hks hne') hL
  have he : L * (T.f ks + T.f' ks * (K / L - ks)) = T.f' ks * K + T.wage ks * L := by
    unfold wage
    field_simp
    ring
  unfold prod
  linarith

/-- Zero profits on the frontier, O&R p. 49: `F(K, L) − r(w) K − w L ≤ 0` for `K ≥ 0`,
`L > 0`. -/
theorem profit_nonpos {w K L : ℝ} (hw : w ∈ T.wageRange) (hK : 0 ≤ K) (hL : 0 < L) :
    prod T.f K L - T.rOf w * K - w * L ≤ 0 := by
  have h := T.prod_le_factor_payments (T.kOf_pos hw) hK hL
  rw [T.wage_kOf hw] at h
  unfold rOf
  linarith

/-- Profits are exactly zero iff the firm uses the frontier capital-labour ratio,
`K = k(w) L` (O&R p. 49). -/
theorem profit_eq_zero_iff {w K L : ℝ} (hw : w ∈ T.wageRange) (hK : 0 ≤ K) (hL : 0 < L) :
    prod T.f K L - T.rOf w * K - w * L = 0 ↔ K = T.kOf w * L := by
  constructor
  · intro h
    by_contra hne
    have h' := T.prod_lt_factor_payments (T.kOf_pos hw) hK hL hne
    rw [T.wage_kOf hw] at h'
    unfold rOf at h
    linarith
  · intro h
    have he := T.prod_eq_factor_payments (K := K) hL
    rw [h, mul_div_cancel_right₀ _ hL.ne', T.wage_kOf hw] at he
    rw [h]
    unfold rOf
    linarith

/-! ## The GNP line, the GDP line and the autarky PPF, O&R pp. 48–50 -/

/-- With free labour trade, date-2 consumption lies on or below the GNP line, O&R pp. 48–49:
`C₂(K₂, L₂) ≤ [1 + r(w)] K₂ + w Lᴴ` for every hiring choice `L₂ > 0`. -/
theorem consumption2_le_gnp {w LH K2 L2 : ℝ} (hw : w ∈ T.wageRange) (hK : 0 ≤ K2)
    (hL : 0 < L2) : consumption2 T.f w LH K2 L2 ≤ (1 + T.rOf w) * K2 + w * LH := by
  have h := T.profit_nonpos hw hK hL
  unfold consumption2
  linarith

/-- Date-2 consumption reaches the GNP line exactly under optimal hiring `K₂ = k(w) L₂`,
O&R (1.38) and p. 49. -/
theorem consumption2_eq_gnp_iff {w LH K2 L2 : ℝ} (hw : w ∈ T.wageRange) (hK : 0 ≤ K2)
    (hL : 0 < L2) :
    consumption2 T.f w LH K2 L2 = (1 + T.rOf w) * K2 + w * LH ↔ K2 = T.kOf w * L2 := by
  rw [← T.profit_eq_zero_iff hw hK hL]
  unfold consumption2
  constructor <;> intro h <;> linarith

/-- The autarky production possibility frontier, O&R p. 49: `C₂ = F(Y₁ − C₁, Lᴴ) + Y₁ − C₁`. -/
noncomputable def ppf (Y1 LH C1 : ℝ) : ℝ := prod T.f (Y1 - C1) LH + (Y1 - C1)

/-- The GNP line, O&R p. 49: `C₂ = [1 + r(w)](Y₁ − C₁) + w Lᴴ`. -/
noncomputable def gnpLine (w Y1 LH C1 : ℝ) : ℝ := (1 + T.rOf w) * (Y1 - C1) + w * LH

/-- The GDP line, O&R p. 50: `Y₂ + K₂ = [1 + r(w) + w/k(w)](Y₁ − C₁)`. -/
noncomputable def gdpLine (w Y1 C1 : ℝ) : ℝ := (1 + T.rOf w + w / T.kOf w) * (Y1 - C1)

/-- Gains from trade, O&R p. 50: the GNP line lies weakly above the autarky PPF,
for all `C₁ ≤ Y₁`. -/
theorem ppf_le_gnpLine {w Y1 LH C1 : ℝ} (hw : w ∈ T.wageRange) (hC1 : C1 ≤ Y1)
    (hLH : 0 < LH) : T.ppf Y1 LH C1 ≤ T.gnpLine w Y1 LH C1 := by
  have h := T.profit_nonpos hw (sub_nonneg.2 hC1) hLH
  unfold ppf gnpLine
  linarith

/-- The GNP line touches the autarky PPF only at point `B`, where `K₂ = Y₁ − C₁ = k(w) Lᴴ`
(O&R pp. 49–50). -/
theorem ppf_eq_gnpLine_iff {w Y1 LH C1 : ℝ} (hw : w ∈ T.wageRange) (hC1 : C1 ≤ Y1)
    (hLH : 0 < LH) : T.ppf Y1 LH C1 = T.gnpLine w Y1 LH C1 ↔ Y1 - C1 = T.kOf w * LH := by
  rw [← T.profit_eq_zero_iff hw (sub_nonneg.2 hC1) hLH]
  unfold ppf gnpLine
  constructor <;> intro h <;> linarith

/-- Slope of the autarky PPF, O&R p. 49: `−(1 + F_K(Y₁ − C₁, Lᴴ))` for `C₁ < Y₁`. -/
theorem hasDerivAt_ppf {Y1 LH C1 : ℝ} (hC1 : C1 < Y1) (hLH : 0 < LH) :
    HasDerivAt (fun c => T.ppf Y1 LH c) (-(1 + T.f' ((Y1 - C1) / LH))) C1 := by
  have hK : HasDerivAt (fun c : ℝ => Y1 - c) (-1) C1 := by
    simpa using (hasDerivAt_id C1).const_sub Y1
  have hF := hasDerivAt_prod_capital hLH
    (T.hasDerivAt_f _ (div_pos (sub_pos.2 hC1) hLH))
  have h := (hF.comp (h := fun c : ℝ => Y1 - c) C1 hK).add hK
  exact h.congr_deriv (by ring)

/-- At point `B` the GNP line is tangent to the autarky PPF, O&R p. 49: when
`Y₁ − C₁ = k(w) Lᴴ` the PPF has slope `−(1 + r(w))`, the slope of the GNP line. -/
theorem ppf_tangent_at_B {w Y1 LH C1 : ℝ} (hw : w ∈ T.wageRange) (hLH : 0 < LH)
    (hB : Y1 - C1 = T.kOf w * LH) :
    HasDerivAt (fun c => T.ppf Y1 LH c) (-(1 + T.rOf w)) C1 := by
  have hC1 : C1 < Y1 := by nlinarith [T.kOf_pos hw]
  have h := T.hasDerivAt_ppf hC1 hLH
  rwa [hB, mul_div_cancel_right₀ _ hLH.ne'] at h

/-- The GDP line, O&R p. 50: with employment `L₂ = K₂/k(w)` and `K₂ = Y₁ − C₁ > 0`,
`F(K₂, L₂) + K₂ = [1 + r(w) + w/k(w)](Y₁ − C₁)`. -/
theorem gdpLine_eq {w Y1 C1 : ℝ} (hw : w ∈ T.wageRange) (hK : 0 < Y1 - C1) :
    prod T.f (Y1 - C1) ((Y1 - C1) / T.kOf w) + (Y1 - C1) = T.gdpLine w Y1 C1 := by
  have hk := T.kOf_pos hw
  have hwk := T.wage_kOf hw
  unfold prod gdpLine rOf
  rw [div_div_cancel₀ hK.ne']
  set k := T.kOf w
  unfold wage at hwk
  rw [← hwk]
  field_simp
  ring

/-- GDP minus GNP equals net wage payments to foreign workers, O&R p. 50:
`gdp − gnp = w (L₂ − Lᴴ)` with `L₂ = (Y₁ − C₁)/k(w)`. -/
theorem gdpLine_sub_gnpLine (w Y1 LH C1 : ℝ) :
    T.gdpLine w Y1 C1 - T.gnpLine w Y1 LH C1 = w * ((Y1 - C1) / T.kOf w - LH) := by
  unfold gdpLine gnpLine
  ring

/-- The GDP line is steeper than the GNP line, O&R p. 50: for `w > 0`, GDP exceeds GNP
exactly when investment exceeds its level at `B`, `Y₁ − C₁ > k(w) Lᴴ`. -/
theorem gnpLine_lt_gdpLine_iff {w Y1 LH C1 : ℝ} (hw : w ∈ T.wageRange) (hwpos : 0 < w) :
    T.gnpLine w Y1 LH C1 < T.gdpLine w Y1 C1 ↔ T.kOf w * LH < Y1 - C1 := by
  have h := T.gdpLine_sub_gnpLine w Y1 LH C1
  have hk := T.kOf_pos hw
  rw [← sub_pos, h, mul_pos_iff_of_pos_left hwpos, sub_pos, lt_div_iff₀ hk, mul_comm]

/-! ## The pattern of labour trade, O&R p. 50

The autarky equilibrium `A` solves the Euler equation with `L₂ = Lᴴ`,
`u'(Y₁ − Kᴬ) = β[1 + f'(Kᴬ/Lᴴ)] u'(F(Kᴬ, Lᴴ) + Kᴬ)`; the trade equilibrium solves (1.37)
on the GNP line, `u'(Y₁ − Kᵀ) = β[1 + r(w)] u'([1 + r(w)]Kᵀ + w Lᴴ)`, with employment
`L₂ = Kᵀ/k(w)` from (1.38). Strict concavity of `u` enters as `u'` strictly decreasing
and positive. -/

/-- The autarky wage `wᴬ = F_L(Kᴬ, Lᴴ) = f(kᴬ) − f'(kᴬ) kᴬ`, `kᴬ = Kᴬ/Lᴴ`, O&R p. 50. -/
noncomputable def autarkyWage (KA LH : ℝ) : ℝ := T.wage (KA / LH)

/-- An interior Euler equation `u'(C₁) = β X u'(C₂)` with `u' > 0`, `β > 0` forces the gross
return `X` to be positive (used for `1 + f'(k)` at the optima of O&R p. 50). -/
theorem gross_return_pos_of_euler {u' : ℝ → ℝ} {β X C1 C2 : ℝ} (hβ : 0 < β)
    (h1 : 0 < u' C1) (h2 : 0 < u' C2) (hfoc : u' C1 = β * X * u' C2) : 0 < X := by
  by_contra hn
  push Not at hn
  nlinarith [mul_pos hβ h2]

/-- Labour imports, O&R p. 50: if the autarky wage exceeds the world wage, `wᴬ > w`, then
at the trade equilibrium the country employs more labour than it owns, `L₂ = Kᵀ/k(w) > Lᴴ`. -/
theorem labour_imports_of_autarkyWage_gt {u' : ℝ → ℝ}
    (hu'anti : ∀ x y, 0 < x → x < y → u' y < u' x) (hu'pos : ∀ x, 0 < x → 0 < u' x)
    {β Y1 w LH KA KT : ℝ} (hβ : 0 < β) (hLH : 0 < LH) (hKA : 0 < KA)
    (hw : w ∈ T.wageRange) (hC1A : 0 < Y1 - KA) (hC2A : 0 < prod T.f KA LH + KA)
    (hC1T : 0 < Y1 - KT) (hC2T : 0 < (1 + T.rOf w) * KT + w * LH)
    (hfocA : u' (Y1 - KA) = β * (1 + T.f' (KA / LH)) * u' (prod T.f KA LH + KA))
    (hfocT : u' (Y1 - KT) = β * (1 + T.rOf w) * u' ((1 + T.rOf w) * KT + w * LH))
    (hgt : w < T.autarkyWage KA LH) : LH < KT / T.kOf w := by
  have hkB := T.kOf_pos hw
  have hwB := T.wage_kOf hw
  have hkA : 0 < KA / LH := div_pos hKA hLH
  have hk : T.kOf w < KA / LH := by
    rw [← T.wage_strictMonoOn.lt_iff_lt hkB hkA, hwB]
    exact hgt
  have hKB : T.kOf w * LH < KA := (lt_div_iff₀ hLH).mp hk
  have hA := gross_return_pos_of_euler hβ (hu'pos _ hC1A) (hu'pos _ hC2A) hfocA
  have hr := gross_return_pos_of_euler hβ (hu'pos _ hC1T) (hu'pos _ hC2T) hfocT
  have hrA : T.f' (KA / LH) < T.rOf w := T.f'_strictAntiOn hkB hkA hk
  rw [lt_div_iff₀ hkB]
  by_contra hcon
  push Not at hcon
  have hu1 : u' (Y1 - KT) < u' (Y1 - KA) := hu'anti _ _ hC1A (by linarith)
  -- `C₂ᵀ ≤ ppf(B) < C₂ᴬ`
  have hB := T.prod_eq_factor_payments (K := T.kOf w * LH) hLH
  rw [mul_div_cancel_right₀ _ hLH.ne', hwB] at hB
  have hBA := T.prod_le_factor_payments hkA (mul_pos hkB hLH).le hLH (K := T.kOf w * LH)
  have hAA := T.prod_eq_factor_payments (K := KA) hLH
  have h1 : (1 + T.rOf w) * KT ≤ (1 + T.rOf w) * (T.kOf w * LH) :=
    mul_le_mul_of_nonneg_left (by linarith) hr.le
  have h2 : (1 + T.f' (KA / LH)) * (T.kOf w * LH) < (1 + T.f' (KA / LH)) * KA :=
    mul_lt_mul_of_pos_left hKB hA
  have hC2 : (1 + T.rOf w) * KT + w * LH < prod T.f KA LH + KA := by
    unfold rOf at h1 ⊢
    linarith
  have hu2 : u' (prod T.f KA LH + KA) < u' ((1 + T.rOf w) * KT + w * LH) :=
    hu'anti _ _ hC2T hC2
  have h3 : (1 + T.f' (KA / LH)) * u' (prod T.f KA LH + KA) <
      (1 + T.rOf w) * u' ((1 + T.rOf w) * KT + w * LH) :=
    mul_lt_mul'' (by linarith) hu2 hA.le (hu'pos _ hC2A).le
  have h4 := mul_lt_mul_of_pos_left h3 hβ
  rw [← mul_assoc, ← mul_assoc, ← hfocA, ← hfocT] at h4
  linarith

/-- Labour exports, O&R p. 50: if the autarky wage is below the world wage, `wᴬ < w`, then at
the trade equilibrium the country employs less labour than it owns, `L₂ = Kᵀ/k(w) < Lᴴ`. -/
theorem labour_exports_of_autarkyWage_lt {u' : ℝ → ℝ}
    (hu'anti : ∀ x y, 0 < x → x < y → u' y < u' x) (hu'pos : ∀ x, 0 < x → 0 < u' x)
    {β Y1 w LH KA KT : ℝ} (hβ : 0 < β) (hLH : 0 < LH) (hKA : 0 < KA)
    (hw : w ∈ T.wageRange) (hC1A : 0 < Y1 - KA) (hC2A : 0 < prod T.f KA LH + KA)
    (hC1T : 0 < Y1 - KT) (hC2T : 0 < (1 + T.rOf w) * KT + w * LH)
    (hfocA : u' (Y1 - KA) = β * (1 + T.f' (KA / LH)) * u' (prod T.f KA LH + KA))
    (hfocT : u' (Y1 - KT) = β * (1 + T.rOf w) * u' ((1 + T.rOf w) * KT + w * LH))
    (hlt : T.autarkyWage KA LH < w) : KT / T.kOf w < LH := by
  have hkB := T.kOf_pos hw
  have hwB := T.wage_kOf hw
  have hkA : 0 < KA / LH := div_pos hKA hLH
  have hk : KA / LH < T.kOf w := by
    rw [← T.wage_strictMonoOn.lt_iff_lt hkA hkB, hwB]
    exact hlt
  have hKB : KA < T.kOf w * LH := (div_lt_iff₀ hLH).mp hk
  have hA := gross_return_pos_of_euler hβ (hu'pos _ hC1A) (hu'pos _ hC2A) hfocA
  have hr := gross_return_pos_of_euler hβ (hu'pos _ hC1T) (hu'pos _ hC2T) hfocT
  have hrA : T.rOf w < T.f' (KA / LH) := T.f'_strictAntiOn hkA hkB hk
  rw [div_lt_iff₀ hkB]
  by_contra hcon
  push Not at hcon
  have hu1 : u' (Y1 - KA) < u' (Y1 - KT) := hu'anti _ _ hC1T (by linarith)
  -- `C₂ᴬ ≤ gnp(Kᴬ) < gnp(Kᵀ) = C₂ᵀ`
  have hAB := T.prod_le_factor_payments hkB hKA.le hLH (K := KA)
  rw [hwB] at hAB
  have h1 : (1 + T.rOf w) * KA < (1 + T.rOf w) * KT :=
    mul_lt_mul_of_pos_left (by linarith) hr
  have hC2 : prod T.f KA LH + KA < (1 + T.rOf w) * KT + w * LH := by
    unfold rOf at h1 ⊢
    linarith
  have hu2 : u' ((1 + T.rOf w) * KT + w * LH) < u' (prod T.f KA LH + KA) :=
    hu'anti _ _ hC2A hC2
  have h3 : (1 + T.rOf w) * u' ((1 + T.rOf w) * KT + w * LH) <
      (1 + T.f' (KA / LH)) * u' (prod T.f KA LH + KA) :=
    mul_lt_mul'' (by linarith) hu2 hr.le (hu'pos _ hC2T).le
  have h4 := mul_lt_mul_of_pos_left h3 hβ
  rw [← mul_assoc, ← mul_assoc, ← hfocA, ← hfocT] at h4
  linarith

/-! ## Comparative statics of the autarky wage, O&R p. 50 -/

/-- Literal reading of O&R p. 50 ("countries that save more ... have higher autarky wages"):
for given `Lᴴ`, the autarky wage is strictly increasing in autarky saving `Kᴬ = Y₁ − C₁ᴬ`. -/
theorem autarkyWage_lt_of_saving_lt {LH KA KA' : ℝ} (hLH : 0 < LH) (hKA : 0 < KA)
    (hlt : KA < KA') : T.autarkyWage KA LH < T.autarkyWage KA' LH :=
  T.wage_strictMonoOn (div_pos hKA hLH) (div_pos (hKA.trans hlt) hLH)
    (div_lt_div_of_pos_right hlt hLH)

/-- A larger labour endowment lowers the autarky wage, O&R p. 50: if `Kᴬ` and `Kᴬ'` solve the
autarky Euler equation with endowments `Lᴴ < Lᴴ'` (same `Y₁`, `β`), then `wᴬ' < wᴬ`. -/
theorem autarkyWage_anti_labour {u' : ℝ → ℝ}
    (hu'anti : ∀ x y, 0 < x → x < y → u' y < u' x) (hu'pos : ∀ x, 0 < x → 0 < u' x)
    {β Y1 LH LH' KA KA' : ℝ} (hβ : 0 < β) (hLH : 0 < LH) (hLH' : LH < LH')
    (hKA : 0 < KA) (hKA' : 0 < KA') (hC2 : 0 < prod T.f KA LH + KA)
    (hC1' : 0 < Y1 - KA') (hC2' : 0 < prod T.f KA' LH' + KA')
    (hfoc : u' (Y1 - KA) = β * (1 + T.f' (KA / LH)) * u' (prod T.f KA LH + KA))
    (hfoc' : u' (Y1 - KA') = β * (1 + T.f' (KA' / LH')) * u' (prod T.f KA' LH' + KA')) :
    T.autarkyWage KA' LH' < T.autarkyWage KA LH := by
  have hLH'0 : 0 < LH' := hLH.trans hLH'
  have hk : 0 < KA / LH := div_pos hKA hLH
  have hk' : 0 < KA' / LH' := div_pos hKA' hLH'0
  refine T.wage_strictMonoOn hk' hk ?_
  by_contra hcon
  push Not at hcon
  have hA' := gross_return_pos_of_euler hβ (hu'pos _ hC1') (hu'pos _ hC2') hfoc'
  set k := KA / LH with hkdef
  set k' := KA' / LH' with hk'def
  have hKAe : KA = k * LH := by rw [hkdef]; field_simp
  have hKA'e : KA' = k' * LH' := by rw [hk'def]; field_simp
  have hC2e : prod T.f KA LH + KA = LH * (T.f k + k) := by
    unfold prod
    rw [← hkdef, hKAe]
    ring
  have hC2e' : prod T.f KA' LH' + KA' = LH' * (T.f k' + k') := by
    unfold prod
    rw [← hk'def, hKA'e]
    ring
  -- more saving: `Kᴬ < Kᴬ'`
  have hK : KA < KA' := by
    rw [hKAe, hKA'e]
    nlinarith
  have hu1 : u' (Y1 - KA) < u' (Y1 - KA') := hu'anti _ _ hC1' (by linarith)
  -- more date-2 consumption: `C₂ < C₂'`
  have htan := T.f_le_tangent hk.le hk'
  have hmono : T.f k + k ≤ T.f k' + k' := by nlinarith
  have hpos : 0 < T.f k + k := by
    rw [hC2e] at hC2
    exact pos_of_mul_pos_right hC2 hLH.le
  have hC : prod T.f KA LH + KA < prod T.f KA' LH' + KA' := by
    rw [hC2e, hC2e']
    nlinarith
  have hu2 : u' (prod T.f KA' LH' + KA') < u' (prod T.f KA LH + KA) := hu'anti _ _ hC2 hC
  have hf' : T.f' k' ≤ T.f' k := T.f'_strictAntiOn.antitoneOn hk hk' hcon
  have h3 : (1 + T.f' k') * u' (prod T.f KA' LH' + KA') <
      (1 + T.f' k) * u' (prod T.f KA LH + KA) :=
    mul_lt_mul' (by linarith) hu2 (hu'pos _ hC2').le (by linarith)
  have h4 := mul_lt_mul_of_pos_left h3 hβ
  rw [← mul_assoc, ← mul_assoc, ← hfoc, ← hfoc'] at h4
  linarith

/-- Higher saving propensity raises the autarky wage, O&R p. 50: if `Kᴬ` solves the autarky
Euler equation at `(Y₁, β)` and `Kᴬ'` at `(Y₁', β')` with `Y₁ ≤ Y₁'`, `β ≤ β'`, one strictly
(same `Lᴴ`), then autarky saving and hence the autarky wage are strictly higher, `wᴬ < wᴬ'`. -/
theorem autarkyWage_lt_of_more_saving {u' : ℝ → ℝ}
    (hu'anti : ∀ x y, 0 < x → x < y → u' y < u' x) (hu'pos : ∀ x, 0 < x → 0 < u' x)
    {β β' Y1 Y1' LH KA KA' : ℝ} (hβ : 0 < β) (hββ : β ≤ β') (hYY : Y1 ≤ Y1')
    (hstrict : Y1 < Y1' ∨ β < β') (hLH : 0 < LH) (hKA : 0 < KA) (hKA' : 0 < KA')
    (hC1 : 0 < Y1 - KA) (hC2 : 0 < prod T.f KA LH + KA)
    (hC2' : 0 < prod T.f KA' LH + KA')
    (hfoc : u' (Y1 - KA) = β * (1 + T.f' (KA / LH)) * u' (prod T.f KA LH + KA))
    (hfoc' : u' (Y1' - KA') = β' * (1 + T.f' (KA' / LH)) * u' (prod T.f KA' LH + KA')) :
    T.autarkyWage KA LH < T.autarkyWage KA' LH := by
  have hk : 0 < KA / LH := div_pos hKA hLH
  have hk' : 0 < KA' / LH := div_pos hKA' hLH
  refine T.wage_strictMonoOn hk hk' ?_
  by_contra hcon
  push Not at hcon
  have hA := gross_return_pos_of_euler hβ (hu'pos _ hC1) (hu'pos _ hC2) hfoc
  set k := KA / LH with hkdef
  set k' := KA' / LH with hk'def
  have hKAe : KA = k * LH := by rw [hkdef]; field_simp
  have hKA'e : KA' = k' * LH := by rw [hk'def]; field_simp
  have hC2e : prod T.f KA LH + KA = LH * (T.f k + k) := by
    unfold prod
    rw [← hkdef, hKAe]
    ring
  have hC2e' : prod T.f KA' LH + KA' = LH * (T.f k' + k') := by
    unfold prod
    rw [← hk'def, hKA'e]
    ring
  have hK : KA' ≤ KA := by
    rw [hKAe, hKA'e]
    exact mul_le_mul_of_nonneg_right hcon hLH.le
  -- date-1 consumption weakly higher, so `u'(C₁') ≤ u'(C₁)`
  have hC1le : Y1 - KA ≤ Y1' - KA' := by linarith
  have hu1 : u' (Y1' - KA') ≤ u' (Y1 - KA) := by
    rcases hC1le.eq_or_lt with h | h
    · rw [h]
    · exact (hu'anti _ _ hC1 h).le
  -- date-2 consumption weakly lower, so `u'(C₂) ≤ u'(C₂')`
  have htan := T.f_le_tangent hk'.le hk
  have hmono : T.f k' + k' ≤ T.f k + k := by nlinarith
  have hC : prod T.f KA' LH + KA' ≤ prod T.f KA LH + KA := by
    rw [hC2e, hC2e']
    exact mul_le_mul_of_nonneg_left hmono hLH.le
  have hu2 : u' (prod T.f KA LH + KA) ≤ u' (prod T.f KA' LH + KA') := by
    rcases hC.eq_or_lt with h | h
    · rw [h]
    · exact (hu'anti _ _ hC2' h).le
  have hf' : T.f' k ≤ T.f' k' := T.f'_strictAntiOn.antitoneOn hk' hk hcon
  have h3 : (1 + T.f' k) * u' (prod T.f KA LH + KA) ≤
      (1 + T.f' k') * u' (prod T.f KA' LH + KA') :=
    mul_le_mul (by linarith) hu2 (hu'pos _ hC2).le (by linarith)
  have hX : 0 < (1 + T.f' k) * u' (prod T.f KA LH + KA) := mul_pos hA (hu'pos _ hC2)
  rcases hstrict with hY | hb
  · have h4 := mul_le_mul hββ h3 hX.le (hβ.trans_le hββ).le
    rw [← mul_assoc, ← mul_assoc, ← hfoc, ← hfoc'] at h4
    have : u' (Y1' - KA') < u' (Y1 - KA) := hu'anti _ _ hC1 (by linarith)
    linarith
  · have h4 := mul_lt_mul hb h3 hX (hβ.trans hb).le
    rw [← mul_assoc, ← mul_assoc, ← hfoc, ← hfoc'] at h4
    linarith

/-- Under free labour trade a larger labour endowment raises net labour exports,
O&R p. 50: with `w > 0`, if `Kᵀ` and `Kᵀ'` solve (1.37) on the GNP line for `Lᴴ < Lᴴ'`,
then `Lᴴ − Kᵀ/k(w) < Lᴴ' − Kᵀ'/k(w)`. -/
theorem netLabourExports_lt_of_labour_lt {u' : ℝ → ℝ}
    (hu'anti : ∀ x y, 0 < x → x < y → u' y < u' x) (hu'pos : ∀ x, 0 < x → 0 < u' x)
    {β Y1 w LH LH' KT KT' : ℝ} (hβ : 0 < β) (hw : w ∈ T.wageRange) (hwpos : 0 < w)
    (hLH : LH < LH') (hC1T : 0 < Y1 - KT) (hC2T : 0 < (1 + T.rOf w) * KT + w * LH)
    (hC1T' : 0 < Y1 - KT')
    (hfocT : u' (Y1 - KT) = β * (1 + T.rOf w) * u' ((1 + T.rOf w) * KT + w * LH))
    (hfocT' : u' (Y1 - KT') = β * (1 + T.rOf w) * u' ((1 + T.rOf w) * KT' + w * LH')) :
    LH - KT / T.kOf w < LH' - KT' / T.kOf w := by
  have hkB := T.kOf_pos hw
  have hr := gross_return_pos_of_euler hβ (hu'pos _ hC1T) (hu'pos _ hC2T) hfocT
  have hK : KT' < KT := by
    by_contra hcon
    push Not at hcon
    have hu1 : u' (Y1 - KT) ≤ u' (Y1 - KT') := by
      rcases hcon.eq_or_lt with h | h
      · rw [h]
      · exact (hu'anti _ _ hC1T' (by linarith)).le
    have hC : (1 + T.rOf w) * KT + w * LH < (1 + T.rOf w) * KT' + w * LH' := by
      nlinarith
    have hu2 := hu'anti _ _ hC2T hC
    have h4 := mul_lt_mul_of_pos_left hu2 (mul_pos hβ hr)
    rw [← hfocT, ← hfocT'] at h4
    linarith
  have := div_lt_div_of_pos_right hK hkB
  linarith

end Technology

end ObstfeldRogoff.IntertemporalTrade.LabourMobility
