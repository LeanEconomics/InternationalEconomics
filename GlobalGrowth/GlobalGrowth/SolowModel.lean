/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.IntermediateValue

/-!
# The Solow–Swan model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §7.1.1
(pp. 430–437) and §7.2.1.1–7.2.2.1 (pp. 459–464).

* A `Neoclassical` intensive production function `f` (continuous, `f 0 = 0`, strictly
  increasing and strictly concave on `[0, ∞)`, differentiable at positive capital).
  Key lemmas: the average product `f(k)/k` is strictly decreasing, the tangent-line
  inequality, `f'(k) k < f(k)`, and the Inada limits for `f'` imply those for `f(k)/k`.
* A generic one-dimensional result: a continuous, strictly increasing map `G` with
  `G(k)/k` strictly decreasing, crossing the diagonal, has a unique positive fixed point,
  and every positive orbit converges to it monotonically, without overshooting.
* Eq. (8): the normalisation `k' = [(1 - δ) k + s f(k)]/(1 + z)` derived from (1)–(6).
* **Global monotone convergence** of the Solow model (Fig. 7.1), with the hypotheses the
  book leaves unstated made explicit: `δ ≤ 1`, `z + δ > 0`, `1 + z > 0` and Inada-type
  boundary behaviour. Without `δ ≤ 1` monotonicity fails (`solow_overshoots_of_delta_gt_one`).
* Comparative statics (p. 433), the golden rule and dynamic inefficiency (p. 434).
* Cobb–Douglas closed forms (10), the log output equation, MRW arithmetic (pp. 435–437).
* Taxes and the small open economy, eq. (42) (p. 460).
* Convergence speed (43)–(45) (pp. 462–464): `G'(k̄) = μ` and the genuine limit
  `(k_{t+1} - k̄)/(k_t - k̄) → μ` along every orbit; numerical checks.
-/

namespace ObstfeldRogoff.GlobalGrowth.SolowModel

open Set Filter Topology

/-! ## Neoclassical technology -/

/-- A neoclassical intensive production function `f(k) = F(k, 1)` (O&R §7.1.1, p. 432,
fn 3): continuous on `[0, ∞)`, no output without capital, strictly increasing, strictly
concave, and differentiable at every positive capital stock. -/
structure Neoclassical (f : ℝ → ℝ) : Prop where
  cont : ContinuousOn f (Ici 0)
  zero : f 0 = 0
  strictMono : StrictMonoOn f (Ici 0)
  strictConcave : StrictConcaveOn ℝ (Ici 0) f
  diff : ∀ k, 0 < k → DifferentiableAt ℝ f k

variable {f : ℝ → ℝ}

/-- Output is positive at positive capital (O&R p. 432). -/
theorem Neoclassical.pos (hf : Neoclassical f) {k : ℝ} (hk : 0 < k) : 0 < f k := by
  have h := hf.strictMono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hk.le) hk
  rwa [hf.zero] at h

/-- The average product `f(k)/k` is strictly decreasing on positive capital
(strict concavity with `f 0 = 0`; this is what makes the Solow diagram, Fig. 7.1, work). -/
theorem Neoclassical.avg_strictAnti (hf : Neoclassical f) :
    StrictAntiOn (fun k => f k / k) (Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have hθ : 0 < a / b := div_pos ha' hb'
  have hθ1 : 0 < 1 - a / b := by rw [sub_pos, div_lt_one hb']; exact hab
  have hs := hf.strictConcave.2 (mem_Ici.mpr hb'.le) (mem_Ici.mpr (le_refl (0 : ℝ)))
    (ne_of_gt hb') hθ hθ1 (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, hf.zero] at hs
  rw [div_mul_cancel₀ a (ne_of_gt hb')] at hs
  change f b / b < f a / a
  rw [div_lt_div_iff₀ hb' ha']
  have : a / b * f b * b = a * f b := by field_simp
  nlinarith

/-- **Tangent-line inequality** (O&R p. 432, concavity of `f`): `f(y) ≤ f(x) + f'(x)(y - x)`
for `x > 0`, `y ≥ 0`. -/
theorem Neoclassical.tangent_le (hf : Neoclassical f) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    f y ≤ f x + deriv f x * (y - x) := by
  have hd := (hf.diff x hx).hasDerivAt
  rcases lt_trichotomy y x with hlt | heq | hgt
  · have hs := hf.strictConcave.concaveOn.le_slope_of_hasDerivAt (mem_Ici.mpr hy)
      (mem_Ici.mpr hx.le) hlt hd
    rw [slope_def_field] at hs
    have hmul := (le_div_iff₀ (sub_pos.mpr hlt)).mp hs
    nlinarith
  · subst heq; simp
  · have hs := hf.strictConcave.concaveOn.slope_le_of_hasDerivAt (mem_Ici.mpr hx.le)
      (mem_Ici.mpr hy) hgt hd
    rw [slope_def_field] at hs
    have := (div_le_iff₀ (sub_pos.mpr hgt)).mp hs
    linarith

/-- Strict tangent-line inequality for `y ≠ x` (strict concavity, O&R p. 432). -/
theorem Neoclassical.tangent_lt (hf : Neoclassical f) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hne : y ≠ x) : f y < f x + deriv f x * (y - x) := by
  have hd := hf.diff x hx
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hs := hf.strictConcave.deriv_lt_slope (mem_Ici.mpr hy) (mem_Ici.mpr hx.le) hlt hd
    rw [slope_def_field] at hs
    have hmul := (lt_div_iff₀ (sub_pos.mpr hlt)).mp hs
    nlinarith
  · have hs := hf.strictConcave.slope_lt_deriv (mem_Ici.mpr hx.le) (mem_Ici.mpr hy) hgt hd
    rw [slope_def_field] at hs
    have := (div_lt_iff₀ (sub_pos.mpr hgt)).mp hs
    linarith

/-- The marginal product is below the average product: `f'(k) k < f(k)` (O&R p. 434). -/
theorem Neoclassical.deriv_mul_lt (hf : Neoclassical f) {k : ℝ} (hk : 0 < k) :
    deriv f k * k < f k := by
  have h := hf.tangent_lt hk (le_refl 0) (ne_of_lt hk)
  rw [hf.zero] at h
  linarith

/-- The marginal product is positive (strictly increasing and concave `f`). -/
theorem Neoclassical.deriv_pos (hf : Neoclassical f) {k : ℝ} (hk : 0 < k) :
    0 < deriv f k := by
  by_contra hle
  push Not at hle
  have h := hf.tangent_lt hk (by linarith : (0 : ℝ) ≤ k + 1) (by linarith)
  have hm := hf.strictMono (mem_Ici.mpr hk.le) (mem_Ici.mpr (by linarith)) (by linarith :
    k < k + 1)
  nlinarith

/-- The marginal product is strictly decreasing (strict concavity). -/
theorem Neoclassical.deriv_strictAnti (hf : Neoclassical f) :
    StrictAntiOn (deriv f) (Ioi 0) :=
  (hf.strictConcave.subset Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv hf.diff

/-- The Inada condition `f'(0+) = ∞` implies `f(k)/k → ∞` as `k → 0+`. -/
theorem Neoclassical.avg_tendsto_atTop (hf : Neoclassical f)
    (h0 : Tendsto (deriv f) (𝓝[>] 0) atTop) :
    Tendsto (fun k => f k / k) (𝓝[>] 0) atTop := by
  refine tendsto_atTop_mono' _ ?_ h0
  filter_upwards [self_mem_nhdsWithin] with k hk
  have hk' : (0 : ℝ) < k := hk
  rw [le_div_iff₀ hk']
  exact (hf.deriv_mul_lt hk').le

/-- The Inada condition `f'(∞) = 0` implies `f(k)/k → 0` as `k → ∞`. -/
theorem Neoclassical.avg_tendsto_zero (hf : Neoclassical f)
    (hinf : Tendsto (deriv f) atTop (𝓝 0)) :
    Tendsto (fun k => f k / k) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨a, ha, hfa⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hinf.eventually (gt_mem_nhds (half_pos hε)))).exists
  filter_upwards [eventually_gt_atTop (max a (2 * f a / ε + 1))] with k hk
  have hak : a < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hk0 : 0 < k := ha.trans hak
  have hbig : 2 * f a / ε < k := lt_of_lt_of_le (by linarith) (le_of_lt
    (lt_of_le_of_lt (le_max_right _ _) hk))
  have ht := hf.tangent_le ha hk0.le
  have hdpos := hf.deriv_pos ha
  have hpos := hf.pos hk0
  have hfa0 := hf.pos ha
  rw [Real.dist_eq, sub_zero, abs_of_pos (div_pos hpos hk0), div_lt_iff₀ hk0]
  have h1 : 2 * f a < ε * k := by
    have := (div_lt_iff₀ hε).mp hbig
    linarith
  have h2 : deriv f a * (k - a) ≤ ε / 2 * k := by
    have := mul_le_mul_of_nonneg_right hfa.le (sub_nonneg.mpr hak.le)
    nlinarith
  nlinarith

/-- **Cobb–Douglas is neoclassical** (O&R p. 434): `f(k) = k^α`, `0 < α < 1`. -/
theorem neoclassical_rpow {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    Neoclassical (fun k : ℝ => k ^ α) where
  cont := (Real.continuous_rpow_const hα.le).continuousOn
  zero := Real.zero_rpow (ne_of_gt hα)
  strictMono := Real.strictMonoOn_rpow_Ici_of_exponent_pos hα
  strictConcave := Real.strictConcaveOn_rpow hα hα1
  diff := fun _ hk => (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hk))).differentiableAt

/-- The Cobb–Douglas marginal product `f'(k) = α k^{α - 1}` (O&R fn 5, p. 437). -/
theorem deriv_rpow {α k : ℝ} (hk : 0 < k) :
    deriv (fun k : ℝ => k ^ α) k = α * k ^ (α - 1) :=
  (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hk))).deriv

/-! ## A generic one-dimensional convergence theorem -/

/-- **Unique positive fixed point** of a continuous map `G` with `G(k)/k` strictly
decreasing that lies above the diagonal at `a` and below it at `b` (the geometry of
Fig. 7.1, O&R p. 433). -/
theorem fixed_point_existsUnique {G : ℝ → ℝ} (hcont : ContinuousOn G (Ioi 0))
    (hanti : StrictAntiOn (fun k => G k / k) (Ioi 0)) {a b : ℝ} (ha : 0 < a) (hGa : a < G a)
    (hb : 0 < b) (hGb : G b < b) : ∃! k, 0 < k ∧ G k = k := by
  have hra : 1 < G a / a := by rw [lt_div_iff₀ ha]; linarith
  have hrb : G b / b < 1 := by rw [div_lt_iff₀ hb]; linarith
  have hab : a < b := by
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt | heq
    · have := hanti hb ha hlt
      simp only at this
      linarith
    · subst heq; linarith
  have hc : ContinuousOn (fun k => G k - k) (Icc a b) :=
    (hcont.mono (fun x hx => lt_of_lt_of_le ha hx.1)).sub continuousOn_id
  obtain ⟨k, hk, hk0⟩ := intermediate_value_Icc' hab.le hc
    (⟨by linarith, by linarith⟩ : (0 : ℝ) ∈ Icc (G b - b) (G a - a))
  have hkpos : 0 < k := lt_of_lt_of_le ha hk.1
  refine ⟨k, ⟨hkpos, by simp only at hk0; linarith⟩, ?_⟩
  rintro y ⟨hy, hGy⟩
  have h1 : G y / y = 1 := by rw [hGy, div_self (ne_of_gt hy)]
  have h2 : G k / k = 1 := by
    have : G k = k := by simp only at hk0; linarith
    rw [this, div_self (ne_of_gt hkpos)]
  exact hanti.injOn hy hkpos (by rw [h1, h2])

/-- The hypotheses of the generic convergence theorem: a positive, continuous, strictly
increasing map whose ratio `G(k)/k` is strictly decreasing, with positive fixed point
`kbar` (O&R Fig. 7.1). -/
structure MonotoneMap (G : ℝ → ℝ) (kbar : ℝ) : Prop where
  cont : ContinuousOn G (Ioi 0)
  pos : ∀ k, 0 < k → 0 < G k
  strictMono : StrictMonoOn G (Ioi 0)
  ratio_anti : StrictAntiOn (fun k => G k / k) (Ioi 0)
  kbar_pos : 0 < kbar
  fixed : G kbar = kbar

/-- Below the fixed point the map moves strictly up but stays strictly below it. -/
theorem MonotoneMap.step_below {G : ℝ → ℝ} {kbar : ℝ} (hG : MonotoneMap G kbar) {k : ℝ}
    (hk : 0 < k) (hlt : k < kbar) : k < G k ∧ G k < kbar := by
  refine ⟨?_, ?_⟩
  · have h := hG.ratio_anti hk hG.kbar_pos hlt
    simp only [hG.fixed, div_self (ne_of_gt hG.kbar_pos)] at h
    rwa [lt_div_iff₀ hk, one_mul] at h
  · have h := hG.strictMono hk hG.kbar_pos hlt
    rwa [hG.fixed] at h

/-- Above the fixed point the map moves strictly down but stays strictly above it. -/
theorem MonotoneMap.step_above {G : ℝ → ℝ} {kbar : ℝ} (hG : MonotoneMap G kbar) {k : ℝ}
    (hlt : kbar < k) : G k < k ∧ kbar < G k := by
  have hk : 0 < k := hG.kbar_pos.trans hlt
  refine ⟨?_, ?_⟩
  · have h := hG.ratio_anti hG.kbar_pos hk hlt
    simp only [hG.fixed, div_self (ne_of_gt hG.kbar_pos)] at h
    rwa [div_lt_iff₀ hk, one_mul] at h
  · have h := hG.strictMono hG.kbar_pos hk hlt
    rwa [hG.fixed] at h

/-- The fixed point is the only positive fixed point. -/
theorem MonotoneMap.fixed_unique {G : ℝ → ℝ} {kbar : ℝ} (hG : MonotoneMap G kbar) {k : ℝ}
    (hk : 0 < k) (hfix : G k = k) : k = kbar := by
  rcases lt_trichotomy k kbar with hlt | heq | hgt
  · have := (hG.step_below hk hlt).1; linarith
  · exact heq
  · have := (hG.step_above hgt).1; linarith

/-- **Monotone convergence from below** (O&R Fig. 7.1): an orbit starting in
`(0, kbar)` increases strictly, stays below `kbar`, and converges to `kbar`. -/
theorem MonotoneMap.orbit_below {G : ℝ → ℝ} {kbar : ℝ} (hG : MonotoneMap G kbar)
    {k : ℕ → ℝ} (hk : ∀ t, k (t + 1) = G (k t)) (h0 : 0 < k 0) (hlt : k 0 < kbar) :
    StrictMono k ∧ (∀ t, k t < kbar) ∧ Tendsto k atTop (𝓝 kbar) := by
  have hbelow : ∀ t, 0 < k t ∧ k t < kbar := by
    intro t
    induction t with
    | zero => exact ⟨h0, hlt⟩
    | succ t ih =>
      rw [hk t]
      exact ⟨hG.pos _ ih.1, (hG.step_below ih.1 ih.2).2⟩
  have hsm : StrictMono k := strictMono_nat_of_lt_succ fun t => by
    rw [hk t]; exact (hG.step_below (hbelow t).1 (hbelow t).2).1
  refine ⟨hsm, fun t => (hbelow t).2, ?_⟩
  have hL := tendsto_atTop_ciSup hsm.monotone ⟨kbar, by
    rintro _ ⟨t, rfl⟩; exact (hbelow t).2.le⟩
  set L := ⨆ t, k t
  have hLpos : 0 < L := lt_of_lt_of_le h0 (le_ciSup ⟨kbar, by
    rintro _ ⟨t, rfl⟩; exact (hbelow t).2.le⟩ 0)
  have hGL : Tendsto (fun t => G (k t)) atTop (𝓝 (G L)) :=
    ((hG.cont.continuousAt (Ioi_mem_nhds hLpos)).tendsto).comp hL
  have hshift : Tendsto (fun t => k (t + 1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)
  have hfix : G L = L := tendsto_nhds_unique (hGL.congr (fun t => (hk t).symm)) hshift
  rwa [hG.fixed_unique hLpos hfix] at hL

/-- **Monotone convergence from above** (O&R Fig. 7.1): an orbit starting above `kbar`
decreases strictly, stays above `kbar`, and converges to `kbar`. -/
theorem MonotoneMap.orbit_above {G : ℝ → ℝ} {kbar : ℝ} (hG : MonotoneMap G kbar)
    {k : ℕ → ℝ} (hk : ∀ t, k (t + 1) = G (k t)) (hgt : kbar < k 0) :
    StrictAnti k ∧ (∀ t, kbar < k t) ∧ Tendsto k atTop (𝓝 kbar) := by
  have habove : ∀ t, kbar < k t := by
    intro t
    induction t with
    | zero => exact hgt
    | succ t ih => rw [hk t]; exact (hG.step_above ih).2
  have hsa : StrictAnti k := strictAnti_nat_of_succ_lt fun t => by
    rw [hk t]; exact (hG.step_above (habove t)).1
  refine ⟨hsa, habove, ?_⟩
  have hbdd : BddBelow (range k) := ⟨kbar, by rintro _ ⟨t, rfl⟩; exact (habove t).le⟩
  have hL := tendsto_atTop_ciInf hsa.antitone hbdd
  set L := ⨅ t, k t
  have hLk : kbar ≤ L := le_ciInf fun t => (habove t).le
  have hLpos : 0 < L := lt_of_lt_of_le hG.kbar_pos hLk
  have hGL : Tendsto (fun t => G (k t)) atTop (𝓝 (G L)) :=
    ((hG.cont.continuousAt (Ioi_mem_nhds hLpos)).tendsto).comp hL
  have hshift : Tendsto (fun t => k (t + 1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)
  have hfix : G L = L := tendsto_nhds_unique (hGL.congr (fun t => (hk t).symm)) hshift
  rwa [hG.fixed_unique hLpos hfix] at hL

/-- **Global convergence** (O&R Fig. 7.1): every positive orbit converges to `kbar`, is
monotone, and never overshoots: `|k_{t+1} - kbar| ≤ |k_t - kbar|`, strictly unless
`k_t = kbar`. -/
theorem MonotoneMap.orbit_tendsto {G : ℝ → ℝ} {kbar : ℝ} (hG : MonotoneMap G kbar)
    {k : ℕ → ℝ} (hk : ∀ t, k (t + 1) = G (k t)) (h0 : 0 < k 0) :
    Tendsto k atTop (𝓝 kbar) ∧ (Monotone k ∨ Antitone k) ∧
      ∀ t, |k (t + 1) - kbar| ≤ |k t - kbar| := by
  rcases lt_trichotomy (k 0) kbar with hlt | heq | hgt
  · obtain ⟨hsm, hb, hL⟩ := hG.orbit_below hk h0 hlt
    refine ⟨hL, Or.inl hsm.monotone, fun t => ?_⟩
    have h1 := hb (t + 1)
    have h2 := hsm (Nat.lt_succ_self t)
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith [hb t])]
    linarith
  · have hconst : ∀ t, k t = kbar := by
      intro t
      induction t with
      | zero => exact heq
      | succ t ih => rw [hk t, ih, hG.fixed]
    refine ⟨?_, Or.inl ?_, fun t => by rw [hconst, hconst]⟩
    · rw [show k = fun _ => kbar from funext hconst]; exact tendsto_const_nhds
    · intro a b _; rw [hconst, hconst]
  · obtain ⟨hsa, hb, hL⟩ := hG.orbit_above hk hgt
    refine ⟨hL, Or.inr hsa.antitone, fun t => ?_⟩
    have h1 := hb (t + 1)
    have h2 := hsa (Nat.lt_succ_self t)
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith [hb t])]
    linarith

/-- **Local rate equals the derivative** (O&R (44)–(45), made exact): along an orbit
converging to the fixed point without reaching it,
`(k_{t+1} - kbar)/(k_t - kbar) → G'(kbar)`. -/
theorem ratio_tendsto_deriv {G : ℝ → ℝ} {kbar μ : ℝ} (hd : HasDerivAt G μ kbar)
    (hfix : G kbar = kbar) {k : ℕ → ℝ} (hk : ∀ t, k (t + 1) = G (k t))
    (hne : ∀ t, k t ≠ kbar) (hL : Tendsto k atTop (𝓝 kbar)) :
    Tendsto (fun t => (k (t + 1) - kbar) / (k t - kbar)) atTop (𝓝 μ) := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd)
  have hk' : Tendsto k atTop (𝓝[≠] kbar) :=
    tendsto_nhdsWithin_iff.mpr ⟨hL, Eventually.of_forall hne⟩
  refine (hs.comp hk').congr (fun t => ?_)
  simp only [Function.comp_apply, slope_def_field, hk t, hfix]

/-! ## The Solow model -/

/-- The Solow map in efficiency units, eq. (8) (O&R p. 432):
`k' = [(1 - δ) k + s f(k)]/(1 + z)`, `1 + z = (1 + n)(1 + g)`. -/
noncomputable def solowMap (f : ℝ → ℝ) (s δ z k : ℝ) : ℝ := ((1 - δ) * k + s * f k) / (1 + z)

/-- Eq. (8) in difference form (O&R p. 432): `k' - k = [s f(k) - (z + δ) k]/(1 + z)`. -/
theorem solowMap_sub (s δ z k : ℝ) (hz : 1 + z ≠ 0) :
    solowMap f s δ z k - k = (s * f k - (z + δ) * k) / (1 + z) := by
  unfold solowMap
  field_simp
  ring

/-- **Derivation of eq. (8)** (O&R (1)–(7), pp. 431–432). With a constant-returns
`F`, saving `S = sY` (2), accumulation (3), productivity (4) and labour force (5)
growth, capital per efficiency worker `k^E = K/(EL)` (6) follows the Solow map with
`1 + z = (1 + n)(1 + g)`. -/
theorem capital_per_efficiency_worker (F : ℝ → ℝ → ℝ)
    (hCRS : ∀ c K N, 0 < c → F (c * K) (c * N) = c * F K N) {s δ n g : ℝ}
    (hn : 0 < 1 + n) (hg : 0 < 1 + g) {K E L : ℕ → ℝ} (hE : ∀ t, 0 < E t)
    (hLpos : ∀ t, 0 < L t) (h3 : ∀ t, K (t + 1) - K t = s * F (K t) (E t * L t) - δ * K t)
    (h4 : ∀ t, E (t + 1) = (1 + g) * E t) (h5 : ∀ t, L (t + 1) = (1 + n) * L t) (t : ℕ) :
    K (t + 1) / (E (t + 1) * L (t + 1)) =
      solowMap (fun k => F k 1) s δ ((1 + n) * (1 + g) - 1) (K t / (E t * L t)) := by
  have hEL : 0 < E t * L t := mul_pos (hE t) (hLpos t)
  have hF : F (K t) (E t * L t) = E t * L t * F (K t / (E t * L t)) 1 := by
    have := hCRS (E t * L t) (K t / (E t * L t)) 1 hEL
    rw [mul_div_cancel₀ _ (ne_of_gt hEL), mul_one] at this
    exact this
  have hK : K (t + 1) = (1 - δ) * K t + s * (E t * L t * F (K t / (E t * L t)) 1) := by
    rw [← hF]; linarith [h3 t]
  have hne := ne_of_gt hEL
  unfold solowMap
  rw [h4, h5, hK]
  set x := K t / (E t * L t) with hx
  have hKt : K t = x * (E t * L t) := by rw [hx, div_mul_cancel₀ _ hne]
  rw [hKt, div_eq_div_iff (ne_of_gt (mul_pos (mul_pos hg (hE t)) (mul_pos hn (hLpos t))))
    (by nlinarith)]
  ring

/-- Parameters of the Solow model with the implicit conditions made explicit: positive
saving, depreciation at most 100 percent, positive effective dilution `z + δ` and
positive gross growth `1 + z` (O&R pp. 431–433). -/
structure SolowParams (s δ z : ℝ) : Prop where
  saving_pos : 0 < s
  depreciation_le_one : δ ≤ 1
  dilution_pos : 0 < z + δ
  growth_pos : 0 < 1 + z

/-- The Solow map is positive at positive capital. -/
theorem solowMap_pos (hf : Neoclassical f) {s δ z : ℝ} (P : SolowParams s δ z) {k : ℝ}
    (hk : 0 < k) : 0 < solowMap f s δ z k := by
  have := mul_pos P.saving_pos (hf.pos hk)
  have := mul_nonneg (sub_nonneg.mpr P.depreciation_le_one) hk.le
  exact div_pos (by linarith) P.growth_pos

/-- The Solow map is strictly increasing when `δ ≤ 1` (O&R p. 432). -/
theorem solowMap_strictMono (hf : Neoclassical f) {s δ z : ℝ} (P : SolowParams s δ z) :
    StrictMonoOn (solowMap f s δ z) (Ioi 0) := by
  intro a ha b hb hab
  have h1 := hf.strictMono (mem_Ici.mpr (le_of_lt ha)) (mem_Ici.mpr (le_of_lt hb)) hab
  have h2 := mul_le_mul_of_nonneg_left hab.le (sub_nonneg.mpr P.depreciation_le_one)
  have h3 := mul_lt_mul_of_pos_left h1 P.saving_pos
  exact div_lt_div_of_pos_right (by linarith) P.growth_pos

/-- The ratio `G(k)/k = [(1 - δ) + s f(k)/k]/(1 + z)` is strictly decreasing. -/
theorem solowMap_ratio_anti (hf : Neoclassical f) {s δ z : ℝ} (P : SolowParams s δ z) :
    StrictAntiOn (fun k => solowMap f s δ z k / k) (Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have heq : ∀ x : ℝ, 0 < x → solowMap f s δ z x / x = ((1 - δ) + s * (f x / x)) / (1 + z) := by
    intro x hx
    unfold solowMap
    field_simp
  simp only [heq a ha', heq b hb']
  have := mul_lt_mul_of_pos_left (hf.avg_strictAnti ha hb hab) P.saving_pos
  exact div_lt_div_of_pos_right (by linarith) P.growth_pos

/-- The Solow map is continuous on positive capital. -/
theorem solowMap_continuousOn (hf : Neoclassical f) (s δ z : ℝ) :
    ContinuousOn (solowMap f s δ z) (Ioi 0) :=
  ((continuousOn_const.mul continuousOn_id).add
    (continuousOn_const.mul (hf.cont.mono Ioi_subset_Ici_self))).div_const _

/-- The steady state (9) is exactly a fixed point of the Solow map (O&R p. 433). -/
theorem solowMap_fixed_iff {s δ z k : ℝ} (P : SolowParams s δ z) :
    solowMap f s δ z k = k ↔ s * f k = (z + δ) * k := by
  unfold solowMap
  rw [div_eq_iff (ne_of_gt P.growth_pos)]
  constructor <;> intro h <;> linarith

/-- **Existence and uniqueness of the Solow steady state**, eq. (9) (O&R p. 433), from
bracket conditions: saving exceeds break-even investment at some `a > 0` and falls short
of it at some `b > 0`. -/
theorem solow_steady_existsUnique (hf : Neoclassical f) {s δ z : ℝ} (P : SolowParams s δ z)
    {a b : ℝ} (ha : 0 < a) (hsa : (z + δ) * a < s * f a) (hb : 0 < b)
    (hsb : s * f b < (z + δ) * b) : ∃! k, 0 < k ∧ s * f k = (z + δ) * k := by
  have hGa : a < solowMap f s δ z a := by
    unfold solowMap; rw [lt_div_iff₀ P.growth_pos]; linarith
  have hGb : solowMap f s δ z b < b := by
    unfold solowMap; rw [div_lt_iff₀ P.growth_pos]; linarith
  obtain ⟨k, ⟨hk, hfix⟩, huniq⟩ := fixed_point_existsUnique (solowMap_continuousOn hf s δ z)
    (solowMap_ratio_anti hf P) ha hGa hb hGb
  exact ⟨k, ⟨hk, (solowMap_fixed_iff P).mp hfix⟩, fun y hy =>
    huniq y ⟨hy.1, (solowMap_fixed_iff P).mpr hy.2⟩⟩

/-- The Inada conditions on `f'` supply the brackets for (9) (O&R p. 432, Fig. 7.1:
the saving curve starts steeper than the break-even ray and ends flatter). -/
theorem solow_brackets_of_inada (hf : Neoclassical f) {s δ z : ℝ} (P : SolowParams s δ z)
    (h0 : Tendsto (deriv f) (𝓝[>] 0) atTop) (hinf : Tendsto (deriv f) atTop (𝓝 0)) :
    (∃ a, 0 < a ∧ (z + δ) * a < s * f a) ∧ (∃ b, 0 < b ∧ s * f b < (z + δ) * b) := by
  have htarget : 0 < (z + δ) / s := div_pos P.dilution_pos P.saving_pos
  constructor
  · obtain ⟨a, ha, hfa⟩ := ((eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi 0).and
      ((hf.avg_tendsto_atTop h0).eventually (eventually_gt_atTop ((z + δ) / s)))).exists
    have ha' : (0 : ℝ) < a := ha
    refine ⟨a, ha', ?_⟩
    rw [div_lt_div_iff₀ P.saving_pos ha'] at hfa
    linarith
  · obtain ⟨b, hb, hfb⟩ := ((eventually_gt_atTop (0 : ℝ)).and
      ((hf.avg_tendsto_zero hinf).eventually (gt_mem_nhds htarget))).exists
    refine ⟨b, hb, ?_⟩
    rw [div_lt_div_iff₀ hb P.saving_pos] at hfb
    linarith

/-- A Solow steady state makes the Solow map a `MonotoneMap`. -/
theorem solow_monotoneMap (hf : Neoclassical f) {s δ z kbar : ℝ} (P : SolowParams s δ z)
    (hk : 0 < kbar) (hss : s * f kbar = (z + δ) * kbar) :
    MonotoneMap (solowMap f s δ z) kbar where
  cont := solowMap_continuousOn hf s δ z
  pos := fun _ hx => solowMap_pos hf P hx
  strictMono := solowMap_strictMono hf P
  ratio_anti := solowMap_ratio_anti hf P
  kbar_pos := hk
  fixed := (solowMap_fixed_iff P).mpr hss

/-- **Global monotone convergence of the Solow model** (O&R Fig. 7.1, p. 432), in the
precise form: under `0 < s`, `δ ≤ 1`, `z + δ > 0`, `1 + z > 0` and the Inada conditions,
there is a unique positive steady state `kbar` solving (9), and from every `k₀ > 0` the path
of (8) is monotone, never overshoots, and converges to `kbar`. -/
theorem solow_global_convergence (hf : Neoclassical f) {s δ z : ℝ} (P : SolowParams s δ z)
    (h0 : Tendsto (deriv f) (𝓝[>] 0) atTop) (hinf : Tendsto (deriv f) atTop (𝓝 0)) :
    ∃! kbar, 0 < kbar ∧ s * f kbar = (z + δ) * kbar ∧
      ∀ k : ℕ → ℝ, 0 < k 0 → (∀ t, k (t + 1) = solowMap f s δ z (k t)) →
        Tendsto k atTop (𝓝 kbar) ∧ (Monotone k ∨ Antitone k) ∧
          ∀ t, |k (t + 1) - kbar| ≤ |k t - kbar| := by
  obtain ⟨⟨a, ha, hsa⟩, ⟨b, hb, hsb⟩⟩ := solow_brackets_of_inada hf P h0 hinf
  obtain ⟨kbar, ⟨hk, hss⟩, huniq⟩ := solow_steady_existsUnique hf P ha hsa hb hsb
  refine ⟨kbar, ⟨hk, hss, fun k hk0 hrec => ?_⟩, fun y hy => huniq y ⟨hy.1, hy.2.1⟩⟩
  exact (solow_monotoneMap hf P hk hss).orbit_tendsto hrec hk0

/-- Below the steady state capital rises strictly and stays below it (O&R p. 432:
"when the capital stock is low ... `k^E_{t+1} - k^E_t > 0`"). -/
theorem solow_rises_below (hf : Neoclassical f) {s δ z kbar : ℝ} (P : SolowParams s δ z)
    (hk : 0 < kbar) (hss : s * f kbar = (z + δ) * kbar) {k : ℕ → ℝ}
    (hrec : ∀ t, k (t + 1) = solowMap f s δ z (k t)) (h0 : 0 < k 0) (hlt : k 0 < kbar) :
    StrictMono k ∧ ∀ t, k t < kbar :=
  let h := (solow_monotoneMap hf P hk hss).orbit_below hrec h0 hlt
  ⟨h.1, h.2.1⟩

/-- Above the steady state capital falls strictly and stays above it (O&R p. 432). -/
theorem solow_falls_above (hf : Neoclassical f) {s δ z kbar : ℝ} (P : SolowParams s δ z)
    (hk : 0 < kbar) (hss : s * f kbar = (z + δ) * kbar) {k : ℕ → ℝ}
    (hrec : ∀ t, k (t + 1) = solowMap f s δ z (k t)) (hgt : kbar < k 0) :
    StrictAnti k ∧ ∀ t, kbar < k t :=
  let h := (solow_monotoneMap hf P hk hss).orbit_above hrec hgt
  ⟨h.1, h.2.1⟩

/-- **The δ ≤ 1 hypothesis cannot be dropped** (a flag on Fig. 7.1): with `f(k) = √k`,
`s = 1`, `z = 0` and `δ = 3/2`, the steady state is `kbar = 4/9`, but the path from `k₀ = 2`
jumps from above `kbar` to below it, so it is not monotone. -/
theorem solow_overshoots_of_delta_gt_one :
    solowMap Real.sqrt 1 (3 / 2) 0 (4 / 9) = 4 / 9 ∧ 4 / 9 < (2 : ℝ) ∧
      solowMap Real.sqrt 1 (3 / 2) 0 2 < 4 / 9 := by
  have h49 : Real.sqrt (4 / 9) = 2 / 3 := by
    rw [show (4 / 9 : ℝ) = (2 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h2 : Real.sqrt 2 < 13 / 9 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine ⟨?_, by norm_num, ?_⟩
  · unfold solowMap; rw [h49]; norm_num
  · unfold solowMap; linarith

/-! ## Comparative statics (O&R pp. 433–434) -/

/-- **Steady states are ordered by the break-even ratio** (O&R p. 433): if
`(z + δ)/s < (z' + δ')/s'` then the second steady state is strictly smaller. -/
theorem steady_lt_of_ratio_lt (hf : Neoclassical f) {s δ z s' δ' z' k k' : ℝ}
    (hs : 0 < s) (hs' : 0 < s') (hk : 0 < k) (hk' : 0 < k')
    (hss : s * f k = (z + δ) * k) (hss' : s' * f k' = (z' + δ') * k')
    (hlt : (z + δ) / s < (z' + δ') / s') : k' < k := by
  have e1 : f k / k = (z + δ) / s := by
    rw [div_eq_div_iff (ne_of_gt hk) (ne_of_gt hs)]; linarith
  have e2 : f k' / k' = (z' + δ') / s' := by
    rw [div_eq_div_iff (ne_of_gt hk') (ne_of_gt hs')]; linarith
  by_contra hle
  push Not at hle
  have := hf.avg_strictAnti.antitoneOn hk hk' hle
  linarith

/-- A higher saving rate gives a strictly higher steady state (O&R Fig. 7.2, p. 434). -/
theorem steady_strictMono_saving (hf : Neoclassical f) {s s' δ z k k' : ℝ} (hs : 0 < s)
    (hss' : s < s') (hzd : 0 < z + δ) (hk : 0 < k) (hk' : 0 < k')
    (h1 : s * f k = (z + δ) * k) (h2 : s' * f k' = (z + δ) * k') : k < k' :=
  steady_lt_of_ratio_lt hf (hs.trans hss') hs hk' hk h2 h1
    (div_lt_div_of_pos_left hzd hs hss')

/-- Faster population growth or technical progress lowers the steady state: `k̄` is
strictly decreasing in `z = (1 + n)(1 + g) - 1` (O&R p. 433–434). -/
theorem steady_strictAnti_dilution (hf : Neoclassical f) {s δ z z' k k' : ℝ} (hs : 0 < s)
    (hzz : z < z') (hk : 0 < k) (hk' : 0 < k') (h1 : s * f k = (z + δ) * k)
    (h2 : s * f k' = (z' + δ) * k') : k' < k :=
  steady_lt_of_ratio_lt hf hs hs hk hk' h1 h2 (div_lt_div_of_pos_right (by linarith) hs)

/-- A higher depreciation rate lowers the steady state (O&R p. 433). -/
theorem steady_strictAnti_depreciation (hf : Neoclassical f) {s δ δ' z k k' : ℝ}
    (hs : 0 < s) (hδ : δ < δ') (hk : 0 < k) (hk' : 0 < k') (h1 : s * f k = (z + δ) * k)
    (h2 : s * f k' = (z + δ') * k') : k' < k :=
  steady_lt_of_ratio_lt hf hs hs hk hk' h1 h2 (div_lt_div_of_pos_right (by linarith) hs)

/-- `z = (1 + n)(1 + g) - 1` is strictly increasing in population growth `n` (for
`1 + g > 0`) and in productivity growth `g` (for `1 + n > 0`), so `k̄` falls in both. -/
theorem dilution_strictMono {n n' g : ℝ} (hg : 0 < 1 + g) (hn : n < n') :
    (1 + n) * (1 + g) - 1 < (1 + n') * (1 + g) - 1 := by nlinarith

/-- **Long-run growth equals technical progress** (O&R p. 433): along any Solow path,
per-capita output `Y/L = E f(k^E)` grows by a factor tending to `1 + g`, whatever the
saving rate; at the steady state the factor is exactly `1 + g`. -/
theorem output_per_capita_growth_tendsto (hf : Neoclassical f) {g kbar E0 : ℝ}
    (hk : 0 < kbar) {k : ℕ → ℝ} (hL : Tendsto k atTop (𝓝 kbar)) (hE0 : E0 ≠ 0) :
    Tendsto (fun t => (E0 * (1 + g) ^ (t + 1) * f (k (t + 1))) / (E0 * (1 + g) ^ t * f (k t)))
      atTop (𝓝 (1 + g)) := by
  have hfc : ContinuousAt f kbar := (hf.diff kbar hk).continuousAt
  have hf1 := (hfc.tendsto.comp (hL.comp (tendsto_add_atTop_nat 1)))
  have hf0 := hfc.tendsto.comp hL
  have hq := (hf1.div hf0 (ne_of_gt (hf.pos hk))).const_mul (1 + g)
  rw [div_self (ne_of_gt (hf.pos hk)), mul_one] at hq
  have hpos : ∀ᶠ t in atTop, 0 < k t := hL.eventually (lt_mem_nhds hk)
  refine hq.congr' ?_
  filter_upwards [hpos] with t ht
  simp only [Pi.div_apply, Function.comp_apply]
  rcases eq_or_ne (1 + g) 0 with h | h
  · rw [h]; simp
  · have hft := ne_of_gt (hf.pos ht)
    field_simp
    ring

/-! ## The golden rule and dynamic inefficiency (O&R p. 434) -/

/-- Consumption per efficiency worker implied by a capital path in the closed economy:
`c_t = f(k_t) + (1 - δ) k_t - (1 + z) k_{t+1}` (from (3) with `C = Y - I`, p. 432). -/
noncomputable def consumptionOf (f : ℝ → ℝ) (δ z : ℝ) (k : ℕ → ℝ) (t : ℕ) : ℝ :=
  f (k t) + (1 - δ) * k t - (1 + z) * k (t + 1)

/-- On a constant path consumption is `f(k) - (z + δ) k` (O&R p. 434). -/
theorem consumptionOf_const (δ z k : ℝ) (t : ℕ) :
    consumptionOf f δ z (fun _ => k) t = f k - (z + δ) * k := by
  unfold consumptionOf; ring

/-- In a Solow steady state consumption is `(1 - s) f(k̄)` (O&R p. 432). -/
theorem steady_consumption_solow {s δ z k : ℝ} (hss : s * f k = (z + δ) * k) :
    f k - (z + δ) * k = (1 - s) * f k := by linarith

/-- **The golden rule** (O&R p. 434): if `f'(k*) = z + δ` then `k*` strictly maximises
steady-state consumption `f(k) - (z + δ) k` over all other `k ≥ 0`. -/
theorem golden_rule_strict_max (hf : Neoclassical f) {z δ kstar k : ℝ} (hks : 0 < kstar)
    (hgr : deriv f kstar = z + δ) (hk : 0 ≤ k) (hne : k ≠ kstar) :
    f k - (z + δ) * k < f kstar - (z + δ) * kstar := by
  have := hf.tangent_lt hks hk hne
  rw [hgr] at this
  linarith

/-- The golden-rule stock is unique. -/
theorem golden_rule_unique (hf : Neoclassical f) {m k k' : ℝ} (hk : 0 < k) (hk' : 0 < k')
    (h1 : deriv f k = m) (h2 : deriv f k' = m) : k = k' :=
  hf.deriv_strictAnti.injOn hk hk' (h1.trans h2.symm)

/-- **Dynamic inefficiency** (O&R p. 434): if the steady state `k̄` exceeds the golden rule
`k*`, cutting capital to `k*` at date 0 gives strictly more consumption at date 0 and at
every later date than staying at `k̄`: a feasible Pareto improvement. -/
theorem dynamic_inefficiency (hf : Neoclassical f) {z δ kstar kbar : ℝ} (hz : 0 < 1 + z)
    (hks : 0 < kstar) (hgr : deriv f kstar = z + δ) (hlt : kstar < kbar) :
    let k : ℕ → ℝ := fun t => if t = 0 then kbar else kstar
    f kbar - (z + δ) * kbar < consumptionOf f δ z k 0 ∧
      ∀ t, 1 ≤ t → f kbar - (z + δ) * kbar < consumptionOf f δ z k t := by
  intro k
  constructor
  · simp only [consumptionOf, k, ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false]
    nlinarith
  · intro t ht
    have ht0 : t ≠ 0 := by omega
    simp only [consumptionOf, k, ht0, ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false]
    have := golden_rule_strict_max hf hks hgr (hks.trans hlt).le (ne_of_gt hlt)
    linarith

/-! ## Cobb–Douglas closed forms (O&R pp. 434–437) -/

/-- **Eq. (10)** (O&R p. 435): `k̄ = (s/(z + δ))^{1/(1-α)}` solves `s k^α = (z + δ) k`. -/
theorem cobbDouglas_steady {α s m : ℝ} (hα1 : α < 1) (hs : 0 < s) (hm : 0 < m) :
    s * ((s / m) ^ (1 / (1 - α))) ^ α = m * (s / m) ^ (1 / (1 - α)) := by
  have hx : 0 < s / m := div_pos hs hm
  have h1α : (1 - α) ≠ 0 := by linarith
  rw [← Real.rpow_mul hx.le]
  have e : 1 + 1 / (1 - α) * α = 1 / (1 - α) := by field_simp; ring
  have : (s / m) ^ (1 / (1 - α)) = (s / m) * (s / m) ^ (1 / (1 - α) * α) := by
    rw [← Real.rpow_one_add' hx.le (by rw [e]; exact ne_of_gt (div_pos one_pos (by linarith))),
      e]
  rw [this]
  field_simp

/-- The Cobb–Douglas steady state is the unique positive solution of (9). -/
theorem cobbDouglas_steady_unique {α s m k : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s)
    (hm : 0 < m) (hk : 0 < k) (hss : s * k ^ α = m * k) : k = (s / m) ^ (1 / (1 - α)) := by
  have h2 := cobbDouglas_steady hα1 hs hm
  set kb := (s / m) ^ (1 / (1 - α))
  have hpos : 0 < kb := Real.rpow_pos_of_pos (div_pos hs hm) _
  have e1 : k ^ α / k = m / s := by
    rw [div_eq_div_iff (ne_of_gt hk) (ne_of_gt hs)]; linarith
  have e2 : kb ^ α / kb = m / s := by
    rw [div_eq_div_iff (ne_of_gt hpos) (ne_of_gt hs)]; linarith
  exact (neoclassical_rpow hα hα1).avg_strictAnti.injOn hk hpos (by simp only [e1, e2])

/-- **The log output-per-worker equation** (O&R p. 435): with `E_t = E₀(1 + g)^t` and
`Y/L = E_t (k̄)^α`,
`log(Y/L) = log E₀ + t log(1 + g) + (α/(1-α)) [log s - log(z + δ)]`. -/
theorem log_output_per_worker {α s m E0 g : ℝ} (hs : 0 < s) (hm : 0 < m)
    (hE0 : 0 < E0) (hg : 0 < 1 + g) (t : ℕ) :
    Real.log (E0 * (1 + g) ^ t * ((s / m) ^ (1 / (1 - α))) ^ α) =
      Real.log E0 + t * Real.log (1 + g) + α / (1 - α) * (Real.log s - Real.log m) := by
  have hx : 0 < s / m := div_pos hs hm
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_pow, ← Real.rpow_mul hx.le, Real.log_rpow hx,
    Real.log_div (ne_of_gt hs) (ne_of_gt hm)]
  ring

/-- **MRW's implied capital share** (O&R p. 437): the coefficient `α/(1 - α) = 1.42` on
`log s` in (12) implies `α = 1.42/2.42`, which lies strictly between 0.58 and 0.59 (the book
rounds it to 0.59). -/
theorem mrw_implied_alpha {α : ℝ} (hα1 : α < 1) (h : α / (1 - α) = 1.42) :
    α = 1.42 / 2.42 ∧ (0.58 : ℝ) < α ∧ α < 0.59 := by
  have h1α : (1 - α) ≠ 0 := by linarith
  rw [div_eq_iff h1α] at h
  have hα : α = 1.42 / 2.42 := by linarith
  refine ⟨hα, ?_, ?_⟩ <;> rw [hα] <;> norm_num

/-- Steady-state capital scales with the saving rate as `(s'/s)^{1/(1-α)}` (O&R p. 437). -/
theorem cobbDouglas_capital_ratio {α s s' m : ℝ} (hs : 0 < s) (hs' : 0 < s') (hm : 0 < m) :
    (s' / m) ^ (1 / (1 - α)) / (s / m) ^ (1 / (1 - α)) = (s' / s) ^ (1 / (1 - α)) := by
  rw [← Real.div_rpow (div_pos hs' hm).le (div_pos hs hm).le]
  congr 1
  field_simp

/-- **Four times the saving rate** (O&R p. 437): at `α = 1/3` capital is `4^{3/2} = 8`
times higher and output `8^{1/3} = 2` times higher; at `α = 2/3` output is `4^2 = 16`
times higher. -/
theorem fourfold_saving :
    (4 : ℝ) ^ ((1 : ℝ) / (1 - 1 / 3)) = 8 ∧ (8 : ℝ) ^ ((1 : ℝ) / 3) = 2 ∧
      ((4 : ℝ) ^ ((1 : ℝ) / (1 - 2 / 3))) ^ ((2 : ℝ) / 3) = 16 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  · rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  · rw [← Real.rpow_mul (by norm_num), show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num)]
    norm_num

/-! ## Taxes and the small open economy (O&R §7.2.1.1, p. 460) -/

/-- The tax-distorted steady state of eq. (42) (O&R p. 460). -/
noncomputable def taxSteady (α r q : ℝ) : ℝ := (q * α / r) ^ (1 / (1 - α))

/-- **Eq. (42)** (O&R p. 460): in a small open economy with world rate `r^W > 0` and an
output tax `τ < 1`, `k̄ = [(1-τ)α/r^W]^{1/(1-α)}` solves `(1 - τ) f'(k) = r^W` for
`f = k^α`, independently of the saving rate and of initial capital. -/
theorem taxSteady_spec {α r q : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r) (hq : 0 < q) :
    0 < taxSteady α r q ∧ q * (α * taxSteady α r q ^ (α - 1)) = r := by
  have hx : 0 < q * α / r := div_pos (mul_pos hq hα) hr
  refine ⟨Real.rpow_pos_of_pos hx _, ?_⟩
  have h1α : 1 - α ≠ 0 := by linarith
  unfold taxSteady
  rw [← Real.rpow_mul hx.le, show 1 / (1 - α) * (α - 1) = -1 by field_simp; ring,
    Real.rpow_neg_one]
  field_simp

/-- Eq. (42) has only this solution (the marginal product is strictly decreasing). -/
theorem taxSteady_unique {α r q k : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r) (hq : 0 < q)
    (hk : 0 < k) (h : q * (α * k ^ (α - 1)) = r) : k = taxSteady α r q := by
  obtain ⟨hpos, hspec⟩ := taxSteady_spec hα hα1 hr hq
  have hd := (neoclassical_rpow hα hα1).deriv_strictAnti
  refine hd.injOn hk hpos ?_
  simp only [deriv_rpow hk, deriv_rpow hpos]
  have := mul_pos hq hα
  nlinarith

/-- **The elasticity of `k̄` with respect to `1 - τ` is `1/(1-α)`** (O&R p. 460): the
derivative of `log k̄` with respect to `log(1 - τ)` is `1/(1 - α)`, which exceeds one and
equals 3 at `α = 2/3`. -/
theorem taxSteady_elasticity {α r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r) (x : ℝ) :
    HasDerivAt (fun x => Real.log (taxSteady α r (Real.exp x))) (1 / (1 - α)) x ∧
      1 < 1 / (1 - α) := by
  have heq : (fun x => Real.log (taxSteady α r (Real.exp x))) =
      fun x => (1 / (1 - α)) * (x + Real.log α - Real.log r) := by
    funext x
    unfold taxSteady
    have hx : 0 < Real.exp x * α / r := div_pos (mul_pos (Real.exp_pos x) hα) hr
    rw [Real.log_rpow hx, Real.log_div (ne_of_gt (mul_pos (Real.exp_pos x) hα)) (ne_of_gt hr),
      Real.log_mul (Real.exp_pos x).ne' (ne_of_gt hα), Real.log_exp]
  rw [heq]
  refine ⟨?_, by rw [lt_div_iff₀ (by linarith)]; linarith⟩
  have h := ((((hasDerivAt_id x).add_const (Real.log α)).sub_const (Real.log r)).const_mul
    (1 / (1 - α)))
  simpa using h

/-- At `α = 2/3` the elasticity `1/(1-α)` equals 3 (O&R p. 460). -/
theorem tax_elasticity_two_thirds : (1 : ℝ) / (1 - 2 / 3) = 3 := by norm_num

/-- Relative capital intensities of two small open economies facing the same world rate
depend only on their tax rates: `k̄₁/k̄₂ = ((1-τ₁)/(1-τ₂))^{1/(1-α)}` (O&R p. 460). -/
theorem taxSteady_ratio {α r q q' : ℝ} (hα : 0 < α) (hr : 0 < r) (hq : 0 < q) (hq' : 0 < q') :
    taxSteady α r q / taxSteady α r q' = (q / q') ^ (1 / (1 - α)) := by
  unfold taxSteady
  rw [← Real.div_rpow (div_pos (mul_pos hq hα) hr).le (div_pos (mul_pos hq' hα) hr).le]
  congr 1
  field_simp

/-! ## Convergence speed (O&R §7.2.2.1, pp. 462–464) -/

/-- The derivative of the Solow map: `G'(k) = [(1 - δ) + s f'(k)]/(1 + z)`. -/
theorem solowMap_hasDerivAt (hf : Neoclassical f) (s δ z : ℝ) {k : ℝ} (hk : 0 < k) :
    HasDerivAt (solowMap f s δ z) (((1 - δ) + s * deriv f k) / (1 + z)) k := by
  have h := (((hasDerivAt_id k).const_mul (1 - δ)).add
    ((hf.diff k hk).hasDerivAt.const_mul s)).div_const (1 + z)
  have e : solowMap f s δ z = fun x => ((1 - δ) * x + s * f x) / (1 + z) := rfl
  rw [e]
  simpa using h

/-- **Eq. (45)** (O&R p. 462): for Cobb–Douglas, the slope of (43) at the steady state is
`μ = [1 + s α k̄^{α-1}/(1+z) - (z+δ)/(1+z)] = [1 + α z + (α - 1) δ]/(1 + z)`. -/
theorem cobbDouglas_mu {α s δ z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s)
    (hzd : 0 < z + δ) :
    HasDerivAt (solowMap (fun k => k ^ α) s δ z) ((1 + α * z + (α - 1) * δ) / (1 + z))
      ((s / (z + δ)) ^ (1 / (1 - α))) := by
  set kbar := (s / (z + δ)) ^ (1 / (1 - α))
  have hk : 0 < kbar := Real.rpow_pos_of_pos (div_pos hs hzd) _
  have hss := cobbDouglas_steady hα1 hs hzd
  have hd := solowMap_hasDerivAt (neoclassical_rpow hα hα1) s δ z hk
  rw [deriv_rpow hk] at hd
  refine hd.congr_deriv ?_
  have hpow : kbar ^ (α - 1) = kbar ^ α / kbar := by
    rw [Real.rpow_sub hk, Real.rpow_one]
  rw [hpow]
  have : s * (α * (kbar ^ α / kbar)) = α * (z + δ) := by
    field_simp
    have := hss
    nlinarith
  rw [this]
  congr 1
  ring

/-- The convergence factor `μ` lies strictly between 0 and 1 when `δ ≤ 1` (O&R p. 463). -/
theorem mu_mem_Ioo {α δ z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hδ : δ ≤ 1) (hzd : 0 < z + δ)
    (hz : 0 < 1 + z) : 0 < (1 + α * z + (α - 1) * δ) / (1 + z) ∧
      (1 + α * z + (α - 1) * δ) / (1 + z) < 1 := by
  constructor
  · apply div_pos _ hz; nlinarith
  · rw [div_lt_one hz]; nlinarith

/-- **A higher capital share slows convergence** (O&R p. 463): `μ` is affine in `α` with
slope `(z + δ)/(1 + z) > 0`. -/
theorem mu_strictMono_alpha {α α' δ z : ℝ} (hzd : 0 < z + δ) (hz : 0 < 1 + z) (h : α < α') :
    (1 + α * z + (α - 1) * δ) / (1 + z) < (1 + α' * z + (α' - 1) * δ) / (1 + z) :=
  div_lt_div_of_pos_right (by nlinarith) hz

/-- The exact slope: `dμ/dα = (z + δ)/(1 + z)`. -/
theorem mu_deriv_alpha {δ z : ℝ} (α : ℝ) :
    HasDerivAt (fun α => (1 + α * z + (α - 1) * δ) / (1 + z)) ((z + δ) / (1 + z)) α := by
  have h := ((((hasDerivAt_id α).mul_const z).const_add 1).add
    (((hasDerivAt_id α).sub_const 1).mul_const δ)).div_const (1 + z)
  simpa using h

/-- **The local convergence rate is exact in the limit** (O&R (44)): along every Solow
path from `k₀ ≠ k̄`, `(k_{t+1} - k̄)/(k_t - k̄) → G'(k̄) = [(1-δ) + s f'(k̄)]/(1+z)`. -/
theorem solow_ratio_tendsto (hf : Neoclassical f) {s δ z kbar : ℝ} (P : SolowParams s δ z)
    (hk : 0 < kbar) (hss : s * f kbar = (z + δ) * kbar) {k : ℕ → ℝ}
    (hrec : ∀ t, k (t + 1) = solowMap f s δ z (k t)) (h0 : 0 < k 0) (hne : k 0 ≠ kbar) :
    Tendsto (fun t => (k (t + 1) - kbar) / (k t - kbar)) atTop
      (𝓝 (((1 - δ) + s * deriv f kbar) / (1 + z))) := by
  have hG := solow_monotoneMap hf P hk hss
  have hne' : ∀ t, k t ≠ kbar := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact fun t => ne_of_lt ((hG.orbit_below hrec h0 hlt).2.1 t)
    · exact fun t => ne_of_gt ((hG.orbit_above hrec hgt).2.1 t)
  exact ratio_tendsto_deriv (solowMap_hasDerivAt hf s δ z hk) hG.fixed hrec hne'
    (hG.orbit_tendsto hrec h0).1

/-- **The book's number `μ ≈ 0.96`** (O&R p. 463): with `α = 1/3`, `g = 0.02`, `n = 0.01`,
`δ = 0.03`, `μ` lies in `(0.960, 0.962)`, so the gap closes at about 4 percent a year. -/
theorem mu_us_one_third :
    (0.960 : ℝ) < (1 + (1 / 3) * ((1.02 : ℝ) * 1.01 - 1) - (2 / 3) * 0.03) / (1.02 * 1.01) ∧
      (1 + (1 / 3) * ((1.02 : ℝ) * 1.01 - 1) - (2 / 3) * 0.03) / (1.02 * 1.01) < 0.962 := by
  constructor <;> norm_num

/-- **At `α = 2/3`, `μ ≈ 0.98`** (O&R p. 464): `μ ∈ (0.980, 0.981)`. -/
theorem mu_us_two_thirds :
    (0.980 : ℝ) < (1 + (2 / 3) * ((1.02 : ℝ) * 1.01 - 1) - (1 / 3) * 0.03) / (1.02 * 1.01) ∧
      (1 + (2 / 3) * ((1.02 : ℝ) * 1.01 - 1) - (1 / 3) * 0.03) / (1.02 * 1.01) < 0.981 := by
  constructor <;> norm_num

/-- Half-life bounds from `log` bracketing: for `0 < μ < 1`,
`(1 - μ) ≤ -log μ ≤ 1/μ - 1`. -/
theorem neg_log_bounds {μ : ℝ} (hμ : 0 < μ) : 1 - μ ≤ -Real.log μ ∧ -Real.log μ ≤ 1 / μ - 1 := by
  constructor
  · linarith [Real.log_le_sub_one_of_pos hμ]
  · have := Real.one_sub_inv_le_log_of_pos hμ
    rw [one_div]; linarith

/-- **The half-life "rises to 35 years"** (O&R p. 464): at `α = 2/3` (with the numbers of
p. 463) the half-life `log 2/(-log μ)` lies strictly between 34 and 36 years. -/
theorem half_life_two_thirds :
    34 < Real.log 2 / (-Real.log ((1 + (2 / 3) * ((1.02 : ℝ) * 1.01 - 1) - (1 / 3) * 0.03) /
      (1.02 * 1.01))) ∧
    Real.log 2 / (-Real.log ((1 + (2 / 3) * ((1.02 : ℝ) * 1.01 - 1) - (1 / 3) * 0.03) /
      (1.02 * 1.01))) < 36 := by
  generalize hμ : (1 + (2 / 3) * ((1.02 : ℝ) * 1.01 - 1) - (1 / 3) * 0.03) / (1.02 * 1.01) = μ
  have hμpos : 0 < μ := by rw [← hμ]; norm_num
  obtain ⟨hlo, hhi⟩ := neg_log_bounds hμpos
  have h1 : (0.0194 : ℝ) < 1 - μ := by rw [← hμ]; norm_num
  have h2 : 1 / μ - 1 < (0.0199 : ℝ) := by rw [← hμ]; norm_num
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hpos : 0 < -Real.log μ := by linarith
  constructor
  · rw [lt_div_iff₀ hpos]; nlinarith
  · rw [div_lt_iff₀ hpos]; nlinarith

/-- **"0.98^X = 0.5 gives X ≈ 34"** (O&R p. 463 region, the 2 percent benchmark): the
half-life at a 2 percent convergence rate lies strictly between 33 and 35 years. -/
theorem half_life_two_percent :
    33 < Real.log 2 / (-Real.log 0.98) ∧ Real.log 2 / (-Real.log 0.98) < 35 := by
  obtain ⟨hlo, hhi⟩ := neg_log_bounds (by norm_num : (0 : ℝ) < 0.98)
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have h1 : (1 : ℝ) - 0.98 = 0.02 := by norm_num
  have h2 : (1 : ℝ) / 0.98 - 1 < 0.0205 := by norm_num
  have hpos : 0 < -Real.log 0.98 := by linarith
  constructor
  · rw [lt_div_iff₀ hpos]; nlinarith
  · rw [div_lt_iff₀ hpos]; nlinarith

end ObstfeldRogoff.GlobalGrowth.SolowModel
