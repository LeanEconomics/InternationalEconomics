/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GlobalGrowth.SolowModel
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen

/-!
# The Ramsey–Cass–Koopmans model in discrete time

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §7.1.2.1
(pp. 440–445), with the open-economy remarks of §7.2.1.1 and §7.2.2.2 (pp. 459–464).

The book derives the Euler equation (20)/(22)/(24) and the steady state (25)–(26), and
asserts from the phase diagram (Fig. 7.4) that for every initial capital stock there is a
unique optimal consumption level placing the economy on the saddle path converging to
the steady state. Here all of this is proved with a genuine infinite horizon.

* **The generic model** (efficiency units): capital `k`, gross resources
  `F(k) = f(k) + (1 - δ) k`, feasibility `0 ≤ k_{t+1} ≤ F(k_t)`, welfare `∑ βᵗ u(c_t)`.
  Existence of an optimal path (compactness of the feasible set in the product topology),
  uniqueness (strict concavity), the Bellman equation, interiority (Inada conditions),
  the Euler equation, a strictly increasing policy, and **monotone convergence** of every
  optimal path to the unique steady state `β(f'(k*) + 1 - δ) = 1`, with consumption moving
  monotonically in the same direction. This part is adapted from the LeanEconomics
  `EconomicGrowth` repository (discrete-time Ramsey–Cass–Koopmans), copied and re-proved
  here so that this project stands alone.
* **Euler equation plus transversality are necessary and sufficient**: any feasible
  interior path satisfying the Euler equation and `lim βᵗ u'(c_t) k_{t+1} = 0` is optimal
  (supporting-hyperplane argument on partial sums, no summability of rivals needed), and
  the optimal path satisfies both (the transversality condition is *derived* from its
  convergence).
* **The book's model**: the per-capita problem (18)–(19) with population growth `n` and
  labour-augmenting progress `g` is detrended exactly into the generic model
  (`β̂ = β(1+n)(1+g)^{1-1/σ}`, condition (23) is exactly `β̂ < 1`), giving (22), (24)–(26),
  (28), fn 7, fn 8, dynamic efficiency (p. 442), and the experiments of Figs. 7.5–7.6.
* **Utility unbounded below** (log and CRRA with `σ ≤ 1`): existence, uniqueness,
  Euler equation and monotone convergence are proved separately (`LogUtility` namespace).
* **No growth and no depreciation** (`z + δ = 0`, O&R p. 441 with `n = g = 0`): feasible
  capital is then unbounded, but geometrically growing bounds keep the compactness argument
  alive and optimal paths are bounded by `max(k₀, k*)`, so all results hold (`book_no_growth`).
* The small open economy (capital jumps to `f'(k) = r + δ`) and the integrated world
  economy (capital is allocated to equalise marginal products, so the world behaves like
  one closed economy).
-/

namespace ObstfeldRogoff.GlobalGrowth.RamseyCassKoopmans

open Set Filter Topology

/-! ## Concavity and steady-state helpers -/

/-- A differentiable concave function lies below its tangent (the supporting-hyperplane
inequality used throughout O&R §7.1.2): `f(y) - f(x) ≤ f'(x)(y - x)`. -/
theorem concave_support {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}
    (hconc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hderiv : HasDerivAt f f' x) :
    f y - f x ≤ f' * (y - x) := by
  rcases lt_trichotomy y x with hlt | heq | hgt
  · have hs := hconc.le_slope_of_hasDerivAt hy hx hlt hderiv
    rw [slope_def_field] at hs
    have hmul := (le_div_iff₀ (sub_pos.mpr hlt)).mp hs
    nlinarith
  · subst y
    simp
  · have hs := hconc.slope_le_of_hasDerivAt hx hy hgt hderiv
    rw [slope_def_field] at hs
    exact (div_le_iff₀ (sub_pos.mpr hgt)).mp hs

/-- A concave technology whose marginal product vanishes at infinity eventually produces
less than `m k` for any `m > 0` (the maximal sustainable capital stock of O&R Fig. 7.4). -/
theorem exists_capacity_of_marginal_tendsto_zero (f : ℝ → ℝ) {m k0 : ℝ}
    (hm : 0 < m) (hf : ConcaveOn ℝ (Ici 0) f)
    (hd : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hpos : ∀ k, 0 < k → 0 ≤ deriv f k)
    (hlim : Tendsto (deriv f) atTop (𝓝 (0 : ℝ))) :
    ∃ K, k0 ≤ K ∧ ∀ k, K ≤ k → f k ≤ m * k := by
  obtain ⟨a, ha, hma⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hlim.eventually (gt_mem_nhds (half_pos hm)))).exists
  let K := max k0 (max a (2 * |f a| / m))
  refine ⟨K, le_max_left _ _, ?_⟩
  intro k hk
  have hak : a ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hratio : 2 * |f a| / m ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hmk : 2 * |f a| ≤ k * m := (div_le_iff₀ hm).mp hratio
  have hs := concave_support hf ha.le (ha.le.trans hak) (hd a ha).hasDerivAt
  have hpk := mul_le_mul_of_nonneg_right hma.le (ha.le.trans hak)
  have hpa := mul_nonneg (hpos a ha) ha.le
  have hfabs := le_abs_self (f a)
  nlinarith

/-- A continuous, strictly decreasing marginal product with the two Inada limits crosses
every positive target exactly once (the steady state (25), O&R p. 442). -/
theorem existsUnique_positive_root_of_inada
    (mp : ℝ → ℝ) (target : ℝ) (htarget : 0 < target)
    (hcont : ContinuousOn mp (Ioi 0))
    (hanti : StrictAntiOn mp (Ioi 0))
    (hatZero : Tendsto mp (𝓝[>] (0 : ℝ)) atTop)
    (hatTop : Tendsto mp atTop (𝓝 (0 : ℝ))) :
    ∃! k : ℝ, 0 < k ∧ mp k = target := by
  have haevent : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), 0 < a := self_mem_nhdsWithin
  obtain ⟨a, ha, hma⟩ := (haevent.and (hatZero.eventually_gt_atTop target)).exists
  obtain ⟨b, hab, hmb⟩ := ((eventually_gt_atTop a).and
    (hatTop.eventually (gt_mem_nhds htarget))).exists
  obtain ⟨k, hk, heq⟩ := intermediate_value_Icc' hab.le
    (hcont.mono (fun _ hk => lt_of_lt_of_le ha hk.1)) ⟨hmb.le, hma.le⟩
  have hkpos : 0 < k := lt_of_lt_of_le ha hk.1
  refine ⟨k, ⟨hkpos, heq⟩, ?_⟩
  intro y hy
  exact hanti.injOn hy.1 hkpos (hy.2.trans heq.symm)

/-- For a strictly concave technology the marginal product is strictly decreasing on
positive capital (O&R fn 7). -/
theorem production_deriv_strictAnti
    (f : ℝ → ℝ)
    (hconc : StrictConcaveOn ℝ (Ici 0) f)
    (hdiff : ∀ k : ℝ, 0 < k → DifferentiableAt ℝ f k) :
    StrictAntiOn (deriv f) (Ioi 0) :=
  (hconc.subset Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv hdiff

/-- Strict concavity with `f 0 = 0` gives `f'(k) k < f(k)` (positive steady-state
consumption (26), O&R p. 442). -/
theorem marginal_product_times_capital_lt_output
    (f : ℝ → ℝ) (k : ℝ)
    (hconc : StrictConcaveOn ℝ (Ici 0) f)
    (hzero : f 0 = 0) (hk : 0 < k)
    (hdiff : DifferentiableAt ℝ f k) :
    deriv f k * k < f k := by
  have h := hconc.deriv_lt_slope (show (0 : ℝ) ∈ Ici 0 by simp)
    (le_of_lt hk) hk hdiff
  rw [slope_def_field, hzero, sub_zero, sub_zero] at h
  exact (lt_div_iff₀ hk).mp h

/-! ## The generic discrete-time model -/

variable {f u : ℝ → ℝ} {β δ : ℝ}


/-!
# The discrete-time Ramsey–Cass–Koopmans model: feasibility and existence

Capital per worker obeys `k(t+1) = F(k(t)) - c(t)` with gross resources
`F(k) = f(k) + (1 - δ) k`, and a path is feasible when `0 ≤ k(t+1) ≤ F(k(t))`.
Welfare is `∑ βᵗ u(c(t))` with `0 < β < 1`.

Utility is continuous at zero consumption (`u` is continuous on `[0, ∞)`), so
welfare is a convergent series on the compact set of feasible paths; logarithmic
utility is treated separately. Depreciation may be zero (`0 ≤ δ`): capital along a feasible
path is then unbounded, but it grows at most geometrically at any rate `1 + m` with
`β(1 + m) < 1` (`Primitives.linear_growth`, from `f' → 0`), so feasible paths lie in a
product of compact intervals (`Feasible.le_bound`), the feasible set is compact in the product
topology, welfare is continuous on it, and an optimal path exists (`exists_optimal`).
-/


/-- O&R §7.1.2.1 (generic discrete-time model): Primitive assumptions of the discrete-time model. -/
structure Primitives (f u : ℝ → ℝ) (β δ : ℝ) : Prop where
  β_pos : 0 < β
  β_lt_one : β < 1
  δ_nonneg : 0 ≤ δ
  δ_le_one : δ ≤ 1
  f_cont : ContinuousOn f (Ici 0)
  f_zero : f 0 = 0
  f_conc : StrictConcaveOn ℝ (Ici 0) f
  f_diff : ∀ k, 0 < k → DifferentiableAt ℝ f k
  f_prime_pos : ∀ k, 0 < k → 0 < deriv f k
  f_prime_cont : ContinuousOn (deriv f) (Ioi 0)
  f_inada0 : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop
  f_inadaTop : Tendsto (deriv f) atTop (𝓝 (0 : ℝ))
  u_cont : ContinuousOn u (Ici 0)
  u_conc : StrictConcaveOn ℝ (Ici 0) u
  u_diff : ∀ c, 0 < c → DifferentiableAt ℝ u c
  u_prime_pos : ∀ c, 0 < c → 0 < deriv u c
  u_prime_cont : ContinuousOn (deriv u) (Ioi 0)
  u_inada0 : Tendsto (deriv u) (𝓝[>] (0 : ℝ)) atTop

/-- O&R §7.1.2.1 (generic discrete-time model): Gross resources: output plus undepreciated capital.
-/
def resources (f : ℝ → ℝ) (δ k : ℝ) : ℝ := f k + (1 - δ) * k

/-- O&R §7.1.2.1 (generic discrete-time model): A feasible capital path from `k₀`. -/
def Feasible (f : ℝ → ℝ) (δ k₀ : ℝ) (k : ℕ → ℝ) : Prop :=
  k 0 = k₀ ∧ ∀ t, 0 ≤ k (t + 1) ∧ k (t + 1) ≤ resources f δ (k t)

/-- O&R §7.1.2.1 (generic discrete-time model): Consumption along a capital path. -/
def consumption (f : ℝ → ℝ) (δ : ℝ) (k : ℕ → ℝ) (t : ℕ) : ℝ :=
  resources f δ (k t) - k (t + 1)

/-- O&R §7.1.2.1 (generic discrete-time model): Discounted lifetime welfare. -/
noncomputable def welfare (f u : ℝ → ℝ) (β δ : ℝ) (k : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * u (consumption f δ k t)

/-- O&R §7.1.2.1 (generic discrete-time model): Output is strictly increasing in capital. -/
theorem Primitives.f_strictMono (P : Primitives f u β δ) : StrictMonoOn f (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici 0) P.f_cont
    (fun k hk => by rw [interior_Ici] at hk; exact P.f_prime_pos k hk)

/-- O&R §7.1.2.1 (generic discrete-time model): Utility is strictly increasing in consumption. -/
theorem Primitives.u_strictMono (P : Primitives f u β δ) : StrictMonoOn u (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici 0) P.u_cont
    (fun c hc => by rw [interior_Ici] at hc; exact P.u_prime_pos c hc)

/-- O&R §7.1.2.1 (generic discrete-time model): Gross resources `f(k) + (1 - δ) k` are strictly
increasing (uses `δ ≤ 1`). -/
theorem Primitives.resources_strictMono (P : Primitives f u β δ) :
    StrictMonoOn (resources f δ) (Ici 0) := by
  intro a ha b hb hab
  have h1 := P.f_strictMono ha hb hab
  have h2 := mul_le_mul_of_nonneg_left hab.le (sub_nonneg.mpr P.δ_le_one)
  simp only [resources]
  linarith

/-- O&R §7.1.2.1 (generic discrete-time model): Gross resources are continuous on `[0, ∞)`. -/
theorem Primitives.resources_cont (P : Primitives f u β δ) :
    ContinuousOn (resources f δ) (Ici 0) :=
  P.f_cont.add (continuousOn_const.mul continuousOn_id)

/-- O&R §7.1.2.1 (generic discrete-time model): No resources without capital. -/
theorem resources_zero (P : Primitives f u β δ) : resources f δ 0 = 0 := by
  simp [resources, P.f_zero]

/-- O&R §7.1.2.1 (generic discrete-time model): Gross resources are nonnegative at nonnegative
capital. -/
theorem Primitives.resources_nonneg (P : Primitives f u β δ) {k : ℝ} (hk : 0 ≤ k) :
    0 ≤ resources f δ k := by
  rw [← resources_zero P]
  exact P.resources_strictMono.monotoneOn (mem_Ici.mpr le_rfl) hk hk

/-- O&R §7.1.2.1 (generic discrete-time model): **resources grow at most linearly** with any
slope above one: there are `m > 0` with `β(1 + m) < 1` and `C ≥ 0` such that
`F(k) ≤ (1 + m) k + C` for all `k ≥ 0` (from `f' → 0`; no depreciation is needed). -/
theorem Primitives.linear_growth (P : Primitives f u β δ) :
    ∃ m C : ℝ, 0 < m ∧ β * (1 + m) < 1 ∧ 0 ≤ C ∧
      ∀ k, 0 ≤ k → resources f δ k ≤ (1 + m) * k + C := by
  set m := (1 / β - 1) / 2
  have hβ := P.β_pos
  have hm : 0 < m := by
    have : 1 < 1 / β := by rw [lt_div_iff₀ hβ]; linarith [P.β_lt_one]
    simp only [m]; linarith
  have hβm : β * (1 + m) < 1 := by
    simp only [m]; field_simp; linarith [P.β_lt_one]
  obtain ⟨K, hK1, hK⟩ := exists_capacity_of_marginal_tendsto_zero f (k0 := 1) hm
    P.f_conc.concaveOn P.f_diff (fun k hk => (P.f_prime_pos k hk).le) P.f_inadaTop
  have hK0 : 0 ≤ K := le_trans zero_le_one hK1
  have hfmono : MonotoneOn f (Ici 0) :=
    (strictMonoOn_of_deriv_pos (convex_Ici 0) P.f_cont
      (fun k hk => by rw [interior_Ici] at hk; exact P.f_prime_pos k hk)).monotoneOn
  have hfK : 0 ≤ f K := by
    rw [← P.f_zero]; exact hfmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hK0) hK0
  refine ⟨m, f K, hm, hβm, hfK, fun k hk => ?_⟩
  have hfk : f k ≤ m * k + f K := by
    rcases le_total k K with h | h
    · have := hfmono (mem_Ici.mpr hk) (mem_Ici.mpr hK0) h
      nlinarith
    · have := hK k h
      linarith
  have : (1 - δ) * k ≤ k := by nlinarith [P.δ_nonneg]
  simp only [resources]
  linarith

/-- O&R §7.1.2.1 (generic discrete-time model): the growth slope `m` of
`Primitives.linear_growth` (chosen). -/
noncomputable def growthSlope (P : Primitives f u β δ) : ℝ :=
  Classical.choose P.linear_growth

/-- O&R §7.1.2.1 (generic discrete-time model): the intercept `C` of
`Primitives.linear_growth` (chosen). -/
noncomputable def growthConst (P : Primitives f u β δ) : ℝ :=
  Classical.choose (Classical.choose_spec P.linear_growth)

/-- O&R §7.1.2.1 (generic discrete-time model): properties of the chosen slope and intercept. -/
theorem growth_spec (P : Primitives f u β δ) :
    0 < growthSlope P ∧ β * (1 + growthSlope P) < 1 ∧ 0 ≤ growthConst P ∧
      ∀ k, 0 ≤ k → resources f δ k ≤ (1 + growthSlope P) * k + growthConst P :=
  Classical.choose_spec (Classical.choose_spec P.linear_growth)

/-- O&R §7.1.2.1 (generic discrete-time model): the date-`t` capital bound for paths from `k₀`,
`B_t = (1+m)^t (k̂₀ + C/m) - C/m` with `k̂₀ = max k₀ 0`, solving `B_{t+1} = (1+m) B_t + C`. -/
noncomputable def bound (P : Primitives f u β δ) (k₀ : ℝ) (t : ℕ) : ℝ :=
  (1 + growthSlope P) ^ t * (max k₀ 0 + growthConst P / growthSlope P) -
    growthConst P / growthSlope P

/-- O&R §7.1.2.1 (generic discrete-time model): the bound starts above `k₀`, is nonnegative,
nondecreasing, and resources at any stock below `B_t` are below `B_{t+1}`. -/
theorem bound_spec (P : Primitives f u β δ) (k₀ : ℝ) :
    k₀ ≤ bound P k₀ 0 ∧ (∀ t, max k₀ 0 ≤ bound P k₀ t) ∧
      (∀ t, bound P k₀ t ≤ bound P k₀ (t + 1)) ∧
      ∀ t k, 0 ≤ k → k ≤ bound P k₀ t → resources f δ k ≤ bound P k₀ (t + 1) := by
  obtain ⟨hm, -, hC, hgr⟩ := growth_spec P
  unfold bound
  generalize growthSlope P = m at *
  generalize growthConst P = C at *
  have hq : 0 ≤ max k₀ 0 + C / m := by have := le_max_right k₀ 0; positivity
  have hrec : ∀ t : ℕ, (1 + m) ^ (t + 1) * (max k₀ 0 + C / m) - C / m =
      (1 + m) * ((1 + m) ^ t * (max k₀ 0 + C / m) - C / m) + C := by
    intro t; rw [pow_succ]; field_simp; ring
  have hge : ∀ t : ℕ, max k₀ 0 ≤ (1 + m) ^ t * (max k₀ 0 + C / m) - C / m := by
    intro t
    have h1 : 1 ≤ (1 + m) ^ t := one_le_pow₀ (by linarith)
    nlinarith
  refine ⟨?_, hge, fun t => ?_, fun t k hk hkt => ?_⟩
  · simp only [pow_zero, one_mul]; linarith [le_max_left k₀ 0]
  · rw [hrec]; nlinarith [hge t, le_max_right k₀ 0]
  · rw [hrec]
    have := hgr k hk
    nlinarith

/-- O&R §7.1.2.1 (generic discrete-time model): the bounds are discount-summable:
`∑ βᵗ B_{t+1} < ∞`. -/
theorem bound_summable (P : Primitives f u β δ) (k₀ : ℝ) :
    Summable (fun t => β ^ t * bound P k₀ (t + 1)) := by
  have hnn : ∀ t, 0 ≤ bound P k₀ t := fun t => (le_max_right k₀ 0).trans ((bound_spec P k₀).2.1 t)
  obtain ⟨hm, hβm, hC, -⟩ := growth_spec P
  have hβ := P.β_pos
  unfold bound at hnn ⊢
  generalize growthSlope P = m at *
  generalize growthConst P = C at *
  have hq : 0 ≤ max k₀ 0 + C / m := by have := le_max_right k₀ 0; positivity
  have hβm0 : 0 ≤ β * (1 + m) := by positivity
  have hgeo := summable_geometric_of_lt_one hβm0 hβm
  have hmaj : Summable (fun t : ℕ => (β * (1 + m)) ^ t * ((1 + m) * (max k₀ 0 + C / m))) :=
    hgeo.mul_right _
  refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hβ.le t) (hnn (t + 1)))
    (fun t => ?_) hmaj
  have hb : (1 + m) ^ (t + 1) * (max k₀ 0 + C / m) - C / m ≤
      (1 + m) ^ (t + 1) * (max k₀ 0 + C / m) := by have := div_nonneg hC hm.le; linarith
  calc β ^ t * ((1 + m) ^ (t + 1) * (max k₀ 0 + C / m) - C / m)
      ≤ β ^ t * ((1 + m) ^ (t + 1) * (max k₀ 0 + C / m)) :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg hβ.le t)
    _ = (β * (1 + m)) ^ t * ((1 + m) * (max k₀ 0 + C / m)) := by rw [mul_pow, pow_succ]; ring

/-- O&R §7.1.2.1 (generic discrete-time model): Capital along a feasible path is nonnegative. -/
theorem Feasible.nonneg {k₀ : ℝ} {k : ℕ → ℝ} (hk : Feasible f δ k₀ k) (hk₀ : 0 ≤ k₀) (t : ℕ) :
    0 ≤ k t := by
  cases t with
  | zero => rw [hk.1]; exact hk₀
  | succ t => exact (hk.2 t).1

/-- O&R §7.1.2.1 (generic discrete-time model): Every feasible path stays below the bounds. -/
theorem Feasible.le_bound (P : Primitives f u β δ) {k₀ : ℝ} {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk₀ : 0 ≤ k₀) (t : ℕ) : k t ≤ bound P k₀ t := by
  obtain ⟨h1, -, -, h4⟩ := bound_spec P k₀
  induction t with
  | zero => rw [hk.1]; exact h1
  | succ t ih => exact (hk.2 t).2.trans (h4 t _ (hk.nonneg hk₀ t) ih)

/-- O&R §7.1.2.1 (generic discrete-time model): Consumption along a feasible path lies in
`[0, B_{t+1}]`. -/
theorem Feasible.consumption_mem (P : Primitives f u β δ) {k₀ : ℝ} {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk₀ : 0 ≤ k₀) (t : ℕ) :
    consumption f δ k t ∈ Icc 0 (bound P k₀ (t + 1)) := by
  refine ⟨sub_nonneg.mpr (hk.2 t).2, ?_⟩
  have := (bound_spec P k₀).2.2.2 t _ (hk.nonneg hk₀ t) (hk.le_bound P hk₀ t)
  have := (hk.2 t).1
  simp only [consumption]
  linarith

/-- O&R §7.1.2.1 (generic discrete-time model): a linear bound on utility over `[0, B]`:
`|u(c)| ≤ |u 0| + |u 1| + u'(1) B` (monotonicity and the tangent line at `1`). -/
theorem utility_linear_bound (P : Primitives f u β δ) {c B : ℝ} (hc : 0 ≤ c) (hcB : c ≤ B) :
    |u c| ≤ |u 0| + |u 1| + deriv u 1 * B := by
  have hlow := P.u_strictMono.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hc) hc
  have hup := concave_support P.u_conc.concaveOn (mem_Ici.mpr zero_le_one) (mem_Ici.mpr hc)
    (P.u_diff 1 one_pos).hasDerivAt
  have hd := P.u_prime_pos 1 one_pos
  have h1 : deriv u 1 * (c - 1) ≤ deriv u 1 * B := by nlinarith
  have h2 : 0 ≤ deriv u 1 * B := mul_nonneg hd.le (hc.trans hcB)
  have h3 := neg_abs_le (u 0)
  have h4 := le_abs_self (u 1)
  have h5 := abs_nonneg (u 0)
  have h6 := abs_nonneg (u 1)
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- O&R §7.1.2.1 (generic discrete-time model): the summable utility majorant along paths from
`k₀`: `βᵗ (|u 0| + |u 1| + u'(1) B_{t+1})`. -/
theorem utility_majorant_summable (P : Primitives f u β δ) (k₀ : ℝ) :
    Summable (fun t => β ^ t * (|u 0| + |u 1| + deriv u 1 * bound P k₀ (t + 1))) := by
  have hgeo := summable_geometric_of_lt_one P.β_pos.le P.β_lt_one
  refine ((hgeo.mul_right (|u 0| + |u 1|)).add ((bound_summable P k₀).mul_left (deriv u 1))).congr
    (fun t => ?_)
  ring

/-- O&R §7.1.2.1 (generic discrete-time model): Discounted utility along any feasible path is
summable (a genuine infinite horizon: welfare is a convergent series). -/
theorem Feasible.summable (P : Primitives f u β δ) {k₀ : ℝ} {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk₀ : 0 ≤ k₀) :
    Summable (fun t => β ^ t * u (consumption f δ k t)) := by
  refine Summable.of_norm_bounded (utility_majorant_summable P k₀) (fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos P.β_pos t)]
  exact mul_le_mul_of_nonneg_left (utility_linear_bound P (hk.consumption_mem P hk₀ t).1
    (hk.consumption_mem P hk₀ t).2) (pow_pos P.β_pos t).le

/-- O&R §7.1.2.1 (generic discrete-time model): The path that consumes everything after the first
period is feasible. -/
theorem feasible_consume_all (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    Feasible f δ k₀ (fun t => if t = 0 then k₀ else 0) := by
  refine ⟨rfl, fun t => ⟨le_rfl, ?_⟩⟩
  cases t with
  | zero => exact P.resources_nonneg hk₀
  | succ t => simp [resources_zero P]

/-- O&R §7.1.2.1 (generic discrete-time model): The feasible set from `k₀` as a subset of the
sequence space. -/
def feasibleSet (f : ℝ → ℝ) (δ k₀ : ℝ) : Set (ℕ → ℝ) := {k | Feasible f δ k₀ k}

/-- O&R §7.1.2.1 (generic discrete-time model): The feasible set is compact in the product topology
(Tychonoff). -/
theorem isCompact_feasibleSet (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    IsCompact (feasibleSet f δ k₀) := by
  -- the continuous extension of `f` to the whole line
  set fe : ℝ → ℝ := fun x => f (max x 0)
  have hfe : Continuous fe := P.f_cont.comp_continuous (continuous_id.max continuous_const)
    (fun x => le_max_right x 0)
  have heq : feasibleSet f δ k₀ = {k | k 0 = k₀} ∩ ⋂ t, ({k : ℕ → ℝ | 0 ≤ k (t + 1)} ∩
      {k | k (t + 1) ≤ fe (k t) + (1 - δ) * k t}) := by
    ext k
    simp only [feasibleSet, Feasible, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨h0, h⟩
      refine ⟨h0, fun t => ⟨(h t).1, ?_⟩⟩
      have hnn : 0 ≤ k t := Feasible.nonneg ⟨h0, h⟩ hk₀ t
      simp only [fe, max_eq_left hnn]
      exact (h t).2
    · rintro ⟨h0, h⟩
      have hnn : ∀ t, 0 ≤ k t := by
        intro t
        cases t with
        | zero => rw [h0]; exact hk₀
        | succ t => exact (h t).1
      refine ⟨h0, fun t => ⟨(h t).1, ?_⟩⟩
      have := (h t).2
      simp only [fe, max_eq_left (hnn t)] at this
      exact this
  have hclosed : IsClosed (feasibleSet f δ k₀) := by
    rw [heq]
    refine (isClosed_eq (continuous_apply 0) continuous_const).inter (isClosed_iInter fun t => ?_)
    exact (isClosed_le continuous_const (continuous_apply (t + 1))).inter
      (isClosed_le (continuous_apply (t + 1)) ((hfe.comp (continuous_apply t)).add
        (continuous_const.mul (continuous_apply t))))
  have hbox : feasibleSet f δ k₀ ⊆ Set.pi univ (fun t => Icc 0 (bound P k₀ t)) := by
    intro k hk _ _
    exact ⟨Feasible.nonneg hk hk₀ _, Feasible.le_bound P hk hk₀ _⟩
  exact (isCompact_univ_pi (fun _ => isCompact_Icc)).of_isClosed_subset hclosed hbox

/-- O&R §7.1.2.1 (generic discrete-time model): Welfare is continuous on the feasible set (uniform
convergence of the series). -/
theorem continuousOn_welfare (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    ContinuousOn (welfare f u β δ) (feasibleSet f δ k₀) := by
  apply continuousOn_tsum
    (u := fun t => β ^ t * (|u 0| + |u 1| + deriv u 1 * bound P k₀ (t + 1)))
  · intro t
    apply continuousOn_const.mul
    apply P.u_cont.comp
    · apply ContinuousOn.sub _ (continuous_apply (t + 1)).continuousOn
      exact (P.resources_cont.comp (continuous_apply t).continuousOn
        (fun k hk => Feasible.nonneg hk hk₀ t))
    · exact fun k hk => (Feasible.consumption_mem P hk hk₀ t).1
  · exact utility_majorant_summable P k₀
  · intro t k hk
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos P.β_pos t)]
    exact mul_le_mul_of_nonneg_left (utility_linear_bound P
      (Feasible.consumption_mem P hk hk₀ t).1 (Feasible.consumption_mem P hk hk₀ t).2)
      (pow_pos P.β_pos t).le

/-- O&R §7.1.2.1 (generic discrete-time model): An optimal path exists from every nonnegative stock.
-/
theorem exists_optimal (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    ∃ k, Feasible f δ k₀ k ∧
      ∀ k', Feasible f δ k₀ k' → welfare f u β δ k' ≤ welfare f u β δ k := by
  obtain ⟨k, hk, hmax⟩ := (isCompact_feasibleSet P hk₀).exists_isMaxOn
    ⟨fun t => if t = 0 then k₀ else 0, (feasible_consume_all P hk₀ : _)⟩
    (continuousOn_welfare P hk₀)
  exact ⟨k, hk, fun k' hk' => hmax hk'⟩

/-- O&R §7.1.2.1 (generic discrete-time model): The optimal path from `k₀ ≥ 0` (chosen). -/
noncomputable def optimalPath (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) : ℕ → ℝ :=
  Classical.choose (exists_optimal P hk₀)

/-- O&R §7.1.2.1 (generic discrete-time model): The chosen optimal path is feasible and optimal. -/
theorem optimalPath_spec (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    Feasible f δ k₀ (optimalPath P hk₀) ∧ ∀ k', Feasible f δ k₀ k' →
      welfare f u β δ k' ≤ welfare f u β δ (optimalPath P hk₀) :=
  Classical.choose_spec (exists_optimal P hk₀)

/-- O&R §7.1.2.1 (generic discrete-time model): The value function. -/
noncomputable def value (P : Primitives f u β δ) (k₀ : ℝ) : ℝ :=
  if hk₀ : 0 ≤ k₀ then welfare f u β δ (optimalPath P hk₀) else 0

/-- O&R §7.1.2.1 (generic discrete-time model): The value function is the welfare of the optimal
path. -/
theorem value_eq (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    value P k₀ = welfare f u β δ (optimalPath P hk₀) := by
  simp only [value, hk₀, ↓reduceDIte]

/-- O&R §7.1.2.1 (generic discrete-time model): Every feasible path yields at most the value. -/
theorem welfare_le_value (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) : welfare f u β δ k ≤ value P k₀ := by
  rw [value_eq P hk₀]
  exact (optimalPath_spec P hk₀).2 k hk


/-!
# The principle of optimality, uniqueness, and the shape of the value function

* `welfare_eq_head_add`: `W(k) = u(c₀) + β W(tailPath k)`.
* `tail_optimal`, `bellman`: the tail of an optimal path is optimal from the stock
  it reaches, and `V(k₀) = max_{0 ≤ y ≤ F(k₀)} u(F(k₀) - y) + β V(y)`.
* `optimal_unique`: the optimal path is unique (strict concavity of `u`).
* `value_strictMono`, `value_strictConcave`: `V` is strictly increasing and strictly
  concave.
-/



/-- O&R §7.1.2.1 (generic discrete-time model): The path from date one on. -/
def tailPath (k : ℕ → ℝ) : ℕ → ℝ := fun t => k (t + 1)

/-- O&R §7.1.2.1 (generic discrete-time model): Prepend a stock to a path. -/
def prependPath (k₀ : ℝ) (k : ℕ → ℝ) : ℕ → ℝ := fun t => if t = 0 then k₀ else k (t - 1)

/-- O&R §7.1.2.1 (generic discrete-time model): The tail of a feasible path is feasible from the
stock it reaches. -/
theorem Feasible.tail {k₀ : ℝ} {k : ℕ → ℝ} (hk : Feasible f δ k₀ k) :
    Feasible f δ (k 1) (tailPath k) :=
  ⟨rfl, fun t => hk.2 (t + 1)⟩

/-- O&R §7.1.2.1 (generic discrete-time model): Prepending a feasible first step to a feasible path
gives a feasible path. -/
theorem Feasible.prepend {k₀ y : ℝ} {k : ℕ → ℝ} (hk : Feasible f δ y k) (hy0 : 0 ≤ y)
    (hy : y ≤ resources f δ k₀) : Feasible f δ k₀ (prependPath k₀ k) := by
  refine ⟨rfl, fun t => ?_⟩
  rcases t with _ | t
  · have h1 : prependPath k₀ k (0 + 1) = y := by simp [prependPath, hk.1]
    have h0 : prependPath k₀ k 0 = k₀ := by simp [prependPath]
    rw [h1, h0]
    exact ⟨hy0, hy⟩
  · have h1 : prependPath k₀ k (t + 1 + 1) = k (t + 1) := by
      simp [prependPath]
    have h0 : prependPath k₀ k (t + 1) = k t := by simp [prependPath]
    rw [h1, h0]
    exact hk.2 t

/-- O&R §7.1.2.1 (generic discrete-time model): Consumption along the tail is shifted consumption.
-/
theorem consumption_tail (k : ℕ → ℝ) (t : ℕ) :
    consumption f δ (tailPath k) t = consumption f δ k (t + 1) := rfl

/-- O&R §7.1.2.1 (generic discrete-time model): Welfare splits as `W(k) = u(c₀) + β W(tail k)`. -/
theorem welfare_eq_head_add (P : Primitives f u β δ) {k₀ : ℝ} {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk₀ : 0 ≤ k₀) :
    welfare f u β δ k = u (consumption f δ k 0) + β * welfare f u β δ (tailPath k) := by
  unfold welfare
  rw [(hk.summable P hk₀).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, pow_succ, consumption_tail]
  congr 1
  congr 1
  funext t
  ring

/-- O&R §7.1.2.1 (generic discrete-time model): First-period consumption of a prepended path. -/
theorem consumption_prepend_zero (k₀ : ℝ) (k : ℕ → ℝ) :
    consumption f δ (prependPath k₀ k) 0 = resources f δ k₀ - k 0 := by
  simp [consumption, prependPath]

/-- O&R §7.1.2.1 (generic discrete-time model): The tail of a prepended path is the original path.
-/
theorem tail_prepend (k₀ : ℝ) (k : ℕ → ℝ) : tailPath (prependPath k₀ k) = k := by
  funext t
  simp [tailPath, prependPath]

/-- O&R §7.1.2.1 (generic discrete-time model): Welfare of a prepended path. -/
theorem welfare_prepend (P : Primitives f u β δ) {k₀ y : ℝ} {k : ℕ → ℝ}
    (hk : Feasible f δ y k) (hy0 : 0 ≤ y) (hy : y ≤ resources f δ k₀) (hk₀ : 0 ≤ k₀) :
    welfare f u β δ (prependPath k₀ k) = u (resources f δ k₀ - y) + β * welfare f u β δ k := by
  rw [welfare_eq_head_add P (hk.prepend hy0 hy) hk₀, consumption_prepend_zero, tail_prepend, hk.1]

/-- O&R §7.1.2.1 (generic discrete-time model): The tail of an optimal path is optimal. -/
theorem tail_optimal (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k)
    (hopt : ∀ k', Feasible f δ k₀ k' → welfare f u β δ k' ≤ welfare f u β δ k) :
    welfare f u β δ (tailPath k) = value P (k 1) := by
  have hk1 : 0 ≤ k 1 := (hk.2 0).1
  apply le_antisymm (welfare_le_value P hk1 hk.tail)
  by_contra hlt
  push Not at hlt
  obtain ⟨hopt1, _⟩ := optimalPath_spec P hk1
  have hbetter := hopt _ (hopt1.prepend hk1 (by rw [← hk.1]; exact (hk.2 0).2))
  rw [welfare_prepend P hopt1 hk1 (by rw [← hk.1]; exact (hk.2 0).2) hk₀,
    welfare_eq_head_add P hk hk₀, ← value_eq P hk1] at hbetter
  have hc0 : consumption f δ k 0 = resources f δ k₀ - k 1 := by
    simp [consumption, hk.1]
  rw [hc0] at hbetter
  have := mul_lt_mul_of_pos_left hlt P.β_pos
  linarith

/-- O&R §7.1.2.1 (generic discrete-time model): The Bellman equation along the optimal path, and the
Bellman inequality for every feasible choice of next period's capital. -/
theorem bellman (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    value P k₀ = u (resources f δ k₀ - optimalPath P hk₀ 1) +
        β * value P (optimalPath P hk₀ 1) ∧
      ∀ y, 0 ≤ y → y ≤ resources f δ k₀ →
        u (resources f δ k₀ - y) + β * value P y ≤ value P k₀ := by
  obtain ⟨hk, hopt⟩ := optimalPath_spec P hk₀
  refine ⟨?_, fun y hy0 hy => ?_⟩
  · rw [value_eq P hk₀, welfare_eq_head_add P hk hk₀, tail_optimal P hk₀ hk hopt]
    simp [consumption, hk.1]
  · obtain ⟨hy', _⟩ := optimalPath_spec P hy0
    have := welfare_le_value P hk₀ (hy'.prepend hy0 hy)
    rwa [welfare_prepend P hy' hy0 hy hk₀, ← value_eq P hy0] at this

/-- O&R §7.1.2.1 (generic discrete-time model): Concavity of resources: mixed resources dominate the
mixture, strictly at distinct stocks. -/
theorem resources_mix (P : Primitives f u β δ) {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    θ * resources f δ a + (1 - θ) * resources f δ b ≤ resources f δ (θ * a + (1 - θ) * b) ∧
      (a ≠ b → θ * resources f δ a + (1 - θ) * resources f δ b <
        resources f δ (θ * a + (1 - θ) * b)) := by
  have hc := P.f_conc.concaveOn.2 ha hb hθ.le (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hc
  refine ⟨by simp only [resources]; nlinarith, fun hne => ?_⟩
  have hs := P.f_conc.2 ha hb hne hθ (by linarith : (0 : ℝ) < 1 - θ) (by ring)
  simp only [smul_eq_mul] at hs
  simp only [resources]
  nlinarith

/-- O&R §7.1.2.1 (generic discrete-time model): The mixture of two feasible paths is feasible, with
consumption at least the mixture of consumptions. -/
theorem Feasible.mix (P : Primitives f u β δ) {k₀ k₀' θ : ℝ} {k k' : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk' : Feasible f δ k₀' k') (hk₀ : 0 ≤ k₀) (hk₀' : 0 ≤ k₀')
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    Feasible f δ (θ * k₀ + (1 - θ) * k₀') (fun t => θ * k t + (1 - θ) * k' t) ∧
      ∀ t, θ * consumption f δ k t + (1 - θ) * consumption f δ k' t ≤
        consumption f δ (fun t => θ * k t + (1 - θ) * k' t) t := by
  have hmix := fun t => (resources_mix P (hk.nonneg hk₀ t) (hk'.nonneg hk₀' t) hθ hθ1).1
  refine ⟨⟨by simp only [hk.1, hk'.1], fun t => ⟨?_, ?_⟩⟩, fun t => ?_⟩
  · have := mul_nonneg hθ.le (hk.2 t).1
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ) (hk'.2 t).1
    linarith
  · have h1 := mul_le_mul_of_nonneg_left (hk.2 t).2 hθ.le
    have h2 := mul_le_mul_of_nonneg_left (hk'.2 t).2 (by linarith : (0 : ℝ) ≤ 1 - θ)
    linarith [hmix t]
  · simp only [consumption]
    linarith [hmix t]

/-- O&R §7.1.2.1 (generic discrete-time model): Termwise comparison of discounted utility for a
mixture. -/
theorem utility_mix (P : Primitives f u β δ) {c c' c'' θ : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hθ : 0 < θ) (hθ1 : θ < 1) (hle : θ * c + (1 - θ) * c' ≤ c'') :
    θ * u c + (1 - θ) * u c' ≤ u c'' ∧
      (c ≠ c' → θ * u c + (1 - θ) * u c' < u c'') := by
  have hmixnn : 0 ≤ θ * c + (1 - θ) * c' := by nlinarith
  have hmono := P.u_strictMono.monotoneOn hmixnn (hmixnn.trans hle) hle
  have hconc := P.u_conc.concaveOn.2 hc hc' hθ.le (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hconc
  refine ⟨hconc.trans hmono, fun hne => ?_⟩
  have hs := P.u_conc.2 hc hc' hne hθ (by linarith : (0 : ℝ) < 1 - θ) (by ring)
  simp only [smul_eq_mul] at hs
  exact hs.trans_le hmono

/-- O&R §7.1.2.1 (generic discrete-time model): The mixture's welfare dominates the mixture of
welfares. -/
theorem welfare_mix (P : Primitives f u β δ) {k₀ k₀' θ : ℝ} {k k' : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk' : Feasible f δ k₀' k') (hk₀ : 0 ≤ k₀) (hk₀' : 0 ≤ k₀')
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    θ * welfare f u β δ k + (1 - θ) * welfare f u β δ k' ≤
        welfare f u β δ (fun t => θ * k t + (1 - θ) * k' t) ∧
      ((∃ t, consumption f δ k t ≠ consumption f δ k' t ∨
          θ * consumption f δ k t + (1 - θ) * consumption f δ k' t <
            consumption f δ (fun t => θ * k t + (1 - θ) * k' t) t) →
        θ * welfare f u β δ k + (1 - θ) * welfare f u β δ k' <
          welfare f u β δ (fun t => θ * k t + (1 - θ) * k' t)) := by
  obtain ⟨hmixf, hcons⟩ := hk.mix P hk' hk₀ hk₀' hθ hθ1
  have hmix0 : 0 ≤ θ * k₀ + (1 - θ) * k₀' := by nlinarith
  have hs := hk.summable P hk₀
  have hs' := hk'.summable P hk₀'
  have hsm := hmixf.summable P hmix0
  have hlhs : θ * welfare f u β δ k + (1 - θ) * welfare f u β δ k' =
      ∑' t, (θ * (β ^ t * u (consumption f δ k t)) +
        (1 - θ) * (β ^ t * u (consumption f δ k' t))) := by
    unfold welfare
    rw [(hs.mul_left θ).tsum_add (hs'.mul_left (1 - θ)), tsum_mul_left, tsum_mul_left]
  have hterm : ∀ t, θ * (β ^ t * u (consumption f δ k t)) +
      (1 - θ) * (β ^ t * u (consumption f δ k' t)) ≤
        β ^ t * u (consumption f δ (fun t => θ * k t + (1 - θ) * k' t) t) := by
    intro t
    have h := (utility_mix P (hk.consumption_mem P hk₀ t).1 (hk'.consumption_mem P hk₀' t).1 hθ
      hθ1 (hcons t)).1
    have := mul_le_mul_of_nonneg_left h (pow_pos P.β_pos t).le
    linarith
  have hsum := (hs.mul_left θ).add (hs'.mul_left (1 - θ))
  refine ⟨?_, fun ⟨t, ht⟩ => ?_⟩
  · rw [hlhs]
    exact hsum.tsum_le_tsum hterm hsm
  · rw [hlhs]
    refine hsum.tsum_lt_tsum (i := t) hterm ?_ hsm
    have hct := (hk.consumption_mem P hk₀ t).1
    have hct' := (hk'.consumption_mem P hk₀' t).1
    have hstrict : θ * u (consumption f δ k t) + (1 - θ) * u (consumption f δ k' t) <
        u (consumption f δ (fun t => θ * k t + (1 - θ) * k' t) t) := by
      rcases ht with hne | hlt
      · exact (utility_mix P hct hct' hθ hθ1 (hcons t)).2 hne
      · have hmixc : 0 ≤ θ * consumption f δ k t + (1 - θ) * consumption f δ k' t := by
          nlinarith
        have h1 := (utility_mix P hct hct' hθ hθ1 le_rfl).1
        exact h1.trans_lt (P.u_strictMono hmixc (hmixc.trans hlt.le) hlt)
    have := mul_lt_mul_of_pos_left hstrict (pow_pos P.β_pos t)
    linarith

/-- O&R §7.1.2.1 (generic discrete-time model): The optimal path is unique. -/
theorem optimal_unique (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k)
    (hopt : ∀ k', Feasible f δ k₀ k' → welfare f u β δ k' ≤ welfare f u β δ k) :
    k = optimalPath P hk₀ := by
  obtain ⟨ho, hoopt⟩ := optimalPath_spec P hk₀
  set o := optimalPath P hk₀
  by_contra hne
  -- two distinct feasible paths from the same stock differ in some consumption
  have hcne : ∃ t, consumption f δ k t ≠ consumption f δ o t := by
    by_contra hall
    push Not at hall
    apply hne
    funext t
    induction t with
    | zero => rw [hk.1, ho.1]
    | succ t ih =>
      have := hall t
      simp only [consumption, ih] at this
      linarith
  have hθ : (0 : ℝ) < 1 / 2 := by norm_num
  have hθ1 : (1 : ℝ) / 2 < 1 := by norm_num
  obtain ⟨hmixf, -⟩ := hk.mix P ho hk₀ hk₀ hθ hθ1
  have hstrict := (welfare_mix P hk ho hk₀ hk₀ hθ hθ1).2
    (by obtain ⟨t, ht⟩ := hcne; exact ⟨t, Or.inl ht⟩)
  have hmix0 : 1 / 2 * k₀ + (1 - 1 / 2) * k₀ = k₀ := by ring
  rw [hmix0] at hmixf
  have h1 := hopt _ hmixf
  have h2 := hoopt k hk
  have h3 := hopt o ho
  linarith

/-- O&R §7.1.2.1 (generic discrete-time model): The value function is strictly increasing. -/
theorem value_strictMono (P : Primitives f u β δ) : StrictMonoOn (value P) (Ici 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) ≤ a := ha
  have hb' : (0 : ℝ) ≤ b := hb
  obtain ⟨hk, hopt⟩ := optimalPath_spec P ha'
  have hk1 : 0 ≤ optimalPath P ha' 1 := (hk.2 0).1
  have hFa : optimalPath P ha' 1 ≤ resources f δ a :=
    (hk.2 0).2.trans_eq (congrArg (resources f δ) hk.1)
  have hFab := P.resources_strictMono ha hb hab
  obtain ⟨hb1, _⟩ := bellman P hb'
  have hbell := (bellman P hb').2 (optimalPath P ha' 1) hk1 (hFa.trans hFab.le)
  rw [(bellman P ha').1]
  have hc : 0 ≤ resources f δ a - optimalPath P ha' 1 := sub_nonneg.mpr hFa
  have hu := P.u_strictMono hc (by linarith : (0 : ℝ) ≤ resources f δ b - optimalPath P ha' 1)
    (by linarith)
  linarith

/-- O&R §7.1.2.1 (generic discrete-time model): The value function is strictly concave. -/
theorem value_strictConcave (P : Primitives f u β δ) : StrictConcaveOn ℝ (Ici 0) (value P) := by
  refine ⟨convex_Ici 0, fun a ha b hb hne θ θ' hθ hθ' hsum => ?_⟩
  have ha' : (0 : ℝ) ≤ a := ha
  have hb' : (0 : ℝ) ≤ b := hb
  have hθ'' : θ' = 1 - θ := by linarith
  subst hθ''
  have hθ1 : θ < 1 := by linarith
  obtain ⟨hka, _⟩ := optimalPath_spec P ha'
  obtain ⟨hkb, _⟩ := optimalPath_spec P hb'
  obtain ⟨hmixf, -⟩ := hka.mix P hkb ha' hb' hθ hθ1
  have hstrict := (welfare_mix P hka hkb ha' hb' hθ hθ1).2 ⟨0, Or.inr (by
    have hne' : optimalPath P ha' 0 ≠ optimalPath P hb' 0 := by rw [hka.1, hkb.1]; exact hne
    have h := (resources_mix P (hka.nonneg ha' 0) (hkb.nonneg hb' 0) hθ hθ1).2 hne'
    simp only [consumption]
    linarith)⟩
  have hmix0 : 0 ≤ θ * a + (1 - θ) * b := by nlinarith
  have hle := welfare_le_value P hmix0 hmixf
  simp only [smul_eq_mul]
  rw [value_eq P ha', value_eq P hb']
  linarith


/-!
# Interiority and the Euler equation

* `IsOptimal.shift`: every tail of an optimal path is optimal from the stock reached,
  and `IsOptimal.bellman_eq` gives the Bellman equation along the path.
* `interior_choice`: by the Inada conditions a maximizer of `u(F(x) - y) + β V(y)` over
  `0 ≤ y ≤ F(x)` is interior: saving and consumption are both strictly positive.
* `IsOptimal.capital_pos`, `IsOptimal.consumption_pos`: an optimal path from positive
  capital keeps capital and consumption strictly positive.
* `IsOptimal.euler`: `u'(c t) = β u'(c (t+1)) F'(k (t+1))`, `F' = f' + 1 - δ`.
-/



/-- O&R §7.1.2.1 (generic discrete-time model): A feasible path attaining the maximal welfare from
`x`. -/
def IsOptimal (f u : ℝ → ℝ) (β δ x : ℝ) (k : ℕ → ℝ) : Prop :=
  Feasible f δ x k ∧ ∀ k', Feasible f δ x k' → welfare f u β δ k' ≤ welfare f u β δ k

/-- O&R §7.1.2.1 (generic discrete-time model): The chosen optimal path is optimal. -/
theorem isOptimal_optimalPath (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) :
    IsOptimal f u β δ x (optimalPath P hx) := optimalPath_spec P hx

/-- O&R §7.1.2.1 (generic discrete-time model): An optimal path attains the value. -/
theorem IsOptimal.welfare_eq (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) : welfare f u β δ k = value P x := by
  apply le_antisymm (welfare_le_value P hx hk.1)
  rw [value_eq P hx]
  exact hk.2 _ (optimalPath_spec P hx).1

/-- O&R §7.1.2.1 (generic discrete-time model): The tail of an optimal path is optimal (principle of
optimality). -/
theorem IsOptimal.tail (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) : IsOptimal f u β δ (k 1) (tailPath k) := by
  refine ⟨hk.1.tail, fun k' hk' => ?_⟩
  rw [tail_optimal P hx hk.1 hk.2]
  exact welfare_le_value P (hk.1.2 0).1 hk'

/-- O&R §7.1.2.1 (generic discrete-time model): Every shifted tail of an optimal path is optimal
from the stock reached. -/
theorem IsOptimal.shift (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) :
    IsOptimal f u β δ (k t) (fun s => k (t + s)) := by
  induction t with
  | zero => simpa only [zero_add, hk.1.1] using hk
  | succ t ih =>
    have h := ih.tail P (hk.1.nonneg hx t)
    have heq : tailPath (fun s => k (t + s)) = fun s => k (t + 1 + s) := by
      funext s
      simp only [tailPath]
      congr 1
      ring
    rw [heq] at h
    simpa only [add_zero] using h

/-- O&R §7.1.2.1 (generic discrete-time model): The Bellman equation along an optimal path. -/
theorem IsOptimal.bellman_eq (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) :
    value P (k t) = u (resources f δ (k t) - k (t + 1)) + β * value P (k (t + 1)) := by
  have hs := hk.shift P hx t
  have hkt := hk.1.nonneg hx t
  rw [← hs.welfare_eq P hkt, welfare_eq_head_add P hs.1 hkt, tail_optimal P hkt hs.1 hs.2]
  simp only [consumption, add_zero]

/-- O&R §7.1.2.1 (generic discrete-time model): The value at zero capital: `V(0) = u(0) + β V(0)`.
-/
theorem value_zero (P : Primitives f u β δ) : value P 0 = u 0 + β * value P 0 := by
  obtain ⟨hk, -⟩ := optimalPath_spec P (le_refl (0 : ℝ))
  have h1 : optimalPath P (le_refl (0 : ℝ)) 1 = 0 := by
    have := hk.2 0
    rw [hk.1, resources_zero P] at this
    linarith [this.1, this.2]
  have := (bellman P (le_refl (0 : ℝ))).1
  rwa [h1, resources_zero P, sub_zero] at this

/-- O&R §7.1.2.1 (generic discrete-time model): Marginal utility is strictly decreasing (strict
concavity). -/
theorem Primitives.u_prime_anti (P : Primitives f u β δ) : StrictAntiOn (deriv u) (Ioi 0) :=
  (P.u_conc.subset Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv P.u_diff

/-- O&R §7.1.2.1 (generic discrete-time model): A maximizer of `u(F(x) - y) + β V(y)` is interior.
-/
theorem interior_choice (P : Primitives f u β δ) {x y : ℝ} (hx : 0 < x) (hy0 : 0 ≤ y)
    (hyF : y ≤ resources f δ x)
    (hmax : ∀ z, 0 ≤ z → z ≤ resources f δ x →
      u (resources f δ x - z) + β * value P z ≤ u (resources f δ x - y) + β * value P y) :
    0 < y ∧ y < resources f δ x := by
  have hFx : 0 < resources f δ x := by
    have h := P.resources_strictMono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx.le) hx
    rwa [resources_zero P] at h
  have hVmono := value_strictMono P
  have hVconc := value_strictConcave P
  constructor
  · -- saving is positive
    by_contra hle
    push Not at hle
    have hy : y = 0 := le_antisymm hle hy0
    subst hy
    set a := resources f δ x / 2 with ha
    have hapos : 0 < a := half_pos hFx
    have hua : 0 < deriv u a := P.u_prime_pos a hapos
    -- small `ε` with `F(ε) ≤ a` and `β f'(ε) > 1`
    have hFcont : Tendsto (resources f δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (P.resources_cont (0 : ℝ) (mem_Ici.mpr le_rfl)).tendsto
      rw [resources_zero P] at this
      exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    obtain ⟨ε, hε⟩ := ((eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi 0).and
      ((hFcont.eventually (gt_mem_nhds hapos)).and
      ((P.f_inada0.eventually (eventually_gt_atTop (1 / β))).and
      (Ioo_mem_nhdsGT hapos : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo 0 a)))).exists
    obtain ⟨hεpos, hFε, hfε, hεa⟩ := hε
    have hεpos' : (0 : ℝ) < ε := hεpos
    have hεF : ε ≤ resources f δ x := by linarith [hεa.2]
    have hcmp := hmax ε hεpos'.le hεF
    -- `u(F x) - u(F x - ε) ≤ u'(a) ε`
    have hu1 : u (resources f δ x) - u (resources f δ x - ε) ≤ deriv u a * ε := by
      have hpos : 0 < resources f δ x - ε := by linarith [hεa.2]
      have hs := concave_support P.u_conc.concaveOn (mem_Ici.mpr hpos.le) (mem_Ici.mpr hFx.le)
        (P.u_diff _ hpos).hasDerivAt
      have hmono : deriv u (resources f δ x - ε) ≤ deriv u a :=
        P.u_prime_anti.antitoneOn hapos hpos (by linarith [hεa.2])
      have : u (resources f δ x) - u (resources f δ x - ε) ≤
          deriv u (resources f δ x - ε) * ε := by
        have := hs
        rw [show resources f δ x - (resources f δ x - ε) = ε by ring] at this
        exact this
      exact this.trans (mul_le_mul_of_nonneg_right hmono hεpos'.le)
    -- `V(ε) - V(0) ≥ u(F ε) - u(0) ≥ u'(a) f'(ε) ε`
    have hFεpos : 0 < resources f δ ε := by
      have h := P.resources_strictMono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hεpos'.le) hεpos'
      rwa [resources_zero P] at h
    have hV1 : u (resources f δ ε) - u 0 ≤ value P ε - value P 0 := by
      have hb := (bellman P hεpos'.le).2 0 le_rfl hFεpos.le
      rw [sub_zero] at hb
      have hz := value_zero P
      have : value P 0 * (1 - β) = u 0 := by linarith
      have hV0 : value P 0 = u 0 + β * value P 0 := hz
      nlinarith [P.β_pos, P.β_lt_one]
    have hu2 : deriv u a * (deriv f ε * ε) ≤ u (resources f δ ε) - u 0 := by
      have hs := concave_support P.u_conc.concaveOn (mem_Ici.mpr hFεpos.le) (mem_Ici.mpr le_rfl)
        (P.u_diff _ hFεpos).hasDerivAt
      have hmono : deriv u a ≤ deriv u (resources f δ ε) :=
        P.u_prime_anti.antitoneOn hFεpos hapos hFε.le
      have hfε' : deriv f ε * ε ≤ resources f δ ε := by
        have hs' := concave_support P.f_conc.concaveOn (mem_Ici.mpr hεpos'.le) (mem_Ici.mpr le_rfl)
          (P.f_diff _ hεpos').hasDerivAt
        rw [P.f_zero] at hs'
        have := mul_nonneg (sub_nonneg.mpr P.δ_le_one) hεpos'.le
        simp only [resources]
        linarith
      have hfpos : 0 ≤ deriv f ε * ε := mul_nonneg (P.f_prime_pos ε hεpos').le hεpos'.le
      have h1 : deriv u a * (deriv f ε * ε) ≤ deriv u (resources f δ ε) * resources f δ ε :=
        mul_le_mul hmono hfε' hfpos (P.u_prime_pos _ hFεpos).le
      linarith
    have hbf : 1 < β * deriv f ε := by
      have := (div_lt_iff₀' P.β_pos).mp hfε
      linarith
    have hgain : deriv u a * ε < β * (deriv u a * (deriv f ε * ε)) := by
      have := mul_lt_mul_of_pos_left hbf (mul_pos hua hεpos')
      nlinarith
    simp only [sub_zero] at hcmp
    have := mul_le_mul_of_nonneg_left (hu2.trans hV1) P.β_pos.le
    linarith
  · -- consumption is positive
    by_contra hle
    push Not at hle
    have hy : y = resources f δ x := le_antisymm hyF hle
    subst hy
    set Y := resources f δ x
    set S := 2 * (value P Y - value P 0) / Y
    obtain ⟨ε, hε⟩ := ((eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi 0).and
      ((P.u_inada0.eventually (eventually_gt_atTop (β * S))).and
      (Ioo_mem_nhdsGT (half_pos hFx) : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo 0 (Y / 2)))).exists
    obtain ⟨hεpos, huε, hεY⟩ := hε
    have hεpos' : (0 : ℝ) < ε := hεpos
    have hYε : Y / 2 < Y - ε := by linarith [hεY.2]
    have hcmp := hmax (Y - ε) (by linarith) (by linarith)
    rw [sub_self, show Y - (Y - ε) = ε by ring] at hcmp
    -- `u(ε) - u(0) ≥ u'(ε) ε`
    have hu : deriv u ε * ε ≤ u ε - u 0 := by
      have hs := concave_support P.u_conc.concaveOn (mem_Ici.mpr hεpos'.le) (mem_Ici.mpr le_rfl)
        (P.u_diff _ hεpos').hasDerivAt
      linarith
    -- `V(Y) - V(Y - ε) ≤ S ε` by concavity and monotonicity
    have hV : value P Y - value P (Y - ε) ≤ S * ε := by
      have hslope := hVconc.concaveOn.slope_anti_adjacent (x := 0) (y := Y - ε) (z := Y)
        (mem_Ici.mpr le_rfl) (mem_Ici.mpr hFx.le) (by linarith) (by linarith)
      rw [show Y - (Y - ε) = ε by ring, div_le_div_iff₀ hεpos' (by linarith : (0 : ℝ) < Y - ε - 0),
        sub_zero] at hslope
      have hmono : value P (Y - ε) ≤ value P Y :=
        hVmono.monotoneOn (mem_Ici.mpr (by linarith)) (mem_Ici.mpr hFx.le) (by linarith)
      have hV0 : value P 0 ≤ value P (Y - ε) :=
        hVmono.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by linarith)) (by linarith)
      have hS : (value P (Y - ε) - value P 0) / (Y - ε) ≤ S := by
        rw [div_le_iff₀ (by linarith)]
        simp only [S]
        rw [div_mul_eq_mul_div, le_div_iff₀ hFx]
        nlinarith
      have h2 : (value P Y - value P (Y - ε)) * (Y - ε) ≤
          (value P (Y - ε) - value P 0) * ε := hslope
      have h3 := (div_le_iff₀ (by linarith : (0 : ℝ) < Y - ε)).mp hS
      nlinarith
    have hgain : β * S * ε < deriv u ε * ε := mul_lt_mul_of_pos_right huε hεpos'
    have := mul_le_mul_of_nonneg_left hV P.β_pos.le
    linarith

/-- O&R §7.1.2.1 (generic discrete-time model): Gross resources are positive at positive capital. -/
theorem Primitives.resources_pos (P : Primitives f u β δ) {k : ℝ} (hk : 0 < k) :
    0 < resources f δ k := by
  have h := P.resources_strictMono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hk.le) hk
  rwa [resources_zero P] at h

/-- O&R §7.1.2.1 (generic discrete-time model): An optimal path from positive capital keeps capital
strictly positive and consumption strictly positive. -/
theorem IsOptimal.interior (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) :
    0 < k t ∧ 0 < k (t + 1) ∧ 0 < consumption f δ k t := by
  have hpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => rw [hk.1.1]; exact hx
    | succ t ih =>
      have hbell := hk.bellman_eq P hx.le t
      exact (interior_choice P ih (hk.1.2 t).1 (hk.1.2 t).2 (fun z hz0 hzF => by
        rw [← hbell]; exact (bellman P (hk.1.nonneg hx.le t)).2 z hz0 hzF)).1
  refine ⟨hpos t, hpos (t + 1), ?_⟩
  have hbell := hk.bellman_eq P hx.le t
  have h := (interior_choice P (hpos t) (hk.1.2 t).1 (hk.1.2 t).2 (fun z hz0 hzF => by
    rw [← hbell]; exact (bellman P (hk.1.nonneg hx.le t)).2 z hz0 hzF)).2
  simp only [consumption]
  linarith

/-- O&R §7.1.2.1 (generic discrete-time model): The derivative of gross resources is `f'(k) + 1 -
δ`. -/
theorem hasDerivAt_resources (P : Primitives f u β δ) {k : ℝ} (hk : 0 < k) :
    HasDerivAt (resources f δ) (deriv f k + (1 - δ)) k := by
  have h1 : HasDerivAt (fun y => f y + (1 - δ) * y) (deriv f k + (1 - δ) * 1) k :=
    (P.f_diff k hk).hasDerivAt.add ((hasDerivAt_id' k).const_mul (1 - δ))
  rw [mul_one] at h1
  exact h1

/-- O&R §7.1.2.1 (generic discrete-time model): The Euler equation along an optimal path. -/
theorem IsOptimal.euler (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) :
    deriv u (consumption f δ k t) =
      β * deriv u (consumption f δ k (t + 1)) * (deriv f (k (t + 1)) + (1 - δ)) := by
  obtain ⟨hkt, hkt1, hct⟩ := hk.interior P hx t
  obtain ⟨-, -, hct1⟩ := hk.interior P hx (t + 1)
  set ψ : ℝ → ℝ := fun y => u (resources f δ (k t) - y) +
    β * (u (resources f δ y - k (t + 2)) + β * value P (k (t + 2)))
  have hct' : 0 < resources f δ (k t) - k (t + 1) := hct
  have hct1' : 0 < resources f δ (k (t + 1)) - k (t + 2) := hct1
  -- `ψ` has a local maximum at `k (t + 1)`
  have hloc : IsLocalMax ψ (k (t + 1)) := by
    have hFc : ContinuousAt (resources f δ) (k (t + 1)) :=
      (hasDerivAt_resources P hkt1).continuousAt
    have hnear : ∀ᶠ y in 𝓝 (k (t + 1)), 0 < y ∧ y < resources f δ (k t) ∧
        k (t + 2) < resources f δ y := by
      refine (lt_mem_nhds hkt1).and
        ((gt_mem_nhds (by linarith : k (t + 1) < resources f δ (k t))).and ?_)
      exact hFc.eventually (lt_mem_nhds (by linarith : k (t + 2) < resources f δ (k (t + 1))))
    filter_upwards [hnear] with y hy
    obtain ⟨hypos, hyF, hy2⟩ := hy
    have hbt := hk.bellman_eq P hx.le t
    have hbt1 := hk.bellman_eq P hx.le (t + 1)
    have hin1 := (bellman P hypos.le).2 (k (t + 2)) (hk.1.2 (t + 1)).1 hy2.le
    have hin0 := (bellman P (hk.1.nonneg hx.le t)).2 y hypos.le hyF.le
    have := mul_le_mul_of_nonneg_left hin1 P.β_pos.le
    simp only [ψ]
    rw [show t + 1 + 1 = t + 2 by ring] at hbt1
    have hbt1' : β * value P (k (t + 1)) = β * (u (resources f δ (k (t + 1)) - k (t + 2)) +
        β * value P (k (t + 2))) := by rw [hbt1]
    linarith
  -- its derivative at `k (t + 1)`
  have hd1 : HasDerivAt (fun y => u (resources f δ (k t) - y))
      (deriv u (resources f δ (k t) - k (t + 1)) * (-1)) (k (t + 1)) :=
    (P.u_diff _ hct').hasDerivAt.comp (k (t + 1)) ((hasDerivAt_id (k (t + 1))).const_sub _)
  have hd2 : HasDerivAt (fun y => u (resources f δ y - k (t + 2)))
      (deriv u (resources f δ (k (t + 1)) - k (t + 2)) * (deriv f (k (t + 1)) + (1 - δ)))
      (k (t + 1)) :=
    (P.u_diff _ hct1').hasDerivAt.comp (k (t + 1)) ((hasDerivAt_resources P hkt1).sub_const _)
  have hd := hd1.add ((hd2.add_const (β * value P (k (t + 2)))).const_mul β)
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hc0 : consumption f δ k t = resources f δ (k t) - k (t + 1) := rfl
  have hc1 : consumption f δ k (t + 1) = resources f δ (k (t + 1)) - k (t + 2) := rfl
  rw [hc0, hc1]
  linarith


/-!
# The policy function and global dynamics of the discrete Ramsey–Cass model

* `policy`: next period's capital `g(x)` on the optimal path from `x`;
  `IsOptimal.succ_eq_policy`: every optimal path follows `k(t+1) = g(k(t))`.
* `policy_strictMono`: `g` is strictly increasing (increasing differences of
  `u(F(x) - y)` in `(x, y)`; strictness from the Euler equation).
* `existsUnique_steady`, `steady`: the unique positive `k*` with
  `β (f'(k*) + 1 - δ) = 1`.
* `IsOptimal.tendsto`: every optimal path from positive capital converges to `k*`;
  `IsOptimal.dynamics_below`, `IsOptimal.dynamics_above`: strictly monotonically,
  with consumption moving in the same direction, and never crossing `k*`.
* `consumptionPolicy_strictMono`, `IsOptimal.capital_lt`, `IsOptimal.consumption_lt`,
  `IsOptimal.absolute_convergence`: consumption is strictly increasing in capital,
  optimal paths of identical economies never cross, and they converge to each other.
-/



/-- O&R §7.1.2.1 (generic discrete-time model): Shifting an interval right lowers the increment of a
strictly concave function. -/
theorem shift_increment_lt (P : Primitives f u β δ) {a b Δ : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hΔ : 0 < Δ) : u (b + Δ) - u (a + Δ) < u b - u a := by
  have hs1 := P.u_conc.secant_strict_mono (a := a) (x := b) (y := b + Δ) (mem_Ici.mpr ha)
    (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith)) (ne_of_gt hab)
    (by linarith) (by linarith)
  have hs2 := P.u_conc.secant_strict_mono (a := b + Δ) (x := a) (y := a + Δ)
    (mem_Ici.mpr (by linarith)) (mem_Ici.mpr ha) (mem_Ici.mpr (by linarith)) (by linarith)
    (by linarith) (by linarith)
  have hL : 0 < b - a := sub_pos.mpr hab
  have e1 : (u (a + Δ) - u (b + Δ)) / (a + Δ - (b + Δ)) = (u (b + Δ) - u (a + Δ)) / (b - a) := by
    rw [show a + Δ - (b + Δ) = -(b - a) by ring, div_neg, ← neg_div]
    ring_nf
  have e2 : (u a - u (b + Δ)) / (a - (b + Δ)) = (u (b + Δ) - u a) / (b + Δ - a) := by
    rw [show a - (b + Δ) = -(b + Δ - a) by ring, div_neg, ← neg_div]
    ring_nf
  rw [e1, e2] at hs2
  have h := hs2.trans hs1
  rwa [div_lt_div_iff_of_pos_right hL] at h

/-- O&R §7.1.2.1 (generic discrete-time model): Next period's capital chosen from `x`. -/
noncomputable def policy (P : Primitives f u β δ) (x : ℝ) : ℝ :=
  if hx : 0 ≤ x then optimalPath P hx 1 else 0

/-- O&R §7.1.2.1 (generic discrete-time model): The policy is the date-one capital of the optimal
path. -/
theorem policy_eq (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) :
    policy P x = optimalPath P hx 1 := by
  simp only [policy, hx, ↓reduceDIte]

/-- O&R §7.1.2.1 (generic discrete-time model): Every optimal path follows the policy. -/
theorem IsOptimal.succ_eq_policy (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) : k (t + 1) = policy P (k t) := by
  have hkt := hk.1.nonneg hx t
  have hs := hk.shift P hx t
  have heq := optimal_unique P hkt hs.1 hs.2
  rw [policy_eq P hkt]
  exact congrFun heq 1

/-- O&R §7.1.2.1 (generic discrete-time model): The Bellman equation at the policy, with its
feasibility. -/
theorem bellman_policy (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) :
    value P x = u (resources f δ x - policy P x) + β * value P (policy P x) ∧
      0 ≤ policy P x ∧ policy P x ≤ resources f δ x := by
  obtain ⟨hk, -⟩ := optimalPath_spec P hx
  rw [policy_eq P hx]
  exact ⟨(bellman P hx).1, (hk.2 0).1, (hk.2 0).2.trans_eq (congrArg (resources f δ) hk.1)⟩

/-- O&R §7.1.2.1 (generic discrete-time model): From `x > 0`, next capital is interior and the Euler
equation holds at date zero. -/
theorem policy_interior (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) :
    0 < policy P x ∧ policy P x < resources f δ x ∧
      deriv u (resources f δ x - policy P x) =
        β * deriv u (resources f δ (policy P x) - policy P (policy P x)) *
          (deriv f (policy P x) + (1 - δ)) := by
  have hk := isOptimal_optimalPath P hx.le
  obtain ⟨-, h1, hc⟩ := hk.interior P hx 0
  have he := hk.euler P hx 0
  have hs0 := hk.succ_eq_policy P hx.le 0
  have hs1 := hk.succ_eq_policy P hx.le 1
  have h0 : optimalPath P hx.le 0 = x := hk.1.1
  simp only [consumption, zero_add] at hc he h1 hs0 hs1
  rw [h0] at hs0 hc he
  rw [hs0] at h1 hc he hs1
  rw [hs1] at he
  exact ⟨h1, by linarith, he⟩

/-- O&R §7.1.2.1 (generic discrete-time model): The policy is strictly increasing. -/
theorem policy_strictMono (P : Primitives f u β δ) : StrictMonoOn (policy P) (Ioi 0) := by
  intro x hx x' hx' hxx
  have hx0 : (0 : ℝ) < x := hx
  have hx0' : (0 : ℝ) < x' := hx'
  obtain ⟨-, hy0, hyF⟩ := bellman_policy P hx0.le
  obtain ⟨-, hy0', hyF'⟩ := bellman_policy P hx0'.le
  have hFF := P.resources_strictMono (mem_Ici.mpr hx0.le) (mem_Ici.mpr hx0'.le) hxx
  have hweak : policy P x ≤ policy P x' := by
    by_contra hlt
    push Not at hlt
    have h1 := (bellman P hx0.le).2 (policy P x') hy0' (hlt.le.trans hyF)
    have h2 := (bellman P hx0'.le).2 (policy P x) hy0 (hyF.trans hFF.le)
    have hb1 := (bellman_policy P hx0.le).1
    have hb2 := (bellman_policy P hx0'.le).1
    have hinc := shift_increment_lt P (a := resources f δ x - policy P x)
      (b := resources f δ x - policy P x') (Δ := resources f δ x' - resources f δ x)
      (sub_nonneg.mpr hyF) (by linarith) (by linarith)
    rw [show resources f δ x - policy P x' + (resources f δ x' - resources f δ x) =
        resources f δ x' - policy P x' by ring,
      show resources f δ x - policy P x + (resources f δ x' - resources f δ x) =
        resources f δ x' - policy P x by ring] at hinc
    linarith
  rcases lt_or_eq_of_le hweak with hlt | heq
  · exact hlt
  · -- equal choices contradict the two Euler equations
    exfalso
    obtain ⟨hp, hpF, he⟩ := policy_interior P hx0
    obtain ⟨-, hpF', he'⟩ := policy_interior P hx0'
    rw [← heq] at he' hpF'
    have hu : deriv u (resources f δ x - policy P x) = deriv u (resources f δ x' - policy P x) := by
      rw [he, he']
    have hc : 0 < resources f δ x - policy P x := by linarith
    have hc' : 0 < resources f δ x' - policy P x := by linarith
    have := P.u_prime_anti.injOn hc hc' hu
    linarith

/-- O&R §7.1.2.1 (generic discrete-time model): The steady-state target `1/β - (1 - δ)` is positive.
-/
theorem Primitives.target_pos (P : Primitives f u β δ) : 0 < 1 / β - (1 - δ) := by
  have h1 : 1 < 1 / β := by rw [lt_div_iff₀ P.β_pos]; linarith [P.β_lt_one]
  linarith [P.δ_nonneg]

/-- O&R §7.1.2.1 (generic discrete-time model): There is a unique positive `k` with `f'(k) = 1/β -
(1 - δ)` (Inada conditions). -/
theorem Primitives.existsUnique_steady (P : Primitives f u β δ) :
    ∃! k : ℝ, 0 < k ∧ deriv f k = 1 / β - (1 - δ) :=
  existsUnique_positive_root_of_inada (deriv f) _ P.target_pos P.f_prime_cont
    (production_deriv_strictAnti f P.f_conc P.f_diff) P.f_inada0 P.f_inadaTop

/-- O&R §7.1.2.1 (generic discrete-time model): The steady state: `β (f'(k*) + 1 - δ) = 1`. -/
noncomputable def steady (P : Primitives f u β δ) : ℝ :=
  Classical.choose P.existsUnique_steady.exists

/-- O&R §7.1.2.1 (generic discrete-time model): The steady state is positive and satisfies the
modified golden rule. -/
theorem steady_spec (P : Primitives f u β δ) :
    0 < steady P ∧ deriv f (steady P) = 1 / β - (1 - δ) :=
  Classical.choose_spec P.existsUnique_steady.exists

/-- O&R §7.1.2.1 (generic discrete-time model): At the steady state the Euler equation holds with
constant consumption: `β (f'(k*) + 1 - δ) = 1`. -/
theorem steady_euler (P : Primitives f u β δ) : β * (deriv f (steady P) + (1 - δ)) = 1 := by
  rw [(steady_spec P).2]
  field_simp [P.β_pos.ne']
  ring

/-- O&R §7.1.2.1 (generic discrete-time model): Steady-state consumption `c* = F(k*) - k*` is
positive. -/
theorem steady_consumption_pos (P : Primitives f u β δ) :
    0 < resources f δ (steady P) - steady P := by
  obtain ⟨hk, hd⟩ := steady_spec P
  have hgap := marginal_product_times_capital_lt_output f _ P.f_conc P.f_zero hk (P.f_diff _ hk)
  rw [hd] at hgap
  have h1 : 1 < 1 / β := by rw [lt_div_iff₀ P.β_pos]; linarith [P.β_lt_one]
  have : (1 - (1 - δ)) * steady P < (1 / β - (1 - δ)) * steady P :=
    mul_lt_mul_of_pos_right (by linarith) hk
  simp only [resources]
  nlinarith

/-- O&R §7.1.2.1 (generic discrete-time model): The gross return `f'(k) + 1 - δ` is positive. -/
theorem hasDerivAt_resources_pos (P : Primitives f u β δ) {k : ℝ} (hk : 0 < k) :
    0 < deriv f k + (1 - δ) := by
  have := P.f_prime_pos k hk
  linarith [P.δ_le_one]

/-- O&R §7.1.2.1 (generic discrete-time model): An optimal path is monotone. -/
theorem IsOptimal.monotone_or_antitone (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x)
    {k : ℕ → ℝ} (hk : IsOptimal f u β δ x k) :
    (k 0 ≤ k 1 → Monotone k) ∧ (k 1 ≤ k 0 → Antitone k) := by
  have hpos : ∀ t, 0 < k t := fun t => (hk.interior P hx t).1
  have hsucc := hk.succ_eq_policy P hx.le
  constructor
  · intro h01
    apply monotone_nat_of_le_succ
    intro t
    induction t with
    | zero => exact h01
    | succ t ih =>
      calc k (t + 1) = policy P (k t) := hsucc t
        _ ≤ policy P (k (t + 1)) := (policy_strictMono P).monotoneOn (hpos t) (hpos (t + 1)) ih
        _ = k (t + 1 + 1) := (hsucc (t + 1)).symm
  · intro h10
    apply antitone_nat_of_succ_le
    intro t
    induction t with
    | zero => exact h10
    | succ t ih =>
      calc k (t + 1 + 1) = policy P (k (t + 1)) := hsucc (t + 1)
        _ ≤ policy P (k t) := (policy_strictMono P).monotoneOn (hpos (t + 1)) (hpos t) ih
        _ = k (t + 1) := (hsucc t).symm

/-- O&R §7.1.2.1 (generic discrete-time model): **optimal paths are bounded by
`max(k₀, k*)`**, even without depreciation. A path that keeps rising above `k*` has falling
consumption (Euler), and is beaten by holding capital constant at the date it passes `k*`. -/
theorem IsOptimal.le_max (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) : k t ≤ max x (steady P) := by
  have hpos : ∀ t, 0 < k t := fun t => (hk.interior P hx t).1
  have hcpos : ∀ t, 0 < consumption f δ k t := fun t => (hk.interior P hx t).2.2
  have hsucc := hk.succ_eq_policy P hx.le
  obtain ⟨hmono, hanti⟩ := hk.monotone_or_antitone P hx
  obtain ⟨hks, hkd⟩ := steady_spec P
  rcases le_total (k 0) (k 1) with h01 | h10
  swap
  · exact ((hanti h10) (Nat.zero_le t)).trans (by rw [hk.1.1]; exact le_max_left _ _)
  by_contra hgt
  push Not at hgt
  have hT : steady P < k t := lt_of_le_of_lt (le_max_right _ _) hgt
  -- above `k*` the Euler equation makes consumption fall whenever capital rises
  have hfall : ∀ s, steady P < k (s + 1) →
      consumption f δ k (s + 1) < consumption f δ k s := by
    intro s hs
    have he := hk.euler P hx s
    have hfd : deriv f (k (s + 1)) < deriv f (steady P) :=
      (production_deriv_strictAnti f P.f_conc P.f_diff) hks (hpos (s + 1)) hs
    have hg : β * (deriv f (k (s + 1)) + (1 - δ)) < 1 := by
      have := steady_euler P; nlinarith [P.β_pos]
    by_contra hle
    push Not at hle
    have hu := P.u_prime_anti.antitoneOn (hcpos s) (hcpos (s + 1)) hle
    have hup := P.u_prime_pos _ (hcpos (s + 1))
    have hFp := hasDerivAt_resources_pos P (hpos (s + 1))
    nlinarith
  by_cases hstrict : ∃ t0, t ≤ t0 ∧ k t0 < k (t0 + 1)
  · obtain ⟨t0, ht0, hlt0⟩ := hstrict
    -- strictly increasing from `t0` on
    have hinc : ∀ s, k (t0 + s) < k (t0 + s + 1) := by
      intro s
      induction s with
      | zero => simpa using hlt0
      | succ s ih =>
        rw [show t0 + (s + 1) = t0 + s + 1 by ring]
        calc k (t0 + s + 1) = policy P (k (t0 + s)) := hsucc _
          _ < policy P (k (t0 + s + 1)) := policy_strictMono P (hpos _) (hpos _) ih
          _ = k (t0 + s + 1 + 1) := (hsucc _).symm
    have habove : ∀ s, steady P < k (t0 + s + 1) := by
      intro s
      have hmon := hmono h01 (show t ≤ t0 + s + 1 by omega)
      linarith
    have hcle : ∀ s, consumption f δ k (t0 + s) ≤ consumption f δ k t0 := by
      intro s
      induction s with
      | zero => simp
      | succ s ih =>
        have := hfall (t0 + s) (habove s)
        rw [show t0 + (s + 1) = t0 + s + 1 by ring]
        linarith
    set y := k t0
    have hsT := hk.shift P hx.le t0
    have hgap : consumption f δ k t0 < resources f δ y - y := by
      simp only [consumption, y]; linarith [hinc 0]
    have hz : Feasible f δ y (fun _ => y) :=
      ⟨rfl, fun _ => ⟨(hpos t0).le, by linarith [hcpos t0]⟩⟩
    have hzc : ∀ s, consumption f δ (fun _ => y) s = resources f δ y - y := fun _ => rfl
    have hle := hsT.2 _ hz
    have hlt : welfare f u β δ (fun s => k (t0 + s)) < welfare f u β δ (fun _ => y) := by
      refine (hsT.1.summable P (hpos t0).le).tsum_lt_tsum (i := 0) (fun s => ?_) ?_
        (hz.summable P (hpos t0).le)
      · rw [hzc]
        refine mul_le_mul_of_nonneg_left (P.u_strictMono.monotoneOn
          (mem_Ici.mpr (hcpos _).le) (mem_Ici.mpr (by linarith [hcpos t0])) ?_)
          (pow_pos P.β_pos s).le
        have := hcle s
        change consumption f δ k (t0 + s) ≤ _
        linarith
      · rw [hzc]
        simp only [pow_zero, one_mul]
        exact P.u_strictMono (mem_Ici.mpr (hcpos _).le) (mem_Ici.mpr (by linarith [hcpos t0]))
          (by change consumption f δ k (t0 + 0) < _; simpa using hgap)
    linarith
  · -- otherwise capital is constant from `t` on, at a stock above `k*`: impossible
    push Not at hstrict
    have hconst : k (t + 1) = k t := le_antisymm (hstrict t le_rfl) (hmono h01 (Nat.le_succ t))
    have hconst2 : k (t + 2) = k (t + 1) :=
      le_antisymm (hstrict (t + 1) (Nat.le_succ t)) (hmono h01 (Nat.le_succ _))
    have he := hk.euler P hx t
    have hc : consumption f δ k (t + 1) = consumption f δ k t := by
      simp only [consumption, hconst, hconst2]
    rw [hc] at he
    have hup := P.u_prime_pos _ (hcpos t)
    have hβ1 : β * (deriv f (k (t + 1)) + (1 - δ)) = 1 := by
      have : deriv u (consumption f δ k t) * (β * (deriv f (k (t + 1)) + (1 - δ)) - 1) = 0 := by
        linear_combination -he
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (ne_of_gt hup)
      · linarith
    have hfd : deriv f (k (t + 1)) < deriv f (steady P) :=
      (production_deriv_strictAnti f P.f_conc P.f_diff) hks (hpos _) (by rw [hconst]; exact hT)
    have := steady_euler P
    nlinarith [P.β_pos]

/-- O&R §7.1.2.1 (generic discrete-time model): Every optimal path from positive capital converges
to the steady state. -/
theorem IsOptimal.tendsto (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) : Tendsto k atTop (𝓝 (steady P)) := by
  have hpos : ∀ t, 0 < k t := fun t => (hk.interior P hx t).1
  have hcpos : ∀ t, 0 < consumption f δ k t := fun t => (hk.interior P hx t).2.2
  have hbd : ∀ t, k t ≤ max x (steady P) := fun t => hk.le_max P hx t
  obtain ⟨hmono, hanti⟩ := hk.monotone_or_antitone P hx
  -- the limit
  obtain ⟨L, hL⟩ : ∃ L, Tendsto k atTop (𝓝 L) := by
    rcases le_total (k 0) (k 1) with h | h
    · exact ⟨_, tendsto_atTop_ciSup (hmono h) ⟨max x (steady P), by
        rintro _ ⟨t, rfl⟩; exact hbd t⟩⟩
    · exact ⟨_, tendsto_atTop_ciInf (hanti h) ⟨0, by rintro _ ⟨t, rfl⟩; exact (hpos t).le⟩⟩
  have hL0 : 0 ≤ L := ge_of_tendsto' hL (fun t => (hpos t).le)
  have hshift : Tendsto (fun t => k (t + 1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)
  have hFcont : ContinuousWithinAt (resources f δ) (Ici 0) L := P.resources_cont L hL0
  have hFk : Tendsto (fun t => resources f δ (k t)) atTop (𝓝 (resources f δ L)) :=
    hFcont.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hL, Eventually.of_forall
      (fun t => mem_Ici.mpr (hpos t).le)⟩)
  have hc : Tendsto (consumption f δ k) atTop (𝓝 (resources f δ L - L)) := hFk.sub hshift
  have hLF : L ≤ resources f δ L := by
    have h := le_of_tendsto_of_tendsto hshift hFk (Eventually.of_forall (fun t => (hk.1.2 t).2))
    exact h
  obtain ⟨hks, hkd⟩ := steady_spec P
  have hr := P.target_pos
  -- case `L = 0` is impossible
  rcases hL0.eq_or_lt with hL00 | hLpos
  · exfalso
    subst hL00
    have hk0 : Tendsto (fun t => k (t + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hshift, Eventually.of_forall (fun t => hpos (t + 1))⟩
    have hbig := (P.f_inada0.comp hk0).eventually (eventually_gt_atTop (1 / β - (1 - δ)))
    obtain ⟨T, hT⟩ := eventually_atTop.mp hbig
    -- consumption rises from `T` on
    have hrise : ∀ t, T ≤ t → consumption f δ k t < consumption f δ k (t + 1) := by
      intro t ht
      have he := hk.euler P hx t
      have hg : 1 < β * (deriv f (k (t + 1)) + (1 - δ)) := by
        have h := hT t ht
        simp only [Function.comp_apply] at h
        have := mul_lt_mul_of_pos_left h P.β_pos
        rw [mul_sub, mul_div_cancel₀ _ P.β_pos.ne'] at this
        nlinarith
      by_contra hle
      push Not at hle
      have hu := P.u_prime_anti.antitoneOn (hcpos (t + 1)) (hcpos t) hle
      have hup := P.u_prime_pos _ (hcpos (t + 1))
      have : deriv u (consumption f δ k (t + 1)) <
          β * deriv u (consumption f δ k (t + 1)) * (deriv f (k (t + 1)) + (1 - δ)) := by
        nlinarith
      linarith
    have hge : ∀ n, consumption f δ k T ≤ consumption f δ k (T + n) := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n ih => exact ih.trans (hrise (T + n) (by omega)).le
    rw [resources_zero P, sub_zero] at hc
    have hev := (hc.eventually (gt_mem_nhds (hcpos T)))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    have := hN (T + N) (by omega)
    have := hge N
    linarith
  -- case `F(L) = L`: consumption vanishes, contradicted by jumping to `k*`
  rcases lt_or_eq_of_le hLF with hFL | hFL
  · -- `F(L) > L`: the Euler equation in the limit pins down `L = k*`
    have hcL : 0 < resources f δ L - L := sub_pos.mpr hFL
    have huc : ContinuousAt (deriv u) (resources f δ L - L) :=
      P.u_prime_cont.continuousAt (Ioi_mem_nhds hcL)
    have hfc : ContinuousAt (deriv f) L := P.f_prime_cont.continuousAt (Ioi_mem_nhds hLpos)
    have hlhs := huc.tendsto.comp hc
    have hrhs := ((huc.tendsto.comp (hc.comp (tendsto_add_atTop_nat 1))).const_mul β).mul
      ((hfc.tendsto.comp hshift).add_const (1 - δ))
    have heq : deriv u (resources f δ L - L) =
        β * deriv u (resources f δ L - L) * (deriv f L + (1 - δ)) :=
      tendsto_nhds_unique hlhs (hrhs.congr (fun t => by
        simp only [Function.comp_apply]
        exact (hk.euler P hx t).symm))
    have hup := P.u_prime_pos _ hcL
    have hβ : β * (deriv f L + (1 - δ)) = 1 := by
      have : deriv u (resources f δ L - L) * (β * (deriv f L + (1 - δ)) - 1) = 0 := by
        linear_combination -heq
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (ne_of_gt hup)
      · linarith
    have hfL : deriv f L = 1 / β - (1 - δ) := by
      field_simp [P.β_pos.ne']
      linarith
    have := P.existsUnique_steady.unique ⟨hLpos, hfL⟩ ⟨hks, hkd⟩
    rw [this] at hL
    exact hL
  · exfalso
    -- consumption tends to zero and `L > k*`
    rw [← hFL, sub_self] at hc
    have hLks : steady P < L := by
      have hfL : f L = δ * L := by simp only [resources] at hFL; linarith
      have hgap := marginal_product_times_capital_lt_output f L P.f_conc P.f_zero hLpos
        (P.f_diff L hLpos)
      rw [hfL] at hgap
      have hdL : deriv f L < δ := by nlinarith
      by_contra hle
      push Not at hle
      have := (production_deriv_strictAnti f P.f_conc P.f_diff).antitoneOn hLpos hks hle
      rw [hkd] at this
      have h1 : 1 < 1 / β := by rw [lt_div_iff₀ P.β_pos]; linarith [P.β_lt_one]
      linarith
    have hcs0 := steady_consumption_pos P
    set cs := resources f δ (steady P) - steady P with hcs_def
    have hcs : 0 < cs := hcs0
    obtain ⟨T, hT⟩ := eventually_atTop.mp ((hL.eventually (lt_mem_nhds hLks)).and
      (hc.eventually (gt_mem_nhds (half_pos hcs))))
    -- the alternative path from `k T`: move to `k*` and stay there
    set z : ℕ → ℝ := fun s => if s = 0 then k T else steady P
    have hFmono : resources f δ (steady P) ≤ resources f δ (k T) :=
      P.resources_strictMono.monotoneOn (mem_Ici.mpr hks.le) (mem_Ici.mpr (hpos T).le)
        (hT T le_rfl).1.le
    have hFT : steady P < resources f δ (k T) := by linarith
    have hz : Feasible f δ (k T) z := by
      refine ⟨rfl, fun s => ⟨?_, ?_⟩⟩
      · simp only [z, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]; exact hks.le
      · rcases s with _ | s
        · simp only [z, zero_add, one_ne_zero, ↓reduceIte]; exact hFT.le
        · simp only [z, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]; linarith
    have hzc : ∀ s, cs ≤ consumption f δ z s := by
      intro s
      rcases s with _ | s
      · simp only [consumption, z, zero_add, one_ne_zero, ↓reduceIte]
        linarith
      · simp only [consumption, z, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
        exact le_rfl
    have hsT := hk.shift P hx.le T
    have hle := hsT.2 z hz
    -- compare welfare termwise
    have hshc : ∀ s, consumption f δ (fun s => k (T + s)) s ≤ cs / 2 := by
      intro s
      have := (hT (T + s) (by omega)).2
      exact this.le
    have hshnn : ∀ s, 0 ≤ consumption f δ (fun s => k (T + s)) s :=
      fun s => (hsT.1.consumption_mem P (hpos T).le s).1
    have hgeo := summable_geometric_of_lt_one P.β_pos.le P.β_lt_one
    have h1 : welfare f u β δ (fun s => k (T + s)) ≤ ∑' s, β ^ s * u (cs / 2) :=
      (hsT.1.summable P (hpos T).le).tsum_le_tsum (fun s => mul_le_mul_of_nonneg_left
        (P.u_strictMono.monotoneOn (hshnn s) (mem_Ici.mpr (half_pos hcs).le) (hshc s))
        (pow_pos P.β_pos s).le) (hgeo.mul_right _)
    have h2 : ∑' s, β ^ s * u (cs / 2) < ∑' s, β ^ s * u cs :=
      (hgeo.mul_right _).tsum_lt_tsum (i := 0) (fun s => mul_le_mul_of_nonneg_left
        (P.u_strictMono.monotoneOn (mem_Ici.mpr (half_pos hcs).le) (mem_Ici.mpr hcs.le)
          (half_le_self hcs.le)) (pow_pos P.β_pos s).le)
        (by
          simp only [pow_zero, one_mul]
          exact P.u_strictMono (mem_Ici.mpr (half_pos hcs).le) (mem_Ici.mpr hcs.le)
            (half_lt_self hcs))
        (hgeo.mul_right _)
    have h3 : ∑' s, β ^ s * u cs ≤ welfare f u β δ z :=
      (hgeo.mul_right _).tsum_le_tsum (fun s => mul_le_mul_of_nonneg_left
        (P.u_strictMono.monotoneOn (mem_Ici.mpr hcs.le)
          (mem_Ici.mpr (hcs.le.trans (hzc s))) (hzc s)) (pow_pos P.β_pos s).le)
        (hz.summable P (hpos T).le)
    linarith

/-- O&R §7.1.2.1 (generic discrete-time model): Consumption converges to `c* = F(k*) - k*`. -/
theorem IsOptimal.consumption_tendsto (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x)
    {k : ℕ → ℝ} (hk : IsOptimal f u β δ x k) :
    Tendsto (consumption f δ k) atTop (𝓝 (resources f δ (steady P) - steady P)) := by
  have hL := hk.tendsto P hx
  have hks := (steady_spec P).1
  have hFk : Tendsto (fun t => resources f δ (k t)) atTop (𝓝 (resources f δ (steady P))) :=
    (P.resources_cont _ (mem_Ici.mpr hks.le)).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hL, Eventually.of_forall (fun t => mem_Ici.mpr (hk.interior P hx t).1.le)⟩)
  exact hFk.sub (hL.comp (tendsto_add_atTop_nat 1))

/-- O&R §7.1.2.1 (generic discrete-time model): Below the steady state an optimal path rises
strictly toward `k*`, with rising consumption. -/
theorem IsOptimal.dynamics_below (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (hlt : x < steady P) :
    StrictMono k ∧ (∀ t, k t < steady P) ∧ StrictMono (consumption f δ k) := by
  have hpos : ∀ t, 0 < k t := fun t => (hk.interior P hx t).1
  have hL := hk.tendsto P hx
  obtain ⟨hmono, hanti⟩ := hk.monotone_or_antitone P hx
  have hsucc := hk.succ_eq_policy P hx.le
  have h01 : k 0 < k 1 := by
    by_contra hle
    push Not at hle
    have hlim := le_of_tendsto' hL (fun t => (hanti hle) (Nat.zero_le t))
    rw [hk.1.1] at hlim
    linarith
  have hsm : StrictMono k := by
    apply strictMono_nat_of_lt_succ
    intro t
    induction t with
    | zero => exact h01
    | succ t ih =>
      calc k (t + 1) = policy P (k t) := hsucc t
        _ < policy P (k (t + 1)) := policy_strictMono P (hpos t) (hpos (t + 1)) ih
        _ = k (t + 1 + 1) := (hsucc (t + 1)).symm
  have hbelow : ∀ t, k t < steady P := fun t =>
    (hsm (Nat.lt_succ_self t)).trans_le (ge_of_tendsto hL (eventually_atTop.mpr
      ⟨t + 1, fun s hs => hsm.monotone hs⟩))
  refine ⟨hsm, hbelow, strictMono_nat_of_lt_succ (fun t => ?_)⟩
  have he := hk.euler P hx t
  have hks := steady_spec P
  have hfd : deriv f (steady P) < deriv f (k (t + 1)) :=
    (production_deriv_strictAnti f P.f_conc P.f_diff) (hpos (t + 1)) hks.1 (hbelow (t + 1))
  have hg : 1 < β * (deriv f (k (t + 1)) + (1 - δ)) := by
    have := steady_euler P
    nlinarith [P.β_pos]
  have hcpos := fun t => (hk.interior P hx t).2.2
  by_contra hle
  push Not at hle
  have hu := P.u_prime_anti.antitoneOn (hcpos (t + 1)) (hcpos t) hle
  have hup := P.u_prime_pos _ (hcpos (t + 1))
  nlinarith

/-- O&R §7.1.2.1 (generic discrete-time model): Above the steady state an optimal path falls
strictly toward `k*`, with falling consumption. -/
theorem IsOptimal.dynamics_above (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (hgt : steady P < x) :
    StrictAnti k ∧ (∀ t, steady P < k t) ∧ StrictAnti (consumption f δ k) := by
  have hpos : ∀ t, 0 < k t := fun t => (hk.interior P hx t).1
  have hL := hk.tendsto P hx
  obtain ⟨hmono, hanti⟩ := hk.monotone_or_antitone P hx
  have hsucc := hk.succ_eq_policy P hx.le
  have h10 : k 1 < k 0 := by
    by_contra hle
    push Not at hle
    have hlim := ge_of_tendsto' hL (fun t => (hmono hle) (Nat.zero_le t))
    rw [hk.1.1] at hlim
    linarith
  have hsa : StrictAnti k := by
    apply strictAnti_nat_of_succ_lt
    intro t
    induction t with
    | zero => exact h10
    | succ t ih =>
      calc k (t + 1 + 1) = policy P (k (t + 1)) := hsucc (t + 1)
        _ < policy P (k t) := policy_strictMono P (hpos (t + 1)) (hpos t) ih
        _ = k (t + 1) := (hsucc t).symm
  have habove : ∀ t, steady P < k t := fun t =>
    lt_of_le_of_lt (le_of_tendsto hL (eventually_atTop.mpr
      ⟨t + 1, fun s hs => hsa.antitone hs⟩)) (hsa (Nat.lt_succ_self t))
  refine ⟨hsa, habove, strictAnti_nat_of_succ_lt (fun t => ?_)⟩
  have he := hk.euler P hx t
  have hks := steady_spec P
  have hfd : deriv f (k (t + 1)) < deriv f (steady P) :=
    (production_deriv_strictAnti f P.f_conc P.f_diff) hks.1 (hpos (t + 1)) (habove (t + 1))
  have hg : β * (deriv f (k (t + 1)) + (1 - δ)) < 1 := by
    have := steady_euler P
    nlinarith [P.β_pos]
  have hcpos := fun t => (hk.interior P hx t).2.2
  by_contra hle
  push Not at hle
  have hu := P.u_prime_anti.antitoneOn (hcpos t) (hcpos (t + 1)) hle
  have hup := P.u_prime_pos _ (hcpos (t + 1))
  have hFp := hasDerivAt_resources_pos P (hpos (t + 1))
  nlinarith

/-- O&R §7.1.2.1 (generic discrete-time model): Optimal paths of identical economies never cross. -/
theorem IsOptimal.capital_lt (P : Primitives f u β δ) {x x' : ℝ} (hx : 0 < x)
    {k k' : ℕ → ℝ} (hk : IsOptimal f u β δ x k) (hk' : IsOptimal f u β δ x' k') (hxx : x < x')
    (t : ℕ) : k t < k' t := by
  have hx' : 0 < x' := hx.trans hxx
  induction t with
  | zero => rw [hk.1.1, hk'.1.1]; exact hxx
  | succ t ih =>
    rw [hk.succ_eq_policy P hx.le t, hk'.succ_eq_policy P hx'.le t]
    exact policy_strictMono P (hk.interior P hx t).1 (hk'.interior P hx' t).1 ih

/-- O&R §7.1.2.1 (generic discrete-time model): Consumption as a function of capital. -/
noncomputable def consumptionPolicy (P : Primitives f u β δ) (x : ℝ) : ℝ :=
  resources f δ x - policy P x

/-- O&R §7.1.2.1 (generic discrete-time model): Consumption on an optimal path follows the
consumption policy. -/
theorem IsOptimal.consumption_eq (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) :
    consumption f δ k t = consumptionPolicy P (k t) := by
  simp only [consumption, consumptionPolicy, hk.succ_eq_policy P hx t]

/-- O&R §7.1.2.1 (generic discrete-time model): Consumption is strictly increasing in capital. -/
theorem consumptionPolicy_strictMono (P : Primitives f u β δ) :
    StrictMonoOn (consumptionPolicy P) (Ioi 0) := by
  intro x hx x' hx' hxx
  have hx0 : (0 : ℝ) < x := hx
  have hx0' : (0 : ℝ) < x' := hx'
  set k := optimalPath P hx0.le
  set k' := optimalPath P hx0'.le
  have hk := isOptimal_optimalPath P hx0.le
  have hk' := isOptimal_optimalPath P hx0'.le
  have hc0 : consumption f δ k 0 = consumptionPolicy P x := by
    rw [hk.consumption_eq P hx0.le 0, hk.1.1]
  have hc0' : consumption f δ k' 0 = consumptionPolicy P x' := by
    rw [hk'.consumption_eq P hx0'.le 0, hk'.1.1]
  rw [← hc0, ← hc0']
  by_contra hle
  push Not at hle
  have hcp := fun t => (hk.interior P hx0 t).2.2
  have hcp' := fun t => (hk'.interior P hx0' t).2.2
  have hkp := fun t => (hk.interior P hx0 t).1
  have hkp' := fun t => (hk'.interior P hx0' t).1
  -- the marginal-utility ratio `R t = u'(c'_t)/u'(c_t)` rises strictly
  set R : ℕ → ℝ := fun t => deriv u (consumption f δ k' t) / deriv u (consumption f δ k t)
  have hup := fun t => P.u_prime_pos _ (hcp t)
  have hup' := fun t => P.u_prime_pos _ (hcp' t)
  have hstep : ∀ t, R t < R (t + 1) := by
    intro t
    have he := hk.euler P hx0 t
    have he' := hk'.euler P hx0' t
    have hlt := hk.capital_lt P hx0 hk' hxx (t + 1)
    have hfd : deriv f (k' (t + 1)) < deriv f (k (t + 1)) :=
      (production_deriv_strictAnti f P.f_conc P.f_diff) (hkp (t + 1)) (hkp' (t + 1)) hlt
    have hF := hasDerivAt_resources_pos P (hkp' (t + 1))
    simp only [R]
    rw [div_lt_div_iff₀ (hup t) (hup (t + 1)), he, he']
    have := mul_pos (mul_pos P.β_pos (hup' (t + 1))) (hup (t + 1))
    nlinarith
  have hR0 : 1 ≤ R 0 := by
    simp only [R]
    rw [le_div_iff₀ (hup 0), one_mul]
    exact P.u_prime_anti.antitoneOn (hcp' 0) (hcp 0) hle
  have hR1 : ∀ t, R 1 ≤ R (t + 1) := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ t ih => exact ih.trans (hstep (t + 1)).le
  -- but `R t → 1`
  have hcs := steady_consumption_pos P
  have huc : ContinuousAt (deriv u) (resources f δ (steady P) - steady P) :=
    P.u_prime_cont.continuousAt (Ioi_mem_nhds hcs)
  have hlim : Tendsto R atTop (𝓝 1) := by
    have h := (huc.tendsto.comp (hk'.consumption_tendsto P hx0')).div
      (huc.tendsto.comp (hk.consumption_tendsto P hx0)) (ne_of_gt (P.u_prime_pos _ hcs))
    rw [div_self (ne_of_gt (P.u_prime_pos _ hcs))] at h
    exact h
  have hge : R 1 ≤ 1 := ge_of_tendsto' (hlim.comp (tendsto_add_atTop_nat 1))
    (fun t => hR1 t)
  have := hstep 0
  linarith

/-- O&R §7.1.2.1 (generic discrete-time model): The poorer economy consumes strictly less at every
date. -/
theorem IsOptimal.consumption_lt (P : Primitives f u β δ) {x x' : ℝ} (hx : 0 < x)
    {k k' : ℕ → ℝ} (hk : IsOptimal f u β δ x k) (hk' : IsOptimal f u β δ x' k') (hxx : x < x')
    (t : ℕ) : consumption f δ k t < consumption f δ k' t := by
  have hx' : 0 < x' := hx.trans hxx
  rw [hk.consumption_eq P hx.le t, hk'.consumption_eq P hx'.le t]
  exact consumptionPolicy_strictMono P (hk.interior P hx t).1 (hk'.interior P hx' t).1
    (hk.capital_lt P hx hk' hxx t)

/-- O&R §7.1.2.1 (generic discrete-time model): Absolute convergence of identical economies. -/
theorem IsOptimal.absolute_convergence (P : Primitives f u β δ) {x x' : ℝ} (hx : 0 < x)
    (hx' : 0 < x') {k k' : ℕ → ℝ} (hk : IsOptimal f u β δ x k)
    (hk' : IsOptimal f u β δ x' k') :
    Tendsto (fun t => k' t - k t) atTop (𝓝 0) ∧
      Tendsto (fun t => consumption f δ k' t - consumption f δ k t) atTop (𝓝 0) := by
  constructor
  · simpa only [sub_self] using (hk'.tendsto P hx').sub (hk.tendsto P hx)
  · simpa only [sub_self] using (hk'.consumption_tendsto P hx').sub (hk.consumption_tendsto P hx)


/-! ## Euler equation and transversality: necessary and sufficient -/

/-- **The supporting-hyperplane bound** (sufficiency argument for O&R (20)/(24)): let `k`
be a feasible path with positive capital along which the Euler equation
`u'(c_t) = β u'(c_{t+1}) F'(k_{t+1})` holds, and let `k'` be any feasible path from the same
initial stock, with both consumption paths in a convex set `S` on which `u` is concave.
Then for every horizon `T`,
`∑_{t ≤ T} βᵗ [u(c'_t) - u(c_t)] ≤ -βᵀ u'(c_T) (k'_{T+1} - k_{T+1})`.
No summability of either path is assumed. -/
theorem partial_sum_le_of_euler {S : Set ℝ} (hu : ConcaveOn ℝ S u)
    (hF : ConcaveOn ℝ (Ici 0) (resources f δ)) {x : ℝ} {k k' : ℕ → ℝ}
    (hk : Feasible f δ x k) (hk' : Feasible f δ x k') (hkpos : ∀ t, 0 < k t)
    (hc : ∀ t, consumption f δ k t ∈ S) (hc' : ∀ t, consumption f δ k' t ∈ S)
    {mu R : ℕ → ℝ} (hud : ∀ t, HasDerivAt u (mu t) (consumption f δ k t))
    (hFd : ∀ t, HasDerivAt (resources f δ) (R t) (k t)) (hmu : ∀ t, 0 ≤ mu t) (hβ : 0 ≤ β)
    (heuler : ∀ t, mu t = β * mu (t + 1) * R (t + 1)) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), β ^ t * (u (consumption f δ k' t) - u (consumption f δ k t)) ≤
      -(β ^ T * mu T * (k' (T + 1) - k (T + 1))) := by
  have hk'nn : ∀ t, 0 ≤ k' t := fun t => hk'.nonneg (by rw [← hk.1]; exact (hkpos 0).le) t
  -- one-period bound
  have hstep : ∀ t, u (consumption f δ k' t) - u (consumption f δ k t) ≤
      mu t * (R t * (k' t - k t) - (k' (t + 1) - k (t + 1))) := by
    intro t
    have h1 := concave_support hu (hc t) (hc' t) (hud t)
    have h2 := concave_support hF (mem_Ici.mpr (hkpos t).le) (mem_Ici.mpr (hk'nn t)) (hFd t)
    have h3 := mul_le_mul_of_nonneg_left h2 (hmu t)
    simp only [consumption] at h1 ⊢
    nlinarith
  induction T with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul]
    have h := hstep 0
    rw [hk.1, hk'.1, sub_self, mul_zero, zero_sub] at h
    linarith
  | succ T ih =>
    rw [Finset.sum_range_succ]
    have h := hstep (T + 1)
    have hb := pow_nonneg hβ (T + 1)
    have h' := mul_le_mul_of_nonneg_left h hb
    have he := heuler T
    have : β ^ (T + 1) * (mu (T + 1) * (R (T + 1) * (k' (T + 1) - k (T + 1)))) =
        β ^ T * mu T * (k' (T + 1) - k (T + 1)) := by
      rw [he, pow_succ]; ring
    nlinarith

/-- Concavity of gross resources `F(k) = f(k) + (1 - δ) k` (O&R p. 441). -/
theorem Primitives.resources_concave (P : Primitives f u β δ) :
    ConcaveOn ℝ (Ici 0) (resources f δ) :=
  P.f_conc.concaveOn.add (LinearMap.concaveOn (LinearMap.lsmul ℝ ℝ (1 - δ)) (convex_Ici 0))

/-- **Sufficiency of the Euler equation and transversality** (O&R (20)/(24) with the
transversality condition the book leaves implicit): in the generic model, any feasible
path from `x` with positive capital and consumption that satisfies the Euler equation
and `βᵗ u'(c_t) k_{t+1} → 0` is optimal. -/
theorem isOptimal_of_euler_tvc (P : Primitives f u β δ) {x : ℝ} {k : ℕ → ℝ}
    (hk : Feasible f δ x k) (hkpos : ∀ t, 0 < k t) (hcpos : ∀ t, 0 < consumption f δ k t)
    (heuler : ∀ t, deriv u (consumption f δ k t) =
      β * deriv u (consumption f δ k (t + 1)) * (deriv f (k (t + 1)) + (1 - δ)))
    (htvc : Tendsto (fun t => β ^ t * deriv u (consumption f δ k t) * k (t + 1)) atTop (𝓝 0)) :
    IsOptimal f u β δ x k := by
  refine ⟨hk, fun k' hk' => ?_⟩
  have hx : 0 ≤ x := by rw [← hk.1]; exact (hkpos 0).le
  have hbound := partial_sum_le_of_euler (S := Ici 0) P.u_conc.concaveOn P.resources_concave hk
    hk' hkpos (fun t => mem_Ici.mpr (hcpos t).le)
    (fun t => (hk'.consumption_mem P hx t).1)
    (fun t => (P.u_diff _ (hcpos t)).hasDerivAt) (fun t => hasDerivAt_resources P (hkpos t))
    (fun t => (P.u_prime_pos _ (hcpos t)).le) P.β_pos.le heuler
  have hs := (hk'.summable P hx).sub (hk.summable P hx)
  have hlim := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hle : ∀ T, ∑ t ∈ Finset.range (T + 1),
      (β ^ t * u (consumption f δ k' t) - β ^ t * u (consumption f δ k t)) ≤
      β ^ T * deriv u (consumption f δ k T) * k (T + 1) := by
    intro T
    have h := hbound T
    have hk'1 : 0 ≤ k' (T + 1) := (hk'.2 T).1
    have hm := mul_nonneg (mul_nonneg (pow_nonneg P.β_pos.le T)
      (P.u_prime_pos _ (hcpos T)).le) hk'1
    simp only [mul_sub] at h ⊢
    linarith
  have := le_of_tendsto_of_tendsto hlim htvc (Eventually.of_forall hle)
  rw [welfare, welfare]
  have e := (hk'.summable P hx).tsum_sub (hk.summable P hx)
  linarith

/-- **The transversality condition is necessary** (derived, not assumed): along the
optimal path from `x > 0`, `βᵗ u'(c_t) k_{t+1} → 0`, because `c_t` and `k_t` converge to
the interior steady state. -/
theorem IsOptimal.tvc (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) :
    Tendsto (fun t => β ^ t * deriv u (consumption f δ k t) * k (t + 1)) atTop (𝓝 0) := by
  have hcs := steady_consumption_pos P
  have huc : ContinuousAt (deriv u) (resources f δ (steady P) - steady P) :=
    P.u_prime_cont.continuousAt (Ioi_mem_nhds hcs)
  have h1 := huc.tendsto.comp (hk.consumption_tendsto P hx)
  have h2 := (hk.tendsto P hx).comp (tendsto_add_atTop_nat 1)
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one P.β_pos.le P.β_lt_one
  have := (h0.mul h1).mul h2
  rw [zero_mul, zero_mul] at this
  exact this

/-- **Euler equation plus transversality characterise the optimum** (O&R pp. 441–442,
Fig. 7.4 made precise): a feasible path from `x > 0` is optimal if and only if capital and
consumption stay positive, the Euler equation holds at every date, and the transversality
condition holds. -/
theorem isOptimal_iff_euler_tvc (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x)
    {k : ℕ → ℝ} (hk : Feasible f δ x k) :
    IsOptimal f u β δ x k ↔ (∀ t, 0 < k t ∧ 0 < consumption f δ k t) ∧
      (∀ t, deriv u (consumption f δ k t) =
        β * deriv u (consumption f δ k (t + 1)) * (deriv f (k (t + 1)) + (1 - δ))) ∧
      Tendsto (fun t => β ^ t * deriv u (consumption f δ k t) * k (t + 1)) atTop (𝓝 0) := by
  constructor
  · intro hopt
    exact ⟨fun t => ⟨(hopt.interior P hx t).1, (hopt.interior P hx t).2.2⟩,
      hopt.euler P hx, hopt.tvc P hx⟩
  · rintro ⟨hpos, he, htvc⟩
    exact isOptimal_of_euler_tvc P hk (fun t => (hpos t).1) (fun t => (hpos t).2) he htvc

/-- **The saddle path is unique** (O&R p. 442: "a unique optimal consumption level"):
two feasible Euler paths from the same `x > 0` that both satisfy transversality coincide,
and both equal the optimal path. -/
theorem euler_tvc_path_unique (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : Feasible f δ x k) (hpos : ∀ t, 0 < k t ∧ 0 < consumption f δ k t)
    (he : ∀ t, deriv u (consumption f δ k t) =
      β * deriv u (consumption f δ k (t + 1)) * (deriv f (k (t + 1)) + (1 - δ)))
    (htvc : Tendsto (fun t => β ^ t * deriv u (consumption f δ k t) * k (t + 1)) atTop (𝓝 0)) :
    k = optimalPath P hx.le :=
  let h := (isOptimal_iff_euler_tvc P hx hk).mpr ⟨hpos, he, htvc⟩
  optimal_unique P hx.le h.1 h.2

/-- **The unique optimal initial consumption** (O&R p. 442): from every `x > 0` initial
consumption on the optimal path is `c(x) = F(x) - g(x)`, strictly increasing in `x`; any
other initial consumption either violates feasibility, the Euler equation or transversality
at some later date. -/
theorem unique_initial_consumption (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x)
    {k : ℕ → ℝ} (hk : IsOptimal f u β δ x k) :
    consumption f δ k 0 = consumptionPolicy P x ∧ 0 < consumptionPolicy P x := by
  have h := hk.consumption_eq P hx.le 0
  rw [hk.1.1] at h
  exact ⟨h, h ▸ (hk.interior P hx 0).2.2⟩

/-- The steady state is optimal from itself: the optimal path from `k*` is constant
(O&R Fig. 7.4; used for Fig. 7.6). -/
theorem optimalPath_steady (P : Primitives f u β δ) :
    optimalPath P (steady_spec P).1.le = fun _ => steady P := by
  obtain ⟨hks, -⟩ := steady_spec P
  have hcs := steady_consumption_pos P
  have hfeas : Feasible f δ (steady P) (fun _ => steady P) :=
    ⟨rfl, fun _ => ⟨hks.le, by linarith⟩⟩
  have hc : ∀ t, consumption f δ (fun _ => steady P) t = resources f δ (steady P) - steady P :=
    fun _ => rfl
  refine (euler_tvc_path_unique P hks hfeas (fun t => ⟨hks, by rw [hc]; exact hcs⟩)
    (fun t => ?_) ?_).symm
  · rw [hc, hc]
    have := steady_euler P
    linear_combination (-(deriv u (resources f δ (steady P) - steady P))) * this
  · simp only [hc]
    have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one P.β_pos.le P.β_lt_one
    have := (h0.mul_const (deriv u (resources f δ (steady P) - steady P))).mul_const (steady P)
    rw [zero_mul, zero_mul] at this
    exact this

/-! ## The book's model in efficiency units (O&R pp. 441–442) -/

/-- Technology hypotheses for the book's model (O&R p. 441, "constant-returns production
function"): a neoclassical intensive form with continuous marginal product and the Inada
conditions, which the book leaves implicit. -/
structure Technology (f : ℝ → ℝ) : Prop where
  neo : SolowModel.Neoclassical f
  prime_cont : ContinuousOn (deriv f) (Ioi 0)
  inada0 : Tendsto (deriv f) (𝓝[>] 0) atTop
  inadaTop : Tendsto (deriv f) atTop (𝓝 0)

/-- Period utility bounded below (O&R (18)): continuous on `[0, ∞)`, strictly concave,
differentiable with positive continuous marginal utility and `u'(0+) = ∞`. Covers the
isoelastic class (21) with `σ > 1`; the unbounded case (`σ ≤ 1`, log) is treated in the
`LogUtility` namespace. -/
structure Preferences (u : ℝ → ℝ) : Prop where
  cont : ContinuousOn u (Ici 0)
  conc : StrictConcaveOn ℝ (Ici 0) u
  diff : ∀ c, 0 < c → DifferentiableAt ℝ u c
  prime_pos : ∀ c, 0 < c → 0 < deriv u c
  prime_cont : ContinuousOn (deriv u) (Ioi 0)
  inada0 : Tendsto (deriv u) (𝓝[>] 0) atTop

/-- The technology seen by the generic model: `f(k)/(1 + z)` (O&R (8′)). -/
noncomputable def effF (f : ℝ → ℝ) (z : ℝ) : ℝ → ℝ := fun k => f k / (1 + z)

/-- The utility seen by the generic model: `u((1 + z) c̃)` (O&R (8′)). -/
noncomputable def effU (u : ℝ → ℝ) (z : ℝ) : ℝ → ℝ := fun c => u ((1 + z) * c)

/-- The depreciation rate seen by the generic model: `(z + δ)/(1 + z)` (O&R (8′)). -/
noncomputable def effDelta (z δ : ℝ) : ℝ := (z + δ) / (1 + z)

/-- Consumption per efficiency worker in the book's accounting, (8′) (O&R p. 442, with
depreciation `δ`; the book sets `δ = 0`): `c_t = f(k_t) + (1 - δ) k_t - (1 + z) k_{t+1}`. -/
def bookConsumption (f : ℝ → ℝ) (δ z : ℝ) (k : ℕ → ℝ) (t : ℕ) : ℝ :=
  f (k t) + (1 - δ) * k t - (1 + z) * k (t + 1)

/-- Eq. (8′) (O&R p. 442) is the difference form of the book's resource constraint:
`k_{t+1} - k_t = [f(k_t) - c_t - z k_t]/(1 + z)` when `δ = 0`. -/
theorem bookConsumption_diff (f : ℝ → ℝ) {z : ℝ} (hz : 0 < 1 + z) (k : ℕ → ℝ) (t : ℕ) :
    k (t + 1) - k t = (f (k t) - bookConsumption f 0 z k t - z * k t) / (1 + z) := by
  unfold bookConsumption
  field_simp
  ring

/-- Gross resources of the transformed model (O&R (8′)). -/
theorem resources_eff (f : ℝ → ℝ) {z : ℝ} (δ : ℝ) (hz : 0 < 1 + z) (k : ℝ) :
    resources (effF f z) (effDelta z δ) k = (f k + (1 - δ) * k) / (1 + z) := by
  unfold resources effF effDelta
  field_simp
  ring

/-- Consumption of the transformed model is book consumption divided by `1 + z`. -/
theorem consumption_eff (f : ℝ → ℝ) {z : ℝ} (δ : ℝ) (hz : 0 < 1 + z) (k : ℕ → ℝ) (t : ℕ) :
    consumption (effF f z) (effDelta z δ) k t = bookConsumption f δ z k t / (1 + z) := by
  unfold consumption bookConsumption
  rw [resources_eff f δ hz]
  field_simp

/-- Transformed utility of transformed consumption is utility of book consumption. -/
theorem effU_consumption (f u : ℝ → ℝ) {z : ℝ} (δ : ℝ) (hz : 0 < 1 + z) (k : ℕ → ℝ) (t : ℕ) :
    effU u z (consumption (effF f z) (effDelta z δ) k t) = u (bookConsumption f δ z k t) := by
  unfold effU
  rw [consumption_eff f δ hz]
  congr 1
  field_simp

/-- Welfare of the transformed model is the book's detrended welfare
`∑ β̂ᵗ u(c_t)` (O&R (18) after detrending). -/
theorem welfare_eff (f u : ℝ → ℝ) {z : ℝ} (β δ : ℝ) (hz : 0 < 1 + z) (k : ℕ → ℝ) :
    welfare (effF f z) (effU u z) β (effDelta z δ) k =
      ∑' t, β ^ t * u (bookConsumption f δ z k t) := by
  unfold welfare
  simp only [effU_consumption f u δ hz]

/-- Feasibility in the transformed model is feasibility in the book's accounting:
nonnegative capital and consumption. -/
theorem feasible_eff_iff (f : ℝ → ℝ) {z : ℝ} (δ : ℝ) (hz : 0 < 1 + z) (x : ℝ) (k : ℕ → ℝ) :
    Feasible (effF f z) (effDelta z δ) x k ↔
      k 0 = x ∧ ∀ t, 0 ≤ k (t + 1) ∧ 0 ≤ bookConsumption f δ z k t := by
  unfold Feasible
  refine and_congr Iff.rfl (forall_congr' fun t => and_congr Iff.rfl ?_)
  rw [resources_eff f δ hz, le_div_iff₀ hz]
  unfold bookConsumption
  constructor <;> intro h <;> linarith

/-- The undepreciated share in the transformed model: `1 - (z+δ)/(1+z) = (1-δ)/(1+z)`. -/
theorem one_sub_effDelta {z : ℝ} (δ : ℝ) (hz : 0 < 1 + z) :
    1 - effDelta z δ = (1 - δ) / (1 + z) := by
  unfold effDelta; field_simp; ring

/-- Marginal product in the transformed model. -/
theorem deriv_effF (f : ℝ → ℝ) (z k : ℝ) : deriv (effF f z) k = deriv f k / (1 + z) := by
  unfold effF
  exact deriv_div_const _

/-- Marginal utility in the transformed model: `(1 + z) u'((1 + z) c)`. -/
theorem deriv_effU (u : ℝ → ℝ) (z c : ℝ) :
    deriv (effU u z) c = (1 + z) * deriv u ((1 + z) * c) := by
  unfold effU
  exact deriv_comp_mul_left (1 + z) u c

/-- **The book's model is an instance of the generic model** (O&R (8′), (18)): with
`0 < β̂ < 1`, `δ ≤ 1`, `z + δ > 0` and `1 + z > 0`, the transformed primitives satisfy all
hypotheses of the generic theory. -/
theorem toPrimitives (hT : Technology f) (hU : Preferences u) {β z : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hδ1 : δ ≤ 1) (hzd : 0 ≤ z + δ) (hz : 0 < 1 + z) :
    Primitives (effF f z) (effU u z) β (effDelta z δ) where
  β_pos := hβ
  β_lt_one := hβ1
  δ_nonneg := div_nonneg hzd hz.le
  δ_le_one := by unfold effDelta; rw [div_le_one hz]; linarith
  f_cont := hT.neo.cont.div_const _
  f_zero := by simp [effF, hT.neo.zero]
  f_conc := ⟨convex_Ici 0, fun x hx y hy hne a b ha hb hab => by
    have h := hT.neo.strictConcave.2 hx hy hne ha hb hab
    simp only [smul_eq_mul, effF] at h ⊢
    have := div_lt_div_of_pos_right h hz
    rw [add_div] at this
    field_simp at this ⊢
    linarith⟩
  f_diff := fun k hk => (hT.neo.diff k hk).div_const _
  f_prime_pos := fun k hk => by rw [deriv_effF]; exact div_pos (hT.neo.deriv_pos hk) hz
  f_prime_cont := by
    rw [show deriv (effF f z) = fun k => deriv f k / (1 + z) from funext (deriv_effF f z)]
    exact hT.prime_cont.div_const _
  f_inada0 := by
    rw [show deriv (effF f z) = fun k => deriv f k / (1 + z) from funext (deriv_effF f z)]
    exact hT.inada0.atTop_div_const hz
  f_inadaTop := by
    rw [show deriv (effF f z) = fun k => deriv f k / (1 + z) from funext (deriv_effF f z)]
    simpa using hT.inadaTop.div_const (1 + z)
  u_cont := hU.cont.comp (continuousOn_const.mul continuousOn_id)
    (fun c hc => mem_Ici.mpr (mul_nonneg hz.le (mem_Ici.mp hc)))
  u_conc := ⟨convex_Ici 0, fun x hx y hy hne a b ha hb hab => by
    have hx' : (1 + z) * x ∈ Ici (0 : ℝ) := mem_Ici.mpr (mul_nonneg hz.le (mem_Ici.mp hx))
    have hy' : (1 + z) * y ∈ Ici (0 : ℝ) := mem_Ici.mpr (mul_nonneg hz.le (mem_Ici.mp hy))
    have hne' : (1 + z) * x ≠ (1 + z) * y := fun h => hne (mul_left_cancel₀ (ne_of_gt hz) h)
    have h := hU.conc.2 hx' hy' hne' ha hb hab
    simp only [smul_eq_mul, effU] at h ⊢
    convert h using 2
    ring⟩
  u_diff := fun c hc => by
    unfold effU
    exact (hU.diff _ (mul_pos hz hc)).comp c ((differentiableAt_id).const_mul _)
  u_prime_pos := fun c hc => by
    rw [deriv_effU]; exact mul_pos hz (hU.prime_pos _ (mul_pos hz hc))
  u_prime_cont := by
    rw [show deriv (effU u z) = fun c => (1 + z) * deriv u ((1 + z) * c) from
      funext (deriv_effU u z)]
    exact continuousOn_const.mul (hU.prime_cont.comp (continuousOn_const.mul continuousOn_id)
      (fun c hc => mem_Ioi.mpr (mul_pos hz (mem_Ioi.mp hc))))
  u_inada0 := by
    rw [show deriv (effU u z) = fun c => (1 + z) * deriv u ((1 + z) * c) from
      funext (deriv_effU u z)]
    have hlin : Tendsto (fun c : ℝ => (1 + z) * c) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have h0 : Tendsto (fun c : ℝ => (1 + z) * c) (𝓝 0) (𝓝 ((1 + z) * 0)) :=
          ((continuous_const.mul continuous_id).tendsto 0)
        rw [mul_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with c hc
        exact mul_pos hz hc
    exact (hU.inada0.comp hlin).const_mul_atTop hz

/-- The set of feasible paths in the book's accounting (O&R (8′)). -/
def BookFeasible (f : ℝ → ℝ) (δ z x : ℝ) (k : ℕ → ℝ) : Prop :=
  k 0 = x ∧ ∀ t, 0 ≤ k (t + 1) ∧ 0 ≤ bookConsumption f δ z k t

/-- Detrended welfare `∑ β̂ᵗ u(c_t)` of a path (O&R (18) after detrending). -/
noncomputable def bookWelfare (f u : ℝ → ℝ) (β δ z : ℝ) (k : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * u (bookConsumption f δ z k t)

/-- **Existence and uniqueness of the optimal path** (O&R p. 442, Fig. 7.4: "for any
initial level of `k^E` there is a unique optimal consumption level"): with a genuine
infinite horizon, from every `k₀ ≥ 0` there is exactly one feasible path maximising
detrended welfare, and the welfare series converges along every feasible path. -/
theorem book_optimal_existsUnique (hT : Technology f) (hU : Preferences u) {β z : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hδ1 : δ ≤ 1) (hzd : 0 ≤ z + δ) (hz : 0 < 1 + z) {x : ℝ}
    (hx : 0 ≤ x) :
    ∃! k, BookFeasible f δ z x k ∧
      ∀ k', BookFeasible f δ z x k' → bookWelfare f u β δ z k' ≤ bookWelfare f u β δ z k := by
  have P := toPrimitives hT hU hβ hβ1 hδ1 hzd hz
  have hiff : ∀ k, BookFeasible f δ z x k ↔ Feasible (effF f z) (effDelta z δ) x k :=
    fun k => (feasible_eff_iff f δ hz x k).symm
  have hW : ∀ k, bookWelfare f u β δ z k = welfare (effF f z) (effU u z) β (effDelta z δ) k :=
    fun k => (welfare_eff f u β δ hz k).symm
  obtain ⟨hk, hopt⟩ := optimalPath_spec P hx
  refine ⟨optimalPath P hx, ⟨(hiff _).mpr hk, fun k' hk' => ?_⟩, fun k ⟨hk1, hk2⟩ => ?_⟩
  · rw [hW, hW]; exact hopt k' ((hiff k').mp hk')
  · exact optimal_unique P hx ((hiff k).mp hk1) (fun k' hk' => by
      rw [← hW, ← hW]; exact hk2 k' ((hiff k').mpr hk'))

/-- Optimality in the book's accounting is optimality in the transformed model. -/
theorem book_isOptimal_iff (u : ℝ → ℝ) {β z : ℝ} (hz : 0 < 1 + z) {x : ℝ} {k : ℕ → ℝ} :
    (BookFeasible f δ z x k ∧
      ∀ k', BookFeasible f δ z x k' → bookWelfare f u β δ z k' ≤ bookWelfare f u β δ z k) ↔
      IsOptimal (effF f z) (effU u z) β (effDelta z δ) x k := by
  unfold IsOptimal BookFeasible bookWelfare
  simp only [← feasible_eff_iff f δ hz, ← welfare_eff f u β δ hz]

/-- **The Euler equation in efficiency units** (O&R (24), general utility, with
depreciation): along the optimal path from `k₀ > 0`,
`u'(c_t) = β̂ u'(c_{t+1}) [1 + f'(k_{t+1}) - δ]/(1 + z)`. -/
theorem book_euler (hT : Technology f) (hU : Preferences u) {β z : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hδ1 : δ ≤ 1) (hzd : 0 ≤ z + δ) (hz : 0 < 1 + z) {x : ℝ} (hx : 0 < x)
    {k : ℕ → ℝ} (hk : IsOptimal (effF f z) (effU u z) β (effDelta z δ) x k) (t : ℕ) :
    0 < bookConsumption f δ z k t ∧
      deriv u (bookConsumption f δ z k t) =
        β * deriv u (bookConsumption f δ z k (t + 1)) * (1 + deriv f (k (t + 1)) - δ) /
          (1 + z) := by
  have P := toPrimitives hT hU hβ hβ1 hδ1 hzd hz
  have he := hk.euler P hx t
  have hc := (hk.interior P hx t).2.2
  simp only [consumption_eff f δ hz] at he hc
  rw [deriv_effU, deriv_effU, deriv_effF] at he
  have e1 : (1 + z) * (bookConsumption f δ z k t / (1 + z)) = bookConsumption f δ z k t := by
    field_simp
  have e2 : (1 + z) * (bookConsumption f δ z k (t + 1) / (1 + z)) =
      bookConsumption f δ z k (t + 1) := by field_simp
  rw [e1, e2] at he
  refine ⟨(div_pos_iff_of_pos_right hz).mp hc, ?_⟩
  rw [one_sub_effDelta δ hz] at he
  field_simp at he ⊢
  nlinarith [he]

/-- **The steady state (25), general form** (O&R p. 442): the generic steady state of the
transformed model is the unique `k̄ > 0` with `1 + f'(k̄) - δ = (1 + z)/β̂`. -/
theorem book_steady_spec (hT : Technology f) {β z : ℝ} (hβ : 0 < β) (hz : 0 < 1 + z)
    {g : ℝ → ℝ} (P : Primitives (effF f z) g β (effDelta z δ)) :
    0 < steady P ∧ 1 + deriv f (steady P) - δ = (1 + z) / β ∧
      ∀ k, 0 < k → 1 + deriv f k - δ = (1 + z) / β → k = steady P := by
  obtain ⟨hks, hd⟩ := steady_spec P
  rw [deriv_effF, one_sub_effDelta δ hz] at hd
  have hd' : 1 + deriv f (steady P) - δ = (1 + z) / β := by
    rw [eq_div_iff (ne_of_gt hβ)]
    field_simp at hd
    linear_combination hd
  refine ⟨hks, hd', fun k hk hk' => ?_⟩
  have := hT.neo.deriv_strictAnti.injOn hk hks (by linarith)
  exact this

/-- **Monotone convergence to the steady state** (O&R Fig. 7.4, the saddle path): the
optimal path from `k₀ > 0` is monotone, converges to `k̄` of (25), never crosses it, and
book consumption converges to `c̄ = f(k̄) - (z + δ) k̄` (eq. (26)), moving monotonically in
the same direction as capital. -/
theorem book_convergence {β z : ℝ} (hz : 0 < 1 + z)
    (P : Primitives (effF f z) (effU u z) β (effDelta z δ)) {x : ℝ} (hx : 0 < x)
    {k : ℕ → ℝ} (hk : IsOptimal (effF f z) (effU u z) β (effDelta z δ) x k) :
    Tendsto k atTop (𝓝 (steady P)) ∧
      Tendsto (bookConsumption f δ z k) atTop
        (𝓝 (f (steady P) - (z + δ) * steady P)) ∧
      (x < steady P → StrictMono k ∧ (∀ t, k t < steady P) ∧
        StrictMono (bookConsumption f δ z k)) ∧
      (steady P < x → StrictAnti k ∧ (∀ t, steady P < k t) ∧
        StrictAnti (bookConsumption f δ z k)) := by
  have hce : ∀ t, bookConsumption f δ z k t = (1 + z) * consumption (effF f z)
      (effDelta z δ) k t := fun t => by rw [consumption_eff f δ hz]; field_simp
  have hcfun : bookConsumption f δ z k = fun t => (1 + z) * consumption (effF f z)
      (effDelta z δ) k t := funext hce
  refine ⟨hk.tendsto P hx, ?_, fun hlt => ?_, fun hgt => ?_⟩
  · rw [hcfun]
    have h := (hk.consumption_tendsto P hx).const_mul (1 + z)
    convert h using 2
    rw [resources_eff f δ hz]
    field_simp
    ring
  · obtain ⟨h1, h2, h3⟩ := hk.dynamics_below P hx hlt
    refine ⟨h1, h2, ?_⟩
    rw [hcfun]
    exact fun a b hab => mul_lt_mul_of_pos_left (h3 hab) hz
  · obtain ⟨h1, h2, h3⟩ := hk.dynamics_above P hx hgt
    refine ⟨h1, h2, ?_⟩
    rw [hcfun]
    exact fun a b hab => mul_lt_mul_of_pos_left (h3 hab) hz

/-- **No growth and no depreciation** (`n = g = δ = 0`, so `z + δ = 0`; O&R p. 441 with
`g = n = 0`, and Appendix 7A): feasible capital is then unbounded (the path consuming nothing
grows for ever), yet the optimal path still exists, is unique, and converges to the steady
state `f'(k̄) = 1/β - 1`, with consumption converging to `f(k̄)`. -/
theorem book_no_growth (hT : Technology f) (hU : Preferences u) {β : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) {x : ℝ} (hx : 0 < x) :
    (∃! k, BookFeasible f 0 0 x k ∧
      ∀ k', BookFeasible f 0 0 x k' → bookWelfare f u β 0 0 k' ≤ bookWelfare f u β 0 0 k) ∧
    ∀ k, IsOptimal (effF f 0) (effU u 0) β (effDelta 0 0) x k →
      ∃ kbar, 0 < kbar ∧ deriv f kbar = 1 / β - 1 ∧ Tendsto k atTop (𝓝 kbar) ∧
        Tendsto (bookConsumption f 0 0 k) atTop (𝓝 (f kbar)) := by
  have hz : (0 : ℝ) < 1 + 0 := by norm_num
  have P := toPrimitives hT hU hβ hβ1 (δ := 0) (by norm_num) (by norm_num) hz
  refine ⟨book_optimal_existsUnique hT hU hβ hβ1 (by norm_num) (by norm_num) hz hx.le,
    fun k hk => ?_⟩
  obtain ⟨hks, hss, -⟩ := book_steady_spec hT hβ hz P
  obtain ⟨h1, h2, -, -⟩ := book_convergence hz P hx hk
  refine ⟨steady P, hks, by field_simp at hss ⊢; linarith, h1, by simpa using h2⟩

/-- Without depreciation or growth the feasible set is unbounded (flag: the compactness route
of the `δ > 0` case needs the growing bounds of `bound`): the path that consumes nothing,
`k_{t+1} = k_t + f(k_t)`, is feasible and unbounded. -/
theorem unbounded_without_depreciation (hT : Technology f) {x : ℝ} (hx : 0 < x) :
    ∃ k : ℕ → ℝ, BookFeasible f 0 0 x k ∧ ¬ BddAbove (Set.range k) := by
  let k : ℕ → ℝ := fun t => (fun y => y + f y)^[t] x
  have hk : ∀ t, k (t + 1) = k t + f (k t) := fun t => Function.iterate_succ_apply' _ t x
  have hpos : ∀ t, 0 < k t := by
    intro t; induction t with
    | zero => exact hx
    | succ t ih => rw [hk t]; linarith [hT.neo.pos ih]
  have hinc : StrictMono k := strictMono_nat_of_lt_succ fun t => by
    rw [hk t]; linarith [hT.neo.pos (hpos t)]
  refine ⟨k, ⟨rfl, fun t => ⟨(hpos _).le, ?_⟩⟩, fun hb => ?_⟩
  · simp only [bookConsumption, hk t]; norm_num; linarith
  · have hL := tendsto_atTop_ciSup hinc.monotone hb
    set L := ⨆ t, k t
    have hLpos : 0 < L := lt_of_lt_of_le hx (le_ciSup hb 0)
    have hfc : ContinuousAt f L := (hT.neo.diff L hLpos).continuousAt
    have h1 : Tendsto (fun t => k (t + 1)) atTop (𝓝 (L + f L)) :=
      (hL.add (hfc.tendsto.comp hL)).congr (fun t => (hk t).symm)
    have h2 : Tendsto (fun t => k (t + 1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)
    have := tendsto_nhds_unique h1 h2
    linarith [hT.neo.pos hLpos]

/-- **Dynamic efficiency** (O&R p. 442): with `β̂ < 1` the steady state lies strictly below
the golden-rule stock defined by `f'(k*) = z + δ`. -/
theorem steady_lt_golden_rule (hT : Technology f) {β z kbar kgr : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hz : 0 < 1 + z) (hk : 0 < kbar) (hkg : 0 < kgr)
    (hss : 1 + deriv f kbar - δ = (1 + z) / β) (hgr : deriv f kgr = z + δ) : kbar < kgr := by
  have h1 : 1 + z < (1 + z) / β := by rw [lt_div_iff₀ hβ]; nlinarith
  by_contra hle
  push Not at hle
  have := hT.neo.deriv_strictAnti.antitoneOn hkg hk hle
  linarith

/-! ### Isoelastic utility (O&R (21)–(26)) -/

/-- Isoelastic utility (21) written with `θ = 1 - 1/σ`: `u(c) = c^θ/θ`. -/
noncomputable def crra (θ c : ℝ) : ℝ := c ^ θ / θ

/-- Marginal utility of (21): `u'(c) = c^{θ-1} = c^{-1/σ}`. -/
theorem crra_hasDerivAt {θ c : ℝ} (hθ : θ ≠ 0) (hc : 0 < c) :
    HasDerivAt (crra θ) (c ^ (θ - 1)) c := by
  have h := (Real.hasDerivAt_rpow_const (p := θ) (Or.inl (ne_of_gt hc))).div_const θ
  unfold crra
  convert h using 1
  field_simp

/-- **Isoelastic utility with `σ > 1` satisfies the hypotheses** (O&R (21)): for
`0 < θ = 1 - 1/σ < 1`, `c^θ/θ` is continuous on `[0, ∞)`, strictly concave, with
positive continuous marginal utility and `u'(0+) = ∞`. -/
theorem crra_preferences {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) : Preferences (crra θ) where
  cont := (Real.continuous_rpow_const hθ.le).continuousOn.div_const _
  conc := by
    refine ⟨convex_Ici 0, fun x hx y hy hne a b ha hb hab => ?_⟩
    have h := (Real.strictConcaveOn_rpow hθ hθ1).2 hx hy hne ha hb hab
    simp only [smul_eq_mul, crra] at h ⊢
    have := div_lt_div_of_pos_right h hθ
    rw [add_div] at this
    field_simp at this ⊢
    linarith
  diff := fun c hc => (crra_hasDerivAt (ne_of_gt hθ) hc).differentiableAt
  prime_pos := fun c hc => by
    rw [(crra_hasDerivAt (ne_of_gt hθ) hc).deriv]; exact Real.rpow_pos_of_pos hc _
  prime_cont := by
    refine ContinuousOn.congr (f := fun c => c ^ (θ - 1)) ?_ ?_
    · exact fun c hc => (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hc))).continuousWithinAt
    · intro c hc; exact (crra_hasDerivAt (ne_of_gt hθ) hc).deriv
  inada0 := by
    refine (tendsto_rpow_neg_nhdsGT_zero (by linarith : θ - 1 < 0)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact (crra_hasDerivAt (ne_of_gt hθ) hc).deriv.symm

/-- **The per-capita Euler equation (22) and its detrended form (24)** (O&R pp. 441–442):
for isoelastic utility with `θ = 1 - 1/σ`, `σ > 0`, the Euler equation of the transformed
model with `β̂ = β(1 + n)(1 + g)^θ`, `1 + z = (1 + n)(1 + g)` and `δ = 0` is equivalent to
`c_{t+1}/c_t = β^σ [1 + f'(k_{t+1})]^σ/(1 + g)`. -/
theorem crra_euler_eq24 {σ β n g c0 c1 fp : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hn : 0 < 1 + n)
    (hg : 0 < 1 + g) (hc0 : 0 < c0) (hc1 : 0 < c1) (hfp : 0 < 1 + fp)
    (he : c0 ^ (1 - 1 / σ - 1) = β * (1 + n) * (1 + g) ^ (1 - 1 / σ) * c1 ^ (1 - 1 / σ - 1) *
      (1 + fp - 0) / ((1 + n) * (1 + g))) :
    c1 / c0 = β ^ σ * (1 + fp) ^ σ / (1 + g) := by
  have hq : 0 < c1 / c0 := div_pos hc1 hc0
  have e1 : (1 : ℝ) - 1 / σ - 1 = -(1 / σ) := by ring
  rw [e1] at he
  have hg' : (1 + g) ^ (1 - 1 / σ) = (1 + g) * (1 + g) ^ (-(1 / σ)) := by
    rw [show (1 : ℝ) - 1 / σ = 1 + -(1 / σ) by ring, Real.rpow_add hg, Real.rpow_one]
  rw [hg'] at he
  have hc1' : c1 ^ (-(1 / σ)) = (c1 / c0) ^ (-(1 / σ)) * c0 ^ (-(1 / σ)) := by
    rw [Real.div_rpow hc1.le hc0.le]
    have : 0 < c0 ^ (-(1 / σ)) := Real.rpow_pos_of_pos hc0 _
    field_simp
  rw [hc1'] at he
  have hc0p : 0 < c0 ^ (-(1 / σ)) := Real.rpow_pos_of_pos hc0 _
  -- `1 = β (1+g)^{-1/σ} (1 + f') q^{-1/σ}`
  have key : (c1 / c0) ^ (1 / σ) = β * (1 + g) ^ (-(1 / σ)) * (1 + fp) := by
    have hqn : (c1 / c0) ^ (-(1 / σ)) = ((c1 / c0) ^ (1 / σ))⁻¹ := Real.rpow_neg hq.le _
    rw [hqn] at he
    have hqp : 0 < (c1 / c0) ^ (1 / σ) := Real.rpow_pos_of_pos hq _
    field_simp at he
    nlinarith [he]
  have hq' : c1 / c0 = ((c1 / c0) ^ (1 / σ)) ^ σ := by
    rw [← Real.rpow_mul hq.le, one_div_mul_cancel (ne_of_gt hσ), Real.rpow_one]
  rw [hq', key, Real.mul_rpow (by positivity) hfp.le, Real.mul_rpow hβ.le (by positivity),
    ← Real.rpow_mul hg.le, show -(1 / σ) * σ = -1 by field_simp, Real.rpow_neg_one]
  field_simp

/-- **Eq. (25)** (O&R p. 442): with `β̂ = β(1 + n)(1 + g)^{1-1/σ}`, `1 + z = (1+n)(1+g)` and
`δ = 0`, the steady-state condition `1 + f'(k̄) = (1 + z)/β̂` reads
`f'(k̄) = (1 + g)^{1/σ}/β - 1`, which does not involve `n`. -/
theorem steady_eq25 {σ β n g : ℝ} (hβ : 0 < β) (hn : 0 < 1 + n) (hg : 0 < 1 + g) :
    (1 + n) * (1 + g) / (β * (1 + n) * (1 + g) ^ (1 - 1 / σ)) = (1 + g) ^ (1 / σ) / β := by
  rw [Real.rpow_sub hg, Real.rpow_one]
  have : 0 < (1 + g) ^ (1 / σ) := Real.rpow_pos_of_pos hg _
  field_simp

/-- **Eq. (28)** (O&R p. 445): under the alternative dynasty weights (27) the detrended
discount factor is `β(1 + g)^{1-1/σ}`, and the steady state satisfies
`1 + f'(k̄) = (1 + g)^{1/σ}(1 + n)/β`. -/
theorem steady_eq28 {σ β n g : ℝ} (hβ : 0 < β) (hn : 0 < 1 + n) (hg : 0 < 1 + g) :
    (1 + n) * (1 + g) / (β * (1 + g) ^ (1 - 1 / σ)) = (1 + g) ^ (1 / σ) * (1 + n) / β := by
  rw [Real.rpow_sub hg, Real.rpow_one]
  have : 0 < (1 + g) ^ (1 / σ) := Real.rpow_pos_of_pos hg _
  field_simp

/-- Under (28) the steady state is strictly decreasing in population growth (O&R p. 445:
"a rise in `n` changes the capital stock in the same way as a pure increase in
impatience"), whereas under (25) it does not depend on `n`. -/
theorem steady_eq28_strictAnti_n (hT : Technology f) {A β n n' k k' : ℝ} (hA : 0 < A)
    (hβ : 0 < β) (hnn : n < n') (hk : 0 < k) (hk' : 0 < k')
    (h1 : 1 + deriv f k = A * (1 + n) / β) (h2 : 1 + deriv f k' = A * (1 + n') / β) :
    k' < k := by
  have hlt : A * (1 + n) / β < A * (1 + n') / β :=
    div_lt_div_of_pos_right (mul_lt_mul_of_pos_left (by linarith) hA) hβ
  by_contra hle
  push Not at hle
  have := hT.neo.deriv_strictAnti.antitoneOn hk hk' hle
  linarith

/-- **Condition (23) is exactly `β̂ < 1`** (O&R p. 441): `β(1+n)(1+g)^{(σ-1)/σ} < 1` is the
statement that the detrended discount factor `β(1 + n)(1 + g)^{1 - 1/σ}` is below one. -/
theorem condition23_iff {σ β n g : ℝ} (hσ : σ ≠ 0) :
    β * (1 + n) * (1 + g) ^ ((σ - 1) / σ) < 1 ↔ β * (1 + n) * (1 + g) ^ (1 - 1 / σ) < 1 := by
  rw [show (σ - 1) / σ = 1 - 1 / σ by field_simp]

/-- **Detrending the dynasty objective (18)** (O&R pp. 441–442, the "stronger assumption"):
with per-capita consumption `c_t = E_t c^E_t`, `E_t = E₀(1 + g)^t` and isoelastic utility,
each term of (18) satisfies `βᵗ (1+n)ᵗ u(c_t) = E₀^θ β̂ᵗ u(c^E_t)` with
`β̂ = β(1+n)(1+g)^θ`, `θ = 1 - 1/σ`. -/
theorem detrend_term {θ β n g E0 cE : ℝ} (hg : 0 < 1 + g) (hE0 : 0 < E0)
    (hc : 0 ≤ cE) (t : ℕ) :
    β ^ t * (1 + n) ^ t * crra θ (E0 * (1 + g) ^ t * cE) =
      E0 ^ θ * ((β * (1 + n) * (1 + g) ^ θ) ^ t * crra θ cE) := by
  have e : ((1 + g) ^ t) ^ θ = ((1 + g) ^ θ) ^ t := by
    rw [← Real.rpow_natCast (1 + g) t, ← Real.rpow_natCast ((1 + g) ^ θ) t,
      ← Real.rpow_mul hg.le, ← Real.rpow_mul hg.le, mul_comm]
  unfold crra
  rw [Real.mul_rpow (by positivity) hc, Real.mul_rpow hE0.le (by positivity), e, mul_pow,
    mul_pow]
  ring

/-- **Detrended welfare** (O&R (18)): the per-capita dynasty objective is summable iff the
detrended one is, and then `U₀/L₀ = E₀^θ ∑ β̂ᵗ u(c^E_t)`. -/
theorem detrend_welfare {θ β n g E0 : ℝ} (hg : 0 < 1 + g) (hE0 : 0 < E0)
    {cE : ℕ → ℝ} (hc : ∀ t, 0 ≤ cE t) :
    (Summable (fun t => β ^ t * (1 + n) ^ t * crra θ (E0 * (1 + g) ^ t * cE t)) ↔
        Summable (fun t => (β * (1 + n) * (1 + g) ^ θ) ^ t * crra θ (cE t))) ∧
      ∑' t, β ^ t * (1 + n) ^ t * crra θ (E0 * (1 + g) ^ t * cE t) =
        E0 ^ θ * ∑' t, (β * (1 + n) * (1 + g) ^ θ) ^ t * crra θ (cE t) := by
  have heq : (fun t => β ^ t * (1 + n) ^ t * crra θ (E0 * (1 + g) ^ t * cE t)) =
      fun t => E0 ^ θ * ((β * (1 + n) * (1 + g) ^ θ) ^ t * crra θ (cE t)) :=
    funext fun t => detrend_term hg hE0 (hc t) t
  have hE : E0 ^ θ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hE0 θ)
  rw [heq]
  exact ⟨summable_mul_left_iff hE, tsum_mul_left⟩

/-- **The bounded-utility condition must be strict** (a flag on O&R p. 440, which writes
`β(1 + n) ≤ 1`): at `β(1 + n) = 1` a constant consumption path with `u(c) ≠ 0` has
non-summable utility, so dynasty utility (18) is unbounded. -/
theorem not_summable_at_boundary {β n uc : ℝ} (h : β * (1 + n) = 1) (huc : uc ≠ 0) :
    ¬ Summable (fun t : ℕ => β ^ t * (1 + n) ^ t * uc) := by
  intro hs
  have ht := hs.tendsto_atTop_zero
  simp only [← mul_pow, h, one_pow, one_mul] at ht
  exact huc (tendsto_nhds_unique tendsto_const_nhds ht)

/-- With `g = 0` and log utility the per-capita objective differs from the per-worker
one only by summable constants: `∑ (β(1+n))ᵗ (a + t b)` converges when `0 ≤ β(1+n) < 1`
(O&R p. 441, the log case `σ = 1` of (23)). -/
theorem summable_affine_geometric {q a b : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun t : ℕ => q ^ t * (a + t * b)) := by
  have h1 : Summable (fun t : ℕ => q ^ t * a) :=
    (summable_geometric_of_lt_one hq hq1).mul_right a
  have hn : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq]; exact hq1
  have h2 : Summable (fun t : ℕ => ((t : ℝ) * q ^ t) * b) :=
    ((summable_pow_mul_geometric_of_norm_lt_one 1 hn).mul_right b).congr (fun t => by simp)
  refine (h1.add h2).congr (fun t => ?_)
  ring

/-- **The per-worker Euler equation (20) without technical progress** (O&R p. 441): with
`g = 0` (so `z = n`) and general utility, the Euler equation of the transformed model with
`β̂ = β(1 + n)` is `u'(c_t) = [1 + f'(k_{t+1})] β u'(c_{t+1})`: population growth cancels. -/
theorem euler_eq20 {β n mu0 mu1 fp : ℝ} (hn : 0 < 1 + n)
    (he : mu0 = β * (1 + n) * mu1 * (1 + fp - 0) / (1 + n)) : mu0 = (1 + fp) * β * mu1 := by
  rw [he]; field_simp; ring

/-- **fn 8** (O&R p. 445): under the weights (27) the discount factor on per-capita utility
is `β` rather than `β(1 + n)`, and the Euler equation becomes
`u'(c_t) = [1 + f'(k_{t+1})] (β/(1+n)) u'(c_{t+1})`. -/
theorem euler_fn8 {β n mu0 mu1 fp : ℝ} (hn : 0 < 1 + n)
    (he : mu0 = β * mu1 * (1 + fp - 0) / (1 + n)) : mu0 = (1 + fp) * (β / (1 + n)) * mu1 := by
  rw [he]; field_simp; ring

/-! ### Comparative statics of the steady state (O&R fn 7, p. 443) -/

/-- A local right inverse of a strictly increasing function is continuous (used for the
implicit steady-state map `β ↦ k̄(β)` of fn 7). -/
theorem continuousAt_of_rightInverse_strictMono {ψ g : ℝ → ℝ} {y0 : ℝ}
    (hψ : StrictMonoOn ψ (Ioi 0)) (hinv : ∀ᶠ y in 𝓝 y0, ψ (g y) = y ∧ 0 < g y) :
    ContinuousAt g y0 := by
  have h0 := hinv.self_of_nhds
  rw [ContinuousAt, tendsto_order]
  constructor
  · intro a ha
    set a' := max a (g y0 / 2)
    have ha'0 : 0 < a' := lt_of_lt_of_le (half_pos h0.2) (le_max_right _ _)
    have ha'g : a' < g y0 := max_lt ha (half_lt_self h0.2)
    have hψa : ψ a' < y0 := by have := hψ ha'0 h0.2 ha'g; rwa [h0.1] at this
    filter_upwards [hinv, lt_mem_nhds hψa] with y hy hyl
    by_contra hle
    push Not at hle
    have hle' : g y ≤ a' := hle.trans (le_max_left _ _)
    have := hψ.monotoneOn hy.2 ha'0 hle'
    rw [hy.1] at this
    linarith
  · intro b hb
    have hb0 : 0 < b := h0.2.trans hb
    have hψb : y0 < ψ b := by have := hψ h0.2 hb0 hb; rwa [h0.1] at this
    filter_upwards [hinv, gt_mem_nhds hψb] with y hy hyl
    by_contra hle
    push Not at hle
    have := hψ.monotoneOn hb0 hy.2 hle
    rw [hy.1] at this
    linarith

/-- **fn 7, sign** (O&R p. 443): a more patient economy has a strictly larger steady
state; steady states solve `1 + f'(k̄) - δ = A/β` with `A = (1 + g)^{1/σ}` (or `1 + z`). -/
theorem steady_strictMono_patience (hT : Technology f) {A β β' k k' : ℝ} (hA : 0 < A)
    (hβ : 0 < β) (hββ : β < β') (hk : 0 < k) (hk' : 0 < k')
    (h1 : 1 + deriv f k - δ = A / β) (h2 : 1 + deriv f k' - δ = A / β') : k < k' := by
  have hlt : A / β' < A / β := div_lt_div_of_pos_left hA hβ hββ
  by_contra hle
  push Not at hle
  have := hT.neo.deriv_strictAnti.antitoneOn hk' hk hle
  linarith

/-- The derivative of a strictly decreasing marginal product is nonpositive. -/
theorem deriv2_nonpos (hT : Technology f) {k f2 : ℝ} (hk : 0 < k)
    (h2 : HasDerivAt (deriv f) f2 k) : f2 ≤ 0 := by
  have hs := hasDerivAt_iff_tendsto_slope.mp h2
  refine le_of_tendsto hs ?_
  have hpos : ∀ᶠ y in 𝓝[≠] k, 0 < y := nhdsWithin_le_nhds (lt_mem_nhds hk)
  filter_upwards [hpos, self_mem_nhdsWithin] with y hy hyne
  rw [slope_def_field]
  rcases lt_or_gt_of_ne (hyne : y ≠ k) with hlt | hgt
  · exact div_nonpos_of_nonneg_of_nonpos
      (by have := hT.neo.deriv_strictAnti hy hk hlt; linarith) (by linarith)
  · exact div_nonpos_of_nonpos_of_nonneg
      (by have := hT.neo.deriv_strictAnti hk hy hgt; linarith) (by linarith)

/-- **fn 7, derivative** (O&R p. 443): if `β ↦ k̄(β)` is the steady-state map near `β₀`
(`1 + f'(k̄(β)) - δ = A/β`, `δ ≤ 1`) and `f''(k̄) ≠ 0`, then `k̄` is differentiable at `β₀`
with `dk̄/dβ = -[1 + f'(k̄) - δ]/(β f''(k̄)) > 0`. Differentiability is derived (inverse
function theorem plus continuity of the inverse), not assumed; strict concavity alone would
not give `f''(k̄) ≠ 0`, which is why that is a hypothesis. -/
theorem steady_hasDerivAt_patience (hT : Technology f) (hδ1 : δ ≤ 1) {A β0 f2 : ℝ}
    (hA : 0 < A) (hβ0 : 0 < β0) {kb : ℝ → ℝ}
    (hkb : ∀ᶠ β in 𝓝 β0, 0 < kb β ∧ 1 + deriv f (kb β) - δ = A / β)
    (h2 : HasDerivAt (deriv f) f2 (kb β0)) (hf2 : f2 ≠ 0) :
    HasDerivAt kb (-(1 + deriv f (kb β0) - δ) / (β0 * f2)) β0 ∧
      0 < -(1 + deriv f (kb β0) - δ) / (β0 * f2) := by
  obtain ⟨hk0, hss0⟩ := hkb.self_of_nhds
  set k0 := kb β0
  set D : ℝ → ℝ := fun k => 1 + deriv f k - δ
  set ψ : ℝ → ℝ := fun k => A / D k
  have hDpos : ∀ k, 0 < k → 0 < D k := fun k hk => by
    simp only [D]; linarith [hT.neo.deriv_pos hk]
  have hD0 : D k0 = A / β0 := hss0
  have hψmono : StrictMonoOn ψ (Ioi 0) := by
    intro a ha b hb hab
    have hd := hT.neo.deriv_strictAnti ha hb hab
    simp only [ψ]
    apply div_lt_div_of_pos_left hA (hDpos b hb)
    simp only [D]; linarith
  have hψinv : ∀ᶠ β in 𝓝 β0, ψ (kb β) = β ∧ 0 < kb β := by
    filter_upwards [hkb, lt_mem_nhds hβ0] with β hβ hβpos
    refine ⟨?_, hβ.1⟩
    simp only [ψ, D]
    rw [hβ.2]
    field_simp
  have hcont : ContinuousAt kb β0 := continuousAt_of_rightInverse_strictMono hψmono hψinv
  have hDd : HasDerivAt D f2 k0 := (h2.const_add 1).sub_const δ
  have hψd : HasDerivAt ψ (A * (-f2 / D k0 ^ 2)) k0 :=
    (hDd.inv (ne_of_gt (hDpos k0 hk0))).const_mul A
  have hne : A * (-f2 / D k0 ^ 2) ≠ 0 := by
    have := hDpos k0 hk0
    exact mul_ne_zero (ne_of_gt hA) (div_ne_zero (neg_ne_zero.mpr hf2) (by positivity))
  have hderiv := HasDerivAt.of_local_left_inverse hcont hψd hne
    (hψinv.mono fun _ h => h.1)
  have hf2neg : f2 < 0 := lt_of_le_of_ne (deriv2_nonpos hT hk0 h2) hf2
  have hR : 0 < 1 + deriv f k0 - δ := hDpos k0 hk0
  refine ⟨hderiv.congr_deriv ?_, ?_⟩
  · have e : D k0 = 1 + deriv f k0 - δ := rfl
    rw [← e, hD0]
    field_simp
  · exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_pos_of_neg hβ0 hf2neg)

/-! ### The experiments of Figs. 7.5 and 7.6 (O&R pp. 443–445) -/

/-- **Fig. 7.5, a rise in impatience** (O&R p. 443): starting from the old steady state
`k̄` (patience `β`), after `β` falls to `β' < β` the new optimal path (i) has a strictly
lower steady state, (ii) consumption jumps *up* on impact above the old steady-state level
`c̄ = f(k̄) - (z+δ)k̄`, (iii) capital and consumption then fall strictly, and (iv) consumption
converges to a new level strictly below `c̄`. -/
theorem impatience_experiment (hT : Technology f) {β β' z : ℝ} (hβ' : 0 < β')
    (hββ : β' < β) (hβ1 : β < 1) (hz : 0 < 1 + z)
    (P' : Primitives (effF f z) (effU u z) β' (effDelta z δ)) {kbar : ℝ} (hk : 0 < kbar)
    (hss : 1 + deriv f kbar - δ = (1 + z) / β) {k : ℕ → ℝ}
    (hopt : IsOptimal (effF f z) (effU u z) β' (effDelta z δ) kbar k) :
    steady P' < kbar ∧
      f kbar - (z + δ) * kbar < bookConsumption f δ z k 0 ∧
      StrictAnti k ∧ StrictAnti (bookConsumption f δ z k) ∧
      Tendsto (bookConsumption f δ z k) atTop (𝓝 (f (steady P') - (z + δ) * steady P')) ∧
      f (steady P') - (z + δ) * steady P' < f kbar - (z + δ) * kbar := by
  obtain ⟨hks, hss', -⟩ := book_steady_spec hT hβ' hz P'
  have hlt : steady P' < kbar :=
    steady_strictMono_patience hT hz hβ' hββ hks hk hss' hss
  obtain ⟨-, hc, -, habove⟩ := book_convergence hz P' hk hopt
  obtain ⟨hsa, -, hca⟩ := habove hlt
  refine ⟨hlt, ?_, hsa, hca, hc, ?_⟩
  · have h1 : k 1 < k 0 := hsa (Nat.lt_succ_self 0)
    rw [hopt.1.1] at h1
    unfold bookConsumption
    rw [hopt.1.1]
    nlinarith
  · -- tangent line at `k̄` and dynamic efficiency `f'(k̄) > z + δ`
    have ht := hT.neo.tangent_lt hk hks.le (ne_of_lt hlt)
    have hdyn : z + δ < deriv f kbar := by
      have : 1 + z < (1 + z) / β := by rw [lt_div_iff₀ (hβ'.trans hββ)]; nlinarith
      linarith
    nlinarith

/-- **Fig. 7.6, a rise in population growth** (O&R pp. 443–444): under the dynasty weights
(18) the steady state of `k^E` is the same before and after (it solves
`1 + f'(k̄) - δ = (1+g)^{1/σ}/β`, eq. (25)), the new optimal path from the old steady state
stays there for ever ("the economy adjusts immediately"), and steady-state consumption per
efficiency worker `f(k̄) - (z + δ)k̄` is strictly lower. -/
theorem population_experiment (hT : Technology f) {β β' z z' : ℝ} (hβ : 0 < β)
    (hβ' : 0 < β') (hz : 0 < 1 + z) (hz' : 0 < 1 + z') (hzz : z < z')
    (hsame : (1 + z) / β = (1 + z') / β')
    (P : Primitives (effF f z) (effU u z) β (effDelta z δ))
    (P' : Primitives (effF f z') (effU u z') β' (effDelta z' δ)) :
    steady P' = steady P ∧
      optimalPath P' (steady_spec P').1.le = (fun _ => steady P') ∧
      f (steady P) - (z' + δ) * steady P < f (steady P) - (z + δ) * steady P := by
  obtain ⟨hks, hss, -⟩ := book_steady_spec hT hβ hz P
  obtain ⟨hks', hss', huniq'⟩ := book_steady_spec hT hβ' hz' P'
  have heq : steady P' = steady P := (huniq' _ hks (by rw [hss, hsame])).symm
  refine ⟨heq, optimalPath_steady P', ?_⟩
  nlinarith

/-- Under (18) the two steady-state conditions of Fig. 7.6 coincide: with
`β̂ = β(1 + n)(1 + g)^{1-1/σ}` and `1 + z = (1 + n)(1 + g)`, the ratio `(1 + z)/β̂` does not
depend on `n` (O&R p. 444). -/
theorem population_same_target {σ β n n' g : ℝ} (hβ : 0 < β) (hn : 0 < 1 + n)
    (hn' : 0 < 1 + n') (hg : 0 < 1 + g) :
    (1 + n) * (1 + g) / (β * (1 + n) * (1 + g) ^ (1 - 1 / σ)) =
      (1 + n') * (1 + g) / (β * (1 + n') * (1 + g) ^ (1 - 1 / σ)) := by
  rw [steady_eq25 hβ hn hg, steady_eq25 hβ hn' hg]

/-! ## Open-economy variants (O&R §7.2.1.1, §7.2.2.2, pp. 459–464) -/

/-- **The small open economy** (O&R p. 464: "transnational investment would quickly force
convergence ... in net marginal products of capital"): facing a world interest rate `r`,
the profit-maximising capital stock per efficiency worker is the unique `k_r` with
`f'(k_r) = r + δ`, whatever the economy's own capital, saving or preferences:
`f(k) - (r + δ) k < f(k_r) - (r + δ) k_r` for every other `k ≥ 0`. -/
theorem small_open_capital (hT : Technology f) {r kr k : ℝ} (hkr : 0 < kr)
    (hmp : deriv f kr = r + δ) (hk : 0 ≤ k) (hne : k ≠ kr) :
    f k - (r + δ) * k < f kr - (r + δ) * kr :=
  SolowModel.golden_rule_strict_max hT.neo hkr hmp hk hne

/-- In a small open economy the capital-labour ratio jumps to `k_r` at once: two such
economies with the same technology and world rate have identical capital and output per
efficiency worker from the first date on, regardless of initial capital (O&R p. 464). -/
theorem small_open_immediate_convergence (hT : Technology f) {r kr k1 k2 : ℝ} (hkr : 0 < kr)
    (hmp : deriv f kr = r + δ) (h1 : 0 < k1) (h2 : 0 < k2) (hm1 : deriv f k1 = r + δ)
    (hm2 : deriv f k2 = r + δ) : k1 = kr ∧ k2 = kr ∧ f k1 = f k2 := by
  have e1 := hT.neo.deriv_strictAnti.injOn h1 hkr (hm1.trans hmp.symm)
  have e2 := hT.neo.deriv_strictAnti.injOn h2 hkr (hm2.trans hmp.symm)
  exact ⟨e1, e2, by rw [e1, e2]⟩

/-- **The integrated world economy** (O&R p. 464): with identical technologies and a world
capital market, allocating world capital `K` across countries with efficiency labour
`L_j > 0` yields world output at most `(∑ L_j) f(K/∑ L_j)`, with equality only when every
country has the same capital intensity; so the world behaves exactly like one closed
Ramsey–Cass–Koopmans economy in `k^W = K/L^W`. -/
theorem world_output_le {ι : Type*} (s : Finset ι) (hT : Technology f) {L k : ι → ℝ}
    (hL : ∀ j ∈ s, 0 < L j) (hk : ∀ j ∈ s, 0 ≤ k j) (hs : s.Nonempty) :
    ∑ j ∈ s, L j * f (k j) ≤
      (∑ j ∈ s, L j) * f ((∑ j ∈ s, L j * k j) / ∑ j ∈ s, L j) := by
  have hLs : 0 < ∑ j ∈ s, L j := Finset.sum_pos hL hs
  have hw0 : ∀ j ∈ s, 0 ≤ L j / ∑ i ∈ s, L i := fun j hj => div_nonneg (hL j hj).le hLs.le
  have hw1 : ∑ j ∈ s, L j / ∑ i ∈ s, L i = 1 := by
    rw [← Finset.sum_div, div_self (ne_of_gt hLs)]
  have hJ := hT.neo.strictConcave.concaveOn.le_map_sum hw0 hw1 hk
  simp only [smul_eq_mul] at hJ
  have e1 : ∑ j ∈ s, (L j / ∑ i ∈ s, L i) * k j = (∑ j ∈ s, L j * k j) / ∑ j ∈ s, L j := by
    rw [Finset.sum_div]; congr 1; ext j; ring
  have e2 : ∑ j ∈ s, (L j / ∑ i ∈ s, L i) * f (k j) =
      (∑ j ∈ s, L j * f (k j)) / ∑ j ∈ s, L j := by
    rw [Finset.sum_div]; congr 1; ext j; ring
  rw [e1, e2, div_le_iff₀ hLs] at hJ
  linarith

/-- Strictness in the world-economy allocation (O&R p. 464): if two countries have
different capital intensities, world output is strictly below its integrated-market level,
so capital flows until intensities (and marginal products) are equalised. -/
theorem world_output_lt {ι : Type*} (s : Finset ι) (hT : Technology f) {L k : ι → ℝ}
    (hL : ∀ j ∈ s, 0 < L j) (hk : ∀ j ∈ s, 0 ≤ k j)
    (hne : ∃ i ∈ s, ∃ j ∈ s, k i ≠ k j) :
    ∑ j ∈ s, L j * f (k j) <
      (∑ j ∈ s, L j) * f ((∑ j ∈ s, L j * k j) / ∑ j ∈ s, L j) := by
  have ⟨i, hi, _⟩ := hne
  have hLs : 0 < ∑ j ∈ s, L j := Finset.sum_pos hL ⟨i, hi⟩
  have hw0 : ∀ j ∈ s, 0 < L j / ∑ i ∈ s, L i := fun j hj => div_pos (hL j hj) hLs
  have hw1 : ∑ j ∈ s, L j / ∑ i ∈ s, L i = 1 := by
    rw [← Finset.sum_div, div_self (ne_of_gt hLs)]
  have hJ := hT.neo.strictConcave.lt_map_sum hw0 hw1 hk hne
  simp only [smul_eq_mul] at hJ
  have e1 : ∑ j ∈ s, (L j / ∑ i ∈ s, L i) * k j = (∑ j ∈ s, L j * k j) / ∑ j ∈ s, L j := by
    rw [Finset.sum_div]; congr 1; ext j; ring
  have e2 : ∑ j ∈ s, (L j / ∑ i ∈ s, L i) * f (k j) =
      (∑ j ∈ s, L j * f (k j)) / ∑ j ∈ s, L j := by
    rw [Finset.sum_div]; congr 1; ext j; ring
  rw [e1, e2, div_lt_iff₀ hLs] at hJ
  linarith

/-- Equal marginal products force equal capital intensities (arbitrage in the integrated
world capital market, O&R p. 464). -/
theorem equal_mpk_iff (hT : Technology f) {k1 k2 : ℝ} (h1 : 0 < k1) (h2 : 0 < k2) :
    deriv f k1 = deriv f k2 ↔ k1 = k2 :=
  ⟨fun h => hT.neo.deriv_strictAnti.injOn h1 h2 h, fun h => by rw [h]⟩

/-! ### Per-capita forms (O&R (19)–(22)) and the small open economy's consumption -/

/-- **The marginal product in per-worker terms** (O&R p. 441, `F(k, E) = F(K, EL)/L`): with
constant returns written as `F(K, N) = N f(K/N)`, `∂F/∂K = f'(K/N)`, so `F_K(k_{t+1}, E_{t+1})`
in (20)–(22) equals `f'(k^E_{t+1})`. -/
theorem marginal_product_crs {F : ℝ → ℝ → ℝ} (hT : Technology f) {K N : ℝ} (hN : 0 < N)
    (hK : 0 < K) (hF : ∀ K', F K' N = N * f (K' / N)) :
    HasDerivAt (fun K' => F K' N) (deriv f (K / N)) K := by
  have hkN : 0 < K / N := div_pos hK hN
  have h := ((hT.neo.diff (K / N) hkN).hasDerivAt.comp K
    ((hasDerivAt_id' K).div_const N)).const_mul N
  rw [show (fun K' => F K' N) = fun K' => N * f (K' / N) from funext hF]
  refine h.congr_deriv ?_
  field_simp

/-- **Eq. (22) from eq. (24)** (O&R pp. 441–442): per-capita consumption is `c_t = E_t c^E_t`
with `E_{t+1} = (1 + g) E_t`, so if efficiency-unit consumption grows by
`β^σ [1 + f'(k^E)]^σ/(1 + g)` then per-capita consumption grows by `β^σ [1 + F_K]^σ`. -/
theorem eq22_of_eq24 {β σ g E cE0 cE1 fp : ℝ} (hg : 0 < 1 + g) (hE : 0 < E) (hc : 0 < cE0)
    (h24 : cE1 / cE0 = β ^ σ * (1 + fp) ^ σ / (1 + g)) :
    ((1 + g) * E * cE1) / (E * cE0) = β ^ σ * (1 + fp) ^ σ := by
  have : ((1 + g) * E * cE1) / (E * cE0) = (1 + g) * (cE1 / cE0) := by field_simp
  rw [this, h24]
  field_simp

/-- **The small open economy's consumption path** (O&R §7.2.1.1 with the dynasty of
§7.1.2.1): facing a constant world rate `r`, the dynasty's Euler equation is (24) with `r` in
place of `f'(k)`, so efficiency-unit consumption grows by the constant factor
`β^σ (1 + r)^σ/(1 + g)`, whatever the domestic capital stock. -/
theorem small_open_consumption_growth {σ β n g c0 c1 r : ℝ} (hσ : 0 < σ) (hβ : 0 < β)
    (hn : 0 < 1 + n) (hg : 0 < 1 + g) (hc0 : 0 < c0) (hc1 : 0 < c1) (hr : 0 < 1 + r)
    (he : c0 ^ (1 - 1 / σ - 1) = β * (1 + n) * (1 + g) ^ (1 - 1 / σ) * c1 ^ (1 - 1 / σ - 1) *
      (1 + r - 0) / ((1 + n) * (1 + g))) :
    c1 / c0 = β ^ σ * (1 + r) ^ σ / (1 + g) :=
  crra_euler_eq24 hσ hβ hn hg hc0 hc1 hr he

/-! ## Utility unbounded below: log and isoelastic utility with `σ ≤ 1` (O&R (21)) -/

namespace LogUtility

/-- Primitives with utility defined on positive consumption only and unbounded below at
zero: covers `log c` and `c^θ/θ` with `θ = 1 - 1/σ < 0` (O&R (21) with `σ ≤ 1`). The
technology hypotheses are those of the generic model. -/
structure UPrimitives (f u : ℝ → ℝ) (β δ : ℝ) : Prop where
  β_pos : 0 < β
  β_lt_one : β < 1
  δ_nonneg : 0 ≤ δ
  δ_le_one : δ ≤ 1
  f_cont : ContinuousOn f (Ici 0)
  f_zero : f 0 = 0
  f_conc : StrictConcaveOn ℝ (Ici 0) f
  f_diff : ∀ k, 0 < k → DifferentiableAt ℝ f k
  f_prime_pos : ∀ k, 0 < k → 0 < deriv f k
  f_prime_cont : ContinuousOn (deriv f) (Ioi 0)
  f_inada0 : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop
  f_inadaTop : Tendsto (deriv f) atTop (𝓝 (0 : ℝ))
  u_cont : ContinuousOn u (Ioi 0)
  u_conc : StrictConcaveOn ℝ (Ioi 0) u
  u_diff : ∀ c, 0 < c → DifferentiableAt ℝ u c
  u_prime_pos : ∀ c, 0 < c → 0 < deriv u c
  u_prime_cont : ContinuousOn (deriv u) (Ioi 0)
  u_inada0 : Tendsto (deriv u) (𝓝[>] (0 : ℝ)) atTop
  u_bot : Tendsto u (𝓝[>] (0 : ℝ)) atBot

/-- The technology side packaged with an auxiliary bounded utility `2√c`, giving access to
the technology lemmas of the generic model (capital bound, compactness, steady state). -/
theorem UPrimitives.aux (P : UPrimitives f u β δ) : Primitives f (crra (1 / 2)) β δ :=
  have hU := crra_preferences (θ := 1 / 2) (by norm_num) (by norm_num)
  { β_pos := P.β_pos, β_lt_one := P.β_lt_one, δ_nonneg := P.δ_nonneg, δ_le_one := P.δ_le_one,
    f_cont := P.f_cont, f_zero := P.f_zero, f_conc := P.f_conc, f_diff := P.f_diff,
    f_prime_pos := P.f_prime_pos, f_prime_cont := P.f_prime_cont, f_inada0 := P.f_inada0,
    f_inadaTop := P.f_inadaTop, u_cont := hU.cont, u_conc := hU.conc, u_diff := hU.diff,
    u_prime_pos := hU.prime_pos, u_prime_cont := hU.prime_cont, u_inada0 := hU.inada0 }

/-- Utility is strictly increasing on positive consumption. -/
theorem UPrimitives.u_strictMono (P : UPrimitives f u β δ) : StrictMonoOn u (Ioi 0) :=
  strictMonoOn_of_deriv_pos (convex_Ioi 0) P.u_cont
    (fun c hc => by rw [interior_Ioi] at hc; exact P.u_prime_pos c hc)

/-- Marginal utility is strictly decreasing. -/
theorem UPrimitives.u_prime_anti (P : UPrimitives f u β δ) : StrictAntiOn (deriv u) (Ioi 0) :=
  P.u_conc.strictAntiOn_deriv P.u_diff

/-- An admissible path (O&R (18) with log utility): feasible, with strictly positive
consumption and a convergent welfare series. -/
def Admissible (f u : ℝ → ℝ) (β δ x : ℝ) (k : ℕ → ℝ) : Prop :=
  Feasible f δ x k ∧ (∀ t, 0 < consumption f δ k t) ∧
    Summable (fun t => β ^ t * u (consumption f δ k t))

/-- An optimal path: admissible and at least as good as every admissible path. Paths with
zero consumption at some date, or with divergent welfare, have welfare `-∞` and are
dominated (see `partial_sums_le_of_euler_log` for the partial-sum version). -/
def UOptimal (f u : ℝ → ℝ) (β δ x : ℝ) (k : ℕ → ℝ) : Prop :=
  Admissible f u β δ x k ∧ ∀ k', Admissible f u β δ x k' → welfare f u β δ k' ≤ welfare f u β δ k

/-- Capital stays strictly positive along an admissible path from `x > 0`: zero capital
would force zero consumption next period. -/
theorem Admissible.capital_pos (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : Admissible f u β δ x k) (t : ℕ) : 0 < k t := by
  cases t with
  | zero => rw [hk.1.1]; exact hx
  | succ t =>
    by_contra hle
    push Not at hle
    have h0 : k (t + 1) = 0 := le_antisymm hle (hk.1.2 t).1
    have hc := hk.2.1 (t + 1)
    simp only [consumption, h0, resources_zero P.aux, zero_sub] at hc
    linarith [(hk.1.2 (t + 1)).1]

/-- Along admissible paths from `x ≥ 0` utility at date `t` is bounded above by `u(B_{t+1})`,
`B` the capital bounds. -/
theorem Admissible.u_le (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : Feasible f δ x k) (hc : ∀ t, 0 < consumption f δ k t) (t : ℕ) :
    u (consumption f δ k t) ≤ u (bound P.aux x (t + 1)) :=
  P.u_strictMono.monotoneOn (hc t) (lt_of_lt_of_le (hc t) (hk.consumption_mem P.aux hx t).2)
    (hk.consumption_mem P.aux hx t).2

/-- The utility majorant `βᵗ u(B_{t+1})` is summable (linear growth of the bounds). -/
theorem umajorant_summable (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) :
    Summable (fun t => β ^ t * u (bound P.aux x (t + 1))) := by
  have A := P.aux
  obtain ⟨-, hge, hmono, -⟩ := bound_spec A x
  have hB : ∀ t, x ≤ bound A x t := fun t => (le_max_left x 0).trans (hge t)
  have hBmono : Monotone (bound A x) := monotone_nat_of_le_succ hmono
  have hB1 : 0 < bound A x 1 := lt_of_lt_of_le hx (hB 1)
  have hd := P.u_prime_pos 1 one_pos
  have hmaj : Summable (fun t => β ^ t * (|u (bound A x 1)| + |u 1| + deriv u 1 *
      bound A x (t + 1))) := by
    have hgeo := summable_geometric_of_lt_one P.β_pos.le P.β_lt_one
    refine ((hgeo.mul_right (|u (bound A x 1)| + |u 1|)).add
      ((bound_summable A x).mul_left (deriv u 1))).congr (fun t => ?_)
    ring
  refine Summable.of_norm_bounded hmaj (fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos P.β_pos t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_pos P.β_pos t).le
  have hBt : 0 < bound A x (t + 1) := lt_of_lt_of_le hx (hB _)
  have hlow : u (bound A x 1) ≤ u (bound A x (t + 1)) :=
    P.u_strictMono.monotoneOn hB1 hBt (hBmono (by omega))
  have hup := concave_support P.u_conc.concaveOn (mem_Ioi.mpr one_pos) (mem_Ioi.mpr hBt)
    (P.u_diff 1 one_pos).hasDerivAt
  have h2 : 0 ≤ deriv u 1 * bound A x (t + 1) := mul_nonneg hd.le hBt.le
  have h3 := neg_abs_le (u (bound A x 1))
  have h4 := le_abs_self (u 1)
  have h5 := abs_nonneg (u (bound A x 1))
  have h6 := abs_nonneg (u 1)
  rw [abs_le]
  constructor
  · linarith
  · nlinarith

/-- Resources exceed capital on `(0, k*]` (concavity of gross resources). -/
theorem resources_gt_self {g : ℝ → ℝ} (A : Primitives f g β δ) {k : ℝ} (hk : 0 < k)
    (hks : k ≤ steady A) : k < resources f δ k := by
  have hs := (steady_spec A).1
  have hcs := steady_consumption_pos A
  have hθ : 0 ≤ k / steady A := div_nonneg hk.le hs.le
  have hθ1 : 0 ≤ 1 - k / steady A := by rw [sub_nonneg, div_le_one hs]; exact hks
  have hc := A.resources_concave.2 (mem_Ici.mpr hs.le) (mem_Ici.mpr (le_refl (0 : ℝ))) hθ hθ1
    (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, resources_zero A] at hc
  rw [div_mul_cancel₀ k (ne_of_gt hs)] at hc
  have : k / steady A * steady A < k / steady A * resources f δ (steady A) :=
    mul_lt_mul_of_pos_left (by linarith) (div_pos hk hs)
  rw [div_mul_cancel₀ k (ne_of_gt hs)] at this
  linarith

/-- An admissible path exists from every `x > 0` (move to `min(x, k*)` and stay). -/
theorem exists_admissible (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) :
    ∃ k, Admissible f u β δ x k := by
  have A := P.aux
  set m := min x (steady A)
  have hm : 0 < m := lt_min hx (steady_spec A).1
  have hmF : m < resources f δ m := resources_gt_self A hm (min_le_right _ _)
  have hFx : resources f δ m ≤ resources f δ x :=
    A.resources_strictMono.monotoneOn (mem_Ici.mpr hm.le) (mem_Ici.mpr hx.le) (min_le_left _ _)
  set k : ℕ → ℝ := fun t => if t = 0 then x else m
  have hc0 : consumption f δ k 0 = resources f δ x - m := by simp [consumption, k]
  have hc1 : ∀ t, consumption f δ k (t + 1) = resources f δ m - m := by
    intro t; simp [consumption, k]
  have hcpos : ∀ t, 0 < consumption f δ k t := by
    intro t; cases t with
    | zero => rw [hc0]; linarith
    | succ t => rw [hc1]; linarith
  refine ⟨k, ⟨rfl, fun t => ⟨by simp [k, hm.le], ?_⟩⟩, hcpos, ?_⟩
  · cases t with
    | zero => simp only [k, ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false]; linarith
    | succ t => simp only [k, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]; linarith
  · refine Summable.of_norm_bounded ((summable_geometric_of_lt_one P.β_pos.le
      P.β_lt_one).mul_right (|u (resources f δ x - m)| + |u (resources f δ m - m)|))
      (fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos P.β_pos t)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_pos P.β_pos t).le
    cases t with
    | zero => rw [hc0]; linarith [abs_nonneg (u (resources f δ m - m))]
    | succ t => rw [hc1]; linarith [abs_nonneg (u (resources f δ x - m))]

/-- Welfare along an admissible path is at most `∑ βᵗ u(B_{t+1})`. -/
theorem Admissible.welfare_le (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : Admissible f u β δ x k) :
    welfare f u β δ k ≤ ∑' t, β ^ t * u (bound P.aux x (t + 1)) :=
  hk.2.2.tsum_le_tsum (fun t => mul_le_mul_of_nonneg_left
    (Admissible.u_le P hx.le hk.1 hk.2.1 t) (pow_pos P.β_pos t).le) (umajorant_summable P hx)

/-- Tail bound: `W(k) ≤ ∑_{t<N} βᵗ u(c_t) + ∑_{t ≥ N} βᵗ u(B_{t+1})`. -/
theorem Admissible.welfare_le_partial (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x)
    {k : ℕ → ℝ} (hk : Admissible f u β δ x k) (N : ℕ) :
    welfare f u β δ k ≤ ∑ t ∈ Finset.range N, β ^ t * u (consumption f δ k t) +
      ∑' t, β ^ (t + N) * u (bound P.aux x (t + N + 1)) := by
  have hsplit := hk.2.2.sum_add_tsum_nat_add N
  have htail : ∑' t, β ^ (t + N) * u (consumption f δ k (t + N)) ≤
      ∑' t, β ^ (t + N) * u (bound P.aux x (t + N + 1)) :=
    ((summable_nat_add_iff N).mpr hk.2.2).tsum_le_tsum (fun t =>
      mul_le_mul_of_nonneg_left (Admissible.u_le P hx.le hk.1 hk.2.1 (t + N))
        (pow_pos P.β_pos (t + N)).le)
      ((summable_nat_add_iff N).mpr (umajorant_summable P hx))
  rw [welfare, ← hsplit]
  linarith

/-- **Existence of an optimal path with utility unbounded below** (O&R (18) with log or
`σ < 1` isoelastic utility): from every `x > 0` some admissible path attains the supremum of
welfare over admissible paths. The proof takes a maximising sequence, extracts a convergent
subsequence in the compact feasible set, shows that the limit has strictly positive
consumption (otherwise welfare would tend to `-∞`), and bounds its partial sums below. -/
theorem exists_optimal (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) :
    ∃ k, UOptimal f u β δ x k := by
  have A := P.aux
  set g : ℕ → ℝ := fun t => β ^ t * u (bound A x (t + 1))
  have hg : Summable g := umajorant_summable P hx
  set C := ∑' t, g t
  have hβ0 := P.β_pos
  have hβ1 := P.β_lt_one
  have hgeo := summable_geometric_of_lt_one hβ0.le hβ1
  set S := (welfare f u β δ) '' {k | Admissible f u β δ x k}
  have hSne : S.Nonempty := by
    obtain ⟨k, hk⟩ := exists_admissible P hx
    exact ⟨_, k, hk, rfl⟩
  have hSbdd : BddAbove S := ⟨C, by rintro _ ⟨k, hk, rfl⟩; exact hk.welfare_le P hx⟩
  set V := sSup S
  have hseq : ∀ n : ℕ, ∃ k, Admissible f u β δ x k ∧
      V - 1 / ((n : ℝ) + 1) < welfare f u β δ k := by
    intro n
    obtain ⟨w, ⟨k, hk, rfl⟩, hw⟩ := exists_lt_of_lt_csSup hSne
      (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith : V - 1 / ((n : ℝ) + 1) < V)
    exact ⟨k, hk, hw⟩
  choose kn hadm hkn using hseq
  obtain ⟨kh, hkh, φ, hφ, hlim⟩ :=
    (isCompact_feasibleSet A hx.le).tendsto_subseq (fun n => (hadm n).1)
  have hkhF : Feasible f δ x kh := hkh
  have hcoord : ∀ t, Tendsto (fun n => kn (φ n) t) atTop (𝓝 (kh t)) :=
    fun t => (continuous_apply t).continuousAt.tendsto.comp hlim
  have hct : ∀ t, Tendsto (fun n => consumption f δ (kn (φ n)) t) atTop
      (𝓝 (consumption f δ kh t)) := by
    intro t
    have hF := (A.resources_cont (kh t) (mem_Ici.mpr (hkhF.nonneg hx.le t))).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hcoord t, Eventually.of_forall
        (fun n => mem_Ici.mpr ((hadm (φ n)).1.nonneg hx.le t))⟩)
    exact hF.sub (hcoord (t + 1))
  have hcnn : ∀ t, 0 ≤ consumption f δ kh t := fun t => (hkhF.consumption_mem A hx.le t).1
  have hinv : Tendsto (fun m => 1 / ((φ m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  -- consumption of the limit path is strictly positive
  have hcpos : ∀ T, 0 < consumption f δ kh T := by
    intro T
    by_contra hle
    push Not at hle
    have h0 : consumption f δ kh T = 0 := le_antisymm hle (hcnn T)
    have hto : Tendsto (fun n => consumption f δ (kn (φ n)) T) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨h0 ▸ hct T, Eventually.of_forall
        (fun n => (hadm (φ n)).2.1 T)⟩
    have hbot := P.u_bot.comp hto
    -- welfare bound through the date-`T` term
    set M := u (bound A x (T + 1))
    have hW : ∀ n, welfare f u β δ (kn n) ≤ C + β ^ T * (u (consumption f δ (kn n) T) - M) := by
      intro n
      set g' : ℕ → ℝ := fun t => g t +
        (if t = T then β ^ T * (u (consumption f δ (kn n) T) - M) else 0)
      have hgs : Summable g' := hg.add
        (hasSum_ite_eq T (β ^ T * (u (consumption f δ (kn n) T) - M))).summable
      have hle' : welfare f u β δ (kn n) ≤ ∑' t, g' t := by
        refine (hadm n).2.2.tsum_le_tsum (fun t => ?_) hgs
        simp only [g', g]
        split_ifs with htT
        · subst htT; simp only [M]; ring_nf; exact le_refl _
        · rw [add_zero]
          exact mul_le_mul_of_nonneg_left (Admissible.u_le P hx.le (hadm n).1 (hadm n).2.1 t)
            (pow_pos hβ0 t).le
      rw [hg.tsum_add (hasSum_ite_eq T _).summable, tsum_ite_eq] at hle'
      exact hle'
    have hlow : ∀ n, (V - 1 - C) / β ^ T + M < u (consumption f δ (kn n) T) := by
      intro n
      have h1 := hkn n
      have h2 := hW n
      have h3 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      have hbT := pow_pos hβ0 T
      rw [div_add' _ _ _ (ne_of_gt hbT), div_lt_iff₀ hbT]
      nlinarith
    obtain ⟨n, hn⟩ := (hbot.eventually (eventually_lt_atBot ((V - 1 - C) / β ^ T + M))).exists
    exact absurd (hlow (φ n)) (not_lt.mpr hn.le)
  -- partial sums of the limit path are bounded below
  set Tl : ℕ → ℝ := fun N => ∑' t, g (t + N)
  have hTl : Tendsto Tl atTop (𝓝 0) := tendsto_sum_nat_add g
  have hpart : ∀ N, V - Tl N ≤
      ∑ t ∈ Finset.range N, β ^ t * u (consumption f δ kh t) := by
    intro N
    have hsum : Tendsto (fun m => ∑ t ∈ Finset.range N, β ^ t * u (consumption f δ (kn (φ m)) t))
        atTop (𝓝 (∑ t ∈ Finset.range N, β ^ t * u (consumption f δ kh t))) := by
      refine tendsto_finsetSum _ (fun t _ => ?_)
      exact ((P.u_cont.continuousAt (Ioi_mem_nhds (hcpos t))).tendsto.comp (hct t)).const_mul _
    have hlow : Tendsto (fun m => V - 1 / ((φ m : ℝ) + 1) - Tl N) atTop
        (𝓝 (V - 0 - Tl N)) := (tendsto_const_nhds.sub hinv).sub tendsto_const_nhds
    rw [sub_zero] at hlow
    refine le_of_tendsto_of_tendsto hlow hsum (Eventually.of_forall (fun m => ?_))
    have h1 := hkn (φ m)
    have h2 := (hadm (φ m)).welfare_le_partial P hx N
    have e : Tl N = ∑' t, β ^ (t + N) * u (bound P.aux x (t + N + 1)) := rfl
    linarith
  -- summability of the limit path's welfare
  have hub : ∀ t, u (consumption f δ kh t) ≤ u (bound A x (t + 1)) :=
    fun t => Admissible.u_le P hx.le hkhF hcpos t
  have hd : Summable (fun t => g t - β ^ t * u (consumption f δ kh t)) := by
    refine summable_of_sum_range_le (c := C - V) (fun t => ?_) (fun N => ?_)
    · have := mul_le_mul_of_nonneg_left (hub t) (pow_pos hβ0 t).le; simp only [g]; linarith
    · rw [Finset.sum_sub_distrib]
      have h := hpart N
      have hsplit := hg.sum_add_tsum_nat_add N
      have e : Tl N = ∑' t, g (t + N) := rfl
      linarith
  have hs : Summable (fun t => β ^ t * u (consumption f δ kh t)) :=
    (hg.sub hd).congr (fun t => by ring)
  have hWkh : V ≤ welfare f u β δ kh := by
    have hlim' : Tendsto (fun N => V - Tl N) atTop (𝓝 (V - 0)) :=
      tendsto_const_nhds.sub hTl
    rw [sub_zero] at hlim'
    exact le_of_tendsto_of_tendsto hlim' hs.hasSum.tendsto_sum_nat
      (Eventually.of_forall hpart)
  exact ⟨kh, ⟨⟨hkhF, hcpos, hs⟩, fun k' hk' => (le_csSup hSbdd ⟨k', hk', rfl⟩).trans hWkh⟩⟩


/-- Welfare splits as `W(k) = u(c₀) + β W(tail k)` along admissible paths. -/
theorem Admissible.welfare_eq_head_add {x : ℝ} {k : ℕ → ℝ}
    (hk : Admissible f u β δ x k) :
    welfare f u β δ k = u (consumption f δ k 0) + β * welfare f u β δ (tailPath k) := by
  unfold welfare
  rw [hk.2.2.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, pow_succ, consumption_tail]
  congr 1
  congr 1
  funext t
  ring

/-- The tail of an admissible path is admissible from the stock it reaches. -/
theorem Admissible.tail (P : UPrimitives f u β δ) {x : ℝ} {k : ℕ → ℝ}
    (hk : Admissible f u β δ x k) : Admissible f u β δ (k 1) (tailPath k) := by
  refine ⟨hk.1.tail, fun t => hk.2.1 (t + 1), ?_⟩
  have h := ((summable_nat_add_iff 1).mpr hk.2.2).mul_left β⁻¹
  refine h.congr (fun t => ?_)
  simp only [consumption_tail, pow_succ]
  field_simp [ne_of_gt P.β_pos]

/-- Prepending a first step with positive consumption to an admissible path gives an
admissible path. -/
theorem Admissible.prepend {x y : ℝ} {k : ℕ → ℝ}
    (hk : Admissible f u β δ y k) (hy0 : 0 ≤ y) (hy : y < resources f δ x) :
    Admissible f u β δ x (prependPath x k) := by
  refine ⟨hk.1.prepend hy0 hy.le, fun t => ?_, ?_⟩
  · cases t with
    | zero => rw [consumption_prepend_zero, hk.1.1]; linarith
    | succ t =>
      have := hk.2.1 t
      rwa [← consumption_tail, tail_prepend]
  · refine (summable_nat_add_iff 1).mp ?_
    have h := hk.2.2.mul_left β
    refine h.congr (fun t => ?_)
    rw [← consumption_tail (f := f) (δ := δ) (prependPath x k) t, tail_prepend, pow_succ]
    ring

/-- Welfare of a prepended path. -/
theorem Admissible.welfare_prepend {x y : ℝ} {k : ℕ → ℝ}
    (hk : Admissible f u β δ y k) (hy0 : 0 ≤ y) (hy : y < resources f δ x) :
    welfare f u β δ (prependPath x k) = u (resources f δ x - y) + β * welfare f u β δ k := by
  rw [(hk.prepend hy0 hy).welfare_eq_head_add, consumption_prepend_zero, tail_prepend, hk.1.1]

/-- **Principle of optimality**: the tail of an optimal path is optimal. -/
theorem UOptimal.tail (P : UPrimitives f u β δ) {x : ℝ} {k : ℕ → ℝ}
    (hk : UOptimal f u β δ x k) : UOptimal f u β δ (k 1) (tailPath k) := by
  refine ⟨hk.1.tail P, fun k' hk' => ?_⟩
  by_contra hlt
  push Not at hlt
  have hk1 : 0 ≤ k 1 := (hk.1.1.2 0).1
  have hc0 : consumption f δ k 0 = resources f δ x - k 1 := by simp [consumption, hk.1.1.1]
  have hy : k 1 < resources f δ x := by have := hk.1.2.1 0; linarith
  have hbetter := hk.2 _ (hk'.prepend hk1 hy)
  rw [hk'.welfare_prepend hk1 hy, hk.1.welfare_eq_head_add, hc0] at hbetter
  have := mul_lt_mul_of_pos_left hlt P.β_pos
  linarith

/-- Every shifted tail of an optimal path is optimal. -/
theorem UOptimal.shift (P : UPrimitives f u β δ) {x : ℝ} {k : ℕ → ℝ}
    (hk : UOptimal f u β δ x k) (t : ℕ) : UOptimal f u β δ (k t) (fun s => k (t + s)) := by
  induction t with
  | zero => simpa only [zero_add, hk.1.1.1] using hk
  | succ t ih =>
    have h := ih.tail P
    have heq : tailPath (fun s => k (t + s)) = fun s => k (t + 1 + s) := by
      funext s; simp only [tailPath]; congr 1; ring
    rw [heq] at h
    simpa only [add_zero] using h

/-- Mixtures of admissible paths are admissible and weakly better (strict concavity). -/
theorem Admissible.mix (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) {k k' : ℕ → ℝ}
    (hk : Admissible f u β δ x k) (hk' : Admissible f u β δ x k') :
    Admissible f u β δ x (fun t => 1 / 2 * k t + (1 - 1 / 2) * k' t) ∧
      ((∃ t, consumption f δ k t ≠ consumption f δ k' t) →
        1 / 2 * welfare f u β δ k + (1 - 1 / 2) * welfare f u β δ k' <
          welfare f u β δ (fun t => 1 / 2 * k t + (1 - 1 / 2) * k' t)) := by
  have A := P.aux
  have hθ : (0 : ℝ) < 1 / 2 := by norm_num
  have hθ1 : (1 : ℝ) / 2 < 1 := by norm_num
  obtain ⟨hmixf, hcons⟩ := hk.1.mix A hk'.1 hx.le hx.le hθ hθ1
  have e : 1 / 2 * x + (1 - 1 / 2) * x = x := by ring
  rw [e] at hmixf
  set m := fun t => 1 / 2 * k t + (1 - 1 / 2) * k' t
  have hcm : ∀ t, 0 < consumption f δ m t := fun t => by
    have := hk.2.1 t; have := hk'.2.1 t; have := hcons t; linarith
  have hu : ∀ t, 1 / 2 * u (consumption f δ k t) + (1 - 1 / 2) * u (consumption f δ k' t) ≤
      u (consumption f δ m t) := fun t => by
    have hmix0 : 0 < 1 / 2 * consumption f δ k t + (1 - 1 / 2) * consumption f δ k' t := by
      have := hk.2.1 t; have := hk'.2.1 t; linarith
    have hc := P.u_conc.concaveOn.2 (hk.2.1 t) (hk'.2.1 t) hθ.le
      (show (0 : ℝ) ≤ 1 - 1 / 2 by norm_num) (by norm_num : (1 : ℝ) / 2 + (1 - 1 / 2) = 1)
    simp only [smul_eq_mul] at hc
    exact hc.trans (P.u_strictMono.monotoneOn hmix0 (hcm t) (hcons t))
  have hlo := (hk.2.2.mul_left (1 / 2)).add (hk'.2.2.mul_left (1 - 1 / 2))
  have hgeo := summable_geometric_of_lt_one P.β_pos.le P.β_lt_one
  have hsm : Summable (fun t => β ^ t * u (consumption f δ m t)) := by
    have hup : ∀ t, β ^ t * u (consumption f δ m t) ≤ β ^ t * u (bound A x (t + 1)) := fun t =>
      mul_le_mul_of_nonneg_left (Admissible.u_le P hx.le hmixf hcm t) (pow_pos P.β_pos t).le
    have hdiff : Summable (fun t => β ^ t * u (consumption f δ m t) -
        (1 / 2 * (β ^ t * u (consumption f δ k t)) +
          (1 - 1 / 2) * (β ^ t * u (consumption f δ k' t)))) := by
      refine Summable.of_nonneg_of_le (fun t => ?_) (fun t => ?_)
        (((umajorant_summable P hx).sub hlo))
      · have := mul_le_mul_of_nonneg_left (hu t) (pow_pos P.β_pos t).le; linarith
      · have := hup t; linarith
    exact (hdiff.add hlo).congr (fun t => by ring)
  refine ⟨⟨hmixf, hcm, hsm⟩, fun ⟨t, ht⟩ => ?_⟩
  have hlhs : 1 / 2 * welfare f u β δ k + (1 - 1 / 2) * welfare f u β δ k' =
      ∑' t, (1 / 2 * (β ^ t * u (consumption f δ k t)) +
        (1 - 1 / 2) * (β ^ t * u (consumption f δ k' t))) := by
    unfold welfare
    rw [(hk.2.2.mul_left (1 / 2)).tsum_add (hk'.2.2.mul_left (1 - 1 / 2)), tsum_mul_left,
      tsum_mul_left]
  rw [hlhs]
  refine hlo.tsum_lt_tsum (i := t) (fun s => ?_) ?_ hsm
  · have := mul_le_mul_of_nonneg_left (hu s) (pow_pos P.β_pos s).le; linarith
  · have hmix0 : 0 < 1 / 2 * consumption f δ k t + (1 - 1 / 2) * consumption f δ k' t := by
      have := hk.2.1 t; have := hk'.2.1 t; linarith
    have hs := P.u_conc.2 (hk.2.1 t) (hk'.2.1 t) ht hθ
      (show (0 : ℝ) < 1 - 1 / 2 by norm_num) (by norm_num : (1 : ℝ) / 2 + (1 - 1 / 2) = 1)
    simp only [smul_eq_mul] at hs
    have := hs.trans_le (P.u_strictMono.monotoneOn hmix0 (hcm t) (hcons t))
    have := mul_lt_mul_of_pos_left this (pow_pos P.β_pos t)
    linarith

/-- **Uniqueness of the optimal path** with utility unbounded below. -/
theorem UOptimal.unique (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) {k k' : ℕ → ℝ}
    (hk : UOptimal f u β δ x k) (hk' : UOptimal f u β δ x k') : k = k' := by
  by_contra hne
  have hcne : ∃ t, consumption f δ k t ≠ consumption f δ k' t := by
    by_contra hall
    push Not at hall
    apply hne
    funext t
    induction t with
    | zero => rw [hk.1.1.1, hk'.1.1.1]
    | succ t ih =>
      have := hall t
      simp only [consumption, ih] at this
      linarith
  obtain ⟨hmix, hstrict⟩ := hk.1.mix P hx hk'.1
  have h1 := hk.2 _ hmix
  have h2 := hk'.2 k hk.1
  have h3 := hk.2 k' hk'.1
  have := hstrict hcne
  linarith

/-- The optimal path from `x > 0` (chosen). -/
noncomputable def uoptimalPath (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) : ℕ → ℝ :=
  Classical.choose (exists_optimal P hx)

/-- The chosen path is optimal. -/
theorem uoptimalPath_spec (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) :
    UOptimal f u β δ x (uoptimalPath P hx) :=
  Classical.choose_spec (exists_optimal P hx)

/-- The value function on positive capital. -/
noncomputable def uvalue (P : UPrimitives f u β δ) (x : ℝ) : ℝ :=
  if hx : 0 < x then welfare f u β δ (uoptimalPath P hx) else 0

/-- Any optimal path attains the value. -/
theorem UOptimal.welfare_eq (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : UOptimal f u β δ x k) : welfare f u β δ k = uvalue P x := by
  simp only [uvalue, hx, ↓reduceDIte]
  rw [hk.unique P hx (uoptimalPath_spec P hx)]

/-- **The Bellman inequality**: for `0 < y < F(x)`, `u(F(x) - y) + β V(y) ≤ V(x)`. -/
theorem bellman_le (P : UPrimitives f u β δ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hyF : y < resources f δ x) : u (resources f δ x - y) + β * uvalue P y ≤ uvalue P x := by
  have hky := uoptimalPath_spec P hy
  have h := (uoptimalPath_spec P hx).2 _ (hky.1.prepend hy.le hyF)
  rw [hky.1.welfare_prepend hy.le hyF, hky.welfare_eq P hy,
    (uoptimalPath_spec P hx).welfare_eq P hx] at h
  exact h

/-- **The Bellman equation** along an optimal path. -/
theorem UOptimal.bellman_eq (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : UOptimal f u β δ x k) (t : ℕ) :
    uvalue P (k t) = u (resources f δ (k t) - k (t + 1)) + β * uvalue P (k (t + 1)) := by
  have hs := hk.shift P t
  have hkt := hk.1.capital_pos P hx t
  have hkt1 := hk.1.capital_pos P hx (t + 1)
  have ht := hs.tail P
  rw [← hs.welfare_eq P hkt, hs.1.welfare_eq_head_add, ← ht.welfare_eq P hkt1]
  simp only [consumption, add_zero]

/-- **The Euler equation** (O&R (20)/(24)) along an optimal path, utility unbounded below. -/
theorem UOptimal.euler (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : UOptimal f u β δ x k) (t : ℕ) :
    deriv u (consumption f δ k t) =
      β * deriv u (consumption f δ k (t + 1)) * (deriv f (k (t + 1)) + (1 - δ)) := by
  have A := P.aux
  have hkt := hk.1.capital_pos P hx t
  have hkt1 := hk.1.capital_pos P hx (t + 1)
  have hkt2 := hk.1.capital_pos P hx (t + 2)
  have hct := hk.1.2.1 t
  have hct1 := hk.1.2.1 (t + 1)
  set ψ : ℝ → ℝ := fun y => u (resources f δ (k t) - y) +
    β * (u (resources f δ y - k (t + 2)) + β * uvalue P (k (t + 2)))
  have hct' : 0 < resources f δ (k t) - k (t + 1) := hct
  have hct1' : 0 < resources f δ (k (t + 1)) - k (t + 2) := hct1
  have hloc : IsLocalMax ψ (k (t + 1)) := by
    have hFc : ContinuousAt (resources f δ) (k (t + 1)) :=
      (hasDerivAt_resources A hkt1).continuousAt
    have hnear : ∀ᶠ y in 𝓝 (k (t + 1)), 0 < y ∧ y < resources f δ (k t) ∧
        k (t + 2) < resources f δ y := by
      refine (lt_mem_nhds hkt1).and
        ((gt_mem_nhds (by linarith : k (t + 1) < resources f δ (k t))).and ?_)
      exact hFc.eventually (lt_mem_nhds (by linarith : k (t + 2) < resources f δ (k (t + 1))))
    filter_upwards [hnear] with y hy
    obtain ⟨hypos, hyF, hy2⟩ := hy
    have hbt := hk.bellman_eq P hx t
    have hbt1 := hk.bellman_eq P hx (t + 1)
    have hin1 := bellman_le P hypos hkt2 hy2
    have hin0 := bellman_le P hkt hypos hyF
    have := mul_le_mul_of_nonneg_left hin1 P.β_pos.le
    simp only [ψ]
    rw [show t + 1 + 1 = t + 2 by ring] at hbt1
    have hbt1' : β * uvalue P (k (t + 1)) = β * (u (resources f δ (k (t + 1)) - k (t + 2)) +
        β * uvalue P (k (t + 2))) := by rw [hbt1]
    linarith
  have hd1 : HasDerivAt (fun y => u (resources f δ (k t) - y))
      (deriv u (resources f δ (k t) - k (t + 1)) * (-1)) (k (t + 1)) :=
    (P.u_diff _ hct').hasDerivAt.comp (k (t + 1)) ((hasDerivAt_id (k (t + 1))).const_sub _)
  have hd2 : HasDerivAt (fun y => u (resources f δ y - k (t + 2)))
      (deriv u (resources f δ (k (t + 1)) - k (t + 2)) * (deriv f (k (t + 1)) + (1 - δ)))
      (k (t + 1)) :=
    (P.u_diff _ hct1').hasDerivAt.comp (k (t + 1)) ((hasDerivAt_resources A hkt1).sub_const _)
  have hd := hd1.add ((hd2.add_const (β * uvalue P (k (t + 2)))).const_mul β)
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hc0 : consumption f δ k t = resources f δ (k t) - k (t + 1) := rfl
  have hc1 : consumption f δ k (t + 1) = resources f δ (k (t + 1)) - k (t + 2) := rfl
  rw [hc0, hc1]
  linarith

/-- The policy function: next period's capital on the optimal path from `x > 0`. -/
noncomputable def upolicy (P : UPrimitives f u β δ) (x : ℝ) : ℝ :=
  if hx : 0 < x then uoptimalPath P hx 1 else 0

/-- Every optimal path follows the policy. -/
theorem UOptimal.succ_eq_policy (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : UOptimal f u β δ x k) (t : ℕ) : k (t + 1) = upolicy P (k t) := by
  have hkt := hk.1.capital_pos P hx t
  have hs := hk.shift P t
  have heq := hs.unique P hkt (uoptimalPath_spec P hkt)
  simp only [upolicy, hkt, ↓reduceDIte]
  exact congrFun heq 1

/-- The policy is interior and satisfies the date-zero Euler equation. -/
theorem upolicy_interior (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) :
    0 < upolicy P x ∧ upolicy P x < resources f δ x ∧
      uvalue P x = u (resources f δ x - upolicy P x) + β * uvalue P (upolicy P x) ∧
      deriv u (resources f δ x - upolicy P x) =
        β * deriv u (resources f δ (upolicy P x) - upolicy P (upolicy P x)) *
          (deriv f (upolicy P x) + (1 - δ)) := by
  have hk := uoptimalPath_spec P hx
  have h1 := hk.1.capital_pos P hx 1
  have hc := hk.1.2.1 0
  have he := hk.euler P hx 0
  have hb := hk.bellman_eq P hx 0
  have hs0 := hk.succ_eq_policy P hx 0
  have hs1 := hk.succ_eq_policy P hx 1
  have h0 : uoptimalPath P hx 0 = x := hk.1.1.1
  simp only [consumption, zero_add] at hc he h1 hs0 hs1 hb
  rw [h0] at hs0 hc he hb
  rw [hs0] at h1 hc he hs1 hb
  rw [hs1] at he
  exact ⟨h1, by linarith, hb, he⟩

/-- Shifting an interval right lowers the increment of `u` (strict concavity on `(0, ∞)`). -/
theorem shift_increment_lt (P : UPrimitives f u β δ) {a b Δ : ℝ} (ha : 0 < a) (hab : a < b)
    (hΔ : 0 < Δ) : u (b + Δ) - u (a + Δ) < u b - u a := by
  have hs1 := P.u_conc.secant_strict_mono (a := a) (x := b) (y := b + Δ) (mem_Ioi.mpr ha)
    (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr (by linarith)) (ne_of_gt hab)
    (by linarith) (by linarith)
  have hs2 := P.u_conc.secant_strict_mono (a := b + Δ) (x := a) (y := a + Δ)
    (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr ha) (mem_Ioi.mpr (by linarith)) (by linarith)
    (by linarith) (by linarith)
  have hL : 0 < b - a := sub_pos.mpr hab
  have e1 : (u (a + Δ) - u (b + Δ)) / (a + Δ - (b + Δ)) = (u (b + Δ) - u (a + Δ)) / (b - a) := by
    rw [show a + Δ - (b + Δ) = -(b - a) by ring, div_neg, ← neg_div]
    ring_nf
  have e2 : (u a - u (b + Δ)) / (a - (b + Δ)) = (u (b + Δ) - u a) / (b + Δ - a) := by
    rw [show a - (b + Δ) = -(b + Δ - a) by ring, div_neg, ← neg_div]
    ring_nf
  rw [e1, e2] at hs2
  have h := hs2.trans hs1
  rwa [div_lt_div_iff_of_pos_right hL] at h

/-- **The policy is strictly increasing** (utility unbounded below). -/
theorem upolicy_strictMono (P : UPrimitives f u β δ) : StrictMonoOn (upolicy P) (Ioi 0) := by
  have A := P.aux
  intro x hx x' hx' hxx
  have hx0 : (0 : ℝ) < x := hx
  have hx0' : (0 : ℝ) < x' := hx'
  obtain ⟨hy0, hyF, hb1, he⟩ := upolicy_interior P hx0
  obtain ⟨hy0', hyF', hb2, he'⟩ := upolicy_interior P hx0'
  have hFF := A.resources_strictMono (mem_Ici.mpr hx0.le) (mem_Ici.mpr hx0'.le) hxx
  have hweak : upolicy P x ≤ upolicy P x' := by
    by_contra hlt
    push Not at hlt
    have h1 := bellman_le P hx0 hy0' (hlt.trans hyF)
    have h2 := bellman_le P hx0' hy0 (hyF.trans hFF)
    have hinc := shift_increment_lt P (a := resources f δ x - upolicy P x)
      (b := resources f δ x - upolicy P x') (Δ := resources f δ x' - resources f δ x)
      (by linarith) (by linarith) (by linarith)
    rw [show resources f δ x - upolicy P x' + (resources f δ x' - resources f δ x) =
        resources f δ x' - upolicy P x' by ring,
      show resources f δ x - upolicy P x + (resources f δ x' - resources f δ x) =
        resources f δ x' - upolicy P x by ring] at hinc
    linarith
  rcases lt_or_eq_of_le hweak with hlt | heq
  · exact hlt
  · exfalso
    rw [← heq] at he' hyF'
    have hu : deriv u (resources f δ x - upolicy P x) =
        deriv u (resources f δ x' - upolicy P x) := by rw [he, he']
    have hc : 0 < resources f δ x - upolicy P x := by linarith
    have hc' : 0 < resources f δ x' - upolicy P x := by linarith
    have := P.u_prime_anti.injOn hc hc' hu
    linarith

/-- An optimal path is monotone. -/
theorem UOptimal.monotone_or_antitone (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x)
    {k : ℕ → ℝ} (hk : UOptimal f u β δ x k) :
    (k 0 ≤ k 1 → Monotone k) ∧ (k 1 ≤ k 0 → Antitone k) := by
  have hpos : ∀ t, 0 < k t := fun t => hk.1.capital_pos P hx t
  have hsucc := hk.succ_eq_policy P hx
  constructor
  · intro h01
    apply monotone_nat_of_le_succ
    intro t
    induction t with
    | zero => exact h01
    | succ t ih =>
      calc k (t + 1) = upolicy P (k t) := hsucc t
        _ ≤ upolicy P (k (t + 1)) := (upolicy_strictMono P).monotoneOn (hpos t) (hpos (t + 1)) ih
        _ = k (t + 1 + 1) := (hsucc (t + 1)).symm
  · intro h10
    apply antitone_nat_of_succ_le
    intro t
    induction t with
    | zero => exact h10
    | succ t ih =>
      calc k (t + 1 + 1) = upolicy P (k (t + 1)) := hsucc (t + 1)
        _ ≤ upolicy P (k t) := (upolicy_strictMono P).monotoneOn (hpos (t + 1)) (hpos t) ih
        _ = k (t + 1) := (hsucc t).symm

/-- **Optimal paths are bounded by `max(x, k*)`** (utility unbounded below, any `δ ≥ 0`):
a path that keeps rising above `k*` has falling consumption and is beaten by holding capital
constant. -/
theorem UOptimal.le_max (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : UOptimal f u β δ x k) (t : ℕ) : k t ≤ max x (steady P.aux) := by
  have A := P.aux
  have hpos : ∀ t, 0 < k t := fun t => hk.1.capital_pos P hx t
  have hcpos : ∀ t, 0 < consumption f δ k t := hk.1.2.1
  have hsucc := hk.succ_eq_policy P hx
  obtain ⟨hmono, hanti⟩ := hk.monotone_or_antitone P hx
  obtain ⟨hks, hkd⟩ := steady_spec A
  rcases le_total (k 0) (k 1) with h01 | h10
  swap
  · exact ((hanti h10) (Nat.zero_le t)).trans (by rw [hk.1.1.1]; exact le_max_left _ _)
  by_contra hgt
  push Not at hgt
  have hT : steady A < k t := lt_of_le_of_lt (le_max_right _ _) hgt
  have hfall : ∀ s, steady A < k (s + 1) →
      consumption f δ k (s + 1) < consumption f δ k s := by
    intro s hs
    have he := hk.euler P hx s
    have hfd : deriv f (k (s + 1)) < deriv f (steady A) :=
      (production_deriv_strictAnti f P.f_conc P.f_diff) hks (hpos (s + 1)) hs
    have hg : β * (deriv f (k (s + 1)) + (1 - δ)) < 1 := by
      have := steady_euler A; nlinarith [P.β_pos]
    by_contra hle
    push Not at hle
    have hu := P.u_prime_anti.antitoneOn (hcpos s) (hcpos (s + 1)) hle
    have hup := P.u_prime_pos _ (hcpos (s + 1))
    have hFp := hasDerivAt_resources_pos A (hpos (s + 1))
    nlinarith
  by_cases hstrict : ∃ t0, t ≤ t0 ∧ k t0 < k (t0 + 1)
  · obtain ⟨t0, ht0, hlt0⟩ := hstrict
    have hinc : ∀ s, k (t0 + s) < k (t0 + s + 1) := by
      intro s
      induction s with
      | zero => simpa using hlt0
      | succ s ih =>
        rw [show t0 + (s + 1) = t0 + s + 1 by ring]
        calc k (t0 + s + 1) = upolicy P (k (t0 + s)) := hsucc _
          _ < upolicy P (k (t0 + s + 1)) := upolicy_strictMono P (hpos _) (hpos _) ih
          _ = k (t0 + s + 1 + 1) := (hsucc _).symm
    have habove : ∀ s, steady A < k (t0 + s + 1) := by
      intro s
      have hmon := hmono h01 (show t ≤ t0 + s + 1 by omega)
      linarith
    have hcle : ∀ s, consumption f δ k (t0 + s) ≤ consumption f δ k t0 := by
      intro s
      induction s with
      | zero => simp
      | succ s ih =>
        have := hfall (t0 + s) (habove s)
        rw [show t0 + (s + 1) = t0 + s + 1 by ring]
        linarith
    set y := k t0
    have hsT := hk.shift P t0
    have hgap : consumption f δ k t0 < resources f δ y - y := by
      simp only [consumption, y]; linarith [hinc 0]
    have hcy : 0 < resources f δ y - y := lt_trans (hcpos t0) hgap
    have hgeo := summable_geometric_of_lt_one P.β_pos.le P.β_lt_one
    have hz : Admissible f u β δ y (fun _ => y) :=
      ⟨⟨rfl, fun _ => ⟨(hpos t0).le, by linarith⟩⟩, fun _ => hcy,
        (hgeo.mul_right (u (resources f δ y - y))).congr (fun _ => rfl)⟩
    have hzc : ∀ s, consumption f δ (fun _ => y) s = resources f δ y - y := fun _ => rfl
    have hle := hsT.2 _ hz
    have hlt : welfare f u β δ (fun s => k (t0 + s)) < welfare f u β δ (fun _ => y) := by
      refine hsT.1.2.2.tsum_lt_tsum (i := 0) (fun s => ?_) ?_ hz.2.2
      · rw [hzc]
        refine mul_le_mul_of_nonneg_left (P.u_strictMono.monotoneOn
          (hcpos _) hcy ?_) (pow_pos P.β_pos s).le
        have := hcle s
        change consumption f δ k (t0 + s) ≤ _
        linarith
      · rw [hzc]
        simp only [pow_zero, one_mul]
        exact P.u_strictMono (hcpos _) hcy
          (by change consumption f δ k (t0 + 0) < _; simpa using hgap)
    linarith
  · push Not at hstrict
    have hconst : k (t + 1) = k t := le_antisymm (hstrict t le_rfl) (hmono h01 (Nat.le_succ t))
    have hconst2 : k (t + 2) = k (t + 1) :=
      le_antisymm (hstrict (t + 1) (Nat.le_succ t)) (hmono h01 (Nat.le_succ _))
    have he := hk.euler P hx t
    have hc : consumption f δ k (t + 1) = consumption f δ k t := by
      simp only [consumption, hconst, hconst2]
    rw [hc] at he
    have hup := P.u_prime_pos _ (hcpos t)
    have hβ1 : β * (deriv f (k (t + 1)) + (1 - δ)) = 1 := by
      have : deriv u (consumption f δ k t) * (β * (deriv f (k (t + 1)) + (1 - δ)) - 1) = 0 := by
        linear_combination -he
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (ne_of_gt hup)
      · linarith
    have hfd : deriv f (k (t + 1)) < deriv f (steady A) :=
      (production_deriv_strictAnti f P.f_conc P.f_diff) hks (hpos _) (by rw [hconst]; exact hT)
    have := steady_euler A
    nlinarith [P.β_pos]

/-- **Convergence to the steady state** with utility unbounded below: every optimal path
from `x > 0` converges to the unique `k*` with `β (f'(k*) + 1 - δ) = 1`. -/
theorem UOptimal.tendsto (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : UOptimal f u β δ x k) : Tendsto k atTop (𝓝 (steady P.aux)) := by
  have A := P.aux
  have hpos : ∀ t, 0 < k t := fun t => hk.1.capital_pos P hx t
  have hcpos : ∀ t, 0 < consumption f δ k t := hk.1.2.1
  have hbd : ∀ t, k t ≤ max x (steady P.aux) := fun t => hk.le_max P hx t
  obtain ⟨hmono, hanti⟩ := hk.monotone_or_antitone P hx
  obtain ⟨L, hL⟩ : ∃ L, Tendsto k atTop (𝓝 L) := by
    rcases le_total (k 0) (k 1) with h | h
    · exact ⟨_, tendsto_atTop_ciSup (hmono h) ⟨max x (steady P.aux), by
        rintro _ ⟨t, rfl⟩; exact hbd t⟩⟩
    · exact ⟨_, tendsto_atTop_ciInf (hanti h) ⟨0, by rintro _ ⟨t, rfl⟩; exact (hpos t).le⟩⟩
  have hL0 : 0 ≤ L := ge_of_tendsto' hL (fun t => (hpos t).le)
  have hshift : Tendsto (fun t => k (t + 1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)
  have hFcont : ContinuousWithinAt (resources f δ) (Ici 0) L := A.resources_cont L hL0
  have hFk : Tendsto (fun t => resources f δ (k t)) atTop (𝓝 (resources f δ L)) :=
    hFcont.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hL, Eventually.of_forall
      (fun t => mem_Ici.mpr (hpos t).le)⟩)
  have hc : Tendsto (consumption f δ k) atTop (𝓝 (resources f δ L - L)) := hFk.sub hshift
  have hLF : L ≤ resources f δ L :=
    le_of_tendsto_of_tendsto hshift hFk (Eventually.of_forall (fun t => (hk.1.1.2 t).2))
  obtain ⟨hks, hkd⟩ := steady_spec A
  rcases hL0.eq_or_lt with hL00 | hLpos
  · exfalso
    subst hL00
    have hk0 : Tendsto (fun t => k (t + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hshift, Eventually.of_forall (fun t => hpos (t + 1))⟩
    have hbig := (P.f_inada0.comp hk0).eventually (eventually_gt_atTop (1 / β - (1 - δ)))
    obtain ⟨T, hT⟩ := eventually_atTop.mp hbig
    have hrise : ∀ t, T ≤ t → consumption f δ k t < consumption f δ k (t + 1) := by
      intro t ht
      have he := hk.euler P hx t
      have hg : 1 < β * (deriv f (k (t + 1)) + (1 - δ)) := by
        have h := hT t ht
        simp only [Function.comp_apply] at h
        have := mul_lt_mul_of_pos_left h P.β_pos
        rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt P.β_pos)] at this
        nlinarith
      by_contra hle
      push Not at hle
      have hu := P.u_prime_anti.antitoneOn (hcpos (t + 1)) (hcpos t) hle
      have hup := P.u_prime_pos _ (hcpos (t + 1))
      have : deriv u (consumption f δ k (t + 1)) <
          β * deriv u (consumption f δ k (t + 1)) * (deriv f (k (t + 1)) + (1 - δ)) := by
        nlinarith
      linarith
    have hge : ∀ n, consumption f δ k T ≤ consumption f δ k (T + n) := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n ih => exact ih.trans (hrise (T + n) (by omega)).le
    rw [resources_zero A, sub_zero] at hc
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hc.eventually (gt_mem_nhds (hcpos T)))
    have := hN (T + N) (by omega)
    have := hge N
    linarith
  rcases lt_or_eq_of_le hLF with hFL | hFL
  · have hcL : 0 < resources f δ L - L := sub_pos.mpr hFL
    have huc : ContinuousAt (deriv u) (resources f δ L - L) :=
      P.u_prime_cont.continuousAt (Ioi_mem_nhds hcL)
    have hfc : ContinuousAt (deriv f) L := P.f_prime_cont.continuousAt (Ioi_mem_nhds hLpos)
    have hlhs := huc.tendsto.comp hc
    have hrhs := ((huc.tendsto.comp (hc.comp (tendsto_add_atTop_nat 1))).const_mul β).mul
      ((hfc.tendsto.comp hshift).add_const (1 - δ))
    have heq : deriv u (resources f δ L - L) =
        β * deriv u (resources f δ L - L) * (deriv f L + (1 - δ)) :=
      tendsto_nhds_unique hlhs (hrhs.congr (fun t => by
        simp only [Function.comp_apply]
        exact (hk.euler P hx t).symm))
    have hup := P.u_prime_pos _ hcL
    have hβ : β * (deriv f L + (1 - δ)) = 1 := by
      have : deriv u (resources f δ L - L) * (β * (deriv f L + (1 - δ)) - 1) = 0 := by
        linear_combination -heq
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (ne_of_gt hup)
      · linarith
    have hfL : deriv f L = 1 / β - (1 - δ) := by
      field_simp [ne_of_gt P.β_pos]
      linarith
    have := A.existsUnique_steady.unique ⟨hLpos, hfL⟩ ⟨hks, hkd⟩
    rw [this] at hL
    exact hL
  · exfalso
    rw [← hFL, sub_self] at hc
    have hLks : steady A < L := by
      have hfL : f L = δ * L := by simp only [resources] at hFL; linarith
      have hgap := marginal_product_times_capital_lt_output f L P.f_conc P.f_zero hLpos
        (P.f_diff L hLpos)
      rw [hfL] at hgap
      have hdL : deriv f L < δ := by nlinarith
      by_contra hle
      push Not at hle
      have := (production_deriv_strictAnti f P.f_conc P.f_diff).antitoneOn hLpos hks hle
      rw [hkd] at this
      have h1 : 1 < 1 / β := by rw [lt_div_iff₀ P.β_pos]; linarith [P.β_lt_one]
      linarith
    have hcs : 0 < resources f δ (steady A) - steady A := steady_consumption_pos A
    set cs := resources f δ (steady A) - steady A with hcs_def
    obtain ⟨T, hT⟩ := eventually_atTop.mp ((hL.eventually (lt_mem_nhds hLks)).and
      (hc.eventually (gt_mem_nhds (half_pos hcs))))
    set z : ℕ → ℝ := fun s => if s = 0 then k T else steady A
    have hFmono : resources f δ (steady A) ≤ resources f δ (k T) :=
      A.resources_strictMono.monotoneOn (mem_Ici.mpr hks.le) (mem_Ici.mpr (hpos T).le)
        (hT T le_rfl).1.le
    have hFT : steady A < resources f δ (k T) := by linarith
    have hzF : Feasible f δ (k T) z := by
      refine ⟨rfl, fun s => ⟨?_, ?_⟩⟩
      · simp only [z, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]; exact hks.le
      · rcases s with _ | s
        · simp only [z, zero_add, one_ne_zero, ↓reduceIte]; exact hFT.le
        · simp only [z, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]; linarith
    have hzc0 : consumption f δ z 0 = resources f δ (k T) - steady A := by simp [consumption, z]
    have hzc1 : ∀ s, consumption f δ z (s + 1) = cs := by intro s; simp [consumption, z, cs]
    have hzc : ∀ s, cs ≤ consumption f δ z s := by
      intro s
      rcases s with _ | s
      · rw [hzc0]; linarith
      · rw [hzc1]
    have hgeo := summable_geometric_of_lt_one P.β_pos.le P.β_lt_one
    have hzadm : Admissible f u β δ (k T) z := by
      refine ⟨hzF, fun s => lt_of_lt_of_le hcs (hzc s), ?_⟩
      refine Summable.of_norm_bounded (hgeo.mul_right
        (|u (resources f δ (k T) - steady A)| + |u cs|)) (fun s => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos P.β_pos s)]
      refine mul_le_mul_of_nonneg_left ?_ (pow_pos P.β_pos s).le
      rcases s with _ | s
      · rw [hzc0]; linarith [abs_nonneg (u cs)]
      · rw [hzc1]; linarith [abs_nonneg (u (resources f δ (k T) - steady A))]
    have hsT := hk.shift P T
    have hle := hsT.2 z hzadm
    have hshc : ∀ s, consumption f δ (fun s => k (T + s)) s ≤ cs / 2 := fun s =>
      (hT (T + s) (by omega)).2.le
    have hshp : ∀ s, 0 < consumption f δ (fun s => k (T + s)) s := hsT.1.2.1
    have h1 : welfare f u β δ (fun s => k (T + s)) ≤ ∑' s, β ^ s * u (cs / 2) :=
      hsT.1.2.2.tsum_le_tsum (fun s => mul_le_mul_of_nonneg_left
        (P.u_strictMono.monotoneOn (hshp s) (half_pos hcs) (hshc s))
        (pow_pos P.β_pos s).le) (hgeo.mul_right _)
    have h2 : ∑' s, β ^ s * u (cs / 2) < ∑' s, β ^ s * u cs :=
      (hgeo.mul_right _).tsum_lt_tsum (i := 0) (fun s => mul_le_mul_of_nonneg_left
        (P.u_strictMono.monotoneOn (half_pos hcs) hcs (half_le_self hcs.le))
        (pow_pos P.β_pos s).le)
        (by
          simp only [pow_zero, one_mul]
          exact P.u_strictMono (half_pos hcs) hcs (half_lt_self hcs))
        (hgeo.mul_right _)
    have h3 : ∑' s, β ^ s * u cs ≤ welfare f u β δ z :=
      (hgeo.mul_right _).tsum_le_tsum (fun s => mul_le_mul_of_nonneg_left
        (P.u_strictMono.monotoneOn hcs (lt_of_lt_of_le hcs (hzc s)) (hzc s))
        (pow_pos P.β_pos s).le) hzadm.2.2
    linarith

/-- Consumption converges to `c* = F(k*) - k*`. -/
theorem UOptimal.consumption_tendsto (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x)
    {k : ℕ → ℝ} (hk : UOptimal f u β δ x k) :
    Tendsto (consumption f δ k) atTop (𝓝 (resources f δ (steady P.aux) - steady P.aux)) := by
  have hL := hk.tendsto P hx
  have hks := (steady_spec P.aux).1
  have hFk : Tendsto (fun t => resources f δ (k t)) atTop
      (𝓝 (resources f δ (steady P.aux))) :=
    (P.aux.resources_cont _ (mem_Ici.mpr hks.le)).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hL, Eventually.of_forall (fun t => mem_Ici.mpr (hk.1.capital_pos P hx t).le)⟩)
  exact hFk.sub (hL.comp (tendsto_add_atTop_nat 1))

/-- **Monotone dynamics below the steady state** (utility unbounded below): capital and
consumption rise strictly and capital never reaches `k*`. -/
theorem UOptimal.dynamics_below (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : UOptimal f u β δ x k) (hlt : x < steady P.aux) :
    StrictMono k ∧ (∀ t, k t < steady P.aux) ∧ StrictMono (consumption f δ k) := by
  have hpos : ∀ t, 0 < k t := fun t => hk.1.capital_pos P hx t
  have hL := hk.tendsto P hx
  obtain ⟨hmono, hanti⟩ := hk.monotone_or_antitone P hx
  have hsucc := hk.succ_eq_policy P hx
  have h01 : k 0 < k 1 := by
    by_contra hle
    push Not at hle
    have hlim := le_of_tendsto' hL (fun t => (hanti hle) (Nat.zero_le t))
    rw [hk.1.1.1] at hlim
    linarith
  have hsm : StrictMono k := by
    apply strictMono_nat_of_lt_succ
    intro t
    induction t with
    | zero => exact h01
    | succ t ih =>
      calc k (t + 1) = upolicy P (k t) := hsucc t
        _ < upolicy P (k (t + 1)) := upolicy_strictMono P (hpos t) (hpos (t + 1)) ih
        _ = k (t + 1 + 1) := (hsucc (t + 1)).symm
  have hbelow : ∀ t, k t < steady P.aux := fun t =>
    (hsm (Nat.lt_succ_self t)).trans_le (ge_of_tendsto hL (eventually_atTop.mpr
      ⟨t + 1, fun s hs => hsm.monotone hs⟩))
  refine ⟨hsm, hbelow, strictMono_nat_of_lt_succ (fun t => ?_)⟩
  have he := hk.euler P hx t
  have hks := steady_spec P.aux
  have hfd : deriv f (steady P.aux) < deriv f (k (t + 1)) :=
    (production_deriv_strictAnti f P.f_conc P.f_diff) (hpos (t + 1)) hks.1 (hbelow (t + 1))
  have hg : 1 < β * (deriv f (k (t + 1)) + (1 - δ)) := by
    have := steady_euler P.aux
    nlinarith [P.β_pos]
  have hcpos := hk.1.2.1
  by_contra hle
  push Not at hle
  have hu := P.u_prime_anti.antitoneOn (hcpos (t + 1)) (hcpos t) hle
  have hup := P.u_prime_pos _ (hcpos (t + 1))
  nlinarith

/-- **Monotone dynamics above the steady state** (utility unbounded below). -/
theorem UOptimal.dynamics_above (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : UOptimal f u β δ x k) (hgt : steady P.aux < x) :
    StrictAnti k ∧ (∀ t, steady P.aux < k t) ∧ StrictAnti (consumption f δ k) := by
  have hpos : ∀ t, 0 < k t := fun t => hk.1.capital_pos P hx t
  have hL := hk.tendsto P hx
  obtain ⟨hmono, hanti⟩ := hk.monotone_or_antitone P hx
  have hsucc := hk.succ_eq_policy P hx
  have h10 : k 1 < k 0 := by
    by_contra hle
    push Not at hle
    have hlim := ge_of_tendsto' hL (fun t => (hmono hle) (Nat.zero_le t))
    rw [hk.1.1.1] at hlim
    linarith
  have hsa : StrictAnti k := by
    apply strictAnti_nat_of_succ_lt
    intro t
    induction t with
    | zero => exact h10
    | succ t ih =>
      calc k (t + 1 + 1) = upolicy P (k (t + 1)) := hsucc (t + 1)
        _ < upolicy P (k t) := upolicy_strictMono P (hpos (t + 1)) (hpos t) ih
        _ = k (t + 1) := (hsucc t).symm
  have habove : ∀ t, steady P.aux < k t := fun t =>
    lt_of_le_of_lt (le_of_tendsto hL (eventually_atTop.mpr
      ⟨t + 1, fun s hs => hsa.antitone hs⟩)) (hsa (Nat.lt_succ_self t))
  refine ⟨hsa, habove, strictAnti_nat_of_succ_lt (fun t => ?_)⟩
  have he := hk.euler P hx t
  have hks := steady_spec P.aux
  have hfd : deriv f (k (t + 1)) < deriv f (steady P.aux) :=
    (production_deriv_strictAnti f P.f_conc P.f_diff) hks.1 (hpos (t + 1)) (habove (t + 1))
  have hg : β * (deriv f (k (t + 1)) + (1 - δ)) < 1 := by
    have := steady_euler P.aux
    nlinarith [P.β_pos]
  have hcpos := hk.1.2.1
  by_contra hle
  push Not at hle
  have hu := P.u_prime_anti.antitoneOn (hcpos t) (hcpos (t + 1)) hle
  have hup := P.u_prime_pos _ (hcpos (t + 1))
  have hFp := hasDerivAt_resources_pos P.aux (hpos (t + 1))
  nlinarith

/-- **Transversality is necessary** (utility unbounded below): along the optimal path
`βᵗ u'(c_t) k_{t+1} → 0`. -/
theorem UOptimal.tvc (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : UOptimal f u β δ x k) :
    Tendsto (fun t => β ^ t * deriv u (consumption f δ k t) * k (t + 1)) atTop (𝓝 0) := by
  have hcs := steady_consumption_pos P.aux
  have huc : ContinuousAt (deriv u) (resources f δ (steady P.aux) - steady P.aux) :=
    P.u_prime_cont.continuousAt (Ioi_mem_nhds hcs)
  have h1 := huc.tendsto.comp (hk.consumption_tendsto P hx)
  have h2 := (hk.tendsto P hx).comp (tendsto_add_atTop_nat 1)
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one P.β_pos.le P.β_lt_one
  have := (h0.mul h1).mul h2
  rw [zero_mul, zero_mul] at this
  exact this

/-- **Euler plus transversality are sufficient** (utility unbounded below), in the strong
partial-sum form: if a feasible path with positive capital and consumption satisfies the
Euler equation and transversality, then against *every* feasible rival with positive
consumption (summable or not), `limsup_T ∑_{t≤T} βᵗ [u(c'_t) - u(c_t)] ≤ 0`; in particular
the path is optimal among admissible paths. -/
theorem euler_tvc_sufficient (P : UPrimitives f u β δ) {x : ℝ} {k : ℕ → ℝ}
    (hk : Feasible f δ x k) (hkpos : ∀ t, 0 < k t) (hcpos : ∀ t, 0 < consumption f δ k t)
    (heuler : ∀ t, deriv u (consumption f δ k t) =
      β * deriv u (consumption f δ k (t + 1)) * (deriv f (k (t + 1)) + (1 - δ)))
    (htvc : Tendsto (fun t => β ^ t * deriv u (consumption f δ k t) * k (t + 1)) atTop (𝓝 0))
    {k' : ℕ → ℝ} (hk' : Feasible f δ x k') (hc' : ∀ t, 0 < consumption f δ k' t) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∑ t ∈ Finset.range (T + 1),
      β ^ t * (u (consumption f δ k' t) - u (consumption f δ k t)) ≤ ε := by
  intro ε hε
  have hbound := partial_sum_le_of_euler (S := Ioi 0) P.u_conc.concaveOn
    P.aux.resources_concave hk hk' hkpos hcpos hc'
    (fun t => (P.u_diff _ (hcpos t)).hasDerivAt) (fun t => hasDerivAt_resources P.aux (hkpos t))
    (fun t => (P.u_prime_pos _ (hcpos t)).le) P.β_pos.le heuler
  filter_upwards [htvc.eventually (gt_mem_nhds hε)] with T hT
  have h := hbound T
  have hk'1 : 0 ≤ k' (T + 1) := (hk'.2 T).1
  have hm := mul_nonneg (mul_nonneg (pow_nonneg P.β_pos.le T)
    (P.u_prime_pos _ (hcpos T)).le) hk'1
  nlinarith

/-- Euler plus transversality imply optimality among admissible paths (unbounded utility). -/
theorem uoptimal_of_euler_tvc (P : UPrimitives f u β δ) {x : ℝ} {k : ℕ → ℝ}
    (hk : Admissible f u β δ x k) (hkpos : ∀ t, 0 < k t)
    (heuler : ∀ t, deriv u (consumption f δ k t) =
      β * deriv u (consumption f δ k (t + 1)) * (deriv f (k (t + 1)) + (1 - δ)))
    (htvc : Tendsto (fun t => β ^ t * deriv u (consumption f δ k t) * k (t + 1)) atTop (𝓝 0)) :
    UOptimal f u β δ x k := by
  refine ⟨hk, fun k' hk' => ?_⟩
  have hs := hk'.2.2.sub hk.2.2
  have hlim := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hle : ∀ ε > 0, ∑' t, (β ^ t * u (consumption f δ k' t) -
      β ^ t * u (consumption f δ k t)) ≤ ε := by
    intro ε hε
    refine le_of_tendsto hlim ?_
    filter_upwards [euler_tvc_sufficient P hk.1 hkpos hk.2.1 heuler htvc hk'.1 hk'.2.1 ε hε]
      with T hT
    simp only [Function.comp_apply, ← mul_sub]
    exact hT
  have h0 : ∑' t, (β ^ t * u (consumption f δ k' t) - β ^ t * u (consumption f δ k t)) ≤ 0 :=
    le_of_forall_pos_le_add (fun ε hε => by linarith [hle ε hε])
  rw [welfare, welfare]
  have e := hk'.2.2.tsum_sub hk.2.2
  linarith

/-- **Euler plus transversality characterise the optimum** with log or `σ < 1` utility. -/
theorem uoptimal_iff_euler_tvc (P : UPrimitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : Admissible f u β δ x k) :
    UOptimal f u β δ x k ↔
      (∀ t, deriv u (consumption f δ k t) =
        β * deriv u (consumption f δ k (t + 1)) * (deriv f (k (t + 1)) + (1 - δ))) ∧
      Tendsto (fun t => β ^ t * deriv u (consumption f δ k t) * k (t + 1)) atTop (𝓝 0) :=
  ⟨fun h => ⟨h.euler P hx, h.tvc P hx⟩, fun ⟨he, ht⟩ =>
    uoptimal_of_euler_tvc P hk (hk.capital_pos P hx) he ht⟩

/-! ### Log and `σ < 1` utility in the book's model -/

/-- **Log utility satisfies the hypotheses** (O&R (21) with `σ = 1`, and (29)). -/
theorem log_uprimitives (hT : Technology f) {β z : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hδ1 : δ ≤ 1) (hzd : 0 ≤ z + δ) (hz : 0 < 1 + z) :
    UPrimitives (effF f z) (effU Real.log z) β (effDelta z δ) := by
  have hP := toPrimitives hT (crra_preferences (θ := 1 / 2) (by norm_num) (by norm_num)) hβ
    hβ1 hδ1 hzd hz
  have hderiv : ∀ c, 0 < c → deriv (effU Real.log z) c = c⁻¹ := by
    intro c hc
    rw [deriv_effU, Real.deriv_log]
    field_simp
  have g1 : ContinuousOn (effU Real.log z) (Ioi 0) := by
    refine Real.continuousOn_log.comp (continuousOn_const.mul continuousOn_id) ?_
    intro c hc
    simpa using ne_of_gt (mul_pos hz (mem_Ioi.mp hc))
  have g2 : StrictConcaveOn ℝ (Ioi 0) (effU Real.log z) := by
    refine ⟨convex_Ioi 0, fun a ha b hb hne s t hs ht hst => ?_⟩
    have ha' : (1 + z) * a ∈ Ioi (0 : ℝ) := mul_pos hz ha
    have hb' : (1 + z) * b ∈ Ioi (0 : ℝ) := mul_pos hz hb
    have hne' : (1 + z) * a ≠ (1 + z) * b := fun h => hne (mul_left_cancel₀ (ne_of_gt hz) h)
    have h := strictConcaveOn_log_Ioi.2 ha' hb' hne' hs ht hst
    simp only [smul_eq_mul, effU] at h ⊢
    convert h using 2
    ring
  have g3 : ∀ c, 0 < c → DifferentiableAt ℝ (effU Real.log z) c := by
    intro c hc
    unfold effU
    exact (Real.differentiableAt_log (ne_of_gt (mul_pos hz hc))).comp c
      ((differentiableAt_id).const_mul _)
  have g4 : ∀ c, 0 < c → 0 < deriv (effU Real.log z) c := by
    intro c hc; rw [hderiv c hc]; exact inv_pos.mpr hc
  have g5 : ContinuousOn (deriv (effU Real.log z)) (Ioi 0) := by
    exact (continuousOn_inv₀.mono (fun c hc => ne_of_gt (mem_Ioi.mp hc))).congr
      (fun c hc => hderiv c hc)
  have g6 : Tendsto (deriv (effU Real.log z)) (𝓝[>] (0 : ℝ)) atTop := by
    exact tendsto_inv_nhdsGT_zero.congr' (by
      filter_upwards [self_mem_nhdsWithin] with c hc
      exact (hderiv c hc).symm)
  have g7 : Tendsto (effU Real.log z) (𝓝[>] (0 : ℝ)) atBot := by
    have hlin : Tendsto (fun c : ℝ => (1 + z) * c) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have h0 : Tendsto (fun c : ℝ => (1 + z) * c) (𝓝 0) (𝓝 ((1 + z) * 0)) :=
          ((continuous_const.mul continuous_id).tendsto 0)
        rw [mul_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with c hc
        exact mul_pos hz hc
    exact Real.tendsto_log_nhdsGT_zero.comp hlin
  exact ⟨hP.β_pos, hP.β_lt_one, hP.δ_nonneg, hP.δ_le_one, hP.f_cont, hP.f_zero, hP.f_conc,
    hP.f_diff, hP.f_prime_pos, hP.f_prime_cont, hP.f_inada0, hP.f_inadaTop, g1, g2, g3, g4,
    g5, g6, g7⟩

/-- **Isoelastic utility with `σ < 1` satisfies the hypotheses** (O&R (21) with
`θ = 1 - 1/σ < 0`): `c^θ/θ` is negative, strictly concave on `(0, ∞)` and tends to `-∞`. -/
theorem crra_neg_uprimitives (hT : Technology f) {θ β z : ℝ} (hθ : θ < 0) (hβ : 0 < β)
    (hβ1 : β < 1) (hδ1 : δ ≤ 1) (hzd : 0 ≤ z + δ) (hz : 0 < 1 + z) :
    UPrimitives (effF f z) (effU (crra θ) z) β (effDelta z δ) := by
  have hP := toPrimitives hT (crra_preferences (θ := 1 / 2) (by norm_num) (by norm_num)) hβ
    hβ1 hδ1 hzd hz
  have hθ0 : θ ≠ 0 := ne_of_lt hθ
  have hd0 : ∀ c, 0 < c → deriv (crra θ) c = c ^ (θ - 1) := fun c hc =>
    (crra_hasDerivAt hθ0 hc).deriv
  have hderiv : ∀ c, 0 < c → deriv (effU (crra θ) z) c = (1 + z) * ((1 + z) * c) ^ (θ - 1) := by
    intro c hc
    rw [deriv_effU, hd0 _ (mul_pos hz hc)]
  have hcont : ContinuousOn (crra θ) (Ioi 0) := fun c hc =>
    (crra_hasDerivAt hθ0 (mem_Ioi.mp hc)).continuousAt.continuousWithinAt
  have hconc : StrictConcaveOn ℝ (Ioi 0) (crra θ) := by
    refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0) hcont ?_
    rw [interior_Ioi]
    intro a ha b hb hab
    rw [hd0 a ha, hd0 b hb]
    exact Real.rpow_lt_rpow_of_neg ha hab (by linarith)
  have hlin : Tendsto (fun c : ℝ => (1 + z) * c) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 : Tendsto (fun c : ℝ => (1 + z) * c) (𝓝 0) (𝓝 ((1 + z) * 0)) :=
        ((continuous_const.mul continuous_id).tendsto 0)
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with c hc
      exact mul_pos hz hc
  have g1 : ContinuousOn (effU (crra θ) z) (Ioi 0) := by
    exact hcont.comp (continuousOn_const.mul continuousOn_id)
      (fun c hc => mem_Ioi.mpr (mul_pos hz (mem_Ioi.mp hc)))
  have g2 : StrictConcaveOn ℝ (Ioi 0) (effU (crra θ) z) := by
    refine ⟨convex_Ioi 0, fun a ha b hb hne s t hs ht hst => ?_⟩
    have ha' : (1 + z) * a ∈ Ioi (0 : ℝ) := mul_pos hz ha
    have hb' : (1 + z) * b ∈ Ioi (0 : ℝ) := mul_pos hz hb
    have hne' : (1 + z) * a ≠ (1 + z) * b := fun h => hne (mul_left_cancel₀ (ne_of_gt hz) h)
    have h := hconc.2 ha' hb' hne' hs ht hst
    simp only [smul_eq_mul, effU] at h ⊢
    convert h using 2
    ring
  have g3 : ∀ c, 0 < c → DifferentiableAt ℝ (effU (crra θ) z) c := by
    intro c hc
    unfold effU
    exact (crra_hasDerivAt hθ0 (mul_pos hz hc)).differentiableAt.comp c
      ((differentiableAt_id).const_mul _)
  have g4 : ∀ c, 0 < c → 0 < deriv (effU (crra θ) z) c := by
    intro c hc; rw [hderiv c hc]
    exact mul_pos hz (Real.rpow_pos_of_pos (mul_pos hz hc) _)
  have g5 : ContinuousOn (deriv (effU (crra θ) z)) (Ioi 0) := by
    refine ContinuousOn.congr (f := fun c => (1 + z) * ((1 + z) * c) ^ (θ - 1)) ?_ hderiv
    exact continuousOn_const.mul (fun c hc => ((Real.continuousAt_rpow_const _ _
      (Or.inl (ne_of_gt (mul_pos hz (mem_Ioi.mp hc))))).comp
        ((continuous_const.mul continuous_id).continuousAt)).continuousWithinAt)
  have g6 : Tendsto (deriv (effU (crra θ) z)) (𝓝[>] (0 : ℝ)) atTop := by
    refine (((tendsto_rpow_neg_nhdsGT_zero (by linarith : θ - 1 < 0)).comp hlin).const_mul_atTop
      hz).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact (hderiv c hc).symm
  have g7 : Tendsto (effU (crra θ) z) (𝓝[>] (0 : ℝ)) atBot := by
    have hneg : Tendsto (fun c : ℝ => c ^ θ / θ) (𝓝[>] 0) atBot :=
      (tendsto_rpow_neg_nhdsGT_zero hθ).atTop_div_const_of_neg hθ |>.congr (fun _ => rfl)
    exact hneg.comp hlin
  exact ⟨hP.β_pos, hP.β_lt_one, hP.δ_nonneg, hP.δ_le_one, hP.f_cont, hP.f_zero, hP.f_conc,
    hP.f_diff, hP.f_prime_pos, hP.f_prime_cont, hP.f_inada0, hP.f_inadaTop, g1, g2, g3, g4,
    g5, g6, g7⟩

/-- **Existence and uniqueness of the optimal path with log or `σ < 1` utility** in the
book's model (O&R p. 442, Fig. 7.4, now for the whole isoelastic class). -/
theorem book_unbounded_existsUnique {β z : ℝ}
    (P : UPrimitives (effF f z) (effU u z) β (effDelta z δ)) {x : ℝ} (hx : 0 < x) :
    ∃! k, UOptimal (effF f z) (effU u z) β (effDelta z δ) x k := by
  obtain ⟨k, hk⟩ := exists_optimal P hx
  exact ⟨k, hk, fun k' hk' => hk'.unique P hx hk⟩

/-- **The Euler equation (24) with log or `σ < 1` utility**, in book consumption:
`u'(c_t) = β̂ u'(c_{t+1}) [1 + f'(k_{t+1}) - δ]/(1 + z)`, with `c_t > 0`. -/
theorem book_unbounded_euler {β z : ℝ} (hz : 0 < 1 + z)
    (P : UPrimitives (effF f z) (effU u z) β (effDelta z δ)) {x : ℝ} (hx : 0 < x)
    {k : ℕ → ℝ} (hk : UOptimal (effF f z) (effU u z) β (effDelta z δ) x k) (t : ℕ) :
    0 < bookConsumption f δ z k t ∧
      deriv u (bookConsumption f δ z k t) =
        β * deriv u (bookConsumption f δ z k (t + 1)) * (1 + deriv f (k (t + 1)) - δ) /
          (1 + z) := by
  have he := hk.euler P hx t
  have hc := hk.1.2.1 t
  simp only [consumption_eff f δ hz] at he hc
  rw [deriv_effU, deriv_effU, deriv_effF] at he
  have e1 : (1 + z) * (bookConsumption f δ z k t / (1 + z)) = bookConsumption f δ z k t := by
    field_simp
  have e2 : (1 + z) * (bookConsumption f δ z k (t + 1) / (1 + z)) =
      bookConsumption f δ z k (t + 1) := by field_simp
  rw [e1, e2] at he
  refine ⟨(div_pos_iff_of_pos_right hz).mp hc, ?_⟩
  rw [one_sub_effDelta δ hz] at he
  field_simp at he ⊢
  nlinarith [he]

/-- **Monotone convergence with log or `σ < 1` utility** (O&R Fig. 7.4): the optimal path
converges to the steady state (25), `1 + f'(k̄) - δ = (1 + z)/β̂`, monotonically, with
book consumption converging to `f(k̄) - (z + δ) k̄` and moving in the same direction. -/
theorem book_unbounded_convergence (hT : Technology f) {β z : ℝ} (hz : 0 < 1 + z)
    (P : UPrimitives (effF f z) (effU u z) β (effDelta z δ)) {x : ℝ} (hx : 0 < x)
    {k : ℕ → ℝ} (hk : UOptimal (effF f z) (effU u z) β (effDelta z δ) x k) :
    1 + deriv f (steady P.aux) - δ = (1 + z) / β ∧
      Tendsto k atTop (𝓝 (steady P.aux)) ∧
      Tendsto (bookConsumption f δ z k) atTop
        (𝓝 (f (steady P.aux) - (z + δ) * steady P.aux)) ∧
      (x < steady P.aux → StrictMono k ∧ StrictMono (bookConsumption f δ z k)) ∧
      (steady P.aux < x → StrictAnti k ∧ StrictAnti (bookConsumption f δ z k)) := by
  have hce : bookConsumption f δ z k = fun t => (1 + z) * consumption (effF f z)
      (effDelta z δ) k t := funext fun t => by rw [consumption_eff f δ hz]; field_simp
  refine ⟨(book_steady_spec hT P.β_pos hz P.aux).2.1, hk.tendsto P hx, ?_, fun hlt => ?_,
    fun hgt => ?_⟩
  · rw [hce]
    have h := (hk.consumption_tendsto P hx).const_mul (1 + z)
    convert h using 2
    rw [resources_eff f δ hz]
    field_simp
    ring
  · obtain ⟨h1, -, h3⟩ := hk.dynamics_below P hx hlt
    exact ⟨h1, by rw [hce]; exact fun a b hab => mul_lt_mul_of_pos_left (h3 hab) hz⟩
  · obtain ⟨h1, -, h3⟩ := hk.dynamics_above P hx hgt
    exact ⟨h1, by rw [hce]; exact fun a b hab => mul_lt_mul_of_pos_left (h3 hab) hz⟩

/-- **The log Euler equation** (O&R (24) with `σ = 1`): with `u = log`,
`β̂ = β(1 + n)`, `1 + z = (1 + n)(1 + g)` and `δ = 0`, the Euler equation is
`c_{t+1}/c_t = β [1 + f'(k_{t+1})]/(1 + g)`. -/
theorem log_euler_eq24 {β n g c0 c1 fp : ℝ} (hn : 0 < 1 + n) (hg : 0 < 1 + g) (hc0 : 0 < c0)
    (hc1 : 0 < c1) (he : c0⁻¹ = β * (1 + n) * c1⁻¹ * (1 + fp - 0) / ((1 + n) * (1 + g))) :
    c1 / c0 = β * (1 + fp) / (1 + g) := by
  field_simp at he ⊢
  nlinarith [he]

end LogUtility

end ObstfeldRogoff.GlobalGrowth.RamseyCassKoopmans
