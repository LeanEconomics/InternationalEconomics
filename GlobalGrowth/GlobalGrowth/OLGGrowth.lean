/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GlobalGrowth.RamseyCassKoopmans

/-!
# An overlapping-generations growth model (Weil 1989)

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §7.1.2.2
(pp. 445–449) and Exercise 1 (p. 512).

* **The log consumer** facing arbitrary interest rates and wages: consuming the fraction
  `1 - β` of financial plus human wealth at every date is the optimum with a genuine
  infinite horizon (supporting-hyperplane argument on partial sums, against every plan that
  satisfies the no-Ponzi condition).
* **Aggregation across vintages** (fn 10, fn 11): cohort sizes `1, n, n(1+n), …`, the
  aggregate capital equation (32) and the aggregate Euler identity; the newborn gap
  `c_{t+1} - c^{t+1}_{t+1} = (1-β)(1+r_{t+1})k_{t+1}` and eq. (33).
* **The steady state** (Fig. 7.7): it exists, is unique, lies below `(f')^{-1}((1-β)/β)`, and
  falls with population growth; the `Δc = 0` locus shifts up with `n` (fn 12). Dynamic
  inefficiency is possible (fn 13): for every `n > 0` there is an explicit `β₀ < 1` such that
  `f'(k̄) < n` for `β > β₀` (for Cobb–Douglas `β₀ = (1 + αn)/(1 + n)`); with `β(1+n) ≤ 1` the
  steady state is dynamically efficient.
* **Local saddle-path stability** of (32)–(33) at the steady state: the Jacobian has one
  eigenvalue in `(0, 1)` and one above `1`.
* **The global saddle path** (`weil_saddle_path`): from every `k₀ > 0` exactly one initial
  consumption keeps the economy in the positive quadrant (existence by shooting, uniqueness by
  the human-wealth representation that every bounded positive orbit satisfies); that path is
  the competitive equilibrium and converges monotonically to the steady state.
* **Exercise 1**: tax-financed government spending changes (30) and (32) but not (33), and
  lowers both steady-state capital and consumption (crowding out), with possibly two
  steady states; for the announced spending rise, in general equilibrium: an equilibrium path
  exists whenever spending is at most the steady-state residual `Φ(k_L)` at some `k_L < k₀`
  with `β(1 + f'(k_L)) > 1` (from the old steady state: the same smallness that makes the
  crowded-out steady states exist; from any `k₀`: every spending path below an explicit
  `Ḡ > 0`), by shooting with a trapping level and a safety invariant; it is unique for every
  nonnegative spending path (a Perron weight on the gaps grows geometrically); consumption
  falls on impact; capital rises strictly and consumption falls strictly until spending
  starts; no equilibrium exists when spending exceeds maximal sustainable consumption; and
  any limit is a crowded-out steady state.
-/

namespace ObstfeldRogoff.GlobalGrowth.OLGGrowth

open Set Filter Topology
open ObstfeldRogoff.GlobalGrowth.RamseyCassKoopmans

variable {f : ℝ → ℝ}

/-! ## The log consumer with a genuine infinite horizon (O&R p. 447) -/

/-- The asset recursion in present-value form: with discount factors `D` (`D₀ = 1`,
`D_{s+1} = D_s/(1 + r_{s+1})`), cash on hand `a_s = (1 + r_s) k_s` obeys
`D_{s+1} a_{s+1} = D_s (a_s + w_s - c_s)`, i.e. (30) (O&R p. 446). -/
def Budget (D w c a : ℕ → ℝ) : Prop := ∀ s, D (s + 1) * a (s + 1) = D s * (a s + w s - c s)

/-- Telescoped budget: `D_T a_T = a₀ + ∑_{s<T} D_s (w_s - c_s)` (with `D₀ = 1`). -/
theorem budget_telescope {D w c a : ℕ → ℝ} (hD0 : D 0 = 1) (hb : Budget D w c a) (T : ℕ) :
    D T * a T = a 0 + ∑ s ∈ Finset.range T, D s * (w s - c s) := by
  induction T with
  | zero => simp [hD0]
  | succ T ih =>
    rw [hb T, Finset.sum_range_succ, ← add_assoc, ← ih]
    ring

/-- The log rule (O&R p. 447): `c*_s = (1 - β) βˢ W₀ / D_s` with total wealth
`W₀ = a₀ + ∑ D_s w_s`. -/
noncomputable def logRule (β W0 : ℝ) (D : ℕ → ℝ) (s : ℕ) : ℝ := (1 - β) * β ^ s * W0 / D s

/-- Assets implied by the log rule: `D_T a*_T = βᵀ W₀ - ∑_{s ≥ T} D_s w_s`. -/
theorem logRule_assets {β W0 : ℝ} {D w a : ℕ → ℝ} (hβ1 : β ≠ 1) (hD0 : D 0 = 1)
    (hDpos : ∀ s, 0 < D s) (hw : Summable (fun s => D s * w s))
    (hW0 : W0 = a 0 + ∑' s, D s * w s) (hb : Budget D w (logRule β W0 D) a) (T : ℕ) :
    D T * a T = β ^ T * W0 - ∑' s, D (s + T) * w (s + T) := by
  rw [budget_telescope hD0 hb T]
  have hsplit := hw.sum_add_tsum_nat_add T
  have hc : ∑ s ∈ Finset.range T, D s * logRule β W0 D s =
      (1 - β) * W0 * ∑ s ∈ Finset.range T, β ^ s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    unfold logRule
    field_simp [ne_of_gt (hDpos s)]
  have hgeom : (1 - β) * ∑ s ∈ Finset.range T, β ^ s = 1 - β ^ T := by
    rw [geom_sum_eq hβ1]
    have : β - 1 ≠ 0 := sub_ne_zero.mpr hβ1
    field_simp
    ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hc]
  have : (1 - β) * W0 * ∑ s ∈ Finset.range T, β ^ s = W0 * (1 - β ^ T) := by
    rw [← hgeom]; ring
  rw [this, hW0]
  linarith

/-- The log rule satisfies the no-Ponzi condition with equality: `D_T a*_T → 0`. -/
theorem logRule_assets_tendsto {β W0 : ℝ} {D w a : ℕ → ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hD0 : D 0 = 1) (hDpos : ∀ s, 0 < D s) (hw : Summable (fun s => D s * w s))
    (hW0 : W0 = a 0 + ∑' s, D s * w s) (hb : Budget D w (logRule β W0 D) a) :
    Tendsto (fun T => D T * a T) atTop (𝓝 0) := by
  have e := logRule_assets (ne_of_lt hβ1) hD0 hDpos hw hW0 hb
  have h1 : Tendsto (fun T => β ^ T * W0) atTop (𝓝 (0 * W0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).mul_const W0
  have h2 : Tendsto (fun T => ∑' s, D (s + T) * w (s + T)) atTop (𝓝 0) :=
    tendsto_sum_nat_add (fun s => D s * w s)
  have := h1.sub h2
  rw [zero_mul, sub_zero] at this
  exact this.congr (fun T => (e T).symm)

/-- **The log consumer's optimum** (O&R p. 447: "an agent with log utility will always
consume a fixed fraction `1 - β` of total wealth"), with a genuine infinite horizon: for any
positive consumption plan `c` whose assets satisfy the no-Ponzi condition
(`liminf D_T a_T ≥ 0`), `limsup_T ∑_{s<T} βˢ [log c_s - log c*_s] ≤ 0`. Rival plans need not
have summable utility. -/
theorem logRule_optimal {β W0 : ℝ} {D w a a' c : ℕ → ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hD0 : D 0 = 1) (hDpos : ∀ s, 0 < D s) (hw : Summable (fun s => D s * w s))
    (hW0 : W0 = a 0 + ∑' s, D s * w s) (hWpos : 0 < W0)
    (hb : Budget D w (logRule β W0 D) a) (hb' : Budget D w c a') (ha' : a' 0 = a 0)
    (hc : ∀ s, 0 < c s) (hnpg : ∀ ε > 0, ∀ᶠ T in atTop, -ε ≤ D T * a' T) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      ∑ s ∈ Finset.range T, β ^ s * (Real.log (c s) - Real.log (logRule β W0 D s)) ≤ ε := by
  intro ε hε
  set lam := 1 / ((1 - β) * W0)
  have h1β : 0 < 1 - β := by linarith
  have hlam : 0 < lam := div_pos one_pos (mul_pos h1β hWpos)
  have hcs : ∀ s, 0 < logRule β W0 D s := fun s => by
    unfold logRule; have : 0 < 1 - β := by linarith
    have := hDpos s; positivity
  -- one-period bound: βˢ (log c - log c*) ≤ λ D_s (c - c*)
  have hstep : ∀ s, β ^ s * (Real.log (c s) - Real.log (logRule β W0 D s)) ≤
      lam * (D s * (c s - logRule β W0 D s)) := by
    intro s
    have hlog : Real.log (c s) - Real.log (logRule β W0 D s) ≤
        (c s - logRule β W0 D s) / logRule β W0 D s := by
      rw [← Real.log_div (ne_of_gt (hc s)) (ne_of_gt (hcs s))]
      have := Real.log_le_sub_one_of_pos (div_pos (hc s) (hcs s))
      rw [sub_div, div_self (ne_of_gt (hcs s))]
      exact this
    have hmul := mul_le_mul_of_nonneg_left hlog (pow_pos hβ s).le
    refine hmul.trans (le_of_eq ?_)
    simp only [lam, logRule]
    have := hDpos s
    have : 0 < 1 - β := by linarith
    field_simp
  -- telescoping both budgets
  have htel : ∀ T, ∑ s ∈ Finset.range T, D s * (c s - logRule β W0 D s) =
      D T * a T - D T * a' T := by
    intro T
    have h1 := budget_telescope hD0 hb T
    have h2 := budget_telescope hD0 hb' T
    rw [ha'] at h2
    have : ∑ s ∈ Finset.range T, D s * (c s - logRule β W0 D s) =
        ∑ s ∈ Finset.range T, D s * (w s - logRule β W0 D s) -
          ∑ s ∈ Finset.range T, D s * (w s - c s) := by
      rw [← Finset.sum_sub_distrib]; congr 1; ext s; ring
    rw [this]
    linarith
  have hA := logRule_assets_tendsto hβ.le hβ1 hD0 hDpos hw hW0 hb
  have hε' : 0 < ε / (2 * lam) := by positivity
  filter_upwards [hA.eventually (gt_mem_nhds hε'), hnpg _ hε'] with T hT1 hT2
  calc ∑ s ∈ Finset.range T, β ^ s * (Real.log (c s) - Real.log (logRule β W0 D s))
      ≤ ∑ s ∈ Finset.range T, lam * (D s * (c s - logRule β W0 D s)) :=
        Finset.sum_le_sum (fun s _ => hstep s)
    _ = lam * (D T * a T - D T * a' T) := by rw [← Finset.mul_sum, htel]
    _ ≤ lam * (ε / (2 * lam) + ε / (2 * lam)) := by
        apply mul_le_mul_of_nonneg_left _ hlam.le; linarith
    _ = ε := by field_simp; ring

/-- **The rule at every date** (O&R p. 447): along the log plan, consumption at date `t` is
`(1 - β)` times financial plus human wealth at `t`, `a_t + H_t` with
`H_t = ∑_{s≥t} (D_s/D_t) w_s`. -/
theorem logRule_fraction_of_wealth {β W0 : ℝ} {D w a : ℕ → ℝ} (hβ1 : β < 1) (hD0 : D 0 = 1)
    (hDpos : ∀ s, 0 < D s) (hw : Summable (fun s => D s * w s))
    (hW0 : W0 = a 0 + ∑' s, D s * w s) (hb : Budget D w (logRule β W0 D) a) (t : ℕ) :
    logRule β W0 D t = (1 - β) * (a t + (∑' s, D (s + t) * w (s + t)) / D t) := by
  have e := logRule_assets (ne_of_lt hβ1) hD0 hDpos hw hW0 hb t
  have hDt := hDpos t
  have e2 : a t + (∑' s, D (s + t) * w (s + t)) / D t = β ^ t * W0 / D t := by
    rw [eq_div_iff (ne_of_gt hDt), add_mul, div_mul_cancel₀ _ (ne_of_gt hDt)]
    linarith
  unfold logRule
  rw [e2]
  ring

/-! ## Aggregation across vintages (O&R pp. 446–447, fn 10, fn 11) -/

/-- Cohort sizes (fn 10): vintage 0 has 1 member, vintage `v ≥ 1` has `n(1+n)^{v-1}`. -/
noncomputable def cohortSize (n : ℝ) (v : ℕ) : ℝ := if v = 0 then 1 else n * (1 + n) ^ (v - 1)

/-- The cohorts alive at `t` add up to the population `(1 + n)^t` (fn 10). -/
theorem sum_cohortSize (n : ℝ) (t : ℕ) :
    ∑ v ∈ Finset.range (t + 1), cohortSize n v = (1 + n) ^ t := by
  induction t with
  | zero => simp [cohortSize]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [cohortSize, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, pow_succ]
    ring

/-- Per-capita aggregate of a vintage variable `x v t` (O&R p. 446). -/
noncomputable def aggregate (n : ℝ) (x : ℕ → ℕ → ℝ) (t : ℕ) : ℝ :=
  (∑ v ∈ Finset.range (t + 1), cohortSize n v * x v t) / (1 + n) ^ t

/-- Summing over the cohorts alive at `t + 1` adds the newborn vintage: the per-capita
aggregate at `t + 1` times `(1+n)^{t+1}` is the date-`t` cohorts' total plus
`n(1+n)^t x^{t+1}`. -/
theorem aggregate_succ (n : ℝ) (hn : 0 < 1 + n) (x : ℕ → ℕ → ℝ) (t : ℕ) :
    (1 + n) ^ (t + 1) * aggregate n x (t + 1) =
      ∑ v ∈ Finset.range (t + 1), cohortSize n v * x v (t + 1) +
        n * (1 + n) ^ t * x (t + 1) (t + 1) := by
  unfold aggregate
  rw [mul_div_cancel₀ _ (pow_ne_zero _ (ne_of_gt hn)), Finset.sum_range_succ]
  simp [cohortSize]

/-- **The aggregate capital equation** (O&R (32) with fn 11): if every vintage alive obeys
(30), `k^v_{t+1} = (1 + r_t) k^v_t + w_t - c^v_t`, and newborns hold no wealth
(`k^{t+1}_{t+1} = 0`), then per-capita aggregates satisfy
`(1 + n) k_{t+1} = (1 + r_t) k_t + w_t - c_t`. -/
theorem aggregate_budget {n : ℝ} (hn : 0 < 1 + n) {kv cv : ℕ → ℕ → ℝ} {r w : ℕ → ℝ}
    (hbud : ∀ v t, v ≤ t → kv v (t + 1) = (1 + r t) * kv v t + w t - cv v t)
    (hnew : ∀ v, kv v v = 0) (t : ℕ) :
    (1 + n) * aggregate n kv (t + 1) = (1 + r t) * aggregate n kv t + w t - aggregate n cv t := by
  have h := aggregate_succ n hn kv t
  rw [hnew, mul_zero, add_zero] at h
  have hsum : ∑ v ∈ Finset.range (t + 1), cohortSize n v * kv v (t + 1) =
      (1 + r t) * ∑ v ∈ Finset.range (t + 1), cohortSize n v * kv v t +
        w t * ∑ v ∈ Finset.range (t + 1), cohortSize n v -
          ∑ v ∈ Finset.range (t + 1), cohortSize n v * cv v t := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [hbud v t (Nat.lt_succ_iff.mp (Finset.mem_range.mp hv))]
    ring
  rw [sum_cohortSize] at hsum
  have hpos : (0 : ℝ) < (1 + n) ^ t := pow_pos hn t
  have hA : aggregate n kv (t + 1) = ((1 + r t) * ∑ v ∈ Finset.range (t + 1),
      cohortSize n v * kv v t + w t * (1 + n) ^ t - ∑ v ∈ Finset.range (t + 1),
        cohortSize n v * cv v t) / (1 + n) ^ (t + 1) := by
    rw [eq_div_iff (pow_ne_zero _ (ne_of_gt hn)), mul_comm, h, hsum]
  rw [hA]
  unfold aggregate
  rw [pow_succ]
  field_simp

/-- **Eq. (32)** (O&R p. 447): with competitive factor prices `r = f'(k)`, `w = f(k) - k f'(k)`
(Euler's theorem, `r k + w = f(k)`), `k_{t+1} - k_t = [f(k_t) - c_t - n k_t]/(1 + n)`. -/
theorem eq32 (f : ℝ → ℝ) {n k k' c : ℝ} (hn : 0 < 1 + n)
    (h : (1 + n) * k' = (1 + deriv f k) * k + (f k - k * deriv f k) - c) :
    k' - k = (f k - c - n * k) / (1 + n) := by
  rw [eq_div_iff (ne_of_gt hn)]
  linarith

/-- **The aggregate Euler identity** (O&R p. 447): if every vintage alive at `t` satisfies
(31), `c^v_{t+1} = (1 + r_{t+1}) β c^v_t`, then
`(1 + n) c_{t+1} - n c^{t+1}_{t+1} = (1 + r_{t+1}) β c_t`. -/
theorem aggregate_euler {n β : ℝ} (hn : 0 < 1 + n) {cv : ℕ → ℕ → ℝ} {r : ℕ → ℝ} (t : ℕ)
    (heul : ∀ v, v ≤ t → cv v (t + 1) = (1 + r (t + 1)) * β * cv v t) :
    (1 + n) * aggregate n cv (t + 1) - n * cv (t + 1) (t + 1) =
      (1 + r (t + 1)) * β * aggregate n cv t := by
  have h := aggregate_succ n hn cv t
  have hsum : ∑ v ∈ Finset.range (t + 1), cohortSize n v * cv v (t + 1) =
      (1 + r (t + 1)) * β * ∑ v ∈ Finset.range (t + 1), cohortSize n v * cv v t := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [heul v (Nat.lt_succ_iff.mp (Finset.mem_range.mp hv))]
    ring
  have hpos : (0 : ℝ) < (1 + n) ^ t := pow_pos hn t
  have hA : aggregate n cv (t + 1) = ((1 + r (t + 1)) * β * ∑ v ∈ Finset.range (t + 1),
      cohortSize n v * cv v t + n * (1 + n) ^ t * cv (t + 1) (t + 1)) / (1 + n) ^ (t + 1) := by
    rw [eq_div_iff (pow_ne_zero _ (ne_of_gt hn)), mul_comm, h, hsum]
  rw [hA]
  unfold aggregate
  rw [pow_succ]
  field_simp
  ring

/-- **The newborn gap** (O&R p. 447): if every vintage alive at `t + 1` consumes
`(1 - β)[(1 + r_{t+1}) k^v_{t+1} + H_{t+1}]` with common human wealth `H_{t+1}` and newborns
hold no wealth, then `c_{t+1} - c^{t+1}_{t+1} = (1 - β)(1 + r_{t+1}) k_{t+1}`. -/
theorem newborn_gap {n β H R : ℝ} (hn : 0 < 1 + n) {kv cv : ℕ → ℕ → ℝ} (t : ℕ)
    (hrule : ∀ v, v ≤ t + 1 → cv v (t + 1) = (1 - β) * (R * kv v (t + 1) + H))
    (hnew : kv (t + 1) (t + 1) = 0) :
    aggregate n cv (t + 1) - cv (t + 1) (t + 1) = (1 - β) * R * aggregate n kv (t + 1) := by
  have hpos : (0 : ℝ) < (1 + n) ^ (t + 1) := pow_pos hn _
  have hsum : ∑ v ∈ Finset.range (t + 1 + 1), cohortSize n v * cv v (t + 1) =
      (1 - β) * R * ∑ v ∈ Finset.range (t + 1 + 1), cohortSize n v * kv v (t + 1) +
        (1 - β) * H * ∑ v ∈ Finset.range (t + 1 + 1), cohortSize n v := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [hrule v (Nat.lt_succ_iff.mp (Finset.mem_range.mp hv))]
    ring
  rw [sum_cohortSize] at hsum
  have hnewc : cv (t + 1) (t + 1) = (1 - β) * H := by
    rw [hrule (t + 1) le_rfl, hnew]; ring
  unfold aggregate
  rw [hsum, hnewc]
  field_simp
  ring

/-- **Eq. (33)** (O&R p. 448): combining the aggregate Euler identity, the newborn gap and
`r_{t+1} = f'(k_{t+1})`: `c_{t+1} = [1 + f'(k_{t+1})][β c_t - n(1 - β) k_{t+1}]`. -/
theorem eq33 {n β c c' cnew k' R : ℝ} (heul : (1 + n) * c' - n * cnew = R * β * c)
    (hgap : c' - cnew = (1 - β) * R * k') : c' = R * (β * c - n * (1 - β) * k') := by
  have : cnew = c' - (1 - β) * R * k' := by linarith
  rw [this] at heul
  linarith

/-! ## The steady state (O&R Fig. 7.7, fn 12, fn 13) -/

/-- The `Δc = 0` locus coefficient `q(k) = (1 + f'(k))/(β(1 + f'(k)) - 1)` (fn 12). -/
noncomputable def qCoef (f : ℝ → ℝ) (β k : ℝ) : ℝ := (1 + deriv f k) / (β * (1 + deriv f k) - 1)

/-- The steady-state residual `Φ(k) = f(k) - n k - n(1 - β) k q(k)`: zero exactly at steady
states of (32)–(33). -/
noncomputable def residual (f : ℝ → ℝ) (β n k : ℝ) : ℝ :=
  f k - n * k - n * (1 - β) * k * qCoef f β k

/-- **Steady states of (32)–(33)** (O&R fn 12): for `k, c > 0`, `n > 0`, `β < 1`, the `Δc = 0`
condition `c = (1 + f'(k))[βc - n(1-β)k]` holds iff `β(1 + f'(k)) > 1` and
`c = n(1 - β) k q(k)`. In particular every steady state lies left of the vertical asymptote
`β(1 + f'(k)) = 1` of Fig. 7.7. -/
theorem deltaC_zero_iff (f : ℝ → ℝ) {β n k c : ℝ} (hβ1 : β < 1) (hn : 0 < n) (hk : 0 < k)
    (hc : 0 < c) (hR : 0 < 1 + deriv f k) :
    c = (1 + deriv f k) * (β * c - n * (1 - β) * k) ↔
      1 < β * (1 + deriv f k) ∧ c = n * (1 - β) * k * qCoef f β k := by
  unfold qCoef
  constructor
  · intro h
    have hgt : 1 < β * (1 + deriv f k) := by
      by_contra hle
      push Not at hle
      have : 0 < n * (1 - β) * k * (1 + deriv f k) := by
        have : 0 < 1 - β := by linarith
        positivity
      nlinarith
    refine ⟨hgt, ?_⟩
    rw [mul_div_assoc', eq_div_iff (by linarith)]
    linarith
  · rintro ⟨hgt, h⟩
    rw [mul_div_assoc', eq_div_iff (by linarith)] at h
    linarith

/-- On `{β(1 + f') > 1}` the coefficient `q` is strictly increasing in `k` (the `Δc = 0`
locus bends up, Fig. 7.7). -/
theorem qCoef_strictMono (hT : Technology f) {β a b : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (hab : a < b) (hb : 1 < β * (1 + deriv f b)) : qCoef f β a < qCoef f β b := by
  have hd := hT.neo.deriv_strictAnti ha (ha.trans hab) hab
  have ha1 : 1 < β * (1 + deriv f a) := by nlinarith
  unfold qCoef
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The residual per unit of capital, `Φ(k)/k`, is strictly decreasing on
`{β(1 + f') > 1}` (O&R Fig. 7.7: the loci cross once). -/
theorem residual_div_strictAnti (hT : Technology f) {β n a b : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hn : 0 < n) (ha : 0 < a) (hab : a < b) (hb : 1 < β * (1 + deriv f b)) :
    residual f β n b / b < residual f β n a / a := by
  have hb0 : 0 < b := ha.trans hab
  have havg := hT.neo.avg_strictAnti ha hb0 hab
  have hq := qCoef_strictMono hT hβ ha hab hb
  have e : ∀ x, 0 < x → residual f β n x / x = f x / x - n - n * (1 - β) * qCoef f β x := by
    intro x hx; unfold residual; field_simp
  rw [e a ha, e b hb0]
  have : 0 < n * (1 - β) := mul_pos hn (by linarith)
  simp only at havg
  nlinarith

/-- The asymptote `k_β`: the unique `k > 0` with `f'(k) = (1 - β)/β`, i.e.
`β(1 + f'(k)) = 1` (O&R Fig. 7.7 label `(f')^{-1}((1-β)/β)`). -/
theorem exists_asymptote (hT : Technology f) {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    ∃! kb, 0 < kb ∧ deriv f kb = (1 - β) / β :=
  existsUnique_positive_root_of_inada (deriv f) _ (div_pos (by linarith) hβ) hT.prime_cont
    hT.neo.deriv_strictAnti hT.inada0 hT.inadaTop

/-- **Existence and uniqueness of the steady state** (O&R Fig. 7.7): with `n > 0`,
`0 < β < 1` and a technology satisfying the Inada conditions, there is exactly one `k̄ > 0`
with `β(1 + f'(k̄)) > 1` and `Φ(k̄) = 0`; then `c̄ = f(k̄) - n k̄ > 0` satisfies both loci. -/
theorem steady_existsUnique (hT : Technology f) {β n : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hn : 0 < n) :
    ∃! k, 0 < k ∧ 1 < β * (1 + deriv f k) ∧ residual f β n k = 0 := by
  obtain ⟨kb, ⟨hkb, hdkb⟩, -⟩ := exists_asymptote hT hβ hβ1
  have hRkb : β * (1 + deriv f kb) = 1 := by rw [hdkb]; field_simp; ring
  have hdom : ∀ k, 0 < k → k < kb → 1 < β * (1 + deriv f k) := by
    intro k hk hlt
    have := hT.neo.deriv_strictAnti hk hkb hlt
    nlinarith
  -- continuity of `Φ(k)/k` on `(0, kb)`
  set g : ℝ → ℝ := fun k => f k / k - n - n * (1 - β) * qCoef f β k
  have hg : ∀ k, 0 < k → residual f β n k / k = g k := by
    intro k hk; unfold residual; simp only [g]; field_simp
  have hfc : ContinuousOn f (Ioi 0) := hT.neo.cont.mono Ioi_subset_Ici_self
  have hgc : ContinuousOn g (Ioo 0 kb) := by
    have hq : ContinuousOn (qCoef f β) (Ioo 0 kb) := by
      refine ContinuousOn.div (continuousOn_const.add (hT.prime_cont.mono Ioo_subset_Ioi_self))
        ((continuousOn_const.mul (continuousOn_const.add
          (hT.prime_cont.mono Ioo_subset_Ioi_self))).sub continuousOn_const) ?_
      intro k hk
      have := hdom k hk.1 hk.2
      linarith
    exact (((hfc.mono Ioo_subset_Ioi_self).div continuousOn_id
      (fun k hk => ne_of_gt hk.1)).sub continuousOn_const).sub (continuousOn_const.mul hq)
  -- `g` is positive near 0
  obtain ⟨a, ha, hakb, hga⟩ : ∃ a, 0 < a ∧ a < kb ∧ 0 < g a := by
    have h1 := hT.neo.avg_tendsto_atTop hT.inada0
    have hev1 := h1.eventually (eventually_gt_atTop (n + n * (1 - β) * (2 / β)))
    have hev2 := hT.inada0.eventually (eventually_ge_atTop (2 / β))
    have hev0 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi 0 := eventually_mem_nhdsWithin
    obtain ⟨a, ha, h1a, h2a, hakb⟩ := (hev0.and
      (hev1.and (hev2.and (Ioo_mem_nhdsGT hkb)))).exists
    refine ⟨a, ha, hakb.2, ?_⟩
    have hq : qCoef f β a ≤ 2 / β := by
      have h2 : 2 ≤ β * deriv f a := by rw [div_le_iff₀ hβ] at h2a; linarith
      unfold qCoef
      rw [div_le_div_iff₀ (by nlinarith) hβ]
      nlinarith
    have : n * (1 - β) * qCoef f β a ≤ n * (1 - β) * (2 / β) :=
      mul_le_mul_of_nonneg_left hq (mul_pos hn (by linarith)).le
    simp only [g]
    linarith
  -- `g` is negative near the asymptote
  obtain ⟨b, hab, hbkb, hgb⟩ : ∃ b, a < b ∧ b < kb ∧ g b < 0 := by
    set M := f a / a
    have hM : 0 < M := div_pos (hT.neo.pos ha) ha
    set η := n * (1 - β) / (β * (M + 1))
    have hη : 0 < η := div_pos (mul_pos hn (by linarith)) (by positivity)
    have hcont : ContinuousAt (fun k => β * (1 + deriv f k) - 1) kb :=
      ((continuousAt_const.mul (continuousAt_const.add
        (hT.prime_cont.continuousAt (Ioi_mem_nhds hkb))))).sub continuousAt_const
    have hlim : Tendsto (fun k => β * (1 + deriv f k) - 1) (𝓝[<] kb) (𝓝 0) := by
      have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio kb))
      rwa [hRkb, sub_self] at this
    obtain ⟨b, hbη, hb⟩ := ((hlim.eventually (gt_mem_nhds hη)).and
      (Ioo_mem_nhdsLT hakb)).exists
    refine ⟨b, hb.1, hb.2, ?_⟩
    have hb0 : 0 < b := ha.trans hb.1
    have hdom_b := hdom b hb0 hb.2
    have hR : 1 / β ≤ 1 + deriv f b := by
      have := hT.neo.deriv_strictAnti hb0 hkb hb.2
      rw [div_le_iff₀ hβ]; nlinarith
    have hq : (M + 1) / (n * (1 - β)) ≤ qCoef f β b := by
      unfold qCoef
      rw [div_le_div_iff₀ (mul_pos hn (by linarith)) (by linarith)]
      have h1 : β * (1 + deriv f b) - 1 < η := hbη
      have h2 : (β * (1 + deriv f b) - 1) * (β * (M + 1)) < n * (1 - β) := by
        rw [lt_div_iff₀ (by positivity)] at h1; linarith
      have h4 : (M + 1) * (β * (1 + deriv f b) - 1) < n * (1 - β) / β := by
        rw [lt_div_iff₀ hβ]; linarith [h2]
      have h5 : n * (1 - β) / β ≤ (1 + deriv f b) * (n * (1 - β)) := by
        calc n * (1 - β) / β = n * (1 - β) * (1 / β) := by ring
          _ ≤ n * (1 - β) * (1 + deriv f b) :=
            mul_le_mul_of_nonneg_left hR (mul_pos hn (by linarith)).le
          _ = (1 + deriv f b) * (n * (1 - β)) := by ring
      linarith
    have havg : f b / b ≤ M := (hT.neo.avg_strictAnti.antitoneOn ha hb0 hb.1.le)
    have hq' : M + 1 ≤ n * (1 - β) * qCoef f β b := by
      rw [div_le_iff₀ (mul_pos hn (by linarith))] at hq; linarith
    simp only [g]
    linarith
  -- intermediate value theorem and uniqueness
  obtain ⟨k, hk, hgk⟩ := intermediate_value_Icc' hab.le (hgc.mono (fun x hx =>
    ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hbkb⟩))
    (⟨hgb.le, hga.le⟩ : (0 : ℝ) ∈ Icc (g b) (g a))
  have hk0 : 0 < k := lt_of_lt_of_le ha hk.1
  have hkkb : k < kb := lt_of_le_of_lt hk.2 hbkb
  have hres : residual f β n k = 0 := by
    have := hg k hk0
    rw [hgk, div_eq_zero_iff] at this
    rcases this with h | h
    · exact h
    · linarith
  refine ⟨k, ⟨hk0, hdom k hk0 hkkb, hres⟩, fun y ⟨hy, hyd, hyr⟩ => ?_⟩
  rcases lt_trichotomy y k with hlt | heq | hgt
  · have := residual_div_strictAnti hT hβ hβ1 hn hy hlt (hdom k hk0 hkkb)
    rw [hres, hyr, zero_div, zero_div] at this
    exact absurd this (lt_irrefl 0)
  · exact heq
  · have := residual_div_strictAnti hT hβ hβ1 hn hk0 hgt hyd
    rw [hres, hyr, zero_div, zero_div] at this
    exact absurd this (lt_irrefl 0)


/-- **Fig. 7.7**: a steady state lies strictly left of the asymptote `(f')^{-1}((1-β)/β)`. -/
theorem steady_lt_asymptote (hT : Technology f) {β k kb : ℝ} (hβ : 0 < β) (hk : 0 < k)
    (hkb : 0 < kb) (hdkb : deriv f kb = (1 - β) / β) (hdom : 1 < β * (1 + deriv f k)) :
    k < kb := by
  by_contra hle
  push Not at hle
  have := hT.neo.deriv_strictAnti.antitoneOn hkb hk hle
  rw [hdkb] at this
  have e : β * (1 + (1 - β) / β) = 1 := by field_simp; ring
  nlinarith

/-- At a steady state, `c̄ = f(k̄) - n k̄ > 0` lies on both loci: `Δk = 0` (32) and `Δc = 0`
(33) (O&R Fig. 7.7). -/
theorem steady_consumption (f : ℝ → ℝ) {β n k : ℝ} (hβ1 : β < 1) (hn : 0 < n) (hk : 0 < k)
    (hR : 0 < 1 + deriv f k) (hdom : 1 < β * (1 + deriv f k)) (hres : residual f β n k = 0) :
    0 < f k - n * k ∧
      f k - n * k = (1 + deriv f k) * (β * (f k - n * k) - n * (1 - β) * k) := by
  have hc : f k - n * k = n * (1 - β) * k * qCoef f β k := by unfold residual at hres; linarith
  have hq : 0 < qCoef f β k := div_pos hR (by linarith)
  have h1β : 0 < 1 - β := by linarith
  have hcpos : 0 < f k - n * k := by rw [hc]; positivity
  exact ⟨hcpos, ((deltaC_zero_iff f hβ1 hn hk hcpos hR).mpr ⟨hdom, hc⟩)⟩

/-- **A rise in population growth lowers the steady state** (O&R p. 448: "Clearly the
equilibrium capital-labor ratio falls as in the Solow model"). -/
theorem steady_strictAnti_n (hT : Technology f) {β n n' k k' : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hn : 0 < n) (hnn : n < n') (hk : 0 < k) (hk' : 0 < k')
    (hd : 1 < β * (1 + deriv f k)) (hd' : 1 < β * (1 + deriv f k'))
    (hr : residual f β n k = 0) (hr' : residual f β n' k' = 0) : k' < k := by
  have hq : 0 < qCoef f β k := div_pos (by nlinarith) (by linarith)
  -- `Φ_{n'}(k) < Φ_n(k) = 0`
  have hlt : residual f β n' k < 0 := by
    have : residual f β n' k - residual f β n k = -(n' - n) * k * (1 + (1 - β) * qCoef f β k) :=
      by unfold residual; ring
    have : 0 < (n' - n) * k * (1 + (1 - β) * qCoef f β k) := by
      have : 0 < 1 - β := by linarith
      have : 0 < n' - n := by linarith
      positivity
    linarith
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt' | heq
  · have := residual_div_strictAnti hT hβ hβ1 (hn.trans hnn) hk hlt' hd'
    rw [hr', zero_div] at this
    have : residual f β n' k / k < 0 := div_neg_of_neg_of_pos hlt hk
    linarith
  · subst heq; linarith

/-- **fn 12**: the `Δc = 0` locus `c = n(1 - β) k q(k)` shifts up when `n` rises. -/
theorem deltaC_locus_shifts_up (f : ℝ → ℝ) {β n n' k : ℝ} (hβ1 : β < 1) (hk : 0 < k)
    (hq : 0 < qCoef f β k) (hnn : n < n') :
    n * (1 - β) * k * qCoef f β k < n' * (1 - β) * k * qCoef f β k := by
  have h1β : 0 < 1 - β := by linarith
  have : 0 < (1 - β) * k * qCoef f β k := by positivity
  nlinarith

/-- The residual at the golden rule `f'(k*) = n`:
`Φ(k*)/k* = D - n(1 - β)(1 + n)/(β(1 + n) - 1)` with `D = f(k*)/k* - n > 0`. -/
theorem residual_golden_rule (f : ℝ → ℝ) {β n ks : ℝ} (hks : 0 < ks) (hgr : deriv f ks = n) :
    residual f β n ks / ks = (f ks / ks - n) - n * (1 - β) * ((1 + n) / (β * (1 + n) - 1)) := by
  unfold residual qCoef
  rw [hgr]
  field_simp

/-- The dynamic-inefficiency threshold `β₀ = (D + n(1+n))/((D + n)(1 + n))`, `D = f(k*)/k* - n`
(fn 13 made precise). -/
noncomputable def betaThreshold (D n : ℝ) : ℝ := (D + n * (1 + n)) / ((D + n) * (1 + n))

/-- `1/(1+n) ≤ β₀ < 1` whenever `D, n > 0`. -/
theorem betaThreshold_bounds {D n : ℝ} (hD : 0 < D) (hn : 0 < n) :
    1 / (1 + n) ≤ betaThreshold D n ∧ betaThreshold D n < 1 := by
  unfold betaThreshold
  constructor
  · rw [div_le_div_iff₀ (by linarith) (by positivity)]
    have : 0 ≤ n ^ 2 + n ^ 3 := by positivity
    nlinarith
  · rw [div_lt_one (by positivity)]; nlinarith

/-- **The golden-rule test** (fn 13 made precise): if `β(1 + n) > 1`, the steady state lies
strictly above the golden rule `f'(k*) = n` (so `f'(k̄) < n`, dynamic inefficiency) exactly
when `β > β₀`. -/
theorem inefficient_iff (hT : Technology f) {β n k ks : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hn : 0 < n) (hk : 0 < k) (hks : 0 < ks) (hdom : 1 < β * (1 + deriv f k))
    (hres : residual f β n k = 0) (hgr : deriv f ks = n) (hβn : 1 < β * (1 + n)) :
    deriv f k < n ↔ betaThreshold (f ks / ks - n) n < β := by
  have hD : 0 < f ks / ks - n := by
    have := hT.neo.deriv_mul_lt hks
    rw [hgr] at this
    rw [sub_pos, lt_div_iff₀ hks]; linarith
  have hdomks : 1 < β * (1 + deriv f ks) := by rw [hgr]; exact hβn
  -- `Φ(k*) > 0 ↔ β > β₀`
  have hsign : 0 < residual f β n ks / ks ↔ betaThreshold (f ks / ks - n) n < β := by
    rw [residual_golden_rule f hks hgr, betaThreshold]
    set D := f ks / ks - n
    have hden : 0 < β * (1 + n) - 1 := by linarith
    rw [sub_pos, div_lt_iff₀ (by positivity), mul_div_assoc', div_lt_iff₀ hden]
    constructor <;> intro h <;> nlinarith
  rw [← hsign]
  constructor
  · intro hlt
    -- `k* < k̄` and `Φ/k` strictly decreasing
    have hkk : ks < k := by
      by_contra hle
      push Not at hle
      have := hT.neo.deriv_strictAnti.antitoneOn hk hks hle
      linarith
    have := residual_div_strictAnti hT hβ hβ1 hn hks hkk hdom
    rw [hres, zero_div] at this
    exact this
  · intro hpos
    have hkk : ks < k := by
      by_contra hle
      push Not at hle
      rcases hle.lt_or_eq with hlt | heq
      · have := residual_div_strictAnti hT hβ hβ1 hn hk hlt hdomks
        rw [hres, zero_div] at this
        linarith
      · subst heq; rw [hres, zero_div] at hpos; exact lt_irrefl 0 hpos
    have := hT.neo.deriv_strictAnti hks hk hkk
    linarith

/-- **Dynamic inefficiency is possible** (O&R fn 13): for every `n > 0` there is `β₀ < 1`
such that with `β ∈ (β₀, 1)` the steady-state interest rate is below the growth rate,
`f'(k̄) < n`. -/
theorem dynamic_inefficiency_possible (hT : Technology f) {β n k ks : ℝ} (hβ1 : β < 1)
    (hn : 0 < n) (hk : 0 < k) (hks : 0 < ks) (hdom : 1 < β * (1 + deriv f k))
    (hres : residual f β n k = 0) (hgr : deriv f ks = n)
    (hβ0 : betaThreshold (f ks / ks - n) n < β) : deriv f k < n := by
  have hD : 0 < f ks / ks - n := by
    have := hT.neo.deriv_mul_lt hks
    rw [hgr] at this
    rw [sub_pos, lt_div_iff₀ hks]; linarith
  have hb := (betaThreshold_bounds hD hn).1
  have hβ : 0 < β := lt_of_lt_of_le (by positivity) (hb.trans hβ0.le)
  have hβn : 1 < β * (1 + n) := by
    have := lt_of_le_of_lt hb hβ0
    rw [div_lt_iff₀ (by linarith)] at this; linarith
  exact (inefficient_iff hT hβ hβ1 hn hk hks hdom hres hgr hβn).mpr hβ0

/-- **Dynamic efficiency with `β(1 + n) ≤ 1`**: then `f'(k̄) > (1 - β)/β ≥ n`. -/
theorem efficient_of_low_beta (f : ℝ → ℝ) {β n k : ℝ} (hβ : 0 < β)
    (hdom : 1 < β * (1 + deriv f k)) (hβn : β * (1 + n) ≤ 1) : n < deriv f k := by
  nlinarith

/-- For Cobb–Douglas `f = k^α` the threshold is `β₀ = (1 + αn)/(1 + n)` (fn 13). -/
theorem betaThreshold_cobbDouglas {α n ks : ℝ} (hα : 0 < α) (hn : 0 < n) (hks : 0 < ks)
    (hgr : α * ks ^ (α - 1) = n) :
    betaThreshold (ks ^ α / ks - n) n = (1 + α * n) / (1 + n) := by
  have hpow : ks ^ α / ks = ks ^ (α - 1) := by rw [Real.rpow_sub hks, Real.rpow_one]
  have hk1 : ks ^ (α - 1) = n / α := by field_simp; linarith
  rw [hpow, hk1, betaThreshold]
  field_simp
  ring

/-- **The numerical example** (survey check of fn 13): with `α = 0.3`, `n = 0.1` the
threshold is `β₀ = 1.03/1.1 ≈ 0.936`, so `β = 0.99` is dynamically inefficient while
`β = 0.9` is efficient. -/
theorem fn13_numbers :
    (1 + (0.3 : ℝ) * 0.1) / (1 + 0.1) < 0.99 ∧ (0.9 : ℝ) < (1 + (0.3 : ℝ) * 0.1) / (1 + 0.1) ∧
      1 < (0.99 : ℝ) * (1 + 0.1) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ## Local saddle-path stability of (32)–(33) -/

/-- The capital map of (32): `k' = [f(k) + k - c]/(1 + n)`. -/
noncomputable def nextK (f : ℝ → ℝ) (n k c : ℝ) : ℝ := (f k + k - c) / (1 + n)

/-- The consumption map of (33): `c' = [1 + f'(k')][β c - n(1 - β) k']`. -/
noncomputable def nextC (f : ℝ → ℝ) (β n k c : ℝ) : ℝ :=
  (1 + deriv f (nextK f n k c)) * (β * c - n * (1 - β) * nextK f n k c)

/-- `∂k'/∂k = (1 + f'(k))/(1 + n)`. -/
theorem nextK_hasDerivAt_k (hT : Technology f) {n k c : ℝ} (hk : 0 < k) :
    HasDerivAt (fun k => nextK f n k c) ((1 + deriv f k) / (1 + n)) k := by
  have h := ((((hT.neo.diff k hk).hasDerivAt).add (hasDerivAt_id' k)).sub_const c).div_const
    (1 + n)
  unfold nextK
  exact h.congr_deriv (by ring)

/-- `∂k'/∂c = -1/(1 + n)`. -/
theorem nextK_hasDerivAt_c (f : ℝ → ℝ) {n k c : ℝ} :
    HasDerivAt (fun c => nextK f n k c) (-1 / (1 + n)) c := by
  unfold nextK
  exact ((hasDerivAt_id' c).const_sub (f k + k)).div_const (1 + n)

/-- `∂c'/∂k` and `∂c'/∂c` at a point where `k' = k̄`, given `f''(k̄) = h`
(`E = h G - R n (1 - β)`, `G = βc - n(1-β)k̄`, `R = 1 + f'(k̄)`). -/
theorem nextC_hasDerivAt (hT : Technology f) {β n k c h : ℝ} (hk : 0 < k)
    (hfix : nextK f n k c = k) (h2 : HasDerivAt (deriv f) h k) :
    HasDerivAt (fun k => nextC f β n k c)
        ((h * (β * c - n * (1 - β) * k) - (1 + deriv f k) * (n * (1 - β))) *
          ((1 + deriv f k) / (1 + n))) k ∧
      HasDerivAt (fun c => nextC f β n k c)
        ((1 + deriv f k) * β - (h * (β * c - n * (1 - β) * k) -
          (1 + deriv f k) * (n * (1 - β))) / (1 + n)) c := by
  have hKk := nextK_hasDerivAt_k (n := n) (c := c) hT hk
  have hKc := nextK_hasDerivAt_c f (n := n) (k := k) (c := c)
  have h2' : HasDerivAt (deriv f) h (nextK f n k c) := by rw [hfix]; exact h2
  constructor
  · have hA := (h2'.comp k hKk).const_add 1
    have hB := (hKk.const_mul (n * (1 - β))).const_sub (β * c)
    have key := hA.mul hB
    unfold nextC
    refine HasDerivAt.congr_deriv key ?_
    simp only [Function.comp_apply, hfix]
    ring
  · have hA := (h2'.comp c hKc).const_add 1
    have hB := ((hasDerivAt_id c).const_mul β).sub (hKc.const_mul (n * (1 - β)))
    have key := hA.mul hB
    unfold nextC
    refine HasDerivAt.congr_deriv key ?_
    simp only [Function.comp_apply, Pi.sub_apply, id, hfix]
    field_simp
    ring

/-- A real quadratic `x² - T x + Δ` with `Δ > 0` and value `1 - T + Δ < 0` at `x = 1` has two
real roots `0 < λ₁ < 1 < λ₂`. -/
theorem quadratic_saddle {T Δ : ℝ} (hΔ : 0 < Δ) (hp1 : 1 - T + Δ < 0) :
    ∃ l1 l2 : ℝ, 0 < l1 ∧ l1 < 1 ∧ 1 < l2 ∧ ∀ x : ℝ, x ^ 2 - T * x + Δ = (x - l1) * (x - l2) := by
  have hdisc : 0 < T ^ 2 - 4 * Δ := by nlinarith [sq_nonneg (T - 2)]
  obtain ⟨sq, hsq0, hsq⟩ : ∃ sq : ℝ, 0 ≤ sq ∧ sq ^ 2 = T ^ 2 - 4 * Δ :=
    ⟨Real.sqrt (T ^ 2 - 4 * Δ), Real.sqrt_nonneg _, Real.sq_sqrt hdisc.le⟩
  have hprod : (1 - (T - sq) / 2) * (1 - (T + sq) / 2) = 1 - T + Δ := by nlinarith
  have h1 : 0 < 1 - (T - sq) / 2 := by nlinarith
  have h2 : 1 - (T + sq) / 2 < 0 := by nlinarith
  refine ⟨(T - sq) / 2, (T + sq) / 2, ?_, by linarith, by linarith, fun x => by nlinarith⟩
  have hroots : (T - sq) / 2 * ((T + sq) / 2) = Δ := by nlinarith
  nlinarith

/-- Entry `(1,1)` of the Jacobian of (32)–(33): `R/(1+n)`, `R = 1 + f'(k̄)`. -/
noncomputable def jac11 (f : ℝ → ℝ) (n k : ℝ) : ℝ := (1 + deriv f k) / (1 + n)

/-- Entry `(1,2)`: `-1/(1+n)`. -/
noncomputable def jac12 (n : ℝ) : ℝ := -1 / (1 + n)

/-- The auxiliary `E = f''(k̄) G - R n(1-β)`, `G = βc̄ - n(1-β)k̄`. -/
noncomputable def jacE (f : ℝ → ℝ) (β n k c h : ℝ) : ℝ :=
  h * (β * c - n * (1 - β) * k) - (1 + deriv f k) * (n * (1 - β))

/-- Entry `(2,1)`: `E R/(1+n)`. -/
noncomputable def jac21 (f : ℝ → ℝ) (β n k c h : ℝ) : ℝ := jacE f β n k c h * jac11 f n k

/-- Entry `(2,2)`: `Rβ - E/(1+n)`. -/
noncomputable def jac22 (f : ℝ → ℝ) (β n k c h : ℝ) : ℝ :=
  (1 + deriv f k) * β - jacE f β n k c h / (1 + n)

/-- The Jacobian entries are the partial derivatives of the maps (32)–(33) at a steady state
(`nextK k̄ c̄ = k̄`), given `f''(k̄) = h`. -/
theorem jacobian_spec (hT : Technology f) {β n k c h : ℝ} (hk : 0 < k)
    (hfix : nextK f n k c = k) (h2 : HasDerivAt (deriv f) h k) :
    HasDerivAt (fun k => nextK f n k c) (jac11 f n k) k ∧
      HasDerivAt (fun c => nextK f n k c) (jac12 n) c ∧
      HasDerivAt (fun k => nextC f β n k c) (jac21 f β n k c h) k ∧
      HasDerivAt (fun c => nextC f β n k c) (jac22 f β n k c h) c :=
  ⟨nextK_hasDerivAt_k hT hk, nextK_hasDerivAt_c f, (nextC_hasDerivAt hT hk hfix h2).1,
    (nextC_hasDerivAt hT hk hfix h2).2⟩

/-- **Local saddle-path stability** (O&R Fig. 7.7, the saddle path `SS`): at the steady state
`(k̄, c̄)` of (32)–(33), with `f''(k̄) = h ≤ 0`, the characteristic polynomial of the Jacobian
factors as `(x - λ₁)(x - λ₂)` with `0 < λ₁ < 1 < λ₂`: one stable, monotone direction and one
unstable direction. The key inequality `(Rβ - (1+n))(R - 1) < 0` is derived from
`f'(k̄) k̄ < f(k̄)` and the steady-state equations. -/
theorem saddle_eigenvalues (hT : Technology f) {β n k c h : ℝ} (hβ1 : β < 1)
    (hn : 0 < n) (hk : 0 < k) (hc : 0 < c) (hh : h ≤ 0) (hss1 : c = f k - n * k)
    (hss2 : c = (1 + deriv f k) * (β * c - n * (1 - β) * k)) :
    ∃ l1 l2 : ℝ, 0 < l1 ∧ l1 < 1 ∧ 1 < l2 ∧ ∀ x : ℝ,
      (x - jac11 f n k) * (x - jac22 f β n k c h) - jac12 n * jac21 f β n k c h =
        (x - l1) * (x - l2) := by
  have hdom := ((deltaC_zero_iff f hβ1 hn hk hc (by linarith [hT.neo.deriv_pos hk])).mp hss2).1
  have hmp := hT.neo.deriv_mul_lt hk
  unfold jac21 jac22 jac11 jac12 jacE
  generalize hR : 1 + deriv f k = R at *
  generalize hG : β * c - n * (1 - β) * k = G at *
  have hR1 : 1 < R := by rw [← hR]; linarith [hT.neo.deriv_pos hk]
  have hn1 : 0 < 1 + n := by linarith
  have hβ : 0 < β := by nlinarith
  have hGpos : 0 < G := by nlinarith
  -- key inequality from `f'(k) k < f(k)`
  have hK1 : (R * β - (1 + n)) * (R - 1) < 0 := by
    have hc' : c * (R * β - 1) = R * (n * (1 - β)) * k := by rw [← hG] at hss2; linarith
    have h1 : (R - 1 - n) * k < c := by rw [← hR] at *; linarith
    have h2 := mul_lt_mul_of_pos_right h1 (by linarith : 0 < R * β - 1)
    have h3 : (R - 1 - n) * (R * β - 1) < R * (n * (1 - β)) := by
      have : (R - 1 - n) * (R * β - 1) * k < R * (n * (1 - β)) * k := by nlinarith
      exact lt_of_mul_lt_mul_right this hk.le
    nlinarith
  set E := h * G - R * (n * (1 - β)) with hE
  set T := R / (1 + n) + (R * β - E / (1 + n)) with hT'
  set Δ := R / (1 + n) * (R * β - E / (1 + n)) - -1 / (1 + n) * (E * (R / (1 + n))) with hΔ'
  have hΔ : Δ = R ^ 2 * β / (1 + n) := by rw [hΔ']; field_simp; ring
  have hΔpos : 0 < Δ := by rw [hΔ]; positivity
  have hp1 : 1 - T + Δ < 0 := by
    have e : (1 - T + Δ) * (1 + n) = (R * β - (1 + n)) * (R - 1) + h * G := by
      rw [hT', hΔ', hE]; field_simp; ring
    have : h * G ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hh hGpos.le
    have : (1 - T + Δ) * (1 + n) < 0 := by rw [e]; linarith
    exact neg_of_mul_neg_left this hn1.le
  obtain ⟨l1, l2, h1, h2, h3, hfac⟩ := quadratic_saddle hΔpos hp1
  refine ⟨l1, l2, h1, h2, h3, fun x => ?_⟩
  rw [← hfac x, hT', hΔ']
  ring

/-! ## Exercise 1: government spending (O&R p. 512) -/

/-- **Ex. 1(a), eq. (32) with spending**: with a per-capita tax `g` on everyone alive, each
vintage's budget (30) has wage `w - g`, and aggregation gives
`k_{t+1} - k_t = [f(k_t) - c_t - g - n k_t]/(1 + n)`. -/
theorem eq32_gov (f : ℝ → ℝ) {n k k' c g : ℝ} (hn : 0 < 1 + n)
    (h : (1 + n) * k' = (1 + deriv f k) * k + ((f k - k * deriv f k) - g) - c) :
    k' - k = (f k - c - g - n * k) / (1 + n) := by
  rw [eq_div_iff (ne_of_gt hn)]
  linarith

/-- **Ex. 1(a), eq. (33) is unchanged**: the newborn gap depends only on financial wealth,
because human wealth *net of taxes* is common to every living vintage; so with any common
`H` (in particular the present value of `w - g`), `c_{t+1} - c^{t+1}_{t+1} = (1-β)(1+r)k_{t+1}`
and (33) follows exactly as without spending. -/
theorem eq33_gov {n β Hnet R : ℝ} (hn : 0 < 1 + n) {kv cv : ℕ → ℕ → ℝ} (t : ℕ)
    (hrule : ∀ v, v ≤ t + 1 → cv v (t + 1) = (1 - β) * (R * kv v (t + 1) + Hnet))
    (hnew : kv (t + 1) (t + 1) = 0) :
    aggregate n cv (t + 1) - cv (t + 1) (t + 1) = (1 - β) * R * aggregate n kv (t + 1) :=
  newborn_gap hn t hrule hnew

/-- The steady-state residual with spending: `Φ_g(k) = Φ(k) - g` (the `Δk = 0` locus shifts
down by `g`, the `Δc = 0` locus does not move; Ex. 1(b)). -/
theorem residual_gov (f : ℝ → ℝ) {β n g k c : ℝ} (hc : c = f k - n * k - g)
    (hlocus : c = n * (1 - β) * k * qCoef f β k) : residual f β n k = g := by
  unfold residual; linarith

/-- **Ex. 1(b), crowding out**: if `(k̄_g, c̄_g)` is a steady state with spending `g > 0` and
`(k̄, c̄)` the steady state without, then capital and consumption are both strictly lower:
`k̄_g < k̄` and `c̄_g < c̄` (the `Δc = 0` locus is increasing). -/
theorem crowding_out (hT : Technology f) {β n g k kg : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hn : 0 < n) (hg : 0 < g) (hk : 0 < k) (hkg : 0 < kg) (hd : 1 < β * (1 + deriv f k))
    (hdg : 1 < β * (1 + deriv f kg)) (hr : residual f β n k = 0)
    (hrg : residual f β n kg = g) :
    kg < k ∧ n * (1 - β) * kg * qCoef f β kg < n * (1 - β) * k * qCoef f β k := by
  have hkk : kg < k := by
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt | heq
    · have := residual_div_strictAnti hT hβ hβ1 hn hk hlt hdg
      rw [hr, hrg, zero_div] at this
      have : 0 < g / kg := div_pos hg hkg
      linarith
    · subst heq; linarith
  refine ⟨hkk, ?_⟩
  have hq := qCoef_strictMono hT hβ hkg hkk hd
  have hq0 : 0 < qCoef f β kg := div_pos (by nlinarith) (by linarith)
  have : 0 < n * (1 - β) := mul_pos hn (by linarith)
  have h1 : n * (1 - β) * kg * qCoef f β kg < n * (1 - β) * k * qCoef f β kg := by
    have := mul_lt_mul_of_pos_left hkk this
    exact mul_lt_mul_of_pos_right this hq0
  have h2 : n * (1 - β) * k * qCoef f β kg < n * (1 - β) * k * qCoef f β k :=
    mul_lt_mul_of_pos_left hq (mul_pos this hk)
  linarith

/-- **Ex. 1(b): with spending the steady state need not be unique** (a flag: the book's
phase-diagram argument is silent on this). The `Δk = 0` locus `c = f(k) - nk - g` starts below
the `Δc = 0` locus, so for every `g` below the height `Φ(k_m)` of the residual at some
`k_m ∈ (0, k̄)` there are two distinct steady states `k₁ < k_m < k₂ < k̄`
(`Φ(k) = g`); both lie below the no-spending steady state (crowding out applies to each). -/
theorem two_steady_states_with_spending (hT : Technology f) {β n g km kbar : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hn : 0 < n) (hg : 0 < g) (hkm : 0 < km) (hkmk : km < kbar)
    (hd : 1 < β * (1 + deriv f kbar)) (hr : residual f β n kbar = 0)
    (hgm : g < residual f β n km) :
    ∃ k1 k2, 0 < k1 ∧ k1 < km ∧ km < k2 ∧ k2 < kbar ∧
      residual f β n k1 = g ∧ residual f β n k2 = g := by
  have hdom : ∀ k, 0 < k → k ≤ kbar → 1 < β * (1 + deriv f k) := by
    intro k hk hle
    rcases hle.lt_or_eq with hlt | heq
    · have := hT.neo.deriv_strictAnti hk (hk.trans hlt) hlt; nlinarith
    · rw [heq]; exact hd
  have hq : ContinuousOn (qCoef f β) (Icc km kbar ∪ Ioc 0 km) := by
    refine ContinuousOn.div (continuousOn_const.add (hT.prime_cont.mono ?_))
      ((continuousOn_const.mul (continuousOn_const.add (hT.prime_cont.mono ?_))).sub
        continuousOn_const) ?_
    · rintro x (hx | hx)
      · exact lt_of_lt_of_le hkm hx.1
      · exact hx.1
    · rintro x (hx | hx)
      · exact lt_of_lt_of_le hkm hx.1
      · exact hx.1
    · rintro x (hx | hx)
      · have := hdom x (lt_of_lt_of_le hkm hx.1) hx.2; linarith
      · have := hdom x hx.1 (hx.2.trans hkmk.le); linarith
  have hΦ : ContinuousOn (residual f β n) (Icc km kbar ∪ Ioc 0 km) := by
    have hfc : ContinuousOn f (Icc km kbar ∪ Ioc 0 km) := hT.neo.cont.mono (by
      rintro x (hx | hx)
      · exact mem_Ici.mpr (hkm.le.trans hx.1)
      · exact mem_Ici.mpr hx.1.le)
    unfold residual
    exact (hfc.sub (continuousOn_const.mul continuousOn_id)).sub
      ((continuousOn_const.mul continuousOn_id).mul hq)
  -- a point near zero where `Φ < g`
  obtain ⟨ε, hε0, hεkm, hfε⟩ : ∃ ε, 0 < ε ∧ ε < km ∧ f ε < g := by
    have hf0 : Tendsto f (𝓝[>] 0) (𝓝 0) := by
      have := (hT.neo.cont 0 (mem_Ici.mpr le_rfl)).tendsto
      rw [hT.neo.zero] at this
      exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    obtain ⟨ε, hε, hεf, hεk⟩ := ((eventually_mem_nhdsWithin :
      ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi 0).and ((hf0.eventually (gt_mem_nhds hg)).and
        (Ioo_mem_nhdsGT hkm))).exists
    exact ⟨ε, hε, hεk.2, hεf⟩
  have hΦε : residual f β n ε < g := by
    have hqε : 0 < qCoef f β ε := div_pos (by linarith [hT.neo.deriv_pos hε0])
      (by linarith [hdom ε hε0 (hεkm.le.trans hkmk.le)])
    have : 0 ≤ n * ε + n * (1 - β) * ε * qCoef f β ε := by
      have : 0 < 1 - β := by linarith
      positivity
    unfold residual
    linarith
  obtain ⟨k1, hk1, hk1g⟩ := intermediate_value_Icc hεkm.le (hΦ.mono (fun x hx =>
    Or.inr ⟨lt_of_lt_of_le hε0 hx.1, hx.2⟩)) (⟨hΦε.le, hgm.le⟩ : g ∈ Icc _ _)
  obtain ⟨k2, hk2, hk2g⟩ := intermediate_value_Icc' hkmk.le (hΦ.mono (fun x hx => Or.inl hx))
    (⟨by rw [hr]; exact hg.le, hgm.le⟩ : g ∈ Icc _ _)
  have hk1m : k1 < km := lt_of_le_of_ne hk1.2 (fun h => by rw [h] at hk1g; linarith)
  have hk2m : km < k2 := lt_of_le_of_ne hk2.1 (fun h => by rw [← h] at hk2g; linarith)
  have hk2b : k2 < kbar := lt_of_le_of_ne hk2.2 (fun h => by rw [h, hr] at hk2g; linarith)
  exact ⟨k1, k2, lt_of_lt_of_le hε0 hk1.1, hk1m, hk2m, hk2b, hk1g, hk2g⟩

/-- **Ex. 1(c), impact effect at given prices**: announcing at date 0 a per-capita tax `g`
from date `T` on lowers every living vintage's date-0 consumption under the log rule
`c = (1 - β)(a + H)` by exactly `(1 - β) ∑_{s ≥ T} D_s g`, since human wealth net of taxes
falls by the present value of the future taxes. (Partial equilibrium at given prices; the
general-equilibrium path is `announcement_equilibrium`.) -/
theorem announced_spending_impact {β g a0 : ℝ} {D w : ℕ → ℝ} (T : ℕ) (hβ1 : β < 1)
    (hg : 0 < g) (hDpos : ∀ s, 0 < D s) (hw : Summable (fun s => D s * w s))
    (hD : Summable D) :
    (1 - β) * (a0 + ∑' s, D s * (w s - if T ≤ s then g else 0)) -
        (1 - β) * (a0 + ∑' s, D s * w s) =
      -((1 - β) * ∑' s, D (s + T) * g) ∧
      (1 - β) * (a0 + ∑' s, D s * (w s - if T ≤ s then g else 0)) <
        (1 - β) * (a0 + ∑' s, D s * w s) := by
  have htax : Summable (fun s => D s * (if T ≤ s then g else 0)) :=
    (hD.mul_right g).of_nonneg_of_le (fun s => by
      split_ifs
      · exact mul_nonneg (hDpos s).le hg.le
      · rw [mul_zero]) (fun s => by
      split_ifs
      · exact le_refl _
      · rw [mul_zero]; exact mul_nonneg (hDpos s).le hg.le)
  have hsplit : ∑' s, D s * (w s - if T ≤ s then g else 0) =
      ∑' s, D s * w s - ∑' s, D s * (if T ≤ s then g else 0) := by
    rw [← hw.tsum_sub htax]; congr 1; ext s; ring
  have htail : ∑' s, D s * (if T ≤ s then g else 0) = ∑' s, D (s + T) * g := by
    rw [← htax.sum_add_tsum_nat_add T]
    have h0 : ∑ s ∈ Finset.range T, D s * (if T ≤ s then g else 0) = 0 :=
      Finset.sum_eq_zero (fun s hs => by
        have : ¬ T ≤ s := by have := Finset.mem_range.mp hs; omega
        simp [this])
    rw [h0, zero_add]
    congr 1; ext s
    have : T ≤ s + T := by omega
    simp [this]
  have hpos : 0 < ∑' s, D (s + T) * g :=
    ((summable_nat_add_iff T).mpr (hD.mul_right g)).tsum_pos
      (fun s => (mul_pos (hDpos _) hg).le) 0 (mul_pos (hDpos _) hg)
  rw [hsplit, htail]
  have h1β : 0 < 1 - β := by linarith
  refine ⟨by ring, ?_⟩
  nlinarith

/-! ## The global saddle path of (32)–(33) (O&R Fig. 7.7)

A path `(k_t, c_t)` of (32)–(33) is an equilibrium only if it stays in the positive quadrant.
We prove that from every `k₀ > 0` there is exactly one initial consumption `c₀` whose orbit
stays positive for ever; that this orbit is the competitive equilibrium (consumption is
`1 - β` times financial plus human wealth); and that it converges monotonically to the unique
steady state. Existence is by shooting (orbits are ordered in `c₀`, "too low" and "too high"
initial consumption are open sets, the separating value stays positive); uniqueness is by
the human-wealth representation, which every positive orbit satisfies because the gap
`X_t = c_t - (1-β)(R_t k_t + H_t)` grows like `∏ R_j` while positive orbits are bounded. -/

/-- One step of (32)–(33) on `(k, c)`. -/
noncomputable def wstep (f : ℝ → ℝ) (β n : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (nextK f n p.1 p.2, nextC f β n p.1 p.2)

/-- The orbit of (32)–(33) from `(k₀, c₀)`. -/
noncomputable def orb (f : ℝ → ℝ) (β n k0 c0 : ℝ) (t : ℕ) : ℝ × ℝ := (wstep f β n)^[t] (k0, c0)

/-- The orbit satisfies the recursion (32)–(33). -/
theorem orb_succ (f : ℝ → ℝ) (β n k0 c0 : ℝ) (t : ℕ) :
    orb f β n k0 c0 (t + 1) = wstep f β n (orb f β n k0 c0 t) :=
  Function.iterate_succ_apply' _ _ _

/-- The orbit starts at `(k₀, c₀)`. -/
theorem orb_zero (f : ℝ → ℝ) (β n k0 c0 : ℝ) : orb f β n k0 c0 0 = (k0, c0) := rfl

/-- Staying in the positive quadrant for ever. -/
def PosOrbit (f : ℝ → ℝ) (β n k0 c0 : ℝ) : Prop :=
  ∀ t, 0 < (orb f β n k0 c0 t).1 ∧ 0 < (orb f β n k0 c0 t).2

/-- Output is nonnegative at nonnegative capital. -/
theorem f_nonneg (hT : Technology f) {k : ℝ} (hk : 0 ≤ k) : 0 ≤ f k := by
  rcases hk.lt_or_eq with h | h
  · exact (hT.neo.pos h).le
  · rw [← h, hT.neo.zero]

/-- Output is monotone on `[0, ∞)`. -/
theorem f_mono (hT : Technology f) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : f a ≤ f b :=
  hT.neo.strictMono.monotoneOn (mem_Ici.mpr ha) (mem_Ici.mpr (ha.trans hab)) hab

/-- The wage `w(k) = f(k) - k f'(k)` is nonnegative and nondecreasing on `(0, ∞)`. -/
theorem wage_nonneg_mono (hT : Technology f) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ f a - a * deriv f a ∧ f a - a * deriv f a ≤ f b - b * deriv f b := by
  have hb : 0 < b := ha.trans_le hab
  refine ⟨by linarith [hT.neo.deriv_mul_lt ha], ?_⟩
  have ht := hT.neo.tangent_le hb ha.le
  have hd := hT.neo.deriv_strictAnti.antitoneOn ha hb hab
  nlinarith

/-- **Orbits are ordered** (the map is monotone for the order `k ↓, c ↑`): if two positive
orbits start with `k^a₀ ≤ k^b₀` and `c^a₀ ≥ c^b₀`, then `k^a_t ≤ k^b_t` and `c^a_t ≥ c^b_t` for
all `t`. -/
theorem orbit_compare (hT : Technology f) {β n : ℝ} (hβ1 : β < 1) (hn : 0 < n)
    {ka kb ca cb : ℝ} (ha : PosOrbit f β n ka ca) (hb : PosOrbit f β n kb cb) (hk : ka ≤ kb)
    (hc : cb ≤ ca) (t : ℕ) :
    (orb f β n ka ca t).1 ≤ (orb f β n kb cb t).1 ∧
      (orb f β n kb cb t).2 ≤ (orb f β n ka ca t).2 := by
  induction t with
  | zero => exact ⟨hk, hc⟩
  | succ t ih =>
    obtain ⟨hk', hc'⟩ := ih
    obtain ⟨hpa, -⟩ := ha t
    obtain ⟨hpb, -⟩ := hb t
    obtain ⟨hpa1, hca1⟩ := ha (t + 1)
    obtain ⟨hpb1, hcb1⟩ := hb (t + 1)
    simp only [orb_succ, wstep] at hpa1 hca1 hpb1 hcb1 ⊢
    have hK : nextK f n (orb f β n ka ca t).1 (orb f β n ka ca t).2 ≤
        nextK f n (orb f β n kb cb t).1 (orb f β n kb cb t).2 := by
      unfold nextK
      apply div_le_div_of_nonneg_right _ (by linarith)
      have := f_mono hT hpa.le hk'
      linarith
    refine ⟨hK, ?_⟩
    unfold nextC at hca1 hcb1 ⊢
    set Ka := nextK f n (orb f β n ka ca t).1 (orb f β n ka ca t).2
    set Kb := nextK f n (orb f β n kb cb t).1 (orb f β n kb cb t).2
    have hR : deriv f Kb ≤ deriv f Ka := hT.neo.deriv_strictAnti.antitoneOn hpa1 hpb1 hK
    have hRb : 0 < 1 + deriv f Kb := by linarith [hT.neo.deriv_pos hpb1]
    have hAb : 0 < β * (orb f β n kb cb t).2 - n * (1 - β) * Kb := by
      by_contra h; push Not at h
      have := mul_nonpos_of_nonneg_of_nonpos hRb.le h
      linarith
    have hA : β * (orb f β n kb cb t).2 - n * (1 - β) * Kb ≤
        β * (orb f β n ka ca t).2 - n * (1 - β) * Ka := by
      have hβ : 0 < β := by
        by_contra h; push Not at h
        have : β * (orb f β n kb cb t).2 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg h (hb t).2.le
        nlinarith [mul_pos (mul_pos hn (by linarith : (0 : ℝ) < 1 - β)) hpb1]
      have := mul_le_mul_of_nonneg_left hc' hβ.le
      have := mul_le_mul_of_nonneg_left hK (mul_pos hn (by linarith : (0 : ℝ) < 1 - β)).le
      linarith
    calc (1 + deriv f Kb) * (β * (orb f β n kb cb t).2 - n * (1 - β) * Kb)
        ≤ (1 + deriv f Ka) * (β * (orb f β n kb cb t).2 - n * (1 - β) * Kb) :=
          mul_le_mul_of_nonneg_right (by linarith) hAb.le
      _ ≤ (1 + deriv f Ka) * (β * (orb f β n ka ca t).2 - n * (1 - β) * Ka) :=
          mul_le_mul_of_nonneg_left hA (by linarith)

/-- A linear bound on output: `f(k) ≤ (n/2) k + C` for all `k ≥ 0`. -/
theorem f_linear_bound (hT : Technology f) {n : ℝ} (hn : 0 < n) :
    ∃ C, 0 ≤ C ∧ ∀ k, 0 ≤ k → f k ≤ n / 2 * k + C := by
  obtain ⟨K, hK1, hK⟩ := exists_capacity_of_marginal_tendsto_zero f (k0 := 1) (half_pos hn)
    hT.neo.strictConcave.concaveOn hT.neo.diff (fun k hk => (hT.neo.deriv_pos hk).le)
    hT.inadaTop
  have hK0 : 0 ≤ K := le_trans zero_le_one hK1
  refine ⟨f K, f_nonneg hT hK0, fun k hk => ?_⟩
  rcases le_total k K with h | h
  · have := f_mono hT hk h; nlinarith
  · have := hK k h; have := f_nonneg hT hK0; linarith

/-- **Positive orbits are bounded**: capital stays below `max(k₀, 2C/n)`. -/
theorem posOrbit_bounded (hT : Technology f) {β n k0 c0 : ℝ} (hn : 0 < n)
    (hp : PosOrbit f β n k0 c0) : ∃ K, 0 < K ∧ ∀ t, (orb f β n k0 c0 t).1 ≤ K := by
  obtain ⟨C, hC, hfC⟩ := f_linear_bound hT hn
  have hk0 : 0 < k0 := (hp 0).1
  refine ⟨max k0 (2 * C / n), lt_of_lt_of_le hk0 (le_max_left _ _), fun t => ?_⟩
  induction t with
  | zero => exact le_max_left _ _
  | succ t ih =>
    obtain ⟨hkt, hct⟩ := hp t
    rw [orb_succ]
    simp only [wstep, nextK]
    rw [div_le_iff₀ (by linarith)]
    have h1 := hfC _ hkt.le
    have h2 : 2 * C / n ≤ max k0 (2 * C / n) := le_max_right _ _
    have h3 : C ≤ n / 2 * max k0 (2 * C / n) := by
      rw [div_le_iff₀ hn] at h2; nlinarith
    nlinarith

/-- Discount factors along a capital path: `D₀ = 1`, `D_{t+1} = D_t/(1 + f'(k_{t+1}))`. -/
noncomputable def discF (f : ℝ → ℝ) (k : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => discF f k t / (1 + deriv f (k (t + 1)))

/-- The wage along a capital path, `w_t = f(k_t) - k_t f'(k_t)`. -/
noncomputable def wageF (f : ℝ → ℝ) (k : ℕ → ℝ) (t : ℕ) : ℝ := f (k t) - k t * deriv f (k t)

/-- Discount factors are positive along a positive capital path. -/
theorem discF_pos (hT : Technology f) {k : ℕ → ℝ} (hk : ∀ t, 0 < k t) (t : ℕ) :
    0 < discF f k t := by
  induction t with
  | zero => simp [discF]
  | succ t ih =>
    simp only [discF]
    exact div_pos ih (by linarith [hT.neo.deriv_pos (hk (t + 1))])

/-- Along a path bounded by `K`, discount factors fall at least geometrically:
`D_{s+t} ≤ D_t ρ^s` with `ρ = 1/(1 + f'(K)) < 1`. -/
theorem discF_ratio (hT : Technology f) {k : ℕ → ℝ} {K : ℝ} (hk : ∀ t, 0 < k t)
    (hK : ∀ t, k t ≤ K) (t s : ℕ) :
    discF f k (s + t) ≤ discF f k t * (1 / (1 + deriv f K)) ^ s := by
  have hK0 : 0 < K := (hk 0).trans_le (hK 0)
  have hR : 0 < 1 + deriv f K := by linarith [hT.neo.deriv_pos hK0]
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show s + 1 + t = (s + t) + 1 by ring]
    simp only [discF]
    have hd : deriv f K ≤ deriv f (k (s + t + 1)) :=
      hT.neo.deriv_strictAnti.antitoneOn (hk _) hK0 (hK _)
    have hpos := discF_pos hT hk (s + t)
    rw [div_le_iff₀ (by linarith [hT.neo.deriv_pos (hk (s + t + 1))]), pow_succ]
    calc discF f k (s + t) ≤ discF f k t * (1 / (1 + deriv f K)) ^ s := ih
      _ = discF f k t * (1 / (1 + deriv f K)) ^ s * (1 / (1 + deriv f K)) *
            (1 + deriv f K) := by field_simp
      _ ≤ discF f k t * (1 / (1 + deriv f K)) ^ s * (1 / (1 + deriv f K)) *
            (1 + deriv f (k (s + t + 1))) := by
          apply mul_le_mul_of_nonneg_left (by linarith)
          have := discF_pos hT hk t
          positivity
      _ = _ := by ring

/-- **The human-wealth representation of a positive orbit** (O&R p. 447): along any orbit of
(32)–(33) that stays in the positive quadrant, the present value of wages `∑ D_t w_t` converges
and initial consumption is `c₀ = (1 - β)[(1 + f'(k₀)) k₀ + ∑ D_t w_t]`, i.e. the log rule with
the market's human wealth: the orbit is the competitive equilibrium. -/
theorem posOrbit_representation (hT : Technology f) {β n k0 c0 : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hn : 0 < n) (hp : PosOrbit f β n k0 c0) :
    Summable (fun t => discF f (fun t => (orb f β n k0 c0 t).1) t *
        wageF f (fun t => (orb f β n k0 c0 t).1) t) ∧
      c0 = (1 - β) * ((1 + deriv f k0) * k0 + ∑' t, discF f (fun t => (orb f β n k0 c0 t).1) t *
        wageF f (fun t => (orb f β n k0 c0 t).1) t) := by
  set k : ℕ → ℝ := fun t => (orb f β n k0 c0 t).1
  set c : ℕ → ℝ := fun t => (orb f β n k0 c0 t).2
  have hk : ∀ t, 0 < k t := fun t => (hp t).1
  have hc : ∀ t, 0 < c t := fun t => (hp t).2
  have hkrec : ∀ t, k (t + 1) = nextK f n (k t) (c t) := fun t => by
    simp only [k, c, orb_succ, wstep]
  have hcrec : ∀ t, c (t + 1) = (1 + deriv f (k (t + 1))) * (β * c t - n * (1 - β) * k (t + 1)) :=
    fun t => by rw [hkrec]; simp only [k, c, orb_succ, wstep, nextC]
  obtain ⟨K, hK0, hK⟩ := posOrbit_bounded hT hn hp
  set ρ := 1 / (1 + deriv f K)
  have hRK : 1 < 1 + deriv f K := by linarith [hT.neo.deriv_pos hK0]
  have hρ0 : 0 < ρ := by simp only [ρ]; positivity
  have hρ1 : ρ < 1 := by simp only [ρ]; rw [div_lt_one (by linarith)]; exact hRK
  set W := f K
  set D := discF f k
  set w := wageF f k
  have hD := discF_pos hT hk
  have hw : ∀ t, 0 ≤ w t ∧ w t ≤ W := by
    intro t
    have h1 := (wage_nonneg_mono hT (hk t) le_rfl).1
    refine ⟨h1, ?_⟩
    have := f_mono hT (hk t).le (hK t)
    have := mul_pos (hk t) (hT.neo.deriv_pos (hk t))
    simp only [w, wageF]; linarith
  have hratio := discF_ratio hT hk hK
  have hgeo := summable_geometric_of_lt_one hρ0.le hρ1
  -- summability of the tails
  have hsumt : ∀ t, Summable (fun s => D (s + t) * w (s + t)) := by
    intro t
    refine Summable.of_nonneg_of_le (fun s => mul_nonneg (hD _).le (hw _).1) (fun s => ?_)
      ((hgeo.mul_left (D t)).mul_right W)
    calc D (s + t) * w (s + t) ≤ D (s + t) * W := mul_le_mul_of_nonneg_left (hw _).2 (hD _).le
      _ ≤ D t * ρ ^ s * W := mul_le_mul_of_nonneg_right (hratio t s) ((hw 0).1.trans (hw 0).2)
  set Tt : ℕ → ℝ := fun t => ∑' s, D (s + t) * w (s + t)
  have hTt_le : ∀ t, Tt t ≤ D t * (W / (1 - ρ)) := by
    intro t
    have := (hsumt t).tsum_le_tsum (fun s => ?_) ((hgeo.mul_left (D t)).mul_right W)
    · rw [tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one hρ0.le hρ1] at this
      simp only [Tt]
      calc _ ≤ D t * (1 - ρ)⁻¹ * W := this
        _ = D t * (W / (1 - ρ)) := by ring
    · calc D (s + t) * w (s + t) ≤ D (s + t) * W :=
            mul_le_mul_of_nonneg_left (hw _).2 (hD _).le
        _ ≤ D t * ρ ^ s * W := mul_le_mul_of_nonneg_right (hratio t s) ((hw 0).1.trans (hw 0).2)
  have hTt_nn : ∀ t, 0 ≤ Tt t := fun t => tsum_nonneg (fun s => mul_nonneg (hD _).le (hw _).1)
  have hTt_rec : ∀ t, Tt t = D t * w t + Tt (t + 1) := by
    intro t
    simp only [Tt]
    rw [(hsumt t).tsum_eq_zero_add]
    simp only [zero_add]
    congr 1
    congr 1; funext s; rw [show s + 1 + t = s + (t + 1) by ring]
  set H : ℕ → ℝ := fun t => Tt t / D t
  set X : ℕ → ℝ := fun t => c t - (1 - β) * ((1 + deriv f (k t)) * k t + H t)
  have hDrec : ∀ t, D (t + 1) = D t / (1 + deriv f (k (t + 1))) := fun t => rfl
  have hXrec : ∀ t, X (t + 1) = (1 + deriv f (k (t + 1))) * X t := by
    intro t
    have hR1 : 0 < 1 + deriv f (k (t + 1)) := by linarith [hT.neo.deriv_pos (hk (t + 1))]
    have hH1 : H (t + 1) = (1 + deriv f (k (t + 1))) * (H t - w t) := by
      have hDt : D t ≠ 0 := ne_of_gt (hD t)
      simp only [H]
      rw [hDrec, hTt_rec t]
      field_simp
      ring
    have h32 : (1 + n) * k (t + 1) = (1 + deriv f (k t)) * k t + w t - c t := by
      rw [hkrec]; simp only [nextK, w, wageF]; field_simp; ring
    simp only [X]
    rw [hcrec, hH1]
    linear_combination (-(1 + deriv f (k (t + 1))) * (1 - β)) * h32
  -- `X` is bounded
  set Bx := 2 * (K + W) + W / (1 - ρ)
  have hXb : ∀ t, |X t| ≤ Bx := by
    intro t
    have hct : c t < f (k t) + k t := by
      have := hk (t + 1); rw [hkrec] at this; simp only [nextK] at this
      rwa [div_pos_iff_of_pos_right (by linarith), sub_pos] at this
    have hfk : f (k t) ≤ W := f_mono hT (hk t).le (hK t)
    have hRk : (1 + deriv f (k t)) * k t ≤ k t + f (k t) := by
      have := hT.neo.deriv_mul_lt (hk t); nlinarith
    have hRk0 : 0 ≤ (1 + deriv f (k t)) * k t :=
      mul_nonneg (by linarith [hT.neo.deriv_pos (hk t)]) (hk t).le
    have hH0 : 0 ≤ H t := div_nonneg (hTt_nn t) (hD t).le
    have hHb : H t ≤ W / (1 - ρ) := by
      simp only [H]; rw [div_le_iff₀ (hD t)]; linarith [hTt_le t]
    have hWρ : 0 ≤ W / (1 - ρ) := div_nonneg (f_nonneg hT hK0.le) (by linarith)
    simp only [X]
    rw [abs_le]
    constructor <;> nlinarith [hc t, hK t]
  -- hence `X₀ = 0`
  have hX0 : X 0 = 0 := by
    by_contra hne
    have hgrow : ∀ t, (1 + deriv f K) ^ t * |X 0| ≤ |X t| := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        have hR1 : 0 < 1 + deriv f (k (t + 1)) := by linarith [hT.neo.deriv_pos (hk (t + 1))]
        rw [hXrec, abs_mul, abs_of_pos hR1, pow_succ]
        have hd : deriv f K ≤ deriv f (k (t + 1)) :=
          hT.neo.deriv_strictAnti.antitoneOn (hk _) hK0 (hK _)
        have := abs_nonneg (X t)
        nlinarith
    have hpos : 0 < |X 0| := abs_pos.mpr hne
    have hinf := (tendsto_pow_atTop_atTop_of_one_lt hRK).atTop_mul_const hpos
    obtain ⟨t, ht⟩ := (hinf.eventually (eventually_gt_atTop Bx)).exists
    linarith [hgrow t, hXb t]
  refine ⟨by simpa using hsumt 0, ?_⟩
  have hH0 : H 0 = ∑' t, D t * w t := by
    simp only [H, Tt, add_zero]
    have : D 0 = 1 := rfl
    rw [this, div_one]
  have : X 0 = c0 - (1 - β) * ((1 + deriv f k0) * k0 + H 0) := rfl
  rw [hH0] at this
  linarith

/-- Along ordered positive orbits the discounted wage sums are ordered. -/
theorem discounted_wages_le (hT : Technology f) {k k' : ℕ → ℝ} (hk : ∀ t, 0 < k t)
    (hk' : ∀ t, 0 < k' t) (hle : ∀ t, k t ≤ k' t) (hs : Summable (fun t => discF f k t *
      wageF f k t)) (hs' : Summable (fun t => discF f k' t * wageF f k' t)) (t0 : ℕ) :
    ∑' t, discF f k (t + t0) * wageF f k (t + t0) ≤
      ∑' t, discF f k' (t + t0) * wageF f k' (t + t0) := by
  have hD : ∀ t, discF f k t ≤ discF f k' t := by
    intro t
    induction t with
    | zero => simp [discF]
    | succ t ih =>
      simp only [discF]
      have hd : deriv f (k' (t + 1)) ≤ deriv f (k (t + 1)) :=
        hT.neo.deriv_strictAnti.antitoneOn (hk _) (hk' _) (hle _)
      have h1 := discF_pos hT hk t
      have hR : 0 < 1 + deriv f (k' (t + 1)) := by linarith [hT.neo.deriv_pos (hk' (t + 1))]
      rw [div_le_div_iff₀ (by linarith [hT.neo.deriv_pos (hk (t + 1))]) hR]
      nlinarith
  refine ((summable_nat_add_iff t0).mpr hs).tsum_le_tsum (fun t => ?_)
    ((summable_nat_add_iff t0).mpr hs')
  have hw := wage_nonneg_mono hT (hk (t + t0)) (hle (t + t0))
  exact mul_le_mul (hD _) hw.2 hw.1 (discF_pos hT hk' _).le

/-- **Uniqueness of the positive orbit**: from a given `k₀` at most one initial consumption
keeps (32)–(33) in the positive quadrant for ever. -/
theorem posOrbit_unique (hT : Technology f) {β n k0 c0 c0' : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hn : 0 < n) (hp : PosOrbit f β n k0 c0) (hp' : PosOrbit f β n k0 c0') : c0 = c0' := by
  wlog hlt : c0 < c0' generalizing c0 c0'
  · rcases lt_trichotomy c0 c0' with h | h | h
    · exact absurd h hlt
    · exact h
    · exact (this hp' hp h).symm
  exfalso
  have hcmp := orbit_compare hT hβ1 hn hp' hp le_rfl hlt.le
  obtain ⟨hs, hrep⟩ := posOrbit_representation hT hβ hβ1 hn hp
  obtain ⟨hs', hrep'⟩ := posOrbit_representation hT hβ hβ1 hn hp'
  have hle := discounted_wages_le hT (fun t => (hp' t).1) (fun t => (hp t).1)
    (fun t => (hcmp t).1) hs' hs 0
  simp only [add_zero] at hle
  have h1β : 0 < 1 - β := by linarith
  have := mul_le_mul_of_nonneg_left (add_le_add_left hle ((1 + deriv f k0) * k0)) h1β.le
  linarith

/-- Capital along the orbit from `(k₀, c)`, as a function of initial consumption `c`. -/
noncomputable def kIt (f : ℝ → ℝ) (β n k0 c : ℝ) (j : ℕ) : ℝ := (orb f β n k0 c j).1

/-- Consumption along the orbit from `(k₀, c)`. -/
noncomputable def cIt (f : ℝ → ℝ) (β n k0 c : ℝ) (j : ℕ) : ℝ := (orb f β n k0 c j).2

/-- The capital recursion (32) along the orbit. -/
theorem kIt_succ (f : ℝ → ℝ) (β n k0 c : ℝ) (j : ℕ) :
    kIt f β n k0 c (j + 1) = nextK f n (kIt f β n k0 c j) (cIt f β n k0 c j) := by
  simp only [kIt, cIt, orb_succ, wstep]

/-- The consumption recursion (33) along the orbit. -/
theorem cIt_succ (f : ℝ → ℝ) (β n k0 c : ℝ) (j : ℕ) :
    cIt f β n k0 c (j + 1) = (1 + deriv f (kIt f β n k0 c (j + 1))) *
      (β * cIt f β n k0 c j - n * (1 - β) * kIt f β n k0 c (j + 1)) := by
  rw [kIt_succ]; simp only [kIt, cIt, orb_succ, wstep, nextC]

/-- The map (32)–(33) is continuous at `(k, c)` when `k > 0` and next capital is positive. -/
theorem wstep_continuousAt (hT : Technology f) {β n : ℝ} {p : ℝ × ℝ} (h1 : 0 < p.1)
    (h2 : 0 < nextK f n p.1 p.2) : ContinuousAt (wstep f β n) p := by
  have hK : ContinuousAt (fun p : ℝ × ℝ => nextK f n p.1 p.2) p := by
    unfold nextK
    exact ((((hT.neo.diff _ h1).continuousAt.comp continuousAt_fst).add continuousAt_fst).sub
      continuousAt_snd).div_const _
  have hD : ContinuousAt (fun p : ℝ × ℝ => deriv f (nextK f n p.1 p.2)) p :=
    ContinuousAt.comp (g := deriv f) (f := fun p : ℝ × ℝ => nextK f n p.1 p.2)
      (hT.prime_cont.continuousAt (Ioi_mem_nhds h2)) hK
  refine ContinuousAt.prodMk hK ?_
  unfold nextC
  exact (continuousAt_const.add hD).mul ((continuousAt_const.mul continuousAt_snd).sub
    (continuousAt_const.mul hK))

/-- **Finite stretches of orbits depend continuously on `c₀`** while capital stays positive. -/
theorem orb_continuousAt (hT : Technology f) {β n k0 c : ℝ} {T : ℕ}
    (hpos : ∀ j ≤ T, 0 < kIt f β n k0 c j) : ContinuousAt (fun c => orb f β n k0 c T) c := by
  induction T with
  | zero => exact continuousAt_const.prodMk continuousAt_id
  | succ T ih =>
    have ih' := ih (fun j hj => hpos j (by omega))
    have h1 : 0 < (orb f β n k0 c T).1 := hpos T (by omega)
    have h2 : 0 < nextK f n (orb f β n k0 c T).1 (orb f β n k0 c T).2 := by
      have := hpos (T + 1) le_rfl; rwa [kIt_succ] at this
    have e : (fun c => orb f β n k0 c (T + 1)) = fun c => wstep f β n (orb f β n k0 c T) :=
      funext fun c => orb_succ f β n k0 c T
    rw [e]
    exact ContinuousAt.comp (g := wstep f β n) (f := fun c => orb f β n k0 c T)
      (wstep_continuousAt hT h1 h2) ih'

/-- Next-period capital is continuous in `c₀` as long as capital so far is positive. -/
theorem kIt_succ_continuousAt (hT : Technology f) {β n k0 c : ℝ} {T : ℕ}
    (hpos : ∀ j ≤ T, 0 < kIt f β n k0 c j) :
    ContinuousAt (fun c => kIt f β n k0 c (T + 1)) c := by
  have h1 : 0 < (orb f β n k0 c T).1 := hpos T le_rfl
  have hK : ContinuousAt (fun p : ℝ × ℝ => nextK f n p.1 p.2) (orb f β n k0 c T) := by
    unfold nextK
    exact ((((hT.neo.diff _ h1).continuousAt.comp continuousAt_fst).add
      continuousAt_fst).sub continuousAt_snd).div_const _
  have e : (fun c => kIt f β n k0 c (T + 1)) =
      fun c => nextK f n (orb f β n k0 c T).1 (orb f β n k0 c T).2 :=
    funext fun c => kIt_succ f β n k0 c T
  rw [e]
  exact ContinuousAt.comp (g := fun p : ℝ × ℝ => nextK f n p.1 p.2)
    (f := fun c => orb f β n k0 c T) hK (orb_continuousAt hT hpos)

/-- "Too low" initial consumption: capital stays positive up to some date at which
consumption is negative. -/
def TooLow (f : ℝ → ℝ) (β n k0 c : ℝ) : Prop :=
  0 < c ∧ ∃ T, (∀ j ≤ T, 0 < kIt f β n k0 c j) ∧ cIt f β n k0 c T < 0

/-- "Too high" initial consumption: capital turns negative. -/
def TooHigh (f : ℝ → ℝ) (β n k0 c : ℝ) : Prop :=
  ∃ T, (∀ j < T, 0 < kIt f β n k0 c j) ∧ kIt f β n k0 c T < 0

/-- Once consumption is negative with positive capital it stays negative and capital stays
positive: "too low" orbits never have negative capital. -/
theorem tooLow_capital_pos (hT : Technology f) {β n k0 c : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hn : 0 < n) (h : TooLow f β n k0 c) (t : ℕ) : 0 < kIt f β n k0 c t := by
  obtain ⟨-, T, hk, hc⟩ := h
  have hafter : ∀ s, 0 < kIt f β n k0 c (T + s) ∧ cIt f β n k0 c (T + s) < 0 := by
    intro s
    induction s with
    | zero => exact ⟨hk T le_rfl, hc⟩
    | succ s ih =>
      obtain ⟨h1, h2⟩ := ih
      have hk1 : 0 < kIt f β n k0 c (T + s + 1) := by
        rw [kIt_succ]; unfold nextK
        have := f_nonneg hT h1.le
        apply div_pos _ (by linarith); linarith
      refine ⟨hk1, ?_⟩
      rw [show T + (s + 1) = T + s + 1 by ring, cIt_succ]
      apply mul_neg_of_pos_of_neg (by linarith [hT.neo.deriv_pos hk1])
      have := mul_pos (mul_pos hn (by linarith : (0 : ℝ) < 1 - β)) hk1
      nlinarith
  rcases le_or_gt t T with h | h
  · exact hk t h
  · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h.le
    exact (hafter s).1

/-- Small initial consumption is too low. -/
theorem tooLow_small (hT : Technology f) {β n k0 : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hn : 0 < n)
    (hk0 : 0 < k0) : ∃ c, TooLow f β n k0 c := by
  set c := min (k0 / 2) (n * (1 - β) * k0 / (4 * β * (1 + n)))
  have h1β : 0 < 1 - β := by linarith
  have hc : 0 < c := lt_min (by linarith) (by positivity)
  refine ⟨c, hc, 1, fun j hj => ?_, ?_⟩
  · have hk1 : 0 < kIt f β n k0 c 1 := by
      rw [kIt_succ]; unfold nextK
      have := f_nonneg hT hk0.le
      have : c ≤ k0 / 2 := min_le_left _ _
      simp only [kIt, cIt, orb_zero]
      apply div_pos _ (by linarith); linarith
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · exact hk0
    · exact hk1
  · rw [cIt_succ]
    have hk1 : k0 / (2 * (1 + n)) ≤ kIt f β n k0 c 1 := by
      rw [kIt_succ]; unfold nextK
      have := f_nonneg hT hk0.le
      have : c ≤ k0 / 2 := min_le_left _ _
      simp only [kIt, cIt, orb_zero]
      rw [div_le_div_iff₀ (by positivity) (by linarith)]; nlinarith
    have hk1p : 0 < kIt f β n k0 c 1 := lt_of_lt_of_le (by positivity) hk1
    apply mul_neg_of_pos_of_neg (by linarith [hT.neo.deriv_pos hk1p])
    simp only [cIt, orb_zero]
    have hc2 : c ≤ n * (1 - β) * k0 / (4 * β * (1 + n)) := min_le_right _ _
    have h1 : β * c ≤ n * (1 - β) * k0 / (4 * (1 + n)) := by
      rw [le_div_iff₀ (by positivity)] at hc2
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have h2 : n * (1 - β) * (k0 / (2 * (1 + n))) ≤ n * (1 - β) * kIt f β n k0 c 1 :=
      mul_le_mul_of_nonneg_left hk1 (mul_pos hn (by linarith)).le
    have h3 : n * (1 - β) * k0 / (4 * (1 + n)) < n * (1 - β) * (k0 / (2 * (1 + n))) := by
      have : 0 < n * (1 - β) * k0 := by positivity
      rw [div_lt_iff₀ (by positivity)]
      field_simp
      nlinarith
    linarith

/-- Too-low initial consumption is below `f(k₀) + k₀`. -/
theorem tooLow_lt {β n k0 c : ℝ} (hn : 0 < n) (h : TooLow f β n k0 c) : c < f k0 + k0 := by
  obtain ⟨hc, T, hk, hcT⟩ := h
  have hT0 : T ≠ 0 := by rintro rfl; simp [cIt, orb_zero] at hcT; linarith
  have h1 := hk 1 (by omega)
  rw [kIt_succ] at h1
  simp only [nextK, kIt, cIt, orb_zero] at h1
  rw [div_pos_iff_of_pos_right (by linarith)] at h1
  linarith

/-- **"Too low" is closed downwards** (orbits are ordered in `c₀`). -/
theorem tooLow_down (hT : Technology f) {β n k0 c c' : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hn : 0 < n) (h : TooLow f β n k0 c) (hc' : 0 < c') (hlt : c' < c) : TooLow f β n k0 c' := by
  classical
  obtain ⟨hc, T, hk, hcT⟩ := h
  have hex : ∃ j, cIt f β n k0 c j < 0 := ⟨T, hcT⟩
  set T1 := Nat.find hex
  have hT1 : cIt f β n k0 c T1 < 0 := Nat.find_spec hex
  have hT1T : T1 ≤ T := Nat.find_min' hex hcT
  have hmin : ∀ j < T1, 0 ≤ cIt f β n k0 c j := fun j hj => not_lt.mp (Nat.find_min hex hj)
  have hT10 : T1 ≠ 0 := by
    intro h0; rw [h0] at hT1; simp [cIt, orb_zero] at hT1; linarith
  have h1β : 0 < n * (1 - β) := mul_pos hn (by linarith)
  -- comparison up to `T1 - 1`
  have hcmp : ∀ j, j < T1 → kIt f β n k0 c j ≤ kIt f β n k0 c' j ∧
      cIt f β n k0 c' j ≤ cIt f β n k0 c j := by
    intro j
    induction j with
    | zero => intro _; simp only [kIt, cIt, orb_zero]; exact ⟨le_rfl, hlt.le⟩
    | succ j ih =>
      intro hj
      obtain ⟨hk', hc''⟩ := ih (by omega)
      have hkj : 0 < kIt f β n k0 c j := hk j (by omega)
      have hk1 : 0 < kIt f β n k0 c (j + 1) := hk (j + 1) (by omega)
      have hK : kIt f β n k0 c (j + 1) ≤ kIt f β n k0 c' (j + 1) := by
        rw [kIt_succ, kIt_succ]; unfold nextK
        apply div_le_div_of_nonneg_right _ (by linarith)
        have := f_mono hT hkj.le hk'; linarith
      refine ⟨hK, ?_⟩
      rw [cIt_succ, cIt_succ]
      have hR : deriv f (kIt f β n k0 c' (j + 1)) ≤ deriv f (kIt f β n k0 c (j + 1)) :=
        hT.neo.deriv_strictAnti.antitoneOn hk1 (hk1.trans_le hK) hK
      have hR'pos : 0 < 1 + deriv f (kIt f β n k0 c' (j + 1)) := by
        linarith [hT.neo.deriv_pos (hk1.trans_le hK)]
      have hc1 := hmin (j + 1) hj
      rw [cIt_succ] at hc1
      have hA : 0 ≤ β * cIt f β n k0 c j - n * (1 - β) * kIt f β n k0 c (j + 1) := by
        by_contra hneg; push Not at hneg
        have := mul_neg_of_pos_of_neg (by linarith [hT.neo.deriv_pos hk1] :
          0 < 1 + deriv f (kIt f β n k0 c (j + 1))) hneg
        linarith
      have hA' : β * cIt f β n k0 c' j - n * (1 - β) * kIt f β n k0 c' (j + 1) ≤
          β * cIt f β n k0 c j - n * (1 - β) * kIt f β n k0 c (j + 1) := by
        have := mul_le_mul_of_nonneg_left hc'' hβ.le
        have := mul_le_mul_of_nonneg_left hK h1β.le
        linarith
      calc _ ≤ (1 + deriv f (kIt f β n k0 c' (j + 1))) *
            (β * cIt f β n k0 c j - n * (1 - β) * kIt f β n k0 c (j + 1)) :=
            mul_le_mul_of_nonneg_left hA' hR'pos.le
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hA
  refine ⟨hc', T1, fun j hj => ?_, ?_⟩
  · rcases hj.lt_or_eq with hj | hj
    · exact (hk j (by omega)).trans_le (hcmp j hj).1
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hT10
      rw [hj, hm, kIt_succ]
      have hkm := hk m (by omega)
      obtain ⟨h1, h2⟩ := hcmp m (by omega)
      have := hk (m + 1) (by omega)
      rw [kIt_succ] at this
      unfold nextK at this ⊢
      apply lt_of_lt_of_le this (div_le_div_of_nonneg_right _ (by linarith))
      have := f_mono hT hkm.le h1; linarith
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hT10
    rw [hm] at hT1 ⊢
    obtain ⟨h1, h2⟩ := hcmp m (by omega)
    have hkm := hk m (by omega)
    have hk1 : 0 < kIt f β n k0 c (m + 1) := hk (m + 1) (by omega)
    have hK : kIt f β n k0 c (m + 1) ≤ kIt f β n k0 c' (m + 1) := by
      rw [kIt_succ, kIt_succ]; unfold nextK
      apply div_le_div_of_nonneg_right _ (by linarith)
      have := f_mono hT hkm.le h1; linarith
    rw [cIt_succ] at hT1 ⊢
    have hA : β * cIt f β n k0 c m - n * (1 - β) * kIt f β n k0 c (m + 1) < 0 := by
      by_contra hnn; push Not at hnn
      have := mul_nonneg (by linarith [hT.neo.deriv_pos hk1] :
        0 ≤ 1 + deriv f (kIt f β n k0 c (m + 1))) hnn
      linarith
    have hA' : β * cIt f β n k0 c' m - n * (1 - β) * kIt f β n k0 c' (m + 1) < 0 := by
      have := mul_le_mul_of_nonneg_left h2 hβ.le
      have := mul_le_mul_of_nonneg_left hK h1β.le
      linarith
    exact mul_neg_of_pos_of_neg (by linarith [hT.neo.deriv_pos (hk1.trans_le hK)]) hA'

/-- "Too low" is an open condition. -/
theorem tooLow_open (hT : Technology f) {β n k0 c : ℝ} (h : TooLow f β n k0 c) :
    ∀ᶠ c' in 𝓝 c, TooLow f β n k0 c' := by
  obtain ⟨hc, T, hk, hcT⟩ := h
  have hcont := orb_continuousAt hT hk
  have hev1 : ∀ᶠ c' in 𝓝 c, 0 < c' := lt_mem_nhds hc
  have hev2 : ∀ᶠ c' in 𝓝 c, cIt f β n k0 c' T < 0 :=
    (continuous_snd.continuousAt.comp hcont).eventually (gt_mem_nhds hcT)
  have hev3 : ∀ j ≤ T, ∀ᶠ c' in 𝓝 c, 0 < kIt f β n k0 c' j := by
    intro j hj
    have := orb_continuousAt hT (T := j) (fun i hi => hk i (by omega))
    exact (continuous_fst.continuousAt.comp this).eventually (lt_mem_nhds (hk j hj))
  have hev4 : ∀ᶠ c' in 𝓝 c, ∀ j ∈ Finset.range (T + 1), 0 < kIt f β n k0 c' j :=
    (Finset.eventually_all _).mpr (fun j hj => hev3 j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  filter_upwards [hev1, hev2, hev4] with c' h1 h2 h4
  exact ⟨h1, T, fun j hj => h4 j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)), h2⟩

/-- "Too high" is an open condition. -/
theorem tooHigh_open (hT : Technology f) {β n k0 c : ℝ} (h : TooHigh f β n k0 c) :
    ∀ᶠ c' in 𝓝 c, TooHigh f β n k0 c' := by
  obtain ⟨T, hk, hkT⟩ := h
  rcases Nat.eq_zero_or_pos T with h0 | hpos
  · subst h0
    exact Eventually.of_forall (fun c' => ⟨0, fun j hj => absurd hj (Nat.not_lt_zero _),
      by simpa [kIt, orb_zero] using hkT⟩)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  have hkm : ∀ j ≤ m, 0 < kIt f β n k0 c j := fun j hj => hk j (by omega)
  have hcont := kIt_succ_continuousAt hT hkm
  have hev2 : ∀ᶠ c' in 𝓝 c, kIt f β n k0 c' (m + 1) < 0 := hcont.eventually (gt_mem_nhds hkT)
  have hev3 : ∀ j ≤ m, ∀ᶠ c' in 𝓝 c, 0 < kIt f β n k0 c' j := by
    intro j hj
    have := orb_continuousAt hT (T := j) (fun i hi => hkm i (by omega))
    exact (continuous_fst.continuousAt.comp this).eventually (lt_mem_nhds (hkm j hj))
  have hev4 : ∀ᶠ c' in 𝓝 c, ∀ j ∈ Finset.range (m + 1), 0 < kIt f β n k0 c' j :=
    (Finset.eventually_all _).mpr (fun j hj => hev3 j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  filter_upwards [hev2, hev4] with c' h2 h4
  exact ⟨m + 1, fun j hj => h4 j (Finset.mem_range.mpr hj), h2⟩

/-- **Existence of the saddle path** (O&R Fig. 7.7, by shooting): from every `k₀ > 0` some
initial consumption keeps (32)–(33) in the positive quadrant for ever, namely the supremum of
the "too low" initial consumptions. -/
theorem posOrbit_exists (hT : Technology f) {β n k0 : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hn : 0 < n) (hk0 : 0 < k0) : ∃ c0, PosOrbit f β n k0 c0 := by
  classical
  set Lo := {c | TooLow f β n k0 c}
  have hne : Lo.Nonempty := tooLow_small hT hβ hβ1 hn hk0
  have hbdd : BddAbove Lo := ⟨f k0 + k0, fun c hc => (tooLow_lt hn hc).le⟩
  set cs := sSup Lo
  obtain ⟨c1, hc1⟩ := hne
  have hcs : 0 < cs := lt_of_lt_of_le hc1.1 (le_csSup hbdd hc1)
  have happrox : ∀ ε > 0, ∃ c, TooLow f β n k0 c ∧ cs - ε < c ∧ c ≤ cs := by
    intro ε hε
    obtain ⟨c, hc, hlt⟩ := exists_lt_of_lt_csSup ⟨c1, hc1⟩ (by linarith : cs - ε < cs)
    exact ⟨c, hc, hlt, le_csSup hbdd hc⟩
  have hnotLo : ¬ TooLow f β n k0 cs := by
    intro h
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (tooLow_open hT h)
    have := hball (show dist (cs + ε / 2) cs < ε by
      rw [Real.dist_eq, show cs + ε / 2 - cs = ε / 2 by ring, abs_of_pos (half_pos hε)]
      exact half_lt_self hε)
    have := le_csSup hbdd this
    linarith
  have hdisj : ∀ c, TooLow f β n k0 c → ¬ TooHigh f β n k0 c := by
    rintro c hl ⟨T, -, hT'⟩
    linarith [tooLow_capital_pos hT hβ hβ1 hn hl T]
  have hnotHi : ¬ TooHigh f β n k0 cs := by
    intro h
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (tooHigh_open hT h)
    obtain ⟨c, hc, hlt, hle⟩ := happrox ε hε
    have := hball (show dist c cs < ε by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    exact hdisj c hc this
  refine ⟨cs, ?_⟩
  by_contra hbad
  simp only [PosOrbit, not_forall] at hbad
  have hex : ∃ t, ¬ (0 < kIt f β n k0 cs t ∧ 0 < cIt f β n k0 cs t) := hbad
  set t := Nat.find hex
  have ht : ¬ (0 < kIt f β n k0 cs t ∧ 0 < cIt f β n k0 cs t) := Nat.find_spec hex
  have hbefore : ∀ j < t, 0 < kIt f β n k0 cs j ∧ 0 < cIt f β n k0 cs j := fun j hj => by
    have := Nat.find_min hex hj; push Not at this; exact this
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0] at ht
    exact ht ⟨by simpa [kIt, orb_zero] using hk0, by simpa [cIt, orb_zero] using hcs⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero ht0
  have hbm : ∀ j ≤ m, 0 < kIt f β n k0 cs j ∧ 0 < cIt f β n k0 cs j :=
    fun j hj => hbefore j (by omega)
  rcases lt_trichotomy (kIt f β n k0 cs t) 0 with hneg | hzero | hkpos
  · exact hnotHi ⟨t, fun j hj => (hbefore j hj).1, hneg⟩
  · -- capital hits zero exactly: nearby too-low orbits would have to jump over it
    rw [hm] at hzero
    have hcm := (hbm m le_rfl).2
    set a0 := β * cIt f β n k0 cs m
    have ha0 : 0 < a0 := mul_pos hβ hcm
    set M := 2 * (f 1 + 1) / a0
    obtain ⟨η, hη, hηM⟩ : ∃ η, 0 < η ∧ η ≤ 1 ∧ ∀ k, 0 < k → k < η → M < deriv f k := by
      have := (hT.inada0.eventually (eventually_gt_atTop M))
      obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp this
      exact ⟨min u 1, lt_min hu one_pos, min_le_right _ _, fun k hk hku =>
        hsub ⟨hk, lt_of_lt_of_le hku (min_le_left _ _)⟩⟩
    have hηM' := hηM.2
    -- continuity at `cs`
    have hposm : ∀ j ≤ m, 0 < kIt f β n k0 cs j := fun j hj => (hbm j hj).1
    have hcontK := kIt_succ_continuousAt hT hposm
    have hcontC : ContinuousAt (fun c => cIt f β n k0 c m) cs :=
      continuous_snd.continuousAt.comp (orb_continuousAt hT hposm)
    have hevA : ∀ᶠ c in 𝓝 cs, a0 / 2 < β * cIt f β n k0 c m - n * (1 - β) *
        kIt f β n k0 c (m + 1) := by
      have hA : ContinuousAt (fun c => β * cIt f β n k0 c m - n * (1 - β) *
          kIt f β n k0 c (m + 1)) cs :=
        (continuousAt_const.mul hcontC).sub (continuousAt_const.mul hcontK)
      have hval : β * cIt f β n k0 cs m - n * (1 - β) * kIt f β n k0 cs (m + 1) = a0 := by
        rw [hzero]; ring
      exact hA.eventually (lt_mem_nhds (by simp only; rw [hval]; exact half_lt_self ha0))
    have hevK : ∀ᶠ c in 𝓝 cs, kIt f β n k0 c (m + 1) < η :=
      hcontK.eventually (gt_mem_nhds (by simp only; rw [hzero]; exact hη))
    have hevP : ∀ᶠ c in 𝓝 cs, ∀ j ∈ Finset.range (m + 1), 0 < cIt f β n k0 c j := by
      refine (Finset.eventually_all _).mpr (fun j hj => ?_)
      have hj' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have := orb_continuousAt hT (T := j) (fun i hi => hposm i (by omega))
      exact (continuous_snd.continuousAt.comp this).eventually (lt_mem_nhds (hbm j hj').2)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp ((hevA.and hevK).and hevP)
    obtain ⟨c, hc, hlt, hle⟩ := happrox ε hε
    obtain ⟨⟨hA, hK⟩, hP⟩ := hball (show dist c cs < ε by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    obtain ⟨-, T, hkT, hcT⟩ := hc
    rcases le_or_gt T m with hTm | hTm
    · linarith [hP T (Finset.mem_range.mpr (by omega))]
    · have hk1 : 0 < kIt f β n k0 c (m + 1) := hkT (m + 1) (by omega)
      have hR : M < deriv f (kIt f β n k0 c (m + 1)) := hηM' _ hk1 hK
      have hc1 : 2 * (f 1 + 1) / a0 * (a0 / 2) < cIt f β n k0 c (m + 1) := by
        rw [cIt_succ]
        have hM0 : 0 ≤ M := by
          have := f_nonneg hT zero_le_one; positivity
        calc 2 * (f 1 + 1) / a0 * (a0 / 2) ≤ (1 + deriv f (kIt f β n k0 c (m + 1))) * (a0 / 2) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
          _ < _ := mul_lt_mul_of_pos_left hA (by linarith)
      have hval : 2 * (f 1 + 1) / a0 * (a0 / 2) = f 1 + 1 := by field_simp
      rw [hval] at hc1
      rcases (Nat.lt_iff_add_one_le.mp hTm).lt_or_eq with hT2 | hT1
      · have hk2 := hkT (m + 2) (by omega)
        rw [show m + 2 = m + 1 + 1 by ring, kIt_succ] at hk2
        unfold nextK at hk2
        rw [div_pos_iff_of_pos_right (by linarith)] at hk2
        have := f_mono hT hk1.le (show kIt f β n k0 c (m + 1) ≤ 1 by linarith)
        linarith
      · rw [← hT1] at hcT
        have := f_nonneg hT zero_le_one
        linarith
  · -- capital positive, consumption nonpositive
    have hct : cIt f β n k0 cs t ≤ 0 := by
      by_contra h; push Not at h; exact ht ⟨hkpos, h⟩
    have hkall : ∀ j ≤ t, 0 < kIt f β n k0 cs j := fun j hj => by
      rcases hj.lt_or_eq with h | h
      · exact (hbefore j h).1
      · rw [h]; exact hkpos
    rcases hct.lt_or_eq with hneg | hz
    · exact hnotLo ⟨hcs, t, hkall, hneg⟩
    · have hk1 : 0 < kIt f β n k0 cs (t + 1) := by
        rw [kIt_succ]; unfold nextK
        have := f_nonneg hT hkpos.le
        apply div_pos _ (by linarith); linarith
      refine hnotLo ⟨hcs, t + 1, fun j hj => ?_, ?_⟩
      · rcases hj.lt_or_eq with h | h
        · exact hkall j (by omega)
        · rw [h]; exact hk1
      · rw [cIt_succ, hz]
        apply mul_neg_of_pos_of_neg (by linarith [hT.neo.deriv_pos hk1])
        have := mul_pos (mul_pos hn (by linarith : (0 : ℝ) < 1 - β)) hk1
        linarith

/-- Shifting an orbit: the orbit from `(k₀, c₀)` after `s + t` steps is the orbit from its
date-`s` state after `t` steps. -/
theorem orb_shift (f : ℝ → ℝ) (β n k0 c0 : ℝ) (s t : ℕ) :
    orb f β n k0 c0 (t + s) = orb f β n (orb f β n k0 c0 s).1 (orb f β n k0 c0 s).2 t := by
  simp only [orb, Prod.mk.eta, Function.iterate_add_apply]

/-- Tails of positive orbits are positive orbits. -/
theorem posOrbit_tail {β n k0 c0 : ℝ} (hp : PosOrbit f β n k0 c0) (s : ℕ) :
    PosOrbit f β n (orb f β n k0 c0 s).1 (orb f β n k0 c0 s).2 := fun t => by
  rw [← orb_shift]; exact hp (t + s)

/-- The value of the initial consumption on a positive orbit, split as
`c₀ = (1-β)[k₀ + f(k₀) + ∑_{t ≥ 1} D_t w_t]`. -/
theorem posOrbit_representation' (hT : Technology f) {β n k0 c0 : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hn : 0 < n) (hp : PosOrbit f β n k0 c0) :
    Summable (fun t => discF f (fun t => (orb f β n k0 c0 t).1) t *
        wageF f (fun t => (orb f β n k0 c0 t).1) t) ∧
      c0 = (1 - β) * (k0 + f k0 + ∑' t, discF f (fun t => (orb f β n k0 c0 t).1) (t + 1) *
        wageF f (fun t => (orb f β n k0 c0 t).1) (t + 1)) := by
  obtain ⟨hs, hrep⟩ := posOrbit_representation hT hβ hβ1 hn hp
  refine ⟨hs, ?_⟩
  have h0 : discF f (fun t => (orb f β n k0 c0 t).1) 0 *
      wageF f (fun t => (orb f β n k0 c0 t).1) 0 = f k0 - k0 * deriv f k0 := by
    simp [discF, wageF, orb_zero]
  set S1 := ∑' t, discF f (fun t => (orb f β n k0 c0 t).1) (t + 1) *
    wageF f (fun t => (orb f β n k0 c0 t).1) (t + 1) with hS1
  have hsplit : ∑' t, discF f (fun t => (orb f β n k0 c0 t).1) t *
      wageF f (fun t => (orb f β n k0 c0 t).1) t = f k0 - k0 * deriv f k0 + S1 := by
    rw [hs.tsum_eq_zero_add, h0]
  rw [hrep, hsplit]
  ring

/-- **The saddle-path consumption is strictly increasing in capital** (O&R Fig. 7.7: `SS`
slopes upward). -/
theorem saddle_c_strictMono (hT : Technology f) {β n k0 k0' c0 c0' : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hn : 0 < n) (hp : PosOrbit f β n k0 c0) (hp' : PosOrbit f β n k0' c0')
    (hlt : k0 < k0') : c0 < c0' := by
  by_contra hle
  push Not at hle
  have hcmp := orbit_compare hT hβ1 hn hp hp' hlt.le hle
  obtain ⟨hs, hrep⟩ := posOrbit_representation' hT hβ hβ1 hn hp
  obtain ⟨hs', hrep'⟩ := posOrbit_representation' hT hβ hβ1 hn hp'
  have hS := discounted_wages_le hT (fun t => (hp t).1) (fun t => (hp' t).1)
    (fun t => (hcmp t).1) hs hs' 1
  have hf := hT.neo.strictMono (mem_Ici.mpr (hp 0).1.le) (mem_Ici.mpr (hp' 0).1.le) hlt
  simp only [orb_zero] at hf
  have h1β : 0 < 1 - β := by linarith
  have : (1 - β) * (k0 + f k0 + ∑' t, discF f (fun t => (orb f β n k0 c0 t).1) (t + 1) *
      wageF f (fun t => (orb f β n k0 c0 t).1) (t + 1)) <
      (1 - β) * (k0' + f k0' + ∑' t, discF f (fun t => (orb f β n k0' c0' t).1) (t + 1) *
      wageF f (fun t => (orb f β n k0' c0' t).1) (t + 1)) :=
    mul_lt_mul_of_pos_left (by linarith) h1β
  linarith

/-- The saddle-path consumption is weakly increasing in capital (uniqueness at equality). -/
theorem saddle_c_mono (hT : Technology f) {β n k0 k0' c0 c0' : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hn : 0 < n) (hp : PosOrbit f β n k0 c0) (hp' : PosOrbit f β n k0' c0') (hle : k0 ≤ k0') :
    c0 ≤ c0' := by
  rcases hle.lt_or_eq with h | h
  · exact (saddle_c_strictMono hT hβ hβ1 hn hp hp' h).le
  · subst h; exact (posOrbit_unique hT hβ hβ1 hn hp hp').le

/-- **The saddle-path capital map `k ↦ k'` is increasing** (via (33) and the monotone
consumption policy). -/
theorem saddle_k_mono (hT : Technology f) {β n k0 k0' c0 c0' : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hn : 0 < n) (hp : PosOrbit f β n k0 c0) (hp' : PosOrbit f β n k0' c0') (hle : k0 ≤ k0') :
    (orb f β n k0 c0 1).1 ≤ (orb f β n k0' c0' 1).1 := by
  rcases hle.lt_or_eq with hlt | heq
  swap
  · subst heq; rw [posOrbit_unique hT hβ hβ1 hn hp hp']
  by_contra hgt
  push Not at hgt
  have hc0 := saddle_c_strictMono hT hβ hβ1 hn hp hp' hlt
  have hc1 := saddle_c_mono hT hβ hβ1 hn (posOrbit_tail hp' 1) (posOrbit_tail hp 1) hgt.le
  have e1 := cIt_succ f β n k0 c0 0
  have e2 := cIt_succ f β n k0' c0' 0
  simp only [kIt, cIt, zero_add, orb_zero] at e1 e2
  have hk1 := (hp 1).1
  have hk1' := (hp' 1).1
  have hc1p := (hp 1).2
  have hR : deriv f (orb f β n k0 c0 1).1 ≤ deriv f (orb f β n k0' c0' 1).1 :=
    hT.neo.deriv_strictAnti.antitoneOn hk1' hk1 hgt.le
  have hA : 0 < β * c0 - n * (1 - β) * (orb f β n k0 c0 1).1 := by
    by_contra h; push Not at h
    have := mul_nonpos_of_nonneg_of_nonpos (by linarith [hT.neo.deriv_pos hk1] :
      0 ≤ 1 + deriv f (orb f β n k0 c0 1).1) h
    linarith
  have hA' : β * c0 - n * (1 - β) * (orb f β n k0 c0 1).1 <
      β * c0' - n * (1 - β) * (orb f β n k0' c0' 1).1 := by
    have := mul_lt_mul_of_pos_left hc0 hβ
    have := mul_le_mul_of_nonneg_left hgt.le (mul_pos hn (by linarith : (0 : ℝ) < 1 - β)).le
    linarith
  have hlt' : (orb f β n k0 c0 1).2 < (orb f β n k0' c0' 1).2 := by
    rw [e1, e2]
    calc (1 + deriv f (orb f β n k0 c0 1).1) * (β * c0 - n * (1 - β) * (orb f β n k0 c0 1).1)
        < (1 + deriv f (orb f β n k0 c0 1).1) *
          (β * c0' - n * (1 - β) * (orb f β n k0' c0' 1).1) :=
          mul_lt_mul_of_pos_left hA' (by linarith [hT.neo.deriv_pos hk1])
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  linarith

/-- **Saddle paths are monotone**: capital and consumption move in the same direction for
ever. -/
theorem saddle_monotone (hT : Technology f) {β n k0 c0 : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hn : 0 < n) (hp : PosOrbit f β n k0 c0) :
    ((orb f β n k0 c0 0).1 ≤ (orb f β n k0 c0 1).1 →
      Monotone (fun t => (orb f β n k0 c0 t).1) ∧ Monotone (fun t => (orb f β n k0 c0 t).2)) ∧
    ((orb f β n k0 c0 1).1 ≤ (orb f β n k0 c0 0).1 →
      Antitone (fun t => (orb f β n k0 c0 t).1) ∧ Antitone (fun t => (orb f β n k0 c0 t).2)) := by
  have hstep : ∀ t, (orb f β n k0 c0 (t + 1)).1 =
      (orb f β n (orb f β n k0 c0 t).1 (orb f β n k0 c0 t).2 1).1 := fun t => by
    rw [← orb_shift, add_comm]
  have hk : ∀ s t, (orb f β n k0 c0 s).1 ≤ (orb f β n k0 c0 t).1 →
      (orb f β n k0 c0 (s + 1)).1 ≤ (orb f β n k0 c0 (t + 1)).1 := by
    intro s t h
    rw [hstep s, hstep t]
    exact saddle_k_mono hT hβ hβ1 hn (posOrbit_tail hp s) (posOrbit_tail hp t) h
  have hc : ∀ s t, (orb f β n k0 c0 s).1 ≤ (orb f β n k0 c0 t).1 →
      (orb f β n k0 c0 s).2 ≤ (orb f β n k0 c0 t).2 := by
    intro s t h
    have := saddle_c_mono hT hβ hβ1 hn (posOrbit_tail hp s) (posOrbit_tail hp t) h
    simpa [orb_zero] using this
  constructor
  · intro h01
    have hmk : Monotone (fun t => (orb f β n k0 c0 t).1) := by
      refine monotone_nat_of_le_succ (fun t => ?_)
      induction t with
      | zero => exact h01
      | succ t ih => exact hk t (t + 1) ih
    exact ⟨hmk, fun a b hab => hc a b (hmk hab)⟩
  · intro h10
    have hak : Antitone (fun t => (orb f β n k0 c0 t).1) := by
      refine antitone_nat_of_succ_le (fun t => ?_)
      induction t with
      | zero => exact h10
      | succ t ih => exact hk (t + 1) t ih
    exact ⟨hak, fun a b hab => hc b a (hak hab)⟩

/-- **The saddle path converges to the steady state** (O&R Fig. 7.7): along the positive orbit
from any `k₀ > 0`, capital converges to the unique steady state `k̄` and consumption to
`c̄ = f(k̄) - n k̄`. Capital cannot run down to zero: near zero the Inada condition makes
consumption along a falling path force capital back up. -/
theorem saddle_tendsto (hT : Technology f) {β n k0 c0 kbar : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hn : 0 < n) (hp : PosOrbit f β n k0 c0) (hkb : 0 < kbar)
    (hdom : 1 < β * (1 + deriv f kbar)) (hres : residual f β n kbar = 0) :
    Tendsto (fun t => (orb f β n k0 c0 t).1) atTop (𝓝 kbar) ∧
      Tendsto (fun t => (orb f β n k0 c0 t).2) atTop (𝓝 (f kbar - n * kbar)) := by
  set k : ℕ → ℝ := fun t => (orb f β n k0 c0 t).1
  set c : ℕ → ℝ := fun t => (orb f β n k0 c0 t).2
  have hk : ∀ t, 0 < k t := fun t => (hp t).1
  have hc : ∀ t, 0 < c t := fun t => (hp t).2
  have hkrec : ∀ t, k (t + 1) = (f (k t) + k t - c t) / (1 + n) := fun t => kIt_succ f β n k0 c0 t
  have hcrec : ∀ t, c (t + 1) = (1 + deriv f (k (t + 1))) * (β * c t - n * (1 - β) * k (t + 1)) :=
    fun t => cIt_succ f β n k0 c0 t
  obtain ⟨K, hK0, hK⟩ := posOrbit_bounded hT hn hp
  have hcb : ∀ t, c t ≤ f K + K := by
    intro t
    have h1 := hk (t + 1)
    rw [hkrec, div_pos_iff_of_pos_right (by linarith)] at h1
    have := f_mono hT (hk t).le (hK t)
    have := hK t
    linarith
  obtain ⟨hmon, hant⟩ := saddle_monotone hT hβ hβ1 hn hp
  -- limits with positive values
  obtain ⟨L, M, hL, hM, hLpos, hMpos⟩ : ∃ L M, Tendsto k atTop (𝓝 L) ∧
      Tendsto c atTop (𝓝 M) ∧ 0 < L ∧ 0 < M := by
    rcases le_total (k 0) (k 1) with h01 | h10
    · obtain ⟨hmk, hmc⟩ := hmon h01
      have hbk : BddAbove (Set.range k) := ⟨K, by rintro _ ⟨t, rfl⟩; exact hK t⟩
      have hbc : BddAbove (Set.range c) := ⟨f K + K, by rintro _ ⟨t, rfl⟩; exact hcb t⟩
      exact ⟨_, _, tendsto_atTop_ciSup hmk hbk, tendsto_atTop_ciSup hmc hbc,
        lt_of_lt_of_le (hk 0) (le_ciSup hbk 0), lt_of_lt_of_le (hc 0) (le_ciSup hbc 0)⟩
    · obtain ⟨hak, hac⟩ := hant h10
      have hbk : BddBelow (Set.range k) := ⟨0, by rintro _ ⟨t, rfl⟩; exact (hk t).le⟩
      have hbc : BddBelow (Set.range c) := ⟨0, by rintro _ ⟨t, rfl⟩; exact (hc t).le⟩
      have hL := tendsto_atTop_ciInf hak hbk
      have hM := tendsto_atTop_ciInf hac hbc
      set L := ⨅ t, k t
      have hL0 : 0 ≤ L := le_ciInf fun t => (hk t).le
      have hLpos : 0 < L := by
        rcases hL0.lt_or_eq with h | h
        · exact h
        exfalso
        have hk0 : Tendsto k atTop (𝓝[>] 0) :=
          tendsto_nhdsWithin_iff.mpr ⟨h ▸ hL, Eventually.of_forall hk⟩
        have hk1 : Tendsto (fun t => k (t + 1)) atTop (𝓝[>] 0) :=
          hk0.comp (tendsto_add_atTop_nat 1)
        have hev1 := (hT.inada0.comp hk1).eventually (eventually_ge_atTop (2 / β))
        have hev2 := ((hT.neo.avg_tendsto_atTop hT.inada0).comp hk0).eventually
          (eventually_gt_atTop (n + 2 * n * (1 - β) / β))
        obtain ⟨t, ht1, ht2⟩ := (hev1.and hev2).exists
        simp only [Function.comp_apply] at ht1 ht2
        have hR : 2 / β ≤ 1 + deriv f (k (t + 1)) := by
          linarith [hT.neo.deriv_pos (hk (t + 1))]
        have hRpos : 0 < 1 + deriv f (k (t + 1)) := by linarith [hT.neo.deriv_pos (hk (t + 1))]
        have hcdec : c (t + 1) ≤ c t := hac (Nat.le_succ t)
        have hkdec : k (t + 1) ≤ k t := hak (Nat.le_succ t)
        have h1β : 0 < n * (1 - β) := mul_pos hn (by linarith)
        -- `n(1-β) k_{t+1} ≥ (β/2) c_t`
        have hA : β / 2 * c t ≤ n * (1 - β) * k (t + 1) := by
          by_cases hA0 : β * c t - n * (1 - β) * k (t + 1) ≤ 0
          · nlinarith [hc t]
          · push Not at hA0
            rw [hcrec] at hcdec
            have h2 : (2 / β) * (β * c t - n * (1 - β) * k (t + 1)) ≤ c t :=
              le_trans (mul_le_mul_of_nonneg_right hR hA0.le) hcdec
            have : 2 / β * β = 2 := by field_simp
            nlinarith
        have hcge : f (k t) - n * k t ≤ c t := by
          rw [hkrec, div_le_iff₀ (by linarith)] at hkdec; linarith
        have hfk : (n + 2 * n * (1 - β) / β) * k t < f (k t) := by
          rw [lt_div_iff₀ (hk t)] at ht2; linarith
        have : n * (1 - β) * k t < n * (1 - β) * k (t + 1) := by
          have e : β / 2 * ((n + 2 * n * (1 - β) / β) * k t - n * k t) = n * (1 - β) * k t := by
            field_simp; ring
          nlinarith
        have := lt_of_mul_lt_mul_left this h1β.le
        linarith
      -- consumption stays above the saddle consumption at `L`
      obtain ⟨cL, hpL⟩ := posOrbit_exists hT hβ hβ1 hn hLpos
      have hcL : ∀ t, cL ≤ c t := fun t => by
        have := saddle_c_mono hT hβ hβ1 hn hpL (posOrbit_tail hp t)
          (ciInf_le hbk t)
        simpa [orb_zero] using this
      exact ⟨L, _, hL, hM, hLpos, lt_of_lt_of_le (hpL 0).2 (le_ciInf hcL)⟩
  -- the limit is a steady state
  have hfc : ContinuousAt f L := (hT.neo.diff L hLpos).continuousAt
  have hdc : ContinuousAt (deriv f) L := hT.prime_cont.continuousAt (Ioi_mem_nhds hLpos)
  have hL1 : Tendsto (fun t => k (t + 1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)
  have hM1 : Tendsto (fun t => c (t + 1)) atTop (𝓝 M) := hM.comp (tendsto_add_atTop_nat 1)
  have eK : L = (f L + L - M) / (1 + n) := by
    refine tendsto_nhds_unique hL1 ?_
    have := (((hfc.tendsto.comp hL).add hL).sub hM).div_const (1 + n)
    exact this.congr (fun t => (hkrec t).symm)
  have eC : M = (1 + deriv f L) * (β * M - n * (1 - β) * L) := by
    refine tendsto_nhds_unique hM1 ?_
    have := (((tendsto_const_nhds (x := (1 : ℝ))).add (hdc.tendsto.comp hL1)).mul
      (((tendsto_const_nhds (x := β)).mul hM).sub
        ((tendsto_const_nhds (x := n * (1 - β))).mul hL1)))
    exact this.congr (fun t => by simp only [Function.comp_apply]; exact (hcrec t).symm)
  have hMfL : M = f L - n * L := by
    rw [eq_div_iff (by linarith)] at eK; linarith
  have hRL : 0 < 1 + deriv f L := by linarith [hT.neo.deriv_pos hLpos]
  obtain ⟨hdomL, hMq⟩ := (deltaC_zero_iff f hβ1 hn hLpos hMpos hRL).mp eC
  have hresL : residual f β n L = 0 := by unfold residual; linarith
  obtain ⟨kb, -, huniq⟩ := steady_existsUnique hT hβ hβ1 hn
  have hLk : L = kbar := (huniq L ⟨hLpos, hdomL, hresL⟩).trans (huniq kbar ⟨hkb, hdom, hres⟩).symm
  subst hLk
  exact ⟨hL, hMfL ▸ hM⟩

/-- **The global saddle path of the Weil OLG model** (O&R §7.1.2.2, Fig. 7.7, made precise):
there is a unique steady state `k̄`, and from every `k₀ > 0` exactly one initial consumption
`c₀` keeps (32)–(33) in the positive quadrant; along that path capital and consumption are
monotone and converge to `(k̄, f(k̄) - n k̄)`, and `c₀ = (1-β)[(1 + f'(k₀)) k₀ + ∑ D_t w_t]` is the
log rule with the market's human wealth, so the path is the competitive equilibrium. Every
other initial consumption eventually drives capital or consumption negative. -/
theorem weil_saddle_path (hT : Technology f) {β n k0 : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hn : 0 < n) (hk0 : 0 < k0) :
    ∃ kbar, 0 < kbar ∧ 1 < β * (1 + deriv f kbar) ∧ residual f β n kbar = 0 ∧
      ∃! c0, PosOrbit f β n k0 c0 ∧
        Tendsto (fun t => (orb f β n k0 c0 t).1) atTop (𝓝 kbar) ∧
        Tendsto (fun t => (orb f β n k0 c0 t).2) atTop (𝓝 (f kbar - n * kbar)) ∧
        (Monotone (fun t => (orb f β n k0 c0 t).1) ∨
          Antitone (fun t => (orb f β n k0 c0 t).1)) ∧
        c0 = (1 - β) * ((1 + deriv f k0) * k0 +
          ∑' t, discF f (fun t => (orb f β n k0 c0 t).1) t *
            wageF f (fun t => (orb f β n k0 c0 t).1) t) := by
  obtain ⟨kbar, ⟨hkb, hdom, hres⟩, -⟩ := steady_existsUnique hT hβ hβ1 hn
  obtain ⟨c0, hp⟩ := posOrbit_exists hT hβ hβ1 hn hk0
  refine ⟨kbar, hkb, hdom, hres, c0, ⟨hp, (saddle_tendsto hT hβ hβ1 hn hp hkb hdom hres).1,
    (saddle_tendsto hT hβ hβ1 hn hp hkb hdom hres).2, ?_,
    (posOrbit_representation hT hβ hβ1 hn hp).2⟩, fun c hc => posOrbit_unique hT hβ hβ1 hn hc.1 hp⟩
  obtain ⟨hmon, hant⟩ := saddle_monotone hT hβ hβ1 hn hp
  rcases le_total (orb f β n k0 c0 0).1 (orb f β n k0 c0 1).1 with h | h
  · exact Or.inl (hmon h).1
  · exact Or.inr (hant h).1

/-! ## Exercise 1(c): the general-equilibrium path under announced spending -/

/-- Capital accumulation (32) with per-capita spending `g` financed by a lump-sum tax. -/
noncomputable def nextKg (f : ℝ → ℝ) (n g k c : ℝ) : ℝ := (f k + k - c - g) / (1 + n)

/-- One step of (32)–(33) with spending `g` at that date ((33) is unchanged, Ex. 1(a)). -/
noncomputable def stepG (f : ℝ → ℝ) (β n g : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (nextKg f n g p.1 p.2,
    (1 + deriv f (nextKg f n g p.1 p.2)) * (β * p.2 - n * (1 - β) * nextKg f n g p.1 p.2))

/-- The orbit of the economy with a spending path `g_t`. -/
noncomputable def orbG (f : ℝ → ℝ) (β n : ℝ) (g : ℕ → ℝ) (k0 c0 : ℝ) : ℕ → ℝ × ℝ
  | 0 => (k0, c0)
  | t + 1 => stepG f β n (g t) (orbG f β n g k0 c0 t)

/-- A positive (equilibrium) path with spending. -/
def PosOrbitG (f : ℝ → ℝ) (β n : ℝ) (g : ℕ → ℝ) (k0 c0 : ℝ) : Prop :=
  ∀ t, 0 < (orbG f β n g k0 c0 t).1 ∧ 0 < (orbG f β n g k0 c0 t).2

/-- **Human-wealth representation with taxes**: along any positive path with spending
`0 ≤ g_t ≤ G`, `c₀ = (1 - β)[(1 + f'(k₀)) k₀ + ∑ D_t (w_t - g_t)]` (human wealth net of taxes;
the gap `X_t` again satisfies `X_{t+1} = R_{t+1} X_t`). -/
theorem posOrbitG_representation (hT : Technology f) {β n G k0 c0 : ℝ} {g : ℕ → ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hn : 0 < n) (hg : ∀ t, 0 ≤ g t ∧ g t ≤ G)
    (hp : PosOrbitG f β n g k0 c0) :
    Summable (fun t => discF f (fun t => (orbG f β n g k0 c0 t).1) t *
        (wageF f (fun t => (orbG f β n g k0 c0 t).1) t - g t)) ∧
      c0 = (1 - β) * ((1 + deriv f k0) * k0 +
        ∑' t, discF f (fun t => (orbG f β n g k0 c0 t).1) t *
          (wageF f (fun t => (orbG f β n g k0 c0 t).1) t - g t)) := by
  set k : ℕ → ℝ := fun t => (orbG f β n g k0 c0 t).1
  set c : ℕ → ℝ := fun t => (orbG f β n g k0 c0 t).2
  have hk : ∀ t, 0 < k t := fun t => (hp t).1
  have hc : ∀ t, 0 < c t := fun t => (hp t).2
  have hkrec : ∀ t, k (t + 1) = (f (k t) + k t - c t - g t) / (1 + n) := fun t => rfl
  have hcrec : ∀ t, c (t + 1) = (1 + deriv f (k (t + 1))) * (β * c t - n * (1 - β) * k (t + 1)) :=
    fun t => rfl
  -- bounded capital
  obtain ⟨C, hC, hfC⟩ := f_linear_bound hT hn
  set K := max k0 (2 * C / n)
  have hK0 : 0 < K := lt_of_lt_of_le (hp 0).1 (le_max_left _ _)
  have hK : ∀ t, k t ≤ K := by
    intro t
    induction t with
    | zero => exact le_max_left _ _
    | succ t ih =>
      rw [hkrec, div_le_iff₀ (by linarith)]
      have h1 := hfC _ (hk t).le
      have h2 : 2 * C / n ≤ K := le_max_right _ _
      have h3 : C ≤ n / 2 * K := by rw [div_le_iff₀ hn] at h2; nlinarith
      nlinarith [hc t, (hg t).1]
  set ρ := 1 / (1 + deriv f K)
  have hRK : 1 < 1 + deriv f K := by linarith [hT.neo.deriv_pos hK0]
  have hρ0 : 0 < ρ := by simp only [ρ]; positivity
  have hρ1 : ρ < 1 := by simp only [ρ]; rw [div_lt_one (by linarith)]; exact hRK
  set W := f K
  set D := discF f k
  set v : ℕ → ℝ := fun t => wageF f k t - g t
  have hD := discF_pos hT hk
  have hv : ∀ t, |v t| ≤ W + G := by
    intro t
    have h1 := (wage_nonneg_mono hT (hk t) le_rfl).1
    have := f_mono hT (hk t).le (hK t)
    have := mul_pos (hk t) (hT.neo.deriv_pos (hk t))
    simp only [v, wageF] at h1 ⊢
    rw [abs_le]; constructor <;> linarith [(hg t).1, (hg t).2]
  have hratio := discF_ratio hT hk hK
  have hgeo := summable_geometric_of_lt_one hρ0.le hρ1
  have hWG : 0 ≤ W + G := (abs_nonneg _).trans (hv 0)
  have hsumt : ∀ t, Summable (fun s => D (s + t) * v (s + t)) := by
    intro t
    refine Summable.of_norm_bounded ((hgeo.mul_left (D t)).mul_right (W + G)) (fun s => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hD _)]
    calc D (s + t) * |v (s + t)| ≤ D (s + t) * (W + G) :=
          mul_le_mul_of_nonneg_left (hv _) (hD _).le
      _ ≤ D t * ρ ^ s * (W + G) := mul_le_mul_of_nonneg_right (hratio t s) hWG
  set Tt : ℕ → ℝ := fun t => ∑' s, D (s + t) * v (s + t)
  have hTt_abs : ∀ t, |Tt t| ≤ D t * ((W + G) / (1 - ρ)) := by
    intro t
    have h1 : |Tt t| ≤ ∑' s, |D (s + t) * v (s + t)| :=
      norm_tsum_le_tsum_norm (f := fun s => D (s + t) * v (s + t)) (hsumt t).abs
    have h2 : ∑' s, |D (s + t) * v (s + t)| ≤ ∑' s, D t * ρ ^ s * (W + G) := by
      refine (hsumt t).abs.tsum_le_tsum (fun s => ?_) ((hgeo.mul_left (D t)).mul_right _)
      rw [abs_mul, abs_of_pos (hD _)]
      calc D (s + t) * |v (s + t)| ≤ D (s + t) * (W + G) :=
            mul_le_mul_of_nonneg_left (hv _) (hD _).le
        _ ≤ D t * ρ ^ s * (W + G) := mul_le_mul_of_nonneg_right (hratio t s) hWG
    rw [tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one hρ0.le hρ1] at h2
    calc |Tt t| ≤ D t * (1 - ρ)⁻¹ * (W + G) := h1.trans h2
      _ = D t * ((W + G) / (1 - ρ)) := by ring
  have hTt_rec : ∀ t, Tt t = D t * v t + Tt (t + 1) := by
    intro t
    simp only [Tt]
    rw [(hsumt t).tsum_eq_zero_add]
    simp only [zero_add]
    congr 1
    congr 1; funext s; rw [show s + 1 + t = s + (t + 1) by ring]
  set H : ℕ → ℝ := fun t => Tt t / D t
  set X : ℕ → ℝ := fun t => c t - (1 - β) * ((1 + deriv f (k t)) * k t + H t)
  have hDrec : ∀ t, D (t + 1) = D t / (1 + deriv f (k (t + 1))) := fun t => rfl
  have hXrec : ∀ t, X (t + 1) = (1 + deriv f (k (t + 1))) * X t := by
    intro t
    have hDt : D t ≠ 0 := ne_of_gt (hD t)
    have hR1 : 0 < 1 + deriv f (k (t + 1)) := by linarith [hT.neo.deriv_pos (hk (t + 1))]
    have hH1 : H (t + 1) = (1 + deriv f (k (t + 1))) * (H t - v t) := by
      simp only [H]
      rw [hDrec, hTt_rec t]
      field_simp
      ring
    have h32 : (1 + n) * k (t + 1) = (1 + deriv f (k t)) * k t + v t - c t := by
      rw [hkrec]; simp only [v, wageF]; field_simp; ring
    simp only [X]
    rw [hcrec, hH1]
    linear_combination (-(1 + deriv f (k (t + 1))) * (1 - β)) * h32
  set Bx := 2 * (K + W) + (W + G) / (1 - ρ)
  have hXb : ∀ t, |X t| ≤ Bx := by
    intro t
    have hct : c t < f (k t) + k t := by
      have := hk (t + 1); rw [hkrec, div_pos_iff_of_pos_right (by linarith)] at this
      linarith [(hg t).1]
    have hfk : f (k t) ≤ W := f_mono hT (hk t).le (hK t)
    have hRk : (1 + deriv f (k t)) * k t ≤ k t + f (k t) := by
      have := hT.neo.deriv_mul_lt (hk t); nlinarith
    have hRk0 : 0 ≤ (1 + deriv f (k t)) * k t :=
      mul_nonneg (by linarith [hT.neo.deriv_pos (hk t)]) (hk t).le
    have hHb : |H t| ≤ (W + G) / (1 - ρ) := by
      simp only [H]; rw [abs_div, abs_of_pos (hD t), div_le_iff₀ (hD t)]; linarith [hTt_abs t]
    have hWρ : 0 ≤ (W + G) / (1 - ρ) := div_nonneg hWG (by linarith)
    have := abs_le.mp hHb
    simp only [X]
    rw [abs_le]
    constructor <;> nlinarith [hc t, hK t, f_nonneg hT hK0.le]
  have hX0 : X 0 = 0 := by
    by_contra hne
    have hgrow : ∀ t, (1 + deriv f K) ^ t * |X 0| ≤ |X t| := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        have hR1 : 0 < 1 + deriv f (k (t + 1)) := by linarith [hT.neo.deriv_pos (hk (t + 1))]
        rw [hXrec, abs_mul, abs_of_pos hR1, pow_succ]
        have hd : deriv f K ≤ deriv f (k (t + 1)) :=
          hT.neo.deriv_strictAnti.antitoneOn (hk _) hK0 (hK _)
        have := abs_nonneg (X t)
        nlinarith
    have hpos : 0 < |X 0| := abs_pos.mpr hne
    have hinf := (tendsto_pow_atTop_atTop_of_one_lt hRK).atTop_mul_const hpos
    obtain ⟨t, ht⟩ := (hinf.eventually (eventually_gt_atTop Bx)).exists
    linarith [hgrow t, hXb t]
  refine ⟨by simpa using hsumt 0, ?_⟩
  have hH0 : H 0 = ∑' t, D t * v t := by
    simp only [H, Tt, add_zero]
    have : D 0 = 1 := rfl
    rw [this, div_one]
  have : X 0 = c0 - (1 - β) * ((1 + deriv f k0) * k0 + H 0) := rfl
  rw [hH0] at this
  linarith

/-- The steady state is a rest point of (32)–(33) without spending. -/
theorem steady_orbit_const {β n k c : ℝ} (hss1 : c = f k - n * k)
    (hss2 : c = (1 + deriv f k) * (β * c - n * (1 - β) * k)) (hn : 0 < n) (t : ℕ) :
    orbG f β n (fun _ => 0) k c t = (k, c) := by
  have hK : nextKg f n 0 k c = k := by
    unfold nextKg; rw [div_eq_iff (by linarith)]; linarith
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [orbG, ih, stepG, hK]
    exact Prod.ext rfl hss2.symm

/-- Comparison with spending: a path with spending `g_t ≥ 0`, starting from lower capital and
higher consumption than a path without spending, keeps lower capital and higher consumption
while both are positive. -/
theorem orbitG_compare (hT : Technology f) {β n : ℝ} {g : ℕ → ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hn : 0 < n) (hg : ∀ t, 0 ≤ g t) {ka kb ca cb : ℝ} (ha : PosOrbitG f β n g ka ca)
    (hb : PosOrbitG f β n (fun _ => 0) kb cb) (hk : ka ≤ kb) (hc : cb ≤ ca) (t : ℕ) :
    (orbG f β n g ka ca t).1 ≤ (orbG f β n (fun _ => 0) kb cb t).1 ∧
      (orbG f β n (fun _ => 0) kb cb t).2 ≤ (orbG f β n g ka ca t).2 := by
  induction t with
  | zero => exact ⟨hk, hc⟩
  | succ t ih =>
    obtain ⟨hk', hc'⟩ := ih
    have hpa := (ha t).1
    have hpa1 := (ha (t + 1)).1
    have hpb1 := (hb (t + 1)).1
    have hcb1 := (hb (t + 1)).2
    simp only [orbG, stepG] at hpa1 hpb1 hcb1 ⊢
    have hK : nextKg f n (g t) (orbG f β n g ka ca t).1 (orbG f β n g ka ca t).2 ≤
        nextKg f n 0 (orbG f β n (fun _ => 0) kb cb t).1 (orbG f β n (fun _ => 0) kb cb t).2 := by
      unfold nextKg
      apply div_le_div_of_nonneg_right _ (by linarith)
      have := f_mono hT hpa.le hk'
      linarith [hg t]
    refine ⟨hK, ?_⟩
    set Ka := nextKg f n (g t) (orbG f β n g ka ca t).1 (orbG f β n g ka ca t).2
    set Kb := nextKg f n 0 (orbG f β n (fun _ => 0) kb cb t).1
      (orbG f β n (fun _ => 0) kb cb t).2
    have hR : deriv f Kb ≤ deriv f Ka := hT.neo.deriv_strictAnti.antitoneOn hpa1 hpb1 hK
    have hRb : 0 < 1 + deriv f Kb := by linarith [hT.neo.deriv_pos hpb1]
    have hAb : 0 < β * (orbG f β n (fun _ => 0) kb cb t).2 - n * (1 - β) * Kb := by
      by_contra h; push Not at h
      have := mul_nonpos_of_nonneg_of_nonpos hRb.le h
      linarith
    have hA : β * (orbG f β n (fun _ => 0) kb cb t).2 - n * (1 - β) * Kb ≤
        β * (orbG f β n g ka ca t).2 - n * (1 - β) * Ka := by
      have := mul_le_mul_of_nonneg_left hc' hβ.le
      have := mul_le_mul_of_nonneg_left hK (mul_pos hn (by linarith : (0 : ℝ) < 1 - β)).le
      linarith
    calc (1 + deriv f Kb) * (β * (orbG f β n (fun _ => 0) kb cb t).2 - n * (1 - β) * Kb)
        ≤ (1 + deriv f Ka) * (β * (orbG f β n (fun _ => 0) kb cb t).2 - n * (1 - β) * Kb) :=
          mul_le_mul_of_nonneg_right (by linarith) hAb.le
      _ ≤ (1 + deriv f Ka) * (β * (orbG f β n g ka ca t).2 - n * (1 - β) * Ka) :=
          mul_le_mul_of_nonneg_left hA (by linarith)

/-- **Ex. 1(c), impact effect in general equilibrium**: starting from the steady state
`(k̄, c̄)` without spending, if a nonnegative bounded spending path that is positive at some
date is announced at date 0, then on every equilibrium path consumption falls on impact:
`c₀ < c̄`. -/
theorem announcement_impact (hT : Technology f) {β n G kbar cbar c0 : ℝ} {g : ℕ → ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hn : 0 < n) (hkb : 0 < kbar) (hcb : 0 < cbar)
    (hss1 : cbar = f kbar - n * kbar)
    (hss2 : cbar = (1 + deriv f kbar) * (β * cbar - n * (1 - β) * kbar))
    (hg : ∀ t, 0 ≤ g t ∧ g t ≤ G) (hgpos : ∃ t, 0 < g t)
    (hp : PosOrbitG f β n g kbar c0) : c0 < cbar := by
  by_contra hle
  push Not at hle
  have hconst := steady_orbit_const hss1 hss2 hn (β := β)
  have hpb : PosOrbitG f β n (fun _ => 0) kbar cbar := fun t => by
    rw [hconst t]; exact ⟨hkb, hcb⟩
  have hcmp := orbitG_compare hT hβ hβ1 hn (fun t => (hg t).1) hp hpb le_rfl hle
  obtain ⟨hs, hrep⟩ := posOrbitG_representation hT hβ hβ1 hn hg hp
  obtain ⟨hsb, hrepb⟩ := posOrbitG_representation hT hβ hβ1 hn
    (fun _ => ⟨le_rfl, le_refl (0 : ℝ)⟩) hpb
  set ka : ℕ → ℝ := fun t => (orbG f β n g kbar c0 t).1
  set kb : ℕ → ℝ := fun t => (orbG f β n (fun _ => 0) kbar cbar t).1
  have hka : ∀ t, 0 < ka t := fun t => (hp t).1
  have hkb' : ∀ t, 0 < kb t := fun t => (hpb t).1
  have hle' : ∀ t, ka t ≤ kb t := fun t => (hcmp t).1
  have hD : ∀ t, discF f ka t ≤ discF f kb t := by
    intro t
    induction t with
    | zero => simp [discF]
    | succ t ih =>
      simp only [discF]
      have hd : deriv f (kb (t + 1)) ≤ deriv f (ka (t + 1)) :=
        hT.neo.deriv_strictAnti.antitoneOn (hka _) (hkb' _) (hle' _)
      have h1 := discF_pos hT hka t
      rw [div_le_div_iff₀ (by linarith [hT.neo.deriv_pos (hka (t + 1))])
        (by linarith [hT.neo.deriv_pos (hkb' (t + 1))])]
      have e1 := mul_le_mul_of_nonneg_right ih
        (by linarith [hT.neo.deriv_pos (hkb' (t + 1))] : (0 : ℝ) ≤ 1 + deriv f (kb (t + 1)))
      have e2 := mul_le_mul_of_nonneg_left (by linarith : 1 + deriv f (kb (t + 1)) ≤
        1 + deriv f (ka (t + 1))) (discF_pos hT hkb' t).le
      linarith
  obtain ⟨t0, ht0⟩ := hgpos
  have hstrict : ∑' t, discF f ka t * (wageF f ka t - g t) <
      ∑' t, discF f kb t * (wageF f kb t - (fun _ => (0 : ℝ)) t) := by
    refine hs.tsum_lt_tsum (i := t0) (fun t => ?_) ?_ hsb
    · have hw := wage_nonneg_mono hT (hka t) (hle' t)
      have := mul_le_mul (hD t) hw.2 hw.1 (discF_pos hT hkb' t).le
      have := mul_nonneg (discF_pos hT hka t).le (hg t).1
      simp only [wageF] at this ⊢
      nlinarith
    · have hw := wage_nonneg_mono hT (hka t0) (hle' t0)
      have := mul_le_mul (hD t0) hw.2 hw.1 (discF_pos hT hkb' t0).le
      have := mul_pos (discF_pos hT hka t0) ht0
      simp only [wageF] at this ⊢
      nlinarith
  have h1β : 0 < 1 - β := by linarith
  have := mul_lt_mul_of_pos_left (add_lt_add_left hstrict ((1 + deriv f kbar) * kbar)) h1β
  linarith

/-- **Ex. 1(c), the anticipation phase**: before spending starts (`g_t = 0` for `t < T`),
capital along the equilibrium path stays above the old steady state and consumption below
it; capital is strictly higher from date 1. -/
theorem announcement_anticipation (hT : Technology f) {β n kbar cbar c0 : ℝ} {g : ℕ → ℝ}
    {T : ℕ} (hβ : 0 < β) (hβ1 : β < 1) (hn : 0 < n) (hkb : 0 < kbar)
    (hss1 : cbar = f kbar - n * kbar)
    (hss2 : cbar = (1 + deriv f kbar) * (β * cbar - n * (1 - β) * kbar))
    (hgT : ∀ t < T, g t = 0) (hp : PosOrbitG f β n g kbar c0) (himp : c0 < cbar) :
    (∀ t ≤ T, kbar ≤ (orbG f β n g kbar c0 t).1 ∧ (orbG f β n g kbar c0 t).2 ≤ cbar) ∧
      (1 ≤ T → kbar < (orbG f β n g kbar c0 1).1) := by
  have hstep : ∀ t < T, kbar ≤ (orbG f β n g kbar c0 t).1 → (orbG f β n g kbar c0 t).2 ≤ cbar →
      kbar ≤ (orbG f β n g kbar c0 (t + 1)).1 ∧ (orbG f β n g kbar c0 (t + 1)).2 ≤ cbar := by
    intro t ht hk hc
    have hkt := (hp t).1
    have hk1 := (hp (t + 1)).1
    simp only [orbG, stepG, hgT t ht] at hk1 ⊢
    have hK : kbar ≤ nextKg f n 0 (orbG f β n g kbar c0 t).1 (orbG f β n g kbar c0 t).2 := by
      unfold nextKg
      rw [le_div_iff₀ (by linarith)]
      have := f_mono hT hkb.le hk
      linarith
    refine ⟨hK, ?_⟩
    set K1 := nextKg f n 0 (orbG f β n g kbar c0 t).1 (orbG f β n g kbar c0 t).2
    have hR : deriv f K1 ≤ deriv f kbar := hT.neo.deriv_strictAnti.antitoneOn hkb hk1 hK
    rw [hss2]
    have hA0 : 0 < β * cbar - n * (1 - β) * kbar := by
      by_contra h; push Not at h
      have := mul_nonpos_of_nonneg_of_nonpos
        (by linarith [hT.neo.deriv_pos hkb] : 0 ≤ 1 + deriv f kbar) h
      have hcb : 0 < cbar := by
        have := (hp 0).2; simp only [orbG] at this; linarith
      linarith
    have hA : β * (orbG f β n g kbar c0 t).2 - n * (1 - β) * K1 ≤
        β * cbar - n * (1 - β) * kbar := by
      have := mul_le_mul_of_nonneg_left hc hβ.le
      have := mul_le_mul_of_nonneg_left hK (mul_pos hn (by linarith : (0 : ℝ) < 1 - β)).le
      linarith
    by_cases hAn : 0 ≤ β * (orbG f β n g kbar c0 t).2 - n * (1 - β) * K1
    · calc (1 + deriv f K1) * (β * (orbG f β n g kbar c0 t).2 - n * (1 - β) * K1)
          ≤ (1 + deriv f kbar) * (β * (orbG f β n g kbar c0 t).2 - n * (1 - β) * K1) :=
            mul_le_mul_of_nonneg_right (by linarith) hAn
        _ ≤ _ := mul_le_mul_of_nonneg_left hA (by linarith [hT.neo.deriv_pos hkb])
    · push Not at hAn
      have := mul_neg_of_pos_of_neg (by linarith [hT.neo.deriv_pos hk1] :
        0 < 1 + deriv f K1) hAn
      have := mul_pos (by linarith [hT.neo.deriv_pos hkb] : 0 < 1 + deriv f kbar) hA0
      linarith
  refine ⟨fun t ht => ?_, fun hT1 => ?_⟩
  · induction t with
    | zero => exact ⟨le_rfl, himp.le⟩
    | succ t ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      exact hstep t (by omega) h1 h2
  · simp only [orbG, stepG, hgT 0 (by omega), nextKg]
    rw [lt_div_iff₀ (by linarith)]
    linarith

/-- **Ex. 1(c), uniqueness**: among equilibrium paths along which the wage always covers the
tax (`g_t ≤ w_t`), there is at most one from a given `k₀`. -/
theorem announcement_unique (hT : Technology f) {β n G k0 c0 c0' : ℝ} {g : ℕ → ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hn : 0 < n) (hg : ∀ t, 0 ≤ g t ∧ g t ≤ G)
    (hp : PosOrbitG f β n g k0 c0) (hp' : PosOrbitG f β n g k0 c0')
    (hw : ∀ t, g t ≤ wageF f (fun t => (orbG f β n g k0 c0 t).1) t)
    (hw' : ∀ t, g t ≤ wageF f (fun t => (orbG f β n g k0 c0' t).1) t) : c0 = c0' := by
  wlog hlt : c0 < c0' generalizing c0 c0'
  · rcases lt_trichotomy c0 c0' with h | h | h
    · exact absurd h hlt
    · exact h
    · exact (this hp' hp hw' hw h).symm
  exfalso
  -- the higher-consumption path has lower capital at every date
  have hcmp : ∀ t, (orbG f β n g k0 c0' t).1 ≤ (orbG f β n g k0 c0 t).1 ∧
      (orbG f β n g k0 c0 t).2 ≤ (orbG f β n g k0 c0' t).2 := by
    intro t
    induction t with
    | zero => exact ⟨le_rfl, hlt.le⟩
    | succ t ih =>
      obtain ⟨hk', hc'⟩ := ih
      have hpa := (hp' t).1
      have hpa1 := (hp' (t + 1)).1
      have hpb1 := (hp (t + 1)).1
      have hcb1 := (hp (t + 1)).2
      simp only [orbG, stepG] at hpa1 hpb1 hcb1 ⊢
      have hK : nextKg f n (g t) (orbG f β n g k0 c0' t).1 (orbG f β n g k0 c0' t).2 ≤
          nextKg f n (g t) (orbG f β n g k0 c0 t).1 (orbG f β n g k0 c0 t).2 := by
        unfold nextKg
        apply div_le_div_of_nonneg_right _ (by linarith)
        have := f_mono hT hpa.le hk'
        linarith
      refine ⟨hK, ?_⟩
      set Ka := nextKg f n (g t) (orbG f β n g k0 c0' t).1 (orbG f β n g k0 c0' t).2
      set Kb := nextKg f n (g t) (orbG f β n g k0 c0 t).1 (orbG f β n g k0 c0 t).2
      have hR : deriv f Kb ≤ deriv f Ka := hT.neo.deriv_strictAnti.antitoneOn hpa1 hpb1 hK
      have hRb : 0 < 1 + deriv f Kb := by linarith [hT.neo.deriv_pos hpb1]
      have hAb : 0 < β * (orbG f β n g k0 c0 t).2 - n * (1 - β) * Kb := by
        by_contra h; push Not at h
        have := mul_nonpos_of_nonneg_of_nonpos hRb.le h
        linarith
      have hA : β * (orbG f β n g k0 c0 t).2 - n * (1 - β) * Kb ≤
          β * (orbG f β n g k0 c0' t).2 - n * (1 - β) * Ka := by
        have := mul_le_mul_of_nonneg_left hc' hβ.le
        have := mul_le_mul_of_nonneg_left hK (mul_pos hn (by linarith : (0 : ℝ) < 1 - β)).le
        linarith
      calc (1 + deriv f Kb) * (β * (orbG f β n g k0 c0 t).2 - n * (1 - β) * Kb)
          ≤ (1 + deriv f Ka) * (β * (orbG f β n g k0 c0 t).2 - n * (1 - β) * Kb) :=
            mul_le_mul_of_nonneg_right (by linarith) hAb.le
        _ ≤ (1 + deriv f Ka) * (β * (orbG f β n g k0 c0' t).2 - n * (1 - β) * Ka) :=
            mul_le_mul_of_nonneg_left hA (by linarith)
  obtain ⟨hs, hrep⟩ := posOrbitG_representation hT hβ hβ1 hn hg hp
  obtain ⟨hs', hrep'⟩ := posOrbitG_representation hT hβ hβ1 hn hg hp'
  set ka : ℕ → ℝ := fun t => (orbG f β n g k0 c0' t).1
  set kb : ℕ → ℝ := fun t => (orbG f β n g k0 c0 t).1
  have hka : ∀ t, 0 < ka t := fun t => (hp' t).1
  have hkb : ∀ t, 0 < kb t := fun t => (hp t).1
  have hle : ∀ t, ka t ≤ kb t := fun t => (hcmp t).1
  have hD : ∀ t, discF f ka t ≤ discF f kb t := by
    intro t
    induction t with
    | zero => simp [discF]
    | succ t ih =>
      simp only [discF]
      have hd : deriv f (kb (t + 1)) ≤ deriv f (ka (t + 1)) :=
        hT.neo.deriv_strictAnti.antitoneOn (hka _) (hkb _) (hle _)
      have h1 := discF_pos hT hka t
      rw [div_le_div_iff₀ (by linarith [hT.neo.deriv_pos (hka (t + 1))])
        (by linarith [hT.neo.deriv_pos (hkb (t + 1))])]
      have e1 := mul_le_mul_of_nonneg_right ih
        (by linarith [hT.neo.deriv_pos (hkb (t + 1))] : (0 : ℝ) ≤ 1 + deriv f (kb (t + 1)))
      have e2 := mul_le_mul_of_nonneg_left (by linarith : 1 + deriv f (kb (t + 1)) ≤
        1 + deriv f (ka (t + 1))) (discF_pos hT hkb t).le
      linarith
  have hsum : ∑' t, discF f ka t * (wageF f ka t - g t) ≤
      ∑' t, discF f kb t * (wageF f kb t - g t) := by
    refine hs'.tsum_le_tsum (fun t => ?_) hs
    have hwm := (wage_nonneg_mono hT (hka t) (hle t)).2
    have h1 : 0 ≤ wageF f ka t - g t := by have := hw' t; simp only [ka]; linarith
    calc discF f ka t * (wageF f ka t - g t) ≤ discF f kb t * (wageF f ka t - g t) :=
          mul_le_mul_of_nonneg_right (hD t) h1
      _ ≤ discF f kb t * (wageF f kb t - g t) :=
          mul_le_mul_of_nonneg_left (by simp only [wageF] at hwm ⊢; linarith)
            (discF_pos hT hkb t).le
  have h1β : 0 < 1 - β := by linarith
  have := mul_le_mul_of_nonneg_left (add_le_add_left hsum ((1 + deriv f k0) * k0)) h1β.le
  linarith

/-- **Ex. 1(c), existence can fail**: if spending from some date `T` on exceeds the maximal
sustainable consumption `max_k [f(k) - nk]` by a margin `ε > 0`, no equilibrium path exists
(capital falls by at least `ε/(1+n)` every period after `T`). -/
theorem announcement_no_equilibrium {β n g ε k0 c0 : ℝ} {gs : ℕ → ℝ}
    {T : ℕ} (hn : 0 < n) (hε : 0 < ε) (hgs : ∀ t, T ≤ t → gs t = g)
    (hbig : ∀ k, 0 ≤ k → f k - n * k ≤ g - ε) : ¬ PosOrbitG f β n gs k0 c0 := by
  intro hp
  have hdrop : ∀ s, (orbG f β n gs k0 c0 (T + s)).1 ≤
      (orbG f β n gs k0 c0 T).1 - s * (ε / (1 + n)) := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      have hk := (hp (T + s)).1
      have hc := (hp (T + s)).2
      rw [show T + (s + 1) = T + s + 1 by ring]
      simp only [orbG, stepG, nextKg, hgs (T + s) (by omega)]
      have hb := hbig _ hk.le
      rw [div_le_iff₀ (by linarith)]
      push_cast
      have e : ((orbG f β n gs k0 c0 T).1 - ((s : ℝ) + 1) * (ε / (1 + n))) * (1 + n) =
          (1 + n) * (orbG f β n gs k0 c0 T).1 - ((s : ℝ) + 1) * ε := by field_simp
      have e2 : (1 + n) * ((orbG f β n gs k0 c0 T).1 - (s : ℝ) * (ε / (1 + n))) =
          (1 + n) * (orbG f β n gs k0 c0 T).1 - (s : ℝ) * ε := by field_simp
      have := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ 1 + n)
      rw [e]
      linarith
  obtain ⟨s, hs⟩ := exists_nat_gt ((orbG f β n gs k0 c0 T).1 / (ε / (1 + n)))
  have h1 := hdrop s
  have h2 := (hp (T + s)).1
  have hpos : 0 < ε / (1 + n) := div_pos hε (by linarith)
  rw [div_lt_iff₀ hpos] at hs
  linarith

/-- **Ex. 1(c), the long run**: if an equilibrium path with spending converging to `g > 0`
converges to a positive rest point `(L, M)`, that rest point is a steady state with spending
(`Φ(L) = g`, `M = f(L) - nL - g`), so capital and consumption end strictly below the
no-spending steady state (crowding out). -/
theorem announcement_long_run (hT : Technology f) {β n g L M kbar : ℝ} {gs : ℕ → ℝ}
    {k0 c0 : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hn : 0 < n) (hg : 0 < g)
    (hgs : Tendsto gs atTop (𝓝 g)) (hL : 0 < L) (hM : 0 < M)
    (hkL : Tendsto (fun t => (orbG f β n gs k0 c0 t).1) atTop (𝓝 L))
    (hcM : Tendsto (fun t => (orbG f β n gs k0 c0 t).2) atTop (𝓝 M))
    (hkb : 0 < kbar) (hdom : 1 < β * (1 + deriv f kbar)) (hres : residual f β n kbar = 0) :
    residual f β n L = g ∧ M = f L - n * L - g ∧ L < kbar ∧
      n * (1 - β) * L * qCoef f β L < n * (1 - β) * kbar * qCoef f β kbar := by
  have hfc : ContinuousAt f L := (hT.neo.diff L hL).continuousAt
  have hdc : ContinuousAt (deriv f) L := hT.prime_cont.continuousAt (Ioi_mem_nhds hL)
  have hL1 := hkL.comp (tendsto_add_atTop_nat 1)
  have hM1 := hcM.comp (tendsto_add_atTop_nat 1)
  have eK : L = (f L + L - M - g) / (1 + n) := by
    refine tendsto_nhds_unique hL1 ?_
    have := ((((hfc.tendsto.comp hkL).add hkL).sub hcM).sub hgs).div_const (1 + n)
    exact this.congr (fun t => rfl)
  have eC : M = (1 + deriv f L) * (β * M - n * (1 - β) * L) := by
    refine tendsto_nhds_unique hM1 ?_
    have := (((tendsto_const_nhds (x := (1 : ℝ))).add (hdc.tendsto.comp hL1)).mul
      (((tendsto_const_nhds (x := β)).mul hcM).sub
        ((tendsto_const_nhds (x := n * (1 - β))).mul hL1)))
    exact this.congr (fun t => rfl)
  have hMfL : M = f L - n * L - g := by rw [eq_div_iff (by linarith)] at eK; linarith
  have hRL : 0 < 1 + deriv f L := by linarith [hT.neo.deriv_pos hL]
  obtain ⟨hdomL, hMq⟩ := (deltaC_zero_iff f hβ1 hn hL hM hRL).mp eC
  have hresL : residual f β n L = g := by unfold residual; linarith
  obtain ⟨h1, h2⟩ := crowding_out hT hβ hβ1 hn hg hkb hL hdom hdomL hres hresL
  exact ⟨hresL, hMfL, h1, h2⟩


/-! ## Exercise 1(c): existence, uniqueness and monotonicity of the equilibrium path -/

/-- Capital at date `t` along the path with spending from `(k₀, c)` (Ex. 1(c)). -/
noncomputable def kG (f : ℝ → ℝ) (β n : ℝ) (g : ℕ → ℝ) (k0 c : ℝ) (t : ℕ) : ℝ :=
  (orbG f β n g k0 c t).1

/-- Consumption at date `t` along the path with spending from `(k₀, c)` (Ex. 1(c)). -/
noncomputable def cG (f : ℝ → ℝ) (β n : ℝ) (g : ℕ → ℝ) (k0 c : ℝ) (t : ℕ) : ℝ :=
  (orbG f β n g k0 c t).2

/-- The capital recursion with spending (Ex. 1(a), eq. (32) with `g_t`). -/
theorem kG_succ (f : ℝ → ℝ) (β n : ℝ) (g : ℕ → ℝ) (k0 c : ℝ) (t : ℕ) :
    kG f β n g k0 c (t + 1) = nextKg f n (g t) (kG f β n g k0 c t) (cG f β n g k0 c t) := rfl

/-- The consumption recursion (33), unchanged by spending (Ex. 1(a)). -/
theorem cG_succ (f : ℝ → ℝ) (β n : ℝ) (g : ℕ → ℝ) (k0 c : ℝ) (t : ℕ) :
    cG f β n g k0 c (t + 1) = (1 + deriv f (kG f β n g k0 c (t + 1))) *
      (β * cG f β n g k0 c t - n * (1 - β) * kG f β n g k0 c (t + 1)) := rfl

/-- One step with spending is continuous at `(k, c)` when `k > 0` and next capital is
positive (Ex. 1(c)). -/
theorem stepG_continuousAt (hT : Technology f) {β n gt : ℝ} {p : ℝ × ℝ} (h1 : 0 < p.1)
    (h2 : 0 < nextKg f n gt p.1 p.2) : ContinuousAt (stepG f β n gt) p := by
  have hK : ContinuousAt (fun p : ℝ × ℝ => nextKg f n gt p.1 p.2) p := by
    unfold nextKg
    exact (((((hT.neo.diff _ h1).continuousAt.comp continuousAt_fst).add continuousAt_fst).sub
      continuousAt_snd).sub continuousAt_const).div_const _
  have hD : ContinuousAt (fun p : ℝ × ℝ => deriv f (nextKg f n gt p.1 p.2)) p :=
    ContinuousAt.comp (g := deriv f) (f := fun p : ℝ × ℝ => nextKg f n gt p.1 p.2)
      (hT.prime_cont.continuousAt (Ioi_mem_nhds h2)) hK
  exact ContinuousAt.prodMk hK ((continuousAt_const.add hD).mul
    ((continuousAt_const.mul continuousAt_snd).sub (continuousAt_const.mul hK)))

/-- Finite stretches of paths with spending depend continuously on `c₀` while capital stays
positive (Ex. 1(c)). -/
theorem orbG_continuousAt (hT : Technology f) {β n k0 c : ℝ} {g : ℕ → ℝ} {T : ℕ}
    (hpos : ∀ j ≤ T, 0 < kG f β n g k0 c j) :
    ContinuousAt (fun c => orbG f β n g k0 c T) c := by
  induction T with
  | zero => exact continuousAt_const.prodMk continuousAt_id
  | succ T ih =>
    have ih' := ih (fun j hj => hpos j (by omega))
    have h1 : 0 < (orbG f β n g k0 c T).1 := hpos T (by omega)
    have h2 : 0 < nextKg f n (g T) (orbG f β n g k0 c T).1 (orbG f β n g k0 c T).2 :=
      hpos (T + 1) le_rfl
    exact ContinuousAt.comp (g := stepG f β n (g T)) (f := fun c => orbG f β n g k0 c T)
      (stepG_continuousAt hT h1 h2) ih'

/-- Next-period capital with spending is continuous in `c₀` while capital so far is positive
(Ex. 1(c)). -/
theorem kG_succ_continuousAt (hT : Technology f) {β n k0 c : ℝ} {g : ℕ → ℝ} {T : ℕ}
    (hpos : ∀ j ≤ T, 0 < kG f β n g k0 c j) :
    ContinuousAt (fun c => kG f β n g k0 c (T + 1)) c := by
  have h1 : 0 < (orbG f β n g k0 c T).1 := hpos T le_rfl
  have hK : ContinuousAt (fun p : ℝ × ℝ => nextKg f n (g T) p.1 p.2)
      (orbG f β n g k0 c T) := by
    unfold nextKg
    exact (((((hT.neo.diff _ h1).continuousAt.comp continuousAt_fst).add
      continuousAt_fst).sub continuousAt_snd).sub continuousAt_const).div_const _
  exact ContinuousAt.comp (g := fun p : ℝ × ℝ => nextKg f n (g T) p.1 p.2)
    (f := fun c => orbG f β n g k0 c T) hK (orbG_continuousAt hT hpos)

/-- Positive paths with nonnegative spending are bounded (Ex. 1(c)). -/
theorem posOrbitG_bounded (hT : Technology f) {β n k0 c0 : ℝ} {g : ℕ → ℝ} (hn : 0 < n)
    (hg : ∀ t, 0 ≤ g t) (hp : PosOrbitG f β n g k0 c0) :
    ∃ K, 0 < K ∧ ∀ t, (orbG f β n g k0 c0 t).1 ≤ K := by
  obtain ⟨C, hC, hfC⟩ := f_linear_bound hT hn
  have hk0 : 0 < k0 := (hp 0).1
  refine ⟨max k0 (2 * C / n), lt_of_lt_of_le hk0 (le_max_left _ _), fun t => ?_⟩
  induction t with
  | zero => exact le_max_left _ _
  | succ t ih =>
    obtain ⟨hkt, hct⟩ := hp t
    change nextKg f n (g t) (orbG f β n g k0 c0 t).1 (orbG f β n g k0 c0 t).2 ≤ _
    unfold nextKg
    rw [div_le_iff₀ (by linarith)]
    have h1 := hfC _ hkt.le
    have h2 : 2 * C / n ≤ max k0 (2 * C / n) := le_max_right _ _
    have h3 : C ≤ n / 2 * max k0 (2 * C / n) := by
      rw [div_le_iff₀ hn] at h2; nlinarith
    nlinarith [hg t]

/-- **The trapping level** (Ex. 1(c)): if `k_L > 0` has `f(k_L) - n k_L > G ≥ g`, then from
`k ≥ k_L` with `c ≤ 0` next capital exceeds `k_L` and next consumption is negative, so such a
path never recovers and never exhausts its capital. -/
theorem trapG (hT : Technology f) {β n gt G kL k c : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hn : 0 < n) (hkL : 0 < kL) (hg : 0 ≤ gt ∧ gt ≤ G) (hm : G < f kL - n * kL)
    (hk : kL ≤ k) (hc : c ≤ 0) :
    kL < nextKg f n gt k c ∧
      (1 + deriv f (nextKg f n gt k c)) * (β * c - n * (1 - β) * nextKg f n gt k c) < 0 := by
  have hK : kL < nextKg f n gt k c := by
    unfold nextKg
    rw [lt_div_iff₀ (by linarith)]
    have := f_mono hT hkL.le hk
    nlinarith
  refine ⟨hK, mul_neg_of_pos_of_neg (by linarith [hT.neo.deriv_pos (hkL.trans hK)]) ?_⟩
  have := mul_pos (mul_pos hn (by linarith : (0 : ℝ) < 1 - β)) (hkL.trans hK)
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ.le hc]

/-- **The safety invariant** (Ex. 1(c)): if `β(1 + f'(k_L)) > 1`, spending satisfies
`0 ≤ g_t ≤ G ≤ Φ(k_L)` (the steady-state residual) and `k₀ ≥ k_L`, then along any path, as
long as it has stayed in the positive quadrant, either capital is at least `k_L` or
consumption is at least `c* = n(1-β) k_L q(k_L) > 0` (the height of the `Δc = 0` locus at
`k_L`). Consumption can therefore turn nonpositive only at capital `≥ k_L`. -/
theorem safeG (hT : Technology f) {β n G kL k0 : ℝ} {g : ℕ → ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hn : 0 < n) (hkL : 0 < kL) (hkL0 : kL ≤ k0) (hdomL : 1 < β * (1 + deriv f kL))
    (hg : ∀ t, 0 ≤ g t ∧ g t ≤ G) (hG : G ≤ residual f β n kL) (c : ℝ) :
    ∀ t, (∀ j < t, 0 < kG f β n g k0 c j ∧ 0 < cG f β n g k0 c j) →
      0 < kG f β n g k0 c t →
        kL ≤ kG f β n g k0 c t ∨ n * (1 - β) * kL * qCoef f β kL ≤ cG f β n g k0 c t := by
  set RL := 1 + deriv f kL
  set q := qCoef f β kL
  set ν := n * (1 - β) * kL
  have hν : 0 < ν := mul_pos (mul_pos hn (by linarith)) hkL
  have hRL : 0 < RL := by linarith [hT.neo.deriv_pos hkL]
  have hq : q * (β * RL - 1) = RL := by
    change RL / (β * RL - 1) * (β * RL - 1) = RL
    exact div_mul_cancel₀ _ (by linarith)
  have hq0 : 0 < q := div_pos hRL (by linarith)
  have hm : ν * q ≤ f kL - n * kL - G := by
    unfold residual at hG; linarith
  intro t
  induction t with
  | zero => intro _ _; exact Or.inl hkL0
  | succ t ih =>
    intro hbefore hk1
    obtain ⟨hkt, hct⟩ := hbefore t (by omega)
    have ih' := ih (fun j hj => hbefore j (by omega)) hkt
    by_cases hK : kL ≤ kG f β n g k0 c (t + 1)
    · exact Or.inl hK
    right
    push Not at hK
    have hR1 : RL ≤ 1 + deriv f (kG f β n g k0 c (t + 1)) := by
      have := hT.neo.deriv_strictAnti.antitoneOn hk1 hkL hK.le
      simp only [RL]; linarith
    have hν' : n * (1 - β) * kG f β n g k0 c (t + 1) ≤ ν :=
      mul_le_mul_of_nonneg_left hK.le (mul_pos hn (by linarith)).le
    rw [cG_succ]
    set b := β * cG f β n g k0 c t - n * (1 - β) * kG f β n g k0 c (t + 1)
    rcases ih' with hkt' | hct'
    · -- entering the low-capital region: consumption was high
      have hk1e := kG_succ f β n g k0 c t
      unfold nextKg at hk1e
      rw [eq_div_iff (by linarith)] at hk1e
      have hf := f_mono hT hkL.le hkt'
      have hgt := (hg t).2
      have hcm : f kL - n * kL - G < cG f β n g k0 c t := by nlinarith
      have hb : β * (f kL - n * kL - G) - ν < b := by
        have := mul_lt_mul_of_pos_left hcm hβ; simp only [b]; linarith
      have hb0 : 0 ≤ β * (f kL - n * kL - G) - ν := by nlinarith
      calc ν * q = RL * (β * (ν * q) - ν) := by nlinarith
        _ ≤ RL * (β * (f kL - n * kL - G) - ν) := by
            apply mul_le_mul_of_nonneg_left _ hRL.le
            nlinarith
        _ ≤ RL * b := mul_le_mul_of_nonneg_left hb.le hRL.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hR1 (by linarith)
    · -- inside the low-capital region consumption does not fall
      have hb : β * cG f β n g k0 c t - ν ≤ b := by simp only [b]; linarith
      have hb0 : 0 ≤ β * cG f β n g k0 c t - ν := by nlinarith
      calc ν * q ≤ cG f β n g k0 c t := hct'
        _ ≤ RL * (β * cG f β n g k0 c t - ν) := by nlinarith
        _ ≤ RL * b := mul_le_mul_of_nonneg_left hb hRL.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hR1 (by linarith)

/-- "Too low" initial consumption with spending (Ex. 1(c)): capital stays positive up to a
date at which consumption is negative while capital exceeds the trapping level `k_L`. -/
def TooLowG (f : ℝ → ℝ) (β n : ℝ) (g : ℕ → ℝ) (kL k0 c : ℝ) : Prop :=
  0 < c ∧ ∃ T, (∀ j ≤ T, 0 < kG f β n g k0 c j) ∧ cG f β n g k0 c T < 0 ∧
    kL < kG f β n g k0 c T

/-- "Too high" initial consumption with spending (Ex. 1(c)): capital turns negative. -/
def TooHighG (f : ℝ → ℝ) (β n : ℝ) (g : ℕ → ℝ) (k0 c : ℝ) : Prop :=
  ∃ T, (∀ j < T, 0 < kG f β n g k0 c j) ∧ kG f β n g k0 c T < 0

/-- Too-low paths are trapped (Ex. 1(c)): from the date consumption turns negative capital
stays above `k_L` and consumption stays negative, so capital is positive at every date. -/
theorem tooLowG_capital_pos (hT : Technology f) {β n G kL k0 c : ℝ} {g : ℕ → ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hn : 0 < n) (hkL : 0 < kL) (hg : ∀ t, 0 ≤ g t ∧ g t ≤ G)
    (hm : G < f kL - n * kL) (h : TooLowG f β n g kL k0 c) (t : ℕ) :
    0 < kG f β n g k0 c t := by
  obtain ⟨-, T, hk, hc, hkT⟩ := h
  have hafter : ∀ s, kL < kG f β n g k0 c (T + s) ∧ cG f β n g k0 c (T + s) < 0 := by
    intro s
    induction s with
    | zero => exact ⟨hkT, hc⟩
    | succ s ih =>
      obtain ⟨h1, h2⟩ := ih
      have := trapG hT hβ hβ1 hn hkL (hg (T + s)) hm h1.le h2.le
      rw [show T + (s + 1) = T + s + 1 by ring, cG_succ, kG_succ]
      exact this
  rcases le_or_gt t T with h | h
  · exact hk t h
  · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h.le
    exact hkL.trans (hafter s).1

/-- Small initial consumption is too low when `k₀ ≥ k_L` (Ex. 1(c)). -/
theorem tooLowG_small (hT : Technology f) {β n G kL k0 : ℝ} {g : ℕ → ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hn : 0 < n) (hkL : 0 < kL) (hkL0 : kL ≤ k0)
    (hg : ∀ t, 0 ≤ g t ∧ g t ≤ G) (hm : G < f kL - n * kL) :
    ∃ c, TooLowG f β n g kL k0 c := by
  set m := f kL - n * kL - G
  have hm0 : 0 < m := by simp only [m]; linarith
  have h1β : 0 < n * (1 - β) := mul_pos hn (by linarith)
  set c := min (m / 2) (n * (1 - β) * kL / (2 * β))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hk0 : 0 < k0 := hkL.trans_le hkL0
  have hk1 : kL < kG f β n g k0 c 1 := by
    change kL < nextKg f n (g 0) k0 c
    unfold nextKg
    rw [lt_div_iff₀ (by linarith)]
    have := f_mono hT hkL.le hkL0
    have : c ≤ m / 2 := min_le_left _ _
    have := (hg 0).2
    simp only [m] at *
    nlinarith
  refine ⟨c, hc, 1, fun j hj => ?_, ?_, hk1⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · exact hk0
    · exact hkL.trans hk1
  · rw [cG_succ]
    apply mul_neg_of_pos_of_neg (by linarith [hT.neo.deriv_pos (hkL.trans hk1)])
    have hc2 : c ≤ n * (1 - β) * kL / (2 * β) := min_le_right _ _
    have h1 : β * c ≤ n * (1 - β) * kL / 2 := by
      rw [le_div_iff₀ (by positivity)] at hc2
      linarith
    have h2 : n * (1 - β) * kL < n * (1 - β) * kG f β n g k0 c 1 :=
      mul_lt_mul_of_pos_left hk1 h1β
    have : 0 < n * (1 - β) * kL := mul_pos h1β hkL
    change β * c - n * (1 - β) * kG f β n g k0 c 1 < 0
    linarith

/-- Too-low initial consumption is below `f(k₀) + k₀` (Ex. 1(c)). -/
theorem tooLowG_lt {β n kL k0 c : ℝ} {g : ℕ → ℝ} (hn : 0 < n) (hg : ∀ t, 0 ≤ g t)
    (h : TooLowG f β n g kL k0 c) : c < f k0 + k0 := by
  obtain ⟨hc, T, hk, hcT, -⟩ := h
  have hT0 : T ≠ 0 := by
    rintro rfl
    have : cG f β n g k0 c 0 = c := rfl
    linarith
  have h1 : 0 < kG f β n g k0 c 1 := hk 1 (by omega)
  change 0 < nextKg f n (g 0) k0 c at h1
  unfold nextKg at h1
  rw [div_pos_iff_of_pos_right (by linarith)] at h1
  linarith [hg 0]

/-- "Too low" is an open condition (Ex. 1(c)). -/
theorem tooLowG_open (hT : Technology f) {β n kL k0 c : ℝ} {g : ℕ → ℝ}
    (h : TooLowG f β n g kL k0 c) : ∀ᶠ c' in 𝓝 c, TooLowG f β n g kL k0 c' := by
  obtain ⟨hc, T, hk, hcT, hkT⟩ := h
  have hcont := orbG_continuousAt hT hk
  have hev1 : ∀ᶠ c' in 𝓝 c, 0 < c' := lt_mem_nhds hc
  have hev2 : ∀ᶠ c' in 𝓝 c, cG f β n g k0 c' T < 0 :=
    (continuous_snd.continuousAt.comp hcont).eventually (gt_mem_nhds hcT)
  have hev2' : ∀ᶠ c' in 𝓝 c, kL < kG f β n g k0 c' T :=
    (continuous_fst.continuousAt.comp hcont).eventually (lt_mem_nhds hkT)
  have hev3 : ∀ j ≤ T, ∀ᶠ c' in 𝓝 c, 0 < kG f β n g k0 c' j := by
    intro j hj
    have := orbG_continuousAt hT (T := j) (fun i hi => hk i (by omega))
    exact (continuous_fst.continuousAt.comp this).eventually (lt_mem_nhds (hk j hj))
  have hev4 : ∀ᶠ c' in 𝓝 c, ∀ j ∈ Finset.range (T + 1), 0 < kG f β n g k0 c' j :=
    (Finset.eventually_all _).mpr
      (fun j hj => hev3 j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  filter_upwards [hev1, hev2, hev2', hev4] with c' h1 h2 h2' h4
  exact ⟨h1, T, fun j hj => h4 j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)), h2, h2'⟩

/-- "Too high" is an open condition (Ex. 1(c)). -/
theorem tooHighG_open (hT : Technology f) {β n k0 c : ℝ} {g : ℕ → ℝ}
    (h : TooHighG f β n g k0 c) : ∀ᶠ c' in 𝓝 c, TooHighG f β n g k0 c' := by
  obtain ⟨T, hk, hkT⟩ := h
  rcases Nat.eq_zero_or_pos T with h0 | hpos
  · subst h0
    exact Eventually.of_forall (fun c' => ⟨0, fun j hj => absurd hj (Nat.not_lt_zero _), hkT⟩)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  have hkm : ∀ j ≤ m, 0 < kG f β n g k0 c j := fun j hj => hk j (by omega)
  have hcont := kG_succ_continuousAt hT hkm
  have hev2 : ∀ᶠ c' in 𝓝 c, kG f β n g k0 c' (m + 1) < 0 := hcont.eventually (gt_mem_nhds hkT)
  have hev3 : ∀ j ≤ m, ∀ᶠ c' in 𝓝 c, 0 < kG f β n g k0 c' j := by
    intro j hj
    have := orbG_continuousAt hT (T := j) (fun i hi => hkm i (by omega))
    exact (continuous_fst.continuousAt.comp this).eventually (lt_mem_nhds (hkm j hj))
  have hev4 : ∀ᶠ c' in 𝓝 c, ∀ j ∈ Finset.range (m + 1), 0 < kG f β n g k0 c' j :=
    (Finset.eventually_all _).mpr
      (fun j hj => hev3 j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  filter_upwards [hev2, hev4] with c' h2 h4
  exact ⟨m + 1, fun j hj => h4 j (Finset.mem_range.mpr hj), h2⟩

/-- **Ex. 1(c), existence of the equilibrium path** (by shooting): if `0 < k_L < k₀`,
`β(1 + f'(k_L)) > 1` and spending satisfies `0 ≤ g_t ≤ G ≤ Φ(k_L)` (`Φ` the steady-state
residual, i.e. the gap between the `Δk = 0` and `Δc = 0` loci at `k_L`), then some initial
consumption keeps the economy in the positive quadrant for ever. The separating value is the
supremum of the too-low initial consumptions; the safety invariant rules out the orbit
running out of consumption at low capital, which is exactly how existence fails for large
spending. -/
theorem announcement_exists (hT : Technology f) {β n G kL k0 : ℝ} {g : ℕ → ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hn : 0 < n) (hkL : 0 < kL) (hkL0 : kL < k0)
    (hdomL : 1 < β * (1 + deriv f kL)) (hg : ∀ t, 0 ≤ g t ∧ g t ≤ G)
    (hG : G ≤ residual f β n kL) : ∃ c0, PosOrbitG f β n g k0 c0 := by
  classical
  have hk0 : 0 < k0 := hkL.trans hkL0
  have h1β : 0 < n * (1 - β) := mul_pos hn (by linarith)
  have hq : 0 < qCoef f β kL := div_pos (by linarith [hT.neo.deriv_pos hkL]) (by linarith)
  have hcs0 : 0 < n * (1 - β) * kL * qCoef f β kL := mul_pos (mul_pos h1β hkL) hq
  have hm : G < f kL - n * kL := by unfold residual at hG; linarith
  have hsafe := safeG hT hβ hβ1 hn hkL hkL0.le hdomL hg hG
  set Lo := {c | TooLowG f β n g kL k0 c}
  have hne : Lo.Nonempty := tooLowG_small hT hβ hβ1 hn hkL hkL0.le hg hm
  have hbdd : BddAbove Lo :=
    ⟨f k0 + k0, fun c hc => (tooLowG_lt hn (fun t => (hg t).1) hc).le⟩
  set cs := sSup Lo
  obtain ⟨c1, hc1⟩ := hne
  have hcs : 0 < cs := lt_of_lt_of_le hc1.1 (le_csSup hbdd hc1)
  have happrox : ∀ ε > 0, ∃ c, TooLowG f β n g kL k0 c ∧ cs - ε < c ∧ c ≤ cs := by
    intro ε hε
    obtain ⟨c, hc, hlt⟩ := exists_lt_of_lt_csSup ⟨c1, hc1⟩ (by linarith : cs - ε < cs)
    exact ⟨c, hc, hlt, le_csSup hbdd hc⟩
  have hnotLo : ¬ TooLowG f β n g kL k0 cs := by
    intro h
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (tooLowG_open hT h)
    have := hball (show dist (cs + ε / 2) cs < ε by
      rw [Real.dist_eq, show cs + ε / 2 - cs = ε / 2 by ring, abs_of_pos (half_pos hε)]
      exact half_lt_self hε)
    have := le_csSup hbdd this
    linarith
  have hdisj : ∀ c, TooLowG f β n g kL k0 c → ¬ TooHighG f β n g k0 c := by
    rintro c hl ⟨T, -, hT'⟩
    linarith [tooLowG_capital_pos hT hβ hβ1 hn hkL hg hm hl T]
  have hnotHi : ¬ TooHighG f β n g k0 cs := by
    intro h
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (tooHighG_open hT h)
    obtain ⟨c, hc, hlt, hle⟩ := happrox ε hε
    have := hball (show dist c cs < ε by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    exact hdisj c hc this
  refine ⟨cs, ?_⟩
  by_contra hbad
  simp only [PosOrbitG, not_forall] at hbad
  have hex : ∃ t, ¬ (0 < kG f β n g k0 cs t ∧ 0 < cG f β n g k0 cs t) := hbad
  set t := Nat.find hex
  have ht : ¬ (0 < kG f β n g k0 cs t ∧ 0 < cG f β n g k0 cs t) := Nat.find_spec hex
  have hbefore : ∀ j < t, 0 < kG f β n g k0 cs j ∧ 0 < cG f β n g k0 cs j := fun j hj => by
    have := Nat.find_min hex hj; push Not at this; exact this
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0] at ht
    exact ht ⟨hk0, hcs⟩
  obtain ⟨m, hm'⟩ := Nat.exists_eq_succ_of_ne_zero ht0
  have hbm : ∀ j ≤ m, 0 < kG f β n g k0 cs j ∧ 0 < cG f β n g k0 cs j :=
    fun j hj => hbefore j (by omega)
  rcases lt_trichotomy (kG f β n g k0 cs t) 0 with hneg | hzero | hkpos
  · exact hnotHi ⟨t, fun j hj => (hbefore j hj).1, hneg⟩
  · -- capital hits zero exactly: nearby too-low orbits would have to jump over it
    rw [hm'] at hzero
    have hcm := (hbm m le_rfl).2
    set a0 := β * cG f β n g k0 cs m
    have ha0 : 0 < a0 := mul_pos hβ hcm
    set M := 2 * (f 1 + 1) / a0
    obtain ⟨η, hη, hηM⟩ : ∃ η, 0 < η ∧ η ≤ 1 ∧ ∀ k, 0 < k → k < η → M < deriv f k := by
      have := (hT.inada0.eventually (eventually_gt_atTop M))
      obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp this
      exact ⟨min u 1, lt_min hu one_pos, min_le_right _ _, fun k hk hku =>
        hsub ⟨hk, lt_of_lt_of_le hku (min_le_left _ _)⟩⟩
    have hηM' := hηM.2
    have hposm : ∀ j ≤ m, 0 < kG f β n g k0 cs j := fun j hj => (hbm j hj).1
    have hcontK := kG_succ_continuousAt hT hposm
    have hcontC : ContinuousAt (fun c => cG f β n g k0 c m) cs :=
      continuous_snd.continuousAt.comp (orbG_continuousAt hT hposm)
    have hevA : ∀ᶠ c in 𝓝 cs, a0 / 2 < β * cG f β n g k0 c m - n * (1 - β) *
        kG f β n g k0 c (m + 1) := by
      have hA : ContinuousAt (fun c => β * cG f β n g k0 c m - n * (1 - β) *
          kG f β n g k0 c (m + 1)) cs :=
        (continuousAt_const.mul hcontC).sub (continuousAt_const.mul hcontK)
      have hval : β * cG f β n g k0 cs m - n * (1 - β) * kG f β n g k0 cs (m + 1) = a0 := by
        rw [hzero]; ring
      exact hA.eventually (lt_mem_nhds (by simp only; rw [hval]; exact half_lt_self ha0))
    have hevK : ∀ᶠ c in 𝓝 cs, kG f β n g k0 c (m + 1) < η :=
      hcontK.eventually (gt_mem_nhds (by simp only; rw [hzero]; exact hη))
    have hevP : ∀ᶠ c in 𝓝 cs, ∀ j ∈ Finset.range (m + 1), 0 < cG f β n g k0 c j := by
      refine (Finset.eventually_all _).mpr (fun j hj => ?_)
      have hj' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have := orbG_continuousAt hT (T := j) (fun i hi => hposm i (by omega))
      exact (continuous_snd.continuousAt.comp this).eventually (lt_mem_nhds (hbm j hj').2)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp ((hevA.and hevK).and hevP)
    obtain ⟨c, hc, hlt, hle⟩ := happrox ε hε
    obtain ⟨⟨hA, hK⟩, hP⟩ := hball (show dist c cs < ε by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    obtain ⟨-, T, hkT, hcT, -⟩ := hc
    rcases le_or_gt T m with hTm | hTm
    · linarith [hP T (Finset.mem_range.mpr (by omega))]
    · have hk1 : 0 < kG f β n g k0 c (m + 1) := hkT (m + 1) (by omega)
      have hR : M < deriv f (kG f β n g k0 c (m + 1)) := hηM' _ hk1 hK
      have hc1 : 2 * (f 1 + 1) / a0 * (a0 / 2) < cG f β n g k0 c (m + 1) := by
        rw [cG_succ]
        have hM0 : 0 ≤ M := by
          have := f_nonneg hT zero_le_one; positivity
        calc 2 * (f 1 + 1) / a0 * (a0 / 2) ≤
              (1 + deriv f (kG f β n g k0 c (m + 1))) * (a0 / 2) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
          _ < _ := mul_lt_mul_of_pos_left hA (by linarith)
      have hval : 2 * (f 1 + 1) / a0 * (a0 / 2) = f 1 + 1 := by field_simp
      rw [hval] at hc1
      rcases (Nat.lt_iff_add_one_le.mp hTm).lt_or_eq with hT2 | hT1
      · have hk2 := hkT (m + 2) (by omega)
        rw [show m + 2 = m + 1 + 1 by ring, kG_succ] at hk2
        unfold nextKg at hk2
        rw [div_pos_iff_of_pos_right (by linarith)] at hk2
        have := f_mono hT hk1.le (show kG f β n g k0 c (m + 1) ≤ 1 by linarith)
        linarith [(hg (m + 1)).1]
      · rw [← hT1] at hcT
        have := f_nonneg hT zero_le_one
        linarith
  · -- capital positive, consumption nonpositive: by the safety invariant capital is at
    -- least `k_L`, so the orbit is trapped and hence too low
    have hct : cG f β n g k0 cs t ≤ 0 := by
      by_contra h; push Not at h; exact ht ⟨hkpos, h⟩
    have hkL' : kL ≤ kG f β n g k0 cs t := by
      rcases hsafe cs t hbefore hkpos with h | h
      · exact h
      · linarith
    obtain ⟨htr1, htr2⟩ := trapG hT hβ hβ1 hn hkL (hg t) hm hkL' hct
    refine hnotLo ⟨hcs, t + 1, fun j hj => ?_, ?_, ?_⟩
    · rcases hj.lt_or_eq with h | h
      · rcases (Nat.lt_succ_iff.mp h).lt_or_eq with h' | h'
        · exact (hbefore j h').1
        · rw [h']; exact hkpos
      · rw [h, kG_succ]; exact hkL.trans htr1
    · rw [cG_succ, kG_succ]; exact htr2
    · rw [kG_succ]; exact htr1

/-- **Ex. 1(c), existence from the old steady state**: starting from the no-spending steady
state `k̄` (`β(1 + f'(k̄)) > 1`, `Φ(k̄) = 0`), an equilibrium path exists for every announced
spending path with `0 ≤ g_t ≤ G ≤ Φ(k_m)` for some `k_m ∈ (0, k̄)`: the same smallness that
makes the crowded-out steady states exist (`two_steady_states_with_spending`). -/
theorem announcement_exists_steady (hT : Technology f) {β n G km kbar : ℝ} {g : ℕ → ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hn : 0 < n) (hkm : 0 < km) (hkmk : km < kbar)
    (hdom : 1 < β * (1 + deriv f kbar)) (hg : ∀ t, 0 ≤ g t ∧ g t ≤ G)
    (hG : G ≤ residual f β n km) : ∃ c0, PosOrbitG f β n g kbar c0 := by
  have hd := hT.neo.deriv_strictAnti hkm (hkm.trans hkmk) hkmk
  exact announcement_exists hT hβ hβ1 hn hkm hkmk (by nlinarith) hg hG

/-- **Ex. 1(c), existence for small spending from any `k₀ > 0`**: there is `Ḡ > 0`
(explicitly `Ḡ = Φ(k_L)` for a small `k_L`) such that every spending path with
`0 ≤ g_t ≤ Ḡ` has an equilibrium path from `k₀`. -/
theorem announcement_exists_small (hT : Technology f) {β n k0 : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hn : 0 < n) (hk0 : 0 < k0) :
    ∃ Gbar, 0 < Gbar ∧ ∀ g : ℕ → ℝ, (∀ t, 0 ≤ g t ∧ g t ≤ Gbar) →
      ∃ c0, PosOrbitG f β n g k0 c0 := by
  set M := n + 2 * (n * (1 - β)) / β + 1
  have hev1 : ∀ᶠ k in 𝓝[>] (0 : ℝ), 2 / β < deriv f k :=
    hT.inada0.eventually (eventually_gt_atTop _)
  have hev2 : ∀ᶠ k in 𝓝[>] (0 : ℝ), M < f k / k :=
    (hT.neo.avg_tendsto_atTop hT.inada0).eventually (eventually_gt_atTop _)
  have hev3 : ∀ᶠ k in 𝓝[>] (0 : ℝ), k < k0 :=
    nhdsWithin_le_nhds (gt_mem_nhds hk0)
  have hev4 : ∀ᶠ k in 𝓝[>] (0 : ℝ), 0 < k := self_mem_nhdsWithin
  obtain ⟨kL, h1, h2, h3, h4⟩ := (hev1.and (hev2.and (hev3.and hev4))).exists
  have hR : 2 ≤ β * (1 + deriv f kL) := by
    have := mul_lt_mul_of_pos_left h1 hβ
    rw [mul_div_cancel₀ _ hβ.ne'] at this
    nlinarith
  have hq : qCoef f β kL ≤ 2 / β := by
    unfold qCoef
    rw [div_le_div_iff₀ (by linarith) hβ]
    nlinarith
  have hres : kL < residual f β n kL := by
    unfold residual
    rw [lt_div_iff₀ h4] at h2
    have h1β : 0 ≤ n * (1 - β) := (mul_pos hn (by linarith)).le
    have := mul_le_mul_of_nonneg_left hq (mul_nonneg h1β h4.le)
    have e : n * (1 - β) * kL * (2 / β) = 2 * (n * (1 - β)) / β * kL := by ring
    simp only [M] at h2
    nlinarith
  refine ⟨residual f β n kL, h4.trans hres, fun g hg => ?_⟩
  exact announcement_exists hT hβ hβ1 hn h4 h3 (by linarith) hg le_rfl

/-- **A Perron weight for the gap dynamics** (used for Ex. 1(c) uniqueness): for `a > 1`,
`0 < β < 1`, `n > 0` there is `x > 0` with `(1 + x) a > 1 + n` and
`x (1 + n - a(n + β)) < a n (1 - β)`. The two conditions say that the linear lower bound
`(Δk, Δc) ↦ ((aΔk + Δc)/(1+n), a(βΔc + n(1-β)Δk'))` of the gap map expands the weight
`Δk + θΔc` (`θ = x/(a n (1-β))`) by a factor above one; the key identity is
`a² n(1-β) - (1+n-a)(1+n-a(n+β)) = (1+n)(a-1)(1+n-aβ)`. -/
theorem perron_weight {a β n : ℝ} (ha : 1 < a) (hβ : 0 < β) (hβ1 : β < 1) (hn : 0 < n) :
    ∃ x, 0 < x ∧ 1 + n < (1 + x) * a ∧ x * (1 + n - a * (n + β)) < a * (n * (1 - β)) := by
  have hν : 0 < a * (n * (1 - β)) := by
    have : 0 < 1 - β := by linarith
    positivity
  set D := 1 + n - a * (n + β)
  by_cases hD : D ≤ 0
  · refine ⟨(1 + n) / a, by positivity, ?_, ?_⟩
    · rw [add_mul, div_mul_cancel₀ _ (by linarith)]; linarith
    · have : (1 + n) / a * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hD
      linarith
  push Not at hD
  set x0 := (1 + n - a) / a
  set x1 := a * (n * (1 - β)) / D
  have hx1 : 0 < x1 := div_pos hν hD
  have hid : a * (a * (n * (1 - β))) - (1 + n - a) * D =
      (1 + n) * (a - 1) * (1 + n - a * β) := by
    simp only [D]; ring
  have haβ : 0 < 1 + n - a * β := by
    have : a * β < a * (n + β) := by nlinarith
    simp only [D] at hD; linarith
  have hx01 : x0 < x1 := by
    simp only [x0, x1]
    rw [div_lt_div_iff₀ (by linarith) hD]
    have : 0 < (1 + n) * (a - 1) * (1 + n - a * β) := by
      have : 0 < a - 1 := by linarith
      positivity
    nlinarith
  refine ⟨(max x0 0 + x1) / 2, by
    have := le_max_right x0 0; linarith, ?_, ?_⟩
  · have h1 : x0 < (max x0 0 + x1) / 2 := by
      have := le_max_left x0 0; have := max_lt hx01 hx1; linarith
    have h2 : (1 + x0) * a = 1 + n := by
      simp only [x0]; field_simp; ring
    nlinarith
  · have h1 : (max x0 0 + x1) / 2 < x1 := by
      have := max_lt hx01 hx1; linarith
    have h2 : x1 * D = a * (n * (1 - β)) := by
      simp only [x1]; field_simp
    nlinarith

/-- **Ex. 1(c), uniqueness without any wage condition**: for any nonnegative spending path,
two equilibrium paths from the same `k₀` coincide. Proof: the higher-consumption path has
lower capital at every date, and the gaps `Δk_t, Δc_t ≥ 0` satisfy
`(1+n)Δk_{t+1} ≥ aΔk_t + Δc_t`, `Δc_{t+1} ≥ a(βΔc_t + n(1-β)Δk_{t+1})` with
`a = 1 + f'(K) > 1` (`K` a capital bound); a Perron weight `φ = Δk + θΔc` then grows
geometrically from `φ₀ = θΔc₀ > 0`, contradicting boundedness of both paths. This removes the
`g_t ≤ w_t` assumption of `announcement_unique` (and gives a second proof of
`posOrbit_unique` for `g = 0` that does not use the human-wealth representation). -/
theorem announcement_unique_general (hT : Technology f) {β n k0 c0 c0' : ℝ} {g : ℕ → ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hn : 0 < n) (hg : ∀ t, 0 ≤ g t)
    (hp : PosOrbitG f β n g k0 c0) (hp' : PosOrbitG f β n g k0 c0') : c0 = c0' := by
  wlog hlt : c0 < c0' generalizing c0 c0'
  · rcases lt_trichotomy c0 c0' with h | h | h
    · exact absurd h hlt
    · exact h
    · exact (this hp' hp h).symm
  exfalso
  -- the higher-consumption path has lower capital at every date
  have hcmp : ∀ t, (orbG f β n g k0 c0' t).1 ≤ (orbG f β n g k0 c0 t).1 ∧
      (orbG f β n g k0 c0 t).2 ≤ (orbG f β n g k0 c0' t).2 := by
    intro t
    induction t with
    | zero => exact ⟨le_rfl, hlt.le⟩
    | succ t ih =>
      obtain ⟨hk', hc'⟩ := ih
      have hpa := (hp' t).1
      have hpa1 := (hp' (t + 1)).1
      have hpb1 := (hp (t + 1)).1
      have hcb1 := (hp (t + 1)).2
      simp only [orbG, stepG] at hpa1 hpb1 hcb1 ⊢
      have hK : nextKg f n (g t) (orbG f β n g k0 c0' t).1 (orbG f β n g k0 c0' t).2 ≤
          nextKg f n (g t) (orbG f β n g k0 c0 t).1 (orbG f β n g k0 c0 t).2 := by
        unfold nextKg
        apply div_le_div_of_nonneg_right _ (by linarith)
        have := f_mono hT hpa.le hk'
        linarith
      refine ⟨hK, ?_⟩
      set Ka := nextKg f n (g t) (orbG f β n g k0 c0' t).1 (orbG f β n g k0 c0' t).2
      set Kb := nextKg f n (g t) (orbG f β n g k0 c0 t).1 (orbG f β n g k0 c0 t).2
      have hR : deriv f Kb ≤ deriv f Ka := hT.neo.deriv_strictAnti.antitoneOn hpa1 hpb1 hK
      have hRb : 0 < 1 + deriv f Kb := by linarith [hT.neo.deriv_pos hpb1]
      have hAb : 0 < β * (orbG f β n g k0 c0 t).2 - n * (1 - β) * Kb := by
        by_contra h; push Not at h
        have := mul_nonpos_of_nonneg_of_nonpos hRb.le h
        linarith
      have hA : β * (orbG f β n g k0 c0 t).2 - n * (1 - β) * Kb ≤
          β * (orbG f β n g k0 c0' t).2 - n * (1 - β) * Ka := by
        have := mul_le_mul_of_nonneg_left hc' hβ.le
        have := mul_le_mul_of_nonneg_left hK (mul_pos hn (by linarith : (0 : ℝ) < 1 - β)).le
        linarith
      calc (1 + deriv f Kb) * (β * (orbG f β n g k0 c0 t).2 - n * (1 - β) * Kb)
          ≤ (1 + deriv f Ka) * (β * (orbG f β n g k0 c0 t).2 - n * (1 - β) * Kb) :=
            mul_le_mul_of_nonneg_right (by linarith) hAb.le
        _ ≤ (1 + deriv f Ka) * (β * (orbG f β n g k0 c0' t).2 - n * (1 - β) * Ka) :=
            mul_le_mul_of_nonneg_left hA (by linarith)
  obtain ⟨K, hK0, hK⟩ := posOrbitG_bounded hT hn hg hp
  set a := 1 + deriv f K
  have ha1 : 1 < a := by simp only [a]; linarith [hT.neo.deriv_pos hK0]
  set ν := n * (1 - β)
  have hν : 0 < ν := mul_pos hn (by linarith)
  set ka : ℕ → ℝ := fun t => (orbG f β n g k0 c0' t).1
  set kb : ℕ → ℝ := fun t => (orbG f β n g k0 c0 t).1
  set ca : ℕ → ℝ := fun t => (orbG f β n g k0 c0' t).2
  set cb : ℕ → ℝ := fun t => (orbG f β n g k0 c0 t).2
  have hka : ∀ t, 0 < ka t := fun t => (hp' t).1
  have hkb : ∀ t, 0 < kb t := fun t => (hp t).1
  have hca : ∀ t, 0 < ca t := fun t => (hp' t).2
  have hcb : ∀ t, 0 < cb t := fun t => (hp t).2
  have hdk : ∀ t, 0 ≤ kb t - ka t := fun t => by linarith [(hcmp t).1]
  have hdc : ∀ t, 0 ≤ ca t - cb t := fun t => by linarith [(hcmp t).2]
  have eka : ∀ t, ka (t + 1) * (1 + n) = f (ka t) + ka t - ca t - g t := fun t => by
    change nextKg f n (g t) (ka t) (ca t) * (1 + n) = _
    unfold nextKg; field_simp
  have ekb : ∀ t, kb (t + 1) * (1 + n) = f (kb t) + kb t - cb t - g t := fun t => by
    change nextKg f n (g t) (kb t) (cb t) * (1 + n) = _
    unfold nextKg; field_simp
  have eca : ∀ t, ca (t + 1) = (1 + deriv f (ka (t + 1))) *
      (β * ca t - ν * ka (t + 1)) := fun t => rfl
  have ecb : ∀ t, cb (t + 1) = (1 + deriv f (kb (t + 1))) *
      (β * cb t - ν * kb (t + 1)) := fun t => rfl
  -- the two gap inequalities
  have hI1 : ∀ t, a * (kb t - ka t) + (ca t - cb t) ≤ (1 + n) * (kb (t + 1) - ka (t + 1)) := by
    intro t
    have htan := hT.neo.tangent_le (hkb t) (hka t).le
    have hd : deriv f K ≤ deriv f (kb t) :=
      hT.neo.deriv_strictAnti.antitoneOn (hkb t) hK0 (hK t)
    have := mul_le_mul_of_nonneg_right hd (hdk t)
    have e1 := eka t
    have e2 := ekb t
    simp only [a]
    nlinarith
  have hI2 : ∀ t, a * (β * (ca t - cb t) + ν * (kb (t + 1) - ka (t + 1))) ≤
      ca (t + 1) - cb (t + 1) := by
    intro t
    have hRb : a ≤ 1 + deriv f (kb (t + 1)) := by
      have := hT.neo.deriv_strictAnti.antitoneOn (hkb (t + 1)) hK0 (hK (t + 1)); simp only [a]
      linarith
    have hRab : 1 + deriv f (kb (t + 1)) ≤ 1 + deriv f (ka (t + 1)) := by
      have := hT.neo.deriv_strictAnti.antitoneOn (hka (t + 1)) (hkb (t + 1))
        (by linarith [hdk (t + 1)])
      linarith
    have hAb : 0 < β * cb t - ν * kb (t + 1) := by
      by_contra h; push Not at h
      have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ 1 + deriv f (kb (t + 1))) h
      linarith [hcb (t + 1), ecb t]
    have hgap : 0 ≤ β * (ca t - cb t) + ν * (kb (t + 1) - ka (t + 1)) := by
      have := mul_nonneg hβ.le (hdc t); have := mul_nonneg hν.le (hdk (t + 1)); linarith
    rw [eca, ecb]
    have hAa : β * ca t - ν * ka (t + 1) =
        (β * cb t - ν * kb (t + 1)) + (β * (ca t - cb t) + ν * (kb (t + 1) - ka (t + 1))) := by
      ring
    rw [hAa]
    set Ab := β * cb t - ν * kb (t + 1)
    set Gp := β * (ca t - cb t) + ν * (kb (t + 1) - ka (t + 1))
    have h1 : (1 + deriv f (kb (t + 1))) * (Ab + Gp) ≤ (1 + deriv f (ka (t + 1))) * (Ab + Gp) :=
      mul_le_mul_of_nonneg_right hRab (by linarith)
    have h2 : a * Gp ≤ (1 + deriv f (kb (t + 1))) * Gp := mul_le_mul_of_nonneg_right hRb hgap
    nlinarith
  -- the Perron weight
  obtain ⟨x, hx, hC1, hC2⟩ := perron_weight ha1 hβ hβ1 hn
  set θ := x / (a * ν)
  have hθ : 0 < θ := div_pos hx (by positivity)
  have hθx : θ * a * ν = x := by simp only [θ]; field_simp
  set P := (1 + x) * a / (1 + n)
  set Q := (1 + x) / (1 + n) + θ * a * β
  have hP : 1 < P := by simp only [P]; rw [lt_div_iff₀ (by linarith)]; linarith
  have hQ : θ < Q := by
    simp only [Q]
    rw [← sub_pos]
    have e : (1 + x) / (1 + n) + θ * a * β - θ =
        (a * ν - x * (1 + n - a * (n + β))) / (a * ν * (1 + n)) := by
      have h1 : (1 : ℝ) - β ≠ 0 := by linarith
      have h2 : a ≠ 0 := by linarith
      have h3 : n ≠ 0 := hn.ne'
      have h4 : 1 + n ≠ 0 := by linarith
      simp only [θ, ν]; field_simp; ring
    rw [e]
    exact div_pos (by simp only [ν] at *; linarith) (by positivity)
  set lam := min P (Q / θ)
  have hlam : 1 < lam := lt_min hP (by rw [lt_div_iff₀ hθ]; linarith)
  set φ : ℕ → ℝ := fun t => (kb t - ka t) + θ * (ca t - cb t)
  have hgrow : ∀ t, lam * φ t ≤ φ (t + 1) := by
    intro t
    have hl1 : lam ≤ P := min_le_left _ _
    have hl2 : lam * θ ≤ Q := by
      have := min_le_right P (Q / θ); rwa [le_div_iff₀ hθ] at this
    have s1 : lam * φ t ≤ P * (kb t - ka t) + Q * (ca t - cb t) := by
      simp only [φ]
      have := mul_le_mul_of_nonneg_right hl1 (hdk t)
      have := mul_le_mul_of_nonneg_right hl2 (hdc t)
      nlinarith
    have s2 : P * (kb t - ka t) + Q * (ca t - cb t) ≤
        (1 + x) * (kb (t + 1) - ka (t + 1)) + θ * a * β * (ca t - cb t) := by
      have h1 := hI1 t
      have e : P * (kb t - ka t) + Q * (ca t - cb t) =
          (1 + x) * (a * (kb t - ka t) + (ca t - cb t)) / (1 + n) +
            θ * a * β * (ca t - cb t) := by simp only [P, Q]; ring
      rw [e]
      have : (1 + x) * (a * (kb t - ka t) + (ca t - cb t)) / (1 + n) ≤
          (1 + x) * (kb (t + 1) - ka (t + 1)) := by
        rw [div_le_iff₀ (by linarith)]
        have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + x)
        linarith
      linarith
    have s3 : (1 + x) * (kb (t + 1) - ka (t + 1)) + θ * a * β * (ca t - cb t) ≤ φ (t + 1) := by
      have h2 := mul_le_mul_of_nonneg_left (hI2 t) hθ.le
      simp only [φ]
      rw [← hθx]
      nlinarith
    linarith
  have hφ0 : 0 < φ 0 := by
    simp only [φ, ka, kb, ca, cb]
    change 0 < (k0 - k0) + θ * (c0' - c0)
    have := mul_pos hθ (sub_pos.mpr hlt); linarith
  have hpow : ∀ t, lam ^ t * φ 0 ≤ φ t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ]
      have := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ lam)
      nlinarith [hgrow t]
  -- boundedness
  set B := K + θ * (f K + K)
  have hbound : ∀ t, φ t ≤ B := by
    intro t
    have hkat : ka t ≤ K := (hcmp t).1.trans (hK t)
    have hcat : ca t < f (ka t) + ka t := by
      have := hka (t + 1)
      have e := eka t
      nlinarith [hg t]
    have := f_mono hT (hka t).le hkat
    have h1 : kb t - ka t ≤ K := by linarith [hka t, hK t]
    have h2 : ca t - cb t ≤ f K + K := by linarith [hcb t]
    simp only [φ, B]
    nlinarith
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (B / φ 0) hlam
  have := hbound N
  have := hpow N
  rw [div_lt_iff₀ hφ0] at hN
  linarith

/-- **Ex. 1(c), capital rises monotonically until spending starts**: on any equilibrium path
from the old steady state `(k̄, c̄)` with `c₀ < c̄` (which `announcement_impact` guarantees) and
`g_t = 0` for `t < T`, capital rises strictly and consumption falls strictly at every date
before `T`: `k_t < k_{t+1}` and `c_{t+1} < c_t` for `t < T`. (The base step uses
`β(1 + f'(k̄)) > 1`; the rest is the monotonicity of (32)–(33) in the order `k ↑, c ↓`.) -/
theorem announcement_monotone (hT : Technology f) {β n kbar cbar c0 : ℝ} {g : ℕ → ℝ} {T : ℕ}
    (hβ : 0 < β) (hβ1 : β < 1) (hn : 0 < n) (hkb : 0 < kbar)
    (hdom : 1 < β * (1 + deriv f kbar)) (hss1 : cbar = f kbar - n * kbar)
    (hss2 : cbar = (1 + deriv f kbar) * (β * cbar - n * (1 - β) * kbar))
    (hgT : ∀ t < T, g t = 0) (hp : PosOrbitG f β n g kbar c0) (himp : c0 < cbar) :
    ∀ t < T, kG f β n g kbar c0 t < kG f β n g kbar c0 (t + 1) ∧
      cG f β n g kbar c0 (t + 1) < cG f β n g kbar c0 t := by
  set ν := n * (1 - β)
  have hν : 0 < ν := mul_pos hn (by linarith)
  have hk : ∀ t, 0 < kG f β n g kbar c0 t := fun t => (hp t).1
  have hc : ∀ t, 0 < cG f β n g kbar c0 t := fun t => (hp t).2
  have ek : ∀ t < T, kG f β n g kbar c0 (t + 1) * (1 + n) =
      f (kG f β n g kbar c0 t) + kG f β n g kbar c0 t - cG f β n g kbar c0 t := by
    intro t ht
    rw [kG_succ, hgT t ht]; unfold nextKg; field_simp; ring
  intro t
  induction t with
  | zero =>
    intro hT0
    have hk1 : kbar < kG f β n g kbar c0 1 := by
      have e := ek 0 hT0
      have e0 : kG f β n g kbar c0 0 = kbar := rfl
      have e1 : cG f β n g kbar c0 0 = c0 := rfl
      rw [e0, e1] at e
      nlinarith
    refine ⟨hk1, ?_⟩
    rw [cG_succ]
    have e1 : cG f β n g kbar c0 0 = c0 := rfl
    rw [e1]
    set R1 := 1 + deriv f (kG f β n g kbar c0 1)
    have hR1 : R1 ≤ 1 + deriv f kbar := by
      have := hT.neo.deriv_strictAnti.antitoneOn hkb (hk 1) hk1.le; simp only [R1]; linarith
    have hR1p : 0 < R1 := by simp only [R1]; linarith [hT.neo.deriv_pos (hk 1)]
    by_cases hb : β * c0 - n * (1 - β) * kG f β n g kbar c0 1 ≤ 0
    · have := mul_nonpos_of_nonneg_of_nonpos hR1p.le hb
      linarith [hc 0]
    push Not at hb
    have hb' : β * c0 - n * (1 - β) * kG f β n g kbar c0 1 ≤ β * c0 - n * (1 - β) * kbar := by
      have := mul_le_mul_of_nonneg_left hk1.le hν.le; simp only [ν] at this; linarith
    have hRb : 0 < 1 + deriv f kbar := by linarith [hT.neo.deriv_pos hkb]
    calc R1 * (β * c0 - n * (1 - β) * kG f β n g kbar c0 1)
        ≤ (1 + deriv f kbar) * (β * c0 - n * (1 - β) * kG f β n g kbar c0 1) :=
          mul_le_mul_of_nonneg_right hR1 hb.le
      _ ≤ (1 + deriv f kbar) * (β * c0 - n * (1 - β) * kbar) :=
          mul_le_mul_of_nonneg_left hb' hRb.le
      _ < c0 := by nlinarith
  | succ t ih =>
    intro ht
    obtain ⟨hk1, hc1⟩ := ih (by omega)
    have hk2 : kG f β n g kbar c0 (t + 1) < kG f β n g kbar c0 (t + 1 + 1) := by
      have e1 := ek t (by omega)
      have e2 := ek (t + 1) ht
      have hf := f_mono hT (hk t).le hk1.le
      nlinarith
    refine ⟨hk2, ?_⟩
    set R1 := 1 + deriv f (kG f β n g kbar c0 (t + 1))
    set R2 := 1 + deriv f (kG f β n g kbar c0 (t + 1 + 1))
    have hR : R2 ≤ R1 := by
      have := hT.neo.deriv_strictAnti.antitoneOn (hk (t + 1)) (hk (t + 1 + 1)) hk2.le
      simp only [R1, R2]; linarith
    have hR1p : 0 < R1 := by simp only [R1]; linarith [hT.neo.deriv_pos (hk (t + 1))]
    have hR2p : 0 < R2 := by simp only [R2]; linarith [hT.neo.deriv_pos (hk (t + 1 + 1))]
    set b1 := β * cG f β n g kbar c0 t - n * (1 - β) * kG f β n g kbar c0 (t + 1)
    set b2 := β * cG f β n g kbar c0 (t + 1) - n * (1 - β) * kG f β n g kbar c0 (t + 1 + 1)
    have hb12 : b2 < b1 := by
      have := mul_lt_mul_of_pos_left hc1 hβ
      have := mul_lt_mul_of_pos_left hk2 hν
      simp only [b1, b2, ν] at *
      linarith
    have hc1e : cG f β n g kbar c0 (t + 1) = R1 * b1 := cG_succ f β n g kbar c0 t
    have hb1 : 0 < b1 := by
      by_contra h; push Not at h
      have := mul_nonpos_of_nonneg_of_nonpos hR1p.le h
      linarith [hc (t + 1)]
    have e2 : cG f β n g kbar c0 (t + 1 + 1) = R2 * b2 := cG_succ f β n g kbar c0 (t + 1)
    rw [e2, hc1e]
    by_cases hb2 : b2 ≤ 0
    · have := mul_nonpos_of_nonneg_of_nonpos hR2p.le hb2
      have := mul_pos hR1p hb1
      linarith
    push Not at hb2
    calc R2 * b2 ≤ R1 * b2 := mul_le_mul_of_nonneg_right hR hb2.le
      _ < R1 * b1 := mul_lt_mul_of_pos_left hb12 hR1p

/-- **Ex. 1(c), the general-equilibrium path** (O&R Exercise 1(c), p. 512): from the
no-spending steady state `(k̄, c̄)`, for any announced spending path with `0 ≤ g_t ≤ G`, `g`
positive at some date, `g_t = 0` before `T`, and `G ≤ Φ(k_m)` for some `k_m ∈ (0, k̄)`,
there is exactly one equilibrium path; on it consumption falls on impact, capital rises
strictly and consumption falls strictly until `T`, and capital stays above `k̄` up to `T`. -/
theorem announcement_equilibrium (hT : Technology f) {β n G km kbar cbar : ℝ} {g : ℕ → ℝ}
    {T : ℕ} (hβ : 0 < β) (hβ1 : β < 1) (hn : 0 < n) (hkm : 0 < km) (hkmk : km < kbar)
    (hcb : 0 < cbar) (hdom : 1 < β * (1 + deriv f kbar)) (hss1 : cbar = f kbar - n * kbar)
    (hss2 : cbar = (1 + deriv f kbar) * (β * cbar - n * (1 - β) * kbar))
    (hg : ∀ t, 0 ≤ g t ∧ g t ≤ G) (hgpos : ∃ t, 0 < g t) (hgT : ∀ t < T, g t = 0)
    (hG : G ≤ residual f β n km) :
    ∃! c0, PosOrbitG f β n g kbar c0 ∧ c0 < cbar ∧
      (∀ t < T, kG f β n g kbar c0 t < kG f β n g kbar c0 (t + 1) ∧
        cG f β n g kbar c0 (t + 1) < cG f β n g kbar c0 t) ∧
      ∀ t ≤ T, kbar ≤ kG f β n g kbar c0 t := by
  have hkb : 0 < kbar := hkm.trans hkmk
  obtain ⟨c0, hp⟩ := announcement_exists_steady hT hβ hβ1 hn hkm hkmk hdom hg hG
  have himp := announcement_impact hT hβ hβ1 hn hkb hcb hss1 hss2 hg hgpos hp
  refine ⟨c0, ⟨hp, himp, announcement_monotone hT hβ hβ1 hn hkb hdom hss1 hss2 hgT hp himp,
    fun t ht => ((announcement_anticipation hT hβ hβ1 hn hkb hss1 hss2 hgT hp himp).1 t ht).1⟩,
    fun c hc => announcement_unique_general hT hβ hβ1 hn (fun t => (hg t).1) hc.1 hp⟩

end ObstfeldRogoff.GlobalGrowth.OLGGrowth
