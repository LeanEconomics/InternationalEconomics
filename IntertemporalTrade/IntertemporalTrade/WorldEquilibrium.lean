/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalTrade.AutarkyGains
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The two-country world equilibrium

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§1.3, pp. 23–38, and Exercises 2 and 5. Two endowment economies, Home and
Foreign, trade date-1 for date-2 output at a common world rate `r`.

* **Walras's law** (p. 23): if the date-1 market clears, so does the date-2 market.
* **The world rate lies strictly between the two autarky rates** (p. 23), and the
  country with the lower autarky rate lends. The book shows this in Figure 1.5
  assuming upward-sloping saving curves; here it follows from the saving-sign
  lemma with no assumption on the slope of saving.
* **Existence** of an equilibrium. Optimal consumption is continuous in `r`
  (`continuousAt_optimal_c1`), and world excess demand changes sign between the
  two autarky rates, so the intermediate value theorem applies.
* **The first welfare theorem** (p. 33): the equilibrium allocation is Pareto optimal.
* **Log utility** (Exercises 2 and 5): the closed-form world rate is the mediant
  of the two autarky gross rates, the saving function, the welfare derivative
  `dU/dr = β(r − rA)/[(1 + r)((1 + r) + β(1 + rA))]`, and the comparative statics
  of the world rate in the four endowments.
* **Blanchard–Summers** (pp. 36–38): with Cobb–Douglas technology the saving curve
  shifts up by more than the investment curve, `(1 + r)/(1 + α/r) > r ⇔ α < 1`.

Uniqueness of equilibrium is not claimed: the book notes on p. 30 that it can fail.
-/

namespace ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium

open Set Filter Topology Consumer

/-- An equilibrium of the two-country endowment world at rate `r` (O&R (1.19), p. 23): both
countries choose optimally and the date-1 goods market clears. -/
def IsEquilibrium (h hs : Household) (r c1 c2 s1 s2 : ℝ) : Prop :=
  h.IsOptimal r c1 c2 ∧ hs.IsOptimal r s1 s2 ∧ c1 + s1 = h.Y1 + hs.Y1

/-- **Walras's law** (O&R p. 23): in equilibrium the date-2 market clears too. -/
theorem walras_law {h hs : Household} {r c1 c2 s1 s2 : ℝ}
    (he : IsEquilibrium h hs r c1 c2 s1 s2) : c2 + s2 = h.Y2 + hs.Y2 := by
  obtain ⟨ho, hos, hc⟩ := he
  rw [h.optimal_binds ho, hs.optimal_binds hos]
  linear_combination (1 + r) * (-hc)

/-- **The world rate lies strictly between the autarky rates** (O&R p. 23, Figure 1.5). -/
theorem rate_between_autarky {h hs : Household} {u' us' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hus : ∀ c, 0 < c → HasDerivAt hs.u (us' c) c) (hposs : ∀ c, 0 < c → 0 < us' c)
    {rA rAs r c1 c2 s1 s2 : ℝ} (hA : h.IsAutarkyRate rA) (hAs : hs.IsAutarkyRate rAs)
    (hlt : rA < rAs) (he : IsEquilibrium h hs r c1 c2 s1 s2) : rA < r ∧ r < rAs := by
  obtain ⟨ho, hos, hc⟩ := he
  constructor
  · by_contra hle
    push Not at hle
    have h1 : h.Y1 ≤ c1 := by
      rcases hle.lt_or_eq with hl | rfl
      · exact (h.saving_neg_of_lt_autarky hu hpos hA hl ho).le
      · exact (h.optimal_at_autarky hA ho).1.ge
    have h2 := hs.saving_neg_of_lt_autarky hus hposs hAs (hle.trans_lt hlt) hos
    linarith
  · by_contra hle
    push Not at hle
    have h1 : s1 ≤ hs.Y1 := by
      rcases hle.lt_or_eq with hl | rfl
      · exact (hs.saving_pos_of_autarky_lt hus hposs hAs hl hos).le
      · exact (hs.optimal_at_autarky hAs hos).1.le
    have h2 := h.saving_pos_of_autarky_lt hu hpos hA (hlt.trans_le hle) ho
    linarith

/-- **Pattern of trade** (O&R pp. 23–24): the country with the lower autarky rate lends on
date 1 and the other borrows. -/
theorem trade_pattern {h hs : Household} {u' us' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hus : ∀ c, 0 < c → HasDerivAt hs.u (us' c) c) (hposs : ∀ c, 0 < c → 0 < us' c)
    {rA rAs r c1 c2 s1 s2 : ℝ} (hA : h.IsAutarkyRate rA) (hAs : hs.IsAutarkyRate rAs)
    (hlt : rA < rAs) (he : IsEquilibrium h hs r c1 c2 s1 s2) : c1 < h.Y1 ∧ hs.Y1 < s1 := by
  obtain ⟨h1, h2⟩ := rate_between_autarky hu hpos hus hposs hA hAs hlt he
  exact ⟨h.saving_pos_of_autarky_lt hu hpos hA h1 he.1,
    hs.saving_neg_of_lt_autarky hus hposs hAs h2 he.2.1⟩

/-- **Optimal consumption is continuous in the world rate.** If `c₁(r), c₂(r)` is optimal for
all `r` near `r₀ > −1` and `u'` is continuous, then `c₁` is continuous at `r₀`. -/
theorem continuousAt_optimal_c1 (h : Household) {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hcont : ContinuousOn u' (Ioi 0))
    {c1 c2 : ℝ → ℝ} {r0 : ℝ} (hr0 : 0 < 1 + r0)
    (hopt : ∀ᶠ r in 𝓝 r0, h.IsOptimal r (c1 r) (c2 r)) : ContinuousAt c1 r0 := by
  -- u' is strictly decreasing
  have anti : ∀ x y, 0 < x → x < y → u' y < u' x := fun x y hx hxy =>
    deriv_lt_of_strictConcave h.concave (mem_Ioi.2 hx) (mem_Ioi.2 (hx.trans hxy)) hxy
      (hu x hx) (hu y (hx.trans hxy))
  have anti' : ∀ x y, 0 < x → x ≤ y → u' y ≤ u' x := fun x y hx hxy => by
    rcases hxy.lt_or_eq with hl | rfl
    · exact (anti x y hx hl).le
    · exact le_rfl
  set g : ℝ → ℝ → ℝ := fun r t => h.Y2 + (1 + r) * (h.Y1 - t) with hg
  set ψ : ℝ → ℝ → ℝ := fun r t => u' t - (1 + r) * h.β * u' (g r t) with hψ
  -- ψ r t is continuous in r wherever g r₀ t > 0
  have hψcont : ∀ t, 0 < g r0 t → ContinuousAt (fun r => ψ r t) r0 := by
    intro t ht
    have hgc : ContinuousAt (fun r => g r t) r0 := by simp only [hg]; fun_prop
    have hu'c : ContinuousAt u' (g r0 t) := hcont.continuousAt (Ioi_mem_nhds ht)
    exact continuousAt_const.sub (((continuousAt_const.add continuousAt_id).mul
      continuousAt_const).mul (hu'c.comp (f := fun r => g r t) hgc))
  have hgcont : ∀ t, ContinuousAt (fun r => g r t) r0 := fun t => by simp only [hg]; fun_prop
  have hev1 : ∀ᶠ r in 𝓝 r0, 0 < 1 + r :=
    (continuousAt_const.add continuousAt_id).eventually (lt_mem_nhds hr0)
  have ho0 : h.IsOptimal r0 (c1 r0) (c2 r0) := hopt.self_of_nhds
  have ha := ho0.1.1
  have hb := ho0.1.2.1
  have hbind0 := h.optimal_binds ho0
  have heul0 := h.euler_of_optimal hu ho0
  -- the Euler residual is zero at every nearby optimum
  have euler_at : ∀ r x y, h.IsOptimal r x y → ψ r x = 0 := fun r x y ho => by
    have e := h.euler_of_optimal hu ho
    have b := h.optimal_binds ho
    simp only [hψ, hg, ← b]
    linarith
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · -- lower bound
    set t := max l (c1 r0 / 2) with ht
    have ht0 : 0 < t := lt_max_of_lt_right (by linarith)
    have hta : t < c1 r0 := max_lt hl (by linarith)
    have hgt : c2 r0 < g r0 t := by simp only [hg]; rw [hbind0]; nlinarith
    have hψt : 0 < ψ r0 t := by
      have h1 := anti _ _ ht0 hta
      have h2 := anti _ _ hb hgt
      simp only [hψ]
      have : (1 + r0) * h.β * u' (g r0 t) < (1 + r0) * h.β * u' (c2 r0) :=
        mul_lt_mul_of_pos_left h2 (mul_pos hr0 h.β_pos)
      linarith
    have hevψ : ∀ᶠ r in 𝓝 r0, 0 < ψ r t :=
      (hψcont t (hb.trans hgt)).eventually (lt_mem_nhds hψt)
    have hevg : ∀ᶠ r in 𝓝 r0, 0 < g r t := (hgcont t).eventually (lt_mem_nhds (hb.trans hgt))
    filter_upwards [hopt, hevψ, hevg, hev1] with r hor hψr hgr hr1
    refine lt_of_le_of_lt (le_max_left l (c1 r0 / 2)) ?_
    by_contra hle
    push Not at hle
    have hx := hor.1.1
    have hbr := h.optimal_binds hor
    have hy : g r t ≤ c2 r := by simp only [hg]; rw [hbr]; nlinarith
    have h1 := anti' _ _ hx hle
    have h2 := anti' _ _ hgr hy
    have e := euler_at r _ _ hor
    have hgc : g r (c1 r) = c2 r := by simp only [hg]; rw [hbr]
    simp only [hψ] at e hψr
    rw [hgc] at e
    try rw [← ht] at h1
    have : (1 + r) * h.β * u' (c2 r) ≤ (1 + r) * h.β * u' (g r t) :=
      mul_le_mul_of_nonneg_left h2 (mul_pos hr1 h.β_pos).le
    linarith
  · -- upper bound
    set T := c1 r0 + c2 r0 / (1 + r0) with hT
    have haT : c1 r0 < T := by
      have : 0 < c2 r0 / (1 + r0) := div_pos hb hr0
      linarith
    set t := min m ((c1 r0 + T) / 2) with ht
    have hat : c1 r0 < t := lt_min hm (by linarith)
    have htT : t < T := min_lt_of_right_lt (by linarith)
    have hg0 : 0 < g r0 t := by
      simp only [hg]
      have e : c2 r0 = (1 + r0) * (T - c1 r0) := by rw [hT]; field_simp; ring
      rw [hbind0] at e
      nlinarith
    have hlt : g r0 t < c2 r0 := by simp only [hg]; rw [hbind0]; nlinarith
    have hψt : ψ r0 t < 0 := by
      have h1 := anti _ _ ha hat
      have h2 := anti _ _ hg0 hlt
      simp only [hψ]
      have : (1 + r0) * h.β * u' (c2 r0) < (1 + r0) * h.β * u' (g r0 t) :=
        mul_lt_mul_of_pos_left h2 (mul_pos hr0 h.β_pos)
      linarith
    have hevψ : ∀ᶠ r in 𝓝 r0, ψ r t < 0 := (hψcont t hg0).eventually (gt_mem_nhds hψt)
    have hevg : ∀ᶠ r in 𝓝 r0, 0 < g r t := (hgcont t).eventually (lt_mem_nhds hg0)
    filter_upwards [hopt, hevψ, hevg, hev1] with r hor hψr hgr hr1
    refine lt_of_lt_of_le ?_ (min_le_left m ((c1 r0 + T) / 2))
    by_contra hle
    push Not at hle
    have hbr := h.optimal_binds hor
    have hy : c2 r ≤ g r t := by simp only [hg]; rw [hbr]; nlinarith
    have h1 := anti' _ _ (ha.trans hat) hle
    have h2 := anti' _ _ hor.1.2.1 hy
    have e := euler_at r _ _ hor
    have hgc : g r (c1 r) = c2 r := by simp only [hg]; rw [hbr]
    simp only [hψ] at e hψr
    rw [hgc] at e
    try rw [← ht] at h1
    have : (1 + r) * h.β * u' (g r t) ≤ (1 + r) * h.β * u' (c2 r) :=
      mul_le_mul_of_nonneg_left h2 (mul_pos hr1 h.β_pos).le
    linarith

/-- The autarky rate exists: `1 + rA = u'(Y₁)/(β u'(Y₂))` (O&R (1.7)). -/
theorem exists_autarkyRate (h : Household) {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c) :
    ∃ rA, 0 < 1 + rA ∧ h.IsAutarkyRate rA := by
  have h1 := hpos _ h.Y1_pos
  have h2 := hpos _ h.Y2_pos
  have hq : 0 < u' h.Y1 / (h.β * u' h.Y2) := div_pos h1 (mul_pos h.β_pos h2)
  have hr : 0 < 1 + (u' h.Y1 / (h.β * u' h.Y2) - 1) := by linarith
  refine ⟨u' h.Y1 / (h.β * u' h.Y2) - 1, hr, (h.isAutarkyRate_iff hu hpos hr).2 ?_⟩
  have hβ := h.β_pos.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  rw [add_sub_cancel, one_div_div]

/-- A selection of optimal plans, one for every `r > −1`. -/
theorem exists_optimal_selection (h : Household) {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hcont : ContinuousOn u' (Ioi 0)) (hinada : Tendsto u' (𝓝[>] 0) atTop) :
    ∃ f : ℝ → ℝ × ℝ, ∀ r, 0 < 1 + r → h.IsOptimal r (f r).1 (f r).2 := by
  have hsel : ∀ r, ∃ p : ℝ × ℝ, 0 < 1 + r → h.IsOptimal r p.1 p.2 := fun r => by
    by_cases hr : 0 < 1 + r
    · obtain ⟨c1, c2, ho⟩ := h.exists_optimal hu hpos hcont hinada hr
      exact ⟨(c1, c2), fun _ => ho⟩
    · exact ⟨(0, 0), fun h' => absurd h' hr⟩
  choose f hf using hsel
  exact ⟨f, hf⟩

/-- Existence of equilibrium when Home's autarky rate is weakly below Foreign's: world excess
demand is positive at `rA` and negative at `rA*`, and continuous in between. -/
theorem exists_equilibrium_of_le {h hs : Household} {u' us' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hcont : ContinuousOn u' (Ioi 0)) (hinada : Tendsto u' (𝓝[>] 0) atTop)
    (hus : ∀ c, 0 < c → HasDerivAt hs.u (us' c) c) (hposs : ∀ c, 0 < c → 0 < us' c)
    (hconts : ContinuousOn us' (Ioi 0)) (hinadas : Tendsto us' (𝓝[>] 0) atTop)
    {rA rAs : ℝ} (hr : 0 < 1 + rA) (hA : h.IsAutarkyRate rA) (hAs : hs.IsAutarkyRate rAs)
    (hle : rA ≤ rAs) : ∃ r c1 c2 s1 s2, IsEquilibrium h hs r c1 c2 s1 s2 := by
  rcases hle.lt_or_eq with hlt | rfl
  swap
  · exact ⟨rA, h.Y1, h.Y2, hs.Y1, hs.Y2, hA, hAs, rfl⟩
  obtain ⟨f, hf⟩ := exists_optimal_selection h hu hpos hcont hinada
  obtain ⟨fs, hfs⟩ := exists_optimal_selection hs hus hposs hconts hinadas
  set z : ℝ → ℝ := fun r => (f r).1 + (fs r).1 - (h.Y1 + hs.Y1) with hz
  have hzc : ContinuousOn z (Icc rA rAs) := by
    intro r hri
    have hr1 : 0 < 1 + r := by linarith [hri.1]
    have hev : ∀ᶠ r' in 𝓝 r, 0 < 1 + r' :=
      (continuousAt_const.add continuousAt_id).eventually (lt_mem_nhds hr1)
    have c1 := continuousAt_optimal_c1 h hu hcont hr1 (hev.mono fun r' h' => hf r' h')
    have c2 := continuousAt_optimal_c1 hs hus hconts hr1 (hev.mono fun r' h' => hfs r' h')
    exact ((c1.add c2).sub continuousAt_const).continuousWithinAt
  have hrs : 0 < 1 + rAs := by linarith
  have hza : 0 < z rA := by
    have e1 := (h.optimal_at_autarky hA (hf rA hr)).1
    have e2 := hs.saving_neg_of_lt_autarky hus hposs hAs hlt (hfs rA hr)
    simp only [hz]
    linarith
  have hzb : z rAs < 0 := by
    have e1 := h.saving_pos_of_autarky_lt hu hpos hA hlt (hf rAs hrs)
    have e2 := (hs.optimal_at_autarky hAs (hfs rAs hrs)).1
    simp only [hz]
    linarith
  obtain ⟨r, hri, hzr⟩ := intermediate_value_Icc' hlt.le hzc ⟨hzb.le, hza.le⟩
  have hr1 : 0 < 1 + r := by linarith [hri.1]
  refine ⟨r, (f r).1, (f r).2, (fs r).1, (fs r).2, hf r hr1, hfs r hr1, ?_⟩
  simp only [hz] at hzr
  linarith

/-- **Existence of a world equilibrium**: two households with continuous, positive marginal
utility satisfying the Inada condition have an equilibrium world interest rate. -/
theorem exists_equilibrium {h hs : Household} {u' us' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hcont : ContinuousOn u' (Ioi 0)) (hinada : Tendsto u' (𝓝[>] 0) atTop)
    (hus : ∀ c, 0 < c → HasDerivAt hs.u (us' c) c) (hposs : ∀ c, 0 < c → 0 < us' c)
    (hconts : ContinuousOn us' (Ioi 0)) (hinadas : Tendsto us' (𝓝[>] 0) atTop) :
    ∃ r c1 c2 s1 s2, IsEquilibrium h hs r c1 c2 s1 s2 := by
  obtain ⟨rA, hr, hA⟩ := exists_autarkyRate h hu hpos
  obtain ⟨rAs, hrs, hAs⟩ := exists_autarkyRate hs hus hposs
  rcases le_total rA rAs with hle | hle
  · exact exists_equilibrium_of_le hu hpos hcont hinada hus hposs hconts hinadas hr hA hAs hle
  · obtain ⟨r, s1, s2, c1, c2, hos, ho, hc⟩ :=
      exists_equilibrium_of_le hus hposs hconts hinadas hu hpos hcont hinada hrs hAs hA hle
    exact ⟨r, c1, c2, s1, s2, ho, hos, by linarith⟩

/-- A bundle at least as good as the optimum costs at least the household's wealth. -/
theorem cost_ge_of_utility_ge (h : Household) {r c1 c2 d1 d2 : ℝ} (ho : h.IsOptimal r c1 c2)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hU : h.utility c1 c2 ≤ h.utility d1 d2) :
    h.Y2 + (1 + r) * (h.Y1 - d1) ≤ d2 := by
  by_contra hlt
  push Not at hlt
  have h1 := ho.2 d1 _ ⟨hd1, hd2.trans hlt, le_rfl⟩
  have h2 := h.utility_lt_utility_of_lt (c1 := d1) hd2 hlt
  linarith

/-- A bundle strictly better than the optimum costs strictly more than the household's wealth. -/
theorem cost_gt_of_utility_gt (h : Household) {r c1 c2 d1 d2 : ℝ} (ho : h.IsOptimal r c1 c2)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hU : h.utility c1 c2 < h.utility d1 d2) :
    h.Y2 + (1 + r) * (h.Y1 - d1) < d2 := by
  by_contra hle
  push Not at hle
  linarith [ho.2 d1 d2 ⟨hd1, hd2, hle⟩]

/-- **The first welfare theorem** (O&R p. 33): no feasible allocation makes one country better
off without making the other worse off. -/
theorem first_welfare_theorem {h hs : Household} {r c1 c2 s1 s2 d1 d2 e1 e2 : ℝ}
    (hr : 0 < 1 + r) (he : IsEquilibrium h hs r c1 c2 s1 s2) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (he1 : 0 < e1) (he2 : 0 < e2) (hres1 : d1 + e1 ≤ h.Y1 + hs.Y1)
    (hres2 : d2 + e2 ≤ h.Y2 + hs.Y2) (hU : h.utility c1 c2 ≤ h.utility d1 d2)
    (hUs : hs.utility s1 s2 ≤ hs.utility e1 e2) :
    h.utility c1 c2 = h.utility d1 d2 ∧ hs.utility s1 s2 = hs.utility e1 e2 := by
  obtain ⟨ho, hos, -⟩ := he
  have wd := cost_ge_of_utility_ge h ho hd1 hd2 hU
  have we := cost_ge_of_utility_ge hs hos he1 he2 hUs
  have hsum : 0 ≤ (1 + r) * (h.Y1 + hs.Y1 - d1 - e1) := mul_nonneg hr.le (by linarith)
  constructor
  · by_contra hne
    have := cost_gt_of_utility_gt h ho hd1 hd2 (lt_of_le_of_ne hU hne)
    nlinarith
  · by_contra hne
    have := cost_gt_of_utility_gt hs hos he1 he2 (lt_of_le_of_ne hUs hne)
    nlinarith

/-! ### Log utility: Exercises 2 and 5 (O&R pp. 55–56) -/

/-- Log-utility date-1 consumption, `C₁ = (Y₁ + Y₂/(1 + r))/(1 + β)` (Exercise 2(a)). -/
noncomputable def logC1 (β Y1 Y2 r : ℝ) : ℝ := (Y1 + Y2 / (1 + r)) / (1 + β)

/-- **Exercise 2(b)**: log-utility saving, `S₁ = βY₁/(1 + β) − Y₂/((1 + β)(1 + r))`. -/
theorem log_saving {β Y1 Y2 r : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r) :
    Y1 - logC1 β Y1 Y2 r = β / (1 + β) * Y1 - Y2 / ((1 + β) * (1 + r)) := by
  have : (1 + β) ≠ 0 := by linarith
  unfold logC1
  field_simp
  ring

/-- **Exercise 2(c)**: the world market clears iff
`1 + r = [Y₂/(1 + β) + Y₂*/(1 + β*)]/[βY₁/(1 + β) + β*Y₁*/(1 + β*)]`. -/
theorem log_equilibrium_iff {β βs Y1 Y2 Y1s Y2s r : ℝ} (hβ : 0 < β) (hβs : 0 < βs)
    (hY1 : 0 < Y1) (hY1s : 0 < Y1s) (hr : 0 < 1 + r) :
    logC1 β Y1 Y2 r + logC1 βs Y1s Y2s r = Y1 + Y1s ↔
      1 + r = (Y2 / (1 + β) + Y2s / (1 + βs)) / (β * Y1 / (1 + β) + βs * Y1s / (1 + βs)) := by
  have h1 : (1 + β) ≠ 0 := by linarith
  have h2 : (1 + βs) ≠ 0 := by linarith
  have hB : 0 < β * Y1 / (1 + β) + βs * Y1s / (1 + βs) := by positivity
  have key : logC1 β Y1 Y2 r + logC1 βs Y1s Y2s r - (Y1 + Y1s) =
      (Y2 / (1 + β) + Y2s / (1 + βs)) / (1 + r) -
        (β * Y1 / (1 + β) + βs * Y1s / (1 + βs)) := by
    unfold logC1
    field_simp
    ring
  rw [eq_div_iff hB.ne']
  constructor
  · intro heq
    have hk : (Y2 / (1 + β) + Y2s / (1 + βs)) / (1 + r) =
        β * Y1 / (1 + β) + βs * Y1s / (1 + βs) := by linarith
    rw [div_eq_iff hr.ne'] at hk
    linarith
  · intro heq
    have hk : (Y2 / (1 + β) + Y2s / (1 + βs)) / (1 + r) =
        β * Y1 / (1 + β) + βs * Y1s / (1 + βs) := by
      rw [div_eq_iff hr.ne']
      linarith
    linarith

/-- The mediant of two fractions lies strictly between them. -/
theorem mediant_between {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) (h : a / b < c / d) :
    a / b < (a + c) / (b + d) ∧ (a + c) / (b + d) < c / d := by
  rw [div_lt_div_iff₀ hb hd] at h
  constructor
  · rw [div_lt_div_iff₀ hb (by linarith)]
    nlinarith
  · rw [div_lt_div_iff₀ (by linarith) hd]
    nlinarith

/-- **Exercise 2(d)**: the log-utility world gross rate lies strictly between the two autarky
gross rates `Y₂/(βY₁)` and `Y₂*/(β*Y₁*)`. -/
theorem log_rate_between {β βs Y1 Y2 Y1s Y2s : ℝ} (hβ : 0 < β) (hβs : 0 < βs)
    (hY1 : 0 < Y1) (hY1s : 0 < Y1s) (hlt : Y2 / (β * Y1) < Y2s / (βs * Y1s)) :
    Y2 / (β * Y1) < (Y2 / (1 + β) + Y2s / (1 + βs)) / (β * Y1 / (1 + β) + βs * Y1s / (1 + βs))
    ∧ (Y2 / (1 + β) + Y2s / (1 + βs)) / (β * Y1 / (1 + β) + βs * Y1s / (1 + βs)) <
      Y2s / (βs * Y1s) := by
  have h1 : (1 + β) ≠ 0 := by linarith
  have h2 : (1 + βs) ≠ 0 := by linarith
  have ea : Y2 / (1 + β) / (β * Y1 / (1 + β)) = Y2 / (β * Y1) := by field_simp
  have ec : Y2s / (1 + βs) / (βs * Y1s / (1 + βs)) = Y2s / (βs * Y1s) := by field_simp
  have hm := mediant_between (a := Y2 / (1 + β)) (c := Y2s / (1 + βs))
    (by positivity : 0 < β * Y1 / (1 + β)) (by positivity : 0 < βs * Y1s / (1 + βs))
    (by rw [ea, ec]; exact hlt)
  rw [ea, ec] at hm
  exact hm

/-- Log-utility lifetime welfare as a function of the world rate (Exercise 2(f)). -/
noncomputable def logWelfare (β Y1 Y2 r : ℝ) : ℝ :=
  Real.log (logC1 β Y1 Y2 r) + β * Real.log ((1 + r) * β * logC1 β Y1 Y2 r)

/-- **Exercise 2(f)**: `dU/dr = β(r − rA)/[(1 + r)((1 + r) + β(1 + rA))]` where
`1 + rA = Y₂/(βY₁)` is the autarky gross rate. Welfare rises with `r` iff `r > rA`. -/
theorem hasDerivAt_logWelfare {β Y1 Y2 r rA : ℝ} (hβ : 0 < β) (hY1 : 0 < Y1) (hY2 : 0 < Y2)
    (hr : 0 < 1 + r) (hrA : 1 + rA = Y2 / (β * Y1)) :
    HasDerivAt (logWelfare β Y1 Y2)
      (β / (1 + r) * ((r - rA) / ((1 + r) + β * (1 + rA)))) r := by
  have h1b : (0 : ℝ) < 1 + β := by linarith
  have hW : 0 < Y1 + Y2 / (1 + r) := by positivity
  have hC : 0 < logC1 β Y1 Y2 r := div_pos hW h1b
  have hd1 : HasDerivAt (fun s : ℝ => 1 + s) 1 r := (hasDerivAt_id r).const_add 1
  have hdW : HasDerivAt (fun s => Y1 + Y2 / (1 + s)) (-(Y2 * 1) / (1 + r) ^ 2) r := by
    have := (hasDerivAt_const r Y2).div hd1 hr.ne'
    simpa using this.const_add Y1
  have hdC : HasDerivAt (logC1 β Y1 Y2) (-(Y2 * 1) / (1 + r) ^ 2 / (1 + β)) r :=
    hdW.div_const (1 + β)
  have hdC2 : HasDerivAt (fun s => (1 + s) * β * logC1 β Y1 Y2 s)
      (1 * β * logC1 β Y1 Y2 r + (1 + r) * β * (-(Y2 * 1) / (1 + r) ^ 2 / (1 + β))) r :=
    (hd1.mul_const β).mul hdC
  have hC2 : 0 < (1 + r) * β * logC1 β Y1 Y2 r := by positivity
  have := (hdC.log hC.ne').add ((hdC2.log hC2.ne').const_mul β)
  refine this.congr_deriv ?_
  have hβ1 : (1 + rA) = Y2 / (β * Y1) := hrA
  have hden : 0 < (1 + r) + β * (1 + rA) := by rw [hrA]; positivity
  have hY : Y2 = β * Y1 * (1 + rA) := by rw [hrA]; field_simp
  unfold logC1
  rw [hβ1]
  field_simp
  linear_combination (-1 : ℝ) * hY

/-- The log-utility world gross rate from Exercise 2(c). -/
noncomputable def logGrossRate (β βs Y1 Y2 Y1s Y2s : ℝ) : ℝ :=
  (Y2 / (1 + β) + Y2s / (1 + βs)) / (β * Y1 / (1 + β) + βs * Y1s / (1 + βs))

/-- **Exercise 5 (log utility)**: a rise in Home's date-1 output lowers the world rate. -/
theorem logGrossRate_anti_Y1 {β βs Y2 Y1s Y2s : ℝ} (hβ : 0 < β) (hβs : 0 < βs)
    (hY2 : 0 < Y2) (hY1s : 0 < Y1s) (hY2s : 0 < Y2s) :
    StrictAntiOn (fun Y1 => logGrossRate β βs Y1 Y2 Y1s Y2s) (Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  unfold logGrossRate
  apply div_lt_div_of_pos_left (by positivity) (by positivity)
  have : β * a / (1 + β) < β * b / (1 + β) :=
    div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hab hβ) (by linarith)
  linarith

/-- **Exercise 5 (log utility)**: a rise in Home's date-2 output raises the world rate. -/
theorem logGrossRate_mono_Y2 {β βs Y1 Y1s Y2s : ℝ} (hβ : 0 < β) (hβs : 0 < βs)
    (hY1 : 0 < Y1) (hY1s : 0 < Y1s) :
    StrictMono (fun Y2 => logGrossRate β βs Y1 Y2 Y1s Y2s) := by
  intro a b hab
  unfold logGrossRate
  apply div_lt_div_of_pos_right _ (by positivity)
  have : a / (1 + β) < b / (1 + β) := div_lt_div_of_pos_right hab (by linarith)
  linarith

/-- The world rate is symmetric in the two countries. -/
theorem logGrossRate_comm (β βs Y1 Y2 Y1s Y2s : ℝ) :
    logGrossRate β βs Y1 Y2 Y1s Y2s = logGrossRate βs β Y1s Y2s Y1 Y2 := by
  unfold logGrossRate
  rw [add_comm (Y2 / (1 + β)), add_comm (β * Y1 / (1 + β))]

/-- **Exercise 5 (log utility)**: a rise in Foreign's date-1 output lowers the world rate. -/
theorem logGrossRate_anti_Y1s {β βs Y1 Y2 Y2s : ℝ} (hβ : 0 < β) (hβs : 0 < βs)
    (hY1 : 0 < Y1) (hY2 : 0 < Y2) (hY2s : 0 < Y2s) :
    StrictAntiOn (fun Y1s => logGrossRate β βs Y1 Y2 Y1s Y2s) (Ioi 0) := by
  simp only [logGrossRate_comm β βs Y1 Y2]
  exact logGrossRate_anti_Y1 hβs hβ hY2s hY1 hY2

/-- **Exercise 5 (log utility)**: a rise in Foreign's date-2 output raises the world rate. -/
theorem logGrossRate_mono_Y2s {β βs Y1 Y2 Y1s : ℝ} (hβ : 0 < β) (hβs : 0 < βs)
    (hY1 : 0 < Y1) (hY1s : 0 < Y1s) :
    StrictMono (fun Y2s => logGrossRate β βs Y1 Y2 Y1s Y2s) := by
  simp only [logGrossRate_comm β βs Y1 Y2]
  exact logGrossRate_mono_Y2 hβs hβ hY1s hY1

/-! ### Investment and productivity (O&R pp. 31–38) -/

/-- **Investment responds to productivity** (O&R p. 34): along a path `K₂(A₂)` with
`A₂ F'(K₂) = r` at a constant `r`, `dK₂/dA₂ = −F'(K₂)/(A₂ F''(K₂))`. -/
theorem hasDerivAt_capital_productivity {F' K : ℝ → ℝ} {A r dK dF : ℝ}
    (hK : HasDerivAt K dK A) (hF : HasDerivAt F' dF (K A))
    (hid : ∀ᶠ a in 𝓝 A, a * F' (K a) = r) (hA : A ≠ 0) (hdF : dF ≠ 0) :
    dK = -F' (K A) / (A * dF) := by
  have hd : HasDerivAt (fun a => a * F' (K a)) (1 * F' (K A) + A * (dF * dK)) A :=
    (hasDerivAt_id A).mul (hF.comp A hK)
  have hc : HasDerivAt (fun a => a * F' (K a)) 0 A :=
    (hasDerivAt_const A r).congr_of_eventuallyEq hid
  have := hd.unique hc
  field_simp
  linarith

/-- With `F' > 0` and `F'' < 0`, higher productivity raises investment at a given world
rate (O&R p. 34). -/
theorem capital_increasing_in_productivity {F' K : ℝ → ℝ} {A r dK dF : ℝ}
    (hK : HasDerivAt K dK A) (hF : HasDerivAt F' dF (K A))
    (hid : ∀ᶠ a in 𝓝 A, a * F' (K a) = r) (hA : 0 < A) (hF'pos : 0 < F' (K A))
    (hdF : dF < 0) : 0 < dK := by
  rw [hasDerivAt_capital_productivity hK hF hid hA.ne' hdF.ne]
  exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_pos_of_neg hA hdF)

/-- **Blanchard–Summers** (O&R pp. 36–38): with `Y = A K^α`, a productivity rise shifts the
world saving curve up by `(1 + r)/(1 + α/r) · Â₂` and the investment curve by `r · Â₂`; the
saving shift is larger iff `α < 1`, so world investment falls. -/
theorem blanchard_summers {r α : ℝ} (hr : 0 < r) (hα : 0 < α) :
    r < (1 + r) / (1 + α / r) ↔ α < 1 := by
  have e : (1 + r) / (1 + α / r) = (1 + r) * r / (r + α) := by field_simp
  rw [e, lt_div_iff₀ (by linarith)]
  constructor <;> intro h <;> nlinarith

end ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium
