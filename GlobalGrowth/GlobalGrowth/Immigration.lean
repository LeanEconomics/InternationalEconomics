/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import GlobalGrowth.RamseyCassKoopmans

/-!
# The benefits of immigration: skilled versus unskilled labour

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §7.1.2.3
(pp. 448–454), equations (34)–(41) and footnotes 14–15.

* **Factor prices (37)–(38).** For a strictly concave intensive technology: the tangent
  inequality, a positive unskilled wage that rises with `h`, and a return to skill that falls
  with `h`.
* **Impact effects.** Immigration raises natives' income on impact. We prove the exact
  identity `F(Nh̄,N+M) - F(Nh̄,N) - M F_L = N[f(h₀) + f'(h₀)(h̄-h₀) - f(h̄)] > 0`. The same
  holds for fn 15 (skilled immigrants). The gain is zero iff immigrants bring `h̄`.
* **Aggregation (41), fn 14.** Per-capita `h` and `c` obey (39)–(40) after immigration too,
  and the steady state is unchanged.
* **Natives gain along any price path.** This is the rigorous version of the "production
  autarky" argument on p. 452. The keep-`h̄` plan is feasible at *any* prices and yields
  `c_t ≥ c̄`, strictly when `h_t ≠ h̄`. So its infinite-horizon log utility exceeds the
  no-immigration utility `log c̄/(1-β)`, and so does the native's optimum.
* **The log consumer facing an arbitrary price path.** The present-value budget, the closed
  form for wealth, the log rule `c = (1-β)(financial + human wealth)`, and optimality of the
  rule over the infinite horizon (supporting hyperplane) under bounded returns, when the rule
  never borrows.
* **Natives and immigrants never converge (p. 452).** The skill gap between log-rule agents
  grows at `βR_t ≥ 1` while `h_t ≤ h̄`. So immigrants stay below `Mh̄/(N+M) < h̄` forever, and
  natives end above `h̄`. This is conditional on the transition staying below `h̄`, which the
  book reads off Fig. 7.8 (the saddle path is not constructed here). It also requires the
  immigrants' unconstrained plan never to borrow (they start with `h^M_0 = 0`), which the book
  assumes implicitly.
* **Round 2 additions.**
  - *Exact no-borrowing condition:* immigrants never borrow iff
    `h_t ≥ h₀ ∏_{s<t} βR_s` for all `t`.
  - *Harberger triangle:* the net gain is `o(M)` while the redistribution from native
    unskilled labour is first order, `→ -h̄²f''(h̄)`.
  - *Newborns:* their human wealth is lower along any transition below `h̄`.
  - *Closed-form saddle path* (`f = h^α`, `δ = 1`): `h_{t+1} = αβh_t^α` rises monotonically to
    `h̄`. Immigrants' optimal plan holds exactly zero human capital (they never borrow, and
    consume the wage). Natives hold `((N+M)/N)h_t → ((N+M)/N)h̄ > h̄`, both plans are
    optimal, and zero-wealth newborns and immigrants lose utility.
* **General saddle path** (via `RamseyCassKoopmans.LogUtility`): for any technology satisfying
  the book's hypotheses and any `δ ∈ [0, 1]`, the per-capita system (39)–(40) with
  transversality has a unique solution from `0 < h₀ < h̄`. It rises strictly, stays below
  `h̄` and converges to `h̄`; this discharges "the path stays below `h̄`" in general.
* **Immigrants never borrow (general `δ`).** Along the saddle path, if
  `φ(h) = (f(h) + (1-δ)h)/(β(f'(h) + 1 - δ)h)` is non-increasing, then
  `h_{t+1} ≥ βR_t h_t` at every date, hence the exact condition. The proof uses the ratio
  `m_t = h_{t+1}/c_t`, which obeys `m_{t+1} = φ(h_{t+1})m_t - 1`, is bounded, and is therefore
  non-decreasing. This holds for Cobb–Douglas with every `δ ∈ [0, 1]`.
-/

namespace ObstfeldRogoff.GlobalGrowth.Immigration

open Filter Topology Finset

/-! ## Technology and factor prices (37)–(38) -/

/-- An intensive production function `f(h) = F(h, 1)` (O&R p. 450): strictly concave on
`[0, ∞)`, with derivative `f'` on `(0, ∞)` and `f(0) = 0`. -/
structure Technology (f f' : ℝ → ℝ) : Prop where
  conc : StrictConcaveOn ℝ (Set.Ici 0) f
  deriv : ∀ h, 0 < h → HasDerivAt f (f' h) h
  zero : f 0 = 0

variable {f f' : ℝ → ℝ}

/-- The unskilled wage O&R (37): `w(h) = f(h) - h f'(h)`. -/
def wageU (f f' : ℝ → ℝ) (h : ℝ) : ℝ := f h - h * f' h

/-- **The tangent inequality** (strict concavity): for `h > 0`, `x ≥ 0`, `x ≠ h`,
`f(x) < f(h) + f'(h)(x - h)`. -/
theorem Technology.tangent_lt (T : Technology f f') {h x : ℝ} (hh : 0 < h) (hx : 0 ≤ x)
    (hne : x ≠ h) : f x < f h + f' h * (x - h) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := T.conc.lt_slope_of_hasDerivAt (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hh.le) hlt
      (T.deriv h hh)
    rw [slope_def_field, lt_div_iff₀ (by linarith)] at this
    nlinarith
  · have := T.conc.slope_lt_of_hasDerivAt (Set.mem_Ici.mpr hh.le) (Set.mem_Ici.mpr hx) hgt
      (T.deriv h hh)
    rw [slope_def_field, div_lt_iff₀ (by linarith)] at this
    nlinarith

/-- The tangent inequality in weak form. -/
theorem Technology.tangent_le (T : Technology f f') {h x : ℝ} (hh : 0 < h) (hx : 0 ≤ x) :
    f x ≤ f h + f' h * (x - h) := by
  rcases eq_or_ne x h with rfl | hne
  · simp
  · exact (T.tangent_lt hh hx hne).le

/-- The unskilled wage is positive: `w(h) = f(h) - hf'(h) > 0` (tangent at `h` evaluated at
`0`, with `f(0) = 0`). -/
theorem Technology.wage_pos (T : Technology f f') {h : ℝ} (hh : 0 < h) : 0 < wageU f f' h := by
  have := T.tangent_lt hh le_rfl hh.ne
  rw [T.zero] at this
  unfold wageU
  linarith

/-- **The return to skill is strictly decreasing** (O&R p. 452: `w_s` rises when `h` falls). -/
theorem Technology.deriv_strictAnti (T : Technology f f') {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    f' b < f' a := by
  have h1 := T.tangent_lt ha (ha.trans hab).le hab.ne'
  have h2 := T.tangent_lt (ha.trans hab) ha.le hab.ne
  nlinarith

/-- **The unskilled wage is strictly increasing in `h`** (O&R p. 452: the wage for unskilled
workers falls when `h` falls). -/
theorem Technology.wage_strictMono (T : Technology f f') {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    wageU f f' a < wageU f f' b := by
  have hb : 0 < b := ha.trans hab
  have h2 := T.tangent_lt hb ha.le hab.ne
  have hd := T.deriv_strictAnti ha hab
  unfold wageU
  nlinarith

/-- **Income from the steady-state portfolio at any price** (the key inequality behind
O&R p. 452): for every `h > 0`, `w(h) + f'(h) h̄ = f(h) + f'(h)(h̄ - h) ≥ f(h̄)`, with strict
inequality iff `h ≠ h̄`. -/
theorem Technology.income_ge (T : Technology f f') {h hbar : ℝ} (hh : 0 < h)
    (hhb : 0 ≤ hbar) :
    f hbar ≤ wageU f f' h + f' h * hbar ∧ (h ≠ hbar → f hbar < wageU f f' h + f' h * hbar) := by
  unfold wageU
  refine ⟨by nlinarith [T.tangent_le hh hhb], fun hne => ?_⟩
  nlinarith [T.tangent_lt hh hhb (Ne.symm hne)]

/-! ## The impact effect and footnote 15 -/

/-- **The impact gain to natives, O&R p. 452**: with `F(H, L) = L f(H/L)` and
`h₀ = Nh̄/(N+M)`, the rise in output net of immigrants' pay,
`F(Nh̄, N+M) - F(Nh̄, N) - M F_L(Nh̄, N+M)`, equals `N[f(h₀) + f'(h₀)(h̄ - h₀) - f(h̄)]`. -/
theorem impact_identity {N M hbar : ℝ} (hN : 0 < N) (hM : 0 < M) :
    (N + M) * f (N * hbar / (N + M)) - N * f (N * hbar / N) -
        M * wageU f f' (N * hbar / (N + M)) =
      N * (f (N * hbar / (N + M)) + f' (N * hbar / (N + M)) *
        (hbar - N * hbar / (N + M)) - f hbar) := by
  unfold wageU
  rw [show N * hbar / N = hbar by field_simp]
  field_simp
  ring

/-- **Unskilled immigration raises natives' income on impact** (O&R p. 452):
`F(Nh̄, N+M) - F(Nh̄, N) - M F_L(Nh̄, N+M) > 0` for `M > 0`, `h̄ > 0`. -/
theorem impact_gain (T : Technology f f') {N M hbar : ℝ} (hN : 0 < N) (hM : 0 < M)
    (hhb : 0 < hbar) :
    0 < (N + M) * f (N * hbar / (N + M)) - N * f (N * hbar / N) -
      M * wageU f f' (N * hbar / (N + M)) := by
  rw [impact_identity hN hM]
  have h0 : 0 < N * hbar / (N + M) := by positivity
  have hlt : N * hbar / (N + M) < hbar := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have := T.tangent_lt h0 hhb.le hlt.ne'
  nlinarith

/-- **Footnote 15 (skilled immigrants)**: with `F(H, L) = L f(H/L)`, adding human capital
`ΔH ≠ 0` at fixed labour `L` and paying it its marginal product at the new point,
`F(H₁ + ΔH, L) - F(H₁, L) - ΔH F_H(H₁ + ΔH, L) > 0`. -/
theorem fn15_gain (T : Technology f f') {H₁ ΔH L : ℝ} (hL : 0 < L) (hH₁ : 0 ≤ H₁)
    (hH₂ : 0 < H₁ + ΔH) (hΔ : ΔH ≠ 0) :
    0 < L * f ((H₁ + ΔH) / L) - L * f (H₁ / L) - ΔH * f' ((H₁ + ΔH) / L) := by
  have hne : H₁ / L ≠ (H₁ + ΔH) / L := by
    intro h
    field_simp at h
    exact hΔ (by linarith)
  have e : ΔH = L * ((H₁ + ΔH) / L - H₁ / L) := by field_simp; ring
  have hx2 : 0 < (H₁ + ΔH) / L := div_pos hH₂ hL
  have hx1 : 0 ≤ H₁ / L := div_nonneg hH₁ hL.le
  set x₂ := (H₁ + ΔH) / L
  set x₁ := H₁ / L
  have := T.tangent_lt hx2 hx1 hne
  rw [e]
  nlinarith

/-- **The impact point** (O&R Fig. 7.8): per-capita human capital falls to
`h₀ = Nh̄/(N+M) < h̄`, the unskilled wage falls and the return to skill rises. -/
theorem impact_prices (T : Technology f f') {N M hbar : ℝ} (hN : 0 < N) (hM : 0 < M)
    (hhb : 0 < hbar) :
    N * hbar / (N + M) < hbar ∧ wageU f f' (N * hbar / (N + M)) < wageU f f' hbar ∧
      f' hbar < f' (N * hbar / (N + M)) := by
  have h0 : 0 < N * hbar / (N + M) := by positivity
  have hlt : N * hbar / (N + M) < hbar := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  exact ⟨hlt, T.wage_strictMono h0 hlt, T.deriv_strictAnti h0 hlt⟩

/-! ## Steady state and aggregation (39)–(41), footnote 14 -/

/-- **Steady-state consumption is positive**: at `f'(h̄) = (1-β)/β + δ` (O&R p. 450) with
`0 < β < 1`, `c̄ = f(h̄) - δh̄ > 0`. -/
theorem steady_consumption_pos (T : Technology f f') {β δ hbar : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hhb : 0 < hbar) (hss : f' hbar = (1 - β) / β + δ) :
    0 < f hbar - δ * hbar := by
  have hw := T.wage_pos hhb
  unfold wageU at hw
  have : 0 < (1 - β) / β := div_pos (by linarith) hβ
  nlinarith

/-- **Aggregation, O&R (41) and fn 14**: if natives (`N`) and immigrants (`M`) each obey the
budget (35) and the log Euler equation (36) at common prices `w_t = w(h_t)`,
`w_{s,t} = f'(h_t)`, where `h_t` is the per-capita stock, then per-capita human capital and
consumption obey (39) and (40), before and after immigration alike. -/
theorem aggregation {N M β δ : ℝ} {h hN hM c cN cM : ℕ → ℝ} (hNM : 0 < N + M)
    (hh : ∀ t, h t = (N * hN t + M * hM t) / (N + M))
    (hc : ∀ t, c t = (N * cN t + M * cM t) / (N + M))
    (bN : ∀ t, hN (t + 1) = (1 + f' (h t) - δ) * hN t + wageU f f' (h t) - cN t)
    (bM : ∀ t, hM (t + 1) = (1 + f' (h t) - δ) * hM t + wageU f f' (h t) - cM t)
    (eN : ∀ t, cN (t + 1) = (1 + f' (h (t + 1)) - δ) * β * cN t)
    (eM : ∀ t, cM (t + 1) = (1 + f' (h (t + 1)) - δ) * β * cM t) (t : ℕ) :
    h (t + 1) - h t = f (h t) - δ * h t - c t ∧
      c (t + 1) = (1 + f' (h (t + 1)) - δ) * β * c t := by
  constructor
  · rw [hh (t + 1), bN t, bM t, hc t]
    have e : h t * (N + M) = N * hN t + M * hM t := by rw [hh t]; field_simp
    unfold wageU
    field_simp
    linear_combination (-(1 + f' (h t) - δ)) * e
  · rw [hc, hc, eN, eM]
    field_simp

/-! ## Natives gain along any price path (O&R p. 452, made rigorous) -/

/-- **Keeping the steady-state skill level is feasible and never worse** (O&R p. 452): along
*any* path of per-capita human capital `h_t > 0` (hence any post-immigration price path),
a native who keeps `h^N_t = h̄` consumes `c_t = w(h_t) + (f'(h_t) - δ)h̄ ≥ c̄ = f(h̄) - δh̄`,
with strict inequality whenever `h_t ≠ h̄`. -/
theorem keep_plan (T : Technology f f') {δ hbar : ℝ} {h : ℕ → ℝ} (hhb : 0 < hbar)
    (hpos : ∀ t, 0 < h t) (t : ℕ) :
    hbar = (1 + f' (h t) - δ) * hbar + wageU f f' (h t) -
        (wageU f f' (h t) + (f' (h t) - δ) * hbar) ∧
      f hbar - δ * hbar ≤ wageU f f' (h t) + (f' (h t) - δ) * hbar ∧
      (h t ≠ hbar → f hbar - δ * hbar < wageU f f' (h t) + (f' (h t) - δ) * hbar) := by
  obtain ⟨h1, h2⟩ := T.income_ge (hpos t) hhb.le
  refine ⟨by ring, by linarith, fun hne => by linarith [h2 hne]⟩

/-- Consumption on the keep-`h̄` plan is bounded above along a path in `[a, b]`, `a > 0`. -/
theorem keep_plan_bounded (T : Technology f f') {δ hbar a b : ℝ} {h : ℕ → ℝ} (hhb : 0 < hbar)
    (ha : 0 < a) (hbnd : ∀ t, a ≤ h t ∧ h t ≤ b) (t : ℕ) :
    wageU f f' (h t) + (f' (h t) - δ) * hbar ≤
      f a + |f' a| * (b + a) + (|f' a| + |f' b|) * (hbar + b) + |δ| * hbar := by
  have hpos : 0 < h t := lt_of_lt_of_le ha (hbnd t).1
  have hb : 0 < b := lt_of_lt_of_le hpos (hbnd t).2
  have hfa : f (h t) ≤ f a + f' a * (h t - a) := T.tangent_le ha hpos.le
  have hd1 : f' (h t) ≤ f' a := by
    rcases eq_or_lt_of_le (hbnd t).1 with h1 | h1
    · rw [h1]
    · exact (T.deriv_strictAnti ha h1).le
  have hd2 : f' b ≤ f' (h t) := by
    rcases eq_or_lt_of_le (hbnd t).2 with h1 | h1
    · rw [h1]
    · exact (T.deriv_strictAnti hpos h1).le
  have habs : |f' (h t)| ≤ |f' a| + |f' b| := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (f' b), le_abs_self (f' a), neg_abs_le (f' a),
      le_abs_self (f' b)]
  have e1 : f' a * (h t - a) ≤ |f' a| * (b + a) := by
    calc f' a * (h t - a) ≤ |f' a * (h t - a)| := le_abs_self _
      _ = |f' a| * |h t - a| := abs_mul _ _
      _ ≤ |f' a| * (b + a) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_le]
        constructor <;> linarith [(hbnd t).1, (hbnd t).2]
  have e2 : f' (h t) * (hbar - h t) ≤ (|f' a| + |f' b|) * (hbar + b) := by
    calc f' (h t) * (hbar - h t) ≤ |f' (h t) * (hbar - h t)| := le_abs_self _
      _ = |f' (h t)| * |hbar - h t| := abs_mul _ _
      _ ≤ (|f' a| + |f' b|) * (hbar + b) := by
        apply mul_le_mul habs _ (abs_nonneg _) (by positivity)
        rw [abs_le]
        constructor <;> linarith [(hbnd t).1, (hbnd t).2]
  have e3 : -(δ * hbar) ≤ |δ| * hbar := by nlinarith [neg_abs_le δ]
  unfold wageU
  nlinarith

/-- **Natives are strictly better off after unskilled (or skilled) immigration, along any
price path** (O&R p. 452, "a simple argument shows that such a reversal can't happen"). Let
the per-capita path `h_t > 0` start at `h₀ ≠ h̄` and stay in a compact interval `[a, b]`,
`a > 0`. The native's keep-`h̄` plan has convergent log utility strictly above the
no-immigration utility `log c̄/(1-β)`. So the native's optimum, which is at least as good as
this feasible plan, is strictly better than no immigration. -/
theorem natives_gain (T : Technology f f') {β δ hbar a b : ℝ} {h : ℕ → ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hhb : 0 < hbar) (hss : f' hbar = (1 - β) / β + δ) (ha : 0 < a)
    (hbnd : ∀ t, a ≤ h t ∧ h t ≤ b) (h0 : h 0 ≠ hbar) :
    Summable (fun t => β ^ t * Real.log (wageU f f' (h t) + (f' (h t) - δ) * hbar)) ∧
      Real.log (f hbar - δ * hbar) / (1 - β) <
        ∑' t, β ^ t * Real.log (wageU f f' (h t) + (f' (h t) - δ) * hbar) := by
  have hpos : ∀ t, 0 < h t := fun t => lt_of_lt_of_le ha (hbnd t).1
  have hcbar := steady_consumption_pos T hβ hβ1 hhb hss
  set c : ℕ → ℝ := fun t => wageU f f' (h t) + (f' (h t) - δ) * hbar with hc
  set Cmax := f a + |f' a| * (b + a) + (|f' a| + |f' b|) * (hbar + b) + |δ| * hbar
  have hlow : ∀ t, f hbar - δ * hbar ≤ c t := fun t => (keep_plan T hhb hpos t).2.1
  have hcpos : ∀ t, 0 < c t := fun t => lt_of_lt_of_le hcbar (hlow t)
  have hup : ∀ t, c t ≤ Cmax := fun t => keep_plan_bounded T hhb ha hbnd t
  set K := |Real.log (f hbar - δ * hbar)| + |Real.log Cmax|
  have hlogb : ∀ t, |Real.log (c t)| ≤ K := by
    intro t
    have l1 := Real.log_le_log hcbar (hlow t)
    have l2 := Real.log_le_log (hcpos t) (hup t)
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (f hbar - δ * hbar)), abs_nonneg (Real.log Cmax)]
    · linarith [le_abs_self (Real.log Cmax), abs_nonneg (Real.log (f hbar - δ * hbar))]
  have hgeo := summable_geometric_of_lt_one hβ.le hβ1
  have hsum : Summable (fun t => β ^ t * Real.log (c t)) := by
    refine Summable.of_norm_bounded (hgeo.mul_right K) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ t)]
    exact mul_le_mul_of_nonneg_left (hlogb t) (pow_pos hβ t).le
  refine ⟨hsum, ?_⟩
  have hbase : ∑' t : ℕ, β ^ t * Real.log (f hbar - δ * hbar) =
      Real.log (f hbar - δ * hbar) / (1 - β) := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ.le hβ1]
    field_simp
  have hbsum := hgeo.mul_right (Real.log (f hbar - δ * hbar))
  have hd : Summable (fun t => β ^ t * Real.log (c t) -
      β ^ t * Real.log (f hbar - δ * hbar)) := hsum.sub hbsum
  have hdnn : ∀ t, 0 ≤ β ^ t * Real.log (c t) - β ^ t * Real.log (f hbar - δ * hbar) := by
    intro t
    have := Real.log_le_log hcbar (hlow t)
    nlinarith [pow_pos hβ t]
  have hd0 : 0 < β ^ 0 * Real.log (c 0) - β ^ 0 * Real.log (f hbar - δ * hbar) := by
    have := Real.log_lt_log hcbar ((keep_plan T hhb hpos 0).2.2 h0)
    simp only [pow_zero, one_mul]
    linarith
  have hle := hd.le_tsum 0 (fun j _ => hdnn j)
  rw [hsum.tsum_sub hbsum, hbase] at hle
  linarith

/-! ## The log consumer facing an arbitrary price path (genuine infinite horizon) -/

/-- Discount factors `q_0 = 1`, `q_{t+1} = q_t / R_{t+1}` for gross returns `R_t` (the price
at date 0 of a unit of consumption at date `t`). -/
noncomputable def disc (R : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => disc R t / R (t + 1)

/-- Discount factors are positive. -/
theorem disc_pos {R : ℕ → ℝ} (hR : ∀ t, 0 < R t) (t : ℕ) : 0 < disc R t := by
  induction t with
  | zero => simp [disc]
  | succ t ih => simp only [disc]; exact div_pos ih (hR _)

/-- `q_{t+1} R_{t+1} = q_t`. -/
theorem disc_succ_mul {R : ℕ → ℝ} (hR : ∀ t, 0 < R t) (t : ℕ) :
    disc R (t + 1) * R (t + 1) = disc R t := by
  simp only [disc]
  field_simp [(hR (t + 1)).ne']

/-- The budget (35) with time-varying prices: `h_{t+1} = R_t h_t + w_t - c_t`, where
`R_t = 1 + w_{s,t} - δ`. -/
def LBudget (R w c h : ℕ → ℝ) : Prop := ∀ t, h (t + 1) = R t * h t + w t - c t

/-- **Present-value budget identity** with time-varying returns:
`∑_{t<T} q_t c_t = R_0 h_0 + ∑_{t<T} q_t w_t - q_T R_T h_T`. -/
theorem lbudget_pv {R w c h : ℕ → ℝ} (hR : ∀ t, 0 < R t) (hb : LBudget R w c h) (T : ℕ) :
    ∑ t ∈ range T, disc R t * c t =
      R 0 * h 0 + ∑ t ∈ range T, disc R t * w t - disc R T * R T * h T := by
  induction T with
  | zero => simp [disc]
  | succ T ih =>
    rw [sum_range_succ, sum_range_succ, ih, hb T, disc_succ_mul hR T]
    ring

/-- The log consumer's candidate consumption `c*_t = (1-β) W₀ βᵗ / q_t`, where `W₀` is total
(financial plus human) wealth. -/
noncomputable def cStar (R : ℕ → ℝ) (β W₀ : ℝ) (t : ℕ) : ℝ := (1 - β) * W₀ * β ^ t / disc R t

/-- The candidate's asset path, generated by the budget from `h₀`. -/
noncomputable def hStar (R w : ℕ → ℝ) (β W₀ h₀ : ℝ) : ℕ → ℝ
  | 0 => h₀
  | t + 1 => R t * hStar R w β W₀ h₀ t + w t - cStar R β W₀ t

/-- The candidate obeys the budget. -/
theorem hStar_budget (R w : ℕ → ℝ) (β W₀ h₀ : ℝ) :
    LBudget R w (cStar R β W₀) (hStar R w β W₀ h₀) := fun _ => rfl

/-- **Closed form of the candidate's wealth**: `q_T R_T h*_T = βᵀ W₀ - ∑_{s ≥ T} q_s w_s`
(financial wealth equals the undissipated share of total wealth minus human wealth). -/
theorem hStar_pv {R w : ℕ → ℝ} {β W₀ h₀ : ℝ} (hR : ∀ t, 0 < R t)
    (hsum : Summable (fun t => disc R t * w t))
    (hW : W₀ = R 0 * h₀ + ∑' t, disc R t * w t) (T : ℕ) :
    disc R T * R T * hStar R w β W₀ h₀ T =
      β ^ T * W₀ - ∑' s, disc R (s + T) * w (s + T) := by
  have hpv := lbudget_pv hR (hStar_budget R w β W₀ h₀) T
  have hc : ∑ t ∈ range T, disc R t * cStar R β W₀ t = W₀ * (1 - β ^ T) := by
    have e : ∀ t ∈ range T, disc R t * cStar R β W₀ t = W₀ * ((1 - β) * β ^ t) := by
      intro t _
      unfold cStar
      field_simp [(disc_pos hR t).ne']
    have hgeom : ∀ n : ℕ, ∑ i ∈ range n, (1 - β) * β ^ i = 1 - β ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring
    rw [sum_congr rfl e, ← mul_sum, hgeom]
  have hsplit := hsum.sum_add_tsum_nat_add T
  have h0 : hStar R w β W₀ h₀ 0 = h₀ := rfl
  rw [h0, hc] at hpv
  linarith

/-- **The log rule** (O&R (73)-style, cf. §7.1.2.2): the candidate consumes the fraction
`1 - β` of total wealth, `c*_t = (1-β)(R_t h*_t + H_t)` with human wealth
`H_t = ∑_{s ≥ t} (q_s/q_t) w_s`, which depends on prices only. -/
theorem cStar_rule {R w : ℕ → ℝ} {β W₀ h₀ : ℝ} (hR : ∀ t, 0 < R t)
    (hsum : Summable (fun t => disc R t * w t))
    (hW : W₀ = R 0 * h₀ + ∑' t, disc R t * w t) (t : ℕ) :
    cStar R β W₀ t = (1 - β) * (R t * hStar R w β W₀ h₀ t +
      (∑' s, disc R (s + t) * w (s + t)) / disc R t) := by
  have h := hStar_pv (β := β) hR hsum hW t
  have hq := disc_pos hR t
  unfold cStar
  field_simp
  linear_combination (β - 1) * h

/-- **Optimality of the log rule, genuine infinite horizon** (the log consumer of O&R §7.1.2
facing an arbitrary price path): if the candidate never borrows (`h*_t ≥ 0`), then for every
plan with `h_t ≥ 0`, `c_t > 0` obeying the budget from `h₀`,
`∑_{t<T} βᵗ log c_t ≤ ∑_{t<T} βᵗ log c*_t + βᵀ/(1-β)`, so `∑ βᵗ log c_t ≤ ∑ βᵗ log c*_t` when
both converge. -/
theorem log_rule_partial {R w c h : ℕ → ℝ} {β W₀ h₀ : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hR : ∀ t, 0 < R t) (hw : ∀ t, 0 ≤ w t) (hsum : Summable (fun t => disc R t * w t))
    (hW : W₀ = R 0 * h₀ + ∑' t, disc R t * w t) (hW0 : 0 < W₀)
    (hc : ∀ t, 0 < c t) (hh : ∀ t, 0 ≤ h t) (hb : LBudget R w c h) (h0 : h 0 = h₀) (T : ℕ) :
    ∑ t ∈ range T, β ^ t * Real.log (c t) ≤
      ∑ t ∈ range T, β ^ t * Real.log (cStar R β W₀ t) + β ^ T / (1 - β) := by
  have h1b : 0 < 1 - β := by linarith
  have hcs : ∀ t, 0 < cStar R β W₀ t := fun t => by
    unfold cStar
    have := disc_pos hR t
    positivity
  set lam := 1 / ((1 - β) * W₀)
  have hsupp : ∀ t, β ^ t * Real.log (c t) ≤ β ^ t * Real.log (cStar R β W₀ t) +
      lam * (disc R t * c t - disc R t * cStar R β W₀ t) := by
    intro t
    have hl := Real.log_le_sub_one_of_pos (div_pos (hc t) (hcs t))
    rw [Real.log_div (hc t).ne' (hcs t).ne'] at hl
    have e : β ^ t * (c t / cStar R β W₀ t - 1) =
        lam * (disc R t * c t - disc R t * cStar R β W₀ t) := by
      simp only [lam]
      unfold cStar
      have := disc_pos hR t
      field_simp
    nlinarith [pow_pos hβ t]
  have hsumle := sum_le_sum fun t (_ : t ∈ range T) => hsupp t
  rw [sum_add_distrib, ← mul_sum, sum_sub_distrib, lbudget_pv hR hb T,
    lbudget_pv hR (hStar_budget R w β W₀ h₀) T, h0] at hsumle
  have hpvT := hStar_pv (β := β) hR hsum hW T
  have htail : 0 ≤ ∑' s, disc R (s + T) * w (s + T) :=
    tsum_nonneg fun s => mul_nonneg (disc_pos hR _).le (hw _)
  have hdT := disc_pos hR T
  have hRT := hR T
  have hlam : 0 < lam := by simp only [lam]; positivity
  have hmain : lam * (disc R T * R T * hStar R w β W₀ h₀ T) ≤ β ^ T / (1 - β) := by
    rw [hpvT]
    simp only [lam]
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) h1b]
    nlinarith [pow_pos hβ T]
  have : 0 ≤ lam * (disc R T * R T * h T) := by
    have := hh T
    positivity
  simp only [hStar] at hsumle
  nlinarith

/-- The candidate's utility converges when returns are bounded, `0 < R_l ≤ R_t ≤ R_u`. -/
theorem cStar_summable {R : ℕ → ℝ} {β W₀ Rl Ru : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hW0 : 0 < W₀) (hRl : 0 < Rl) (hRb : ∀ t, Rl ≤ R t ∧ R t ≤ Ru) :
    Summable (fun t => β ^ t * Real.log (cStar R β W₀ t)) := by
  have hR : ∀ t, 0 < R t := fun t => lt_of_lt_of_le hRl (hRb t).1
  set K := |Real.log Rl| + |Real.log Ru|
  have hlogR : ∀ t, |Real.log (R t)| ≤ K := by
    intro t
    have hRu : 0 < Ru := lt_of_lt_of_le (hR t) (hRb t).2
    have l1 := Real.log_le_log hRl (hRb t).1
    have l2 := Real.log_le_log (hR t) (hRb t).2
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log Rl), abs_nonneg (Real.log Ru)]
    · linarith [le_abs_self (Real.log Ru), abs_nonneg (Real.log Rl)]
  have hdisc : ∀ t, |Real.log (disc R t)| ≤ t * K := by
    intro t
    induction t with
    | zero => simp [disc]
    | succ t ih =>
      simp only [disc]
      rw [Real.log_div (disc_pos hR t).ne' (hR _).ne']
      calc |Real.log (disc R t) - Real.log (R (t + 1))|
          ≤ |Real.log (disc R t)| + |Real.log (R (t + 1))| := abs_sub _ _
        _ ≤ t * K + K := add_le_add ih (hlogR _)
        _ = ((t + 1 : ℕ) : ℝ) * K := by push_cast; ring
  have h1b : 0 < 1 - β := by linarith
  set C0 := |Real.log ((1 - β) * W₀)| + |Real.log β| + K
  have hbound : ∀ t, ‖β ^ t * Real.log (cStar R β W₀ t)‖ ≤
      β ^ t * |Real.log ((1 - β) * W₀)| + ((t : ℝ) ^ 1 * β ^ t) * (|Real.log β| + K) := by
    intro t
    have hq := disc_pos hR t
    unfold cStar
    rw [Real.log_div (by positivity) hq.ne', Real.log_mul (by positivity)
      (pow_pos hβ t).ne', Real.log_pow, Real.norm_eq_abs, abs_mul,
      abs_of_pos (pow_pos hβ t)]
    have := hdisc t
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have h1 : |Real.log ((1 - β) * W₀) + t * Real.log β - Real.log (disc R t)| ≤
        |Real.log ((1 - β) * W₀)| + t * |Real.log β| + t * K := by
      calc _ ≤ |Real.log ((1 - β) * W₀) + t * Real.log β| + |Real.log (disc R t)| :=
            abs_sub _ _
        _ ≤ |Real.log ((1 - β) * W₀)| + |t * Real.log β| + |Real.log (disc R t)| := by
            gcongr; exact abs_add_le _ _
        _ ≤ _ := by rw [abs_mul, abs_of_nonneg ht]; linarith
    calc β ^ t * |Real.log ((1 - β) * W₀) + t * Real.log β - Real.log (disc R t)|
        ≤ β ^ t * (|Real.log ((1 - β) * W₀)| + t * |Real.log β| + t * K) :=
          mul_le_mul_of_nonneg_left h1 (pow_pos hβ t).le
      _ = _ := by ring
  have hn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ]; exact hβ1
  exact Summable.of_norm_bounded (((summable_geometric_of_lt_one hβ.le hβ1).mul_right _).add
    ((summable_pow_mul_geometric_of_norm_lt_one 1 hn).mul_right _)) hbound

/-- **The log rule is optimal over the infinite horizon**: under bounded returns, summable
human wealth and no borrowing by the candidate, `∑ βᵗ log c_t ≤ ∑ βᵗ log c*_t` for every
feasible plan with convergent utility. -/
theorem log_rule_optimal {R w c h : ℕ → ℝ} {β W₀ h₀ Rl Ru : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hRl : 0 < Rl) (hRb : ∀ t, Rl ≤ R t ∧ R t ≤ Ru) (hw : ∀ t, 0 ≤ w t)
    (hsum : Summable (fun t => disc R t * w t))
    (hW : W₀ = R 0 * h₀ + ∑' t, disc R t * w t) (hW0 : 0 < W₀)
    (hc : ∀ t, 0 < c t) (hh : ∀ t, 0 ≤ h t) (hb : LBudget R w c h) (h0 : h 0 = h₀)
    (hs : Summable (fun t => β ^ t * Real.log (c t))) :
    ∑' t, β ^ t * Real.log (c t) ≤ ∑' t, β ^ t * Real.log (cStar R β W₀ t) := by
  have hR : ∀ t, 0 < R t := fun t => lt_of_lt_of_le hRl (hRb t).1
  have hss := cStar_summable (R := R) hβ hβ1 hW0 hRl hRb
  have htail : Tendsto (fun T : ℕ => β ^ T / (1 - β)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).div_const (1 - β)
  have h2 := hss.hasSum.tendsto_sum_nat.add htail
  rw [add_zero] at h2
  exact le_of_tendsto_of_tendsto hs.hasSum.tendsto_sum_nat h2
    (Eventually.of_forall fun T => log_rule_partial hβ hβ1 hR hw hsum hW hW0 hc hh hb h0 T)

/-! ## Natives and immigrants never converge (O&R p. 452, made precise) -/

/-- **The skill gap between two log consumers facing the same prices** grows at `βR_t`:
`h*^N_{t+1} - h*^M_{t+1} = β R_t (h*^N_t - h*^M_t)` (natives and immigrants tilt consumption
identically, fn 14). -/
theorem skill_gap {R w : ℕ → ℝ} {β WN WM hN hM : ℝ} (hR : ∀ t, 0 < R t)
    (hsum : Summable (fun t => disc R t * w t))
    (hWN : WN = R 0 * hN + ∑' t, disc R t * w t) (hWM : WM = R 0 * hM + ∑' t, disc R t * w t)
    (t : ℕ) :
    hStar R w β WN hN (t + 1) - hStar R w β WM hM (t + 1) =
      β * R t * (hStar R w β WN hN t - hStar R w β WM hM t) := by
  simp only [hStar]
  rw [cStar_rule hR hsum hWN t, cStar_rule hR hsum hWM t]
  ring

/-- **Immigrants never catch up; natives end up above `h̄`** (O&R p. 452, "the steady state
will have `h^N > h̄ > h^M`"), conditional on the transition staying below `h̄`, which the book
takes from Fig. 7.8. Suppose the skill gap obeys `gap_{t+1} = βR_t gap_t` with
`R_t = 1 + f'(h_t) - δ`, `gap_0 = h̄` (natives at `h̄`, immigrants at 0), per-capita capital
`h_t = (N h^N_t + M h^M_t)/(N+M) ≤ h̄`, and `f'(h̄) = (1-β)/β + δ`. Then `gap_t ≥ h̄` for all
`t`, immigrants stay at or below `Mh̄/(N+M) < h̄` at every date, and natives hold at least
`h_t + Mh̄/(N+M)`; so if `h_t → h̄`, eventually `h^N_t > h̄`. -/
theorem natives_immigrants_diverge (T : Technology f f') {β δ N M hbar : ℝ}
    {h hN hM : ℕ → ℝ} (hβ : 0 < β) (hN0 : 0 < N) (hM0 : 0 < M) (hhb : 0 < hbar)
    (hss : f' hbar = (1 - β) / β + δ) (hpos : ∀ t, 0 < h t) (hle : ∀ t, h t ≤ hbar)
    (hagg : ∀ t, h t = (N * hN t + M * hM t) / (N + M))
    (hgap : ∀ t, hN (t + 1) - hM (t + 1) = β * (1 + f' (h t) - δ) * (hN t - hM t))
    (hgap0 : hN 0 - hM 0 = hbar) :
    (∀ t, hbar ≤ hN t - hM t) ∧ (∀ t, hM t ≤ M * hbar / (N + M)) ∧
      M * hbar / (N + M) < hbar ∧ (∀ t, h t + M * hbar / (N + M) ≤ hN t) ∧
      (Tendsto h atTop (𝓝 hbar) → ∀ᶠ t in atTop, hbar < hN t) := by
  have hNM : 0 < N + M := by linarith
  have hfac : ∀ t, 1 ≤ β * (1 + f' (h t) - δ) := by
    intro t
    have hd : f' hbar ≤ f' (h t) := by
      rcases eq_or_lt_of_le (hle t) with h1 | h1
      · rw [h1]
      · exact (T.deriv_strictAnti (hpos t) h1).le
    rw [hss] at hd
    have : β * (1 + ((1 - β) / β + δ) - δ) = 1 := by field_simp; ring
    nlinarith
  have hg : ∀ t, hbar ≤ hN t - hM t := by
    intro t
    induction t with
    | zero => rw [hgap0]
    | succ t ih =>
      rw [hgap t]
      nlinarith [hfac t]
  have hMle : ∀ t, hM t ≤ M * hbar / (N + M) := by
    intro t
    have e := hagg t
    have := hg t
    have := hle t
    rw [le_div_iff₀ hNM]
    rw [eq_div_iff hNM.ne'] at e
    nlinarith
  have hNge : ∀ t, h t + M * hbar / (N + M) ≤ hN t := by
    intro t
    have e := hagg t
    have := hg t
    rw [eq_div_iff hNM.ne'] at e
    have : h t + M * hbar / (N + M) = (h t * (N + M) + M * hbar) / (N + M) := by field_simp
    rw [this, div_le_iff₀ hNM]
    nlinarith
  have hlt : M * hbar / (N + M) < hbar := by
    rw [div_lt_iff₀ hNM]
    nlinarith
  refine ⟨hg, hMle, hlt, hNge, fun hlim => ?_⟩
  have hpos' : 0 < M * hbar / (N + M) := by positivity
  have := hlim.eventually (lt_mem_nhds (show hbar - M * hbar / (N + M) < hbar by linarith))
  filter_upwards [this] with t ht
  linarith [hNge t]

/-- **Natives lose nothing only when immigrants bring the same skills** (O&R p. 453): the
impact gain `N[f(h₀) + f'(h₀)(h̄ - h₀) - f(h̄)]` is zero iff `h₀ = h̄`, and positive
otherwise, whether `h₀ < h̄` (unskilled) or `h₀ > h̄` (skilled). -/
theorem impact_zero_iff (T : Technology f f') {N h₀ hbar : ℝ} (hN : 0 < N) (h₀p : 0 < h₀)
    (hhb : 0 < hbar) :
    (N * (f h₀ + f' h₀ * (hbar - h₀) - f hbar) = 0 ↔ h₀ = hbar) ∧
      (h₀ ≠ hbar → 0 < N * (f h₀ + f' h₀ * (hbar - h₀) - f hbar)) := by
  have hpos : h₀ ≠ hbar → 0 < N * (f h₀ + f' h₀ * (hbar - h₀) - f hbar) := fun hne =>
    mul_pos hN (by linarith [T.tangent_lt h₀p hhb.le (Ne.symm hne)])
  refine ⟨⟨fun h0 => ?_, fun h => by rw [h]; ring⟩, hpos⟩
  by_contra hne
  linarith [hpos hne]

/-- **Utility without immigration** (O&R p. 452): at the steady state the native consumes
`c̄ = f(h̄) - δh̄` forever, with lifetime utility `log c̄/(1-β)`. -/
theorem no_immigration_utility {β δ hbar : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    wageU f f' hbar + (f' hbar - δ) * hbar = f hbar - δ * hbar ∧
      HasSum (fun t : ℕ => β ^ t * Real.log (f hbar - δ * hbar))
        (Real.log (f hbar - δ * hbar) / (1 - β)) := by
  refine ⟨by unfold wageU; ring, ?_⟩
  have := (hasSum_geometric_of_lt_one hβ.le hβ1).mul_right (Real.log (f hbar - δ * hbar))
  convert this using 1
  field_simp

/-- **The native's optimum strictly beats no immigration** (O&R p. 452, in full): along a
post-immigration path `h_t ∈ [a, b]` (`a > 0`, `h₀ ≠ h̄`) with returns
`R_t = 1 + f'(h_t) - δ ∈ [R_l, R_u]`, `R_l > 0`, the native's log-rule plan from `h̄`, when it
never borrows, is optimal and gives utility strictly above `log c̄/(1-β)`. -/
theorem native_optimum_gain (T : Technology f f') {β δ hbar a b Rl Ru W₀ : ℝ} {h : ℕ → ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hhb : 0 < hbar) (hss : f' hbar = (1 - β) / β + δ)
    (ha : 0 < a) (hbnd : ∀ t, a ≤ h t ∧ h t ≤ b) (h0 : h 0 ≠ hbar) (hRl : 0 < Rl)
    (hRb : ∀ t, Rl ≤ 1 + f' (h t) - δ ∧ 1 + f' (h t) - δ ≤ Ru)
    (hsum : Summable (fun t => disc (fun s => 1 + f' (h s) - δ) t * wageU f f' (h t)))
    (hW : W₀ = (1 + f' (h 0) - δ) * hbar +
      ∑' t, disc (fun s => 1 + f' (h s) - δ) t * wageU f f' (h t)) :
    Real.log (f hbar - δ * hbar) / (1 - β) <
      ∑' t, β ^ t * Real.log (cStar (fun s => 1 + f' (h s) - δ) β W₀ t) := by
  have hpos : ∀ t, 0 < h t := fun t => lt_of_lt_of_le ha (hbnd t).1
  obtain ⟨hs, hgain⟩ := natives_gain T hβ hβ1 hhb hss ha hbnd h0
  have hR : ∀ t, 0 < 1 + f' (h t) - δ := fun t => lt_of_lt_of_le hRl (hRb t).1
  have hw : ∀ t, 0 ≤ wageU f f' (h t) := fun t => (T.wage_pos (hpos t)).le
  have hcbar := steady_consumption_pos T hβ hβ1 hhb hss
  have hW0 : 0 < W₀ := by
    rw [hW]
    have : 0 ≤ ∑' t, disc (fun s => 1 + f' (h s) - δ) t * wageU f f' (h t) :=
      tsum_nonneg fun t => mul_nonneg (disc_pos hR t).le (hw t)
    have := hR 0
    positivity
  have hopt := log_rule_optimal (R := fun s => 1 + f' (h s) - δ) (w := fun s => wageU f f' (h s))
    (c := fun t => wageU f f' (h t) + (f' (h t) - δ) * hbar) (h := fun _ => hbar)
    hβ hβ1 hRl hRb hw hsum hW hW0
    (fun t => lt_of_lt_of_le hcbar (keep_plan T hhb hpos t).2.1) (fun _ => hhb.le)
    (fun t => (keep_plan T hhb hpos t).1) rfl hs
  linarith

/-- **Natives and immigrants following the log rule never converge** (O&R p. 452): combining
`skill_gap` (common prices, log rule) with `natives_immigrants_diverge`. Immigrants start with
`h^M_0 = 0` and natives with `h̄`. If both log-rule plans are the agents' choices and the
per-capita path stays below `h̄`, immigrants stay below `Mh̄/(N+M)` forever. -/
theorem immigrants_never_catch_up (T : Technology f f') {β δ N M hbar WN WM : ℝ}
    {h : ℕ → ℝ} (hβ : 0 < β) (hN0 : 0 < N) (hM0 : 0 < M) (hhb : 0 < hbar)
    (hss : f' hbar = (1 - β) / β + δ) (hpos : ∀ t, 0 < h t) (hle : ∀ t, h t ≤ hbar)
    (hR : ∀ t, 0 < 1 + f' (h t) - δ)
    (hsum : Summable (fun t => disc (fun s => 1 + f' (h s) - δ) t * wageU f f' (h t)))
    (hWN : WN = (1 + f' (h 0) - δ) * hbar +
      ∑' t, disc (fun s => 1 + f' (h s) - δ) t * wageU f f' (h t))
    (hWM : WM = (1 + f' (h 0) - δ) * 0 +
      ∑' t, disc (fun s => 1 + f' (h s) - δ) t * wageU f f' (h t))
    (hagg : ∀ t, h t = (N * hStar (fun s => 1 + f' (h s) - δ) (fun s => wageU f f' (h s)) β
      WN hbar t + M * hStar (fun s => 1 + f' (h s) - δ) (fun s => wageU f f' (h s)) β WM 0 t) /
      (N + M)) (t : ℕ) :
    hStar (fun s => 1 + f' (h s) - δ) (fun s => wageU f f' (h s)) β WM 0 t ≤
      M * hbar / (N + M) := by
  have hgap := fun t => skill_gap (R := fun s => 1 + f' (h s) - δ)
    (w := fun s => wageU f f' (h s)) (β := β) hR hsum hWN hWM t
  have := natives_immigrants_diverge T hβ hN0 hM0 hhb hss hpos hle hagg
    (fun t => by rw [hgap t]) (by simp [hStar])
  exact this.2.1 t

/-! ## When do immigrants never borrow? (exact condition) -/

/-- **Immigrants never borrow iff aggregate capital keeps pace with the skill gap**: with
natives at `h̄`, immigrants at `0`, per-capita `h_t = (Nh^N_t + Mh^M_t)/(N+M)` and the gap
recursion `gap_{t+1} = βR_t gap_t` (log rule, fn 14), immigrants' human capital is
`h^M_t = h_t - (N/(N+M)) h̄ ∏_{s<t} βR_s`; so `h^M_t ≥ 0` iff `h_t ≥ h₀ ∏_{s<t} βR_s`,
where `h₀ = Nh̄/(N+M)`. -/
theorem immigrants_nonneg_iff {β N M hbar : ℝ} {h hN hM R : ℕ → ℝ} (hN0 : 0 < N) (hM0 : 0 < M)
    (hagg : ∀ t, h t = (N * hN t + M * hM t) / (N + M))
    (hgap : ∀ t, hN (t + 1) - hM (t + 1) = β * R t * (hN t - hM t))
    (hgap0 : hN 0 - hM 0 = hbar) (t : ℕ) :
    hM t = h t - N / (N + M) * (hbar * ∏ s ∈ range t, (β * R s)) ∧
      (0 ≤ hM t ↔ N * hbar / (N + M) * ∏ s ∈ range t, (β * R s) ≤ h t) := by
  have hNM : 0 < N + M := by linarith
  have hg : ∀ t, hN t - hM t = hbar * ∏ s ∈ range t, (β * R s) := by
    intro t
    induction t with
    | zero => simp [hgap0]
    | succ t ih => rw [hgap t, ih, prod_range_succ]; ring
  have e : hM t = h t - N / (N + M) * (hbar * ∏ s ∈ range t, (β * R s)) := by
    rw [← hg t, hagg t]
    field_simp
    ring
  refine ⟨e, ?_⟩
  rw [e, sub_nonneg]
  constructor <;> intro h1 <;> [skip; skip] <;> (have : N / (N + M) * (hbar *
    ∏ s ∈ range t, (β * R s)) = N * hbar / (N + M) * ∏ s ∈ range t, (β * R s) := by ring) <;>
    linarith

/-! ## The Harberger triangle (O&R p. 453) -/

/-- The impact point `h₀(M) = Nh̄/(N+M)` tends to `h̄` as `M ↓ 0`. -/
theorem impact_point_tendsto {N hbar : ℝ} (hN : 0 < N) :
    Tendsto (fun M : ℝ => N * hbar / (N + M)) (𝓝[>] 0) (𝓝 hbar) := by
  have hc : ContinuousAt (fun M : ℝ => N * hbar / (N + M)) 0 :=
    continuousAt_const.div (continuousAt_const.add continuousAt_id) (by simp; linarith)
  have := hc.tendsto
  simp only [add_zero] at this
  rw [show N * hbar / N = hbar by field_simp] at this
  exact tendsto_nhdsWithin_of_tendsto_nhds this

/-- **The aggregate gain is second order** (O&R p. 453, "a Harberger triangle"): if `f'` is
continuous at `h̄`, the impact gain `N[f(h₀) + f'(h₀)(h̄ - h₀) - f(h̄)]`, with
`h₀ = Nh̄/(N+M)`, satisfies `gain(M)/M → 0` as `M ↓ 0`. -/
theorem harberger_gain_second_order (T : Technology f f') {N hbar : ℝ} (hN : 0 < N)
    (hhb : 0 < hbar) (hcont : ContinuousAt f' hbar) :
    Tendsto (fun M => N * (f (N * hbar / (N + M)) + f' (N * hbar / (N + M)) *
      (hbar - N * hbar / (N + M)) - f hbar) / M) (𝓝[>] 0) (𝓝 0) := by
  have hh0 := impact_point_tendsto (hbar := hbar) hN
  have hup : Tendsto (fun M : ℝ => N * hbar / (N + M) * (f' (N * hbar / (N + M)) - f' hbar))
      (𝓝[>] 0) (𝓝 0) := by
    have := hh0.mul ((hcont.tendsto.comp hh0).sub_const (f' hbar))
    rwa [sub_self, mul_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with M hM
    have hM0 : 0 < M := hM
    have h0 : 0 < N * hbar / (N + M) := by positivity
    have := T.tangent_le h0 hhb.le
    exact div_nonneg (mul_nonneg hN.le (by linarith)) hM0.le
  · filter_upwards [self_mem_nhdsWithin] with M hM
    have hM0 : 0 < M := hM
    have h0 : 0 < N * hbar / (N + M) := by positivity
    have ht := T.tangent_le hhb h0.le
    have e : hbar - N * hbar / (N + M) = M * hbar / (N + M) := by field_simp; ring
    rw [div_le_iff₀ hM0, e]
    have key : f (N * hbar / (N + M)) + f' (N * hbar / (N + M)) * (M * hbar / (N + M)) -
        f hbar ≤ (f' (N * hbar / (N + M)) - f' hbar) * (M * hbar / (N + M)) := by
      have : N * hbar / (N + M) - hbar = -(M * hbar / (N + M)) := by linarith
      rw [this] at ht
      linarith
    have := mul_le_mul_of_nonneg_left key hN.le
    calc N * (f (N * hbar / (N + M)) + f' (N * hbar / (N + M)) * (M * hbar / (N + M)) -
          f hbar) ≤ N * ((f' (N * hbar / (N + M)) - f' hbar) * (M * hbar / (N + M))) := this
      _ = N * hbar / (N + M) * (f' (N * hbar / (N + M)) - f' hbar) * M := by ring

/-- **The redistribution is first order** (O&R p. 453: "the distributional effect is generally
large compared to the overall welfare gain"): if `f'` has derivative `f'' < 0` at `h̄`, the
fall in natives' unskilled wage bill `N[w(h̄) - w(h₀(M))]` is first order in `M`, with
`N[w(h̄) - w(h₀(M))]/M → -h̄² f''(h̄) > 0`, while the net gain is `o(M)`
(`harberger_gain_second_order`). -/
theorem harberger_transfer_first_order (T : Technology f f') {N hbar f2 : ℝ} (hN : 0 < N)
    (hhb : 0 < hbar) (hd : HasDerivAt f' f2 hbar) (hf2 : f2 < 0) :
    Tendsto (fun M => N * (wageU f f' hbar - wageU f f' (N * hbar / (N + M))) / M)
      (𝓝[>] 0) (𝓝 (-(hbar ^ 2 * f2))) ∧ 0 < -(hbar ^ 2 * f2) := by
  refine ⟨?_, by nlinarith [sq_pos_of_pos hhb]⟩
  have hw : HasDerivAt (wageU f f') (-(hbar * f2)) hbar := by
    have h3 : HasDerivAt (fun y => f y - y * f' y) (f' hbar - (1 * f' hbar + hbar * f2)) hbar :=
      (T.deriv hbar hhb).sub ((hasDerivAt_id' hbar).mul hd)
    have e : f' hbar - (1 * f' hbar + hbar * f2) = -(hbar * f2) := by ring
    rw [e] at h3
    exact h3
  have hh : HasDerivAt (fun M : ℝ => N * hbar / (N + M)) (-(hbar / N)) 0 := by
    have hg : HasDerivAt (fun M : ℝ => N + M) 1 0 := (hasDerivAt_id' (0 : ℝ)).const_add N
    have hi := (hg.inv (by simp; linarith)).const_mul (N * hbar)
    convert hi using 1
    · funext M
      rw [div_eq_mul_inv]
      rfl
    · field_simp
      ring
  have hcomp : HasDerivAt (fun M : ℝ => wageU f f' (N * hbar / (N + M)))
      (-(hbar * f2) * -(hbar / N)) 0 := by
    have hw' : HasDerivAt (wageU f f') (-(hbar * f2)) (N * hbar / (N + 0)) := by
      rw [add_zero, show N * hbar / N = hbar by field_simp]
      exact hw
    exact hw'.comp 0 hh
  have hs := (hasDerivAt_iff_tendsto_slope_zero.mp hcomp).mono_left
    (nhdsWithin_mono _ (fun x (hx : x ∈ Set.Ioi (0 : ℝ)) => ne_of_gt hx))
  have := hs.const_mul (-N)
  refine (this.congr' ?_).trans ?_
  · filter_upwards [self_mem_nhdsWithin] with M hM
    simp only [zero_add, add_zero, smul_eq_mul]
    rw [show N * hbar / N = hbar by field_simp]
    field_simp
    ring
  · rw [show -N * (-(hbar * f2) * -(hbar / N)) = -(hbar ^ 2 * f2) by field_simp]

/-! ## The saddle path in closed form: `f(h) = h^α`, `δ = 1` (Fig. 7.8 constructed) -/

/-- The Cobb–Douglas technology `f(h) = h^α` (`0 < α < 1`) satisfies `Technology`. -/
theorem bm_technology {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    Technology (fun h => h ^ α) (fun h => α * h ^ (α - 1)) :=
  ⟨Real.strictConcaveOn_rpow hα hα1, fun h hh => Real.hasDerivAt_rpow_const (Or.inl hh.ne'),
    by simp [Real.zero_rpow hα.ne']⟩

/-- The steady state with `δ = 1`: `h̄ = (αβ)^{1/(1-α)}`, where `f'(h̄) = 1/β = (1-β)/β + δ`. -/
noncomputable def bmHbar (α β : ℝ) : ℝ := (α * β) ^ (1 / (1 - α))

/-- `α h̄^{α-1} = (1-β)/β + 1` (O&R's steady-state condition with `δ = 1`). -/
theorem bmHbar_spec {α β : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) :
    0 < bmHbar α β ∧ α * bmHbar α β ^ (α - 1) = (1 - β) / β + 1 := by
  have h1a : 0 < 1 - α := by linarith
  have hpos : 0 < bmHbar α β := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨hpos, ?_⟩
  unfold bmHbar
  rw [← Real.rpow_mul (by positivity), show 1 / (1 - α) * (α - 1) = -1 by field_simp; ring,
    Real.rpow_neg_one]
  field_simp
  ring

/-- **The saddle path** (log utility, `δ = 1`): `h_{t+1} = αβ h_t^α`. -/
noncomputable def bmPath (α β h₀ : ℝ) : ℕ → ℝ
  | 0 => h₀
  | t + 1 => α * β * bmPath α β h₀ t ^ α

/-- The saddle path stays positive. -/
theorem bmPath_pos {α β h₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hh₀ : 0 < h₀) (t : ℕ) :
    0 < bmPath α β h₀ t := by
  induction t with
  | zero => exact hh₀
  | succ t ih => simp only [bmPath]; have := Real.rpow_pos_of_pos ih α; positivity

/-- **The saddle path solves the per-capita system (39)–(40)** with `c_t = (1-αβ)h_t^α`:
`h_{t+1} - h_t = f(h_t) - δh_t - c_t` and `c_{t+1} = (1 + f'(h_{t+1}) - δ)βc_t` (`δ = 1`). -/
theorem bmPath_system {α β h₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hh₀ : 0 < h₀) (t : ℕ) :
    bmPath α β h₀ (t + 1) - bmPath α β h₀ t = bmPath α β h₀ t ^ α - 1 * bmPath α β h₀ t -
        (1 - α * β) * bmPath α β h₀ t ^ α ∧
      (1 - α * β) * bmPath α β h₀ (t + 1) ^ α =
        (1 + α * bmPath α β h₀ (t + 1) ^ (α - 1) - 1) * β *
          ((1 - α * β) * bmPath α β h₀ t ^ α) := by
  have h1 := bmPath_pos hα hβ hh₀ (t + 1)
  constructor
  · simp only [bmPath]
    ring
  · have e : bmPath α β h₀ (t + 1) ^ (α - 1) * bmPath α β h₀ (t + 1) =
        bmPath α β h₀ (t + 1) ^ α := by rw [← Real.rpow_add_one h1.ne', sub_add_cancel]
    have hs : bmPath α β h₀ (t + 1) = α * β * bmPath α β h₀ t ^ α := rfl
    have key : bmPath α β h₀ (t + 1) ^ α = α * β * bmPath α β h₀ (t + 1) ^ (α - 1) *
        bmPath α β h₀ t ^ α := by
      have := congrArg (fun y => bmPath α β h₀ (t + 1) ^ (α - 1) * y) hs
      rw [← e, this]
      ring
    linear_combination (1 - α * β) * key

/-- **Monotone convergence along the saddle path** (Fig. 7.8): from `0 < h₀ < h̄` the path
rises strictly, stays below `h̄`, and converges to `h̄`. -/
theorem bmPath_converges {α β h₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hh₀ : 0 < h₀) (hlt : h₀ < bmHbar α β) :
    (∀ t, bmPath α β h₀ t < bmPath α β h₀ (t + 1)) ∧ (∀ t, bmPath α β h₀ t < bmHbar α β) ∧
      Tendsto (bmPath α β h₀) atTop (𝓝 (bmHbar α β)) := by
  obtain ⟨hb, hspec⟩ := bmHbar_spec hα hα1 hβ
  have h1a : 0 < 1 - α := by linarith
  have hbfix : α * β * bmHbar α β ^ α = bmHbar α β := by
    have e : bmHbar α β ^ α = bmHbar α β ^ (α - 1) * bmHbar α β := by
      rw [← Real.rpow_add_one hb.ne', sub_add_cancel]
    rw [e]
    have : α * bmHbar α β ^ (α - 1) = 1 / β := by rw [hspec]; field_simp; ring
    calc α * β * (bmHbar α β ^ (α - 1) * bmHbar α β) =
        β * (α * bmHbar α β ^ (α - 1)) * bmHbar α β := by ring
      _ = bmHbar α β := by rw [this]; field_simp
  have hbelow : ∀ t, bmPath α β h₀ t < bmHbar α β := by
    intro t
    induction t with
    | zero => exact hlt
    | succ t ih =>
      simp only [bmPath]
      rw [← hbfix]
      have := Real.rpow_lt_rpow (bmPath_pos hα hβ hh₀ t).le ih hα
      nlinarith [mul_pos hα hβ]
  refine ⟨fun t => ?_, hbelow, ?_⟩
  · have ht := bmPath_pos hα hβ hh₀ t
    have hp := Real.rpow_lt_rpow_of_neg ht (hbelow t) (by linarith : α - 1 < 0)
    have e : bmPath α β h₀ t ^ α = bmPath α β h₀ t ^ (α - 1) * bmPath α β h₀ t := by
      rw [← Real.rpow_add_one ht.ne', sub_add_cancel]
    have hq : 1 / β < α * bmPath α β h₀ t ^ (α - 1) := by
      rw [show 1 / β = α * bmHbar α β ^ (α - 1) by rw [hspec]; field_simp; ring]
      exact mul_lt_mul_of_pos_left hp hα
    change bmPath α β h₀ t < α * β * bmPath α β h₀ t ^ α
    rw [e]
    have : 1 < β * (α * bmPath α β h₀ t ^ (α - 1)) := by
      rw [div_lt_iff₀ hβ] at hq
      linarith
    nlinarith
  · -- log-linear closed form
    set lb := Real.log (bmHbar α β)
    have hlb : lb * (1 - α) = Real.log (α * β) := by
      simp only [lb, bmHbar]
      rw [Real.log_rpow (by positivity)]
      field_simp
    have hlog : ∀ t, Real.log (bmPath α β h₀ t) = lb + α ^ t * (Real.log h₀ - lb) := by
      intro t
      induction t with
      | zero => simp [bmPath]
      | succ t ih =>
        have ht := bmPath_pos hα hβ hh₀ t
        simp only [bmPath]
        rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos ht α).ne',
          Real.log_rpow ht, ih, pow_succ]
        linear_combination (-1 : ℝ) * hlb
    have hl : Tendsto (fun t => Real.log (bmPath α β h₀ t)) atTop (𝓝 lb) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hα.le hα1).mul_const
        (Real.log h₀ - lb)).const_add lb
      rw [zero_mul, add_zero] at this
      exact this.congr fun t => (hlog t).symm
    have := (Real.continuous_exp.tendsto lb).comp hl
    rw [Real.exp_log hb] at this
    exact this.congr fun t => by simp [Real.exp_log (bmPath_pos hα hβ hh₀ t)]

/-- Market prices along the saddle path: `R_{t+1} = α h_{t+1}^{α-1} = h_{t+1}^α/(β h_t^α)`, so
the discount factors are `q_t = βᵗ h₀^α/h_t^α` and the discounted wage is
`q_t w_t = (1-α)βᵗ h₀^α`, with `w_t = (1-α)h_t^α`. -/
theorem bm_disc {α β h₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hh₀ : 0 < h₀) (t : ℕ) :
    disc (fun s => α * bmPath α β h₀ s ^ (α - 1)) t =
      β ^ t * h₀ ^ α / bmPath α β h₀ t ^ α := by
  induction t with
  | zero => simp [disc, bmPath, div_self (Real.rpow_pos_of_pos hh₀ α).ne']
  | succ t ih =>
    have ht := bmPath_pos hα hβ hh₀ t
    have ht1 := bmPath_pos hα hβ hh₀ (t + 1)
    simp only [disc]
    rw [ih]
    have e : bmPath α β h₀ (t + 1) ^ (α - 1) * bmPath α β h₀ (t + 1) =
        bmPath α β h₀ (t + 1) ^ α := by rw [← Real.rpow_add_one ht1.ne', sub_add_cancel]
    have hs : bmPath α β h₀ (t + 1) = α * β * bmPath α β h₀ t ^ α := rfl
    have hR : α * bmPath α β h₀ (t + 1) ^ (α - 1) =
        bmPath α β h₀ (t + 1) ^ α / (β * bmPath α β h₀ t ^ α) := by
      have hta := Real.rpow_pos_of_pos ht α
      have := congrArg (fun y => bmPath α β h₀ (t + 1) ^ (α - 1) * y) hs
      rw [eq_div_iff (by positivity), ← e]
      linear_combination -this
    rw [hR, pow_succ]
    have := Real.rpow_pos_of_pos ht α
    have := Real.rpow_pos_of_pos ht1 α
    field_simp

/-- The unskilled wage with `f(h) = h^α` is `w(h) = (1-α)h^α`. -/
theorem bm_wage {α h : ℝ} (hh : 0 < h) :
    wageU (fun h => h ^ α) (fun h => α * h ^ (α - 1)) h = (1 - α) * h ^ α := by
  unfold wageU
  have : h * h ^ (α - 1) = h ^ α := by
    rw [mul_comm, ← Real.rpow_add_one hh.ne', sub_add_cancel]
  linear_combination (-α) * this

/-- Human wealth of a zero-wealth agent along the saddle path:
`∑ q_t w_t = (1-α)h₀^α/(1-β)`. -/
theorem bm_human_wealth {α β h₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1) (hh₀ : 0 < h₀) :
    HasSum (fun t => disc (fun s => α * bmPath α β h₀ s ^ (α - 1)) t *
      ((1 - α) * bmPath α β h₀ t ^ α)) ((1 - α) * h₀ ^ α / (1 - β)) := by
  have h := (hasSum_geometric_of_lt_one hβ.le hβ1).mul_left ((1 - α) * h₀ ^ α)
  convert h using 1
  · funext t
    rw [bm_disc hα hβ hh₀ t]
    have := Real.rpow_pos_of_pos (bmPath_pos hα hβ hh₀ t) α
    field_simp
  · field_simp

/-- **Immigrants arriving with no human capital never borrow — they hold exactly zero**
(the knife edge of O&R p. 452 in the closed-form case): the zero-wealth log-rule plan
consumes the wage every period, `c*_t = w_t = (1-α)h_t^α`, and `h*_t = 0` for all `t`. -/
theorem bm_immigrant_plan {α β h₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1)
    (hh₀ : 0 < h₀) (t : ℕ) :
    cStar (fun s => α * bmPath α β h₀ s ^ (α - 1)) β ((1 - α) * h₀ ^ α / (1 - β)) t =
        (1 - α) * bmPath α β h₀ t ^ α ∧
      hStar (fun s => α * bmPath α β h₀ s ^ (α - 1)) (fun s => (1 - α) * bmPath α β h₀ s ^ α)
        β ((1 - α) * h₀ ^ α / (1 - β)) 0 t = 0 := by
  have hc : ∀ t, cStar (fun s => α * bmPath α β h₀ s ^ (α - 1)) β
      ((1 - α) * h₀ ^ α / (1 - β)) t = (1 - α) * bmPath α β h₀ t ^ α := by
    intro t
    unfold cStar
    rw [bm_disc hα hβ hh₀ t]
    have := Real.rpow_pos_of_pos (bmPath_pos hα hβ hh₀ t) α
    have := Real.rpow_pos_of_pos hh₀ α
    have : (1 - β) ≠ 0 := by linarith
    field_simp
  refine ⟨hc t, ?_⟩
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [hStar] at ih ⊢
    rw [ih, hc t]
    ring

/-- **Natives end up above `h̄`** (closed-form case): the natives' log-rule plan from `h̄`
satisfies `h*^N_t = ((N+M)/N) h_t`, so per-capita aggregation holds exactly with immigrants
at zero, and `h*^N_t → ((N+M)/N)h̄ > h̄`. -/
theorem bm_native_plan {α β N M h₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1)
    (hh₀ : 0 < h₀) (t : ℕ) :
    hStar (fun s => α * bmPath α β h₀ s ^ (α - 1)) (fun s => (1 - α) * bmPath α β h₀ s ^ α) β
        (α * bmPath α β h₀ 0 ^ (α - 1) * ((N + M) / N * h₀) + (1 - α) * h₀ ^ α / (1 - β))
        ((N + M) / N * h₀) t = (N + M) / N * bmPath α β h₀ t := by
  set R := fun s => α * bmPath α β h₀ s ^ (α - 1) with hR
  set w := fun s => (1 - α) * bmPath α β h₀ s ^ α with hw
  have hRpos : ∀ t, 0 < R t := fun t => by
    simp only [hR]
    have := Real.rpow_pos_of_pos (bmPath_pos hα hβ hh₀ t) (α - 1)
    positivity
  have hsum := (bm_human_wealth hα hβ hβ1 hh₀).summable
  have htsum := (bm_human_wealth hα hβ hβ1 hh₀).tsum_eq
  have hWN : α * bmPath α β h₀ 0 ^ (α - 1) * ((N + M) / N * h₀) + (1 - α) * h₀ ^ α / (1 - β) =
      R 0 * ((N + M) / N * h₀) + ∑' t, disc R t * w t := by
    rw [htsum]
  have hWM : (1 - α) * h₀ ^ α / (1 - β) = R 0 * 0 + ∑' t, disc R t * w t := by
    rw [htsum]
    ring
  induction t with
  | zero => rfl
  | succ t ih =>
    have hg := skill_gap (β := β) hRpos hsum hWN hWM t
    rw [(bm_immigrant_plan hα hβ hβ1 hh₀ (t + 1)).2, (bm_immigrant_plan hα hβ hβ1 hh₀ t).2,
      sub_zero, sub_zero, ih] at hg
    rw [hg]
    have ht := bmPath_pos hα hβ hh₀ t
    have e : bmPath α β h₀ t ^ (α - 1) * bmPath α β h₀ t = bmPath α β h₀ t ^ α := by
      rw [← Real.rpow_add_one ht.ne', sub_add_cancel]
    simp only [hR]
    change β * (α * bmPath α β h₀ t ^ (α - 1)) * ((N + M) / N * bmPath α β h₀ t) =
      (N + M) / N * (α * β * bmPath α β h₀ t ^ α)
    rw [← e]
    ring

/-- **Both log-rule plans are optimal** along the saddle path (closed-form case), for every
initial skill level `ĥ ≥ 0` (immigrants `ĥ = 0`, natives `ĥ = h̄`), provided the plan never
borrows: no feasible plan with convergent utility does better. -/
theorem bm_plan_optimal {α β h₀ ĥ : ℝ} {c h : ℕ → ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hh₀ : 0 < h₀) (hlt : h₀ < bmHbar α β) (hĥ : 0 ≤ ĥ)
    (hc : ∀ t, 0 < c t) (hh : ∀ t, 0 ≤ h t)
    (hb : LBudget (fun s => α * bmPath α β h₀ s ^ (α - 1))
      (fun s => (1 - α) * bmPath α β h₀ s ^ α) c h) (h0 : h 0 = ĥ)
    (hs : Summable (fun t => β ^ t * Real.log (c t))) :
    ∑' t, β ^ t * Real.log (c t) ≤ ∑' t, β ^ t * Real.log (cStar
      (fun s => α * bmPath α β h₀ s ^ (α - 1)) β
      (α * bmPath α β h₀ 0 ^ (α - 1) * ĥ + (1 - α) * h₀ ^ α / (1 - β)) t) := by
  obtain ⟨hinc, hbelow, -⟩ := bmPath_converges hα hα1 hβ hh₀ hlt
  obtain ⟨hb0, -⟩ := bmHbar_spec hα hα1 hβ
  have hge : ∀ t, h₀ ≤ bmPath α β h₀ t := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ t ih => exact ih.trans (hinc t).le
  have hRb : ∀ t, α * bmHbar α β ^ (α - 1) ≤ α * bmPath α β h₀ t ^ (α - 1) ∧
      α * bmPath α β h₀ t ^ (α - 1) ≤ α * h₀ ^ (α - 1) := by
    intro t
    have ht := bmPath_pos hα hβ hh₀ t
    exact ⟨mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ht (hbelow t).le
      (by linarith)) hα.le, mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hh₀
      (hge t) (by linarith)) hα.le⟩
  have hsum := (bm_human_wealth hα hβ hβ1 hh₀).summable
  have htsum := (bm_human_wealth hα hβ hβ1 hh₀).tsum_eq
  have hR0 : 0 < α * bmPath α β h₀ 0 ^ (α - 1) := by
    have := Real.rpow_pos_of_pos hh₀ (α - 1)
    simp only [bmPath]
    positivity
  have hW0 : 0 < α * bmPath α β h₀ 0 ^ (α - 1) * ĥ + (1 - α) * h₀ ^ α / (1 - β) := by
    have := Real.rpow_pos_of_pos hh₀ α
    have : 0 < 1 - α := by linarith
    have : 0 < 1 - β := by linarith
    have : 0 ≤ α * bmPath α β h₀ 0 ^ (α - 1) * ĥ := mul_nonneg hR0.le hĥ
    have : 0 < (1 - α) * h₀ ^ α / (1 - β) := by positivity
    linarith
  exact log_rule_optimal hβ hβ1 (by have := Real.rpow_pos_of_pos hb0 (α - 1); positivity) hRb
    (fun t => by have := Real.rpow_pos_of_pos (bmPath_pos hα hβ hh₀ t) α
                 have : 0 < 1 - α := by linarith
                 positivity) hsum (by rw [htsum]) hW0 hc hh hb h0 hs

/-- **Newborns and immigrants lose, natives gain** (O&R p. 453, closed-form case): an agent
entering with no human capital (a newborn, or an immigrant) consumes the wage
`(1-α)h_t^α < (1-α)h̄^α` every period. Its lifetime utility is therefore strictly below
`log w̄/(1-β)`, the utility of a zero-wealth agent without immigration. -/
theorem bm_newborn_loses {α β h₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hh₀ : 0 < h₀) (hlt : h₀ < bmHbar α β) :
    Summable (fun t => β ^ t * Real.log ((1 - α) * bmPath α β h₀ t ^ α)) ∧
      ∑' t, β ^ t * Real.log ((1 - α) * bmPath α β h₀ t ^ α) <
        Real.log ((1 - α) * bmHbar α β ^ α) / (1 - β) := by
  obtain ⟨hinc, hbelow, -⟩ := bmPath_converges hα hα1 hβ hh₀ hlt
  obtain ⟨hb0, -⟩ := bmHbar_spec hα hα1 hβ
  have h1a : 0 < 1 - α := by linarith
  have hge : ∀ t, h₀ ≤ bmPath α β h₀ t := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ t ih => exact ih.trans (hinc t).le
  have hwpos : ∀ t, 0 < (1 - α) * bmPath α β h₀ t ^ α := fun t => by
    have := Real.rpow_pos_of_pos (bmPath_pos hα hβ hh₀ t) α
    positivity
  have hlo : ∀ t, Real.log ((1 - α) * h₀ ^ α) ≤ Real.log ((1 - α) * bmPath α β h₀ t ^ α) :=
    fun t => Real.log_le_log (by have := Real.rpow_pos_of_pos hh₀ α; positivity)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hh₀.le (hge t) hα.le) h1a.le)
  have hhi : ∀ t, Real.log ((1 - α) * bmPath α β h₀ t ^ α) <
      Real.log ((1 - α) * bmHbar α β ^ α) :=
    fun t => Real.log_lt_log (hwpos t)
      (mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (bmPath_pos hα hβ hh₀ t).le (hbelow t) hα) h1a)
  set K := |Real.log ((1 - α) * h₀ ^ α)| + |Real.log ((1 - α) * bmHbar α β ^ α)|
  have hgeo := summable_geometric_of_lt_one hβ.le hβ1
  have hsum : Summable (fun t => β ^ t * Real.log ((1 - α) * bmPath α β h₀ t ^ α)) := by
    refine Summable.of_norm_bounded (hgeo.mul_right K) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ t)]
    apply mul_le_mul_of_nonneg_left _ (pow_pos hβ t).le
    rw [abs_le]
    constructor
    · linarith [hlo t, neg_abs_le (Real.log ((1 - α) * h₀ ^ α)),
        abs_nonneg (Real.log ((1 - α) * bmHbar α β ^ α))]
    · linarith [(hhi t).le, le_abs_self (Real.log ((1 - α) * bmHbar α β ^ α)),
        abs_nonneg (Real.log ((1 - α) * h₀ ^ α))]
  refine ⟨hsum, ?_⟩
  have hbase : ∑' t : ℕ, β ^ t * Real.log ((1 - α) * bmHbar α β ^ α) =
      Real.log ((1 - α) * bmHbar α β ^ α) / (1 - β) := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ.le hβ1]
    field_simp
  have hbsum := hgeo.mul_right (Real.log ((1 - α) * bmHbar α β ^ α))
  have hd := hbsum.sub hsum
  have hle := hd.le_tsum 0 (fun j _ => by
    have := hhi j
    nlinarith [pow_pos hβ j])
  rw [hbsum.tsum_sub hsum, hbase] at hle
  have h0 := hhi 0
  simp only [pow_zero, one_mul] at hle
  linarith

/-- **Newborns lose human wealth along any transition below `h̄`** (O&R p. 453, general
technology): if `h_t ≤ h̄` for all `t` with `h₀ < h̄`, then wages are lower
(`w(h_t) ≤ w(h̄)`, strictly at 0) and returns higher (`R_t = 1 + f'(h_t) - δ ≥ 1/β`). So the
human wealth of an agent born at date 0, `∑ q_t w_t`, is strictly below the no-immigration
value `w(h̄)/(1-β)`. (The utility comparison is not implied in general, because the newborn
also earns the higher return; in the closed-form case it holds — `bm_newborn_loses`.) -/
theorem newborn_human_wealth_lower (T : Technology f f') {β δ hbar : ℝ} {h : ℕ → ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hss : f' hbar = (1 - β) / β + δ)
    (hpos : ∀ t, 0 < h t) (hle : ∀ t, h t ≤ hbar) (h0 : h 0 < hbar)
    (hsum : Summable (fun t => disc (fun s => 1 + f' (h s) - δ) t * wageU f f' (h t))) :
    ∑' t, disc (fun s => 1 + f' (h s) - δ) t * wageU f f' (h t) <
      wageU f f' hbar / (1 - β) := by
  have hR : ∀ t, 1 / β ≤ 1 + f' (h t) - δ := by
    intro t
    have : f' hbar ≤ f' (h t) := by
      rcases eq_or_lt_of_le (hle t) with e | e
      · rw [e]
      · exact (T.deriv_strictAnti (hpos t) e).le
    rw [hss] at this
    have : 1 / β = 1 + (1 - β) / β := by field_simp; ring
    linarith
  have hRpos : ∀ t, 0 < 1 + f' (h t) - δ := fun t => lt_of_lt_of_le (by positivity) (hR t)
  have hdisc : ∀ t, disc (fun s => 1 + f' (h s) - δ) t ≤ β ^ t := by
    intro t
    induction t with
    | zero => simp [disc]
    | succ t ih =>
      simp only [disc]
      rw [div_le_iff₀ (hRpos (t + 1)), pow_succ]
      have h1 := hR (t + 1)
      have h2 : 1 ≤ β * (1 + f' (h (t + 1)) - δ) := by
        rw [div_le_iff₀ hβ] at h1
        linarith
      have := disc_pos hRpos t
      nlinarith [pow_pos hβ t]
  have hw : ∀ t, wageU f f' (h t) ≤ wageU f f' hbar := fun t => by
    rcases eq_or_lt_of_le (hle t) with e | e
    · rw [e]
    · exact (T.wage_strictMono (hpos t) e).le
  have hwpos : ∀ t, 0 < wageU f f' (h t) := fun t => T.wage_pos (hpos t)
  have hgeo := (summable_geometric_of_lt_one hβ.le hβ1).mul_right (wageU f f' hbar)
  have hbase : ∑' t : ℕ, β ^ t * wageU f f' hbar = wageU f f' hbar / (1 - β) := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ.le hβ1]
    field_simp
  have hle' : ∀ t, disc (fun s => 1 + f' (h s) - δ) t * wageU f f' (h t) ≤
      β ^ t * wageU f f' hbar := fun t =>
    mul_le_mul (hdisc t) (hw t) (hwpos t).le (pow_pos hβ t).le
  have hd := hgeo.sub hsum
  have hlt0 : disc (fun s => 1 + f' (h s) - δ) 0 * wageU f f' (h 0) <
      β ^ 0 * wageU f f' hbar := by
    simp only [disc, pow_zero, one_mul]
    exact T.wage_strictMono (hpos 0) h0
  have := hd.le_tsum 0 (fun j _ => by linarith [hle' j])
  rw [hgeo.tsum_sub hsum, hbase] at this
  linarith

/-! ## The saddle path for general technology and depreciation (via the RCK module) -/

/-- The immigration economy's per-capita problem is the discrete Ramsey–Cass–Koopmans problem
with log utility and `g = n = 0` (O&R p. 450: "isomorphic to the one for the Koopmans model"):
the book's technology hypotheses give the `UPrimitives` of `RamseyCassKoopmans.LogUtility`. -/
theorem immig_uprimitives {f : ℝ → ℝ} (hT : RamseyCassKoopmans.Technology f) {β δ : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    RamseyCassKoopmans.LogUtility.UPrimitives f Real.log β δ := by
  have h := RamseyCassKoopmans.LogUtility.log_uprimitives (δ := δ) hT hβ hβ1 hδ1
    (by linarith) (by norm_num : (0 : ℝ) < 1 + 0)
  have e1 : RamseyCassKoopmans.effF f 0 = f := by
    funext k
    simp [RamseyCassKoopmans.effF]
  have e2 : RamseyCassKoopmans.effU Real.log 0 = Real.log := by
    funext c
    simp [RamseyCassKoopmans.effU]
  have e3 : RamseyCassKoopmans.effDelta 0 δ = δ := by
    simp [RamseyCassKoopmans.effDelta]
  rw [e1, e2, e3] at h
  exact h

/-- The RCK primitives give this module's `Technology` with `f' = deriv f`. -/
theorem technology_of_uprimitives {f : ℝ → ℝ} {β δ : ℝ}
    (P : RamseyCassKoopmans.LogUtility.UPrimitives f Real.log β δ) :
    Technology f (deriv f) :=
  ⟨P.f_conc, fun h hh => (P.f_diff h hh).hasDerivAt, P.f_zero⟩

/-- **The saddle path of the immigration economy exists, is unique, and converges
monotonically from below** (O&R Fig. 7.8, general technology and depreciation). For any
`0 < h₀ < h̄`, where `h̄` solves `f'(h̄) = (1-β)/β + δ`, there is a path `h` from `h₀` with
consumption `c_t = f(h_t) + (1-δ)h_t - h_{t+1} > 0` such that:
* it obeys (39) and the Euler equation (40), `c_{t+1} = (1 + f'(h_{t+1}) - δ)βc_t`;
* `h` rises strictly, stays below `h̄` and converges to `h̄`, and consumption rises strictly;
* any feasible path from `h₀` obeying (40) and the transversality condition is this path.

This discharges the hypothesis "the path stays below `h̄`" in general. -/
theorem immig_saddle_path {f : ℝ → ℝ} {β δ h₀ : ℝ}
    (P : RamseyCassKoopmans.LogUtility.UPrimitives f Real.log β δ) (hh₀ : 0 < h₀)
    (hlt : h₀ < RamseyCassKoopmans.steady P.aux) :
    ∃ h : ℕ → ℝ, h 0 = h₀ ∧
      (∀ t, 0 < RamseyCassKoopmans.consumption f δ h t) ∧
      (∀ t, h (t + 1) - h t = f (h t) - δ * h t - RamseyCassKoopmans.consumption f δ h t) ∧
      (∀ t, RamseyCassKoopmans.consumption f δ h (t + 1) =
        (1 + deriv f (h (t + 1)) - δ) * β * RamseyCassKoopmans.consumption f δ h t) ∧
      StrictMono h ∧ (∀ t, h t < RamseyCassKoopmans.steady P.aux) ∧
      StrictMono (RamseyCassKoopmans.consumption f δ h) ∧
      Tendsto h atTop (𝓝 (RamseyCassKoopmans.steady P.aux)) ∧
      deriv f (RamseyCassKoopmans.steady P.aux) = (1 - β) / β + δ ∧
      ∀ k : ℕ → ℝ, RamseyCassKoopmans.LogUtility.Admissible f Real.log β δ h₀ k →
        (∀ t, deriv Real.log (RamseyCassKoopmans.consumption f δ k t) =
          β * deriv Real.log (RamseyCassKoopmans.consumption f δ k (t + 1)) *
            (deriv f (k (t + 1)) + (1 - δ))) →
        Tendsto (fun t => β ^ t * deriv Real.log (RamseyCassKoopmans.consumption f δ k t) *
          k (t + 1)) atTop (𝓝 0) → k = h := by
  set h := RamseyCassKoopmans.LogUtility.uoptimalPath P hh₀
  have hopt := RamseyCassKoopmans.LogUtility.uoptimalPath_spec P hh₀
  obtain ⟨hmono, hbelow, hcmono⟩ := hopt.dynamics_below P hh₀ hlt
  have hc := hopt.1.2.1
  refine ⟨h, hopt.1.1.1, hc, fun t => ?_, fun t => ?_, hmono, hbelow, hcmono,
    hopt.tendsto P hh₀, ?_, fun k hk he ht => ?_⟩
  · simp only [RamseyCassKoopmans.consumption, RamseyCassKoopmans.resources]
    ring
  · have he := hopt.euler P hh₀ t
    rw [Real.deriv_log, Real.deriv_log] at he
    have h1 := hc t
    have h2 := hc (t + 1)
    field_simp at he
    linarith
  · rw [(RamseyCassKoopmans.steady_spec P.aux).2]
    have := P.β_pos
    field_simp
    ring
  · have hk' := (RamseyCassKoopmans.LogUtility.uoptimal_iff_euler_tvc P hh₀ hk).mpr ⟨he, ht⟩
    exact hk'.unique P hh₀ hopt

/-! ## Immigrants never borrow along the saddle path -/

/-- The ratio of gross resources to `β` times their marginal value,
`φ(h) = (f(h) + (1-δ)h)/(β(f'(h) + 1 - δ)h)`; along the saddle path the ratio
`m_t = h_{t+1}/c_t` obeys `m_{t+1} = φ(h_{t+1}) m_t - 1`. -/
noncomputable def phiRatio (f : ℝ → ℝ) (β δ h : ℝ) : ℝ :=
  (f h + (1 - δ) * h) / (β * (deriv f h + 1 - δ) * h)

/-- **Immigrants never borrow, in general** (O&R p. 452): along the saddle path from
`0 < h₀ < h̄`, if `φ` is non-increasing on `[h₀, h̄]` (true for Cobb–Douglas with any
`δ ∈ [0, 1]`, `phiRatio_antitone_cobbDouglas`), then aggregate capital grows at least at the
rate of the skill gap: `h_{t+1} ≥ β(1 + f'(h_t) - δ)h_t` at every date. Hence
`h_t ≥ h₀ ∏_{s<t} βR_s`, which by `immigrants_nonneg_iff` is exactly the condition for the
immigrants' log-rule plan to hold nonnegative human capital. -/
theorem saddle_growth_ge_gap {f : ℝ → ℝ} {β δ h₀ : ℝ}
    (P : RamseyCassKoopmans.LogUtility.UPrimitives f Real.log β δ) {h : ℕ → ℝ} (hh₀ : 0 < h₀)
    (h0 : h 0 = h₀)
    (hc : ∀ t, 0 < RamseyCassKoopmans.consumption f δ h t)
    (heuler : ∀ t, RamseyCassKoopmans.consumption f δ h (t + 1) =
      (1 + deriv f (h (t + 1)) - δ) * β * RamseyCassKoopmans.consumption f δ h t)
    (hmono : StrictMono h) (hbelow : ∀ t, h t < RamseyCassKoopmans.steady P.aux)
    (hcmono : StrictMono (RamseyCassKoopmans.consumption f δ h))
    (hphi : AntitoneOn (phiRatio f β δ) (Set.Icc h₀ (RamseyCassKoopmans.steady P.aux))) :
    (∀ t, β * (1 + deriv f (h t) - δ) * h t ≤ h (t + 1)) ∧
      ∀ t, h₀ * ∏ s ∈ range t, (β * (1 + deriv f (h s) - δ)) ≤ h t := by
  set hs := RamseyCassKoopmans.steady P.aux
  set c := RamseyCassKoopmans.consumption f δ h
  have hβ := P.β_pos
  have hge : ∀ t, h₀ ≤ h t := fun t => by rw [← h0]; exact hmono.monotone (Nat.zero_le t)
  have hpos : ∀ t, 0 < h t := fun t => lt_of_lt_of_le hh₀ (hge t)
  have hIcc : ∀ t, h t ∈ Set.Icc h₀ hs := fun t => ⟨hge t, (hbelow t).le⟩
  have hR : ∀ t, 0 < deriv f (h t) + 1 - δ := fun t => by
    have := P.f_prime_pos _ (hpos t)
    linarith [P.δ_le_one]
  have hT := technology_of_uprimitives P
  -- φ ≥ 1/β
  have hphi_ge : ∀ t, 1 / β ≤ phiRatio f β δ (h t) := by
    intro t
    have hw := hT.wage_pos (hpos t)
    unfold wageU at hw
    unfold phiRatio
    rw [div_le_div_iff₀ hβ (by have := hR t; have := hpos t; positivity)]
    have := hpos t
    nlinarith [P.δ_le_one]
  -- the ratio m_t = h_{t+1}/c_t
  set m : ℕ → ℝ := fun t => h (t + 1) / c t with hm
  have hmpos : ∀ t, 0 < m t := fun t => div_pos (hpos _) (hc t)
  have hres : ∀ t, c t = f (h t) + (1 - δ) * h t - h (t + 1) := fun t => rfl
  have hmrec : ∀ t, m (t + 1) = phiRatio f β δ (h (t + 1)) * m t - 1 := by
    intro t
    have e := heuler t
    have hc0 := hc t
    have hc1 := hc (t + 1)
    have hr := hR (t + 1)
    have hr' : 0 < 1 + deriv f (h (t + 1)) - δ := by linarith
    have hp := hpos (t + 1)
    have key : phiRatio f β δ (h (t + 1)) * (h (t + 1) / c t) =
        (f (h (t + 1)) + (1 - δ) * h (t + 1)) / c (t + 1) := by
      unfold phiRatio
      rw [e]
      field_simp
      ring
    have hF : h (t + 1 + 1) = f (h (t + 1)) + (1 - δ) * h (t + 1) - c (t + 1) := by
      linarith [hres (t + 1)]
    simp only [hm]
    rw [hF, sub_div, div_self hc1.ne', key]
  have hmbd : ∀ t, m t ≤ hs / c 0 := by
    intro t
    simp only [hm]
    have := hcmono.monotone (Nat.zero_le t)
    rw [div_le_div_iff₀ (hc t) (hc 0)]
    have := hbelow (t + 1)
    nlinarith [hc 0, hpos (t + 1)]
  -- m is nondecreasing
  have hmono_m : ∀ t, m t ≤ m (t + 1) := by
    by_contra hne
    push Not at hne
    obtain ⟨t₀, ht₀⟩ := hne
    set d₀ := m (t₀ + 1) - m t₀
    have hd₀ : d₀ < 0 := by simp only [d₀]; linarith
    have hdec : ∀ n, m (t₀ + n + 1) - m (t₀ + n) ≤ d₀ / β ^ n := by
      intro n
      induction n with
      | zero => simp [d₀]
      | succ n ih =>
        have e1 := hmrec (t₀ + n + 1)
        have e0 := hmrec (t₀ + n)
        have hφ : phiRatio f β δ (h (t₀ + n + 1 + 1)) ≤ phiRatio f β δ (h (t₀ + n + 1)) :=
          hphi (hIcc _) (hIcc _) (hmono.monotone (Nat.le_succ _))
        have hφb := hphi_ge (t₀ + n + 1 + 1)
        have hmt := hmpos (t₀ + n)
        -- d_{n+1} ≤ φ_{n+2} d_n
        have hstep : m (t₀ + (n + 1) + 1) - m (t₀ + (n + 1)) ≤
            phiRatio f β δ (h (t₀ + n + 1 + 1)) * (m (t₀ + n + 1) - m (t₀ + n)) := by
          rw [show t₀ + (n + 1) + 1 = t₀ + n + 1 + 1 by ring,
            show t₀ + (n + 1) = t₀ + n + 1 by ring, e1, e0]
          nlinarith
        have hneg : m (t₀ + n + 1) - m (t₀ + n) < 0 := by
          have : d₀ / β ^ n < 0 := div_neg_of_neg_of_pos hd₀ (pow_pos hβ n)
          linarith
        have h2 : phiRatio f β δ (h (t₀ + n + 1 + 1)) * (m (t₀ + n + 1) - m (t₀ + n)) ≤
            1 / β * (m (t₀ + n + 1) - m (t₀ + n)) := by nlinarith
        have h3 : 1 / β * (m (t₀ + n + 1) - m (t₀ + n)) ≤ 1 / β * (d₀ / β ^ n) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        rw [pow_succ]
        calc _ ≤ _ := hstep
          _ ≤ _ := h2
          _ ≤ 1 / β * (d₀ / β ^ n) := h3
          _ = d₀ / (β ^ n * β) := by field_simp
    have hq : Tendsto (fun n : ℕ => (1 / β) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by rw [one_lt_div hβ]; exact P.β_lt_one)
    obtain ⟨n, hn⟩ := (hq.eventually_gt_atTop ((hs / c 0 + 1) / (-d₀))).exists
    have h1 := hdec n
    have h2 := hmbd (t₀ + n)
    have h3 := hmpos (t₀ + n + 1)
    have e : d₀ / β ^ n = d₀ * (1 / β) ^ n := by rw [one_div_pow]; ring
    rw [e] at h1
    rw [div_lt_iff₀ (by linarith)] at hn
    nlinarith
  -- the step condition
  have hstep : ∀ t, β * (1 + deriv f (h t) - δ) * h t ≤ h (t + 1) := by
    intro t
    have e := hmrec t
    have hmt := hmono_m t
    have hφ : phiRatio f β δ (h (t + 1)) ≤ phiRatio f β δ (h t) :=
      hphi (hIcc _) (hIcc _) (hmono.monotone (Nat.le_succ _))
    have key : 1 + m t ≤ m t * phiRatio f β δ (h t) := by nlinarith [hmpos t]
    have hct := hc t
    have hr := hR t
    have hp := hpos t
    have hc_eq : c t * (1 + m t) = f (h t) + (1 - δ) * h t := by
      simp only [hm]
      field_simp
      rw [hres t]
      ring
    unfold phiRatio at key
    have hden : 0 < β * (deriv f (h t) + 1 - δ) * h t := by positivity
    rw [mul_div_assoc', le_div_iff₀ hden] at key
    have hhm : h (t + 1) = m t * c t := by simp only [hm]; field_simp
    rw [hhm]
    have hm1 : 0 < 1 + m t := by linarith [hmpos t]
    have h4 : β * (1 + deriv f (h t) - δ) * h t * (1 + m t) ≤ m t * c t * (1 + m t) := by
      have : m t * c t * (1 + m t) = m t * (f (h t) + (1 - δ) * h t) := by
        rw [← hc_eq]
        ring
      rw [this]
      linarith
    exact le_of_mul_le_mul_right h4 hm1
  refine ⟨hstep, fun t => ?_⟩
  induction t with
  | zero => simp [h0]
  | succ t ih =>
    rw [prod_range_succ]
    have := hstep t
    have hb : 0 ≤ β * (1 + deriv f (h t) - δ) := mul_nonneg hβ.le (by linarith [hR t])
    calc h₀ * ((∏ s ∈ range t, (β * (1 + deriv f (h s) - δ))) * (β * (1 + deriv f (h t) - δ)))
        = h₀ * (∏ s ∈ range t, (β * (1 + deriv f (h s) - δ))) * (β * (1 + deriv f (h t) - δ)) := by
          ring
      _ ≤ h t * (β * (1 + deriv f (h t) - δ)) := mul_le_mul_of_nonneg_right ih hb
      _ ≤ h (t + 1) := by linarith

/-- Cobb–Douglas `f(h) = h^α` satisfies the RCK module's technology hypotheses (neoclassical,
continuous marginal product, both Inada conditions). -/
theorem cobbDouglas_rckTechnology {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    RamseyCassKoopmans.Technology (fun h : ℝ => h ^ α) := by
  have hderiv : deriv (fun h : ℝ => h ^ α) = fun h => α * h ^ (α - 1) := Real.deriv_rpow_const' α
  refine ⟨⟨(continuous_id.rpow_const fun _ => Or.inr hα.le).continuousOn,
    Real.zero_rpow hα.ne', fun a ha b _ hab => Real.rpow_lt_rpow ha hab hα,
    Real.strictConcaveOn_rpow hα hα1,
    fun k hk => (Real.hasDerivAt_rpow_const (Or.inl hk.ne')).differentiableAt⟩, ?_, ?_, ?_⟩
  · rw [hderiv]
    exact fun x hx => (continuousAt_const.mul
      (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx)))).continuousWithinAt
  · rw [hderiv]
    exact (tendsto_rpow_neg_nhdsGT_zero (by linarith : α - 1 < 0)).const_mul_atTop hα
  · rw [hderiv]
    have := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - α)).const_mul α
    rw [mul_zero] at this
    refine this.congr fun x => ?_
    rw [neg_sub]

/-- For Cobb–Douglas and any `δ ∈ [0, 1]`, `φ(h) = (h^{α-1} + 1 - δ)/(β(αh^{α-1} + 1 - δ))` is
non-increasing on `(0, ∞)`. -/
theorem phiRatio_antitone_cobbDouglas {α β δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hδ1 : δ ≤ 1) : AntitoneOn (phiRatio (fun h : ℝ => h ^ α) β δ) (Set.Ioi 0) := by
  have hderiv : deriv (fun h : ℝ => h ^ α) = fun h => α * h ^ (α - 1) := Real.deriv_rpow_const' α
  have hform : ∀ h, 0 < h → phiRatio (fun h : ℝ => h ^ α) β δ h =
      (h ^ (α - 1) + (1 - δ)) / (β * (α * h ^ (α - 1) + (1 - δ))) := by
    intro h hh
    unfold phiRatio
    rw [hderiv]
    have e : h ^ α = h ^ (α - 1) * h := by rw [← Real.rpow_add_one hh.ne', sub_add_cancel]
    have := Real.rpow_pos_of_pos hh (α - 1)
    have hd : 0 < α * h ^ (α - 1) + (1 - δ) := by nlinarith
    have hd' : 0 < β * (α * h ^ (α - 1) + 1 - δ) * h := by
      have : 0 < α * h ^ (α - 1) + 1 - δ := by linarith
      positivity
    simp only
    rw [e, div_eq_div_iff hd'.ne' (by positivity)]
    ring
  intro a ha b hb hab
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  rw [hform b hb', hform a ha']
  have hxa := Real.rpow_pos_of_pos ha' (α - 1)
  have hxb := Real.rpow_pos_of_pos hb' (α - 1)
  have hx : b ^ (α - 1) ≤ a ^ (α - 1) := Real.rpow_le_rpow_of_nonpos ha' hab (by linarith)
  have hda : 0 < α * a ^ (α - 1) + (1 - δ) := by nlinarith
  have hdb : 0 < α * b ^ (α - 1) + (1 - δ) := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1a : 0 ≤ (1 - α) * (1 - δ) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_nonneg h1a (sub_nonneg.mpr hx)]

/-- **Immigrants never borrow: Cobb–Douglas, any depreciation** (O&R p. 452, proved in
general for `f = h^α` and `δ ∈ [0, 1]`). The unique saddle path from `0 < h₀ < h̄` exists, rises
monotonically below `h̄`, and aggregate capital outgrows the skill gap at every date:
`h_{t+1} ≥ β(1 + f'(h_t) - δ)h_t`, so `h_t ≥ h₀ ∏_{s<t} βR_s`. By `immigrants_nonneg_iff` the
immigrants' log-rule plan never borrows. -/
theorem cobbDouglas_immigrants_never_borrow {α β δ h₀ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hh₀ : 0 < h₀)
    (hlt : h₀ < RamseyCassKoopmans.steady
      (immig_uprimitives (cobbDouglas_rckTechnology hα hα1) hβ hβ1 hδ hδ1).aux) :
    ∃ h : ℕ → ℝ, h 0 = h₀ ∧ StrictMono h ∧
      (∀ t, h t < RamseyCassKoopmans.steady
        (immig_uprimitives (cobbDouglas_rckTechnology hα hα1) hβ hβ1 hδ hδ1).aux) ∧
      (∀ t, β * (1 + α * h t ^ (α - 1) - δ) * h t ≤ h (t + 1)) ∧
      ∀ t, h₀ * ∏ s ∈ range t, (β * (1 + α * h s ^ (α - 1) - δ)) ≤ h t := by
  set P := immig_uprimitives (cobbDouglas_rckTechnology hα hα1) hβ hβ1 hδ hδ1
  obtain ⟨h, h0, hc, -, heu, hmono, hbelow, hcmono, -, -, -⟩ := immig_saddle_path P hh₀ hlt
  have hphi : AntitoneOn (phiRatio (fun h : ℝ => h ^ α) β δ)
      (Set.Icc h₀ (RamseyCassKoopmans.steady P.aux)) :=
    (phiRatio_antitone_cobbDouglas hα hα1 hβ hδ1).mono fun x hx => lt_of_lt_of_le hh₀ hx.1
  obtain ⟨h1, h2⟩ := saddle_growth_ge_gap P hh₀ h0 hc heu hmono hbelow hcmono hphi
  have hderiv : ∀ x, deriv (fun h : ℝ => h ^ α) x = α * x ^ (α - 1) :=
    fun x => Real.deriv_rpow_const x α
  refine ⟨h, h0, hmono, hbelow, fun t => ?_, fun t => ?_⟩
  · have := h1 t
    rwa [hderiv] at this
  · have := h2 t
    simp only [hderiv] at this
    exact this

end ObstfeldRogoff.GlobalGrowth.Immigration
