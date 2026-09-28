/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Recontracting sovereign debt: Rubinstein bargaining

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, Appendix 6A,
pp. 419–422 (eqs. (54)–(57), footnotes 71–73).

The sovereign has linear utility `Σ_s hC_{t+hs}/(1+δh)^s` (54), `δ > r`, produces `Yh` export
units per period of length `h` worth `P` imports each, and can store output at depreciation
rate `θ` (`θh < 1`). Creditors (world rate `r`) cannot seize goods at home, so repayments are
bargained over. We prove:
* the present value (55): `Σ_{s≥1} PYh/(1+rh)^s = PY/r`, and that with linear utility and
  `δ > r` the sovereign optimally consumes everything on the initial date (any plan with
  consumption after `t` is strictly worse);
* the recursions of footnote 73, their stationary solution `x = a(1−b)/(1−ab)`, `x′ = (1−b)/(1−ab)`
  with `a = (1−θh)/(1+rh)`, `b = (1−θh)/(1+δh)`, and that every BOUNDED solution of the
  difference equations is this stationary one;
* the exact creditors' share for period length `h`,
  `x(h) = (1−θh)(δ+θ)/[r + δ + 2θ + h(rδ − θ²)]`, and its limit (56)
  `(δ+θ)/(δ+r+2θ)` as `h → 0` (also for the creditors' own offers), the country's share (57),
  and the lending limit `D = [(δ+θ)/(δ+r+2θ)]PY/r < PY/r`;
* the Rubinstein (1982) alternating-offers game in full: histories, strategies, the outcome of
  every strategy profile in every subgame, and subgame-perfect equilibrium. The stationary
  strategies of footnote 73 form a subgame-perfect equilibrium (EXISTENCE), and in EVERY
  subgame-perfect equilibrium, in every subgame, the proposer offers the stationary share, it is
  accepted at once, and payoffs are the stationary ones (UNIQUENESS, by the Shaked–Sutton
  sup/inf argument).
-/

namespace ObstfeldRogoff.CapitalMarketImperfections.SovereignBargaining

open Set Filter Topology

/-! ## (55): the present value of the income stream, and the consumption corner -/

/-- The present value (55), O&R p. 420: for `r, h > 0`,
`Σ_{s ≥ 1} PYh/(1+rh)^s = PYh/(rh) = PY/r`, with the series summable. -/
theorem present_value_income {P Y r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    Summable (fun s : ℕ => P * Y * h / (1 + r * h) ^ (s + 1)) ∧
      ∑' s : ℕ, P * Y * h / (1 + r * h) ^ (s + 1) = P * Y / r := by
  have hq0 : 0 ≤ 1 / (1 + r * h) := by positivity
  have hq1 : 1 / (1 + r * h) < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  have hsum := summable_geometric_of_lt_one hq0 hq1
  have e : (fun s : ℕ => P * Y * h / (1 + r * h) ^ (s + 1)) =
      fun s : ℕ => P * Y * h / (1 + r * h) * (1 / (1 + r * h)) ^ s := by
    funext s
    rw [one_div_pow, pow_succ]
    field_simp
  rw [e]
  refine ⟨hsum.mul_left _, ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  field_simp
  ring

/-- Linear utility and impatience give a consumption corner, O&R p. 420 ("the country will do all
its consuming on the initial date"): with `0 < r < δ`, `h > 0`, any nonnegative consumption plan
`C` whose present value at the world rate is at most `W` gives utility (54)
`Σ_s hC_s/(1+δh)^s ≤ hW`; the plan `C₀ = W`, `C_s = 0` (`s ≥ 1`) attains `hW`; and any plan that
consumes a positive amount at some date `s ≥ 1` is strictly worse. -/
theorem linear_utility_corner {r δ h W : ℝ} (hr : 0 < r) (hrδ : r < δ) (hh : 0 < h)
    {C : ℕ → ℝ} (hC0 : ∀ s, 0 ≤ C s) (hCs : Summable fun s => C s / (1 + r * h) ^ s)
    (hbud : ∑' s, C s / (1 + r * h) ^ s ≤ W) :
    Summable (fun s => h * C s / (1 + δ * h) ^ s) ∧
      ∑' s, h * C s / (1 + δ * h) ^ s ≤ h * W ∧
      ∑' s : ℕ, h * (if s = 0 then W else 0) / (1 + δ * h) ^ s = h * W ∧
      ((∃ s, 1 ≤ s ∧ 0 < C s) → ∑' s, h * C s / (1 + δ * h) ^ s < h * W) := by
  have hle : ∀ s : ℕ, h * C s / (1 + δ * h) ^ s ≤ h * (C s / (1 + r * h) ^ s) := by
    intro s
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hh.le
    apply div_le_div_of_nonneg_left (hC0 s) (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) s
  have hδ : 0 < δ := by linarith
  have hnn : ∀ s : ℕ, 0 ≤ h * C s / (1 + δ * h) ^ s := fun s => by
    have := hC0 s; positivity
  have hsum : Summable (fun s => h * C s / (1 + δ * h) ^ s) :=
    (hCs.mul_left h).of_nonneg_of_le hnn hle
  have hmain : ∑' s, h * C s / (1 + δ * h) ^ s ≤ h * W := by
    calc ∑' s, h * C s / (1 + δ * h) ^ s ≤ ∑' s, h * (C s / (1 + r * h) ^ s) :=
          hsum.tsum_le_tsum hle (hCs.mul_left h)
      _ = h * ∑' s, C s / (1 + r * h) ^ s := tsum_mul_left
      _ ≤ h * W := mul_le_mul_of_nonneg_left hbud hh.le
  refine ⟨hsum, hmain, ?_, ?_⟩
  · rw [tsum_eq_single 0]
    · simp
    · intro s hs
      simp [hs]
  · rintro ⟨s, hs1, hspos⟩
    have hlt : h * C s / (1 + δ * h) ^ s < h * (C s / (1 + r * h) ^ s) := by
      rw [mul_div_assoc]
      apply mul_lt_mul_of_pos_left _ hh
      apply div_lt_div_of_pos_left hspos (by positivity)
      exact pow_lt_pow_left₀ (by nlinarith) (by positivity) (by omega)
    calc ∑' s, h * C s / (1 + δ * h) ^ s < ∑' s, h * (C s / (1 + r * h) ^ s) :=
          hsum.tsum_lt_tsum hle hlt (hCs.mul_left h)
      _ = h * ∑' s, C s / (1 + r * h) ^ s := tsum_mul_left
      _ ≤ h * W := mul_le_mul_of_nonneg_left hbud hh.le

/-! ## Footnote 73: the recursions and their stationary solution -/

/-- The creditors' per-period discount factor in bargaining, footnote 73:
`a = (1−θh)/(1+rh)` (waiting a period costs interest and storage losses). -/
noncomputable def creditorFactor (r θ h : ℝ) : ℝ := (1 - θ * h) / (1 + r * h)

/-- The country's per-period discount factor in bargaining, footnote 73:
`b = (1−θh)/(1+δh)`. -/
noncomputable def countryFactor (δ θ h : ℝ) : ℝ := (1 - θ * h) / (1 + δ * h)

/-- The share the country offers the creditors when it proposes (stationary solution of
footnote 73): `x = a(1−b)/(1−ab)`. -/
noncomputable def countryOfferShare (a b : ℝ) : ℝ := a * (1 - b) / (1 - a * b)

/-- The share the creditors claim when they propose (stationary solution of footnote 73):
`x′ = (1−b)/(1−ab)`. -/
noncomputable def creditorOfferShare (a b : ℝ) : ℝ := (1 - b) / (1 - a * b)

/-- The stationary state of the footnote 73 recursions, O&R p. 421: if `ab ≠ 1`, the pair
`(x, x′)` solves `x = a x′` and `1 − x′ = b(1 − x)` if and only if `x = a(1−b)/(1−ab)` and
`x′ = (1−b)/(1−ab)`. -/
theorem stationary_iff {a b x x' : ℝ} (hab : a * b ≠ 1) :
    (x = a * x' ∧ 1 - x' = b * (1 - x)) ↔
      (x = countryOfferShare a b ∧ x' = creditorOfferShare a b) := by
  have h1 : 1 - a * b ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  unfold countryOfferShare creditorOfferShare
  constructor
  · rintro ⟨e1, e2⟩
    have hx' : x' = (1 - b) / (1 - a * b) := by
      rw [eq_div_iff h1]; rw [e1] at e2; linear_combination -e2
    refine ⟨?_, hx'⟩
    rw [e1, hx']; ring
  · rintro ⟨e1, e2⟩
    rw [e1, e2]
    constructor
    · ring
    · rw [one_sub_div h1, one_sub_div h1, mul_div_assoc']
      congr 1
      ring

/-- Every bounded solution of the footnote 73 difference equations is the stationary one
(O&R p. 421, "the stationary state of these difference equations"): if `0 ≤ ab < 1` and
`x_t = a x′_{t+1}`, `1 − x′_t = b(1 − x_{t+1})` for all `t`, with `x` bounded, then `x_t` and
`x′_t` equal the stationary shares for every `t`. -/
theorem bounded_solution_stationary {a b : ℝ} (hab0 : 0 ≤ a * b) (hab1 : a * b < 1)
    {x x' : ℕ → ℝ} (hx : ∀ t, x t = a * x' (t + 1)) (hx' : ∀ t, 1 - x' t = b * (1 - x (t + 1)))
    {B : ℝ} (hB : ∀ t, |x t| ≤ B) :
    ∀ t, x t = countryOfferShare a b ∧ x' t = creditorOfferShare a b := by
  have h1 : 1 - a * b ≠ 0 := by linarith
  set xs := countryOfferShare a b with hxs
  set xs' := creditorOfferShare a b with hxs'
  have hstat := (stationary_iff (x := xs) (x' := xs') (by linarith)).mpr ⟨rfl, rfl⟩
  -- the deviation from the stationary share contracts by `ab` every two periods
  have hstep : ∀ t, x t - xs = a * b * (x (t + 2) - xs) := by
    intro t
    have e1 := hx t
    have e2 := hx' (t + 1)
    linear_combination e1 - a * e2 - hstat.1 + a * hstat.2
  have hiter : ∀ n t, x t - xs = (a * b) ^ n * (x (t + 2 * n) - xs) := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      rw [ih t, hstep (t + 2 * n), show t + 2 * n + 2 = t + 2 * (n + 1) by ring]
      ring
  have hxt : ∀ t, x t = xs := by
    intro t
    by_contra hne
    have hpos : 0 < |x t - xs| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hlim : Tendsto (fun n : ℕ => (a * b) ^ n * (B + |xs|)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hab0 hab1).mul_const (B + |xs|)
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hpos)).exists
    have hb : |x (t + 2 * n) - xs| ≤ B + |xs| := by
      calc |x (t + 2 * n) - xs| ≤ |x (t + 2 * n)| + |xs| := abs_sub _ _
        _ ≤ B + |xs| := by linarith [hB (t + 2 * n)]
    have : |x t - xs| ≤ (a * b) ^ n * (B + |xs|) := by
      rw [hiter n t, abs_mul, abs_of_nonneg (pow_nonneg hab0 n)]
      exact mul_le_mul_of_nonneg_left hb (pow_nonneg hab0 n)
    linarith
  intro t
  refine ⟨hxt t, ?_⟩
  have e := hx' t
  rw [hxt (t + 1)] at e
  linarith [hstat.2]

/-! ## The exact share for period length `h`, and the limits (56)–(57) -/

/-- The exact creditors' share when the country proposes, for period length `h`, O&R
footnote 73: with `a = (1−θh)/(1+rh)`, `b = (1−θh)/(1+δh)`,
`a(1−b)/(1−ab) = (1−θh)(δ+θ)/[r + δ + 2θ + h(rδ − θ²)]` (for `h > 0`, `1 + rh > 0`,
`1 + δh > 0` and a nonzero denominator). -/
theorem countryOfferShare_exact {r δ θ h : ℝ} (hh : 0 < h) (hr : 0 < 1 + r * h)
    (hd : 0 < 1 + δ * h) (hden : r + δ + 2 * θ + h * (r * δ - θ ^ 2) ≠ 0) :
    countryOfferShare (creditorFactor r θ h) (countryFactor δ θ h) =
      (1 - θ * h) * (δ + θ) / (r + δ + 2 * θ + h * (r * δ - θ ^ 2)) := by
  unfold countryOfferShare creditorFactor countryFactor
  have hr' : 1 + r * h ≠ 0 := hr.ne'
  have hd' : 1 + δ * h ≠ 0 := hd.ne'
  have hh' : h ≠ 0 := hh.ne'
  have e : 1 - (1 - θ * h) / (1 + r * h) * ((1 - θ * h) / (1 + δ * h)) =
      h * (r + δ + 2 * θ + h * (r * δ - θ ^ 2)) / ((1 + r * h) * (1 + δ * h)) := by
    rw [div_mul_div_comm, one_sub_div (mul_ne_zero hr' hd')]
    congr 1
    ring
  have e2 : 1 - (1 - θ * h) / (1 + δ * h) = h * (δ + θ) / (1 + δ * h) := by
    rw [one_sub_div hd']
    congr 1
    ring
  rw [e, e2, div_mul_div_comm, div_div_div_cancel_right₀ (mul_ne_zero hr' hd'),
    div_eq_div_iff (mul_ne_zero hh' hden) hden]
  ring

/-- The exact creditors' share when the creditors propose, footnote 73:
`(1−b)/(1−ab) = (1+rh)(δ+θ)/[r + δ + 2θ + h(rδ − θ²)]`. -/
theorem creditorOfferShare_exact {r δ θ h : ℝ} (hh : 0 < h) (hr : 0 < 1 + r * h)
    (hd : 0 < 1 + δ * h) (hden : r + δ + 2 * θ + h * (r * δ - θ ^ 2) ≠ 0) :
    creditorOfferShare (creditorFactor r θ h) (countryFactor δ θ h) =
      (1 + r * h) * (δ + θ) / (r + δ + 2 * θ + h * (r * δ - θ ^ 2)) := by
  unfold creditorOfferShare creditorFactor countryFactor
  have hr' : 1 + r * h ≠ 0 := hr.ne'
  have hd' : 1 + δ * h ≠ 0 := hd.ne'
  have hh' : h ≠ 0 := hh.ne'
  have e : 1 - (1 - θ * h) / (1 + r * h) * ((1 - θ * h) / (1 + δ * h)) =
      h * (r + δ + 2 * θ + h * (r * δ - θ ^ 2)) / ((1 + r * h) * (1 + δ * h)) := by
    rw [div_mul_div_comm, one_sub_div (mul_ne_zero hr' hd')]
    congr 1
    ring
  have e2 : 1 - (1 - θ * h) / (1 + δ * h) = h * (δ + θ) / (1 + δ * h) := by
    rw [one_sub_div hd']
    congr 1
    ring
  rw [e, e2, div_div_eq_mul_div]
  have e3 : h * (δ + θ) / (1 + δ * h) * ((1 + r * h) * (1 + δ * h)) =
      h * (δ + θ) * (1 + r * h) := by
    rw [div_mul_eq_mul_div, div_eq_iff hd']
    ring
  rw [e3, div_eq_div_iff (mul_ne_zero hh' hden) hden]
  ring

/-- The continuous-bargaining limit (56), O&R p. 421: with `r + θ > 0` and `δ + θ > 0`, as the
period length `h → 0` the creditors' share (whoever proposes) tends to
`(δ+θ)/[(δ+θ) + (r+θ)] = (δ+θ)/(δ+r+2θ)`. -/
theorem share_limit56 {r δ θ : ℝ} (hrθ : 0 < r + θ) (hδθ : 0 < δ + θ) :
    Tendsto (fun h => countryOfferShare (creditorFactor r θ h) (countryFactor δ θ h))
        (𝓝[>] 0) (𝓝 ((δ + θ) / (δ + r + 2 * θ))) ∧
      Tendsto (fun h => creditorOfferShare (creditorFactor r θ h) (countryFactor δ θ h))
        (𝓝[>] 0) (𝓝 ((δ + θ) / (δ + r + 2 * θ))) := by
  have hden0 : r + δ + 2 * θ + 0 * (r * δ - θ ^ 2) ≠ 0 := by linarith
  have hc1 : ContinuousAt (fun h : ℝ => (1 - θ * h) * (δ + θ) /
      (r + δ + 2 * θ + h * (r * δ - θ ^ 2))) 0 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hden0
  have hc2 : ContinuousAt (fun h : ℝ => (1 + r * h) * (δ + θ) /
      (r + δ + 2 * θ + h * (r * δ - θ ^ 2))) 0 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hden0
  have hv : (δ + θ) / (δ + r + 2 * θ) =
      (1 - θ * 0) * (δ + θ) / (r + δ + 2 * θ + 0 * (r * δ - θ ^ 2)) := by ring_nf
  have hv2 : (δ + θ) / (δ + r + 2 * θ) =
      (1 + r * 0) * (δ + θ) / (r + δ + 2 * θ + 0 * (r * δ - θ ^ 2)) := by ring_nf
  -- for small `h > 0` the shares equal the closed forms
  have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ 0 < 1 + r * h ∧ 0 < 1 + δ * h ∧
      r + δ + 2 * θ + h * (r * δ - θ ^ 2) ≠ 0 := by
    have c1 : ContinuousAt (fun h : ℝ => 1 + r * h) 0 := by fun_prop
    have c2 : ContinuousAt (fun h : ℝ => 1 + δ * h) 0 := by fun_prop
    have c3 : ContinuousAt (fun h : ℝ => r + δ + 2 * θ + h * (r * δ - θ ^ 2)) 0 := by fun_prop
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (c1.eventually (lt_mem_nhds (by simp : (0 : ℝ) < 1 + r * 0))),
      nhdsWithin_le_nhds (c2.eventually (lt_mem_nhds (by simp : (0 : ℝ) < 1 + δ * 0))),
      nhdsWithin_le_nhds (c3.eventually (lt_mem_nhds (by linarith :
        (0 : ℝ) < r + δ + 2 * θ + 0 * (r * δ - θ ^ 2))))] with h h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3.ne'⟩
  constructor
  · rw [hv]
    refine (hc1.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hsmall] with h ⟨h0, h1, h2, h3⟩
    exact (countryOfferShare_exact h0 h1 h2 h3).symm
  · rw [hv2]
    refine (hc2.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hsmall] with h ⟨h0, h1, h2, h3⟩
    exact (creditorOfferShare_exact h0 h1 h2 h3).symm

/-- The country's share (57), O&R p. 421: `1 − (δ+θ)/(δ+r+2θ) = (r+θ)/(δ+r+2θ)`. -/
theorem country_share57 {r δ θ : ℝ} (hrθ : 0 < r + θ) (hδθ : 0 < δ + θ) :
    1 - (δ + θ) / (δ + r + 2 * θ) = (r + θ) / (δ + r + 2 * θ) := by
  have : δ + r + 2 * θ ≠ 0 := by linarith
  rw [eq_div_iff this, sub_mul, div_mul_cancel₀ _ this]
  ring

/-- The lending limit under bargaining, O&R p. 421: creditors never lend more than
`D = [(δ+θ)/(δ+r+2θ)]PY/r`, which is strictly below the present value `PY/r` of (55) when
`r + θ > 0`, `δ + θ > 0`, `r > 0` and `PY > 0`. -/
theorem bargaining_debt_lt_pv {P Y r δ θ : ℝ} (hrθ : 0 < r + θ) (hδθ : 0 < δ + θ)
    (hr : 0 < r) (hPY : 0 < P * Y) :
    (δ + θ) / (δ + r + 2 * θ) * (P * Y / r) < P * Y / r := by
  have hs : (δ + θ) / (δ + r + 2 * θ) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have : 0 < P * Y / r := div_pos hPY hr
  nlinarith

/-- The bargaining discount factors lie in `(0, 1)` (footnotes 72–73): for `h > 0`, `θh < 1`,
`1 + rh > 0`, `1 + δh > 0`, `r + θ > 0` and `δ + θ > 0` (so storage may even have a
nonnegative return, `θ ≤ 0`, provided `−θ < r`). -/
theorem factors_mem_unit {r δ θ h : ℝ} (hh : 0 < h) (hθh : θ * h < 1) (hr : 0 < 1 + r * h)
    (hd : 0 < 1 + δ * h) (hrθ : 0 < r + θ) (hδθ : 0 < δ + θ) :
    0 < creditorFactor r θ h ∧ creditorFactor r θ h < 1 ∧
      0 < countryFactor δ θ h ∧ countryFactor δ θ h < 1 := by
  unfold creditorFactor countryFactor
  refine ⟨div_pos (by linarith) hr, ?_, div_pos (by linarith) hd, ?_⟩
  · rw [div_lt_one hr]; nlinarith
  · rw [div_lt_one hd]; nlinarith

/-! ## The alternating-offers game (Rubinstein 1982), footnote 73

Histories are the lists of offers rejected so far; an offer is the creditors' share of the pie.
The country proposes after an even number of rejections (it makes the first offer, footnote
73), the creditors after an odd number. An agreement on creditors' share `s` after `k`
rejections gives the creditors `aᵏs` and the country `bᵏ(1 − s)`; perpetual disagreement gives
both zero. -/

/-- A strategy in the alternating-offers game, footnote 73: at a history `g` where it is her
turn, the player proposes the creditors' share `propose g`; offered the share `y` at `g`, she
accepts iff `respond g y`. -/
structure BargainStrategy where
  propose : List ℝ → ℝ
  respond : List ℝ → ℝ → Bool

/-- A history is admissible if every rejected offer is a share in `[0, 1]`.
(O&R Appendix 6A, footnote 73, p. 421.) -/
def Admissible (g : List ℝ) : Prop := ∀ z ∈ g, z ∈ Icc (0 : ℝ) 1

/-- A strategy is valid if it proposes shares in `[0, 1]` at admissible histories.
(O&R Appendix 6A, footnote 73, p. 421.) -/
def ValidStrategy (τ : BargainStrategy) : Prop :=
  ∀ g, Admissible g → τ.propose g ∈ Icc (0 : ℝ) 1

/-- The offer made at history `g`: by the country if `g` has even length, else by the
creditors. (O&R Appendix 6A, footnote 73, p. 421.) -/
def offerAt (σc σk : BargainStrategy) (g : List ℝ) : ℝ :=
  if Even g.length then σc.propose g else σk.propose g

/-- The response to offer `y` at history `g`: by the creditors if `g` has even length, else by
the country. (O&R Appendix 6A, footnote 73, p. 421.) -/
def acceptAt (σc σk : BargainStrategy) (g : List ℝ) (y : ℝ) : Bool :=
  if Even g.length then σk.respond g y else σc.respond g y

/-- The path of play from history `h`: the history after `k` further rejections.
(O&R Appendix 6A, footnote 73, p. 421.) -/
def play (σc σk : BargainStrategy) (h : List ℝ) : ℕ → List ℝ
  | 0 => h
  | k + 1 => play σc σk h k ++ [offerAt σc σk (play σc σk h k)]

/-- Agreement is reached after exactly `k` further rejections' worth of offers, i.e. the offer
at `play h k` is accepted. (O&R Appendix 6A, footnote 73, p. 421.) -/
def AgreedAt (σc σk : BargainStrategy) (h : List ℝ) (k : ℕ) : Prop :=
  acceptAt σc σk (play σc σk h k) (offerAt σc σk (play σc σk h k)) = true

/-- The value of an outcome: if agreement first occurs at `k`, `dᵏ · val k`; with perpetual
disagreement, `0`. (O&R Appendix 6A, footnote 73, p. 421.) -/
noncomputable def outcomeValue (d : ℝ) (agreed : ℕ → Prop) (val : ℕ → ℝ) : ℝ := by
  classical
  exact if hex : ∃ k, agreed k then d ^ Nat.find hex * val (Nat.find hex) else 0

/-- The country's payoff in the subgame starting at proposal node `h`.
(O&R Appendix 6A, footnote 73, p. 421.) -/
noncomputable def countryPayoff (b : ℝ) (σc σk : BargainStrategy) (h : List ℝ) : ℝ :=
  outcomeValue b (AgreedAt σc σk h) fun k => 1 - offerAt σc σk (play σc σk h k)

/-- The creditors' payoff in the subgame starting at proposal node `h`.
(O&R Appendix 6A, footnote 73, p. 421.) -/
noncomputable def creditorPayoff (a : ℝ) (σc σk : BargainStrategy) (h : List ℝ) : ℝ :=
  outcomeValue a (AgreedAt σc σk h) fun k => offerAt σc σk (play σc σk h k)

/-- The country's payoff in the subgame starting at the response node where `y` has just been
offered at history `h`. (O&R Appendix 6A, footnote 73, p. 421.) -/
noncomputable def countryRespPayoff (b : ℝ) (σc σk : BargainStrategy) (h : List ℝ) (y : ℝ) :
    ℝ :=
  if acceptAt σc σk h y = true then 1 - y else b * countryPayoff b σc σk (h ++ [y])

/-- The creditors' payoff in the subgame starting at the response node where `y` has just been
offered at history `h`. (O&R Appendix 6A, footnote 73, p. 421.) -/
noncomputable def creditorRespPayoff (a : ℝ) (σc σk : BargainStrategy) (h : List ℝ) (y : ℝ) :
    ℝ :=
  if acceptAt σc σk h y = true then y else a * creditorPayoff a σc σk (h ++ [y])

/-- Bounding an outcome value: if `0 ≤ E` and `dᵏ · val k ≤ E` at every `k` where agreement
could occur, the outcome value is at most `E`. (O&R Appendix 6A, footnote 73, p. 421.) -/
theorem outcomeValue_le {d E : ℝ} {agreed : ℕ → Prop} {val : ℕ → ℝ} (hE : 0 ≤ E)
    (h : ∀ k, agreed k → d ^ k * val k ≤ E) : outcomeValue d agreed val ≤ E := by
  classical
  unfold outcomeValue
  split_ifs with hex
  · exact h _ (Nat.find_spec hex)
  · exact hE

/-- An outcome value is nonnegative if every possible agreement value is.
(O&R Appendix 6A, footnote 73, p. 421.) -/
theorem outcomeValue_nonneg {d : ℝ} {agreed : ℕ → Prop} {val : ℕ → ℝ}
    (h : ∀ k, agreed k → 0 ≤ d ^ k * val k) : 0 ≤ outcomeValue d agreed val := by
  classical
  unfold outcomeValue
  split_ifs with hex
  · exact h _ (Nat.find_spec hex)
  · exact le_rfl

/-- Two outcome values for the same agreement event add up to at most `E` if they do at every
possible agreement date. (O&R Appendix 6A, footnote 73, p. 421.) -/
theorem outcomeValue_add_le {d₁ d₂ E : ℝ} {agreed : ℕ → Prop} {v₁ v₂ : ℕ → ℝ} (hE : 0 ≤ E)
    (h : ∀ k, agreed k → d₁ ^ k * v₁ k + d₂ ^ k * v₂ k ≤ E) :
    outcomeValue d₁ agreed v₁ + outcomeValue d₂ agreed v₂ ≤ E := by
  classical
  unfold outcomeValue
  split_ifs with hex
  · exact h _ (Nat.find_spec hex)
  · simpa using hE

/-- An outcome value when agreement occurs at once: `val 0`.
(O&R Appendix 6A, footnote 73, p. 421.) -/
theorem outcomeValue_of_agreed {d : ℝ} {agreed : ℕ → Prop} {val : ℕ → ℝ} (h0 : agreed 0) :
    outcomeValue d agreed val = val 0 := by
  classical
  have hex : ∃ k, agreed k := ⟨0, h0⟩
  have hn : Nat.find hex = 0 := (Nat.find_eq_zero hex).mpr h0
  unfold outcomeValue
  rw [dite_eq_left_of_eq_true (eq_true hex), hn, pow_zero, one_mul]

/-- The one-step recursion of an outcome value when the first offer is rejected: the
continuation is discounted once. (O&R Appendix 6A, footnote 73, p. 421.) -/
theorem outcomeValue_of_not_agreed {d : ℝ} {agreed : ℕ → Prop} {val : ℕ → ℝ} (h0 : ¬ agreed 0) :
    outcomeValue d agreed val =
      d * outcomeValue d (fun k => agreed (k + 1)) fun k => val (k + 1) := by
  classical
  unfold outcomeValue
  by_cases hex : ∃ k, agreed k
  · have hex' : ∃ k, agreed (k + 1) := by
      obtain ⟨k, hk⟩ := hex
      rcases k with _ | k
      · exact absurd hk h0
      · exact ⟨k, hk⟩
    rw [dite_eq_left_of_eq_true (eq_true hex), dite_eq_left_of_eq_true (eq_true hex'),
      Nat.find_comp_succ hex hex' h0, pow_succ]
    ring
  · have hex' : ¬ ∃ k, agreed (k + 1) := fun ⟨k, hk⟩ => hex ⟨k + 1, hk⟩
    rw [dite_eq_right_of_eq_false (eq_false hex), dite_eq_right_of_eq_false (eq_false hex'),
      mul_zero]

/-- The length of the history along the path of play: `|play h k| = |h| + k`.
(O&R Appendix 6A, footnote 73, p. 421.) -/
theorem play_length (σc σk : BargainStrategy) (h : List ℝ) (k : ℕ) :
    (play σc σk h k).length = h.length + k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [play, ih, add_assoc]

/-- Shifting the path of play: after the first offer is rejected, play continues from
`h ++ [offer]`. (O&R Appendix 6A, footnote 73, p. 421.) -/
theorem play_succ (σc σk : BargainStrategy) (h : List ℝ) (k : ℕ) :
    play σc σk h (k + 1) = play σc σk (h ++ [offerAt σc σk h]) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [play, ih, play]

/-- The country's payoff at a proposal node equals its payoff at the response node reached by
the proposer's offer (the game's recursive structure). (O&R Appendix 6A, footnote 73, p. 421.) -/
theorem countryPayoff_eq_resp (b : ℝ) (σc σk : BargainStrategy) (h : List ℝ) :
    countryPayoff b σc σk h = countryRespPayoff b σc σk h (offerAt σc σk h) := by
  unfold countryPayoff countryRespPayoff
  by_cases h0 : AgreedAt σc σk h 0
  · rw [outcomeValue_of_agreed h0]
    have : acceptAt σc σk h (offerAt σc σk h) = true := h0
    simp only [this, ↓reduceIte, play]
  · rw [outcomeValue_of_not_agreed h0]
    have : ¬ acceptAt σc σk h (offerAt σc σk h) = true := h0
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    unfold countryPayoff
    simp only [AgreedAt, play_succ]
    rfl

/-- The creditors' payoff at a proposal node equals their payoff at the response node reached by
the proposer's offer. (O&R Appendix 6A, footnote 73, p. 421.) -/
theorem creditorPayoff_eq_resp (a : ℝ) (σc σk : BargainStrategy) (h : List ℝ) :
    creditorPayoff a σc σk h = creditorRespPayoff a σc σk h (offerAt σc σk h) := by
  unfold creditorPayoff creditorRespPayoff
  by_cases h0 : AgreedAt σc σk h 0
  · rw [outcomeValue_of_agreed h0]
    have : acceptAt σc σk h (offerAt σc σk h) = true := h0
    simp only [this, ↓reduceIte, play]
  · rw [outcomeValue_of_not_agreed h0]
    have : ¬ acceptAt σc σk h (offerAt σc σk h) = true := h0
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    unfold creditorPayoff
    simp only [AgreedAt, play_succ]
    rfl

/-- Payoffs depend only on behaviour at histories at least as long as the current one: if two
profiles make the same offers and responses at all histories of length `≥ L`, they give the same
payoffs at every proposal node of length `≥ L`. (O&R Appendix 6A, footnote 73, p. 421.) -/
theorem payoffs_congr {σc σk σc' σk' : BargainStrategy} {L : ℕ}
    (hagree : ∀ g : List ℝ, L ≤ g.length →
      offerAt σc σk g = offerAt σc' σk' g ∧ ∀ y, acceptAt σc σk g y = acceptAt σc' σk' g y)
    {h : List ℝ} (hh : L ≤ h.length) (a b : ℝ) :
    countryPayoff b σc σk h = countryPayoff b σc' σk' h ∧
      creditorPayoff a σc σk h = creditorPayoff a σc' σk' h := by
  have hp : ∀ k, play σc σk h k = play σc' σk' h k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have hl : L ≤ (play σc σk h k).length := by rw [play_length]; omega
      rw [play, play, ih, ← ih, (hagree _ hl).1]
  have hA : AgreedAt σc σk h = AgreedAt σc' σk' h := by
    funext k
    have hl : L ≤ (play σc σk h k).length := by rw [play_length]; omega
    unfold AgreedAt
    rw [(hagree _ hl).1, (hagree _ hl).2, hp k]
  have hO : (fun k => offerAt σc σk (play σc σk h k)) =
      fun k => offerAt σc' σk' (play σc' σk' h k) := by
    funext k
    have hl : L ≤ (play σc σk h k).length := by rw [play_length]; omega
    rw [(hagree _ hl).1, hp k]
  unfold countryPayoff creditorPayoff
  rw [hA]
  constructor
  · congr 1
    funext k
    exact congrArg (fun f => 1 - f k) hO
  · rw [hO]

/-- The path of play stays admissible under valid strategies.
(O&R Appendix 6A, footnote 73, p. 421.) -/
theorem play_admissible {σc σk : BargainStrategy} (hc : ValidStrategy σc)
    (hk : ValidStrategy σk) {h : List ℝ} (hh : Admissible h) (k : ℕ) :
    Admissible (play σc σk h k) := by
  induction k with
  | zero => exact hh
  | succ k ih =>
    intro z hz
    rw [play, List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | hz
    · exact ih z hz
    · rw [hz]
      unfold offerAt
      split_ifs
      · exact hc _ ih
      · exact hk _ ih

/-- Offers along the path of play are shares in `[0, 1]` under valid strategies.
(O&R Appendix 6A, footnote 73, p. 421.) -/
theorem offer_mem {σc σk : BargainStrategy} (hc : ValidStrategy σc) (hk : ValidStrategy σk)
    {g : List ℝ} (hg : Admissible g) : offerAt σc σk g ∈ Icc (0 : ℝ) 1 := by
  unfold offerAt
  split_ifs
  · exact hc _ hg
  · exact hk _ hg

/-- Payoffs are in `[0, 1]` and sum to at most one (with `0 ≤ a, b ≤ 1`): in every subgame the
two players cannot jointly get more than the pie. (O&R Appendix 6A, footnote 73, p. 421.) -/
theorem payoffs_bounds {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    {σc σk : BargainStrategy} (hc : ValidStrategy σc) (hk : ValidStrategy σk) {h : List ℝ}
    (hh : Admissible h) :
    0 ≤ countryPayoff b σc σk h ∧ 0 ≤ creditorPayoff a σc σk h ∧
      countryPayoff b σc σk h + creditorPayoff a σc σk h ≤ 1 := by
  have hk' : ∀ k, offerAt σc σk (play σc σk h k) ∈ Icc (0 : ℝ) 1 := fun k =>
    offer_mem hc hk (play_admissible hc hk hh k)
  unfold countryPayoff creditorPayoff
  refine ⟨outcomeValue_nonneg fun k _ => ?_, outcomeValue_nonneg fun k _ => ?_,
    outcomeValue_add_le zero_le_one fun k _ => ?_⟩
  · exact mul_nonneg (pow_nonneg hb0 k) (by linarith [(hk' k).2])
  · exact mul_nonneg (pow_nonneg ha0 k) (hk' k).1
  · have hbn : b ^ k ≤ 1 := pow_le_one₀ hb0 hb1
    have han : a ^ k ≤ 1 := pow_le_one₀ ha0 ha1
    have hb' : 0 ≤ b ^ k := pow_nonneg hb0 k
    have ha' : 0 ≤ a ^ k := pow_nonneg ha0 k
    nlinarith [(hk' k).1, (hk' k).2]

/-! ### Subgame-perfect equilibrium -/

/-- Subgame-perfect equilibrium of the alternating-offers game (discount factors `a` for the
creditors, `b` for the country): both strategies are valid, and in every subgame — at every
admissible proposal node `h` and at every response node `(h, y)` with `y ∈ [0, 1]` — neither
player can gain by switching to any other valid strategy. (O&R Appendix 6A, footnote 73, p. 421.) -/
def IsSPE (a b : ℝ) (σc σk : BargainStrategy) : Prop :=
  ValidStrategy σc ∧ ValidStrategy σk ∧
    (∀ h, Admissible h → ∀ τ, ValidStrategy τ →
      countryPayoff b τ σk h ≤ countryPayoff b σc σk h) ∧
    (∀ h, Admissible h → ∀ τ, ValidStrategy τ →
      creditorPayoff a σc τ h ≤ creditorPayoff a σc σk h) ∧
    (∀ h, Admissible h → ∀ y ∈ Icc (0 : ℝ) 1, ∀ τ, ValidStrategy τ →
      countryRespPayoff b τ σk h y ≤ countryRespPayoff b σc σk h y) ∧
    (∀ h, Admissible h → ∀ y ∈ Icc (0 : ℝ) 1, ∀ τ, ValidStrategy τ →
      creditorRespPayoff a σc τ h y ≤ creditorRespPayoff a σc σk h y)

/-- The strategy `σ` with its proposal at the single history `h` replaced by `y` (a one-shot
deviation). (O&R Appendix 6A, footnote 73, p. 421.) -/
noncomputable def withProposal (σ : BargainStrategy) (h : List ℝ) (y : ℝ) : BargainStrategy := by
  classical
  exact ⟨fun g => if g = h then y else σ.propose g, σ.respond⟩

/-- The strategy `σ` with its response to `y` at the single history `h` replaced by `v`.
(O&R Appendix 6A, footnote 73, p. 421.) -/
noncomputable def withResponse (σ : BargainStrategy) (h : List ℝ) (y : ℝ) (v : Bool) :
    BargainStrategy := by
  classical
  exact ⟨σ.propose, fun g z => if g = h ∧ z = y then v else σ.respond g z⟩

/-- One-shot deviations of a valid strategy are valid (for an offer `y ∈ [0, 1]`).
(O&R Appendix 6A, footnote 73, p. 421.) -/
theorem withProposal_valid {σ : BargainStrategy} (hσ : ValidStrategy σ) (h : List ℝ) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) : ValidStrategy (withProposal σ h y) := by
  intro g hg
  unfold withProposal
  simp only
  split_ifs
  · exact hy
  · exact hσ g hg

/-- Response deviations of a valid strategy are valid. (O&R Appendix 6A, footnote 73, p. 421.) -/
theorem withResponse_valid {σ : BargainStrategy} (hσ : ValidStrategy σ) (h : List ℝ) (y : ℝ)
    (v : Bool) : ValidStrategy (withResponse σ h y v) := fun g hg => hσ g hg

/-- A one-shot deviation at `h` does not affect play after `h`: the continuation payoffs at
`h ++ [y]` are unchanged (country deviating). (O&R Appendix 6A, footnote 73, p. 421.) -/
theorem continuation_country_dev (σc σk τc : BargainStrategy) (h : List ℝ) (y a b : ℝ)
    (hag : ∀ g : List ℝ, g ≠ h →
      τc.propose g = σc.propose g ∧ ∀ z, τc.respond g z = σc.respond g z) :
    countryPayoff b τc σk (h ++ [y]) = countryPayoff b σc σk (h ++ [y]) ∧
      creditorPayoff a τc σk (h ++ [y]) = creditorPayoff a σc σk (h ++ [y]) := by
  apply payoffs_congr (L := h.length + 1)
  · intro g hg
    have hne : g ≠ h := by rintro rfl; omega
    unfold offerAt acceptAt
    refine ⟨by rw [(hag g hne).1], fun z => by rw [(hag g hne).2 z]⟩
  · simp

/-- A one-shot deviation at `h` does not affect play after `h` (creditors deviating).
(O&R Appendix 6A, footnote 73, p. 421.) -/
theorem continuation_creditor_dev (σc σk τk : BargainStrategy) (h : List ℝ) (y a b : ℝ)
    (hag : ∀ g : List ℝ, g ≠ h →
      τk.propose g = σk.propose g ∧ ∀ z, τk.respond g z = σk.respond g z) :
    countryPayoff b σc τk (h ++ [y]) = countryPayoff b σc σk (h ++ [y]) ∧
      creditorPayoff a σc τk (h ++ [y]) = creditorPayoff a σc σk (h ++ [y]) := by
  apply payoffs_congr (L := h.length + 1)
  · intro g hg
    have hne : g ≠ h := by rintro rfl; omega
    unfold offerAt acceptAt
    refine ⟨by rw [(hag g hne).1], fun z => by rw [(hag g hne).2 z]⟩
  · simp

/-- In an SPE the country, when proposing (`h` even), cannot gain by offering any other share
`y ∈ [0, 1]` once: `P₁(h) ≥` its payoff at the response node `(h, y)`.
(O&R Appendix 6A, footnote 73, p. 421.) -/
theorem spe_country_proposal {a b : ℝ} {σc σk : BargainStrategy} (hs : IsSPE a b σc σk)
    {h : List ℝ} (hh : Admissible h) (he : Even h.length) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    countryRespPayoff b σc σk h y ≤ countryPayoff b σc σk h := by
  set τ := withProposal σc h y
  have hag : ∀ g : List ℝ, g ≠ h →
      τ.propose g = σc.propose g ∧ ∀ z, τ.respond g z = σc.respond g z := by
    intro g hg
    simp only [τ, withProposal, hg, ↓reduceIte, implies_true, and_self]
  have hdev := hs.2.2.1 h hh τ (withProposal_valid hs.1 h hy)
  rw [countryPayoff_eq_resp] at hdev
  have hoff : offerAt τ σk h = y := by
    simp only [offerAt, he, ↓reduceIte, τ, withProposal]
  rw [hoff] at hdev
  have hcont := (continuation_country_dev σc σk τ h y a b hag).1
  have hacc : acceptAt τ σk h y = acceptAt σc σk h y := by simp only [acceptAt, he, ↓reduceIte]
  unfold countryRespPayoff at hdev ⊢
  rw [hacc, hcont] at hdev
  exact hdev

/-- In an SPE the creditors, when proposing (`h` odd), cannot gain by offering any other share
`y ∈ [0, 1]` once. (O&R Appendix 6A, footnote 73, p. 421.) -/
theorem spe_creditor_proposal {a b : ℝ} {σc σk : BargainStrategy} (hs : IsSPE a b σc σk)
    {h : List ℝ} (hh : Admissible h) (ho : ¬ Even h.length) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    creditorRespPayoff a σc σk h y ≤ creditorPayoff a σc σk h := by
  set τ := withProposal σk h y
  have hag : ∀ g : List ℝ, g ≠ h →
      τ.propose g = σk.propose g ∧ ∀ z, τ.respond g z = σk.respond g z := by
    intro g hg
    simp only [τ, withProposal, hg, ↓reduceIte, implies_true, and_self]
  have hdev := hs.2.2.2.1 h hh τ (withProposal_valid hs.2.1 h hy)
  rw [creditorPayoff_eq_resp] at hdev
  have hoff : offerAt σc τ h = y := by
    simp only [offerAt, ho, ↓reduceIte, τ, withProposal]
  rw [hoff] at hdev
  have hcont := (continuation_creditor_dev σc σk τ h y a b hag).2
  have hacc : acceptAt σc τ h y = acceptAt σc σk h y := by simp only [acceptAt, ho, ↓reduceIte]
  unfold creditorRespPayoff at hdev ⊢
  rw [hacc, hcont] at hdev
  exact hdev

/-- In an SPE the creditors, responding to the country's offer `y` (`h` even), get at least `y`
(they could accept) and at least `a` times their continuation payoff (they could reject).
(O&R Appendix 6A, footnote 73, p. 421.) -/
theorem spe_creditor_response {a b : ℝ} {σc σk : BargainStrategy} (hs : IsSPE a b σc σk)
    {h : List ℝ} (hh : Admissible h) (he : Even h.length) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    y ≤ creditorRespPayoff a σc σk h y ∧
      a * creditorPayoff a σc σk (h ++ [y]) ≤ creditorRespPayoff a σc σk h y := by
  have hagv : ∀ v, ∀ g : List ℝ, g ≠ h → (withResponse σk h y v).propose g = σk.propose g ∧
      ∀ z, (withResponse σk h y v).respond g z = σk.respond g z := by
    intro v g hg
    simp only [withResponse, hg, false_and, ↓reduceIte, implies_true, and_self]
  constructor
  · have hdev := hs.2.2.2.2.2 h hh y hy _ (withResponse_valid hs.2.1 h y true)
    have hacc : acceptAt σc (withResponse σk h y true) h y = true := by
      simp only [acceptAt, he, ↓reduceIte, withResponse, and_self]
    unfold creditorRespPayoff at hdev ⊢
    rw [hacc] at hdev
    simpa using hdev
  · have hdev := hs.2.2.2.2.2 h hh y hy _ (withResponse_valid hs.2.1 h y false)
    have hacc : acceptAt σc (withResponse σk h y false) h y = false := by
      simp only [acceptAt, he, ↓reduceIte, withResponse, and_self]
    have hcont := (continuation_creditor_dev σc σk (withResponse σk h y false) h y a b
      (hagv false)).2
    unfold creditorRespPayoff at hdev ⊢
    rw [hacc, hcont] at hdev
    simpa using hdev

/-- In an SPE the country, responding to the creditors' offer `y` (`h` odd), gets at least
`1 − y` (it could accept) and at least `b` times its continuation payoff (it could reject).
(O&R Appendix 6A, footnote 73, p. 421.) -/
theorem spe_country_response {a b : ℝ} {σc σk : BargainStrategy} (hs : IsSPE a b σc σk)
    {h : List ℝ} (hh : Admissible h) (ho : ¬ Even h.length) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    1 - y ≤ countryRespPayoff b σc σk h y ∧
      b * countryPayoff b σc σk (h ++ [y]) ≤ countryRespPayoff b σc σk h y := by
  have hagv : ∀ v, ∀ g : List ℝ, g ≠ h → (withResponse σc h y v).propose g = σc.propose g ∧
      ∀ z, (withResponse σc h y v).respond g z = σc.respond g z := by
    intro v g hg
    simp only [withResponse, hg, false_and, ↓reduceIte, implies_true, and_self]
  constructor
  · have hdev := hs.2.2.2.2.1 h hh y hy _ (withResponse_valid hs.1 h y true)
    have hacc : acceptAt (withResponse σc h y true) σk h y = true := by
      simp only [acceptAt, ho, ↓reduceIte, withResponse, and_self]
    unfold countryRespPayoff at hdev ⊢
    rw [hacc] at hdev
    simpa using hdev
  · have hdev := hs.2.2.2.2.1 h hh y hy _ (withResponse_valid hs.1 h y false)
    have hacc : acceptAt (withResponse σc h y false) σk h y = false := by
      simp only [acceptAt, ho, ↓reduceIte, withResponse, and_self]
    have hcont := (continuation_country_dev σc σk (withResponse σc h y false) h y a b
      (hagv false)).1
    unfold countryRespPayoff at hdev ⊢
    rw [hacc, hcont] at hdev
    simpa using hdev

/-- Appending an admissible offer keeps a history admissible and flips the proposer.
(O&R Appendix 6A, footnote 73, p. 421.) -/
theorem admissible_append {g : List ℝ} (hg : Admissible g) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    Admissible (g ++ [y]) ∧ (Even (g ++ [y]).length ↔ ¬ Even g.length) := by
  refine ⟨fun z hz => ?_, by simp [Nat.even_add_one]⟩
  rw [List.mem_append, List.mem_singleton] at hz
  rcases hz with hz | hz
  · exact hg z hz
  · rw [hz]; exact hy

/-- A delayed agreement wastes surplus: if both discount factors are below one, payoffs
`b·P₁ + a·P₂` from a continuation with `P₁, P₂ ≥ 0`, `P₁ + P₂ ≤ 1` sum to strictly less than
one. (O&R Appendix 6A, footnote 73, p. 421.) -/
theorem delay_wastes {a b P₁ P₂ : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb1 : b < 1)
    (h1 : 0 ≤ P₁) (h2 : 0 ≤ P₂) (h12 : P₁ + P₂ ≤ 1) : b * P₁ + a * P₂ < 1 := by
  have hc : max a b < 1 := max_lt ha1 hb1
  have t1 : b * P₁ ≤ max a b * P₁ := mul_le_mul_of_nonneg_right (le_max_right a b) h1
  have t2 : a * P₂ ≤ max a b * P₂ := mul_le_mul_of_nonneg_right (le_max_left a b) h2
  have t3 : max a b * (P₁ + P₂) ≤ max a b :=
    by nlinarith [le_max_left a b]
  nlinarith

/-- UNIQUENESS of subgame-perfect equilibrium in the alternating-offers game (Rubinstein 1982;
the Shaked–Sutton sup/inf argument), O&R footnote 73: let `0 ≤ a < 1`, `0 ≤ b < 1`. In ANY
subgame-perfect equilibrium, at EVERY admissible history `h`:
* if the country proposes (`h` even), it offers the creditors exactly
  `x = a(1−b)/(1−ab)`, the creditors accept at once, and payoffs are `(1 − x, x)`;
* if the creditors propose (`h` odd), they claim exactly `x′ = (1−b)/(1−ab)`, the country accepts
  at once, and payoffs are `(1 − x′, x′)`.
Proof: with `M₁, m₁` the sup and inf of the country's payoff over subgames where it proposes and
`M₂, m₂` the creditors' over subgames where they propose, SPE gives `m₁ ≥ 1 − aM₂`,
`M₁ ≤ 1 − am₂`, `m₂ ≥ 1 − bM₁`, `M₂ ≤ 1 − bm₁`, which force `M₁ = m₁` and `M₂ = m₂`. -/
theorem spe_unique {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1)
    {σc σk : BargainStrategy} (hs : IsSPE a b σc σk) {h : List ℝ} (hh : Admissible h) :
    (Even h.length → countryPayoff b σc σk h = 1 - countryOfferShare a b ∧
        creditorPayoff a σc σk h = countryOfferShare a b ∧
        σc.propose h = countryOfferShare a b ∧ σk.respond h (σc.propose h) = true) ∧
      (¬ Even h.length → countryPayoff b σc σk h = 1 - creditorOfferShare a b ∧
        creditorPayoff a σc σk h = creditorOfferShare a b ∧
        σk.propose h = creditorOfferShare a b ∧ σc.respond h (σk.propose h) = true) := by
  have hc := hs.1
  have hk := hs.2.1
  have hbd := fun g (hg : Admissible g) =>
    payoffs_bounds ha0 ha1.le hb0 hb1.le hc hk (σc := σc) (σk := σk) hg
  set E1 := {v | ∃ g, Admissible g ∧ Even g.length ∧ v = countryPayoff b σc σk g} with hE1
  set E2 := {v | ∃ g, Admissible g ∧ ¬ Even g.length ∧ v = creditorPayoff a σc σk g} with hE2
  have hadm0 : Admissible ([] : List ℝ) := fun z hz => by simp at hz
  have hadm1 : Admissible [(0 : ℝ)] := fun z hz => by
    rw [List.mem_singleton] at hz; rw [hz]; exact ⟨le_rfl, zero_le_one⟩
  have hE1ne : E1.Nonempty := ⟨_, [], hadm0, by simp, rfl⟩
  have hE2ne : E2.Nonempty := ⟨_, [0], hadm1, by simp, rfl⟩
  have hE1a : BddAbove E1 := ⟨1, by
    rintro v ⟨g, hg, -, rfl⟩; linarith [(hbd g hg).1, (hbd g hg).2.1, (hbd g hg).2.2]⟩
  have hE1b : BddBelow E1 := ⟨0, by rintro v ⟨g, hg, -, rfl⟩; exact (hbd g hg).1⟩
  have hE2a : BddAbove E2 := ⟨1, by
    rintro v ⟨g, hg, -, rfl⟩; linarith [(hbd g hg).1, (hbd g hg).2.1, (hbd g hg).2.2]⟩
  have hE2b : BddBelow E2 := ⟨0, by rintro v ⟨g, hg, -, rfl⟩; exact (hbd g hg).2.1⟩
  set M₁ := sSup E1
  set m₁ := sInf E1
  set M₂ := sSup E2
  set m₂ := sInf E2
  have mem1 : ∀ g, Admissible g → Even g.length →
      m₁ ≤ countryPayoff b σc σk g ∧ countryPayoff b σc σk g ≤ M₁ := fun g hg he =>
    ⟨csInf_le hE1b ⟨g, hg, he, rfl⟩, le_csSup hE1a ⟨g, hg, he, rfl⟩⟩
  have mem2 : ∀ g, Admissible g → ¬ Even g.length →
      m₂ ≤ creditorPayoff a σc σk g ∧ creditorPayoff a σc σk g ≤ M₂ := fun g hg ho =>
    ⟨csInf_le hE2b ⟨g, hg, ho, rfl⟩, le_csSup hE2a ⟨g, hg, ho, rfl⟩⟩
  have hM₂0 : 0 ≤ M₂ := le_trans (hbd [0] hadm1).2.1 (mem2 [0] hadm1 (by simp)).2
  have hM₂1 : M₂ ≤ 1 := csSup_le hE2ne (by
    rintro v ⟨g, hg, -, rfl⟩; linarith [(hbd g hg).1, (hbd g hg).2.2])
  have hM₁0 : 0 ≤ M₁ := le_trans (hbd [] hadm0).1 (mem1 [] hadm0 (by simp)).2
  have hM₁1 : M₁ ≤ 1 := csSup_le hE1ne (by
    rintro v ⟨g, hg, -, rfl⟩; linarith [(hbd g hg).2.1, (hbd g hg).2.2])
  -- (A2), (B2): the responder can always reject
  have A2 : ∀ g, Admissible g → Even g.length → a * m₂ ≤ creditorPayoff a σc σk g := by
    intro g hg he
    have hy := offer_mem hc hk (σc := σc) (σk := σk) hg
    obtain ⟨hadm, hpar⟩ := admissible_append hg hy
    rw [creditorPayoff_eq_resp]
    refine le_trans ?_ (spe_creditor_response hs hg he hy).2
    exact mul_le_mul_of_nonneg_left (mem2 _ hadm (by rw [hpar]; exact not_not.mpr he)).1 ha0
  have B2 : ∀ g, Admissible g → ¬ Even g.length → b * m₁ ≤ countryPayoff b σc σk g := by
    intro g hg ho
    have hy := offer_mem hc hk (σc := σc) (σk := σk) hg
    obtain ⟨hadm, hpar⟩ := admissible_append hg hy
    rw [countryPayoff_eq_resp]
    refine le_trans ?_ (spe_country_response hs hg ho hy).2
    exact mul_le_mul_of_nonneg_left (mem1 _ hadm (by rw [hpar]; exact ho)).1 hb0
  -- (A1), (B1): the proposer can always make an offer that must be accepted
  have A1 : ∀ g, Admissible g → Even g.length → 1 - a * M₂ ≤ countryPayoff b σc σk g := by
    intro g hg he
    by_contra hlt
    push Not at hlt
    set P := countryPayoff b σc σk g
    have hP0 := (hbd g hg).1
    set y := (a * M₂ + (1 - P)) / 2 with hy
    have haM : 0 ≤ a * M₂ := mul_nonneg ha0 hM₂0
    have hy1 : a * M₂ < y := by rw [hy]; linarith
    have hy2 : y < 1 - P := by rw [hy]; linarith
    have hyI : y ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    obtain ⟨hadm, hpar⟩ := admissible_append hg hyI
    have hprop := spe_country_proposal hs hg he hyI
    have hacc : acceptAt σc σk g y = true := by
      by_contra hrej
      have hresp := (spe_creditor_response hs hg he hyI).1
      unfold creditorRespPayoff at hresp
      simp only [hrej, ↓reduceIte] at hresp
      have := mul_le_mul_of_nonneg_left (mem2 _ hadm (by rw [hpar]; exact not_not.mpr he)).2 ha0
      linarith
    unfold countryRespPayoff at hprop
    simp only [hacc, ↓reduceIte] at hprop
    linarith
  have B1 : ∀ g, Admissible g → ¬ Even g.length → 1 - b * M₁ ≤ creditorPayoff a σc σk g := by
    intro g hg ho
    by_contra hlt
    push Not at hlt
    set P := creditorPayoff a σc σk g
    have hP0 := (hbd g hg).2.1
    set y := 1 - (b * M₁ + (1 - P)) / 2 with hy
    have hbM : 0 ≤ b * M₁ := mul_nonneg hb0 hM₁0
    have hy1 : 1 - y > b * M₁ := by rw [hy]; linarith
    have hy2 : P < y := by rw [hy]; linarith
    have hyI : y ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    obtain ⟨hadm, hpar⟩ := admissible_append hg hyI
    have hprop := spe_creditor_proposal hs hg ho hyI
    have hacc : acceptAt σc σk g y = true := by
      by_contra hrej
      have hresp := (spe_country_response hs hg ho hyI).1
      unfold countryRespPayoff at hresp
      simp only [hrej, ↓reduceIte] at hresp
      have := mul_le_mul_of_nonneg_left (mem1 _ hadm (by rw [hpar]; exact ho)).2 hb0
      linarith
    unfold creditorRespPayoff at hprop
    simp only [hacc, ↓reduceIte] at hprop
    linarith
  -- the four Shaked–Sutton inequalities
  have hm1 : 1 - a * M₂ ≤ m₁ := le_csInf hE1ne (by rintro v ⟨g, hg, he, rfl⟩; exact A1 g hg he)
  have hM1 : M₁ ≤ 1 - a * m₂ := csSup_le hE1ne (by
    rintro v ⟨g, hg, he, rfl⟩; linarith [A2 g hg he, (hbd g hg).2.2])
  have hm2 : 1 - b * M₁ ≤ m₂ := le_csInf hE2ne (by rintro v ⟨g, hg, ho, rfl⟩; exact B1 g hg ho)
  have hM2 : M₂ ≤ 1 - b * m₁ := csSup_le hE2ne (by
    rintro v ⟨g, hg, ho, rfl⟩; linarith [B2 g hg ho, (hbd g hg).2.2])
  have hmM1 : m₁ ≤ M₁ := (mem1 [] hadm0 (by simp)).1.trans (mem1 [] hadm0 (by simp)).2
  have hmM2 : m₂ ≤ M₂ := (mem2 [0] hadm1 (by simp)).1.trans (mem2 [0] hadm1 (by simp)).2
  have hs0 : 0 < 1 - a * b := by nlinarith
  have hs0' : 1 - a * b ≠ 0 := hs0.ne'
  have e_a : 1 - b * ((1 - a) / (1 - a * b)) = (1 - b) / (1 - a * b) := by
    rw [mul_div_assoc', one_sub_div hs0']; congr 1; ring
  have t1 := mul_le_mul_of_nonneg_left hm2 ha0
  have t2 := mul_le_mul_of_nonneg_left hM2 ha0
  have hM1' : M₁ * (1 - a * b) ≤ 1 - a := by nlinarith
  have hm1' : 1 - a ≤ m₁ * (1 - a * b) := by nlinarith
  have heq1 : M₁ = (1 - a) / (1 - a * b) := by
    rw [eq_div_iff hs0.ne']; nlinarith
  have heqm1 : m₁ = (1 - a) / (1 - a * b) := by
    rw [eq_div_iff hs0.ne']; nlinarith
  have heq2 : M₂ = (1 - b) / (1 - a * b) := by
    apply le_antisymm
    · calc M₂ ≤ 1 - b * m₁ := hM2
        _ = (1 - b) / (1 - a * b) := by rw [heqm1, e_a]
    · calc (1 - b) / (1 - a * b) = 1 - b * M₁ := by rw [heq1, e_a]
        _ ≤ m₂ := hm2
        _ ≤ M₂ := hmM2
  have heqm2 : m₂ = (1 - b) / (1 - a * b) := by
    apply le_antisymm
    · rw [← heq2]; exact hmM2
    · calc (1 - b) / (1 - a * b) = 1 - b * M₁ := by rw [heq1, e_a]
        _ ≤ m₂ := hm2
  have hx1 : 1 - countryOfferShare a b = (1 - a) / (1 - a * b) := by
    unfold countryOfferShare; rw [one_sub_div hs0']; congr 1; ring
  have hx2 : 1 - creditorOfferShare a b = b * ((1 - a) / (1 - a * b)) := by
    unfold creditorOfferShare; rw [one_sub_div hs0', mul_div_assoc']; congr 1; ring
  constructor
  · intro he
    have hP1 : countryPayoff b σc σk h = 1 - countryOfferShare a b := by
      rw [hx1]; apply le_antisymm
      · rw [← heq1]; exact (mem1 h hh he).2
      · rw [← heqm1]; exact (mem1 h hh he).1
    have hP2 : creditorPayoff a σc σk h = countryOfferShare a b := by
      apply le_antisymm
      · linarith [(hbd h hh).2.2]
      · have := A2 h hh he
        rw [heqm2] at this
        unfold countryOfferShare
        rw [mul_div_assoc]
        exact this
    have hy := offer_mem hc hk (σc := σc) (σk := σk) hh
    have hacc : acceptAt σc σk h (offerAt σc σk h) = true := by
      by_contra hrej
      have e1 := countryPayoff_eq_resp b σc σk h
      have e2 := creditorPayoff_eq_resp a σc σk h
      unfold countryRespPayoff at e1
      unfold creditorRespPayoff at e2
      simp only [hrej, ↓reduceIte] at e1 e2
      obtain ⟨hadm, -⟩ := admissible_append hh hy
      obtain ⟨p1, p2, p12⟩ := hbd _ hadm
      have := delay_wastes ha0 ha1 hb1 p1 p2 p12
      linarith
    have hoff : offerAt σc σk h = σc.propose h := by simp [offerAt, he]
    have hresp : acceptAt σc σk h (offerAt σc σk h) = σk.respond h (offerAt σc σk h) := by
      simp [acceptAt, he]
    have e2 := creditorPayoff_eq_resp a σc σk h
    unfold creditorRespPayoff at e2
    simp only [hacc, ↓reduceIte] at e2
    refine ⟨hP1, hP2, by rw [← hoff, ← e2, hP2], ?_⟩
    rw [← hoff, ← hresp]
    exact hacc
  · intro ho
    have hP2 : creditorPayoff a σc σk h = creditorOfferShare a b := by
      unfold creditorOfferShare
      apply le_antisymm
      · rw [← heq2]; exact (mem2 h hh ho).2
      · rw [← heqm2]; exact (mem2 h hh ho).1
    have hP1 : countryPayoff b σc σk h = 1 - creditorOfferShare a b := by
      apply le_antisymm
      · linarith [(hbd h hh).2.2]
      · have := B2 h hh ho
        rw [heqm1] at this
        rw [hx2]
        exact this
    have hy := offer_mem hc hk (σc := σc) (σk := σk) hh
    have hacc : acceptAt σc σk h (offerAt σc σk h) = true := by
      by_contra hrej
      have e1 := countryPayoff_eq_resp b σc σk h
      have e2 := creditorPayoff_eq_resp a σc σk h
      unfold countryRespPayoff at e1
      unfold creditorRespPayoff at e2
      simp only [hrej, ↓reduceIte] at e1 e2
      obtain ⟨hadm, -⟩ := admissible_append hh hy
      obtain ⟨p1, p2, p12⟩ := hbd _ hadm
      have := delay_wastes ha0 ha1 hb1 p1 p2 p12
      linarith
    have hoff : offerAt σc σk h = σk.propose h := by simp [offerAt, ho]
    have hresp : acceptAt σc σk h (offerAt σc σk h) = σc.respond h (offerAt σc σk h) := by
      simp [acceptAt, ho]
    have e2 := creditorPayoff_eq_resp a σc σk h
    unfold creditorRespPayoff at e2
    simp only [hacc, ↓reduceIte] at e2
    refine ⟨hP1, hP2, by rw [← hoff, ← e2, hP2], ?_⟩
    rw [← hoff, ← hresp]
    exact hacc

/-! ### Existence: the stationary strategies of footnote 73 -/

/-- The country's stationary strategy, footnote 73: always offer the creditors `x`; accept a
creditors' claim `y` iff `y ≤ x′`. -/
noncomputable def statCountry (x x' : ℝ) : BargainStrategy :=
  ⟨fun _ => x, fun _ y => decide (y ≤ x')⟩

/-- The creditors' stationary strategy, footnote 73: always claim `x′`; accept the country's
offer `y` iff `y ≥ x`. -/
noncomputable def statCreditor (x x' : ℝ) : BargainStrategy :=
  ⟨fun _ => x', fun _ y => decide (x ≤ y)⟩

/-- Payoffs under the stationary profile: `(1 − x, x)` where the country proposes and
`(1 − x′, x′)` where the creditors propose, provided `x ≤ x′` (agreement is immediate).
(O&R Appendix 6A, footnote 73, p. 421.) -/
theorem stat_payoffs {a b x x' : ℝ} (h : List ℝ) :
    countryPayoff b (statCountry x x') (statCreditor x x') h =
        (if Even h.length then 1 - x else 1 - x') ∧
      creditorPayoff a (statCountry x x') (statCreditor x x') h =
        (if Even h.length then x else x') := by
  rw [countryPayoff_eq_resp, creditorPayoff_eq_resp]
  unfold countryRespPayoff creditorRespPayoff
  by_cases he : Even h.length
  · simp [offerAt, acceptAt, he, statCountry, statCreditor]
  · simp [offerAt, acceptAt, he, statCountry, statCreditor]

/-- Parity along the path: `|play h k|` is even iff `|h|` and `k` have the same parity.
(O&R Appendix 6A, footnote 73, p. 421.) -/
theorem play_even_iff (σc σk : BargainStrategy) (h : List ℝ) (k : ℕ) :
    Even (play σc σk h k).length ↔ (Even h.length ↔ Even k) := by
  rw [play_length, Nat.even_add]

/-- Against the creditors' stationary strategy no country strategy does better than the
stationary payoff, in any subgame (`x ≤ x′ ≤ 1`, `1 − x′ = b(1 − x)`, `0 ≤ b ≤ 1`).
(O&R Appendix 6A, footnote 73, p. 421.) -/
theorem stat_country_best {b x x' : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hxx : x ≤ x') (hx'1 : x' ≤ 1) (hrel : 1 - x' = b * (1 - x)) (τ : BargainStrategy)
    (h : List ℝ) :
    countryPayoff b τ (statCreditor x x') h ≤ (if Even h.length then 1 - x else 1 - x') := by
  have hE : 0 ≤ (if Even h.length then 1 - x else 1 - x') := by split_ifs <;> linarith
  unfold countryPayoff
  refine outcomeValue_le hE fun k hk => ?_
  have hbk : b ^ k ≤ 1 := pow_le_one₀ hb0 hb1
  have hbk0 : 0 ≤ b ^ k := pow_nonneg hb0 k
  have hpar := play_even_iff τ (statCreditor x x') h k
  unfold AgreedAt at hk
  set g := play τ (statCreditor x x') h k with hgdef
  by_cases hg : Even g.length
  · -- the country proposed and the creditors accepted: the offer was at least `x`
    have hoff : offerAt τ (statCreditor x x') g = τ.propose g := by simp [offerAt, hg]
    have hacc : acceptAt τ (statCreditor x x') g (τ.propose g) = decide (x ≤ τ.propose g) := by
      simp [acceptAt, hg, statCreditor]
    rw [hoff, hacc, decide_eq_true_eq] at hk
    rw [hoff]
    have hv : b ^ k * (1 - τ.propose g) ≤ b ^ k * (1 - x) :=
      mul_le_mul_of_nonneg_left (by linarith) hbk0
    by_cases he : Even h.length
    · simp only [he, ↓reduceIte]; nlinarith
    · simp only [he, ↓reduceIte]
      have hk0 : k ≠ 0 := by
        rintro rfl; exact he ((hpar.mp hg).mpr (by simp))
      have := pow_le_of_le_one hb0 hb1 hk0
      nlinarith
  · -- the creditors proposed `x′` and the country accepted
    have hoff : offerAt τ (statCreditor x x') g = x' := by simp [offerAt, hg, statCreditor]
    rw [hoff]
    by_cases he : Even h.length
    · simp only [he, ↓reduceIte]; nlinarith
    · simp only [he, ↓reduceIte]; nlinarith

/-- Against the country's stationary strategy no creditors' strategy does better than the
stationary payoff, in any subgame (`0 ≤ x ≤ x′`, `x = a x′`, `0 ≤ a ≤ 1`).
(O&R Appendix 6A, footnote 73, p. 421.) -/
theorem stat_creditor_best {a x x' : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx0 : 0 ≤ x)
    (hxx : x ≤ x') (hrel : x = a * x') (τ : BargainStrategy) (h : List ℝ) :
    creditorPayoff a (statCountry x x') τ h ≤ (if Even h.length then x else x') := by
  have hE : 0 ≤ (if Even h.length then x else x') := by split_ifs <;> linarith
  unfold creditorPayoff
  refine outcomeValue_le hE fun k hk => ?_
  have hak : a ^ k ≤ 1 := pow_le_one₀ ha0 ha1
  have hak0 : 0 ≤ a ^ k := pow_nonneg ha0 k
  have hpar := play_even_iff (statCountry x x') τ h k
  unfold AgreedAt at hk
  set g := play (statCountry x x') τ h k with hgdef
  by_cases hg : Even g.length
  · -- the country offered `x` and the creditors accepted
    have hoff : offerAt (statCountry x x') τ g = x := by simp [offerAt, hg, statCountry]
    rw [hoff]
    by_cases he : Even h.length
    · simp only [he, ↓reduceIte]; nlinarith
    · simp only [he, ↓reduceIte]; nlinarith
  · -- the creditors claimed `z` and the country accepted: `z ≤ x′`
    have hoff : offerAt (statCountry x x') τ g = τ.propose g := by simp [offerAt, hg]
    have hacc : acceptAt (statCountry x x') τ g (τ.propose g) = decide (τ.propose g ≤ x') := by
      simp [acceptAt, hg, statCountry]
    rw [hoff, hacc, decide_eq_true_eq] at hk
    rw [hoff]
    have hv : a ^ k * τ.propose g ≤ a ^ k * x' := mul_le_mul_of_nonneg_left hk hak0
    by_cases he : Even h.length
    · simp only [he, ↓reduceIte]
      have hk0 : k ≠ 0 := by
        rintro rfl; exact hg (hpar.mpr (by simp [he]))
      have := pow_le_of_le_one ha0 ha1 hk0
      nlinarith
    · simp only [he, ↓reduceIte]; nlinarith

/-- EXISTENCE: the stationary strategies of footnote 73 form a subgame-perfect equilibrium of
the alternating-offers game, for any discount factors `0 ≤ a < 1`, `0 ≤ b < 1`: the country
always offers `x = a(1−b)/(1−ab)` and accepts claims `y ≤ x′`, the creditors always claim
`x′ = (1−b)/(1−ab)` and accept offers `y ≥ x`. -/
theorem stationary_isSPE {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    IsSPE a b (statCountry (countryOfferShare a b) (creditorOfferShare a b))
      (statCreditor (countryOfferShare a b) (creditorOfferShare a b)) := by
  set x := countryOfferShare a b with hxdef
  set x' := creditorOfferShare a b with hx'def
  have hs0 : 0 < 1 - a * b := by nlinarith
  have hstat := (stationary_iff (x := x) (x' := x') (by nlinarith)).mpr ⟨rfl, rfl⟩
  have hx'0 : 0 ≤ x' := by
    rw [hx'def]; unfold creditorOfferShare; exact div_nonneg (by linarith) hs0.le
  have hx'1 : x' ≤ 1 := by
    rw [hx'def]; unfold creditorOfferShare; rw [div_le_one hs0]; nlinarith
  have hx0 : 0 ≤ x := by rw [hstat.1]; positivity
  have hxx : x ≤ x' := by rw [hstat.1]; nlinarith
  have hcb := stat_country_best hb0 hb1.le hxx hx'1 hstat.2
  have hkb := stat_creditor_best ha0 ha1.le hx0 hxx hstat.1
  have hpay := fun h => stat_payoffs (a := a) (b := b) (x := x) (x' := x') h
  refine ⟨fun _ _ => ⟨hx0, hxx.trans hx'1⟩, fun _ _ => ⟨hx'0, hx'1⟩, ?_, ?_, ?_, ?_⟩
  · intro h _ τ _
    rw [(hpay h).1]
    exact hcb τ h
  · intro h _ τ _
    rw [(hpay h).2]
    exact hkb τ h
  · intro h _ y _ τ _
    unfold countryRespPayoff
    have hnext := hcb τ (h ++ [y])
    rw [(hpay (h ++ [y])).1]
    by_cases he : Even h.length
    · have hpar : ¬ Even (h ++ [y]).length := by simp [Nat.even_add_one, he]
      simp only [acceptAt, he, hpar, ↓reduceIte] at hnext ⊢
      split_ifs
      · exact le_rfl
      · exact mul_le_mul_of_nonneg_left hnext hb0
    · have hpar : Even (h ++ [y]).length := by simp [Nat.even_add_one, he]
      simp only [acceptAt, he, hpar, ↓reduceIte, statCountry, decide_eq_true_eq] at hnext ⊢
      have hb' : b * countryPayoff b τ (statCreditor x x') (h ++ [y]) ≤ 1 - x' := by
        have := mul_le_mul_of_nonneg_left hnext hb0
        linarith [hstat.2]
      by_cases hy : y ≤ x'
      · simp only [hy, ↓reduceIte]
        split_ifs
        · exact le_rfl
        · linarith
      · simp only [hy, ↓reduceIte]
        split_ifs
        · linarith [hstat.2]
        · linarith [hstat.2]
  · intro h _ y _ τ _
    unfold creditorRespPayoff
    have hnext := hkb τ (h ++ [y])
    rw [(hpay (h ++ [y])).2]
    by_cases he : Even h.length
    · have hpar : ¬ Even (h ++ [y]).length := by simp [Nat.even_add_one, he]
      simp only [acceptAt, he, hpar, ↓reduceIte, statCreditor, decide_eq_true_eq] at hnext ⊢
      have ha' : a * creditorPayoff a (statCountry x x') τ (h ++ [y]) ≤ x := by
        have := mul_le_mul_of_nonneg_left hnext ha0
        linarith [hstat.1]
      by_cases hy : x ≤ y
      · simp only [hy, ↓reduceIte]
        split_ifs
        · exact le_rfl
        · linarith
      · simp only [hy, ↓reduceIte]
        split_ifs
        · linarith [hstat.1]
        · linarith [hstat.1]
    · have hpar : Even (h ++ [y]).length := by simp [Nat.even_add_one, he]
      simp only [acceptAt, he, hpar, ↓reduceIte] at hnext ⊢
      split_ifs
      · exact le_rfl
      · exact mul_le_mul_of_nonneg_left hnext ha0

/-! ### The equilibrium, and the bargaining outcome of Appendix 6A -/

/-- Rubinstein's theorem, O&R footnote 73: for discount factors `0 ≤ a < 1`, `0 ≤ b < 1` a
subgame-perfect equilibrium exists, and in every subgame-perfect equilibrium the country (the
first proposer) gets `1 − x` and the creditors `x = a(1−b)/(1−ab)`, by immediate agreement. -/
theorem rubinstein_exists_unique {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b)
    (hb1 : b < 1) :
    (∃ σc σk, IsSPE a b σc σk) ∧
      ∀ σc σk, IsSPE a b σc σk →
        countryPayoff b σc σk [] = 1 - countryOfferShare a b ∧
          creditorPayoff a σc σk [] = countryOfferShare a b ∧
          σk.respond [] (σc.propose []) = true := by
  refine ⟨⟨_, _, stationary_isSPE ha0 ha1 hb0 hb1⟩, fun σc σk hs => ?_⟩
  have hadm0 : Admissible ([] : List ℝ) := fun z hz => by simp at hz
  obtain ⟨h1, h2, -, h4⟩ := (spe_unique ha0 ha1 hb0 hb1 hs hadm0).1 (by simp)
  exact ⟨h1, h2, h4⟩

/-- The bargaining denominator is positive when the discount factors lie in `(0, 1)`:
`r + δ + 2θ + h(rδ − θ²) > 0` (footnote 73), since `1 − ab = h[r + δ + 2θ + h(rδ − θ²)] /
[(1+rh)(1+δh)]`. -/
theorem bargaining_denominator_pos {r δ θ h : ℝ} (hh : 0 < h) (hθh : θ * h < 1)
    (hr : 0 < 1 + r * h) (hd : 0 < 1 + δ * h) (hrθ : 0 < r + θ) (hδθ : 0 < δ + θ) :
    0 < r + δ + 2 * θ + h * (r * δ - θ ^ 2) := by
  obtain ⟨ha0, ha1, hb0, hb1⟩ := factors_mem_unit hh hθh hr hd hrθ hδθ
  have hab : 0 < 1 - creditorFactor r θ h * countryFactor δ θ h := by nlinarith
  have e : (1 - creditorFactor r θ h * countryFactor δ θ h) * ((1 + r * h) * (1 + δ * h)) =
      h * (r + δ + 2 * θ + h * (r * δ - θ ^ 2)) := by
    unfold creditorFactor countryFactor
    have hne : (1 + r * h) * (1 + δ * h) ≠ 0 := mul_ne_zero hr.ne' hd.ne'
    rw [div_mul_div_comm, one_sub_div hne, div_mul_cancel₀ _ hne]
    ring
  have : 0 < h * (r + δ + 2 * θ + h * (r * δ - θ ^ 2)) := by rw [← e]; positivity
  exact pos_of_mul_pos_right this hh.le

/-- The subgame-perfect bargaining outcome of Appendix 6A for period length `h`, O&R p. 421 and
footnote 73: with `h > 0`, `θh < 1`, `1 + rh > 0`, `1 + δh > 0`, `r + θ > 0`, `δ + θ > 0`, in
every subgame-perfect equilibrium of the bargaining game with discount factors
`a = (1−θh)/(1+rh)` (creditors) and `b = (1−θh)/(1+δh)` (country), the creditors receive
exactly the share `(1−θh)(δ+θ)/[r + δ + 2θ + h(rδ − θ²)]`. -/
theorem spe_creditor_share {r δ θ h : ℝ} (hh : 0 < h) (hθh : θ * h < 1) (hr : 0 < 1 + r * h)
    (hd : 0 < 1 + δ * h) (hrθ : 0 < r + θ) (hδθ : 0 < δ + θ) {σc σk : BargainStrategy}
    (hs : IsSPE (creditorFactor r θ h) (countryFactor δ θ h) σc σk) :
    creditorPayoff (creditorFactor r θ h) σc σk [] =
      (1 - θ * h) * (δ + θ) / (r + δ + 2 * θ + h * (r * δ - θ ^ 2)) := by
  obtain ⟨ha0, ha1, hb0, hb1⟩ := factors_mem_unit hh hθh hr hd hrθ hδθ
  rw [((rubinstein_exists_unique ha0.le ha1 hb0.le hb1).2 σc σk hs).2.1,
    countryOfferShare_exact hh hr hd (bargaining_denominator_pos hh hθh hr hd hrθ hδθ).ne']

/-- The continuous-bargaining limit (56) for the GAME, O&R p. 421: for every `ε > 0` there is
`h₀ > 0` such that for every period length `0 < h < h₀` and EVERY subgame-perfect equilibrium
of the bargaining game with period length `h`, the creditors' share is within `ε` of
`(δ+θ)/(δ+r+2θ)` (and the country's within `ε` of `(r+θ)/(δ+r+2θ)`, (57)). -/
theorem spe_share_limit {r δ θ : ℝ} (hrθ : 0 < r + θ) (hδθ : 0 < δ + θ) {ε : ℝ} (hε : 0 < ε) :
    ∃ h₀ > 0, ∀ h, 0 < h → h < h₀ → ∀ σc σk,
      IsSPE (creditorFactor r θ h) (countryFactor δ θ h) σc σk →
        |creditorPayoff (creditorFactor r θ h) σc σk [] - (δ + θ) / (δ + r + 2 * θ)| < ε ∧
        |countryPayoff (countryFactor δ θ h) σc σk [] - (r + θ) / (δ + r + 2 * θ)| < ε := by
  have hlim := (share_limit56 hrθ hδθ).1
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      |countryOfferShare (creditorFactor r θ h) (countryFactor δ θ h) -
        (δ + θ) / (δ + r + 2 * θ)| < ε ∧ θ * h < 1 ∧ 0 < 1 + r * h ∧ 0 < 1 + δ * h := by
    have c1 : ContinuousAt (fun h : ℝ => θ * h) 0 := by fun_prop
    have c2 : ContinuousAt (fun h : ℝ => 1 + r * h) 0 := by fun_prop
    have c3 : ContinuousAt (fun h : ℝ => 1 + δ * h) 0 := by fun_prop
    filter_upwards [hlim.eventually (Metric.ball_mem_nhds _ hε),
      nhdsWithin_le_nhds (c1.eventually (gt_mem_nhds (by simp : θ * (0 : ℝ) < 1))),
      nhdsWithin_le_nhds (c2.eventually (lt_mem_nhds (by simp : (0 : ℝ) < 1 + r * 0))),
      nhdsWithin_le_nhds (c3.eventually (lt_mem_nhds (by simp : (0 : ℝ) < 1 + δ * 0)))]
      with h h1 h2 h3 h4
    exact ⟨by rw [Real.dist_eq] at h1; exact h1, h2, h3, h4⟩
  obtain ⟨h₀, hh₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨h₀, hh₀, fun h hh hlt σc σk hs => ?_⟩
  obtain ⟨hε', hθh, hr, hd⟩ := hsub ⟨hh, hlt⟩
  obtain ⟨ha0, ha1, hb0, hb1⟩ := factors_mem_unit hh hθh hr hd hrθ hδθ
  obtain ⟨hc, hk, -⟩ := (rubinstein_exists_unique ha0.le ha1 hb0.le hb1).2 σc σk hs
  rw [hk]
  refine ⟨hε', ?_⟩
  rw [hc, ← country_share57 hrθ hδθ]
  rw [show 1 - countryOfferShare (creditorFactor r θ h) (countryFactor δ θ h) -
      (1 - (δ + θ) / (δ + r + 2 * θ)) = -(countryOfferShare (creditorFactor r θ h)
        (countryFactor δ θ h) - (δ + θ) / (δ + r + 2 * θ)) by ring, abs_neg]
  exact hε'

end ObstfeldRogoff.CapitalMarketImperfections.SovereignBargaining
