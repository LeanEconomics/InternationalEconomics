/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Aggregate and intergenerational gains from trade in an OLG economy

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §3.5,
pp. 164–167, and Chapter 3 Exercise 2, p. 195.

A small Diamond economy with log utility `log c^Y + β log c^O`, no government, and a
production sector whose wage is a function `w(r)` of the interest rate (the factor-price
frontier, with `dw/dr = −k`, fn 32; for Cobb–Douglas `Y = A K^α L^(1−α)` the frontier is
`w(r) = (1−α) A (α A / r)^(α/(1−α))` and `k(r) = (α A / r)^(1/(1−α))`).
A generation facing `(w, r)` has lifetime utility `U(r) = (1+β) log w(r) + β log(1+r)`
up to a constant.

**Timing assumption.** Following the book, every generation born on or after the opening
date `t` is treated as a steady-state generation facing the post-opening factor prices
`(w(r), r)`, and the date-`t` old earn the world rate on their saving: the capital stock
jumps to its world-rate level at `t`. If instead date-`t` capital is predetermined at its
autarky level, the date-`t` young still earn the autarky wage and only gain from a rise in
`r` (`dateT_young_predetermined_hasDerivAt`).

Main results:
* (3.47): at the autarky rate `dU/dr = −βr/(1+r) < 0`; the first-period income equivalent
  is `−rk/(1+r)` per generation, with present value `−k` over all generations, exactly
  offsetting the old's gain `k`; a budget-balanced compensation scheme.
* The already-open economy: `dU/dr = −βk/(k+b) + β/(1+r)`; generations gain iff `b > rk`;
  economy-wide gain `(1+r) b / r`.
* Exercise 2(a): with growth `n`, `dU/dr = β(1/(1+r) − 1/(1+n))`, positive iff `r < n`.
* Exercise 2(b): the book's claim that for `n > r^A > r` opening makes *everyone* worse off
  is false as stated: in the Cobb–Douglas case `U(r) → +∞` as `r → 0⁺`, so the young gain
  from a sufficiently low world rate (explicit instance with `α = 1/20`, `β = 9/10`,
  `n = 1/2`). The correct statement holds for `r ∈ [r^A/(1+n−r^A), r^A)`.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade

open Real Filter Set Topology

/-! ## Lifetime utility as a function of the world rate -/

/-- Lifetime utility of a steady-state generation facing the world rate `r`, O&R §3.5,
p. 165: `U(r) = (1+β) log w(r) + β log(1+r)` (apart from an additive constant), where
`w` is the wage schedule (factor-price frontier). -/
noncomputable def lifetimeUtility (β : ℝ) (w : ℝ → ℝ) (r : ℝ) : ℝ :=
  (1 + β) * Real.log (w r) + β * Real.log (1 + r)

/-- O&R §3.5, p. 165: `dU/dr = ((1+β)/w)(dw/dr) + β/(1+r)`, for a positive wage
differentiable at `r` and `r > −1`. -/
theorem hasDerivAt_lifetimeUtility (β : ℝ) (w : ℝ → ℝ) {r w' : ℝ} (hw : 0 < w r)
    (hr : 0 < 1 + r) (hdw : HasDerivAt w w' r) :
    HasDerivAt (lifetimeUtility β w) ((1 + β) * (w' / w r) + β * (1 / (1 + r))) r := by
  have h1 : HasDerivAt (fun x => Real.log (w x)) (w' / w r) r := hdw.log hw.ne'
  have h2 : HasDerivAt (fun x => 1 + x) 1 r := (hasDerivAt_id r).const_add 1
  have h3 : HasDerivAt (fun x => Real.log (1 + x)) (1 / (1 + r)) r := h2.log hr.ne'
  exact HasDerivAt.add (h1.const_mul (1 + β)) (h3.const_mul β)

/-- O&R §3.5, p. 165 with fn 32: along the factor-price frontier `dw/dr = −k`,
`dU/dr = −(1+β) k / w + β/(1+r)`. -/
theorem hasDerivAt_lifetimeUtility_frontier (β : ℝ) (w : ℝ → ℝ) {r k : ℝ} (hw : 0 < w r)
    (hr : 0 < 1 + r) (hdw : HasDerivAt w (-k) r) :
    HasDerivAt (lifetimeUtility β w) (-(1 + β) * k / w r + β / (1 + r)) r := by
  refine (hasDerivAt_lifetimeUtility β w hw hr hdw).congr_deriv ?_
  field_simp

/-- O&R (3.47), p. 165: at the autarky steady state, where the capital-labour ratio
equals the saving of the young, `k = βw/(1+β)`, a marginal rise in the interest rate
changes the lifetime utility of every generation born on or after the opening date by
`dU/dr = −βr/(1+r)`. -/
theorem hasDerivAt_lifetimeUtility_autarky {β : ℝ} (w : ℝ → ℝ) {r k : ℝ} (hβ : 0 < β)
    (hw : 0 < w r) (hr : 0 < 1 + r) (hdw : HasDerivAt w (-k) r)
    (hk : k = β * w r / (1 + β)) :
    HasDerivAt (lifetimeUtility β w) (-(β * r) / (1 + r)) r := by
  refine (hasDerivAt_lifetimeUtility_frontier β w hw hr hdw).congr_deriv ?_
  subst hk
  have : (1 + β) ≠ 0 := by linarith
  field_simp
  ring

/-- O&R (3.47), p. 165: the utility change is strictly negative when `r > 0`, so a
marginal rise of the world rate above the autarky rate hurts the date-`t` young and all
later generations. -/
theorem autarky_utility_slope_neg {β r : ℝ} (hβ : 0 < β) (hr : 0 < r) :
    -(β * r) / (1 + r) < 0 := by
  have : 0 < β * r / (1 + r) := by positivity
  rw [neg_div]; linarith

/-- O&R §3.5, p. 165: the old at the opening date hold capital `k` per person, so their
second-period income `(1+r)k` rises at rate `k` with the interest rate (they gain `k dr`). -/
theorem old_income_hasDerivAt (k r : ℝ) : HasDerivAt (fun x => (1 + x) * k) k r := by
  have h := ((hasDerivAt_id r).const_add 1).mul_const k
  simpa using h

/-! ## Income equivalents, present values and compensation (n = 0) -/

/-- O&R §3.5, p. 165: dividing the utility change `−βr/(1+r)` by the marginal utility of
first-period income `(1+β)/w` gives the first-period income equivalent `−rk/(1+r)`
when `k = βw/(1+β)`; it equals the wage loss `−k` plus the capital-income gain
`k/(1+r)` discounted one period. -/
theorem income_equivalent_autarky {β w k r : ℝ} (hβ : 0 < β) (hw : 0 < w) (hr : 0 < 1 + r)
    (hk : k = β * w / (1 + β)) :
    (-(β * r) / (1 + r)) / ((1 + β) / w) = -(r * k) / (1 + r) ∧
      -k + β * w / ((1 + β) * (1 + r)) = -(r * k) / (1 + r) := by
  subst hk
  have : (1 + β) ≠ 0 := by linarith
  constructor
  · field_simp
  · field_simp
    ring

/-- O&R §3.5, p. 166: the present discounted value, at date `t`, of the per capita income
losses `−rk/(1+r)` of the date-`t` young and all later generations is `−k`, provided
`r > 0` (the geometric series converges). -/
theorem pv_generation_losses {k r : ℝ} (hr : 0 < r) :
    HasSum (fun j : ℕ => -(r * k) / (1 + r) * (1 / (1 + r)) ^ j) (-k) := by
  have hq0 : 0 ≤ 1 / (1 + r) := by positivity
  have hq1 : 1 / (1 + r) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (-(r * k) / (1 + r))
  convert h using 1
  have : (1 + r) ≠ 0 := by linarith
  have h2 : r ≠ 0 := hr.ne'
  rw [one_sub_div this, add_sub_cancel_left, inv_div]
  field_simp

/-- O&R §3.5, p. 166: the aggregate first-order effect of the marginal opening is zero:
the date-`t` old's gain `k` exactly offsets the present value `−k` of all other
generations' losses. -/
theorem aggregate_first_order_zero {k r : ℝ} (hr : 0 < r) :
    HasSum (fun j : ℕ => -(r * k) / (1 + r) * (1 / (1 + r)) ^ j) (-k) ∧ k + -k = 0 :=
  ⟨pv_generation_losses hr, by ring⟩

/-- O&R §3.5, p. 166, the compensation scheme stated precisely: tax each date-`t` old
person `k dr` and give each generation born on or after `t` a transfer `rk dr/(1+r)`
when young. For `r > 0` (i) the present value of the transfers equals the revenue
`k dr`, so the scheme is budget balanced in present value; (ii) every agent's net
first-order income change is zero (old: `k dr − k dr`; each later generation:
`−rk dr/(1+r) + rk dr/(1+r)`), so to first order nobody is worse off. -/
theorem compensation_scheme {k r dr : ℝ} (hr : 0 < r) :
    HasSum (fun j : ℕ => r * k * dr / (1 + r) * (1 / (1 + r)) ^ j) (k * dr) ∧
      k * dr - k * dr = 0 ∧ -(r * k * dr) / (1 + r) + r * k * dr / (1 + r) = 0 := by
  refine ⟨?_, by ring, by ring⟩
  have h := (pv_generation_losses (k := k) hr).mul_left (-dr)
  convert h using 1
  · funext j
    ring
  · ring

/-! ## An economy already open to trade (O&R p. 166) -/

/-- O&R §3.5, p. 166: in an economy already open, the saving of the young `βw/(1+β)`
equals `k + b` (capital plus net foreign assets per worker), and the utility change
becomes `dU/dr = −βk/(k+b) + β/(1+r)`. -/
theorem hasDerivAt_lifetimeUtility_open {β : ℝ} (w : ℝ → ℝ) {r k b : ℝ} (hβ : 0 < β)
    (hw : 0 < w r) (hr : 0 < 1 + r) (hdw : HasDerivAt w (-k) r)
    (hkb : k + b = β * w r / (1 + β)) :
    HasDerivAt (lifetimeUtility β w) (-(β * k) / (k + b) + β / (1 + r)) r := by
  refine (hasDerivAt_lifetimeUtility_frontier β w hw hr hdw).congr_deriv ?_
  rw [hkb]
  have : (1 + β) ≠ 0 := by linarith
  field_simp

/-- O&R §3.5, p. 166: the first-period income equivalent of the utility change in the
open economy is `−k + (k+b)/(1+r)` (per unit `dr`). -/
theorem income_equivalent_open {β w k b r : ℝ} (hβ : 0 < β) (hw : 0 < w)
    (hkb : k + b = β * w / (1 + β)) :
    (-(β * k) / (k + b) + β / (1 + r)) / ((1 + β) / w) = -k + (k + b) / (1 + r) := by
  have hkb0 : k + b ≠ 0 := by rw [hkb]; positivity
  have hw' : w = (1 + β) * (k + b) / β := by
    rw [hkb]; field_simp
  subst hw'
  have : (1 + β) ≠ 0 := by linarith
  field_simp

/-- O&R §3.5, p. 166, made precise: each generation gains from a rise in `r`
(positive income equivalent) if and only if `b > rk` ("b sufficiently positive"). -/
theorem open_generation_gains_iff {k b r : ℝ} (hr : 0 < 1 + r) :
    0 < -k + (k + b) / (1 + r) ↔ r * k < b := by
  rw [show -k + (k + b) / (1 + r) = (b - r * k) / (1 + r) by
    field_simp; ring]
  constructor
  · intro h
    have := (div_pos_iff_of_pos_right hr).mp h
    linarith
  · intro h
    exact div_pos (by linarith) hr

/-- O&R §3.5, pp. 166–167: the gain to the economy as a whole from a rise `dr` in the
world rate is `(1+r) b dr / r`: the date-`t` old gain `(k+b) dr` and the generations born
on or after `t` have present value `(−k + (k+b)/(1+r)) dr (1+r)/r` (for `r > 0`). It is
a loss iff `b < 0`. -/
theorem open_economywide_gain {k b r dr : ℝ} (hr : 0 < r) :
    HasSum (fun j : ℕ => (-k + (k + b) / (1 + r)) * dr * (1 / (1 + r)) ^ j)
        ((-k + (k + b) / (1 + r)) * dr * ((1 + r) / r)) ∧
      (k + b) * dr + (-k + (k + b) / (1 + r)) * dr * ((1 + r) / r) =
        (1 + r) * b * dr / r := by
  have hq0 : 0 ≤ 1 / (1 + r) := by positivity
  have hq1 : 1 / (1 + r) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((-k + (k + b) / (1 + r)) * dr)
  have h1 : (1 + r) ≠ 0 := by linarith
  have h2 : r ≠ 0 := hr.ne'
  refine ⟨?_, ?_⟩
  · convert h using 1
    congr 1
    rw [one_sub_div h1, add_sub_cancel_left, inv_div]
  · field_simp
    ring

/-! ## Timing caveat: predetermined capital at the opening date -/

/-- Timing caveat to O&R §3.5: if date-`t` capital is predetermined at its autarky level,
the date-`t` young earn the autarky wage `w^A` whatever the world rate, and their utility
`(1+β) log w^A + β log(1+r)` has slope `β/(1+r) > 0`: they gain from a rise in `r`,
unlike the steady-state generations of (3.47). -/
theorem dateT_young_predetermined_hasDerivAt (β wA r : ℝ) (hr : 0 < 1 + r) :
    HasDerivAt (fun x => (1 + β) * Real.log wA + β * Real.log (1 + x)) (β / (1 + r)) r ∧
      (0 < β → 0 < β / (1 + r)) := by
  refine ⟨?_, fun hβ => div_pos hβ hr⟩
  have h2 : HasDerivAt (fun x => 1 + x) 1 r := (hasDerivAt_id r).const_add 1
  have h3 := (h2.log hr.ne').const_mul β
  have h4 := h3.const_add ((1 + β) * Real.log wA)
  convert h4 using 1
  field_simp

/-! ## Exercise 2(a): population growth and dynamic inefficiency -/

/-- O&R Ch. 3 Exercise 2(a), p. 195: with labour-force growth `n > −1`, autarky capital
per worker is `k = βw/((1+β)(1+n))`, and at the autarky rate
`dU/dr = β (1/(1+r) − 1/(1+n))`. -/
theorem hasDerivAt_lifetimeUtility_growth {β n : ℝ} (w : ℝ → ℝ) {r k : ℝ} (hβ : 0 < β)
    (hn : 0 < 1 + n) (hw : 0 < w r) (hr : 0 < 1 + r) (hdw : HasDerivAt w (-k) r)
    (hk : k = β * w r / ((1 + β) * (1 + n))) :
    HasDerivAt (lifetimeUtility β w) (β * (1 / (1 + r) - 1 / (1 + n))) r := by
  refine (hasDerivAt_lifetimeUtility_frontier β w hw hr hdw).congr_deriv ?_
  subst hk
  have : (1 + β) ≠ 0 := by linarith
  field_simp
  ring

/-- O&R Ch. 3 Exercise 2(a), p. 195: the slope `β(1/(1+r) − 1/(1+n))` is positive iff
`r < n` (dynamic inefficiency), so when the world rate equals `r^A < n` a small permanent
rise benefits every generation born on or after `t`; the date-`t` old, whose income
`(1+r) s` rises at rate `s > 0`, gain as well (`old_income_hasDerivAt`). -/
theorem growth_slope_pos_iff {β n r : ℝ} (hβ : 0 < β) (hn : 0 < 1 + n) (hr : 0 < 1 + r) :
    0 < β * (1 / (1 + r) - 1 / (1 + n)) ↔ r < n := by
  rw [mul_pos_iff_of_pos_left hβ, sub_pos, one_div_lt_one_div hn hr]
  constructor <;> intro h <;> linarith

/-! ## Cobb–Douglas factor-price frontier -/

/-- Cobb–Douglas wage as a function of the interest rate, O&R §1.5.2 and §3.5 fn 32:
`w(r) = (1−α) A (αA/r)^(α/(1−α))`. -/
noncomputable def wageCD (α A r : ℝ) : ℝ :=
  (1 - α) * A * (α * A / r) ^ (α / (1 - α))

/-- Cobb–Douglas capital-labour ratio as a function of the interest rate, O&R §3.5:
`k(r) = (αA/r)^(1/(1−α))`, from `r = αA k^(α−1)`. -/
noncomputable def capitalCD (α A r : ℝ) : ℝ :=
  (α * A / r) ^ (1 / (1 - α))

/-- O&R §3.5 fn 32, checked directly for Cobb–Douglas: the factor-price frontier has slope
`dw/dr = −k(r)`, for `0 < α < 1`, `A > 0`, `r > 0`. -/
theorem hasDerivAt_wageCD {α A r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hr : 0 < r) : HasDerivAt (wageCD α A) (-capitalCD α A r) r := by
  have h1α : (1 - α) ≠ 0 := by linarith
  have hx : 0 < α * A / r := by positivity
  have hq : HasDerivAt (fun x => α * A / x) (-(α * A) / r ^ 2) r := by
    have := (hasDerivAt_inv hr.ne').const_mul (α * A)
    convert this using 1
    · funext x; simp [div_eq_mul_inv]
    · field_simp
  have hp := hq.rpow_const (p := α / (1 - α)) (Or.inl hx.ne')
  have hw := hp.const_mul ((1 - α) * A)
  unfold wageCD capitalCD
  convert hw using 1
  have he : α / (1 - α) - 1 = 1 / (1 - α) - 2 := by field_simp; ring
  rw [he, Real.rpow_sub hx, Real.rpow_two]
  have hxpos : 0 < (α * A / r) ^ (1 / (1 - α)) := Real.rpow_pos_of_pos hx _
  field_simp

/-- O&R §3.5 (Cobb–Douglas): the ratio of capital to the wage is `k/w = α/((1−α) r)`. -/
theorem capitalCD_div_wageCD {α A r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hr : 0 < r) : capitalCD α A r / wageCD α A r = α / ((1 - α) * r) := by
  have h1α : (1 - α) ≠ 0 := by linarith
  have hx : 0 < α * A / r := by positivity
  have he : 1 / (1 - α) = α / (1 - α) + 1 := by field_simp; ring
  unfold capitalCD wageCD
  rw [he, Real.rpow_add hx, Real.rpow_one]
  have hxpos : 0 < (α * A / r) ^ (α / (1 - α)) := Real.rpow_pos_of_pos hx _
  field_simp

/-- O&R §3.5 (Cobb–Douglas): the wage is positive for `0 < α < 1`, `A > 0`, `r > 0`. -/
theorem wageCD_pos {α A r : ℝ} (hα1 : α < 1) (hA : 0 < A) (hx : 0 < α * A / r) :
    0 < wageCD α A r := by
  unfold wageCD
  have : 0 < 1 - α := by linarith
  have := Real.rpow_pos_of_pos hx (α / (1 - α))
  positivity

/-- O&R Ch. 3 Exercise 2 (Cobb–Douglas): the autarky steady-state interest rate with
growth `n`, `r^A = α(1+β)(1+n)/((1−α)β)`. -/
noncomputable def autarkyRateCD (α β n : ℝ) : ℝ :=
  α * (1 + β) * (1 + n) / ((1 - α) * β)

/-- O&R Ch. 3 Exercise 2 hint (Cobb–Douglas): at `r = r^A` the capital-labour ratio
satisfies the autarky condition `k = βw/((1+β)(1+n))`. -/
theorem capitalCD_autarky {α β n A : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hn : 0 < 1 + n) (hA : 0 < A) :
    capitalCD α A (autarkyRateCD α β n) =
      β * wageCD α A (autarkyRateCD α β n) / ((1 + β) * (1 + n)) := by
  have h1α : 0 < 1 - α := by linarith
  have hrA : 0 < autarkyRateCD α β n := by unfold autarkyRateCD; positivity
  have hwpos := wageCD_pos (r := autarkyRateCD α β n) hα1 hA (by positivity)
  have hratio := capitalCD_div_wageCD hα0 hα1 hA hrA
  rw [div_eq_iff hwpos.ne'] at hratio
  rw [hratio]
  unfold autarkyRateCD
  field_simp

/-! ## Exercise 2(b): the Cobb–Douglas welfare function and the counterexample -/

/-- O&R Ch. 3 Exercise 2(b) (Cobb–Douglas): lifetime utility is, up to a constant `C`,
`U(r) = C − (1+β)(α/(1−α)) log r + β log(1+r)`. -/
theorem lifetimeUtility_wageCD {α β A r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hr : 0 < r) :
    lifetimeUtility β (wageCD α A) r =
      (1 + β) * (Real.log ((1 - α) * A) + α / (1 - α) * Real.log (α * A)) -
        (1 + β) * (α / (1 - α)) * Real.log r + β * Real.log (1 + r) := by
  have h1α : 0 < 1 - α := by linarith
  have hx : 0 < α * A / r := by positivity
  unfold lifetimeUtility wageCD
  rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hx _).ne', Real.log_rpow hx,
    Real.log_div (by positivity) hr.ne']
  ring

/-- O&R Ch. 3 Exercise 2(b) (Cobb–Douglas): the slope of lifetime utility at any `r > 0`
is `dU/dr = β (1/(1+r) − r^A/((1+n) r))`. -/
theorem hasDerivAt_lifetimeUtility_CD {α β n A r : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hn : 0 < 1 + n) (hA : 0 < A) (hr : 0 < r) :
    HasDerivAt (lifetimeUtility β (wageCD α A))
      (β * (1 / (1 + r) - autarkyRateCD α β n / ((1 + n) * r))) r := by
  have hwpos := wageCD_pos (r := r) hα1 hA (by positivity)
  have h := hasDerivAt_lifetimeUtility_frontier β (wageCD α A) hwpos (by linarith)
    (hasDerivAt_wageCD hα0 hα1 hA hr)
  refine h.congr_deriv ?_
  have hratio := capitalCD_div_wageCD hα0 hα1 hA hr
  have h1α : (1 - α) ≠ 0 := by linarith
  rw [show -(1 + β) * capitalCD α A r / wageCD α A r =
      -(1 + β) * (capitalCD α A r / wageCD α A r) by ring, hratio]
  unfold autarkyRateCD
  field_simp
  ring

/-- The threshold `r* = r^A/(1+n−r^A)` of O&R Ch. 3 Exercise 2(b) (Cobb–Douglas) at which
lifetime utility is minimised. -/
noncomputable def utilityMinRateCD (α β n : ℝ) : ℝ :=
  autarkyRateCD α β n / (1 + n - autarkyRateCD α β n)

/-- O&R Ch. 3 Exercise 2(b) (Cobb–Douglas): sign of the slope. For `r > 0` and
`r^A < 1+n`, `dU/dr > 0` iff `r > r^A/(1+n−r^A)`. -/
theorem slope_CD_pos_iff {α β n r : ℝ} (hβ : 0 < β) (hn : 0 < 1 + n) (hr : 0 < r)
    (hA1 : autarkyRateCD α β n < 1 + n) :
    0 < β * (1 / (1 + r) - autarkyRateCD α β n / ((1 + n) * r)) ↔
      utilityMinRateCD α β n < r := by
  set rA := autarkyRateCD α β n
  have hd : 0 < 1 + n - rA := by linarith
  unfold utilityMinRateCD
  rw [mul_pos_iff_of_pos_left hβ, sub_pos, div_lt_div_iff₀ (by positivity) (by linarith),
    div_lt_iff₀ hd]
  constructor <;> intro h <;> nlinarith

/-- O&R Ch. 3 Exercise 2(b) (Cobb–Douglas): lifetime utility is strictly increasing in the
world rate on `[r*, ∞)`, `r* = r^A/(1+n−r^A)`, when `0 < r^A < 1+n`. -/
theorem lifetimeUtility_CD_strictMonoOn {α β n A : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hn : 0 < 1 + n) (hA : 0 < A) (hA1 : autarkyRateCD α β n < 1 + n) :
    StrictMonoOn (lifetimeUtility β (wageCD α A)) (Ici (utilityMinRateCD α β n)) := by
  have hrA : 0 < autarkyRateCD α β n := by
    unfold autarkyRateCD; have : 0 < 1 - α := by linarith
    positivity
  have hstar : 0 < utilityMinRateCD α β n := by
    unfold utilityMinRateCD; exact div_pos hrA (by linarith)
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hstar hx
    exact (hasDerivAt_lifetimeUtility_CD (n := n) hα0 hα1 hβ hn hA hx0).continuousAt
      |>.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := lt_trans hstar hx
    rw [(hasDerivAt_lifetimeUtility_CD (n := n) hα0 hα1 hβ hn hA hx0).deriv]
    exact (slope_CD_pos_iff hβ hn hx0 hA1).mpr hx

/-- O&R Ch. 3 Exercise 2(b) (Cobb–Douglas): lifetime utility is strictly decreasing in the
world rate on `(0, r*]`, `r* = r^A/(1+n−r^A)`, when `0 < r^A < 1+n`. -/
theorem lifetimeUtility_CD_strictAntiOn {α β n A : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hn : 0 < 1 + n) (hA : 0 < A) (hA1 : autarkyRateCD α β n < 1 + n) :
    StrictAntiOn (lifetimeUtility β (wageCD α A)) (Ioc 0 (utilityMinRateCD α β n)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc _ _)
  · intro x hx
    exact (hasDerivAt_lifetimeUtility_CD (n := n) hα0 hα1 hβ hn hA hx.1).continuousAt
      |>.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    rw [(hasDerivAt_lifetimeUtility_CD (n := n) hα0 hα1 hβ hn hA hx.1).deriv]
    have h := (slope_CD_pos_iff (r := x) hβ hn hx.1 hA1).not
    push Not at h
    rcases (h.mpr hx.2.le).lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have hβ' : β ≠ 0 := hβ.ne'
      have hsub := (mul_eq_zero.mp h').resolve_left hβ'
      set rA := autarkyRateCD α β n
      have hd : 0 < 1 + n - rA := by linarith
      have hx1 := hx.1
      have hx2 := hx.2
      unfold utilityMinRateCD at hx2
      rw [lt_div_iff₀ hd] at hx2
      rw [sub_eq_zero, div_eq_div_iff (by linarith) (by positivity)] at hsub
      nlinarith

/-- O&R Ch. 3 Exercise 2(b), corrected (Cobb–Douglas): if `r^A < n` then
`r* = r^A/(1+n−r^A) < r^A`, and for every world rate `r ∈ [r*, r^A)` opening to trade makes
everyone worse off: every steady-state generation (`U(r) < U(r^A)`) and the date-`t` old,
whose income `(1+r)s` on autarky saving `s > 0` falls. -/
theorem everyone_worse_off_corrected {α β n A r s : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hn : 0 < 1 + n) (hA : 0 < A) (hs : 0 < s)
    (hAn : autarkyRateCD α β n < n) (hr1 : utilityMinRateCD α β n ≤ r)
    (hr2 : r < autarkyRateCD α β n) :
    utilityMinRateCD α β n < autarkyRateCD α β n ∧
      lifetimeUtility β (wageCD α A) r <
        lifetimeUtility β (wageCD α A) (autarkyRateCD α β n) ∧
      (1 + r) * s < (1 + autarkyRateCD α β n) * s := by
  have hA1 : autarkyRateCD α β n < 1 + n := by linarith
  have hrA : 0 < autarkyRateCD α β n := by
    unfold autarkyRateCD; have : 0 < 1 - α := by linarith
    positivity
  have hlt : utilityMinRateCD α β n < autarkyRateCD α β n := by
    unfold utilityMinRateCD
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  refine ⟨hlt, ?_, by nlinarith⟩
  exact lifetimeUtility_CD_strictMonoOn hα0 hα1 hβ hn hA hA1 hr1 (le_of_lt hlt) hr2

/-- O&R Ch. 3 Exercise 2(b) refuted (Cobb–Douglas): lifetime utility tends to `+∞` as the
world rate falls to zero, because the wage `w(r) ∝ r^(−α/(1−α))` explodes. -/
theorem lifetimeUtility_CD_tendsto_atTop {α β A : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hA : 0 < A) :
    Tendsto (lifetimeUtility β (wageCD α A)) (𝓝[>] 0) atTop := by
  have h1α : 0 < 1 - α := by linarith
  set C := (1 + β) * (Real.log ((1 - α) * A) + α / (1 - α) * Real.log (α * A))
  set c := (1 + β) * (α / (1 - α))
  have hc : 0 < c := by positivity
  have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      C + (-c * Real.log r + β * Real.log (1 + r)) = lifetimeUtility β (wageCD α A) r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [lifetimeUtility_wageCD hα0 hα1 hA hr]
    ring
  refine Tendsto.congr' heq ?_
  refine tendsto_atTop_add_const_left _ C ?_
  have hlog : Tendsto (fun r => -c * Real.log r) (𝓝[>] 0) atTop :=
    Real.tendsto_log_nhdsGT_zero.const_mul_atBot_of_neg (by linarith)
  have hcont :
      Tendsto (fun r : ℝ => β * Real.log (1 + r)) (𝓝[>] 0) (𝓝 (β * Real.log 1)) := by
    have : ContinuousAt (fun r : ℝ => β * Real.log (1 + r)) 0 := by
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.log (continuousAt_const.add continuousAt_id)
      norm_num
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  exact hlog.atTop_add hcont

/-- O&R Ch. 3 Exercise 2(b) refuted (Cobb–Douglas): for any parameters and any autarky
rate `r^A > 0` there is a world rate `r ∈ (0, r^A)` at which every steady-state generation
is strictly better off than in autarky. Hence "opening to trade makes everyone worse off
whenever `n > r^A > r`" is false. -/
theorem exists_rate_below_autarky_young_gain {α β A rA : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hA : 0 < A) (hrA : 0 < rA) :
    ∃ r ∈ Ioo 0 rA,
      lifetimeUtility β (wageCD α A) rA < lifetimeUtility β (wageCD α A) r := by
  have h1 := (lifetimeUtility_CD_tendsto_atTop hα0 hα1 hβ hA).eventually_gt_atTop
    (lifetimeUtility β (wageCD α A) rA)
  have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 rA := Ioo_mem_nhdsGT hrA
  obtain ⟨r, hr1, hr2⟩ := (h2.and h1).exists
  exact ⟨r, hr1, hr2⟩

/-- O&R Ch. 3 Exercise 2(b), explicit counterexample: with `α = 1/20`, `β = 9/10`,
`n = 1/2`, the autarky rate is `r^A = 1/6 < n`, yet at the world rate `r = e^(−7) < r^A`
every steady-state generation is strictly better off than in autarky. -/
theorem counterexample_everyone_worse_off {A : ℝ} (hA : 0 < A) :
    autarkyRateCD (1 / 20) (9 / 10) (1 / 2) = 1 / 6 ∧ (1 / 6 : ℝ) < 1 / 2 ∧
      Real.exp (-7) < 1 / 6 ∧
      lifetimeUtility (9 / 10) (wageCD (1 / 20) A) (1 / 6) <
        lifetimeUtility (9 / 10) (wageCD (1 / 20) A) (Real.exp (-7)) := by
  have he7 : Real.exp (-7) < 1 / 6 := by
    have h7 : (7 : ℝ) + 1 ≤ Real.exp 7 := Real.add_one_le_exp 7
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 7) (by norm_num)]
    linarith
  refine ⟨by unfold autarkyRateCD; norm_num, by norm_num, he7, ?_⟩
  rw [lifetimeUtility_wageCD (by norm_num) (by norm_num) hA (by norm_num),
    lifetimeUtility_wageCD (by norm_num) (by norm_num) hA (Real.exp_pos _), Real.log_exp]
  have hl6 : Real.log (1 / 6) = -Real.log 6 := by
    rw [one_div, Real.log_inv]
  have h6 : Real.log 6 ≤ 6 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h76 : Real.log (1 + 1 / 6) ≤ (1 + 1 / 6) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hpos : 0 < Real.log (1 + Real.exp (-7)) :=
    Real.log_pos (by linarith [Real.exp_pos (-7)])
  rw [hl6]
  norm_num at h76 ⊢
  nlinarith

end ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade
