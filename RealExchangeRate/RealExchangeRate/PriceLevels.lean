/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RealExchangeRate.Model
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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
