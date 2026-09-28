import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Cagan money-demand equation

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§8.2, pp. 515–517. In logs, money demand is `m_t − p_t = −η(p_{t+1} − p_t)`, so the
price level satisfies `p_t = (m_t + η p_{t+1})/(1 + η)`.
-/

namespace ObstfeldRogoff.MoneyExchangeRates

/-- The Cagan money-demand residual `m − p + η(p′ − p)` (O&R (8.2), p. 516). -/
def caganResidual (η m p p' : ℝ) : ℝ := m - p + η * (p' - p)

/-- **The price level from money demand** (O&R (8.3), p. 516): the residual vanishes iff
`p = (m + η p′)/(1 + η)`. -/
theorem cagan_price_iff {η m p p' : ℝ} (hη : 1 + η ≠ 0) :
    caganResidual η m p p' = 0 ↔ p = (m + η * p') / (1 + η) := by
  unfold caganResidual
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- A constant money supply supports a constant price level equal to it (O&R §8.2). -/
theorem cagan_steady (η m : ℝ) : caganResidual η m m m = 0 := by
  unfold caganResidual
  ring

end ObstfeldRogoff.MoneyExchangeRates

set_option linter.style.longLine false
#print axioms ObstfeldRogoff.MoneyExchangeRates.caganResidual
#print axioms ObstfeldRogoff.MoneyExchangeRates.cagan_price_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.cagan_steady
