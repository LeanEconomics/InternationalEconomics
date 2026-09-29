/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A finite state space

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§6.1, pp. 349–351. Uncertainty is modelled by finitely many states of nature `s`
with probabilities `π(s) ≥ 0` summing to one, and expectations are finite sums
`E[X] = Σ_s π(s) X(s)`.
-/

namespace ObstfeldRogoff.CapitalMarketImperfections

open Finset

/-- Probabilities on a finite set of states of nature (O&R §6.1). -/
structure StateSpace (S : Type) [Fintype S] where
  prob : S → ℝ
  prob_nonneg : ∀ s, 0 ≤ prob s
  prob_sum : ∑ s, prob s = 1

namespace StateSpace

variable {S : Type} [Fintype S] (Ω : StateSpace S)

/-- The expectation `E[X] = Σ_s π(s) X(s)`. -/
def expect (X : S → ℝ) : ℝ := ∑ s, Ω.prob s * X s

/-- The expectation of a constant is that constant. -/
theorem expect_const (c : ℝ) : Ω.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, Ω.prob_sum]

/-- Expectation is additive. -/
theorem expect_add (X Y : S → ℝ) :
    Ω.expect (fun s => X s + Y s) = Ω.expect X + Ω.expect Y := by
  simp [expect, mul_add, Finset.sum_add_distrib]

end StateSpace

end ObstfeldRogoff.CapitalMarketImperfections
