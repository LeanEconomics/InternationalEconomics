/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Walrasian stability and the Marshall–Lerner condition

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Appendix 1A, pp. 53–54. The world market for date-1 output is Walras-stable when
world excess saving rises with the interest rate (O&R (1.39)). Written with
date-1 Home imports `IM₁ = C₁ + I₁ − Y₁` and date-2 Foreign imports
`IM₂* = C₂* + I₂* − Y₂*`, it becomes O&R (1.40): the value of Foreign's date-2
imports in date-1 units, net of Home's date-1 imports, rises with `r`.

At an equilibrium where Home imports on date 1, (1.40) holds if and only if the
import elasticities `ζ = −(1 + r) IM₁'/IM₁` and `ζ* = (1 + r) IM₂*'/IM₂*` sum to
more than one: the **Marshall–Lerner condition** O&R (1.41).
-/

namespace ObstfeldRogoff.IntertemporalTrade.Stability

/-- Home's date-1 import elasticity with respect to the gross interest rate (O&R p. 54). -/
noncomputable def zeta (r IM1 dIM1 : ℝ) : ℝ := -(1 + r) * dIM1 / IM1

/-- Foreign's date-2 import elasticity with respect to the gross interest rate (O&R p. 54). -/
noncomputable def zetaStar (r IM2s dIM2s : ℝ) : ℝ := (1 + r) * dIM2s / IM2s

/-- The derivative of `IM₂*(r)/(1 + r) − IM₁(r)`, the left side of O&R (1.40). -/
theorem hasDerivAt_netImports {IM1 IM2s : ℝ → ℝ} {r dIM1 dIM2s : ℝ} (hr : 0 < 1 + r)
    (h1 : HasDerivAt IM1 dIM1 r) (h2 : HasDerivAt IM2s dIM2s r) :
    HasDerivAt (fun s => IM2s s / (1 + s) - IM1 s)
      (dIM2s / (1 + r) - IM2s r / (1 + r) ^ 2 - dIM1) r := by
  have hd : HasDerivAt (fun s : ℝ => 1 + s) 1 r := (hasDerivAt_id r).const_add 1
  have h3 : HasDerivAt (fun s => IM2s s / (1 + s))
      ((dIM2s * (1 + r) - IM2s r * 1) / (1 + r) ^ 2) r := h2.div hd hr.ne'
  refine HasDerivAt.congr_deriv (HasDerivAt.sub h3 h1) ?_
  field_simp

/-- **(1.39) ⇔ (1.40)**: if Home's saving minus investment is `−IM₁` and Foreign's is
`IM₂*/(1 + r)` (its budget constraint), world excess saving and the net-import expression
have the same derivative. -/
theorem worldExcessSaving_eq {S I Ss Is IM1 IM2s : ℝ → ℝ}
    (hH : ∀ s, S s - I s = -IM1 s) (hF : ∀ s, Ss s - Is s = IM2s s / (1 + s)) :
    (fun s => S s + Ss s - I s - Is s) = fun s => IM2s s / (1 + s) - IM1 s := by
  funext s
  linarith [hH s, hF s]

/-- **The Marshall–Lerner condition** O&R (1.41), p. 54: at an equilibrium with
`IM₁ = IM₂*/(1 + r) > 0`, the stability condition (1.40) holds iff `ζ + ζ* > 1`. -/
theorem marshall_lerner {r IM1 IM2s dIM1 dIM2s : ℝ} (hr : 0 < 1 + r) (hIM : 0 < IM1)
    (heq : IM1 = IM2s / (1 + r)) :
    0 < dIM2s / (1 + r) - IM2s / (1 + r) ^ 2 - dIM1 ↔
      1 < zeta r IM1 dIM1 + zetaStar r IM2s dIM2s := by
  have hIM2 : IM2s = (1 + r) * IM1 := by rw [heq]; field_simp
  have hIM2pos : 0 < IM2s := by rw [hIM2]; positivity
  unfold zeta zetaStar
  have key : dIM2s / (1 + r) - IM2s / (1 + r) ^ 2 - dIM1 =
      (IM1 / (1 + r)) * (-(1 + r) * dIM1 / IM1 + (1 + r) * dIM2s / IM2s - 1) := by
    rw [hIM2]
    field_simp
    ring
  rw [key]
  constructor
  · intro hpos
    have := (pos_iff_pos_of_mul_pos hpos).1 (div_pos hIM hr)
    linarith
  · intro hml
    exact mul_pos (div_pos hIM hr) (by linarith)

/-- **Stability via Marshall–Lerner**: combining (1.39) ⇔ (1.40) with (1.41), world excess
saving is increasing at the equilibrium iff `ζ + ζ* > 1`. -/
theorem stable_iff_marshall_lerner {S I Ss Is IM1 IM2s : ℝ → ℝ} {r dIM1 dIM2s : ℝ}
    (hr : 0 < 1 + r) (hH : ∀ s, S s - I s = -IM1 s)
    (hF : ∀ s, Ss s - Is s = IM2s s / (1 + s)) (h1 : HasDerivAt IM1 dIM1 r)
    (h2 : HasDerivAt IM2s dIM2s r) (hIM : 0 < IM1 r) (heq : IM1 r = IM2s r / (1 + r)) :
    HasDerivAt (fun s => S s + Ss s - I s - Is s)
        (dIM2s / (1 + r) - IM2s r / (1 + r) ^ 2 - dIM1) r ∧
      (0 < dIM2s / (1 + r) - IM2s r / (1 + r) ^ 2 - dIM1 ↔
        1 < zeta r (IM1 r) dIM1 + zetaStar r (IM2s r) dIM2s) := by
  refine ⟨?_, marshall_lerner hr hIM heq⟩
  rw [worldExcessSaving_eq hH hF]
  exact hasDerivAt_netImports hr h1 h2

/-- The numerator and denominator of O&R (1.23) at a zero current account (`C₁ = Y₁`):
with `u' > 0` and `u'' < 0`, `dC₁/dr = βu'(C₂)/[u''(C₁) + β(1 + r)²u''(C₂)] < 0`. -/
theorem dC1_neg_of_zero_ca {β r du2 d2u1 d2u2 Y1 C1 : ℝ} (hβ : 0 < β) (hdu : 0 < du2)
    (h1 : d2u1 < 0) (h2 : d2u2 < 0) (hca : C1 = Y1) :
    (β * du2 + β * (1 + r) * d2u2 * (Y1 - C1)) / (d2u1 + β * (1 + r) ^ 2 * d2u2) < 0 := by
  rw [hca, sub_self, mul_zero, add_zero]
  have : β * (1 + r) ^ 2 * d2u2 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) h2.le
  exact div_neg_of_pos_of_neg (mul_pos hβ hdu) (by linarith)

/-- **Zero-current-account equilibria are stable** (O&R p. 53): if both countries' saving
rises with `r` (as (1.23) gives at `C₁ = Y₁`, see `dC1_neg_of_zero_ca`) and investment
does not, world excess saving is strictly increasing, i.e. (1.39) holds. -/
theorem stable_of_saving_increasing {dS dSs dI dIs : ℝ} (hS : 0 < dS) (hSs : 0 < dSs)
    (hI : dI ≤ 0) (hIs : dIs ≤ 0) : 0 < dS + dSs - dI - dIs := by
  linarith

end ObstfeldRogoff.IntertemporalTrade.Stability
