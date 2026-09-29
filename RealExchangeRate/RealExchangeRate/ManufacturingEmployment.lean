/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Productivity growth and employment in nontradables

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.3.2,
pp. 220–225. Nontradables are produced with `Y_N = A_N K_N^α L_N^{1−α}` and consumed
at home, and consumers have CES preferences over traded and nontraded goods.
Growth rates are written `x̂ = dx/x`.

* **Employment in nontradables** (O&R (4.12)): with `Y_N = C_N` and `A_N` fixed,
  `L̂_N = Ĉ_N − αk̂_N`.
* **Demand for nontradables** (O&R (4.17)): at `p = 1` the log-derivative of CES
  demand with respect to `p` is `−[γθ + (1 − γ)]`, and wealth `Z = wL + rQ` grows at
  `Ẑ = ψ_L ŵ` with `ψ_L = wL/(wL + rQ)`.
* **The employment effect of tradables productivity** (O&R (4.18)):
  `L̂_N = {ψ_L − (1 − α)[γθ + 1 − γ] − α} Â_T/μ_LT`. With unit elasticity (`θ = 1`) this is
  `(ψ_L − 1)Â_T/μ_LT`, negative when the country has positive wealth (`ψ_L < 1` iff
  `Q > 0`).
-/

namespace ObstfeldRogoff.RealExchangeRate.ManufacturingEmployment

/-- **Employment in nontradables**, O&R (4.12), p. 221: `Y_N = A_N k_N^α L_N` (CRS), so with `A_N`
fixed `Ŷ_N = αk̂_N + L̂_N`; market clearing `Ŷ_N = Ĉ_N` gives `L̂_N = Ĉ_N − αk̂_N`. -/
theorem employment_growth {α hatY hatC hatk hatL : ℝ} (hprod : hatY = α * hatk + hatL)
    (hclear : hatY = hatC) : hatL = hatC - α * hatk := by linarith

/-- The CES demand for nontradables `C_N = p^{−θ}(1 − γ)Z/(γ + (1 − γ)p^{1−θ})`, O&R (4.16). -/
noncomputable def cesDemandN (γ θ Z p : ℝ) : ℝ :=
  p ^ (-θ) * (1 - γ) * Z / (γ + (1 - γ) * p ^ (1 - θ))

/-- **The price elasticity of nontradables demand at `p = 1`**, O&R (4.17), p. 223: the
log-derivative of `C_N` with respect to `p` at `p = 1` is `−[γθ + (1 − γ)]`. -/
theorem hasDerivAt_log_cesDemandN {γ θ Z : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hZ : 0 < Z) :
    HasDerivAt (fun p => Real.log (cesDemandN γ θ Z p)) (-(γ * θ + (1 - γ))) 1 := by
  have h1 : HasDerivAt (fun p : ℝ => p ^ (-θ)) (-θ * 1 ^ (-θ - 1)) 1 :=
    Real.hasDerivAt_rpow_const (Or.inl one_ne_zero)
  have h2 : HasDerivAt (fun p : ℝ => p ^ (1 - θ)) ((1 - θ) * 1 ^ (1 - θ - 1)) 1 :=
    Real.hasDerivAt_rpow_const (Or.inl one_ne_zero)
  have hden : HasDerivAt (fun p : ℝ => γ + (1 - γ) * p ^ (1 - θ))
      ((1 - γ) * ((1 - θ) * 1 ^ (1 - θ - 1))) 1 := (h2.const_mul (1 - γ)).const_add γ
  have hnum : HasDerivAt (fun p : ℝ => p ^ (-θ) * (1 - γ) * Z)
      (-θ * 1 ^ (-θ - 1) * (1 - γ) * Z) 1 := (h1.mul_const (1 - γ)).mul_const Z
  have hden1 : γ + (1 - γ) * (1 : ℝ) ^ (1 - θ) ≠ 0 := by simp
  have hC := hnum.div hden hden1
  have hC1 : cesDemandN γ θ Z 1 ≠ 0 := by
    unfold cesDemandN
    simp only [Real.one_rpow, one_mul, mul_one]
    have : (0 : ℝ) < 1 - γ := by linarith
    positivity
  have := hC.log hC1
  unfold cesDemandN at this ⊢
  refine this.congr_deriv ?_
  have : (0 : ℝ) < 1 - γ := by linarith
  simp only [Pi.div_apply, Real.one_rpow, one_mul, mul_one]
  field_simp
  ring

/-- **Wealth growth**, O&R p. 224: with `Z = wL + rQ` and `r`, `L`, `Q` fixed,
`Ẑ = ψ_L ŵ` where `ψ_L = wL/(wL + rQ)`. -/
theorem wealth_growth {w L r Q dw : ℝ} (hw : w ≠ 0) :
    (dw * L) / (w * L + r * Q) = (w * L / (w * L + r * Q)) * (dw / w) := by
  field_simp

/-- **The employment effect of tradables productivity**, O&R (4.18), p. 224: combining
`L̂_N = Ĉ_N − αk̂_N` (4.12), `Ĉ_N = Ẑ − [γθ + 1 − γ]p̂` (4.17), `Ẑ = ψ_L ŵ`, and the supply side
`ŵ = k̂_N = Â_T/μ_LT`, `p̂ = (1 − α)Â_T/μ_LT`, gives
`L̂_N = {ψ_L − (1 − α)[γθ + 1 − γ] − α} Â_T/μ_LT`. -/
theorem employment_effect {α γ θ ψ μ hatA hatL hatC hatZ hatw hatp hatk : ℝ}
    (h12 : hatL = hatC - α * hatk) (h17 : hatC = hatZ - (γ * θ + (1 - γ)) * hatp)
    (hZ : hatZ = ψ * hatw) (hw : hatw = hatA / μ) (hk : hatk = hatA / μ)
    (hp : hatp = (1 - α) * hatA / μ) :
    hatL = (ψ - (1 - α) * (γ * θ + 1 - γ) - α) * hatA / μ := by
  rw [h12, h17, hZ, hw, hk, hp]
  ring

/-- **Unit elasticity** (O&R p. 224): with `θ = 1` the bracket in (4.18) reduces to `ψ_L − 1`. -/
theorem employment_effect_unit {α γ ψ μ hatA : ℝ} :
    (ψ - (1 - α) * (γ * 1 + 1 - γ) - α) * hatA / μ = (ψ - 1) * hatA / μ := by ring

/-- **The labour share of wealth is below one iff wealth is positive** (O&R p. 224): with
`wL > 0` and `r > 0`, `ψ_L = wL/(wL + rQ) < 1` iff `Q > 0`. -/
theorem psi_lt_one_iff {w L r Q : ℝ} (hr : 0 < r) (hden : 0 < w * L + r * Q) :
    w * L / (w * L + r * Q) < 1 ↔ 0 < Q := by
  rw [div_lt_one hden]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Productivity growth in tradables shrinks nontradables employment** (O&R p. 224): with unit
elasticity, positive wealth and `Â_T > 0`, `L̂_N = (ψ_L − 1)Â_T/μ_LT < 0`. -/
theorem employment_falls {ψ μ hatA : ℝ} (hψ : ψ < 1) (hμ : 0 < μ) (hA : 0 < hatA) :
    (ψ - 1) * hatA / μ < 0 :=
  div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hA) hμ

end ObstfeldRogoff.RealExchangeRate.ManufacturingEmployment
