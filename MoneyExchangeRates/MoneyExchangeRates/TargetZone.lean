/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MoneyExchangeRates.CaganModel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Target zones for exchange rates

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §8.5–8.6 and
Exercise 5, pp. 569–579, 601.

* The target-zone ODE (84) `G(k) = k + (ηv²/2)G″(k)` and, with trending fundamentals
  (Exercise 5), `G = k + ημG′ + (ηv²/2)G″`: on any open interval its (twice differentiable)
  solutions are **exactly** `ημ + k + b₁e^{λ₁k} + b₂e^{λ₂k}` (for `μ = 0`: `λ₁,₂ = ±λ`,
  `λ = √(2/(ηv²))`); `b₂ = 0` iff `G(k) − k − ημ → 0` as `k → −∞` (§8.6).
* The symmetric zone (85): there are **unique** `b, k̄ > 0` with value matching `S(k̄) = ē` and
  smooth pasting `S′(k̄) = 0`; `k̄` is the unique positive root of `k − tanh(λk)/λ = ē` and
  `b = 1/(2λ cosh λk̄)`. Properties 1–3 of Figure 8.5: `S` is odd, `S′ = 1 − cosh λk/cosh λk̄ ∈
  [0, 1)` on the band with zeros exactly at `±k̄`, `S` maps `[−k̄, k̄]` increasingly onto
  `[−ē, ē]`, concave/convex on the positive/negative side; the **honeymoon effect**
  `|S(k)| < |k|`, so `ē < k̄ < ē + 1/λ`; `k̄ → ē` as `v → 0`.
* Smooth pasting in continuous time (the Itô/local-time argument of *8.5.5, flagged in the
  survey as T13) is *not* formalised; its rigorous substitute here is the **discrete target
  zone**: fundamentals on a lattice `k_i = iΔ`, `|i| ≤ N`, moving `±Δ` with probability ½,
  with the step out of the band suppressed (intervention). The equilibrium condition
  `e = k + (η/h)(E e − e)` has a **unique** solution, given in closed form
  `e_i = iΔ − D sinh(θi)` (`cosh θ = 1 + h/η`); it is odd, strictly increasing, obeys the
  honeymoon effect, its increments are `Δ(1 − cosh θ(i+½)/cosh θ(N+½))` (the discrete
  `S′ = 1 − cosh λk/cosh λk̄`), it pastes smoothly at the ghost node (`e_{N+1} = e_N`), and its
  boundary slope is `O(Δ)`. Without barriers the free float `e = k` is the unique solution with
  `e − k` bounded. The lattice equilibrium *is* CaganModel's `markovFundamental` for the
  regulated band kernel, i.e. (80) holds with expectations under the regulated process.
* **Lattice → continuous** (scaling `h = Δ²/v²`): `θ_Δ = 2 arsinh(λΔ/2)` solves the lattice
  characteristic equation, `θ_Δ/Δ → λ`, the smooth-pasting constant is exactly
  `1/(λ cosh(θ_Δ K/Δ))`, the error is bounded uniformly on the band by `(2K/λ)|θ_Δ/Δ − λ|`,
  so the lattice equilibrium converges uniformly to `S`; for a prescribed ceiling the lattice
  spacing is unique and the lattice band edge converges to `k̄`.
* p. 578: on the lattice the ceiling is hit, and interventions recur, with probability one:
  for every `r`, P(at most `r` interventions by date `n`) → 0, so any finite reserve stock is
  exhausted.
* The one-sided zone of §8.6: (88)–(89) give `k̄ = ē + ℜ`, `b₁ = −ℜe^{−λk̄} < 0`; smooth pasting
  (90) holds iff `ℜ = ℜ′ = 1/λ`; the fully credible zone `k̄′ = ē + 1/λ`; for `ℜ > ℜ′` an attack
  would be an anticipated appreciation (impossible); for `ℜ < ℜ′` the locus `S₁` lacks smooth
  pasting.
* Exercise 5: roots `λ₁ > 0 > λ₂` with `λ₁λ₂ = −2/(ηv²)`; for given fundamental barriers
  `k̲ < k̄`, smooth pasting at both determines `(b₁, b₂)` uniquely; and for **every** drift and
  every prescribed currency band `e̲ < ē` the full 4-equation system (value matching and
  smooth pasting at both edges) has exactly one solution `(b₁, b₂, k̲, k̄)`: by translation
  invariance it reduces to `W(k̄ − k̲) = ē − e̲`, with `W` strictly increasing from 0 to ∞.
* §8.5.6 and fn 60: in a band, `(1+i)/(1+i*)` lies in the range of possible exchange-rate
  changes, by no-arbitrage alone (whatever the preferences); the numbers 2%, 4%, 24%.
* The flag on (86): for a symmetric increment, the regulated increment `min(dk, 0)` has second
  moment `E(dk)²/2`, not `E(dk)²`, and first moment `−E|dk|/2`.
-/

namespace ObstfeldRogoff.MoneyExchangeRates.TargetZone

open Filter Topology Set

/-! ## The target-zone ODE and its general solution -/

/-- A constancy lemma used for O&R (84), p. 572: a function with zero derivative on an open
interval is constant there. -/
theorem const_of_hasDerivAt_zero {f : ℝ → ℝ} {a b : ℝ} (h : ∀ x ∈ Ioo a b, HasDerivAt f 0 x)
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) : f x = f y :=
  IsOpen.is_const_of_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo
    (fun z hz => (h z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (h z hz).deriv) hx hy

/-- O&R (84), p. 572, and Exercise 5, p. 601: the candidate solutions
`G(k) = d + k + b₁e^{λ₁k} + b₂e^{λ₂k}` (`d = ημ`). -/
noncomputable def zoneSolution (d b₁ b₂ l₁ l₂ k : ℝ) : ℝ :=
  d + k + b₁ * Real.exp (l₁ * k) + b₂ * Real.exp (l₂ * k)

/-- O&R (84) and Exercise 5: if `λ₁, λ₂` are the roots of `cλ² + dλ − 1 = 0`
(`c = ηv²/2`, `d = ημ`), the candidates solve `G = k + dG′ + cG″`. -/
theorem zoneSolution_solves {c d l₁ l₂ : ℝ} (h1 : c * l₁ ^ 2 + d * l₁ - 1 = 0)
    (h2 : c * l₂ ^ 2 + d * l₂ - 1 = 0) (b₁ b₂ k : ℝ) :
    HasDerivAt (zoneSolution d b₁ b₂ l₁ l₂)
        (1 + b₁ * l₁ * Real.exp (l₁ * k) + b₂ * l₂ * Real.exp (l₂ * k)) k ∧
      HasDerivAt (fun x => 1 + b₁ * l₁ * Real.exp (l₁ * x) + b₂ * l₂ * Real.exp (l₂ * x))
        (b₁ * l₁ ^ 2 * Real.exp (l₁ * k) + b₂ * l₂ ^ 2 * Real.exp (l₂ * k)) k ∧
      zoneSolution d b₁ b₂ l₁ l₂ k =
        k + d * (1 + b₁ * l₁ * Real.exp (l₁ * k) + b₂ * l₂ * Real.exp (l₂ * k)) +
          c * (b₁ * l₁ ^ 2 * Real.exp (l₁ * k) + b₂ * l₂ ^ 2 * Real.exp (l₂ * k)) := by
  have e1 : ∀ l : ℝ, HasDerivAt (fun x => Real.exp (l * x)) (Real.exp (l * k) * l) k := fun l =>
    by simpa using ((hasDerivAt_id' k).const_mul l).exp
  refine ⟨?_, ?_, ?_⟩
  · have := ((((hasDerivAt_id' k).const_add d).add ((e1 l₁).const_mul b₁)).add
      ((e1 l₂).const_mul b₂))
    unfold zoneSolution; convert this using 1; ring
  · have := ((((e1 l₁).const_mul (b₁ * l₁)).const_add 1).add ((e1 l₂).const_mul (b₂ * l₂)))
    convert this using 1; ring
  · unfold zoneSolution
    linear_combination (-(b₁ * Real.exp (l₁ * k))) * h1 - (b₂ * Real.exp (l₂ * k)) * h2

/-- O&R (84), p. 572, and Exercise 5, p. 601 (**all solutions**): on an open interval, every
twice-differentiable solution of `G = k + dG′ + cG″` is `d + k + b₁e^{λ₁k} + b₂e^{λ₂k}`, where
`λ₁ ≠ λ₂` are the roots of `cλ² + dλ − 1 = 0`. -/
theorem zone_ode_general {c d l₁ l₂ a b : ℝ} (hc : 0 < c) (h1 : c * l₁ ^ 2 + d * l₁ - 1 = 0)
    (h2 : c * l₂ ^ 2 + d * l₂ - 1 = 0) (hne : l₁ ≠ l₂) (hab : a < b) {G G' G'' : ℝ → ℝ}
    (hG : ∀ k ∈ Ioo a b, HasDerivAt G (G' k) k) (hG' : ∀ k ∈ Ioo a b, HasDerivAt G' (G'' k) k)
    (hode : ∀ k ∈ Ioo a b, G k = k + d * G' k + c * G'' k) :
    ∃ b₁ b₂ : ℝ, ∀ k ∈ Ioo a b, G k = zoneSolution d b₁ b₂ l₁ l₂ k := by
  -- Vieta
  have hsum : c * (l₁ + l₂) + d = 0 := by
    have : (l₁ - l₂) * (c * (l₁ + l₂) + d) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  have hprod : c * (l₁ * l₂) = -1 := by linear_combination l₁ * hsum - h1
  have hl : l₂ - l₁ ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  set x₀ := (a + b) / 2 with hx₀
  have hx₀m : x₀ ∈ Ioo a b := ⟨by rw [hx₀]; linarith, by rw [hx₀]; linarith⟩
  set u : ℝ → ℝ := fun k => (G' k - 1 - l₁ * (G k - k - d)) * Real.exp (-l₂ * k) with hu
  have hu' : ∀ k ∈ Ioo a b, HasDerivAt u 0 k := by
    intro k hk
    have hw' : HasDerivAt (fun x => G' x - 1 - l₁ * (G x - x - d))
        (G'' k - l₁ * (G' k - 1)) k := by
      have := ((hG' k hk).sub_const 1).sub ((((hG k hk).sub (hasDerivAt_id' k)).sub_const
        d).const_mul l₁)
      convert this using 1
    have he : HasDerivAt (fun x => Real.exp (-l₂ * x)) (Real.exp (-l₂ * k) * (-l₂)) k := by
      simpa using ((hasDerivAt_id' k).const_mul (-l₂)).exp
    have := hw'.mul he
    convert this using 1
    have hG'' : c * G'' k = G k - k - d * G' k := by linarith [hode k hk]
    have hE := Real.exp_pos (-l₂ * k)
    have key : G'' k - l₁ * (G' k - 1) + (G' k - 1 - l₁ * (G k - k - d)) * (-l₂) = 0 := by
      have hcc : c ≠ 0 := hc.ne'
      have : c * (G'' k - l₁ * (G' k - 1) + (G' k - 1 - l₁ * (G k - k - d)) * (-l₂)) = 0 := by
        linear_combination hG'' - (G' k - 1) * hsum + (G k - k - d) * hprod
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hcc
      · exact h
    linear_combination (-(Real.exp (-l₂ * k))) * key
  obtain ⟨A, hAdef⟩ : ∃ A, A = u x₀ := ⟨_, rfl⟩
  have huA : ∀ k ∈ Ioo a b, u k = A := fun k hk => hAdef ▸ const_of_hasDerivAt_zero hu' hk hx₀m
  set v : ℝ → ℝ := fun k => (G k - k - d) * Real.exp (-l₁ * k) -
    A / (l₂ - l₁) * Real.exp ((l₂ - l₁) * k) with hv
  have hv' : ∀ k ∈ Ioo a b, HasDerivAt v 0 k := by
    intro k hk
    have hw : HasDerivAt (fun x => G x - x - d) (G' k - 1) k :=
      ((hG k hk).sub (hasDerivAt_id' k)).sub_const d
    have he1 : HasDerivAt (fun x => Real.exp (-l₁ * x)) (Real.exp (-l₁ * k) * (-l₁)) k := by
      simpa using ((hasDerivAt_id' k).const_mul (-l₁)).exp
    have he2 : HasDerivAt (fun x => Real.exp ((l₂ - l₁) * x))
        (Real.exp ((l₂ - l₁) * k) * (l₂ - l₁)) k := by
      simpa using ((hasDerivAt_id' k).const_mul (l₂ - l₁)).exp
    have := (hw.mul he1).sub (he2.const_mul (A / (l₂ - l₁)))
    convert this using 1
    have hA := huA k hk
    simp only [hu] at hA
    have x1 : Real.exp (-l₂ * k) * Real.exp ((l₂ - l₁) * k) = Real.exp (-l₁ * k) := by
      rw [← Real.exp_add]; congr 1; ring
    have hAl : A / (l₂ - l₁) * (l₂ - l₁) = A := div_mul_cancel₀ _ hl
    linear_combination (G' k - 1 - l₁ * (G k - k - d)) * x1 -
      Real.exp ((l₂ - l₁) * k) * hA + Real.exp ((l₂ - l₁) * k) * hAl
  obtain ⟨V, hVdef⟩ : ∃ V, V = v x₀ := ⟨_, rfl⟩
  refine ⟨V, A / (l₂ - l₁), fun k hk => ?_⟩
  have hvk : v k = V := hVdef ▸ const_of_hasDerivAt_zero hv' hk hx₀m
  simp only [hv] at hvk
  have y1 : Real.exp (-l₁ * k) * Real.exp (l₁ * k) = 1 := by
    rw [← Real.exp_add]; simp
  have y2 : Real.exp ((l₂ - l₁) * k) * Real.exp (l₁ * k) = Real.exp (l₂ * k) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold zoneSolution
  linear_combination (Real.exp (l₁ * k)) * hvk - (G k - k - d) * y1 +
    (A / (l₂ - l₁)) * y2

/-- O&R p. 572: `λ = √(2/(ηv²))` satisfies `(ηv²/2)λ² = 1`. -/
theorem lambda_spec {η v : ℝ} (hη : 0 < η) (hv : 0 < v) :
    0 < Real.sqrt (2 / (η * v ^ 2)) ∧ η * v ^ 2 / 2 * Real.sqrt (2 / (η * v ^ 2)) ^ 2 = 1 := by
  have hpos : 0 < 2 / (η * v ^ 2) := by positivity
  refine ⟨Real.sqrt_pos.2 hpos, ?_⟩
  rw [Real.sq_sqrt hpos.le]; field_simp

/-- O&R (84), p. 572 (no drift): every twice-differentiable solution of
`G = k + (ηv²/2)G″` on an open interval is `k + b₁e^{λk} + b₂e^{−λk}`,
`λ = √(2/(ηv²))`. -/
theorem zone_ode_no_drift {η v a b : ℝ} (hη : 0 < η) (hv : 0 < v) (hab : a < b)
    {G G' G'' : ℝ → ℝ} (hG : ∀ k ∈ Ioo a b, HasDerivAt G (G' k) k)
    (hG' : ∀ k ∈ Ioo a b, HasDerivAt G' (G'' k) k)
    (hode : ∀ k ∈ Ioo a b, G k = k + η * v ^ 2 / 2 * G'' k) :
    ∃ b₁ b₂ : ℝ, ∀ k ∈ Ioo a b, G k = k + b₁ * Real.exp (Real.sqrt (2 / (η * v ^ 2)) * k) +
      b₂ * Real.exp (-Real.sqrt (2 / (η * v ^ 2)) * k) := by
  obtain ⟨hl, hl2⟩ := lambda_spec hη hv
  set l := Real.sqrt (2 / (η * v ^ 2))
  obtain ⟨b₁, b₂, h⟩ := zone_ode_general (c := η * v ^ 2 / 2) (d := 0) (l₁ := l) (l₂ := -l)
    (by positivity) (by linear_combination hl2) (by linear_combination hl2)
    (by intro h; linarith) hab hG hG' (fun k hk => by rw [hode k hk]; ring)
  exact ⟨b₁, b₂, fun k hk => by rw [h k hk]; unfold zoneSolution; ring⟩

/-- O&R Exercise 5, p. 601: the roots `λ₁,₂ = [−ημ ± √(η²μ² + 2ηv²)]/(ηv²)` of
`(ηv²/2)λ² + ημλ − 1 = 0`. -/
noncomputable def driftRoot (η μ v : ℝ) (sgn : ℝ) : ℝ :=
  (-(η * μ) + sgn * Real.sqrt ((η * μ) ^ 2 + 2 * η * v ^ 2)) / (η * v ^ 2)

/-- O&R Exercise 5, p. 601: both roots solve the characteristic equation. -/
theorem driftRoot_spec {η μ v : ℝ} (hη : 0 < η) (hv : 0 < v) {sgn : ℝ} (hs : sgn ^ 2 = 1) :
    η * v ^ 2 / 2 * driftRoot η μ v sgn ^ 2 + η * μ * driftRoot η μ v sgn - 1 = 0 := by
  have hq : 0 ≤ (η * μ) ^ 2 + 2 * η * v ^ 2 := by positivity
  have hD : 0 < η * v ^ 2 := by positivity
  have key : (sgn * Real.sqrt ((η * μ) ^ 2 + 2 * η * v ^ 2)) ^ 2 =
      (η * μ) ^ 2 + η * v ^ 2 * 2 := by
    rw [mul_pow, hs, one_mul, Real.sq_sqrt hq]; ring
  unfold driftRoot
  generalize Real.sqrt ((η * μ) ^ 2 + 2 * η * v ^ 2) = R at key ⊢
  field_simp
  linear_combination key

/-- O&R Exercise 5, p. 601: `λ₁ > 0 > λ₂`, and `λ₁λ₂ = −2/(ηv²)`. -/
theorem driftRoot_props {η μ v : ℝ} (hη : 0 < η) (hv : 0 < v) :
    0 < driftRoot η μ v 1 ∧ driftRoot η μ v (-1) < 0 ∧
      driftRoot η μ v 1 * driftRoot η μ v (-1) = -2 / (η * v ^ 2) := by
  have hq : 0 ≤ (η * μ) ^ 2 + 2 * η * v ^ 2 := by positivity
  have hsq := Real.sq_sqrt hq
  have hD : 0 < η * v ^ 2 := by positivity
  have hgt : |η * μ| < Real.sqrt ((η * μ) ^ 2 + 2 * η * v ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith [mul_pos hη (pow_pos hv 2)])
  have ha := abs_lt.1 hgt
  refine ⟨?_, ?_, ?_⟩
  · unfold driftRoot; apply div_pos _ hD; linarith [ha.2, ha.1]
  · unfold driftRoot; apply div_neg_of_neg_of_pos _ hD; linarith [ha.2, ha.1]
  · have key : Real.sqrt ((η * μ) ^ 2 + 2 * η * v ^ 2) ^ 2 = (η * μ) ^ 2 + η * v ^ 2 * 2 := by
      rw [hsq]; ring
    unfold driftRoot
    generalize Real.sqrt ((η * μ) ^ 2 + 2 * η * v ^ 2) = R at key ⊢
    field_simp
    linear_combination -key

/-- O&R Exercise 5, p. 601: with `μ = 0` the roots are `±√(2/(ηv²))`. -/
theorem driftRoot_no_drift {η v : ℝ} (hη : 0 < η) (hv : 0 < v) :
    driftRoot η 0 v 1 = Real.sqrt (2 / (η * v ^ 2)) ∧
      driftRoot η 0 v (-1) = -Real.sqrt (2 / (η * v ^ 2)) := by
  have hD : 0 < η * v ^ 2 := by positivity
  have e : Real.sqrt (2 / (η * v ^ 2)) = Real.sqrt (2 * η * v ^ 2) / (η * v ^ 2) := by
    have h1 : Real.sqrt (2 * η * v ^ 2) =
        Real.sqrt (2 / (η * v ^ 2)) * Real.sqrt ((η * v ^ 2) ^ 2) := by
      rw [← Real.sqrt_mul (by positivity)]; congr 1; field_simp
    rw [Real.sqrt_sq hD.le] at h1
    rw [h1]; field_simp
  unfold driftRoot
  simp only [mul_zero, neg_zero, zero_add, one_mul, neg_one_mul, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [e]
  constructor
  · rfl
  · ring

/-- O&R §8.6, p. 577: for `λ₁ > 0 > λ₂`, `G(k) − k − d → 0` as `k → −∞` iff `b₂ = 0`
(so a one-sided zone has `S = k + b₁e^{λk}`). -/
theorem tendsto_atBot_iff {d b₁ b₂ l₁ l₂ : ℝ} (hl₁ : 0 < l₁) (hl₂ : l₂ < 0) :
    Tendsto (fun k => zoneSolution d b₁ b₂ l₁ l₂ k - k - d) atBot (𝓝 0) ↔ b₂ = 0 := by
  have h1 : Tendsto (fun k => Real.exp (l₁ * k)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hl₁)
  have h2 : Tendsto (fun k => Real.exp (-l₂ * k)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot (by linarith))
  have e : ∀ k, zoneSolution d b₁ b₂ l₁ l₂ k - k - d =
      b₁ * Real.exp (l₁ * k) + b₂ * Real.exp (l₂ * k) := fun k => by unfold zoneSolution; ring
  simp_rw [e]
  constructor
  · intro h
    have h3 : Tendsto (fun k => b₂ * Real.exp (l₂ * k)) atBot (𝓝 0) := by
      have := h.sub (h1.const_mul b₁)
      simpa using this
    have h4 := h3.mul h2
    rw [zero_mul] at h4
    have h5 : (fun k => b₂ * Real.exp (l₂ * k) * Real.exp (-l₂ * k)) = fun _ => b₂ := by
      funext k; rw [mul_assoc, ← Real.exp_add]; simp
    rw [h5] at h4
    exact tendsto_nhds_unique tendsto_const_nhds h4
  · intro h; subst h; simpa using h1.const_mul b₁

/-! ## The symmetric target zone -/

/-- O&R (85), p. 572: the symmetric-zone locus `S(k) = k − b[e^{λk} − e^{−λk}] =
k − 2b sinh(λk)`. -/
noncomputable def symS (l b k : ℝ) : ℝ := k - 2 * b * Real.sinh (l * k)

/-- O&R (85), p. 572: the two forms of the locus agree. -/
theorem symS_eq_exp (l b k : ℝ) :
    symS l b k = k - b * (Real.exp (l * k) - Real.exp (-(l * k))) := by
  unfold symS; rw [Real.sinh_eq]; ring

/-- O&R p. 575: `S′(k) = 1 − 2bλ cosh(λk)`. -/
theorem hasDerivAt_symS (l b k : ℝ) :
    HasDerivAt (symS l b) (1 - 2 * b * l * Real.cosh (l * k)) k := by
  have := (hasDerivAt_id' k).sub ((((hasDerivAt_id' k).const_mul l).sinh).const_mul (2 * b))
  unfold symS; convert this using 1; ring

/-- O&R p. 575: `S″(k) = −2bλ² sinh(λk)`. -/
theorem hasDerivAt_symS' (l b k : ℝ) :
    HasDerivAt (fun x => 1 - 2 * b * l * Real.cosh (l * x))
      (-(2 * b * l ^ 2 * Real.sinh (l * k))) k := by
  have := ((((hasDerivAt_id' k).const_mul l).cosh).const_mul (2 * b * l)).const_sub 1
  convert this using 1; ring

/-- O&R (84)–(85), p. 572: `S` solves (84) `S = k + (1/λ²)S″` (i.e. `(ηv²/2) = 1/λ²`). -/
theorem symS_solves_ode {l : ℝ} (hl : l ≠ 0) (b k : ℝ) :
    symS l b k = k + 1 / l ^ 2 * (-(2 * b * l ^ 2 * Real.sinh (l * k))) := by
  unfold symS; field_simp; ring

/-- O&R (85), Figure 8.5: `S` is odd (symmetric zone). -/
theorem symS_odd (l b k : ℝ) : symS l b (-k) = -symS l b k := by
  unfold symS; rw [mul_neg, Real.sinh_neg]; ring

/-- O&R *8.5.5, p. 575: the function `φ(k) = k − tanh(λk)/λ` whose root gives `k̄`. -/
noncomputable def edgeMap (l k : ℝ) : ℝ := k - Real.sinh (l * k) / (l * Real.cosh (l * k))

/-- O&R *8.5.5: `φ′(k) = tanh²(λk)`. -/
theorem hasDerivAt_edgeMap {l : ℝ} (hl : 0 < l) (k : ℝ) :
    HasDerivAt (edgeMap l) ((Real.sinh (l * k) / Real.cosh (l * k)) ^ 2) k := by
  have hs := ((hasDerivAt_id' k).const_mul l).sinh
  have hc := (((hasDerivAt_id' k).const_mul l).cosh).const_mul l
  have hcne : l * Real.cosh (l * k) ≠ 0 := mul_ne_zero hl.ne' (Real.cosh_pos _).ne'
  have := (hasDerivAt_id' k).sub (hs.div hc hcne)
  unfold edgeMap
  convert this using 1
  have hc0 := (Real.cosh_pos (l * k)).ne'
  field_simp
  ring

/-- O&R *8.5.5: `φ` is continuous. -/
theorem continuous_edgeMap {l : ℝ} (hl : 0 < l) : Continuous (edgeMap l) :=
  continuous_iff_continuousAt.2 fun k => (hasDerivAt_edgeMap hl k).continuousAt

/-- O&R *8.5.5: `φ` is strictly increasing on `[0, ∞)`. -/
theorem edgeMap_strictMonoOn {l : ℝ} (hl : 0 < l) : StrictMonoOn (edgeMap l) (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) (continuous_edgeMap hl).continuousOn
    fun x hx => ?_
  rw [interior_Ici] at hx
  rw [(hasDerivAt_edgeMap hl x).deriv]
  have : 0 < Real.sinh (l * x) := Real.sinh_pos_iff.2 (mul_pos hl hx)
  positivity

/-- O&R *8.5.5: `k − 1/λ < φ(k) < k` for `k > 0` (`0 < tanh < 1`). -/
theorem edgeMap_bounds {l : ℝ} (hl : 0 < l) {k : ℝ} (hk : 0 < k) :
    k - 1 / l < edgeMap l k ∧ edgeMap l k < k := by
  have hs : 0 < Real.sinh (l * k) := Real.sinh_pos_iff.2 (mul_pos hl hk)
  have hlt := Real.sinh_lt_cosh (l * k)
  have hc := Real.cosh_pos (l * k)
  unfold edgeMap
  constructor
  · have : Real.sinh (l * k) / (l * Real.cosh (l * k)) < 1 / l := by
      rw [div_lt_div_iff₀ (by positivity) hl]; nlinarith
    linarith
  · have : 0 < Real.sinh (l * k) / (l * Real.cosh (l * k)) := by positivity
    linarith

/-- O&R *8.5.5, p. 575 (**existence and uniqueness of the band edge**): for `ē > 0` there is a
unique `k̄ > 0` with `k̄ − tanh(λk̄)/λ = ē`. -/
theorem existsUnique_edge {l : ℝ} (hl : 0 < l) {ebar : ℝ} (he : 0 < ebar) :
    ∃! kb : ℝ, 0 < kb ∧ edgeMap l kb = ebar := by
  have hx : 0 ≤ ebar + 1 / l := by positivity
  have h0 : edgeMap l 0 = 0 := by simp [edgeMap]
  have h1 : ebar ≤ edgeMap l (ebar + 1 / l) := by
    have := (edgeMap_bounds hl (show 0 < ebar + 1 / l by positivity)).1; linarith
  obtain ⟨kb, hkb, hval⟩ := intermediate_value_Icc hx (continuous_edgeMap hl).continuousOn
    ⟨by rw [h0]; exact he.le, h1⟩
  have hkb0 : 0 < kb := by
    rcases eq_or_lt_of_le hkb.1 with h | h
    · rw [← h, h0] at hval; linarith
    · exact h
  refine ⟨kb, ⟨hkb0, hval⟩, fun y hy => ?_⟩
  exact (edgeMap_strictMonoOn hl).injOn (le_of_lt hy.1) (le_of_lt hkb0) (hy.2.trans hval.symm)

/-- O&R *8.5.5, p. 575 (**the symmetric target-zone solution exists and is unique**): there is
exactly one pair `(b, k̄)` with `k̄ > 0`, value matching `S(k̄) = ē` and smooth pasting
`S′(k̄) = 0`; it has `b = 1/(2λ cosh λk̄)` and `k̄ − tanh(λk̄)/λ = ē`. -/
theorem existsUnique_symmetric_zone {l : ℝ} (hl : 0 < l) {ebar : ℝ} (he : 0 < ebar) :
    ∃! p : ℝ × ℝ, 0 < p.2 ∧ symS l p.1 p.2 = ebar ∧
      1 - 2 * p.1 * l * Real.cosh (l * p.2) = 0 := by
  obtain ⟨kb, ⟨hkb, hval⟩, huniq⟩ := existsUnique_edge hl he
  have hc := Real.cosh_pos (l * kb)
  refine ⟨(1 / (2 * l * Real.cosh (l * kb)), kb), ⟨hkb, ?_, ?_⟩, ?_⟩
  · simp only; unfold symS; unfold edgeMap at hval; rw [← hval]; field_simp
  · simp only; field_simp; ring
  · rintro ⟨b, k⟩ ⟨hk, hS, hS'⟩
    simp only at hk hS hS'
    have hb : b = 1 / (2 * l * Real.cosh (l * k)) := by
      have := Real.cosh_pos (l * k)
      field_simp; linarith
    have hedge : edgeMap l k = ebar := by
      unfold edgeMap; unfold symS at hS; rw [← hS, hb]; field_simp
    have := huniq k ⟨hk, hedge⟩
    subst this
    rw [hb]

/-- O&R Figure 8.5: the properties of the symmetric solution. Given `k̄ > 0` and
`b = 1/(2λ cosh λk̄)` (smooth pasting): `S′(k) = 1 − cosh(λk)/cosh(λk̄)`. -/
theorem symS_deriv_formula {l kb : ℝ} (hl : 0 < l) (k : ℝ) :
    1 - 2 * (1 / (2 * l * Real.cosh (l * kb))) * l * Real.cosh (l * k) =
      1 - Real.cosh (l * k) / Real.cosh (l * kb) := by
  have := (Real.cosh_pos (l * kb)).ne'
  field_simp

/-- O&R Figure 8.5, properties 2–3: `S′(k) ≥ 0` iff `|k| ≤ k̄` (so `0 ≤ S′` on the band),
`S′(k) = 0` iff `|k| = k̄` (smooth pasting exactly at the edges), and `S′ < 1` everywhere
(less sensitive than the free float). -/
theorem symS_deriv_props {l kb : ℝ} (hl : 0 < l) (hkb : 0 < kb) (k : ℝ) :
    (0 ≤ 1 - Real.cosh (l * k) / Real.cosh (l * kb) ↔ |k| ≤ kb) ∧
      (1 - Real.cosh (l * k) / Real.cosh (l * kb) = 0 ↔ |k| = kb) ∧
      1 - Real.cosh (l * k) / Real.cosh (l * kb) < 1 := by
  have hc := Real.cosh_pos (l * kb)
  have hck := Real.cosh_pos (l * k)
  have habs : ∀ x, |l * x| = l * |x| := fun x => by rw [abs_mul, abs_of_pos hl]
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_nonneg, div_le_one hc, Real.cosh_le_cosh, habs, habs, abs_of_pos hkb]
    constructor <;> intro h <;> nlinarith
  · rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq hc.ne']
    constructor
    · intro h
      have h1 : Real.cosh (l * k) ≤ Real.cosh (l * kb) := h.le
      have h2 : Real.cosh (l * kb) ≤ Real.cosh (l * k) := h.ge
      rw [Real.cosh_le_cosh, habs, habs, abs_of_pos hkb] at h1 h2
      nlinarith
    · intro h
      rw [← Real.cosh_abs, habs, h, ← Real.cosh_abs (l * kb), habs, abs_of_pos hkb]
  · have : 0 < Real.cosh (l * k) / Real.cosh (l * kb) := div_pos hck hc
    linarith

/-- O&R Figure 8.5: `S` (with smooth pasting) is strictly increasing on `[−k̄, k̄]`. -/
theorem symS_strictMonoOn {l kb : ℝ} (hl : 0 < l) (hkb : 0 < kb) :
    StrictMonoOn (symS l (1 / (2 * l * Real.cosh (l * kb)))) (Icc (-kb) kb) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (continuous_iff_continuousAt.2 fun x => (hasDerivAt_symS _ _ x).continuousAt).continuousOn
    fun x hx => ?_
  rw [interior_Icc] at hx
  rw [(hasDerivAt_symS _ _ x).deriv, symS_deriv_formula hl]
  have hx' : |x| < kb := abs_lt.2 hx
  have hc := Real.cosh_pos (l * kb)
  rw [sub_pos, div_lt_one hc, Real.cosh_lt_cosh, abs_mul, abs_mul, abs_of_pos hl,
    abs_of_pos hkb]
  nlinarith

/-- O&R Figure 8.5, property 1: with value matching and smooth pasting, `S(±k̄) = ±ē` and `S`
maps `[−k̄, k̄]` onto `[−ē, ē]`. -/
theorem symS_maps_band {l kb ebar : ℝ} (hl : 0 < l) (hkb : 0 < kb)
    (hS : symS l (1 / (2 * l * Real.cosh (l * kb))) kb = ebar) :
    symS l (1 / (2 * l * Real.cosh (l * kb))) (-kb) = -ebar ∧
      symS l (1 / (2 * l * Real.cosh (l * kb))) '' Icc (-kb) kb = Icc (-ebar) ebar := by
  set b := 1 / (2 * l * Real.cosh (l * kb))
  have hodd : symS l b (-kb) = -ebar := by rw [symS_odd, hS]
  refine ⟨hodd, ?_⟩
  have hmono := symS_strictMonoOn hl hkb
  have hcont : ContinuousOn (symS l b) (Icc (-kb) kb) :=
    (continuous_iff_continuousAt.2 fun x => (hasDerivAt_symS _ _ x).continuousAt).continuousOn
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    constructor
    · rw [← hodd]; exact hmono.monotoneOn ⟨le_rfl, by linarith⟩ hx hx.1
    · rw [← hS]; exact hmono.monotoneOn hx ⟨by linarith, le_rfl⟩ hx.2
  · have := intermediate_value_Icc (by linarith : -kb ≤ kb) hcont
    rw [hodd, hS] at this
    exact this

/-- O&R p. 575: `S″ < 0` on `(0, ∞)` (concave above the centre) and `S″ > 0` on `(−∞, 0)`
(convex below), for `b > 0`. -/
theorem symS_curvature {l b : ℝ} (hl : 0 < l) (hb : 0 < b) (k : ℝ) :
    (0 < k → -(2 * b * l ^ 2 * Real.sinh (l * k)) < 0) ∧
      (k < 0 → 0 < -(2 * b * l ^ 2 * Real.sinh (l * k))) := by
  constructor
  · intro hk
    have := Real.sinh_pos_iff.2 (mul_pos hl hk)
    have : 0 < 2 * b * l ^ 2 * Real.sinh (l * k) := by positivity
    linarith
  · intro hk
    have h1 : Real.sinh (l * k) < 0 := by
      have := Real.sinh_lt_sinh.2 (show l * k < 0 by nlinarith)
      simpa using this
    have : 0 < 2 * b * l ^ 2 := by positivity
    nlinarith

/-- O&R p. 575 (**honeymoon effect**): for `b > 0`, `|S(k)| < |k|` for `0 < |k| ≤ k̄`; more
precisely `0 < S(k) < k` for `0 < k ≤ k̄` (and symmetrically). -/
theorem honeymoon {l kb : ℝ} (hl : 0 < l) (hkb : 0 < kb) {k : ℝ} (hk : 0 < k) (hkk : k ≤ kb) :
    0 < symS l (1 / (2 * l * Real.cosh (l * kb))) k ∧
      symS l (1 / (2 * l * Real.cosh (l * kb))) k < k := by
  have hb : 0 < 1 / (2 * l * Real.cosh (l * kb)) := by
    have := Real.cosh_pos (l * kb); positivity
  constructor
  · have h0 : symS l (1 / (2 * l * Real.cosh (l * kb))) 0 = 0 := by simp [symS]
    rw [← h0]
    exact symS_strictMonoOn hl hkb ⟨by linarith, by linarith⟩ ⟨by linarith, hkk⟩ hk
  · unfold symS
    have := Real.sinh_pos_iff.2 (mul_pos hl hk)
    have : 0 < 2 * (1 / (2 * l * Real.cosh (l * kb))) * Real.sinh (l * k) := by positivity
    linarith

/-- O&R p. 575–576: the fundamentals band is strictly wider than the currency band, and not
by more than `1/λ`: `ē < k̄ < ē + 1/λ`. -/
theorem edge_bounds {l kb ebar : ℝ} (hl : 0 < l) (hkb : 0 < kb) (h : edgeMap l kb = ebar) :
    ebar < kb ∧ kb < ebar + 1 / l := by
  have := edgeMap_bounds hl hkb
  constructor <;> linarith

/-- O&R p. 575: as the variance of fundamentals vanishes (`λ → ∞`), the fundamentals band
shrinks to the currency band: `k̄(λ) → ē`. -/
theorem edge_tendsto {ebar : ℝ} {kb : ℝ → ℝ}
    (hkb : ∀ l, 0 < l → 0 < kb l ∧ edgeMap l (kb l) = ebar) :
    Tendsto kb atTop (𝓝 ebar) := by
  have hup : Tendsto (fun l : ℝ => ebar + 1 / l) atTop (𝓝 ebar) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id :
      Tendsto (fun l : ℝ => (1 : ℝ) / l) atTop (𝓝 0))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with l hl
    exact (edge_bounds hl (hkb l hl).1 (hkb l hl).2).1.le
  · filter_upwards [eventually_gt_atTop 0] with l hl
    exact (edge_bounds hl (hkb l hl).1 (hkb l hl).2).2.le

/-- O&R p. 572: `λ = √(2/(ηv²)) → ∞` as `v → 0⁺`. -/
theorem lambda_tendsto {η : ℝ} (hη : 0 < η) :
    Tendsto (fun v => Real.sqrt (2 / (η * v ^ 2))) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun v : ℝ => η * v ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun v : ℝ => η * v ^ 2) (𝓝 0) (𝓝 (η * 0 ^ 2)) :=
        ((continuous_const.mul (continuous_pow 2)).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with v hv
      simp only [mem_Ioi] at hv ⊢; positivity
  have h2 : Tendsto (fun v : ℝ => 2 / (η * v ^ 2)) (𝓝[>] 0) atTop :=
    (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop (by norm_num : (0 : ℝ) < 2) |>.congr
      fun v => by simp [div_eq_mul_inv]
  exact Real.tendsto_sqrt_atTop.comp h2

/-! ## The discrete target zone (a finite Markov chain) -/

/-- O&R (79), (81), pp. 570–571, discretised: an equilibrium of the lattice target zone.
Fundamentals are `k_i = iΔ`, `|i| ≤ N`; each period they move `±Δ` with probability ½, the
step out of the band being suppressed by intervention; the equilibrium condition is
`e_i = k_i + (η/h)(E[e_next | i] − e_i)` with `a = η/h`. -/
def IsLatticeEqm (a Δ : ℝ) (N : ℤ) (e : ℤ → ℝ) : Prop :=
  ∀ i : ℤ, -N ≤ i → i ≤ N →
    e i = i * Δ + a * ((e (min (i + 1) N) + e (max (i - 1) (-N))) / 2 - e i)

/-- O&R §8.5 (discrete version): **uniqueness**: two lattice equilibria coincide on the band
(the equilibrium system is strictly diagonally dominant; discrete maximum principle). -/
theorem latticeEqm_unique {a Δ : ℝ} (ha : 0 < a) {N : ℤ} (hN : 0 ≤ N) {e e' : ℤ → ℝ}
    (he : IsLatticeEqm a Δ N e) (he' : IsLatticeEqm a Δ N e') :
    ∀ i : ℤ, -N ≤ i → i ≤ N → e i = e' i := by
  set d : ℤ → ℝ := fun i => e i - e' i with hd
  have hdeq : ∀ i : ℤ, -N ≤ i → i ≤ N →
      (1 + a) * d i = a * ((d (min (i + 1) N) + d (max (i - 1) (-N))) / 2) := by
    intro i h1 h2
    have := he i h1 h2; have := he' i h1 h2
    simp only [hd]; linarith
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image (Finset.Icc (-N) N) (fun i => |d i|)
    ⟨0, Finset.mem_Icc.2 ⟨by omega, hN⟩⟩
  rw [Finset.mem_Icc] at hi₀
  have hup : min (i₀ + 1) N ∈ Finset.Icc (-N) N := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hdn : max (i₀ - 1) (-N) ∈ Finset.Icc (-N) N := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have h0 : |d i₀| = 0 := by
    have key := hdeq i₀ hi₀.1 hi₀.2
    have hb1 := hmax _ hup
    have hb2 := hmax _ hdn
    have : (1 + a) * |d i₀| ≤ a * |d i₀| := by
      calc (1 + a) * |d i₀| = |(1 + a) * d i₀| := by
            rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 + a by linarith)]
        _ = |a * ((d (min (i₀ + 1) N) + d (max (i₀ - 1) (-N))) / 2)| := by rw [key]
        _ ≤ a * ((|d (min (i₀ + 1) N)| + |d (max (i₀ - 1) (-N))|) / 2) := by
            rw [abs_mul, abs_of_pos ha, abs_div, abs_two]
            gcongr; exact abs_add_le _ _
        _ ≤ a * |d i₀| := by gcongr; linarith
    linarith [abs_nonneg (d i₀)]
  intro i h1 h2
  have := hmax i (Finset.mem_Icc.2 ⟨h1, h2⟩)
  rw [h0] at this
  have : d i = 0 := abs_nonpos_iff.1 this
  simp only [hd] at this; linarith

/-- O&R §8.5 (discrete version): the characteristic root: there is `θ > 0` with
`cosh θ = 1 + 1/a`. -/
theorem exists_theta {a : ℝ} (ha : 0 < a) : ∃ θ : ℝ, 0 < θ ∧ Real.cosh θ = 1 + 1 / a := by
  set c := 1 + 1 / a with hc
  have hc1 : 1 < c := by
    have : 0 < 1 / a := by positivity
    rw [hc]; linarith
  have hcc : c ≤ Real.cosh c := by
    have h1 := Real.quadratic_le_exp_of_nonneg (show 0 ≤ c by linarith)
    have h2 := Real.exp_pos (-c)
    rw [Real.cosh_eq]; nlinarith
  obtain ⟨θ, hθ, hval⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ c by linarith)
    Real.continuous_cosh.continuousOn ⟨by rw [Real.cosh_zero]; linarith, hcc⟩
  refine ⟨θ, ?_, hval⟩
  rcases eq_or_lt_of_le hθ.1 with h | h
  · rw [← h, Real.cosh_zero] at hval; linarith
  · exact h

/-- O&R §8.5 (discrete version): the closed-form lattice solution `e_i = iΔ − D sinh(θi)`. -/
noncomputable def latticeSol (Δ θ D : ℝ) (i : ℤ) : ℝ := i * Δ - D * Real.sinh (θ * i)

/-- O&R §8.5 (discrete version): the smooth-pasting coefficient
`D = Δ/(sinh θ(N+1) − sinh θN)`. -/
noncomputable def latticeCoeff (Δ θ : ℝ) (N : ℤ) : ℝ :=
  Δ / (Real.sinh (θ * (N + 1)) - Real.sinh (θ * N))

/-- A hyperbolic identity used for the lattice solution:
`sinh(x + θ) + sinh(x − θ) = 2 sinh x cosh θ`. -/
theorem sinh_add_add_sinh_sub (x θ : ℝ) :
    Real.sinh (x + θ) + Real.sinh (x - θ) = 2 * Real.sinh x * Real.cosh θ := by
  rw [Real.sinh_add, Real.sinh_sub]; ring

/-- A hyperbolic identity used for the lattice increments:
`sinh(u + v) − sinh(u − v) = 2 cosh u sinh v`. -/
theorem sinh_add_sub_sinh_sub (u v : ℝ) :
    Real.sinh (u + v) - Real.sinh (u - v) = 2 * Real.cosh u * Real.sinh v := by
  rw [Real.sinh_add, Real.sinh_sub]; ring

/-- O&R §8.5 (discrete version): `sinh θ(j+1) − sinh θj = 2 cosh(θ(j+½)) sinh(θ/2)`. -/
theorem sinh_step (θ x : ℝ) :
    Real.sinh (θ * (x + 1)) - Real.sinh (θ * x) =
      2 * Real.cosh (θ * (x + 1 / 2)) * Real.sinh (θ / 2) := by
  rw [← sinh_add_sub_sinh_sub]; congr 2 <;> ring

/-- O&R §8.5 (discrete version): the smooth-pasting coefficient is positive. -/
theorem latticeCoeff_pos {Δ θ : ℝ} (hΔ : 0 < Δ) (hθ : 0 < θ) (N : ℤ) :
    0 < latticeCoeff Δ θ N := by
  unfold latticeCoeff
  rw [sinh_step]
  have := Real.sinh_pos_iff.2 (show 0 < θ / 2 by linarith)
  have := Real.cosh_pos (θ * (N + 1 / 2))
  positivity

/-- O&R §8.5 (discrete version): **existence**: the closed form solves the lattice equilibrium
conditions, interior and boundary (`N ≥ 1`, `cosh θ = 1 + 1/a`). -/
theorem latticeSol_isEqm {a Δ θ : ℝ} (ha : 0 < a) (hΔ : 0 < Δ) (hθ : 0 < θ)
    (hcosh : Real.cosh θ = 1 + 1 / a) {N : ℤ} (hN : 1 ≤ N) :
    IsLatticeEqm a Δ N (latticeSol Δ θ (latticeCoeff Δ θ N)) := by
  set D := latticeCoeff Δ θ N with hD
  have hDdef : D * (Real.sinh (θ * (N + 1)) - Real.sinh (θ * N)) = Δ := by
    rw [hD]; unfold latticeCoeff
    have : 0 < Real.sinh (θ * (N + 1)) - Real.sinh (θ * N) := by
      rw [sinh_step]
      have := Real.sinh_pos_iff.2 (show 0 < θ / 2 by linarith)
      have := Real.cosh_pos (θ * (N + 1 / 2))
      positivity
    field_simp
  have hid : ∀ x : ℝ, Real.sinh (θ * (x + 1)) + Real.sinh (θ * (x - 1)) =
      2 * Real.sinh (θ * x) * (1 + 1 / a) := by
    intro x; rw [← hcosh, ← sinh_add_add_sinh_sub]; congr 2 <;> ring
  have ha1 : a * (1 / a) = 1 := by field_simp
  intro i h1 h2
  unfold latticeSol
  rcases eq_or_lt_of_le h2 with hi | hi
  · -- the upper boundary `i = N`
    subst hi
    rw [min_eq_right (by omega), max_eq_left (by omega)]
    push_cast
    have := hid (i : ℝ)
    linear_combination (-(a / 2)) * hDdef + (a * D / 2) * this + D * Real.sinh (θ * i) * ha1
  rcases eq_or_lt_of_le h1 with hi' | hi'
  · -- the lower boundary `i = −N`
    rw [← hi', min_eq_left (by omega), max_eq_right (by omega)]
    push_cast
    have := hid (N : ℝ)
    have e1 : Real.sinh (θ * (-(N : ℝ) + 1)) = -Real.sinh (θ * (N - 1)) := by
      rw [← Real.sinh_neg]; congr 1; ring
    have e2 : Real.sinh (θ * (-(N : ℝ))) = -Real.sinh (θ * N) := by
      rw [← Real.sinh_neg]; congr 1; ring
    rw [e1, e2]
    linear_combination (a / 2) * hDdef - (a * D / 2) * this - D * Real.sinh (θ * N) * ha1
  · -- interior nodes
    rw [min_eq_left (by omega), max_eq_left (by omega)]
    push_cast
    have := hid (i : ℝ)
    linear_combination (a * D / 2) * this + D * Real.sinh (θ * i) * ha1

/-- O&R §8.5 (discrete version): **existence and uniqueness** of the lattice equilibrium. -/
theorem latticeEqm_existsUnique {a Δ : ℝ} (ha : 0 < a) (hΔ : 0 < Δ) {N : ℤ} (hN : 1 ≤ N) :
    ∃ e : ℤ → ℝ, IsLatticeEqm a Δ N e ∧
      ∀ e' : ℤ → ℝ, IsLatticeEqm a Δ N e' → ∀ i : ℤ, -N ≤ i → i ≤ N → e' i = e i := by
  obtain ⟨θ, hθ, hcosh⟩ := exists_theta ha
  have he := latticeSol_isEqm ha hΔ hθ hcosh hN
  exact ⟨_, he, fun e' he' => latticeEqm_unique ha (by omega) he' he⟩

/-- O&R Figure 8.5 (discrete version): the lattice solution is odd (symmetric zone). -/
theorem latticeSol_odd (Δ θ D : ℝ) (i : ℤ) : latticeSol Δ θ D (-i) = -latticeSol Δ θ D i := by
  unfold latticeSol; push_cast; rw [mul_neg, Real.sinh_neg]; ring

/-- O&R p. 575 (discrete version): the increments of the lattice solution are
`e_{i+1} − e_i = Δ(1 − cosh θ(i+½)/cosh θ(N+½))`, the discrete analogue of
`S′(k) = 1 − cosh λk/cosh λk̄` (with `k̄` at `N + ½`). -/
theorem latticeSol_increment {Δ θ : ℝ} (hθ : 0 < θ) (N i : ℤ) :
    latticeSol Δ θ (latticeCoeff Δ θ N) (i + 1) - latticeSol Δ θ (latticeCoeff Δ θ N) i =
      Δ * (1 - Real.cosh (θ * (i + 1 / 2)) / Real.cosh (θ * (N + 1 / 2))) := by
  unfold latticeSol latticeCoeff
  push_cast
  have h1 := sinh_step θ (i : ℝ)
  have h2 := sinh_step θ (N : ℝ)
  have hs := Real.sinh_pos_iff.2 (show 0 < θ / 2 by linarith)
  have hc := Real.cosh_pos (θ * (N + 1 / 2))
  rw [h2]
  have e : Δ / (2 * Real.cosh (θ * (N + 1 / 2)) * Real.sinh (θ / 2)) *
      Real.sinh (θ * (i + 1)) - Δ / (2 * Real.cosh (θ * (N + 1 / 2)) * Real.sinh (θ / 2)) *
      Real.sinh (θ * i) = Δ * (Real.cosh (θ * (i + 1 / 2)) / Real.cosh (θ * (N + 1 / 2))) := by
    rw [← mul_sub, h1]; field_simp
  linear_combination -e

/-- O&R Figure 8.5 (discrete version): the lattice solution is strictly increasing on the band
and responds less than one-for-one to fundamentals: `0 < e_{i+1} − e_i < Δ` for
`−N ≤ i ≤ N − 1`. -/
theorem latticeSol_increment_bounds {Δ θ : ℝ} (hΔ : 0 < Δ) (hθ : 0 < θ) {N i : ℤ}
    (h1 : -N ≤ i) (h2 : i ≤ N - 1) :
    0 < latticeSol Δ θ (latticeCoeff Δ θ N) (i + 1) - latticeSol Δ θ (latticeCoeff Δ θ N) i ∧
      latticeSol Δ θ (latticeCoeff Δ θ N) (i + 1) - latticeSol Δ θ (latticeCoeff Δ θ N) i <
        Δ := by
  rw [latticeSol_increment hθ]
  have hc := Real.cosh_pos (θ * (N + 1 / 2))
  have hci := Real.cosh_pos (θ * (i + 1 / 2))
  have hlt : Real.cosh (θ * (i + 1 / 2)) < Real.cosh (θ * (N + 1 / 2)) := by
    rw [Real.cosh_lt_cosh, abs_mul, abs_mul, abs_of_pos hθ]
    refine mul_lt_mul_of_pos_left ?_ hθ
    have hi1 : (-(N : ℝ)) ≤ i := by exact_mod_cast h1
    have hi2 : (i : ℝ) ≤ N - 1 := by exact_mod_cast h2
    rw [abs_of_pos (by linarith : (0 : ℝ) < N + 1 / 2)]
    exact abs_lt.2 ⟨by linarith, by linarith⟩
  constructor
  · have : Real.cosh (θ * (i + 1 / 2)) / Real.cosh (θ * (N + 1 / 2)) < 1 :=
      (div_lt_one hc).2 hlt
    nlinarith
  · have : 0 < Real.cosh (θ * (i + 1 / 2)) / Real.cosh (θ * (N + 1 / 2)) := div_pos hci hc
    nlinarith

/-- O&R p. 573, property 3 (discrete version, **smooth pasting at the ghost node**): extending
the closed form one step beyond the band, `e_{N+1} = e_N`. -/
theorem latticeSol_smooth_pasting {Δ θ : ℝ} (hθ : 0 < θ) (N : ℤ) :
    latticeSol Δ θ (latticeCoeff Δ θ N) (N + 1) = latticeSol Δ θ (latticeCoeff Δ θ N) N := by
  have := latticeSol_increment (Δ := Δ) hθ N N
  rw [div_self (Real.cosh_pos _).ne'] at this
  linarith

/-- O&R p. 575 (discrete honeymoon effect): `0 < e_i < k_i = iΔ` for `0 < i ≤ N`. -/
theorem latticeSol_honeymoon {Δ θ : ℝ} (hΔ : 0 < Δ) (hθ : 0 < θ) {N : ℤ} {i : ℤ} (hi : 0 < i)
    (hiN : i ≤ N) :
    0 < latticeSol Δ θ (latticeCoeff Δ θ N) i ∧ latticeSol Δ θ (latticeCoeff Δ θ N) i < i * Δ := by
  constructor
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
    induction n with
    | zero =>
      have := (latticeSol_increment_bounds hΔ hθ (N := N) (i := 0) (by omega) (by omega)).1
      simp only [zero_add] at this
      have h0 : latticeSol Δ θ (latticeCoeff Δ θ N) 0 = 0 := by simp [latticeSol]
      simp only [Nat.cast_zero, zero_add]; linarith
    | succ n ih =>
      have := (latticeSol_increment_bounds hΔ hθ (N := N) (i := (n : ℤ) + 1) (by omega)
        (by omega)).1
      have h' := ih (by omega) (by omega)
      push_cast at this ⊢
      linarith
  · unfold latticeSol
    have hi' : (0 : ℝ) < i := by exact_mod_cast hi
    have := Real.sinh_pos_iff.2 (mul_pos hθ hi')
    have := latticeCoeff_pos hΔ hθ N
    have : 0 < latticeCoeff Δ θ N * Real.sinh (θ * i) := by positivity
    linarith

/-- O&R (79) at the band edge (discrete version): the boundary equation gives
`e_N − e_{N−1} = (2/a)(k_N − e_N)`; with `a = η/h`, `h = Δ²/v²`, the boundary slope is
`O(Δ)`: `(e_N − e_{N−1})/Δ ≤ 2Δ k_N/(ηv²)` (discrete smooth pasting; `e_N ≥ 0` holds for the
equilibrium by `latticeSol_honeymoon`). -/
theorem lattice_boundary_slope {η v Δ : ℝ} (hη : 0 < η) (hv : 0 < v) (hΔ : 0 < Δ) {N : ℤ}
    (hN : 1 ≤ N) {e : ℤ → ℝ} (he : IsLatticeEqm (η * v ^ 2 / Δ ^ 2) Δ N e)
    (heN : 0 ≤ e N) :
    e N - e (N - 1) = 2 / (η * v ^ 2 / Δ ^ 2) * (N * Δ - e N) ∧
      (e N - e (N - 1)) / Δ ≤ 2 * Δ * (N * Δ) / (η * v ^ 2) := by
  have h := he N (by omega) le_rfl
  rw [min_eq_right (by omega), max_eq_left (by omega)] at h
  have ha : 0 < η * v ^ 2 / Δ ^ 2 := by positivity
  have key : e N - e (N - 1) = 2 / (η * v ^ 2 / Δ ^ 2) * (N * Δ - e N) := by
    field_simp; field_simp at h; linarith
  refine ⟨key, ?_⟩
  have e1 : 2 / (η * v ^ 2 / Δ ^ 2) = 2 * Δ ^ 2 / (η * v ^ 2) := by field_simp
  have hden : 0 < η * v ^ 2 := by positivity
  rw [key, e1, div_le_iff₀ hΔ, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right hden]
  nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sq_nonneg Δ)) heN]

/-- O&R p. 571 (the free float): without barriers, `e = k` solves the lattice equation on all
of `ℤ`. -/
theorem freeFloat_solves (a Δ : ℝ) (i : ℤ) :
    (i : ℝ) * Δ = i * Δ + a * ((((i + 1 : ℤ) : ℝ) * Δ + ((i - 1 : ℤ) : ℝ) * Δ) / 2 - i * Δ) := by
  push_cast; ring

/-- O&R p. 571 (the free float): it is the unique solution on the unrestricted lattice whose
deviation from fundamentals is bounded (no bubbles). -/
theorem freeFloat_unique {a Δ : ℝ} (ha : 0 < a) {e : ℤ → ℝ}
    (he : ∀ i : ℤ, e i = i * Δ + a * ((e (i + 1) + e (i - 1)) / 2 - e i)) {M : ℝ}
    (hM : ∀ i, |e i - i * Δ| ≤ M) : ∀ i, e i = i * Δ := by
  set B : ℤ → ℝ := fun i => e i - i * Δ with hB
  have hbub : ∀ i, B i = a / (1 + a) * ((B (i + 1) + B (i - 1)) / 2) := by
    intro i
    have := he i
    simp only [hB]; push_cast
    rw [div_mul_eq_mul_div, eq_div_iff (by linarith)]
    linear_combination this
  have h0 := CaganModel.bubble_eq_zero_of_bounded (fun g i => (g (i + 1) + g (i - 1)) / 2)
    (fun g M hg i => by
      rw [abs_div, abs_two]
      linarith [abs_add_le (g (i + 1)) (g (i - 1)), hg (i + 1), hg (i - 1)])
    (by positivity) (by rw [div_lt_one (by linarith)]; linarith) hbub (M := M) hM
  intro i
  have := congrFun h0 i
  simp only [hB, Pi.zero_apply] at this
  linarith

/-! ## Speculative attacks on a one-sided target zone (§8.6) -/

/-- O&R §8.6, p. 577: the one-sided zone locus `S(k) = k + b₁e^{λk}`. -/
noncomputable def oneS (l b₁ k : ℝ) : ℝ := k + b₁ * Real.exp (l * k)

/-- O&R (88)–(89), p. 577: value matching at the attack point and no jump into the float hold
iff `k̄ = ē + ℜ` and `b₁ = −ℜe^{−λk̄}`; hence `b₁ < 0` for `ℜ > 0`. -/
theorem oneSided_attack_iff (l ebar R b₁ kb : ℝ) :
    (oneS l b₁ kb = ebar ∧ oneS l b₁ kb = kb - R) ↔
      kb = ebar + R ∧ b₁ = -R * Real.exp (-(l * kb)) := by
  have he := Real.exp_pos (l * kb)
  have hinv : Real.exp (l * kb) * Real.exp (-(l * kb)) = 1 := by rw [← Real.exp_add]; simp
  unfold oneS
  constructor
  · rintro ⟨h1, h2⟩
    have hb : b₁ * Real.exp (l * kb) = -R := by linarith
    refine ⟨by linarith, ?_⟩
    linear_combination Real.exp (-(l * kb)) * hb - b₁ * hinv
  · rintro ⟨h1, h2⟩
    have hb : b₁ * Real.exp (l * kb) = -R := by rw [h2]; linear_combination (-R) * hinv
    constructor <;> linarith

/-- O&R p. 577: for `ℜ > 0` the attack locus has `b₁ < 0`. -/
theorem oneSided_b_neg {l R kb : ℝ} (hR : 0 < R) : -R * Real.exp (-(l * kb)) < 0 := by
  have := Real.exp_pos (-(l * kb)); nlinarith

/-- O&R (90), p. 578: under (88)–(89), smooth pasting `S′(k̄) = 1 + λb₁e^{λk̄} = 0` holds iff
`ℜ = ℜ′ = 1/λ`. -/
theorem oneSided_smooth_pasting_iff {l ebar R : ℝ} (hl : 0 < l) :
    1 + l * (-R * Real.exp (-(l * (ebar + R)))) * Real.exp (l * (ebar + R)) = 0 ↔ R = 1 / l := by
  have hinv : Real.exp (-(l * (ebar + R))) * Real.exp (l * (ebar + R)) = 1 := by
    rw [← Real.exp_add]; simp
  have e : 1 + l * (-R * Real.exp (-(l * (ebar + R)))) * Real.exp (l * (ebar + R)) =
      1 - l * R := by linear_combination (-(l * R)) * hinv
  rw [e, eq_div_iff hl.ne']
  constructor <;> intro h <;> linarith

/-- O&R p. 578–579 (the fully credible zone): there is a unique `(b₁, k̄′)` with value matching
`S(k̄′) = ē` and smooth pasting `S′(k̄′) = 0`: `k̄′ = ē + 1/λ`, `b₁ = −(1/λ)e^{−λk̄′}`. -/
theorem credible_zone_existsUnique {l : ℝ} (hl : 0 < l) (ebar : ℝ) :
    ∃! p : ℝ × ℝ, oneS l p.1 p.2 = ebar ∧ 1 + l * p.1 * Real.exp (l * p.2) = 0 := by
  have hinv : ∀ x, Real.exp x * Real.exp (-x) = 1 := fun x => by rw [← Real.exp_add]; simp
  refine ⟨(-(1 / l) * Real.exp (-(l * (ebar + 1 / l))), ebar + 1 / l), ⟨?_, ?_⟩, ?_⟩
  · simp only; unfold oneS
    have := hinv (l * (ebar + 1 / l))
    linear_combination (-(1 / l)) * this
  · simp only
    have := hinv (l * (ebar + 1 / l))
    have hl1 : l * (1 / l) = 1 := by field_simp
    linear_combination (-1) * this - (Real.exp (-(l * (ebar + 1 / l))) *
      Real.exp (l * (ebar + 1 / l))) * hl1
  · rintro ⟨b, k⟩ ⟨h1, h2⟩
    simp only at h1 h2
    unfold oneS at h1
    have hb : b * Real.exp (l * k) = -(1 / l) := by field_simp; linarith
    have hk : k = ebar + 1 / l := by linarith
    subst hk
    have := hinv (l * (ebar + 1 / l))
    simp only [Prod.mk.injEq, and_true]
    linear_combination Real.exp (-(l * (ebar + 1 / l))) * hb - b * this

/-- O&R p. 579: if reserves are large (`ℜ > ℜ′ = 1/λ`) an attack at `k̄′` would move the rate
to the float value `k̄′ − ℜ < ē`, an anticipated appreciation: no attack can occur; attacks are
possible only if `ℜ ≤ ℜ′`. -/
theorem attack_impossible_iff {l ebar R : ℝ} :
    ebar + 1 / l - R < ebar ↔ 1 / l < R := by constructor <;> intro h <;> linarith

/-- O&R Figure 8.6 (`S₂`): the fully credible locus satisfies `S₂′(k) = 1 − e^{λ(k−k̄′)}`,
which is `≥ 0` exactly for `k ≤ k̄′` and vanishes only at `k̄′`. -/
theorem credible_zone_deriv {l k kb : ℝ} (hl : 0 < l) :
    1 + l * (-(1 / l) * Real.exp (-(l * kb))) * Real.exp (l * k) = 1 - Real.exp (l * (k - kb)) ∧
      (0 ≤ 1 - Real.exp (l * (k - kb)) ↔ k ≤ kb) ∧ (1 - Real.exp (l * (k - kb)) = 0 ↔ k = kb) := by
  refine ⟨?_, ?_, ?_⟩
  · have : Real.exp (-(l * kb)) * Real.exp (l * k) = Real.exp (l * (k - kb)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hl1 : l * (1 / l) = 1 := by field_simp
    linear_combination (-(Real.exp (-(l * kb)) * Real.exp (l * k))) * hl1 - this
  · rw [sub_nonneg]
    constructor
    · intro h; by_contra hc; push Not at hc
      have := Real.one_lt_exp_iff.2 (show 0 < l * (k - kb) by nlinarith); linarith
    · intro h; exact Real.exp_le_one_iff.2 (by nlinarith)
  · rw [sub_eq_zero, eq_comm, Real.exp_eq_one_iff]
    constructor
    · intro h; rcases mul_eq_zero.1 h with h | h
      · linarith
      · linarith
    · intro h; rw [h, sub_self, mul_zero]

/-- O&R Figure 8.6: the fully credible locus lies strictly below the free float
(`S₂(k) < k`, honeymoon) and never above the ceiling `ē` (its maximum, `ē`, is at `k̄′`). -/
theorem credible_zone_below {l ebar k : ℝ} (hl : 0 < l) :
    oneS l (-(1 / l) * Real.exp (-(l * (ebar + 1 / l)))) k < k ∧
      oneS l (-(1 / l) * Real.exp (-(l * (ebar + 1 / l)))) k ≤ ebar := by
  set kb := ebar + 1 / l
  have hE : Real.exp (-(l * kb)) * Real.exp (l * k) = Real.exp (l * (k - kb)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos := Real.exp_pos (l * (k - kb))
  unfold oneS
  constructor
  · have : 0 < 1 / l * (Real.exp (-(l * kb)) * Real.exp (l * k)) := by rw [hE]; positivity
    nlinarith
  · -- `k − e^{λ(k−k̄′)}/λ ≤ k̄′ − 1/λ` since `x − e^{λ x}/λ` is maximal at `x = 0`
    have h1 := Real.add_one_le_exp (l * (k - kb))
    have : k - 1 / l * Real.exp (l * (k - kb)) ≤ kb - 1 / l := by
      have : 1 / l * (l * (k - kb) + 1) ≤ 1 / l * Real.exp (l * (k - kb)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have e : 1 / l * (l * (k - kb) + 1) = k - kb + 1 / l := by field_simp
      linarith
    have e2 : k + -(1 / l) * Real.exp (-(l * kb)) * Real.exp (l * k) =
        k - 1 / l * Real.exp (l * (k - kb)) := by rw [← hE]; ring
    rw [e2]; simp only [kb] at this ⊢; linarith

/-- O&R Figure 8.6 (`S₁`): when reserves are small (`ℜ < 1/λ`) the attack locus has no smooth
pasting (`S₁′(k̄) = 1 − λℜ > 0`) and is strictly increasing up to `k̄`. -/
theorem small_reserves_locus {l R ebar : ℝ} (hl : 0 < l) (hRl : R < 1 / l) :
    0 < 1 - l * R ∧ StrictMonoOn (oneS l (-R * Real.exp (-(l * (ebar + R))))) (Iic (ebar + R)) := by
  have hlR : l * R < 1 := by rw [lt_div_iff₀ hl] at hRl; linarith
  refine ⟨by linarith, ?_⟩
  set kb := ebar + R
  have hd : ∀ x, HasDerivAt (oneS l (-R * Real.exp (-(l * kb))))
      (1 - l * R * Real.exp (l * (x - kb))) x := by
    intro x
    have := (hasDerivAt_id' x).add ((((hasDerivAt_id' x).const_mul l).exp).const_mul
      (-R * Real.exp (-(l * kb))))
    unfold oneS
    convert this using 1
    have : Real.exp (-(l * kb)) * Real.exp (l * x) = Real.exp (l * (x - kb)) := by
      rw [← Real.exp_add]; congr 1; ring
    linear_combination (l * R) * this
  refine strictMonoOn_of_deriv_pos (convex_Iic _)
    (continuous_iff_continuousAt.2 fun x => (hd x).continuousAt).continuousOn fun x hx => ?_
  rw [interior_Iic] at hx
  rw [(hd x).deriv]
  have : Real.exp (l * (x - kb)) < 1 := Real.exp_lt_one_iff.2 (by
    simp only [mem_Iio] at hx; nlinarith)
  nlinarith [Real.exp_pos (l * (x - kb))]

/-! ## Exercise 5: trending fundamentals with given barriers -/

/-- O&R Exercise 5, p. 601: for fundamental barriers `k̲ < k̄` and distinct nonzero roots
`λ₁ ≠ λ₂`, smooth pasting at both barriers,
`1 + λ₁b₁e^{λ₁k} + λ₂b₂e^{λ₂k} = 0` at `k = k̲, k̄`, has a unique solution `(b₁, b₂)`. -/
theorem drift_band_smooth_pasting {l₁ l₂ kl kh : ℝ} (h1 : l₁ ≠ 0) (h2 : l₂ ≠ 0)
    (hne : l₁ ≠ l₂) (hk : kl < kh) :
    ∃! p : ℝ × ℝ,
      1 + l₁ * p.1 * Real.exp (l₁ * kl) + l₂ * p.2 * Real.exp (l₂ * kl) = 0 ∧
        1 + l₁ * p.1 * Real.exp (l₁ * kh) + l₂ * p.2 * Real.exp (l₂ * kh) = 0 := by
  set E1 := Real.exp (l₁ * kl); set E2 := Real.exp (l₂ * kl)
  set F1 := Real.exp (l₁ * kh); set F2 := Real.exp (l₂ * kh)
  have hdet : E1 * F2 - E2 * F1 ≠ 0 := by
    intro h
    have : Real.exp (l₁ * kl + l₂ * kh) = Real.exp (l₂ * kl + l₁ * kh) := by
      rw [Real.exp_add, Real.exp_add]; linarith
    have := Real.exp_injective this
    have : (l₁ - l₂) * (kl - kh) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact hne (by linarith)
    · linarith
  set det := l₁ * l₂ * (E1 * F2 - E2 * F1) with hdd
  have hdet' : det ≠ 0 := mul_ne_zero (mul_ne_zero h1 h2) hdet
  refine ⟨(l₂ * (E2 - F2) / det, l₁ * (F1 - E1) / det), ⟨?_, ?_⟩, ?_⟩
  · simp only; field_simp; rw [hdd]; ring
  · simp only; field_simp; rw [hdd]; ring
  · rintro ⟨x, y⟩ ⟨hx1, hx2⟩
    simp only at hx1 hx2
    have hxd : x * det = l₂ * (E2 - F2) := by
      rw [hdd]; linear_combination (l₂ * F2) * hx1 - (l₂ * E2) * hx2
    have hyd : y * det = l₁ * (F1 - E1) := by
      rw [hdd]; linear_combination (-(l₁ * F1)) * hx1 + (l₁ * E1) * hx2
    simp only [Prod.mk.injEq]
    constructor
    · field_simp; linarith
    · field_simp; linarith

/-! ## Interest differentials in a band (§8.5.6, fn 60) -/

/-- O&R §8.5.6 and fn 60, p. 576: if the exchange-rate change `ℰ_{t+τ}/ℰ_t` lies in `[a, b]` in
every state, and there is no arbitrage between home and foreign bonds (no zero-cost position
with a strictly positive payoff in every state), then `(1+i)/(1+i*) ∈ [a, b]`, whatever the
preferences (risk aversion is irrelevant). -/
theorem band_interest_bounds {Ω : Type} [Nonempty Ω] (R : Ω → ℝ) {a b i istar : ℝ}
    (hR : ∀ ω, a ≤ R ω ∧ R ω ≤ b) (hi : 0 < 1 + istar)
    (noArb : ¬ ∃ x : ℝ, ∀ ω, 0 < x * ((1 + i) - (1 + istar) * R ω)) :
    a ≤ (1 + i) / (1 + istar) ∧ (1 + i) / (1 + istar) ≤ b := by
  constructor
  · by_contra h
    push Not at h
    rw [div_lt_iff₀ hi] at h
    exact noArb ⟨-1, fun ω => by nlinarith [(hR ω).1]⟩
  · by_contra h
    push Not at h
    rw [lt_div_iff₀ hi] at h
    exact noArb ⟨1, fun ω => by nlinarith [(hR ω).2]⟩

/-- O&R fn 60, p. 576: equivalently, with positive state prices `π` pricing both bonds
(`1/(1+i) = Σπ`, `1/(1+i*) = Σ π R`, prices in home currency per unit), the ratio
`(1+i)/(1+i*) = Σ πR/Σ π` is a weighted average of the possible changes. -/
theorem band_interest_state_prices {Ω : Type} [Fintype Ω] [Nonempty Ω] (R π : Ω → ℝ)
    {a b : ℝ} (hR : ∀ ω, a ≤ R ω ∧ R ω ≤ b) (hπ : ∀ ω, 0 < π ω) :
    a ≤ (∑ ω, π ω * R ω) / ∑ ω, π ω ∧ (∑ ω, π ω * R ω) / ∑ ω, π ω ≤ b := by
  have hS : 0 < ∑ ω, π ω := Finset.sum_pos (fun ω _ => hπ ω) Finset.univ_nonempty
  constructor
  · rw [le_div_iff₀ hS, Finset.mul_sum]
    exact Finset.sum_le_sum fun ω _ => by nlinarith [(hR ω).1, hπ ω]
  · rw [div_le_iff₀ hS, Finset.mul_sum]
    exact Finset.sum_le_sum fun ω _ => by nlinarith [(hR ω).2, hπ ω]

/-- O&R p. 576: a ±1% band allows a maximal change of about 2% (`1.01/0.99 ≈ 1.0202`); a 2%
change over six months is 4% per annum, and over one month 24% per annum. -/
theorem band_interest_numbers :
    ((1.0202 : ℝ) < 1.01 / 0.99 ∧ (1.01 : ℝ) / 0.99 < 1.0203) ∧
      (2 : ℝ) * (12 / 6) = 4 ∧ (2 : ℝ) * (12 / 1) = 24 := by
  norm_num

/-! ## The flag on (86): regulated increments -/

/-- O&R (86), p. 574 (flag): for a symmetric increment `dk` (an involution `σ` of the finite
state space preserving probabilities with `dk ∘ σ = −dk`), the regulated increment
`min(dk, 0)` has second moment `E(dk)²/2`, not `E(dk)² = hv²`. -/
theorem regulated_second_moment {Ω : Type} [Fintype Ω] (p X : Ω → ℝ) (σ : Ω → Ω)
    (hσ : Function.Involutive σ) (hp : ∀ ω, p (σ ω) = p ω) (hX : ∀ ω, X (σ ω) = -X ω) :
    ∑ ω, p ω * min (X ω) 0 ^ 2 = (∑ ω, p ω * X ω ^ 2) / 2 := by
  have hre : ∑ ω, p ω * min (X ω) 0 ^ 2 = ∑ ω, p ω * min (-X ω) 0 ^ 2 := by
    rw [← Equiv.sum_comp (hσ.toPerm σ)]
    exact Finset.sum_congr rfl fun ω _ => by
      simp only [Function.Involutive.coe_toPerm, hp, hX]
  have hpt : ∀ x : ℝ, min x 0 ^ 2 + min (-x) 0 ^ 2 = x ^ 2 := by
    intro x
    rcases le_total x 0 with h | h
    · rw [min_eq_left h, min_eq_right (by linarith)]; ring
    · rw [min_eq_right h, min_eq_left (by linarith)]; ring
  have : 2 * ∑ ω, p ω * min (X ω) 0 ^ 2 = ∑ ω, p ω * X ω ^ 2 := by
    rw [two_mul]
    nth_rewrite 2 [hre]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ω _ => by rw [← mul_add, hpt]
  linarith

/-- O&R (86), p. 574 (flag): the regulated increment has mean `E min(dk, 0) = −E|dk|/2 < 0`
(the `O(h^{1/2})` term that drives smooth pasting). -/
theorem regulated_mean {Ω : Type} [Fintype Ω] (p X : Ω → ℝ) (σ : Ω → Ω)
    (hσ : Function.Involutive σ) (hp : ∀ ω, p (σ ω) = p ω) (hX : ∀ ω, X (σ ω) = -X ω) :
    ∑ ω, p ω * min (X ω) 0 = -(∑ ω, p ω * |X ω|) / 2 := by
  have hre : ∑ ω, p ω * min (X ω) 0 = ∑ ω, p ω * min (-X ω) 0 := by
    rw [← Equiv.sum_comp (hσ.toPerm σ)]
    exact Finset.sum_congr rfl fun ω _ => by
      simp only [Function.Involutive.coe_toPerm, hp, hX]
  have hpt : ∀ x : ℝ, min x 0 + min (-x) 0 = -|x| := by
    intro x
    rcases le_total x 0 with h | h
    · rw [min_eq_left h, min_eq_right (by linarith), abs_of_nonpos h]; ring
    · rw [min_eq_right h, min_eq_left (by linarith), abs_of_nonneg h]; ring
  have : 2 * ∑ ω, p ω * min (X ω) 0 = -∑ ω, p ω * |X ω| := by
    rw [two_mul]
    nth_rewrite 2 [hre]
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun ω _ => by rw [← mul_add, hpt]; ring
  linarith

/-! ## Reserve exhaustion is inevitable (§8.6, p. 578) -/

/-- O&R p. 578, discrete version: the probability that the lattice fundamentals, started at
`i`, have **not** reached the ceiling `N` by date `n` (steps `±1` with probability ½, the
downward step at the floor `−N` suppressed). -/
noncomputable def notHitProb (N : ℕ) : ℕ → ℤ → ℝ
  | 0 => fun i => if i = N then 0 else 1
  | n + 1 => fun i => if i = N then 0 else
      (notHitProb N n (min (i + 1) N) + notHitProb N n (max (i - 1) (-N))) / 2

/-- O&R p. 578: `notHitProb` is a probability. -/
theorem notHitProb_mem (N : ℕ) (n : ℕ) (i : ℤ) :
    0 ≤ notHitProb N n i ∧ notHitProb N n i ≤ 1 := by
  induction n generalizing i with
  | zero => unfold notHitProb; split_ifs <;> norm_num
  | succ n ih =>
    unfold notHitProb
    split_ifs
    · norm_num
    · have := ih (min (i + 1) N); have := ih (max (i - 1) (-N))
      constructor <;> linarith

/-- O&R p. 578: the ceiling state itself has been hit. -/
theorem notHitProb_ceiling (N n : ℕ) : notHitProb N n N = 0 := by
  cases n <;> simp [notHitProb]

/-- O&R p. 578: the not-yet-hit probability is non-increasing in `n`. -/
theorem notHitProb_antitone (N : ℕ) (i : ℤ) : Antitone fun n => notHitProb N n i := by
  have e : ∀ n j, notHitProb N (n + 1) j = if j = N then 0 else
      (notHitProb N n (min (j + 1) N) + notHitProb N n (max (j - 1) (-N))) / 2 :=
    fun _ _ => rfl
  have step : ∀ n j, notHitProb N (n + 1) j ≤ notHitProb N n j := by
    intro n
    induction n with
    | zero =>
      intro j
      rw [e 0 j]
      simp only [notHitProb]
      split_ifs <;> norm_num
    | succ n ih =>
      intro j
      rw [e (n + 1) j, e n j]
      split_ifs
      · exact le_rfl
      · have := ih (min (j + 1) N); have := ih (max (j - 1) (-N))
        linarith
  exact antitone_nat_of_succ_le fun n => step n i

/-- O&R p. 578: the one-block estimate: if `q_n ≤ S` on the band, then after `m` more steps
`q ≤ S` on the band, and `q ≤ S(1 − 2^{−m})` from every state within `m` steps of the
ceiling (the all-up path has probability `2^{−m}`). -/
theorem notHitProb_block (N : ℕ) (n : ℕ) {S : ℝ} (hS : 0 ≤ S)
    (hb : ∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ N → notHitProb N n j ≤ S) (m : ℕ) :
    ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N → notHitProb N (n + m) i ≤ S ∧
      ((N : ℤ) - i ≤ m → notHitProb N (n + m) i ≤ S * (1 - (1 / 2) ^ m)) := by
  induction m with
  | zero =>
    intro i h1 h2
    refine ⟨hb i h1 h2, fun h => ?_⟩
    have : i = N := by omega
    rw [this, notHitProb_ceiling]; simp
  | succ m ih =>
    intro i h1 h2
    have hx : (0 : ℝ) ≤ (1 / 2) ^ (m + 1) := by positivity
    have hx1 : ((1 : ℝ) / 2) ^ (m + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    by_cases hi : i = N
    · rw [hi, notHitProb_ceiling]
      exact ⟨hS, fun _ => mul_nonneg hS (by linarith)⟩
    · have hup := ih (min (i + 1) N) (by omega) (by omega)
      have hdn := ih (max (i - 1) (-N)) (by omega) (by omega)
      have e : notHitProb N (n + (m + 1)) i =
          (notHitProb N (n + m) (min (i + 1) N) + notHitProb N (n + m) (max (i - 1) (-N))) /
            2 := by
        rw [show n + (m + 1) = (n + m) + 1 by ring]
        simp only [notHitProb, ite_eq_right hi]
      rw [e]
      refine ⟨by linarith [hup.1, hdn.1], fun hd => ?_⟩
      have hup' := hup.2 (by omega)
      rw [pow_succ]
      nlinarith [hdn.1]

/-- O&R p. 578: from every state of the band, the probability of not having reached the
ceiling after `k` blocks of `2N` steps is at most `(1 − 2^{−2N})^k`. -/
theorem notHitProb_blocks (N : ℕ) (k : ℕ) :
    ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N →
      notHitProb N (k * (2 * N)) i ≤ (1 - (1 / 2) ^ (2 * N)) ^ k := by
  have hc : (0 : ℝ) ≤ 1 - (1 / 2) ^ (2 * N) := by
    have : ((1 : ℝ) / 2) ^ (2 * N) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  induction k with
  | zero => intro i _ _; simpa using (notHitProb_mem N 0 i).2
  | succ k ih =>
    intro i h1 h2
    have := (notHitProb_block N (k * (2 * N)) (pow_nonneg hc k) ih (2 * N) i h1 h2).2
      (by push_cast; omega)
    rw [show (k + 1) * (2 * N) = k * (2 * N) + 2 * N by ring, pow_succ]
    exact this

/-- O&R p. 578 (**reserve exhaustion is inevitable**): with random-walk fundamentals and no
floor intervention on the upside, the ceiling is reached with probability one from every
state of the band: the not-yet-hit probability tends to zero. (Each visit to the ceiling
costs reserves, so with the chain restarting at the ceiling a finite stock is eventually
exhausted; the repeated-visit statement is the strong Markov property, not formalised.) -/
theorem ceiling_hit_almost_surely {N : ℕ} (hN : 0 < N) {i : ℤ} (h1 : -(N : ℤ) ≤ i)
    (h2 : i ≤ N) : Tendsto (fun n => notHitProb N n i) atTop (𝓝 0) := by
  set K := 2 * N with hK
  have hKpos : 0 < K := by omega
  set c : ℝ := 1 - (1 / 2) ^ K with hc
  have hc0 : 0 ≤ c := by
    have : ((1 : ℝ) / 2) ^ K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hc1 : c < 1 := by
    have : (0 : ℝ) < (1 / 2) ^ K := by positivity
    linarith
  have hdiv : Tendsto (fun n : ℕ => n / K) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨b * K, fun n hn => ?_⟩
    exact (Nat.le_div_iff_mul_le hKpos).2 hn
  have hup : Tendsto (fun n : ℕ => c ^ (n / K)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).comp hdiv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => (notHitProb_mem N n i).1) fun n => ?_
  have hle : (n / K) * K ≤ n := Nat.div_mul_le_self n K
  calc notHitProb N n i ≤ notHitProb N ((n / K) * K) i := notHitProb_antitone N i hle
    _ ≤ c ^ (n / K) := notHitProb_blocks N (n / K) i h1 h2

/-! ## The lattice equilibrium as the stochastic Cagan solution (80) -/

/-- O&R (80)–(81), pp. 570–571: the up-step on the band `{0, …, 2N}` (state `j` ↔
fundamentals `(j − N)Δ`), suppressed at the ceiling. -/
def bandUp (N : ℕ) (j : Fin (2 * N + 1)) : Fin (2 * N + 1) :=
  ⟨min (j.val + 1) (2 * N), by omega⟩

/-- O&R (80)–(81): the down-step on the band, suppressed at the floor. -/
def bandDown (N : ℕ) (j : Fin (2 * N + 1)) : Fin (2 * N + 1) :=
  ⟨j.val - 1, by omega⟩

/-- O&R (81), p. 571, discretised: the regulated random walk on the band as a Markov kernel
(`±Δ` with probability ½; the step out of the band is suppressed). -/
noncomputable def bandKernel (N : ℕ) : CaganModel.MarkovKernel (Fin (2 * N + 1)) where
  K j j' := (if j' = bandUp N j then 1 / 2 else 0) + (if j' = bandDown N j then 1 / 2 else 0)
  nonneg j j' := by split_ifs <;> norm_num
  rowSum j := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]; norm_num

/-- O&R (80): the conditional expectation under the regulated walk is the average of the up
and down states. -/
theorem bandKernel_apply (N : ℕ) (g : Fin (2 * N + 1) → ℝ) (j : Fin (2 * N + 1)) :
    CaganModel.kernelApply (bandKernel N) g j = (g (bandUp N j) + g (bandDown N j)) / 2 := by
  unfold CaganModel.kernelApply bandKernel
  simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring

/-- O&R (80), p. 570 (**identification**): the lattice target-zone equilibrium is exactly the
no-bubble solution of the stochastic Cagan equation (79) for the regulated fundamentals
process, i.e. CaganModel's `markovFundamental` with semielasticity `a = η/h` for the band
kernel. The reflecting boundary does not change the form of (80): the expectations in (80)
are simply taken under the regulated (intervention-adjusted) process. -/
theorem lattice_eq_markovFundamental {a Δ : ℝ} (ha : 0 < a) {N : ℕ} {e : ℤ → ℝ}
    (he : IsLatticeEqm a Δ N e) (j : Fin (2 * N + 1)) :
    CaganModel.markovFundamental a (bandKernel N) (fun j => ((j : ℤ) - N : ℝ) * Δ) j =
      e ((j : ℤ) - N) := by
  have hp : CaganModel.IsMarkovEqm a (bandKernel N) (fun j => ((j : ℤ) - N : ℝ) * Δ)
      (fun j => e ((j : ℤ) - N)) := by
    intro j
    rw [bandKernel_apply]
    have hj := j.isLt
    have h := he ((j : ℤ) - N) (by omega) (by omega)
    have hu : ((bandUp N j : ℕ) : ℤ) - N = min ((j : ℤ) - N + 1) N := by
      unfold bandUp; simp only; omega
    have hd : ((bandDown N j : ℕ) : ℤ) - N = max ((j : ℤ) - N - 1) (-N) := by
      unfold bandDown; simp only; omega
    simp only
    rw [hu, hd]
    push_cast at h ⊢
    unfold CaganModel.disc
    rw [div_mul_eq_mul_div, ← add_div, eq_div_iff (by linarith)]
    linear_combination h
  rw [← CaganModel.isMarkovEqm_unique ha (bandKernel N) hp]

/-- O&R (80), p. 570, in the book's form: with `a = η/h` the lattice equilibrium is
`e_t = (h/(h+η)) Σ_n (1 + h/η)^{−n} E_t k_{t+n}`, expectations under the regulated walk. -/
theorem lattice_eq_80 {η h Δ : ℝ} (hη : 0 < η) (hh : 0 < h) {N : ℕ} {e : ℤ → ℝ}
    (he : IsLatticeEqm (η / h) Δ N e) (j : Fin (2 * N + 1)) :
    e ((j : ℤ) - N) = h / (h + η) * ∑' n : ℕ, (1 + h / η)⁻¹ ^ n *
      CaganModel.kernelPow (bandKernel N) n (fun j => ((j : ℤ) - N : ℝ) * Δ) j := by
  rw [← lattice_eq_markovFundamental (div_pos hη hh) he j]
  unfold CaganModel.markovFundamental
  have e1 : CaganModel.disc (η / h) = (1 + h / η)⁻¹ := by
    unfold CaganModel.disc; field_simp; ring
  have e2 : 1 / (1 + η / h) = h / (h + η) := by field_simp
  rw [e1, e2]

/-! ## Repeated interventions: reserves are exhausted with probability one (p. 578) -/

/-- O&R p. 578, discrete version: `intervProb N n r i` is the probability that, starting from
state `i`, at most `r` ceiling interventions occur in the first `n` periods. At the ceiling an
attempted up-step (probability ½) is blocked by selling reserves (an intervention) and the
state stays at the ceiling; otherwise the walk moves `±1`, the down-step at the floor being
suppressed. -/
noncomputable def intervProb (N : ℕ) : ℕ → ℕ → ℤ → ℝ
  | 0 => fun _ _ => 1
  | n + 1 => fun r i =>
      if i = N then
        ((if r = 0 then 0 else intervProb N n (r - 1) N) + intervProb N n r (N - 1)) / 2
      else (intervProb N n r (min (i + 1) N) + intervProb N n r (max (i - 1) (-N))) / 2

/-- O&R p. 578: the one-step recursion for `intervProb`. -/
theorem intervProb_succ (N n r : ℕ) (i : ℤ) :
    intervProb N (n + 1) r i =
      if i = N then
        ((if r = 0 then 0 else intervProb N n (r - 1) N) + intervProb N n r (N - 1)) / 2
      else (intervProb N n r (min (i + 1) N) + intervProb N n r (max (i - 1) (-N))) / 2 :=
  rfl

/-- O&R p. 578: `intervProb` is a probability. -/
theorem intervProb_mem (N n r : ℕ) (i : ℤ) :
    0 ≤ intervProb N n r i ∧ intervProb N n r i ≤ 1 := by
  induction n generalizing r i with
  | zero => simp [intervProb]
  | succ n ih =>
    rw [intervProb_succ]
    split_ifs with h1 h2
    · have := ih r (N - 1); constructor <;> linarith
    · have := ih (r - 1) N; have := ih r (N - 1); constructor <;> linarith
    · have := ih r (min (i + 1) N); have := ih r (max (i - 1) (-N))
      constructor <;> linarith

/-- O&R p. 578: allowing more interventions makes the event more likely (monotone in `r`). -/
theorem intervProb_mono_r (N n r : ℕ) (i : ℤ) :
    intervProb N n r i ≤ intervProb N n (r + 1) i := by
  induction n generalizing r i with
  | zero => simp [intervProb]
  | succ n ih =>
    rw [intervProb_succ N n r i, intervProb_succ N n (r + 1) i]
    by_cases hi : i = N
    · rw [ite_eq_left hi, ite_eq_left hi, ite_eq_right (Nat.succ_ne_zero r), Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr
        rw [ite_eq_left rfl]
        have := (intervProb_mem N n 0 N).1; have := ih 0 (N - 1); linarith
      · rw [ite_eq_right (by omega)]
        have h5 := ih (r - 1) N
        rw [Nat.sub_add_cancel hr] at h5
        have := ih r (N - 1); linarith
    · rw [ite_eq_right hi, ite_eq_right hi]
      have := ih r (min (i + 1) N); have := ih r (max (i - 1) (-N)); linarith

/-- O&R p. 578: more time makes the event less likely (antitone in `n`). -/
theorem intervProb_antitone (N r : ℕ) (i : ℤ) : Antitone fun n => intervProb N n r i := by
  have step : ∀ n r j, intervProb N (n + 1) r j ≤ intervProb N n r j := by
    intro n
    induction n with
    | zero =>
      intro r j
      rw [show intervProb N 0 r j = 1 from rfl]; exact (intervProb_mem N 1 r j).2
    | succ n ih =>
      intro r j
      rw [intervProb_succ N (n + 1) r j, intervProb_succ N n r j]
      by_cases hj : j = N
      · rw [ite_eq_left hj, ite_eq_left hj]
        by_cases hr : r = 0
        · rw [ite_eq_left hr, ite_eq_left hr]; have := ih r (N - 1); linarith
        · rw [ite_eq_right hr, ite_eq_right hr]
          have := ih (r - 1) N; have := ih r (N - 1); linarith
      · rw [ite_eq_right hj, ite_eq_right hj]
        have := ih r (min (j + 1) N); have := ih r (max (j - 1) (-N)); linarith
  exact antitone_nat_of_succ_le fun n => step n r i

/-- O&R p. 578: a bound on the band is preserved over time. -/
theorem intervProb_bound (N : ℕ) (hN : 1 ≤ N) (n r : ℕ) {S : ℝ}
    (hb : ∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ N → intervProb N n r j ≤ S) (m : ℕ) :
    ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N → intervProb N (n + m) r i ≤ S := by
  induction m with
  | zero => exact hb
  | succ m ih =>
    intro i h1 h2
    rw [show n + (m + 1) = (n + m) + 1 by ring, intervProb_succ]
    split_ifs with h3 h4
    · have := ih (N - 1) (by omega) (by omega)
      have := (intervProb_mem N (n + m) r N).1 |>.trans (ih N (by omega) le_rfl)
      linarith
    · have h5 := intervProb_mono_r N (n + m) (r - 1) N
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h4)] at h5
      have := ih N (by omega) le_rfl; have := ih (N - 1) (by omega) (by omega)
      linarith
    · have := ih (min (i + 1) N) (by omega) (by omega)
      have := ih (max (i - 1) (-N)) (by omega) (by omega)
      linarith

/-- O&R p. 578: the block estimate: if on the band `intervProb n r ≤ S` and
`intervProb n (r−1) ≤ S′` (with `S′ = 0`-bound when `r = 0`), then from any state within
`m` steps of an intervention (`N − i + 1 ≤ m`), after `m` more periods
`intervProb ≤ S − 2^{−m}(S − S′)`: the path running straight up and intervening has
probability `2^{−m}`. -/
theorem intervProb_block (N : ℕ) (hN : 1 ≤ N) (n r : ℕ) {S S' : ℝ} (hS' : 0 ≤ S')
    (hSS : S' ≤ S) (hb : ∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ N → intervProb N n r j ≤ S)
    (hb' : ∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ N → r ≠ 0 → intervProb N n (r - 1) j ≤ S') (m : ℕ) :
    ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N → (N : ℤ) - i + 1 ≤ m →
      intervProb N (n + m) r i ≤ S - (1 / 2) ^ m * (S - S') := by
  induction m with
  | zero => intro i _ h2 h3; push_cast at h3; omega
  | succ m ih =>
    intro i h1 h2 h3
    rw [show n + (m + 1) = (n + m) + 1 by ring, intervProb_succ]
    have hx : ((1 : ℝ) / 2) ^ (m + 1) ≤ 1 / 2 := by
      rw [pow_succ]; have : ((1 : ℝ) / 2) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have hS0 : 0 ≤ S - S' := by linarith
    split_ifs with h4 h5
    · -- at the ceiling with no interventions allowed
      have := intervProb_bound N hN n r hb m (N - 1) (by omega) (by omega)
      nlinarith
    · -- at the ceiling: intervene (prob ½) or step down
      have e1 := intervProb_bound N hN n (r - 1) (fun j h1 h2 => hb' j h1 h2 h5) m N
        (by omega) le_rfl
      have e2 := intervProb_bound N hN n r hb m (N - 1) (by omega) (by omega)
      nlinarith
    · -- below the ceiling: step up (prob ½)
      have hi : i < N := lt_of_le_of_ne h2 h4
      have e1 := ih (i + 1) (by omega) (by omega) (by push_cast at h3 ⊢; omega)
      rw [min_eq_left (by omega)]
      have e2 := intervProb_bound N hN n r hb m (max (i - 1) (-N)) (by omega) (by omega)
      rw [pow_succ]
      nlinarith

/-- O&R p. 578: the explicit bound `U_k(r) = (k+1)^r (1−c)^k/(1−c)^r` used for block `k`. -/
noncomputable def intervBound (c : ℝ) (k r : ℕ) : ℝ := ((k : ℝ) + 1) ^ r * (1 - c) ^ k / (1 - c) ^ r

/-- O&R p. 578: after `k` blocks of `L = 2N + 1` periods, the probability of at most `r`
interventions is at most `U_k(r)` with `c = 2^{−L}`. -/
theorem intervProb_blocks (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    ∀ r : ℕ, ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N →
      intervProb N (k * (2 * N + 1)) r i ≤ intervBound ((1 / 2) ^ (2 * N + 1)) k r := by
  set c : ℝ := (1 / 2) ^ (2 * N + 1) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have h1c : 0 < 1 - c := by linarith
  have hU0 : ∀ k r, 0 ≤ intervBound c k r := fun k r => by unfold intervBound; positivity
  have hUmono : ∀ k r, intervBound c k r ≤ intervBound c k (r + 1) := by
    intro k r
    unfold intervBound
    rw [pow_succ, pow_succ, div_le_div_iff₀ (by positivity) (by positivity)]
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
    have hp : 0 ≤ ((k : ℝ) + 1) ^ r * (1 - c) ^ k * (1 - c) ^ r := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (show 1 - c ≤ (k : ℝ) + 1 by linarith) hp]
  induction k with
  | zero =>
    intro r i _ _
    simp only [zero_mul, intervProb, intervBound, Nat.cast_zero, zero_add, one_pow, pow_zero,
      one_mul]
    rw [le_div_iff₀ (by positivity), one_mul]
    exact pow_le_one₀ h1c.le (by linarith)
  | succ k ih =>
    intro r i h1 h2
    have hbl := intervProb_block N hN (k * (2 * N + 1)) r
      (S := intervBound c k r) (S' := if r = 0 then 0 else intervBound c k (r - 1))
      (by split_ifs <;> [exact le_rfl; exact hU0 k (r - 1)])
      (by split_ifs with h
          · exact hU0 k r
          · have := hUmono k (r - 1); rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h)]
                at this)
      (ih r) (fun j h1 h2 hr => by rw [ite_eq_right hr]; exact ih (r - 1) j h1 h2)
      (2 * N + 1) i h1 h2
      (by push_cast; omega)
    rw [show (k + 1) * (2 * N + 1) = k * (2 * N + 1) + (2 * N + 1) by ring]
    refine hbl.trans ?_
    rw [← hc]
    have hcomb : intervBound c k r - c * (intervBound c k r -
        (if r = 0 then 0 else intervBound c k (r - 1))) ≤ intervBound c (k + 1) r := by
      split_ifs with hr
      · subst hr; unfold intervBound; simp only [pow_zero, div_one, one_mul]
        rw [pow_succ]; ring_nf; exact le_rfl
      · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        unfold intervBound
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hpow : ((k : ℝ) + 1) ^ (r' + 1) + ((k : ℝ) + 1) ^ r' ≤
            ((k : ℝ) + 1 + 1) ^ (r' + 1) := by
          have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)
            (show (k : ℝ) + 1 ≤ (k : ℝ) + 1 + 1 by linarith) r'
          rw [pow_succ, pow_succ ((k : ℝ) + 1 + 1)]
          nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1) r']
        have hx : 0 < (1 - c) ^ (r' + 1) := by positivity
        push_cast
        rw [show ((k : ℝ) + 1 + 1) = ((k + 1 : ℕ) : ℝ) + 1 by push_cast; ring] at hpow
        push_cast at hpow
        have e : ((k : ℝ) + 1) ^ (r' + 1) * (1 - c) ^ k / (1 - c) ^ (r' + 1) -
            c * (((k : ℝ) + 1) ^ (r' + 1) * (1 - c) ^ k / (1 - c) ^ (r' + 1) -
              ((k : ℝ) + 1) ^ r' * (1 - c) ^ k / (1 - c) ^ r') =
            (1 - c) ^ (k + 1) / (1 - c) ^ (r' + 1) *
              (((k : ℝ) + 1) ^ (r' + 1) + c * ((k : ℝ) + 1) ^ r') := by
          field_simp; ring
        rw [e, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hx]
        have hc' : c * ((k : ℝ) + 1) ^ r' ≤ ((k : ℝ) + 1) ^ r' :=
          mul_le_of_le_one_left (by positivity) hc1.le
        have : 0 ≤ (1 - c) ^ (k + 1) := by positivity
        nlinarith
    exact hcomb

/-- O&R p. 578 (**repeated visits**): on the finite lattice, for every `r` the probability of
at most `r` ceiling interventions in the first `n` periods tends to zero: interventions occur
infinitely often with probability one. -/
theorem interventions_infinitely_often {N : ℕ} (hN : 1 ≤ N) (r : ℕ) {i : ℤ}
    (h1 : -(N : ℤ) ≤ i) (h2 : i ≤ N) : Tendsto (fun n => intervProb N n r i) atTop (𝓝 0) := by
  set L := 2 * N + 1 with hL
  set c : ℝ := (1 / 2) ^ L with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hLpos : 0 < L := by omega
  have hdiv : Tendsto (fun n : ℕ => n / L) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b * L, fun n hn => (Nat.le_div_iff_mul_le hLpos).2 hn⟩
  have hU : Tendsto (fun k : ℕ => intervBound c k r) atTop (𝓝 0) := by
    have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one r
      (show |1 - c| < 1 by rw [abs_of_pos (by linarith)]; linarith)).comp
      (tendsto_add_atTop_nat 1)
    have h' := h.div_const ((1 - c) ^ (r + 1))
    rw [zero_div] at h'
    refine h'.congr fun k => ?_
    unfold intervBound
    simp only [Function.comp]
    push_cast
    have : (0 : ℝ) < 1 - c := by linarith
    field_simp
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hU.comp hdiv)
    (fun n => (intervProb_mem N n r i).1) fun n => ?_
  calc intervProb N n r i ≤ intervProb N ((n / L) * L) r i :=
        intervProb_antitone N r i (Nat.div_mul_le_self n L)
    _ ≤ intervBound c (n / L) r := intervProb_blocks N hN (n / L) r i h1 h2

/-- O&R p. 578 (**any finite reserve stock is exhausted**): if each intervention costs at least
`c₀ > 0` of reserves and the stock is `R`, the probability that the stock survives the first
`n` periods (at most `⌊R/c₀⌋` interventions) tends to zero. -/
theorem reserves_exhausted_almost_surely {N : ℕ} (hN : 1 ≤ N) (R c₀ : ℝ) {i : ℤ}
    (h1 : -(N : ℤ) ≤ i) (h2 : i ≤ N) :
    Tendsto (fun n => intervProb N n ⌊R / c₀⌋₊ i) atTop (𝓝 0) :=
  interventions_infinitely_often hN _ h1 h2

/-! ## Exercise 5: the full band solution with drift -/

/-- O&R Exercise 5, p. 601: the currency-band width generated by a fundamentals band of width
`L` when the locus pastes smoothly at both edges (`α = λ₁ > 0`, `β = −λ₂ > 0`):
`W(L) = L − (1/α + 1/β)(e^{αL} − 1)(e^{βL} − 1)/(e^{αL}e^{βL} − 1)`. -/
noncomputable def bandWidth (α β L : ℝ) : ℝ :=
  L - (1 / α + 1 / β) * ((Real.exp (α * L) - 1) * (Real.exp (β * L) - 1) /
    (Real.exp (α * L) * Real.exp (β * L) - 1))

/-- Two elementary exponential inequalities used for O&R Exercise 5: for `x > 0`,
`x < e^x − 1 < x e^x`. -/
theorem exp_sub_one_bounds {x : ℝ} (hx : 0 < x) :
    x < Real.exp x - 1 ∧ Real.exp x - 1 < x * Real.exp x := by
  constructor
  · linarith [Real.add_one_lt_exp hx.ne']
  · have h := Real.add_one_lt_exp (show -x ≠ 0 by linarith)
    have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos x
    nlinarith

/-- O&R Exercise 5: the width function has derivative
`W′(L) = 1 − (1/α + 1/β)(αA(B−1)² + βB(A−1)²)/(AB − 1)²` (`A = e^{αL}`, `B = e^{βL}`). -/
theorem hasDerivAt_bandWidth {α β L : ℝ} (hα : 0 < α) (hβ : 0 < β) (hL : 0 < L) :
    HasDerivAt (bandWidth α β) (1 - (1 / α + 1 / β) *
      ((α * Real.exp (α * L) * (Real.exp (β * L) - 1) ^ 2 +
        β * Real.exp (β * L) * (Real.exp (α * L) - 1) ^ 2) /
        (Real.exp (α * L) * Real.exp (β * L) - 1) ^ 2)) L := by
  set A := Real.exp (α * L) with hAdef
  set B := Real.exp (β * L) with hBdef
  have hA : HasDerivAt (fun x => Real.exp (α * x)) (A * α) L := by
    simpa using ((hasDerivAt_id' L).const_mul α).exp
  have hB : HasDerivAt (fun x => Real.exp (β * x)) (B * β) L := by
    simpa using ((hasDerivAt_id' L).const_mul β).exp
  have hA1 : 1 < A := Real.one_lt_exp_iff.2 (by positivity)
  have hB1 : 1 < B := Real.one_lt_exp_iff.2 (by positivity)
  have hD : A * B - 1 ≠ 0 := by nlinarith
  have hN := (hA.sub_const 1).mul (hB.sub_const 1)
  have hDd := (hA.mul hB).sub_const 1
  have hq := hN.div hDd hD
  have := (hasDerivAt_id' L).sub (hq.const_mul (1 / α + 1 / β))
  unfold bandWidth
  convert this using 1
  simp only [Pi.mul_apply, ← hAdef, ← hBdef]
  rw [show ((A * α) * (B - 1) + (A - 1) * (B * β)) * (A * B - 1) -
      (A - 1) * (B - 1) * (A * α * B + A * (B * β)) = α * A * (B - 1) ^ 2 + β * B * (A - 1) ^ 2
      by ring]

/-- O&R Exercise 5 (key inequality): the width is strictly increasing: `W′(L) > 0` for `L > 0`.
(Proof: `αβ(AB−1)² − (α+β)(αA(B−1)² + βB(A−1)²) = (βB(A−1) − α(B−1))(αA(B−1) − β(A−1))`, and
both factors are positive by `x < e^x − 1 < xe^x`.) -/
theorem bandWidth_deriv_pos {α β L : ℝ} (hα : 0 < α) (hβ : 0 < β) (hL : 0 < L) :
    0 < 1 - (1 / α + 1 / β) *
      ((α * Real.exp (α * L) * (Real.exp (β * L) - 1) ^ 2 +
        β * Real.exp (β * L) * (Real.exp (α * L) - 1) ^ 2) /
        (Real.exp (α * L) * Real.exp (β * L) - 1) ^ 2) := by
  set A := Real.exp (α * L) with hAdef
  set B := Real.exp (β * L) with hBdef
  obtain ⟨hs1, hs2⟩ := exp_sub_one_bounds (show 0 < α * L by positivity)
  obtain ⟨ht1, ht2⟩ := exp_sub_one_bounds (show 0 < β * L by positivity)
  rw [← hAdef] at hs1 hs2; rw [← hBdef] at ht1 ht2
  have hA1 : 1 < A := by nlinarith
  have hB1 : 1 < B := by nlinarith
  have hDpos : 0 < (A * B - 1) ^ 2 := by
    have : 0 < A * B - 1 := by nlinarith
    positivity
  -- the two factors, scaled by `L`
  have f1 : 0 < β * B * (A - 1) - α * (B - 1) := by
    have : 0 < L * (β * B * (A - 1) - α * (B - 1)) := by nlinarith
    exact pos_of_mul_pos_right this hL.le
  have f2 : 0 < α * A * (B - 1) - β * (A - 1) := by
    have : 0 < L * (α * A * (B - 1) - β * (A - 1)) := by nlinarith
    exact pos_of_mul_pos_right this hL.le
  have key : α * β * (A * B - 1) ^ 2 - (α + β) * (α * A * (B - 1) ^ 2 + β * B * (A - 1) ^ 2) =
      (β * B * (A - 1) - α * (B - 1)) * (α * A * (B - 1) - β * (A - 1)) := by ring
  have hlt : (α + β) * (α * A * (B - 1) ^ 2 + β * B * (A - 1) ^ 2) <
      α * β * (A * B - 1) ^ 2 := by nlinarith [mul_pos f1 f2]
  rw [sub_pos, show 1 / α + 1 / β = (α + β) / (α * β) by field_simp; ring, div_mul_div_comm,
    div_lt_one (by positivity)]
  exact hlt

/-- O&R Exercise 5: the width is continuous on `(0, ∞)`. -/
theorem continuousOn_bandWidth {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ContinuousOn (bandWidth α β) (Ioi 0) :=
  fun _ hL => (hasDerivAt_bandWidth hα hβ hL).continuousAt.continuousWithinAt

/-- O&R Exercise 5: `W` is strictly increasing on `(0, ∞)`. -/
theorem bandWidth_strictMonoOn {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    StrictMonoOn (bandWidth α β) (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) (continuousOn_bandWidth hα hβ) fun L hL => ?_
  rw [interior_Ioi] at hL
  rw [(hasDerivAt_bandWidth hα hβ hL).deriv]
  exact bandWidth_deriv_pos hα hβ hL

/-- O&R Exercise 5: bounds `L − (1/α + 1/β)(e^{αL} − 1) ≤ W(L)` and
`L − (1/α + 1/β) < W(L) < L` for `L > 0`. -/
theorem bandWidth_bounds {α β L : ℝ} (hα : 0 < α) (hβ : 0 < β) (hL : 0 < L) :
    L - (1 / α + 1 / β) * (Real.exp (α * L) - 1) ≤ bandWidth α β L ∧
      L - (1 / α + 1 / β) < bandWidth α β L ∧ bandWidth α β L < L := by
  set A := Real.exp (α * L); set B := Real.exp (β * L)
  have hA1 : 1 < A := Real.one_lt_exp_iff.2 (by positivity)
  have hB1 : 1 < B := Real.one_lt_exp_iff.2 (by positivity)
  have hD : 0 < A * B - 1 := by nlinarith
  have hk : 0 < 1 / α + 1 / β := by positivity
  have hP0 : 0 < (A - 1) * (B - 1) / (A * B - 1) := by
    apply div_pos _ hD; nlinarith
  have hP1 : (A - 1) * (B - 1) / (A * B - 1) < 1 := by
    rw [div_lt_one hD]; nlinarith
  have hP2 : (A - 1) * (B - 1) / (A * B - 1) ≤ A - 1 := by
    rw [div_le_iff₀ hD]
    nlinarith [mul_le_mul_of_nonneg_left (show B - 1 ≤ A * B - 1 by nlinarith)
      (show 0 ≤ A - 1 by linarith)]
  unfold bandWidth
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hP2 hk.le]
  · nlinarith [mul_lt_mul_of_pos_left hP1 hk]
  · nlinarith [mul_pos hk hP0]

/-- O&R Exercise 5: `W(L) → 0` as `L → 0⁺`. -/
theorem bandWidth_tendsto_zero {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (bandWidth α β) (𝓝[>] 0) (𝓝 0) := by
  have hlow : Tendsto (fun L => L - (1 / α + 1 / β) * (Real.exp (α * L) - 1)) (𝓝[>] 0)
      (𝓝 0) := by
    have : Tendsto (fun L => L - (1 / α + 1 / β) * (Real.exp (α * L) - 1)) (𝓝 0)
        (𝓝 (0 - (1 / α + 1 / β) * (Real.exp (α * 0) - 1))) :=
      ((continuous_id.sub (continuous_const.mul
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub
          continuous_const)))).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hup : Tendsto (fun L : ℝ => L) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with L hL using (bandWidth_bounds hα hβ hL).1
  · filter_upwards [self_mem_nhdsWithin] with L hL using (bandWidth_bounds hα hβ hL).2.2.le

/-- O&R Exercise 5: every positive currency-band width is generated by exactly one
fundamentals-band width `L > 0`. -/
theorem bandWidth_existsUnique {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {w : ℝ} (hw : 0 < w) :
    ∃! L : ℝ, 0 < L ∧ bandWidth α β L = w := by
  obtain ⟨δ, hδ, hδw⟩ : ∃ δ, 0 < δ ∧ bandWidth α β δ < w := by
    have := (bandWidth_tendsto_zero hα hβ).eventually (gt_mem_nhds hw)
    obtain ⟨δ, hδ⟩ := (this.and self_mem_nhdsWithin).exists
    exact ⟨δ, hδ.2, hδ.1⟩
  set M := max δ (w + (1 / α + 1 / β)) with hM
  have hMpos : 0 < M := lt_of_lt_of_le hδ (le_max_left _ _)
  have hMw : w ≤ bandWidth α β M := by
    have := (bandWidth_bounds hα hβ hMpos).2.1
    have : w + (1 / α + 1 / β) ≤ M := le_max_right _ _
    linarith
  obtain ⟨L, hL, hval⟩ := intermediate_value_Icc (le_max_left δ _)
    ((continuousOn_bandWidth hα hβ).mono fun x hx => lt_of_lt_of_le hδ hx.1) ⟨hδw.le, hMw⟩
  have hL0 : 0 < L := lt_of_lt_of_le hδ hL.1
  exact ⟨L, ⟨hL0, hval⟩, fun y hy => (bandWidth_strictMonoOn hα hβ).injOn hy.1 hL0
    (hy.2.trans hval.symm)⟩

/-- O&R Exercise 5: the four band conditions: value matching `G(k̲) = e̲`, `G(k̄) = ē` and smooth
pasting `G′(k̲) = G′(k̄) = 0`, for `G(k) = ημ + k + b₁e^{λ₁k} + b₂e^{λ₂k}`. -/
def IsDriftBand (d l₁ l₂ elo ehi b₁ b₂ kl kh : ℝ) : Prop :=
  kl < kh ∧ zoneSolution d b₁ b₂ l₁ l₂ kl = elo ∧ zoneSolution d b₁ b₂ l₁ l₂ kh = ehi ∧
    1 + l₁ * b₁ * Real.exp (l₁ * kl) + l₂ * b₂ * Real.exp (l₂ * kl) = 0 ∧
    1 + l₁ * b₁ * Real.exp (l₁ * kh) + l₂ * b₂ * Real.exp (l₂ * kh) = 0

/-- O&R Exercise 5: under smooth pasting at both edges, `X = b₁e^{λ₁k̲}` and `Y = b₂e^{λ₂k̲}`
are determined by the band width: `αX = (1 − B)/(AB − 1)`, `βY = (A − 1)B/(AB − 1)`. -/
theorem drift_band_XY {α β L X Y : ℝ} (hα : 0 < α) (hβ : 0 < β) (hL : 0 < L)
    (h1 : 1 + α * X + -β * Y = 0)
    (h2 : 1 + α * X * Real.exp (α * L) + -β * Y * (Real.exp (β * L))⁻¹ = 0) :
    X = (1 - Real.exp (β * L)) / (α * (Real.exp (α * L) * Real.exp (β * L) - 1)) ∧
      Y = (Real.exp (α * L) - 1) * Real.exp (β * L) /
        (β * (Real.exp (α * L) * Real.exp (β * L) - 1)) := by
  set A := Real.exp (α * L); set B := Real.exp (β * L)
  have hA1 : 1 < A := Real.one_lt_exp_iff.2 (by positivity)
  have hB1 : 1 < B := Real.one_lt_exp_iff.2 (by positivity)
  have hD : 0 < A * B - 1 := by nlinarith
  have hB0 : B ≠ 0 := by positivity
  have hBB : B * B⁻¹ = 1 := mul_inv_cancel₀ hB0
  have h2' : B + α * X * A * B - β * Y = 0 := by linear_combination B * h2 + β * Y * hBB
  have hY : β * Y * (A * B - 1) = (A - 1) * B := by linear_combination h2' - A * B * h1
  have hX : α * X * (A * B - 1) = 1 - B := by linear_combination h2' - h1
  constructor
  · rw [eq_div_iff (by positivity)]; linear_combination hX
  · rw [eq_div_iff (by positivity)]; linear_combination hY

/-- O&R Exercise 5: with smooth pasting at both edges, the currency band is
`G(k̄) − G(k̲) = W(k̄ − k̲)`. -/
theorem drift_band_width {α β L X Y : ℝ} (hα : 0 < α) (hβ : 0 < β) (hL : 0 < L)
    (h1 : 1 + α * X + -β * Y = 0)
    (h2 : 1 + α * X * Real.exp (α * L) + -β * Y * (Real.exp (β * L))⁻¹ = 0) :
    L + X * (Real.exp (α * L) - 1) + Y * ((Real.exp (β * L))⁻¹ - 1) = bandWidth α β L := by
  obtain ⟨hX, hY⟩ := drift_band_XY hα hβ hL h1 h2
  have hA1 : 1 < Real.exp (α * L) := Real.one_lt_exp_iff.2 (by positivity)
  have hB1 : 1 < Real.exp (β * L) := Real.one_lt_exp_iff.2 (by positivity)
  have hD : Real.exp (α * L) * Real.exp (β * L) - 1 ≠ 0 := by nlinarith
  rw [hX, hY]
  unfold bandWidth
  field_simp
  ring

/-- O&R Exercise 5: the pasting constant `X = b₁e^{λ₁k̲}` as a function of the band width. -/
noncomputable def driftX (α β L : ℝ) : ℝ :=
  (1 - Real.exp (β * L)) / (α * (Real.exp (α * L) * Real.exp (β * L) - 1))

/-- O&R Exercise 5: the pasting constant `Y = b₂e^{λ₂k̲}` as a function of the band width. -/
noncomputable def driftY (α β L : ℝ) : ℝ :=
  (Real.exp (α * L) - 1) * Real.exp (β * L) / (β * (Real.exp (α * L) * Real.exp (β * L) - 1))

/-- O&R Exercise 5: the explicit pasting constants satisfy both smooth-pasting conditions. -/
theorem driftXY_paste {α β L : ℝ} (hα : 0 < α) (hβ : 0 < β) (hL : 0 < L) :
    1 + α * driftX α β L + -β * driftY α β L = 0 ∧
      1 + α * driftX α β L * Real.exp (α * L) + -β * driftY α β L * (Real.exp (β * L))⁻¹ =
        0 := by
  have hA1 : 1 < Real.exp (α * L) := Real.one_lt_exp_iff.2 (by positivity)
  have hB1 : 1 < Real.exp (β * L) := Real.one_lt_exp_iff.2 (by positivity)
  have hD : Real.exp (α * L) * Real.exp (β * L) - 1 ≠ 0 := by nlinarith
  have hB0 : Real.exp (β * L) ≠ 0 := by positivity
  unfold driftX driftY
  generalize Real.exp (α * L) = A at hA1 hD ⊢
  generalize Real.exp (β * L) = B at hB1 hD hB0 ⊢
  have e1 : α * ((1 - B) / (α * (A * B - 1))) = (1 - B) / (A * B - 1) := by
    rw [mul_div_assoc', mul_div_mul_left _ _ hα.ne']
  have e2 : -β * ((A - 1) * B / (β * (A * B - 1))) = -((A - 1) * B / (A * B - 1)) := by
    rw [neg_mul, mul_div_assoc', mul_div_mul_left _ _ hβ.ne']
  rw [e1, e2]
  have hI := mul_inv_cancel₀ hD
  have hb := mul_inv_cancel₀ hB0
  constructor
  · rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination -hI
  · rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination -hI - (A - 1) * (A * B - 1)⁻¹ * hb

/-- O&R Exercise 5: any solution of the four band conditions has fundamentals width `L` with
`W(L) = ē − e̲`, pasting constants `driftX`, `driftY` and lower edge `k̲ = e̲ − ημ − X − Y`. -/
theorem driftBand_characterisation {d l₁ l₂ elo ehi b₁ b₂ kl kh : ℝ} (hl₁ : 0 < l₁)
    (hl₂ : l₂ < 0) (h : IsDriftBand d l₁ l₂ elo ehi b₁ b₂ kl kh) :
    bandWidth l₁ (-l₂) (kh - kl) = ehi - elo ∧
      b₁ * Real.exp (l₁ * kl) = driftX l₁ (-l₂) (kh - kl) ∧
      b₂ * Real.exp (l₂ * kl) = driftY l₁ (-l₂) (kh - kl) ∧
      kl = elo - d - driftX l₁ (-l₂) (kh - kl) - driftY l₁ (-l₂) (kh - kl) := by
  obtain ⟨hk, hlo, hhi, hp1, hp2⟩ := h
  set L := kh - kl with hLdef
  have hL : 0 < L := by linarith
  have hβ : 0 < -l₂ := by linarith
  set X := b₁ * Real.exp (l₁ * kl)
  set Y := b₂ * Real.exp (l₂ * kl)
  have e1 : Real.exp (l₁ * kh) = Real.exp (l₁ * kl) * Real.exp (l₁ * L) := by
    rw [← Real.exp_add]; congr 1; rw [hLdef]; ring
  have e2 : Real.exp (l₂ * kh) = Real.exp (l₂ * kl) * (Real.exp (-l₂ * L))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; congr 1; rw [hLdef]; ring
  have h1 : 1 + l₁ * X + -(-l₂) * Y = 0 := by rw [neg_neg]; linear_combination hp1
  have h2 : 1 + l₁ * X * Real.exp (l₁ * L) + -(-l₂) * Y * (Real.exp (-l₂ * L))⁻¹ = 0 := by
    rw [neg_neg]; rw [e1, e2] at hp2; linear_combination hp2
  have hw := drift_band_width hl₁ hβ hL h1 h2
  obtain ⟨hX, hY⟩ := drift_band_XY hl₁ hβ hL h1 h2
  have hwidth : ehi - elo = L + X * (Real.exp (l₁ * L) - 1) +
      Y * ((Real.exp (-l₂ * L))⁻¹ - 1) := by
    unfold zoneSolution at hlo hhi
    rw [e1, e2] at hhi
    have : kh = kl + L := by rw [hLdef]; ring
    rw [this] at hhi
    linear_combination hlo - hhi
  refine ⟨by rw [← hw, hwidth], hX, hY, ?_⟩
  unfold zoneSolution at hlo
  have : kl = elo - d - X - Y := by linarith
  rw [this, hX, hY]; rfl

/-- O&R Exercise 5, p. 601 (**the full band solution with drift**): for any drift and any
prescribed currency band `e̲ < ē`, there is exactly one quadruple `(b₁, b₂, k̲, k̄)` satisfying
value matching and smooth pasting at both edges (`λ₁ > 0 > λ₂` the characteristic roots).
The proof reduces the 4×4 system by translation invariance to the one equation
`W(k̄ − k̲) = ē − e̲` for the width, which has a unique root since `W` rises strictly from `0`
to `∞`. -/
theorem driftBand_existsUnique {d l₁ l₂ elo ehi : ℝ} (hl₁ : 0 < l₁) (hl₂ : l₂ < 0)
    (hband : elo < ehi) :
    ∃! q : ℝ × ℝ × ℝ × ℝ, IsDriftBand d l₁ l₂ elo ehi q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have hβ : 0 < -l₂ := by linarith
  obtain ⟨L, ⟨hL, hWL⟩, hLu⟩ := bandWidth_existsUnique hl₁ hβ (sub_pos.2 hband)
  obtain ⟨hp1, hp2⟩ := driftXY_paste hl₁ hβ hL
  generalize hX : driftX l₁ (-l₂) L = X at hp1 hp2
  generalize hY : driftY l₁ (-l₂) L = Y at hp1 hp2
  have hw := drift_band_width hl₁ hβ hL hp1 hp2
  obtain ⟨kl, hkl⟩ : ∃ kl, kl = elo - d - X - Y := ⟨_, rfl⟩
  have ex1 : ∀ c x, Real.exp (-c * x) * Real.exp (c * x) = 1 := fun c x => by
    rw [← Real.exp_add]; simp
  have hEneg : Real.exp (l₂ * L) = (Real.exp (-l₂ * L))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have hX' : X * Real.exp (-l₁ * kl) * Real.exp (l₁ * kl) = X := by rw [mul_assoc, ex1, mul_one]
  have hY' : Y * Real.exp (-l₂ * kl) * Real.exp (l₂ * kl) = Y := by rw [mul_assoc, ex1, mul_one]
  have eA : Real.exp (l₁ * (kl + L)) = Real.exp (l₁ * kl) * Real.exp (l₁ * L) := by
    rw [← Real.exp_add]; congr 1; ring
  have eB : Real.exp (l₂ * (kl + L)) = Real.exp (l₂ * kl) * Real.exp (l₂ * L) := by
    rw [← Real.exp_add]; congr 1; ring
  refine ⟨(X * Real.exp (-l₁ * kl), Y * Real.exp (-l₂ * kl), kl, kl + L), ?_, ?_⟩
  · refine ⟨by linarith, ?_, ?_, ?_, ?_⟩
    · unfold zoneSolution; linear_combination hX' + hY' + hkl
    · unfold zoneSolution; rw [eA, eB, hEneg]
      linear_combination Real.exp (l₁ * L) * hX' + (Real.exp (-l₂ * L))⁻¹ * hY' + hkl + hw + hWL
    · linear_combination hp1 + l₁ * hX' + l₂ * hY'
    · rw [eA, eB, hEneg]
      linear_combination hp2 + l₁ * Real.exp (l₁ * L) * hX' +
        l₂ * (Real.exp (-l₂ * L))⁻¹ * hY'
  · rintro ⟨b₁, b₂, kl', kh'⟩ h
    obtain ⟨hw', hX1, hY1, hkl1⟩ := driftBand_characterisation hl₁ hl₂ h
    have hk' := h.1
    simp only at hw' hX1 hY1 hkl1 hk'
    have hLL : kh' - kl' = L := hLu _ ⟨by linarith, hw'⟩
    rw [hLL] at hX1 hY1 hkl1
    rw [hX] at hX1 hkl1
    rw [hY] at hY1 hkl1
    have hkk : kl' = kl := by rw [hkl1, hkl]
    subst hkk
    have hb1 : b₁ = X * Real.exp (-l₁ * kl') := by
      linear_combination (-b₁) * ex1 l₁ kl' + Real.exp (-l₁ * kl') * hX1
    have hb2 : b₂ = Y * Real.exp (-l₂ * kl') := by
      linear_combination (-b₂) * ex1 l₂ kl' + Real.exp (-l₂ * kl') * hY1
    simp only [Prod.mk.injEq]
    exact ⟨hb1, hb2, trivial, by linarith⟩

/-! ## Convergence of the lattice zone to the continuous zone as `Δ → 0` -/

/-- O&R §8.5 (lattice scaling `h = Δ²/v²`): the lattice characteristic root
`θ_Δ = 2 arsinh(λΔ/2)`. -/
noncomputable def latTheta (l Δ : ℝ) : ℝ := 2 * Real.arsinh (l * Δ / 2)

/-- O&R §8.5: `sinh(θ_Δ/2) = λΔ/2`. -/
theorem sinh_half_latTheta (l Δ : ℝ) : Real.sinh (latTheta l Δ / 2) = l * Δ / 2 := by
  unfold latTheta; rw [mul_div_cancel_left₀ _ two_ne_zero, Real.sinh_arsinh]

/-- O&R §8.5: `cosh θ_Δ = 1 + λ²Δ²/2`. -/
theorem cosh_latTheta (l Δ : ℝ) : Real.cosh (latTheta l Δ) = 1 + l ^ 2 * Δ ^ 2 / 2 := by
  have h := sinh_half_latTheta l Δ
  have e : latTheta l Δ = 2 * (latTheta l Δ / 2) := by ring
  rw [e, Real.cosh_two_mul, Real.cosh_sq, h]; ring

/-- O&R §8.5 (lattice scaling): with `λ = √(2/(ηv²))`, `a = η/h = ηv²/Δ²` and
`θ = θ_Δ`, the characteristic equation `cosh θ = 1 + 1/a` of the lattice holds. -/
theorem latTheta_char {η v Δ : ℝ} (hη : 0 < η) (hv : 0 < v) (hΔ : 0 < Δ) :
    Real.cosh (latTheta (Real.sqrt (2 / (η * v ^ 2))) Δ) = 1 + 1 / (η * v ^ 2 / Δ ^ 2) := by
  rw [cosh_latTheta, Real.sq_sqrt (by positivity)]
  field_simp

/-- O&R §8.5: `θ_Δ > 0` for `λ, Δ > 0`. -/
theorem latTheta_pos {l Δ : ℝ} (hl : 0 < l) (hΔ : 0 < Δ) : 0 < latTheta l Δ := by
  unfold latTheta; have := Real.arsinh_pos_iff.2 (show 0 < l * Δ / 2 by positivity)
  linarith

/-- O&R §8.5: `θ_Δ/Δ → λ` as `Δ → 0⁺`. -/
theorem latTheta_div_tendsto {l : ℝ} (hl : 0 < l) :
    Tendsto (fun Δ => latTheta l Δ / Δ) (𝓝[>] 0) (𝓝 l) := by
  have hd := Real.hasDerivAt_arsinh 0
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    Real.sqrt_one, inv_one] at hd
  have hs := hasDerivAt_iff_tendsto_slope.1 hd
  have hy : Tendsto (fun Δ : ℝ => l * Δ / 2) (𝓝[>] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun Δ : ℝ => l * Δ / 2) (𝓝 0) (𝓝 (l * 0 / 2)) :=
        ((continuous_const.mul continuous_id).div_const 2).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with Δ hΔ
      simp only [mem_Ioi] at hΔ; simp only [mem_compl_iff, mem_singleton_iff]; positivity
  have h2 := (hs.comp hy).const_mul l
  rw [mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with Δ hΔ
  simp only [mem_Ioi] at hΔ
  simp only [Function.comp, slope_def_field, Real.arsinh_zero, sub_zero, latTheta]
  field_simp

/-- O&R §8.5: the lattice solution written as a function of fundamentals
`e(k) = k − sinh(μk)/(λ cosh μK)` (`μ = θ/Δ`, `K` the pasting point); `μ = λ` gives the
continuous `S`. -/
noncomputable def latRate (l μ K k : ℝ) : ℝ := k - Real.sinh (μ * k) / (l * Real.cosh (μ * K))

/-- O&R (85): the continuous smooth-pasting locus with pasting point `K` is `latRate λ λ K`. -/
theorem symS_eq_latRate {l : ℝ} (hl : 0 < l) (K k : ℝ) :
    symS l (1 / (2 * l * Real.cosh (l * K))) k = latRate l l K k := by
  unfold symS latRate
  have := Real.cosh_pos (l * K)
  field_simp

/-- O&R §8.5: at the lattice nodes, with `(N + ½)Δ = K` and `θ = θ_Δ`, the closed-form
lattice solution is `latRate λ (θ/Δ) K (iΔ)`. -/
theorem latticeSol_eq_latRate {l Δ : ℝ} (hl : 0 < l) (hΔ : 0 < Δ) (N i : ℤ) :
    latticeSol Δ (latTheta l Δ) (latticeCoeff Δ (latTheta l Δ) N) i =
      latRate l (latTheta l Δ / Δ) ((N + 1 / 2) * Δ) (i * Δ) := by
  unfold latticeSol latRate latticeCoeff
  rw [sinh_step, sinh_half_latTheta]
  have hc := Real.cosh_pos (latTheta l Δ * (N + 1 / 2))
  have e1 : latTheta l Δ / Δ * (i * Δ) = latTheta l Δ * i := by field_simp
  have e2 : latTheta l Δ / Δ * ((N + 1 / 2) * Δ) = latTheta l Δ * (N + 1 / 2) := by field_simp
  rw [e1, e2]
  field_simp

/-- O&R §8.5: `|sinh x| ≤ cosh x`. -/
theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  rw [abs_le]
  constructor
  · have := Real.sinh_lt_cosh (-x); rw [Real.sinh_neg, Real.cosh_neg] at this; linarith
  · exact (Real.sinh_lt_cosh x).le

/-- O&R §8.5 (**uniform error bound**): for `|k| ≤ K`,
`|latRate λ μ K k − S_K(k)| ≤ (2K/λ)|μ − λ|`. -/
theorem latRate_uniform_bound {l K : ℝ} (hl : 0 < l) (hK : 0 ≤ K) (μ : ℝ) {k : ℝ}
    (hk : |k| ≤ K) : |latRate l μ K k - latRate l l K k| ≤ 2 * K / l * |μ - l| := by
  set F : ℝ → ℝ := fun m => Real.sinh (m * k) / Real.cosh (m * K) with hF
  set F' : ℝ → ℝ := fun m => (k * Real.cosh (m * k) * Real.cosh (m * K) -
    Real.sinh (m * k) * (K * Real.sinh (m * K))) / Real.cosh (m * K) ^ 2 with hF'
  have hder : ∀ m ∈ (univ : Set ℝ), HasDerivWithinAt F (F' m) univ m := by
    intro m _
    have h1 : HasDerivAt (fun x => Real.sinh (x * k)) (Real.cosh (m * k) * k) m := by
      simpa using ((hasDerivAt_id' m).mul_const k).sinh
    have h2 : HasDerivAt (fun x => Real.cosh (x * K)) (Real.sinh (m * K) * K) m := by
      simpa using ((hasDerivAt_id' m).mul_const K).cosh
    have := (h1.div h2 (Real.cosh_pos _).ne').hasDerivWithinAt (s := univ)
    convert this using 1
    simp only [hF']; ring
  have hbound : ∀ m ∈ (univ : Set ℝ), ‖F' m‖ ≤ 2 * K := by
    intro m _
    have hc := Real.cosh_pos (m * K)
    have hck : Real.cosh (m * k) ≤ Real.cosh (m * K) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hk.trans (le_abs_self K)) (abs_nonneg m)
    have hsk := (abs_sinh_le_cosh (m * k)).trans hck
    have hsK := abs_sinh_le_cosh (m * K)
    rw [Real.norm_eq_abs, hF', abs_div, abs_of_pos (by positivity : 0 < Real.cosh (m * K) ^ 2),
      div_le_iff₀ (by positivity)]
    calc |k * Real.cosh (m * k) * Real.cosh (m * K) - Real.sinh (m * k) * (K * Real.sinh (m * K))|
        ≤ |k * Real.cosh (m * k) * Real.cosh (m * K)| +
            |Real.sinh (m * k) * (K * Real.sinh (m * K))| := abs_sub _ _
      _ ≤ K * Real.cosh (m * K) * Real.cosh (m * K) +
            Real.cosh (m * K) * (K * Real.cosh (m * K)) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.cosh_pos (m * k)),
            abs_of_pos hc, abs_of_nonneg hK]
          gcongr
      _ = 2 * K * Real.cosh (m * K) ^ 2 := by ring
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound convex_univ
    (mem_univ μ) (mem_univ l)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have e : latRate l μ K k - latRate l l K k = (F l - F μ) / l := by
    simp only [latRate, hF]; field_simp; ring
  rw [e, abs_div, abs_of_pos hl, div_le_iff₀ hl, abs_sub_comm μ l]
  calc |F l - F μ| ≤ 2 * K * |l - μ| := hmvt
    _ = 2 * K / l * |l - μ| * l := by field_simp

/-- O&R §8.5 (**uniform convergence on the band**): the extended lattice solution converges to
the continuous locus uniformly on `[−K, K]` as `Δ → 0`. -/
theorem latRate_uniform_tendsto {l K : ℝ} (hl : 0 < l) (hK : 0 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Δ in 𝓝[>] 0, ∀ k : ℝ, |k| ≤ K →
      |latRate l (latTheta l Δ / Δ) K k - latRate l l K k| < ε := by
  have ht := latTheta_div_tendsto hl
  have hC : 0 ≤ 2 * K / l := by positivity
  have hev : ∀ᶠ Δ in 𝓝[>] 0, 2 * K / l * |latTheta l Δ / Δ - l| < ε := by
    have h1 : Tendsto (fun Δ => 2 * K / l * |latTheta l Δ / Δ - l|) (𝓝[>] 0)
        (𝓝 (2 * K / l * |l - l|)) := ((ht.sub_const l).abs).const_mul _
    rw [sub_self, abs_zero, mul_zero] at h1
    exact h1.eventually (gt_mem_nhds hε)
  filter_upwards [hev] with Δ hΔ k hk
  exact lt_of_le_of_lt (latRate_uniform_bound hl hK _ hk) hΔ

/-- O&R §8.5 (**convergence of the lattice equilibrium**): fix the fundamental pasting point
`K > 0` and put `Δ_N = K/(N + ½)`, `h_N = Δ_N²/v²`. Then for every `ε > 0`, for all large `N`,
every lattice equilibrium `e` (with `a = η/h_N`) satisfies `|e_i − S(iΔ_N)| < ε` at every node
`|i| ≤ N`, where `S` is the continuous smooth-pasting locus with pasting point `K`. -/
theorem lattice_converges {η v K : ℝ} (hη : 0 < η) (hv : 0 < v) (hK : 0 < K) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ e : ℤ → ℝ,
      IsLatticeEqm (η * v ^ 2 / (K / (N + 1 / 2)) ^ 2) (K / (N + 1 / 2)) N e →
      ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N →
        |e i - symS (Real.sqrt (2 / (η * v ^ 2)))
          (1 / (2 * Real.sqrt (2 / (η * v ^ 2)) *
            Real.cosh (Real.sqrt (2 / (η * v ^ 2)) * K))) (i * (K / (N + 1 / 2)))| < ε := by
  set l := Real.sqrt (2 / (η * v ^ 2)) with hl
  have hl0 : 0 < l := (lambda_spec hη hv).1
  have hΔ : Tendsto (fun N : ℕ => K / ((N : ℝ) + 1 / 2)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun N => by
      simp only [mem_Ioi]; positivity⟩
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _
      tendsto_natCast_atTop_atTop)
  filter_upwards [hΔ.eventually (latRate_uniform_tendsto hl0 hK.le hε),
    eventually_ge_atTop 1] with N hN hN1 e he i h1 h2
  set Δ := K / ((N : ℝ) + 1 / 2) with hΔdef
  have hΔ0 : 0 < Δ := by positivity
  have hKΔ : ((N : ℤ) + 1 / 2 : ℝ) * Δ = K := by
    rw [hΔdef]; push_cast; field_simp
  have hsol := latticeSol_isEqm (by positivity) hΔ0 (latTheta_pos hl0 hΔ0)
    (latTheta_char hη hv hΔ0) (N := N) (by exact_mod_cast hN1)
  have heq := latticeEqm_unique (by positivity) (by positivity) he hsol i h1 h2
  rw [heq, latticeSol_eq_latRate hl0 hΔ0, hKΔ, symS_eq_latRate hl0]
  apply hN
  have hi : |(i : ℝ)| ≤ N := by
    rw [abs_le]; constructor <;> [exact_mod_cast (by omega : -(N : ℤ) ≤ i);
      exact_mod_cast h2]
  rw [abs_mul, abs_of_pos hΔ0]
  calc |(i : ℝ)| * Δ ≤ N * Δ := mul_le_mul_of_nonneg_right hi hΔ0.le
    _ ≤ K := by rw [← hKΔ]; push_cast; nlinarith

/-- O&R §8.5: the lattice rate at the top node `N` as a function of the spacing `Δ`
(lattice value matching sets it equal to the currency ceiling `ē`). -/
noncomputable def topValue (l : ℝ) (N : ℕ) (Δ : ℝ) : ℝ :=
  N * Δ - Real.sinh (N * latTheta l Δ) / (l * Real.cosh ((N + 1 / 2) * latTheta l Δ))

/-- O&R §8.5: for `Δ > 0` the top value is the lattice solution at node `N` (pasting point
`(N + ½)Δ`). -/
theorem topValue_eq_latticeSol {l Δ : ℝ} (hl : 0 < l) (hΔ : 0 < Δ) (N : ℕ) :
    topValue l N Δ = latticeSol Δ (latTheta l Δ) (latticeCoeff Δ (latTheta l Δ) N) N ∧
      topValue l N Δ = latRate l (latTheta l Δ / Δ) ((N + 1 / 2) * Δ) (N * Δ) := by
  have h := latticeSol_eq_latRate hl hΔ N N
  push_cast at h
  have e : topValue l N Δ = latRate l (latTheta l Δ / Δ) ((N + 1 / 2) * Δ) (N * Δ) := by
    unfold topValue latRate
    have e1 : latTheta l Δ / Δ * (N * Δ) = N * latTheta l Δ := by field_simp
    have e2 : latTheta l Δ / Δ * ((N + 1 / 2) * Δ) = (N + 1 / 2) * latTheta l Δ := by
      field_simp
    rw [e1, e2]
  exact ⟨e.trans h.symm, e⟩

/-- O&R §8.5: the top value is continuous in `Δ`. -/
theorem continuous_topValue {l : ℝ} (hl : 0 < l) (N : ℕ) : Continuous (topValue l N) := by
  have hθ : Continuous (latTheta l) := by
    unfold latTheta
    exact continuous_const.mul (Real.continuous_arsinh.comp
      ((continuous_const.mul continuous_id).div_const 2))
  unfold topValue
  refine Continuous.sub (continuous_const.mul continuous_id)
    (Continuous.div (Real.continuous_sinh.comp (continuous_const.mul hθ))
      (continuous_const.mul (Real.continuous_cosh.comp (continuous_const.mul hθ)))
      fun x => mul_ne_zero hl.ne' (Real.cosh_pos _).ne')

/-- O&R §8.5: `NΔ − 1/λ ≤ topValue ≤ NΔ` for `Δ ≥ 0`. -/
theorem topValue_bounds {l : ℝ} (hl : 0 < l) (N : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    N * Δ - 1 / l ≤ topValue l N Δ ∧ topValue l N Δ ≤ N * Δ := by
  have hθ : 0 ≤ latTheta l Δ := by
    unfold latTheta; have := Real.arsinh_nonneg_iff.2 (show 0 ≤ l * Δ / 2 by positivity)
    linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hs : 0 ≤ Real.sinh (N * latTheta l Δ) := Real.sinh_nonneg_iff.2 (mul_nonneg hN0 hθ)
  have hc := Real.cosh_pos ((N + 1 / 2) * latTheta l Δ)
  have hle : Real.sinh (N * latTheta l Δ) ≤ Real.cosh ((N + 1 / 2) * latTheta l Δ) := by
    refine (Real.sinh_lt_cosh _).le.trans ?_
    rw [Real.cosh_le_cosh, abs_of_nonneg (mul_nonneg hN0 hθ),
      abs_of_nonneg (mul_nonneg (by linarith) hθ)]
    nlinarith
  unfold topValue
  constructor
  · have : Real.sinh (N * latTheta l Δ) / (l * Real.cosh ((N + 1 / 2) * latTheta l Δ)) ≤ 1 / l :=
      by rw [div_le_div_iff₀ (by positivity) hl]; nlinarith
    linarith
  · have : 0 ≤ Real.sinh (N * latTheta l Δ) / (l * Real.cosh ((N + 1 / 2) * latTheta l Δ)) :=
      by positivity
    linarith

/-- A product inequality for `cosh` used for O&R §8.5: for `0 ≤ a ≤ b` and `0 ≤ θ₁ ≤ θ₂`,
`cosh(aθ₂) cosh(bθ₁) ≤ cosh(aθ₁) cosh(bθ₂)` (the ratio `cosh(aθ)/cosh(bθ)` decreases). -/
theorem cosh_ratio_antitone {a b θ₁ θ₂ : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (h1 : 0 ≤ θ₁)
    (h12 : θ₁ ≤ θ₂) :
    Real.cosh (a * θ₂) * Real.cosh (b * θ₁) ≤ Real.cosh (a * θ₁) * Real.cosh (b * θ₂) := by
  have prod : ∀ x y, 2 * (Real.cosh x * Real.cosh y) = Real.cosh (x + y) + Real.cosh (x - y) := by
    intro x y; rw [Real.cosh_add, Real.cosh_sub]; ring
  have c1 : Real.cosh (a * θ₂ + b * θ₁) ≤ Real.cosh (a * θ₁ + b * θ₂) := by
    have hθ2 : 0 ≤ θ₂ := le_trans h1 h12
    rw [Real.cosh_le_cosh, abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)]
    nlinarith
  have c2 : Real.cosh (a * θ₂ - b * θ₁) ≤ Real.cosh (a * θ₁ - b * θ₂) := by
    rw [Real.cosh_le_cosh]
    have hr : |a * θ₂ - b * θ₁| ≤ b * θ₂ - a * θ₁ := abs_le.2 ⟨by nlinarith, by nlinarith⟩
    have : |a * θ₁ - b * θ₂| = b * θ₂ - a * θ₁ := by
      rw [abs_sub_comm]; exact abs_of_nonneg (by nlinarith)
    linarith
  nlinarith [prod (a * θ₂) (b * θ₁), prod (a * θ₁) (b * θ₂)]

/-- O&R §8.5: the top value is the sum of the lattice increments,
`topValue = Σ_{i<N} Δ(1 − cosh θ(i+½)/cosh θ(N+½))`. -/
theorem topValue_eq_sum {l Δ : ℝ} (hl : 0 < l) (hΔ : 0 < Δ) (N : ℕ) :
    topValue l N Δ = ∑ i ∈ Finset.range N, Δ * (1 - Real.cosh (latTheta l Δ * (i + 1 / 2)) /
      Real.cosh (latTheta l Δ * (N + 1 / 2))) := by
  rw [(topValue_eq_latticeSol hl hΔ N).1]
  have hθ := latTheta_pos hl hΔ
  have h0 : latticeSol Δ (latTheta l Δ) (latticeCoeff Δ (latTheta l Δ) N) 0 = 0 := by
    simp [latticeSol]
  have htel := Finset.sum_range_sub
    (fun i : ℕ => latticeSol Δ (latTheta l Δ) (latticeCoeff Δ (latTheta l Δ) N) i) N
  simp only [Nat.cast_zero] at htel
  rw [h0, sub_zero] at htel
  rw [← htel]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := latticeSol_increment (Δ := Δ) hθ N i
  push_cast at this ⊢
  exact this

/-- O&R §8.5: the top value is strictly increasing in the spacing `Δ > 0` (`N ≥ 1`). -/
theorem topValue_strictMonoOn {l : ℝ} (hl : 0 < l) {N : ℕ} (hN : 1 ≤ N) :
    StrictMonoOn (topValue l N) (Ioi 0) := by
  intro Δ₁ h1 Δ₂ h2 h12
  simp only [mem_Ioi] at h1 h2
  rw [topValue_eq_sum hl h1, topValue_eq_sum hl h2]
  have hθ1 := latTheta_pos hl h1
  have hθ12 : latTheta l Δ₁ < latTheta l Δ₂ := by
    unfold latTheta
    have := Real.arsinh_strictMono (show l * Δ₁ / 2 < l * Δ₂ / 2 by nlinarith)
    linarith
  refine Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.2 (by omega)⟩ fun i hi => ?_
  have hiN : (i : ℝ) + 1 / 2 < N + 1 / 2 := by
    have h3 : (i : ℝ) < N := by exact_mod_cast Finset.mem_range.1 hi
    linarith
  set r₁ := Real.cosh (latTheta l Δ₁ * (i + 1 / 2)) / Real.cosh (latTheta l Δ₁ * (N + 1 / 2))
  set r₂ := Real.cosh (latTheta l Δ₂ * (i + 1 / 2)) / Real.cosh (latTheta l Δ₂ * (N + 1 / 2))
  have hc1 := Real.cosh_pos (latTheta l Δ₁ * (N + 1 / 2))
  have hc2 := Real.cosh_pos (latTheta l Δ₂ * (N + 1 / 2))
  have hr1 : r₁ < 1 := by
    rw [div_lt_one hc1, Real.cosh_lt_cosh, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    nlinarith
  have hr21 : r₂ ≤ r₁ := by
    rw [div_le_div_iff₀ hc2 hc1]
    have := cosh_ratio_antitone (a := (i : ℝ) + 1 / 2) (b := (N : ℝ) + 1 / 2) (by positivity)
      hiN.le hθ1.le hθ12.le
    rw [mul_comm (latTheta l Δ₂) _, mul_comm (latTheta l Δ₁) ((N : ℝ) + 1 / 2),
      mul_comm (latTheta l Δ₁) ((i : ℝ) + 1 / 2), mul_comm (latTheta l Δ₂) ((N : ℝ) + 1 / 2)]
    linarith
  nlinarith

/-- O&R §8.5 (**lattice value matching**): for each `N ≥ 1` and ceiling `ē > 0` there is a
unique spacing `Δ_N > 0` for which the lattice rate at the top node equals `ē`. -/
theorem existsUnique_lattice_spacing {l : ℝ} (hl : 0 < l) {N : ℕ} (hN : 1 ≤ N) {ebar : ℝ}
    (he : 0 < ebar) : ∃! Δ : ℝ, 0 < Δ ∧ topValue l N Δ = ebar := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set M := (ebar + 1 / l) / N with hM
  have hM0 : 0 ≤ M := by positivity
  have h0 : topValue l N 0 = 0 := by simp [topValue, latTheta]
  have hMv : ebar ≤ topValue l N M := by
    have := (topValue_bounds hl N hM0).1
    have e : (N : ℝ) * M = ebar + 1 / l := by rw [hM]; field_simp
    linarith
  obtain ⟨Δ, hΔ, hval⟩ := intermediate_value_Icc hM0 (continuous_topValue hl N).continuousOn
    ⟨by rw [h0]; exact he.le, hMv⟩
  have hΔ0 : 0 < Δ := by
    rcases eq_or_lt_of_le hΔ.1 with h | h
    · rw [← h, h0] at hval; linarith
    · exact h
  exact ⟨Δ, ⟨hΔ0, hval⟩, fun y hy => (topValue_strictMonoOn hl hN).injOn hy.1 hΔ0
    (hy.2.trans hval.symm)⟩

/-- O&R §8.5: the continuous locus with pasting point `K` moves by at most `δ` between
`K − δ` and `K` (its slope `1 − cosh λk/cosh λK` lies in `[0, 1]` on the band). -/
theorem latRate_near_edge {l K δ : ℝ} (hl : 0 < l) (hδ : 0 ≤ δ) (hδK : δ ≤ 2 * K) :
    |latRate l l K K - latRate l l K (K - δ)| ≤ δ := by
  have hK : 0 ≤ K := by linarith
  have hder : ∀ x ∈ Icc (K - δ) K, HasDerivWithinAt (latRate l l K)
      (1 - Real.cosh (l * x) / Real.cosh (l * K)) (Icc (K - δ) K) x := by
    intro x _
    have h1 : HasDerivAt (fun y => Real.sinh (l * y)) (Real.cosh (l * x) * l) x := by
      simpa using ((hasDerivAt_id' x).const_mul l).sinh
    have := ((hasDerivAt_id' x).sub (h1.div_const (l * Real.cosh (l * K)))).hasDerivWithinAt
      (s := Icc (K - δ) K)
    unfold latRate
    convert this using 1
    have := Real.cosh_pos (l * K)
    field_simp
  have hbound : ∀ x ∈ Icc (K - δ) K, ‖1 - Real.cosh (l * x) / Real.cosh (l * K)‖ ≤ 1 := by
    intro x hx
    have hc := Real.cosh_pos (l * K)
    have hle : Real.cosh (l * x) ≤ Real.cosh (l * K) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos hl, abs_of_nonneg hK]
      exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith [hx.1], hx.2⟩) hl.le
    have hr : Real.cosh (l * x) / Real.cosh (l * K) ≤ 1 := (div_le_one hc).2 hle
    have hr0 : 0 < Real.cosh (l * x) / Real.cosh (l * K) := div_pos (Real.cosh_pos _) hc
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_Icc _ _)
    (⟨le_rfl, by linarith⟩ : K - δ ∈ Icc (K - δ) K) (⟨by linarith, le_rfl⟩ : K ∈ Icc (K - δ) K)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, show K - (K - δ) = δ by ring, abs_of_nonneg hδ,
    one_mul] at this
  exact this

/-- O&R §8.5 (**the lattice band edge converges**): if `Δ_N` solves the lattice
value-matching condition for the ceiling `ē` (for every `N ≥ 1`) and `k̄ > 0` is the
continuous band edge (`k̄ − tanh(λk̄)/λ = ē`), then the lattice pasting point
`(N + ½)Δ_N → k̄` (and `Δ_N → 0`). -/
theorem lattice_edge_tendsto {l : ℝ} (hl : 0 < l) {ebar kb : ℝ} (he : 0 < ebar) (hkb : 0 < kb)
    (hedge : edgeMap l kb = ebar) {Δ : ℕ → ℝ}
    (hΔ : ∀ N : ℕ, 1 ≤ N → 0 < Δ N ∧ topValue l N (Δ N) = ebar) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1 / 2) * Δ N) atTop (𝓝 kb) := by
  set C := ebar + 1 / l with hC
  have hC0 : 0 < C := by positivity
  -- `Δ_N ≤ C/N`
  have hΔle : ∀ N : ℕ, 1 ≤ N → Δ N ≤ C / N := by
    intro N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have := (topValue_bounds hl N (hΔ N hN).1.le).1
    rw [(hΔ N hN).2] at this
    rw [le_div_iff₀ hN']; linarith
  have hΔ0 : Tendsto Δ atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := (0 : ℝ)))
        ((tendsto_const_nhds (x := C)).div_atTop tendsto_natCast_atTop_atTop) ?_ ?_
      · filter_upwards [eventually_ge_atTop 1] with N hN using (hΔ N hN).1.le
      · filter_upwards [eventually_ge_atTop 1] with N hN using hΔle N hN
    · filter_upwards [eventually_ge_atTop 1] with N hN using (hΔ N hN).1
  have hμ := (latTheta_div_tendsto hl).comp hΔ0
  -- the error bound `|edgeMap(K_N) − ē| ≤ (3C/λ)|μ_N − λ| + Δ_N/2`
  have hbnd : ∀ N : ℕ, 1 ≤ N → |edgeMap l (((N : ℝ) + 1 / 2) * Δ N) - ebar| ≤
      2 * (2 * C) / l * |latTheta l (Δ N) / Δ N - l| + Δ N / 2 := by
    intro N hN
    obtain ⟨hpos, hval⟩ := hΔ N hN
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    set K := ((N : ℝ) + 1 / 2) * Δ N with hK
    have hK0 : 0 ≤ K := by positivity
    have hKC : K ≤ 2 * C := by
      have := hΔle N hN
      calc K = ((N : ℝ) + 1 / 2) * Δ N := rfl
        _ ≤ ((N : ℝ) + 1 / 2) * (C / N) := mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ 2 * C := by rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    have hval' := (topValue_eq_latticeSol hl hpos N).2
    rw [hval] at hval'
    have hk : |(N : ℝ) * Δ N| ≤ K := by
      rw [abs_of_nonneg (by positivity), hK]; nlinarith
    have e1 := latRate_uniform_bound hl hK0 (latTheta l (Δ N) / Δ N) hk
    rw [← hval'] at e1
    have e2 := latRate_near_edge (K := K) hl (show 0 ≤ Δ N / 2 by positivity)
      (by rw [hK]; nlinarith)
    have e3 : K - Δ N / 2 = (N : ℝ) * Δ N := by rw [hK]; ring
    rw [e3] at e2
    have e4 : latRate l l K K = edgeMap l K := rfl
    rw [e4] at e2
    have e5 : 2 * K / l * |latTheta l (Δ N) / Δ N - l| ≤
        2 * (2 * C) / l * |latTheta l (Δ N) / Δ N - l| := by gcongr
    calc |edgeMap l K - ebar| = |(edgeMap l K - latRate l l K (N * Δ N)) +
          (latRate l l K (N * Δ N) - ebar)| := by ring_nf
      _ ≤ |edgeMap l K - latRate l l K (N * Δ N)| + |latRate l l K (N * Δ N) - ebar| :=
          abs_add_le _ _
      _ ≤ Δ N / 2 + 2 * K / l * |latTheta l (Δ N) / Δ N - l| := by
          rw [abs_sub_comm (latRate l l K _) ebar]; exact add_le_add e2 e1
      _ ≤ _ := by linarith
  have hlim : Tendsto (fun N : ℕ => edgeMap l (((N : ℝ) + 1 / 2) * Δ N)) atTop (𝓝 ebar) := by
    have hr : Tendsto (fun N : ℕ => 2 * (2 * C) / l * |latTheta l (Δ N) / Δ N - l| + Δ N / 2)
        atTop (𝓝 (2 * (2 * C) / l * |l - l| + 0 / 2)) :=
      (((hμ.sub_const l).abs).const_mul _).add
        ((hΔ0.mono_right nhdsWithin_le_nhds).div_const 2)
    rw [sub_self, abs_zero, mul_zero, zero_div, add_zero] at hr
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hr
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]; exact hbnd N hN
  -- invert the strictly increasing continuous `edgeMap`
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := min ε (kb / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by positivity)
  have hmono := edgeMap_strictMonoOn hl
  have hup : ebar < edgeMap l (kb + ε') := by
    rw [← hedge]; exact hmono (le_of_lt hkb) (by simp only [mem_Ici]; positivity) (by linarith)
  have hlo : edgeMap l (kb - ε') < ebar := by
    rw [← hedge]
    exact hmono (by simp only [mem_Ici]; linarith [min_le_right ε (kb / 2)]) (le_of_lt hkb)
      (by linarith)
  have hev := (hlim.eventually (Ioo_mem_nhds hlo hup)).and (eventually_ge_atTop 1)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨⟨h1, h2⟩, hN1⟩ := hN₀ N hN
  have hKpos : 0 ≤ ((N : ℝ) + 1 / 2) * Δ N := by
    have := (hΔ N hN1).1; positivity
  have hlt1 : ((N : ℝ) + 1 / 2) * Δ N < kb + ε' := by
    by_contra hc; push Not at hc
    have := hmono.monotoneOn (by simp only [mem_Ici]; positivity) (by simpa using hKpos) hc
    linarith
  have hlt2 : kb - ε' < ((N : ℝ) + 1 / 2) * Δ N := by
    by_contra hc; push Not at hc
    have := hmono.monotoneOn (by simpa using hKpos)
      (by simp only [mem_Ici]; linarith [min_le_right ε (kb / 2)]) hc
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [min_le_left ε (kb / 2)]

/-- O&R §8.5 (**lattice → continuous, prescribed band**): for a ceiling `ē > 0`, the lattice
spacings `Δ_N` fixed by lattice value matching exist, and the lattice pasting points
`(N + ½)Δ_N` converge to the unique continuous band edge `k̄`. -/
theorem lattice_edge_converges {l : ℝ} (hl : 0 < l) {ebar : ℝ} (he : 0 < ebar) :
    ∃ kb : ℝ, 0 < kb ∧ edgeMap l kb = ebar ∧ ∃ Δ : ℕ → ℝ,
      (∀ N : ℕ, 1 ≤ N → 0 < Δ N ∧ topValue l N (Δ N) = ebar) ∧
      Tendsto (fun N : ℕ => ((N : ℝ) + 1 / 2) * Δ N) atTop (𝓝 kb) := by
  obtain ⟨kb, ⟨hkb, hedge⟩, -⟩ := existsUnique_edge hl he
  have hex : ∀ N : ℕ, ∃ d : ℝ, 1 ≤ N → 0 < d ∧ topValue l N d = ebar := by
    intro N
    by_cases hN : 1 ≤ N
    · obtain ⟨d, hd, -⟩ := existsUnique_lattice_spacing hl hN he
      exact ⟨d, fun _ => hd⟩
    · exact ⟨0, fun h => absurd h hN⟩
  choose Δ hΔ using hex
  exact ⟨kb, hkb, hedge, Δ, hΔ, lattice_edge_tendsto hl he hkb hedge hΔ⟩

end ObstfeldRogoff.MoneyExchangeRates.TargetZone
