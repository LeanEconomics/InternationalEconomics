/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GlobalGrowth.RamseyCassKoopmans
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.Floor

/-!
# Continuous-time growth models as limits of discrete-time models

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, Appendix 7A
(pp. 508–510), eq. (11) (p. 435) and fn 23 (p. 463).

* **The continuous-time Solow model** (fn 23): for Cobb–Douglas technology, `x = k^{1-α}`
  solves a linear ODE, so every solution of `k̇ = s k^α - (n+g+δ) k` with `k > 0` is given in
  closed form, the closed form is a solution (existence), solutions are unique, and every
  solution converges monotonically to `k̄ = (s/(n+g+δ))^{1/(1-α)}`; eq. (11).
* **The period-`h` Solow model** (3′)–(5′): the exact difference equation, its steady state
  `s f(k̄_h) = (n + g + δ + ngh) k̄_h`, and genuine `h → 0` limits: the steady state
  converges to that of (9′) (for any neoclassical `f`), the difference quotient converges to
  the right-hand side of the ODE, `(1 + gh)^{t/h} E₀ → e^{gt} E₀`, and the derivation of
  (3″) from (3″)–(5″) by the quotient rule.
* **The period-`h` Ramsey–Cass–Koopmans model**: the first-order condition
  `u'(C_s) = [1 + hF'(K_{s+h})] u'(C_{s+h})/(1 + ρh)` is *derived* as a necessary condition
  for any optimal plan (one-period perturbation), its difference-quotient form, the genuine
  limit of the Euler residual as `h → 0` (so a path satisfying the period-`h` Euler equation
  for a sequence `h → 0` satisfies `u''(C) Ċ = [ρ - F'(K)] u'(C)`), the discount factor
  limit `(1 + ρh)^{-τ/h} → e^{-ρτ}`, and the Hamiltonian first-order conditions.
* **Precise convergence statements**: period-`h` steady states equal the continuous one; the
  period-`h` Euler dynamics converge to the Ramsey ODE uniformly on compact time intervals,
  for log utility and for isoelastic utility with any `σ > 0` (a general convergence theorem
  for one-step schemes along any filter `l ≤ 𝓝[>] 0`, instantiated; the isoelastic uniform
  consistency is the first-order expansion of `(1 + x)^{1/σ}`); the period-`h` discounted
  objectives converge to `∫₀^∞ e^{-ρs} u(C(s)) ds` for continuous bounded flow utility
  (dominated convergence for the step functions); and the period-`h` saddle choice of initial
  consumption converges to the continuous saddle value whenever the discrete saddle paths stay
  in a set `S` and every other continuous-time initial choice leaves `S` in finite time
  (compactness plus scheme convergence along a subnet). The continuous-time phase-diagram
  fact itself (that non-saddle solutions do leave) is a hypothesis.
-/

namespace ObstfeldRogoff.GlobalGrowth.ContinuousTimeLimits

open Set Filter Topology MeasureTheory
open ObstfeldRogoff.GlobalGrowth.SolowModel

variable {f : ℝ → ℝ}

/-! ## The continuous-time Cobb–Douglas Solow model (fn 23, p. 463) -/

/-- **fn 23's transformation** (O&R p. 463): if `k > 0` solves
`k̇ = s k^α - m k` (`m = n + g + δ`), then `x = k^{1-α}` solves the linear ODE
`ẋ = (1-α) s - (1-α) m x`. -/
theorem transformed_ode {α s m : ℝ} {k : ℝ → ℝ} {t : ℝ} (hk : 0 < k t)
    (hd : HasDerivAt k (s * k t ^ α - m * k t) t) :
    HasDerivAt (fun t => k t ^ (1 - α))
      ((1 - α) * s - (1 - α) * m * k t ^ (1 - α)) t := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl (ne_of_gt hk))).comp t hd
  refine h.congr_deriv ?_
  have e1 : k t ^ (1 - α - 1) * k t ^ α = 1 := by
    rw [← Real.rpow_add hk]; simp
  have e2 : k t ^ (1 - α - 1) * k t = k t ^ (1 - α) := by
    rw [← Real.rpow_add_one (ne_of_gt hk)]; ring_nf
  calc (1 - α) * k t ^ (1 - α - 1) * (s * k t ^ α - m * k t)
      = (1 - α) * s * (k t ^ (1 - α - 1) * k t ^ α) -
          (1 - α) * m * (k t ^ (1 - α - 1) * k t) := by ring
    _ = _ := by rw [e1, e2]; ring

/-- **The closed form** (fn 23): every positive solution on `[0, ∞)` satisfies
`k_t^{1-α} = x̄ + (k₀^{1-α} - x̄) e^{-(1-α) m t}`, `x̄ = s/m`. -/
theorem closed_form {α s m : ℝ} (hm : m ≠ 0) {k : ℝ → ℝ} (hk : ∀ t, 0 ≤ t → 0 < k t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt k (s * k t ^ α - m * k t) t) {t : ℝ} (ht : 0 ≤ t) :
    k t ^ (1 - α) = s / m + (k 0 ^ (1 - α) - s / m) * Real.exp (-((1 - α) * m) * t) := by
  set lam := (1 - α) * m
  -- `y(t) = (x(t) - x̄) e^{λ t}` is constant on `[0, t]`
  set y : ℝ → ℝ := fun t => (k t ^ (1 - α) - s / m) * Real.exp (lam * t)
  have hy : ∀ τ, 0 ≤ τ → HasDerivAt y 0 τ := by
    intro τ hτ
    have hx := transformed_ode (hk τ hτ) (hd τ hτ)
    have he := (Real.hasDerivAt_exp (lam * τ)).comp τ ((hasDerivAt_id' τ).const_mul lam)
    have := (hx.sub_const (s / m)).mul he
    refine this.congr_deriv ?_
    simp only [Function.comp_apply, lam]
    field_simp
    ring
  have hcont : ContinuousOn y (Icc 0 t) := fun τ hτ => (hy τ hτ.1).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun τ hτ => (hy τ hτ.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩
  simp only [y, mul_zero, Real.exp_zero, mul_one] at hconst
  have hexp : Real.exp (lam * t) * Real.exp (-lam * t) = 1 := by
    rw [← Real.exp_add]; simp
  have : k t ^ (1 - α) - s / m = (k 0 ^ (1 - α) - s / m) * Real.exp (-lam * t) := by
    rw [← hconst]
    calc k t ^ (1 - α) - s / m = (k t ^ (1 - α) - s / m) *
        (Real.exp (lam * t) * Real.exp (-lam * t)) := by rw [hexp, mul_one]
      _ = _ := by ring
  linarith

/-- **Global convergence in continuous time** (fn 23): every positive solution converges to
`k̄ = (s/m)^{1/(1-α)}` of (9′); the gap in `x = k^{1-α}` shrinks monotonically at the constant
exponential rate `(1-α)(n+g+δ)`. -/
theorem continuous_convergence {α s m : ℝ} (hα1 : α < 1) (hs : 0 < s) (hm : 0 < m)
    {k : ℝ → ℝ} (hk : ∀ t, 0 ≤ t → 0 < k t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt k (s * k t ^ α - m * k t) t) :
    Tendsto k atTop (𝓝 ((s / m) ^ (1 / (1 - α)))) ∧
      ∀ t, 0 ≤ t → |k t ^ (1 - α) - s / m| =
        |k 0 ^ (1 - α) - s / m| * Real.exp (-((1 - α) * m) * t) := by
  have hlam : 0 < (1 - α) * m := mul_pos (by linarith) hm
  have hcf := fun t (ht : 0 ≤ t) => closed_form (ne_of_gt hm) hk hd ht
  refine ⟨?_, fun t ht => ?_⟩
  · have hexp : Tendsto (fun t => Real.exp (-((1 - α) * m) * t)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => -((1 - α) * m) * t) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      exact Real.tendsto_exp_atBot.comp h1
    have hx : Tendsto (fun t => k t ^ (1 - α)) atTop (𝓝 (s / m)) := by
      have := (hexp.const_mul (k 0 ^ (1 - α) - s / m)).const_add (s / m)
      rw [mul_zero, add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with t ht
      exact (hcf t ht).symm
    have hpow := ((Real.continuousAt_rpow_const (s / m) (1 / (1 - α))
      (Or.inl (ne_of_gt (div_pos hs hm)))).tendsto).comp hx
    refine hpow.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    simp only [Function.comp_apply]
    rw [← Real.rpow_mul (hk t ht).le, mul_one_div_cancel (by linarith : (1 : ℝ) - α ≠ 0),
      Real.rpow_one]
  · rw [hcf t ht, add_sub_cancel_left, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- **Existence** (fn 23): the closed form
`k(t) = [x̄ + (x₀ - x̄) e^{-(1-α)mt}]^{1/(1-α)}` with `x₀ = k₀^{1-α} > 0` is a positive solution
of `k̇ = s k^α - m k` for all `t ≥ 0`. -/
theorem closed_form_solves {α s m k0 : ℝ} (hα1 : α < 1) (hs : 0 < s) (hm : 0 < m)
    (hk0 : 0 < k0) {t : ℝ} (ht : 0 ≤ t) :
    let x : ℝ → ℝ := fun t => s / m + (k0 ^ (1 - α) - s / m) * Real.exp (-((1 - α) * m) * t)
    0 < x t ∧ HasDerivAt (fun t => x t ^ (1 / (1 - α)))
      (s * (x t ^ (1 / (1 - α))) ^ α - m * x t ^ (1 / (1 - α))) t := by
  intro x
  have h1α : 0 < 1 - α := by linarith
  have hlam : 0 < (1 - α) * m := mul_pos h1α hm
  have he : 0 < Real.exp (-((1 - α) * m) * t) := Real.exp_pos _
  have he1 : Real.exp (-((1 - α) * m) * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hx0 : 0 < k0 ^ (1 - α) := Real.rpow_pos_of_pos hk0 _
  have hxpos : 0 < x t := by
    -- a convex combination of `x₀ > 0` and `x̄ > 0`
    have : x t = s / m * (1 - Real.exp (-((1 - α) * m) * t)) +
        k0 ^ (1 - α) * Real.exp (-((1 - α) * m) * t) := by simp only [x]; ring
    rw [this]
    have := div_pos hs hm
    have : 0 ≤ 1 - Real.exp (-((1 - α) * m) * t) := by linarith
    positivity
  refine ⟨hxpos, ?_⟩
  have hxd : HasDerivAt x (-((1 - α) * m) * (k0 ^ (1 - α) - s / m) *
      Real.exp (-((1 - α) * m) * t)) t := by
    have := (((Real.hasDerivAt_exp _).comp t ((hasDerivAt_id' t).const_mul
      (-((1 - α) * m)))).const_mul (k0 ^ (1 - α) - s / m)).const_add (s / m)
    refine this.congr_deriv ?_
    ring
  have h := (Real.hasDerivAt_rpow_const (p := 1 / (1 - α)) (Or.inl (ne_of_gt hxpos))).comp t hxd
  refine h.congr_deriv ?_
  -- rewrite in terms of `x t`
  have hxd' : -((1 - α) * m) * (k0 ^ (1 - α) - s / m) * Real.exp (-((1 - α) * m) * t) =
      (1 - α) * s - (1 - α) * m * x t := by simp only [x]; field_simp; ring
  rw [hxd']
  have e1 : (x t ^ (1 / (1 - α))) ^ α = x t ^ (1 / (1 - α) - 1) := by
    rw [← Real.rpow_mul hxpos.le]; congr 1; field_simp; ring
  have e2 : x t ^ (1 / (1 - α)) = x t ^ (1 / (1 - α) - 1) * x t := by
    rw [← Real.rpow_add_one (ne_of_gt hxpos)]; ring_nf
  rw [e1, e2]
  field_simp

/-- **Eq. (11)** (O&R p. 435): in continuous time with `E_t = E₀ e^{gt}`,
`log(Y/L) = log E₀ + g t + (α/(1-α))[log s - log(n + g + δ)]`. -/
theorem log_output_continuous {α s m E0 g t : ℝ} (hs : 0 < s) (hm : 0 < m) (hE0 : 0 < E0) :
    Real.log (E0 * Real.exp (g * t) * ((s / m) ^ (1 / (1 - α))) ^ α) =
      Real.log E0 + g * t + α / (1 - α) * (Real.log s - Real.log m) := by
  have hx : 0 < s / m := div_pos hs hm
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_exp, ← Real.rpow_mul hx.le, Real.log_rpow hx,
    Real.log_div (ne_of_gt hs) (ne_of_gt hm)]
  ring

/-! ## The period-`h` Solow model (O&R pp. 508–509) -/

/-- **The period-`h` accumulation equation** (O&R (3′)–(5′), p. 508): with
`K_{t+h} = K_t + h[s F(K_t, E_t L_t) - δ K_t]`, `E_{t+h} = (1 + gh) E_t`, `L_{t+h} = (1 + nh) L_t`
and constant returns,
`(k_{t+h} - k_t)/h = s f(k_t)/((1+nh)(1+gh)) - (n + g + δ + ngh) k_t/((1+nh)(1+gh))`. -/
theorem period_h_solow (F : ℝ → ℝ → ℝ) (hCRS : ∀ c K N, 0 < c → F (c * K) (c * N) = c * F K N)
    {s δ n g h K K' E L : ℝ} (hh : 0 < h) (hE : 0 < E) (hL : 0 < L) (hn : 0 < 1 + n * h)
    (hg : 0 < 1 + g * h) (hK : K' = K + h * (s * F K (E * L) - δ * K)) :
    (K' / ((1 + g * h) * E * ((1 + n * h) * L)) - K / (E * L)) / h =
      s * F (K / (E * L)) 1 / ((1 + n * h) * (1 + g * h)) -
        (n + g + δ + n * g * h) * (K / (E * L)) / ((1 + n * h) * (1 + g * h)) := by
  have hEL : 0 < E * L := mul_pos hE hL
  have hF : F K (E * L) = E * L * F (K / (E * L)) 1 := by
    have := hCRS (E * L) (K / (E * L)) 1 hEL
    rw [mul_div_cancel₀ _ (ne_of_gt hEL), mul_one] at this
    exact this
  rw [hK, hF]
  set x := K / (E * L) with hx
  have hKx : K = x * (E * L) := by rw [hx, div_mul_cancel₀ _ (ne_of_gt hEL)]
  rw [hKx]
  have hE' := ne_of_gt hE
  have hL' := ne_of_gt hL
  have hh' := ne_of_gt hh
  have hn' := ne_of_gt hn
  have hg' := ne_of_gt hg
  have hD : 1 + h * g + h * n + h ^ 2 * g * n ≠ 0 := by
    have := mul_pos hg hn
    exact ne_of_gt (by nlinarith)
  field_simp
  linear_combination x * mul_inv_cancel₀ hD

/-- **The period-`h` steady state** (O&R p. 508): a fixed point of the period-`h` equation
satisfies `s f(k̄) = (n + g + δ + ngh) k̄`. -/
theorem period_h_steady {f : ℝ → ℝ} {s δ n g h k : ℝ} (hn : 0 < 1 + n * h)
    (hg : 0 < 1 + g * h)
    (hfix : s * f k / ((1 + n * h) * (1 + g * h)) -
      (n + g + δ + n * g * h) * k / ((1 + n * h) * (1 + g * h)) = 0) :
    s * f k = (n + g + δ + n * g * h) * k := by
  rw [← sub_div, div_eq_zero_iff] at hfix
  rcases hfix with h1 | h1
  · linarith
  · exact absurd h1 (ne_of_gt (mul_pos hn hg))

/-- Continuity of an implicitly defined steady state: if `ψ` is strictly increasing on
`(0, ∞)` and `ψ(k(h)) = T(h)` with `k(h) > 0` near `h₀` and `T` continuous at `h₀`, then `k` is
continuous at `h₀` (used for the `h → 0` limit of the steady state). -/
theorem continuousAt_implicit {ψ kh T : ℝ → ℝ} {h0 : ℝ} (hψ : StrictMonoOn ψ (Ioi 0))
    (hT : ContinuousAt T h0) (hk : ∀ᶠ h in 𝓝 h0, ψ (kh h) = T h ∧ 0 < kh h) :
    ContinuousAt kh h0 := by
  have h0' := hk.self_of_nhds
  rw [ContinuousAt, tendsto_order]
  constructor
  · intro a ha
    set a' := max a (kh h0 / 2)
    have ha'0 : 0 < a' := lt_of_lt_of_le (half_pos h0'.2) (le_max_right _ _)
    have ha'g : a' < kh h0 := max_lt ha (half_lt_self h0'.2)
    have hψa : ψ a' < T h0 := by have := hψ ha'0 h0'.2 ha'g; rwa [h0'.1] at this
    filter_upwards [hk, hT.eventually (lt_mem_nhds hψa)] with h hh hTh
    by_contra hle
    push Not at hle
    have := hψ.monotoneOn hh.2 ha'0 (hle.trans (le_max_left _ _))
    rw [hh.1] at this
    linarith
  · intro b hb
    have hb0 : 0 < b := h0'.2.trans hb
    have hψb : T h0 < ψ b := by have := hψ h0'.2 hb0 hb; rwa [h0'.1] at this
    filter_upwards [hk, hT.eventually (gt_mem_nhds hψb)] with h hh hTh
    by_contra hle
    push Not at hle
    have := hψ.monotoneOn hb0 hh.2 hle
    rw [hh.1] at this
    linarith

/-- **The `h → 0` limit of the steady state** (O&R (9′), p. 508), for any neoclassical `f`:
if `k̄_h > 0` solves `s f(k̄_h) = (n + g + δ + ngh) k̄_h` for all small `h`, then
`k̄_h → k̄_0`, the steady state of the continuous-time model `s f(k̄) = (n + g + δ) k̄`. -/
theorem steady_limit (hf : Neoclassical f) {s n g δ : ℝ} (hs : 0 < s) {kh : ℝ → ℝ}
    (hk : ∀ᶠ h in 𝓝 0, 0 < kh h ∧ s * f (kh h) = (n + g + δ + n * g * h) * kh h) :
    Tendsto kh (𝓝[>] 0) (𝓝 (kh 0)) := by
  have hcont : ContinuousAt kh 0 := by
    refine continuousAt_implicit (ψ := fun k => -(f k / k))
      (T := fun h => -((n + g + δ + n * g * h) / s)) ?_ ?_ ?_
    · intro a ha b hb hab
      exact neg_lt_neg (hf.avg_strictAnti ha hb hab)
    · exact (by fun_prop : Continuous (fun h : ℝ => -((n + g + δ + n * g * h) / s))).continuousAt
    · filter_upwards [hk] with h hh
      refine ⟨?_, hh.1⟩
      congr 1
      rw [div_eq_div_iff (ne_of_gt hh.1) (ne_of_gt hs)]
      linarith [hh.2]
  exact hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- The Cobb–Douglas steady state for period `h`, `k̄_h = (s/(n+g+δ+ngh))^{1/(1-α)}`, converges
to `(s/(n+g+δ))^{1/(1-α)}` as `h → 0` (O&R (9′)). -/
theorem cobbDouglas_steady_limit {α s n g δ : ℝ} (hs : 0 < s) (hm : 0 < n + g + δ) :
    Tendsto (fun h => (s / (n + g + δ + n * g * h)) ^ (1 / (1 - α))) (𝓝[>] 0)
      (𝓝 ((s / (n + g + δ)) ^ (1 / (1 - α)))) := by
  have hq : Tendsto (fun h => s / (n + g + δ + n * g * h)) (𝓝 0) (𝓝 (s / (n + g + δ))) := by
    have hc : Continuous (fun h : ℝ => n + g + δ + n * g * h) := by fun_prop
    have hc' : Tendsto (fun h : ℝ => n + g + δ + n * g * h) (𝓝 0) (𝓝 (n + g + δ)) := by
      simpa using hc.tendsto 0
    exact (tendsto_const_nhds (x := s)).div hc' (ne_of_gt hm)
  exact (((Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt (div_pos hs hm)))).tendsto).comp
    hq).mono_left nhdsWithin_le_nhds

/-- **The difference quotient converges to the ODE** (O&R (3″)): for fixed `k`, the right-hand
side of the period-`h` equation tends to `s f(k) - (n + g + δ) k` as `h → 0`. -/
theorem difference_quotient_limit (s fk k n g δ : ℝ) :
    Tendsto (fun h => s * fk / ((1 + n * h) * (1 + g * h)) -
      (n + g + δ + n * g * h) * k / ((1 + n * h) * (1 + g * h))) (𝓝 0)
      (𝓝 (s * fk - (n + g + δ) * k)) := by
  have hden : Tendsto (fun h : ℝ => (1 + n * h) * (1 + g * h)) (𝓝 0) (𝓝 1) := by
    have hc : Continuous (fun h : ℝ => (1 + n * h) * (1 + g * h)) := by fun_prop
    simpa using hc.tendsto 0
  have hnum : Tendsto (fun h : ℝ => (n + g + δ + n * g * h) * k) (𝓝 0)
      (𝓝 ((n + g + δ) * k)) := by
    have hc : Continuous (fun h : ℝ => (n + g + δ + n * g * h) * k) := by fun_prop
    simpa using hc.tendsto 0
  have := ((tendsto_const_nhds (x := s * fk)).div hden one_ne_zero).sub
    (hnum.div hden one_ne_zero)
  simpa using this

/-- **Deriving (3″) in intensive form** (O&R p. 509): if `K̇ = s F(K, EL) - δK`, `Ė = gE`,
`L̇ = nL` with constant returns, then `k = K/(EL)` satisfies `k̇ = s f(k) - (n + g + δ) k`. -/
theorem continuous_solow_derivation (F : ℝ → ℝ → ℝ)
    (hCRS : ∀ c K N, 0 < c → F (c * K) (c * N) = c * F K N) {s δ n g t : ℝ}
    {K E L : ℝ → ℝ} (hE : 0 < E t) (hL : 0 < L t)
    (hK : HasDerivAt K (s * F (K t) (E t * L t) - δ * K t) t)
    (hEd : HasDerivAt E (g * E t) t) (hLd : HasDerivAt L (n * L t) t) :
    HasDerivAt (fun t => K t / (E t * L t))
      (s * F (K t / (E t * L t)) 1 - (n + g + δ) * (K t / (E t * L t))) t := by
  have hEL : 0 < E t * L t := mul_pos hE hL
  have hF : F (K t) (E t * L t) = E t * L t * F (K t / (E t * L t)) 1 := by
    have := hCRS (E t * L t) (K t / (E t * L t)) 1 hEL
    rw [mul_div_cancel₀ _ (ne_of_gt hEL), mul_one] at this
    exact this
  have h := hK.div (hEd.mul hLd) (ne_of_gt hEL)
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [hF]
  field_simp
  ring

/-! ## Exponential limits (O&R p. 509) -/

/-- **The compounding limit** (O&R p. 509): `(1 + a h)^{t/h} → e^{a t}` as `h → 0⁺`. -/
theorem compound_limit (a t : ℝ) :
    Tendsto (fun h : ℝ => (1 + a * h) ^ (t / h)) (𝓝[>] 0) (𝓝 (Real.exp (a * t))) := by
  -- substitute `x = 1/h → ∞`
  have hx : Tendsto (fun h : ℝ => h⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have hbase := (Real.tendsto_one_add_div_rpow_exp a).comp hx
  have hpow := ((Real.continuousAt_rpow_const (Real.exp a) t
    (Or.inl (ne_of_gt (Real.exp_pos a)))).tendsto).comp hbase
  rw [← Real.exp_mul] at hpow
  refine hpow.congr' ?_
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < 1 + a * h := by
    have : Tendsto (fun h : ℝ => 1 + a * h) (𝓝[>] 0) (𝓝 1) := by
      have hc : Continuous (fun h : ℝ => 1 + a * h) := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    exact this.eventually (lt_mem_nhds one_pos)
  filter_upwards [hev, self_mem_nhdsWithin] with h hpos hh
  have hh' : (0 : ℝ) < h := hh
  simp only [Function.comp_apply]
  rw [div_inv_eq_mul, ← Real.rpow_mul hpos.le, inv_mul_eq_div]

/-- **Productivity in the limit** (O&R p. 509): `E_t = (1 + gh)^{t/h} E₀ → e^{gt} E₀`. -/
theorem productivity_limit (g t E0 : ℝ) :
    Tendsto (fun h : ℝ => (1 + g * h) ^ (t / h) * E0) (𝓝[>] 0) (𝓝 (Real.exp (g * t) * E0)) :=
  (compound_limit g t).mul_const E0

/-- **The discount factor in the limit** (O&R p. 509): `(1 + ρh)^{-τ/h} → e^{-ρτ}`, so the
period-`h` objective discounts like `∫ u(C) e^{-ρ(s-t)} ds`. -/
theorem discount_limit (ρ τ : ℝ) :
    Tendsto (fun h : ℝ => (1 + ρ * h) ^ (-τ / h)) (𝓝[>] 0) (𝓝 (Real.exp (-(ρ * τ)))) := by
  have := compound_limit ρ (-τ)
  rwa [mul_neg] at this

/-! ## The period-`h` Ramsey–Cass–Koopmans model (O&R pp. 509–510) -/

/-- Consumption rate in the period-`h` model: `C_j = (K_j - K_{j+1})/h + F(K_j)`. -/
noncomputable def consH (F : ℝ → ℝ) (h : ℝ) (K : ℕ → ℝ) (j : ℕ) : ℝ :=
  (K j - K (j + 1)) / h + F (K j)

/-- Period-`h` welfare `∑_j (1 + ρh)^{-j} u(C_j) h` (O&R p. 509). -/
noncomputable def welfareH (F u : ℝ → ℝ) (ρ h : ℝ) (K : ℕ → ℝ) : ℝ :=
  ∑' j, (1 / (1 + ρ * h)) ^ j * (u (consH F h K j) * h)

/-- Admissible period-`h` plans: given initial capital, nonnegative capital, positive
consumption and a convergent welfare series (O&R p. 509). -/
def AdmissibleH (F u : ℝ → ℝ) (ρ h K0 : ℝ) (K : ℕ → ℝ) : Prop :=
  K 0 = K0 ∧ (∀ j, 0 ≤ K j) ∧ (∀ j, 0 < consH F h K j) ∧
    Summable (fun j => (1 / (1 + ρ * h)) ^ j * (u (consH F h K j) * h))

/-- Changing capital at date `j + 1` changes consumption only at dates `j` and `j + 1`. -/
theorem consH_update {F : ℝ → ℝ} {h : ℝ} (K : ℕ → ℝ) (j : ℕ) (e : ℝ) (i : ℕ)
    (hi : i ≠ j) (hi1 : i ≠ j + 1) :
    consH F h (Function.update K (j + 1) (K (j + 1) + e)) i = consH F h K i := by
  unfold consH
  rw [Function.update_of_ne hi1, Function.update_of_ne (by omega)]

/-- **The period-`h` first-order condition is necessary** (O&R p. 509, "maximizing with
respect to `K_{s+h}` gives the necessary first-order condition"): if `K` is an optimal
admissible plan with `K_{j+1} > 0`, and `u`, `F` are differentiable at the relevant points,
then `u'(C_j) = [1 + h F'(K_{j+1})] u'(C_{j+1})/(1 + ρh)`; for `h = 1` this is eq. (20). -/
theorem euler_h_necessary {F u : ℝ → ℝ} {ρ h K0 : ℝ} (hh : 0 < h) (hρ : 0 < 1 + ρ * h)
    {K : ℕ → ℝ} (hK : AdmissibleH F u ρ h K0 K)
    (hopt : ∀ K', AdmissibleH F u ρ h K0 K' → welfareH F u ρ h K' ≤ welfareH F u ρ h K)
    (j : ℕ) (hKj : 0 < K (j + 1)) (hu0 : DifferentiableAt ℝ u (consH F h K j))
    (hu1 : DifferentiableAt ℝ u (consH F h K (j + 1)))
    (hF : DifferentiableAt ℝ F (K (j + 1))) :
    deriv u (consH F h K j) =
      (1 + h * deriv F (K (j + 1))) * deriv u (consH F h K (j + 1)) / (1 + ρ * h) := by
  set β := 1 / (1 + ρ * h)
  have hβ : 0 < β := div_pos one_pos hρ
  set C0 := consH F h K j
  set C1 := consH F h K (j + 1)
  have hC0 : 0 < C0 := hK.2.2.1 j
  have hC1 : 0 < C1 := hK.2.2.1 (j + 1)
  set Ke : ℝ → ℕ → ℝ := fun e => Function.update K (j + 1) (K (j + 1) + e)
  have hKe0 : ∀ e, consH F h (Ke e) j = C0 - e / h := by
    intro e
    simp only [Ke, consH, C0]
    rw [Function.update_of_ne (by omega), Function.update_self]
    ring
  have hKe1 : ∀ e, consH F h (Ke e) (j + 1) = C1 + e / h + F (K (j + 1) + e) - F (K (j + 1)) := by
    intro e
    simp only [Ke, consH, C1]
    rw [Function.update_self, Function.update_of_ne (by omega)]
    ring
  set φ : ℝ → ℝ := fun e =>
    u (C0 - e / h) + β * u (C1 + e / h + F (K (j + 1) + e) - F (K (j + 1)))
  set T : (ℕ → ℝ) → ℕ → ℝ := fun K' i => β ^ i * (u (consH F h K' i) * h)
  -- the welfare change is supported on dates `j`, `j + 1`
  have hsupp : ∀ e, ∀ i ∉ ({j, j + 1} : Finset ℕ), T (Ke e) i - T K i = 0 := by
    intro e i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    simp only [T, Ke, consH_update K j e i hi.1 hi.2, sub_self]
  have hTs : Summable (T K) := hK.2.2.2
  have hWdiff : ∀ e, Summable (T (Ke e)) ∧
      welfareH F u ρ h (Ke e) - welfareH F u ρ h K = β ^ j * h * (φ e - φ 0) := by
    intro e
    have hD : Summable (fun i => T (Ke e) i - T K i) :=
      summable_of_ne_finset_zero (hsupp e)
    have hsum : Summable (T (Ke e)) := (hD.add hTs).congr (fun i => by ring)
    refine ⟨hsum, ?_⟩
    have h1 : welfareH F u ρ h (Ke e) - welfareH F u ρ h K = ∑' i, (T (Ke e) i - T K i) :=
      (hsum.tsum_sub hTs).symm
    rw [h1, tsum_eq_sum (hsupp e), Finset.sum_pair (by omega)]
    simp only [T, hKe0, hKe1, φ, zero_div, sub_zero, add_zero, add_sub_cancel_right]
    have e0 : consH F h K j = C0 := rfl
    have e1 : consH F h K (j + 1) = C1 := rfl
    rw [e0, e1, pow_succ]
    ring
  -- `φ` has a local maximum at `0`
  have hloc : IsLocalMax φ 0 := by
    have hFe : ContinuousAt (fun e => F (K (j + 1) + e)) 0 := by
      have h1 : ContinuousAt (fun e : ℝ => K (j + 1) + e) 0 :=
        continuousAt_const.add continuousAt_id
      have h2 : ContinuousAt F (K (j + 1) + 0) := by simpa using hF.continuousAt
      exact h2.comp h1
    have hFc : ContinuousAt (fun e => C1 + e / h + F (K (j + 1) + e) - F (K (j + 1))) 0 :=
      ((continuousAt_const.add (continuousAt_id.div_const h)).add hFe).sub continuousAt_const
    have hC1e : ∀ᶠ e in 𝓝 (0 : ℝ), 0 < C1 + e / h + F (K (j + 1) + e) - F (K (j + 1)) := by
      have := hFc.eventually (lt_mem_nhds (show 0 < C1 + 0 / h + F (K (j + 1) + 0) -
        F (K (j + 1)) by simpa using hC1))
      exact this
    have hC0e : ∀ᶠ e in 𝓝 (0 : ℝ), 0 < C0 - e / h := by
      have hc : ContinuousAt (fun e => C0 - e / h) 0 :=
        continuousAt_const.sub (continuousAt_id.div_const h)
      exact hc.eventually (lt_mem_nhds (by simpa using hC0))
    have hKe : ∀ᶠ e in 𝓝 (0 : ℝ), 0 < K (j + 1) + e := by
      have hc : ContinuousAt (fun e => K (j + 1) + e) 0 := continuousAt_const.add continuousAt_id
      exact hc.eventually (lt_mem_nhds (by simpa using hKj))
    filter_upwards [hC1e, hC0e, hKe] with e h1 h0 hk
    have hadm : AdmissibleH F u ρ h K0 (Ke e) := by
      refine ⟨?_, fun i => ?_, fun i => ?_, (hWdiff e).1⟩
      · simp only [Ke]; rw [Function.update_of_ne (by omega)]; exact hK.1
      · simp only [Ke]
        by_cases hi : i = j + 1
        · subst hi; rw [Function.update_self]; exact hk.le
        · rw [Function.update_of_ne hi]; exact hK.2.1 i
      · by_cases hi : i = j
        · subst hi; rw [hKe0]; exact h0
        · by_cases hi1 : i = j + 1
          · subst hi1; rw [hKe1]; exact h1
          · rw [consH_update K j e i hi hi1]; exact hK.2.2.1 i
    have hle := hopt _ hadm
    have hw := (hWdiff e).2
    have hpos : 0 < β ^ j * h := mul_pos (pow_pos hβ j) hh
    have : β ^ j * h * (φ e - φ 0) ≤ 0 := by linarith
    by_contra hcon
    push Not at hcon
    have := mul_pos hpos (sub_pos.mpr hcon)
    linarith
  -- the derivative of `φ` at `0`
  have hd0 : HasDerivAt (fun e => u (C0 - e / h)) (deriv u C0 * (-(1 / h))) 0 := by
    have hin : HasDerivAt (fun e : ℝ => C0 - e / h) (-(1 / h)) 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).div_const h).const_sub C0
      simpa [neg_div] using this
    have hu0' : HasDerivAt u (deriv u C0) (C0 - 0 / h) := by
      simpa using hu0.hasDerivAt
    exact hu0'.comp 0 hin
  have hd1 : HasDerivAt (fun e => u (C1 + e / h + F (K (j + 1) + e) - F (K (j + 1))))
      (deriv u C1 * (1 / h + deriv F (K (j + 1)))) 0 := by
    have hin : HasDerivAt (fun e : ℝ => C1 + e / h + F (K (j + 1) + e) - F (K (j + 1)))
        (1 / h + deriv F (K (j + 1))) 0 := by
      have hFd : HasDerivAt (fun e => F (K (j + 1) + e)) (deriv F (K (j + 1))) 0 := by
        have h2 : HasDerivAt F (deriv F (K (j + 1))) (K (j + 1) + 0) := by
          simpa using hF.hasDerivAt
        exact HasDerivAt.comp_const_add (K (j + 1)) 0 h2
      have := ((((hasDerivAt_id' (0 : ℝ)).div_const h).const_add C1).add hFd).sub_const
        (F (K (j + 1)))
      refine this.congr_deriv ?_
      ring
    have hu1' : HasDerivAt u (deriv u C1)
        (C1 + 0 / h + F (K (j + 1) + 0) - F (K (j + 1))) := by
      simpa using hu1.hasDerivAt
    exact hu1'.comp 0 hin
  have hφd := hd0.add (hd1.const_mul β)
  have h0 := hloc.hasDerivAt_eq_zero hφd
  have hβρ : β * (1 + ρ * h) = 1 := by simp only [β]; field_simp
  have key : deriv u C0 * (1 / h) = β * (deriv u C1 * (1 / h + deriv F (K (j + 1)))) := by
    linarith
  have hh' := ne_of_gt hh
  have key2 : deriv u C0 = β * (deriv u C1 * (1 + h * deriv F (K (j + 1)))) := by
    calc deriv u C0 = (deriv u C0 * (1 / h)) * h := by field_simp
      _ = β * (deriv u C1 * (1 / h + deriv F (K (j + 1)))) * h := by rw [key]
      _ = β * (deriv u C1 * (1 + h * deriv F (K (j + 1)))) := by field_simp
  rw [eq_div_iff (ne_of_gt hρ), key2]
  linear_combination (deriv u C1 * (1 + h * deriv F (K (j + 1)))) * hβρ

/-- **The difference-quotient form of the period-`h` Euler equation** (O&R p. 510):
`u'(C_s) = [1 + hF'(K_{s+h})] u'(C_{s+h})/(1 + ρh)` is equivalent to
`[u'(C_{s+h}) - u'(C_s)]/h = [ρ/(1 + ρh) - F'(K_{s+h})/(1 + ρh)] u'(C_{s+h})`. -/
theorem euler_h_difference_form {ρ h m0 m1 Fp : ℝ} (hh : h ≠ 0) (hρ : 1 + ρ * h ≠ 0) :
    m0 = (1 + h * Fp) * m1 / (1 + ρ * h) ↔
      (m1 - m0) / h = (ρ / (1 + ρ * h) - Fp / (1 + ρ * h)) * m1 := by
  have hρ' : 1 + h * ρ ≠ 0 := by rwa [mul_comm] at hρ
  constructor
  · intro h0
    rw [h0]
    field_simp
    ring
  · intro h1
    field_simp at h1
    rw [eq_div_iff hρ]
    linear_combination -h1

/-- The period-`h` Euler residual:
`R_h(s) = [u'(C(s+h)) - u'(C(s))]/h - [ρ - F'(K(s+h))]/(1 + ρh) · u'(C(s+h))`. -/
noncomputable def eulerResidual (F u C K : ℝ → ℝ) (ρ s h : ℝ) : ℝ :=
  (deriv u (C (s + h)) - deriv u (C s)) / h -
    (ρ - deriv F (K (s + h))) / (1 + ρ * h) * deriv u (C (s + h))

/-- **The `h → 0` limit of the Euler equation** (O&R p. 510, "taking the limit of both sides
as `h → 0` yields (by the chain rule)"): for a differentiable consumption path, with `u'`
differentiable at `C(s)` and `F' ∘ K`, `u' ∘ C` continuous at `s`, the period-`h` Euler residual
converges to `u''(C(s)) Ċ(s) - [ρ - F'(K(s))] u'(C(s))`. -/
theorem eulerResidual_tendsto {F u C K : ℝ → ℝ} {ρ s Cdot u2 : ℝ}
    (hC : HasDerivAt C Cdot s) (hu2 : HasDerivAt (deriv u) u2 (C s))
    (hFK : ContinuousAt (fun t => deriv F (K t)) s) :
    Tendsto (fun h => eulerResidual F u C K ρ s h) (𝓝[≠] 0)
      (𝓝 (u2 * Cdot - (ρ - deriv F (K s)) * deriv u (C s))) := by
  have hm : HasDerivAt (fun t => deriv u (C t)) (u2 * Cdot) s := hu2.comp s hC
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hm
  have huc : ContinuousAt (fun t => deriv u (C t)) s := hm.continuousAt
  have hshift : Tendsto (fun h : ℝ => s + h) (𝓝[≠] 0) (𝓝 s) := by
    have hc : Continuous (fun h : ℝ => s + h) := by fun_prop
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
  have h1 := huc.tendsto.comp hshift
  have h2 := hFK.tendsto.comp hshift
  have h3 : Tendsto (fun h : ℝ => 1 + ρ * h) (𝓝[≠] 0) (𝓝 1) := by
    have hc : Continuous (fun h : ℝ => 1 + ρ * h) := by fun_prop
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
  have hlim := hslope.sub ((((tendsto_const_nhds (x := ρ)).sub h2).div h3 one_ne_zero).mul h1)
  rw [div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [eulerResidual, Function.comp_apply, Pi.div_apply]
  rw [smul_eq_mul, inv_mul_eq_div]

/-- **Consequence**: if a smooth path satisfies the period-`h` Euler equation for a sequence
of period lengths `h_n → 0` (`h_n ≠ 0`), then it satisfies the continuous-time Euler equation
`u''(C) Ċ = [ρ - F'(K)] u'(C)` at `s` (O&R p. 510). -/
theorem continuous_euler_of_discrete {F u C K : ℝ → ℝ} {ρ s Cdot u2 : ℝ}
    (hC : HasDerivAt C Cdot s) (hu2 : HasDerivAt (deriv u) u2 (C s))
    (hFK : ContinuousAt (fun t => deriv F (K t)) s) {hs : ℕ → ℝ}
    (hlim : Tendsto hs atTop (𝓝[≠] 0)) (hzero : ∀ n, eulerResidual F u C K ρ s (hs n) = 0) :
    u2 * Cdot = (ρ - deriv F (K s)) * deriv u (C s) := by
  have := (eulerResidual_tendsto (ρ := ρ) hC hu2 hFK).comp hlim
  have h0 : Tendsto (fun n => eulerResidual F u C K ρ s (hs n)) atTop (𝓝 0) := by
    simp only [hzero]; exact tendsto_const_nhds
  have := tendsto_nhds_unique this h0
  linarith

/-- **The Hamiltonian conditions** (O&R p. 510): with `H = u(C) + λ[F(K) - C]`, the conditions
`∂H/∂C = 0` (`λ = u'(C)` along the path) and `λ̇ = δλ - ∂H/∂K = λ[δ - F'(K)]`, together with
the chain rule, give `u''(C) Ċ = [δ - F'(K)] u'(C)`, the same equation as the discrete-time
limit. -/
theorem hamiltonian_euler {F u C K lam : ℝ → ℝ} {ρ s Cdot u2 : ℝ}
    (hlam : ∀ t, lam t = deriv u (C t)) (hC : HasDerivAt C Cdot s)
    (hu2 : HasDerivAt (deriv u) u2 (C s))
    (hcostate : HasDerivAt lam (lam s * (ρ - deriv F (K s))) s) :
    u2 * Cdot = (ρ - deriv F (K s)) * deriv u (C s) := by
  have h1 : HasDerivAt lam (u2 * Cdot) s := by
    have : lam = fun t => deriv u (C t) := funext hlam
    rw [this]; exact hu2.comp s hC
  have := h1.unique hcostate
  rw [this, hlam s]
  ring

/-- For `h = 1` the period-`h` Euler equation is eq. (20) (O&R p. 509, with `β = 1/(1+ρ)`). -/
theorem euler_h_one {ρ m0 m1 Fp : ℝ} :
    m0 = (1 + 1 * Fp) * m1 / (1 + ρ * 1) ↔ m0 = (1 + Fp) * (1 / (1 + ρ)) * m1 := by
  constructor <;> intro h <;> rw [h] <;> ring

/-! ## Period-`h` dynamics converge to the continuous-time system (O&R p. 510, made precise) -/

/-- **Convergence of one-step schemes on compact time intervals** (the precise content of
"dividing by `h` and taking the limit"): let `x` solve `ẋ = Φ(x)` on `[0, T]`, let `Φ` be
`L`-Lipschitz on the tube of radius `r > 0` around the trajectory, let the period-`h` maps be
`X ↦ X + h Φ_h(X)` with `Φ_h → Φ` uniformly on the tube, and let initial conditions converge.
Then `max_{jh ≤ T} ‖X^h_j - x(jh)‖ → 0` as `h → 0⁺`, along any filter `l ≤ 𝓝[>] 0` (so
along any sequence `h_m → 0⁺`) on which the initial conditions converge. -/
theorem one_step_scheme_converges_along {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → E} {Φh : ℝ → E → E} {x : ℝ → E} {T L r : ℝ} {l : Filter ℝ} (hl : l ≤ 𝓝[>] 0)
    (hT : 0 ≤ T) (hr : 0 < r)
    (hL : 0 ≤ L) (hx : ∀ t ∈ Icc 0 T, HasDerivWithinAt x (Φ (x t)) (Icc 0 T) t)
    (hΦc : ContinuousOn (fun t => Φ (x t)) (Icc 0 T))
    (hLip : ∀ y, ∀ t ∈ Icc 0 T, ‖y - x t‖ ≤ r → ‖Φ y - Φ (x t)‖ ≤ L * ‖y - x t‖)
    (hcons : ∀ ε > 0, ∀ᶠ h in 𝓝[>] 0, ∀ y, ∀ t ∈ Icc 0 T, ‖y - x t‖ ≤ r → ‖Φh h y - Φ y‖ ≤ ε)
    {X : ℝ → ℕ → E} (hX : ∀ h j, X h (j + 1) = X h j + h • Φh h (X h j))
    (hX0 : Tendsto (fun h => X h 0) l (𝓝 (x 0))) :
    ∀ ε > 0, ∀ᶠ h in l, ∀ j : ℕ, (j : ℝ) * h ≤ T → ‖X h j - x (j * h)‖ ≤ ε := by
  intro ε hε
  set E0 := Real.exp (L * T)
  have hE0 : 1 ≤ E0 := Real.one_le_exp (mul_nonneg hL hT)
  set m := min ε r
  have hm : 0 < m := lt_min hε hr
  set e0 := m / (2 * E0)
  set cε := m / (2 * E0 * (T + 1))
  have he0 : 0 < e0 := by positivity
  have hcε : 0 < cε := by positivity
  -- uniform continuity of `Φ ∘ x` on `[0, T]`
  have huc := (isCompact_Icc.uniformContinuousOn_of_continuous hΦc)
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff_le.mp huc (cε / 2) (by positivity)
  have hev0 : ∀ᶠ h in l, ‖X h 0 - x 0‖ ≤ e0 := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hX0).eventually (ge_mem_nhds he0)
    filter_upwards [this] with h hh using hh
  have hevI : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo 0 δ := Ioo_mem_nhdsGT hδ
  have hevδ : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < δ ∧ 0 < h := hevI.mono fun h hh => ⟨hh.2, hh.1⟩
  filter_upwards [hev0, hl hevδ, hl (hcons (cε / 2) (by positivity))] with h h0 ⟨hhδ, hh⟩ hc
  -- local truncation error
  have htrunc : ∀ t, 0 ≤ t → t + h ≤ T →
      ‖x (t + h) - x t - h • Φ (x t)‖ ≤ cε / 2 * h := by
    intro t ht0 hth
    have hsub : Icc t (t + h) ⊆ Icc 0 T := fun s hs => ⟨ht0.trans hs.1, hs.2.trans hth⟩
    have hd : ∀ s ∈ Icc t (t + h), HasDerivWithinAt (fun s => x s - s • Φ (x t))
        (Φ (x s) - Φ (x t)) (Icc t (t + h)) s := by
      intro s hs
      have h1 := (hx s (hsub hs)).mono hsub
      have h2 := ((hasDerivAt_id s).smul_const (Φ (x t))).hasDerivWithinAt (s := Icc t (t + h))
      exact (h1.sub h2).congr_deriv (by simp)
    have hb : ∀ s ∈ Ico t (t + h), ‖Φ (x s) - Φ (x t)‖ ≤ cε / 2 := by
      intro s hs
      have := hδu s (hsub (Ico_subset_Icc_self hs)) t (hsub ⟨le_rfl, by linarith⟩)
        (by rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]; linarith [hs.2])
      rwa [dist_eq_norm] at this
    have := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (t + h) ⟨by linarith, le_rfl⟩
    simp only [add_sub_cancel_left] at this
    convert this using 2
    rw [add_smul]; abel
  -- the discrete Gronwall bound, keeping the scheme inside the tube
  set c := cε
  have hbound : ∀ j : ℕ, (j : ℝ) * h ≤ T →
      ‖X h j - x (j * h)‖ ≤ (1 + h * L) ^ j * ‖X h 0 - x 0‖ + j * h * (1 + h * L) ^ j * c := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hj' : (j : ℝ) * h ≤ T := by push_cast at hj; nlinarith
      have ihj := ih hj'
      have hpow : (1 + h * L) ^ j ≤ E0 := by
        calc (1 + h * L) ^ j ≤ Real.exp (h * L) ^ j :=
              pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (h * L)]) j
          _ = Real.exp (L * (j * h)) := by rw [← Real.exp_nat_mul]; ring_nf
          _ ≤ E0 := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hj' hL)
      have hej : ‖X h j - x (j * h)‖ ≤ r := by
        have h1 : (1 + h * L) ^ j * ‖X h 0 - x 0‖ ≤ E0 * e0 :=
          mul_le_mul hpow h0 (norm_nonneg _) (by linarith)
        have h2 : (j : ℝ) * h * (1 + h * L) ^ j * c ≤ T * E0 * c := by
          have := mul_le_mul hj' hpow (by positivity) hT
          exact mul_le_mul_of_nonneg_right this hcε.le
        have h3 : E0 * e0 = m / 2 := by simp only [e0]; field_simp
        have h4 : T * E0 * c ≤ m / 2 := by
          simp only [c, cε]; rw [show T * E0 * (m / (2 * E0 * (T + 1))) = m / 2 * (T / (T + 1)) by
            field_simp]
          have : T / (T + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
          nlinarith
        have : m ≤ r := min_le_right _ _
        linarith
      have htj : (j : ℝ) * h ∈ Icc 0 T := ⟨by positivity, hj'⟩
      have hcast : ((j + 1 : ℕ) : ℝ) * h = j * h + h := by push_cast; ring
      rw [hX, hcast]
      have hstep := htrunc (j * h) (by positivity) (by rw [← hcast]; exact hj)
      have hlip := hLip (X h j) _ htj hej
      have hcon := hc (X h j) _ htj hej
      have hsplit : X h j + h • Φh h (X h j) - x (j * h + h) =
          (X h j - x (j * h)) + h • (Φh h (X h j) - Φ (X h j)) +
            h • (Φ (X h j) - Φ (x (j * h))) - (x (j * h + h) - x (j * h) - h • Φ (x (j * h))) := by
        simp only [smul_sub]; abel
      rw [hsplit]
      have hn1 : ‖h • (Φh h (X h j) - Φ (X h j))‖ ≤ h * (c / 2) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
        exact mul_le_mul_of_nonneg_left hcon hh.le
      have hn2 : ‖h • (Φ (X h j) - Φ (x (j * h)))‖ ≤ h * (L * ‖X h j - x (j * h)‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
        exact mul_le_mul_of_nonneg_left hlip hh.le
      have htri : ‖(X h j - x (j * h)) + h • (Φh h (X h j) - Φ (X h j)) +
          h • (Φ (X h j) - Φ (x (j * h))) - (x (j * h + h) - x (j * h) - h • Φ (x (j * h)))‖ ≤
          ‖X h j - x (j * h)‖ + h * (c / 2) + h * (L * ‖X h j - x (j * h)‖) + c / 2 * h := by
        refine (norm_sub_le _ _).trans ?_
        have := norm_add₃_le (a := X h j - x (j * h)) (b := h • (Φh h (X h j) - Φ (X h j)))
          (c := h • (Φ (X h j) - Φ (x (j * h))))
        linarith
      refine htri.trans ?_
      have hpow1 : (1 + h * L) ^ j ≤ (1 + h * L) ^ (j + 1) :=
        pow_le_pow_right₀ (by nlinarith) (Nat.le_succ j)
      have hq : 1 ≤ (1 + h * L) ^ (j + 1) := one_le_pow₀ (by nlinarith)
      have e1 := mul_le_mul_of_nonneg_left ihj (by nlinarith : (0 : ℝ) ≤ 1 + h * L)
      have e2 : (1 + h * L) * ((j : ℝ) * h * (1 + h * L) ^ j * c) =
          j * h * (1 + h * L) ^ (j + 1) * c := by ring
      have e3 : (1 + h * L) * ((1 + h * L) ^ j * ‖X h 0 - x 0‖) =
          (1 + h * L) ^ (j + 1) * ‖X h 0 - x 0‖ := by ring
      have e4 : h * c ≤ h * (1 + h * L) ^ (j + 1) * c := by
        have := mul_le_mul_of_nonneg_left hq (mul_pos hh hcε).le
        nlinarith
      nlinarith
  intro j hj
  have hpow : (1 + h * L) ^ j ≤ E0 := by
    calc (1 + h * L) ^ j ≤ Real.exp (h * L) ^ j :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (h * L)]) j
      _ = Real.exp (L * (j * h)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ E0 := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hj hL)
  have h1 : (1 + h * L) ^ j * ‖X h 0 - x 0‖ ≤ E0 * e0 :=
    mul_le_mul hpow h0 (norm_nonneg _) (by linarith)
  have h2 : (j : ℝ) * h * (1 + h * L) ^ j * c ≤ T * E0 * c := by
    have := mul_le_mul hj hpow (by positivity) hT
    exact mul_le_mul_of_nonneg_right this hcε.le
  have h3 : E0 * e0 = m / 2 := by simp only [e0]; field_simp
  have h4 : T * E0 * c ≤ m / 2 := by
    simp only [c, cε]; rw [show T * E0 * (m / (2 * E0 * (T + 1))) = m / 2 * (T / (T + 1)) by
      field_simp]
    have : T / (T + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  have : m ≤ ε := min_le_left _ _
  linarith [hbound j hj]

/-- **Convergence of one-step schemes on compact time intervals** (O&R Appendix 7A, "dividing
by `h` and taking the limit"): the case `l = 𝓝[>] 0` of `one_step_scheme_converges_along`. -/
theorem one_step_scheme_converges {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → E} {Φh : ℝ → E → E} {x : ℝ → E} {T L r : ℝ} (hT : 0 ≤ T) (hr : 0 < r)
    (hL : 0 ≤ L) (hx : ∀ t ∈ Icc 0 T, HasDerivWithinAt x (Φ (x t)) (Icc 0 T) t)
    (hΦc : ContinuousOn (fun t => Φ (x t)) (Icc 0 T))
    (hLip : ∀ y, ∀ t ∈ Icc 0 T, ‖y - x t‖ ≤ r → ‖Φ y - Φ (x t)‖ ≤ L * ‖y - x t‖)
    (hcons : ∀ ε > 0, ∀ᶠ h in 𝓝[>] 0, ∀ y, ∀ t ∈ Icc 0 T, ‖y - x t‖ ≤ r → ‖Φh h y - Φ y‖ ≤ ε)
    {X : ℝ → ℕ → E} (hX : ∀ h j, X h (j + 1) = X h j + h • Φh h (X h j))
    (hX0 : Tendsto (fun h => X h 0) (𝓝[>] 0) (𝓝 (x 0))) :
    ∀ ε > 0, ∀ᶠ h in 𝓝[>] 0, ∀ j : ℕ, (j : ℝ) * h ≤ T → ‖X h j - x (j * h)‖ ≤ ε :=
  one_step_scheme_converges_along le_rfl hT hr hL hx hΦc hLip hcons hX hX0

/-- The continuous-time Ramsey system with log utility (O&R p. 510 with `u = log`):
`K̇ = F(K) - C`, `Ċ = C [F'(K) - ρ]`. -/
noncomputable def ramseyField (F : ℝ → ℝ) (ρ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (F p.1 - p.2, p.2 * (deriv F p.1 - ρ))

/-- The period-`h` Ramsey system (O&R p. 509 with `u = log`) written as `X + h Φ_h(X)`. -/
noncomputable def ramseyFieldH (F : ℝ → ℝ) (ρ h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (F p.1 - p.2, p.2 * (deriv F (p.1 + h * (F p.1 - p.2)) - ρ) / (1 + ρ * h))

/-- **The period-`h` Ramsey equations are a one-step scheme** (O&R p. 509, `u = log`): with
`K_{s+h} = K_s + h[F(K_s) - C_s]` and the period-`h` Euler equation
`1/C_s = [1 + h F'(K_{s+h})]/((1 + ρh) C_{s+h})`, the state moves by `h Φ_h`. -/
theorem period_h_ramsey_step (F : ℝ → ℝ) {ρ h K C K' C' : ℝ} (hρh : 0 < 1 + ρ * h)
    (hC : 0 < C) (hC' : 0 < C') (hK' : K' = K + h * (F K - C))
    (heuler : 1 / C = (1 + h * deriv F K') / ((1 + ρ * h) * C')) :
    (K', C') = (K, C) + h • ramseyFieldH F ρ h (K, C) := by
  have hC'e : C' = C * (1 + h * deriv F K') / (1 + ρ * h) := by
    field_simp at heuler ⊢; linarith
  simp only [ramseyFieldH, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, ← hK']
  refine Prod.ext ?_ ?_
  · simp only
  · have hρh' : 1 + h * ρ ≠ 0 := by rw [mul_comm]; exact ne_of_gt hρh
    simp only; rw [hC'e]; field_simp; ring

/-- **The period-`h` Euler dynamics converge to the Ramsey ODE on compact intervals**
(O&R p. 510, made precise for `u = log`): if `(K, C)` solves `K̇ = F(K) - C`,
`Ċ = C[F'(K) - ρ]` on `[0, T]` with `K` in `[a + 2r, b - 2r]`, `F` and `F'` Lipschitz on
`[a, b]` and `ρ ≥ 0`, then the period-`h` paths (feasibility plus the period-`h` Euler
equation) started from initial conditions converging to `(K₀, C₀)` converge to the solution
uniformly on `[0, T]` as `h → 0⁺`, along any filter `l ≤ 𝓝[>] 0`. -/
theorem ramsey_period_h_converges_along (F : ℝ → ℝ) {ρ T a b r LF LF' : ℝ} {l : Filter ℝ}
    (hl : l ≤ 𝓝[>] 0) (hρ : 0 ≤ ρ)
    (hT : 0 ≤ T) (hr : 0 < r) (hLF : 0 ≤ LF) (hLF' : 0 ≤ LF')
    (hFL : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |F u - F v| ≤ LF * |u - v|)
    (hF'L : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |deriv F u - deriv F v| ≤ LF' * |u - v|)
    {K C : ℝ → ℝ}
    (hsol : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => (K t, C t))
      (ramseyField F ρ (K t, C t)) (Icc 0 T) t)
    (hKr : ∀ t ∈ Icc 0 T, a + 2 * r ≤ K t ∧ K t ≤ b - 2 * r)
    {X : ℝ → ℕ → ℝ × ℝ} (hX : ∀ h j, X h (j + 1) = X h j + h • ramseyFieldH F ρ h (X h j))
    (hX0 : Tendsto (fun h => X h 0) l (𝓝 (K 0, C 0))) :
    ∀ ε > 0, ∀ᶠ h in l, ∀ j : ℕ, (j : ℝ) * h ≤ T →
      ‖X h j - (K (j * h), C (j * h))‖ ≤ ε := by
  set x : ℝ → ℝ × ℝ := fun t => (K t, C t)
  have hxc : ContinuousOn x (Icc 0 T) := fun t ht => (hsol t ht).continuousWithinAt
  have hCc : ContinuousOn C (Icc 0 T) := continuous_snd.comp_continuousOn hxc
  obtain ⟨Cb, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn hCc
  have hFc : ContinuousOn F (Icc a b) :=
    (LipschitzOnWith.of_dist_le' (K := LF) (fun u hu v hv => by
      simpa [Real.dist_eq] using hFL u hu v hv)).continuousOn
  have hF'c : ContinuousOn (deriv F) (Icc a b) :=
    (LipschitzOnWith.of_dist_le' (K := LF') (fun u hu v hv => by
      simpa [Real.dist_eq] using hF'L u hu v hv)).continuousOn
  -- bounds on `[a, b]`
  obtain ⟨BF, hBF⟩ := isCompact_Icc.exists_bound_of_continuousOn hFc
  obtain ⟨BF', hBF'⟩ := isCompact_Icc.exists_bound_of_continuousOn hF'c
  have hab : ∀ t ∈ Icc 0 T, ∀ y : ℝ × ℝ, ‖y - x t‖ ≤ r →
      y.1 ∈ Icc a b ∧ |y.2| ≤ |Cb| + r := by
    intro t ht y hy
    have h1 : |y.1 - K t| ≤ r := by
      have := (norm_prod_le_iff.mp hy).1; simpa [x, Real.norm_eq_abs] using this
    have h2 : |y.2 - C t| ≤ r := by
      have := (norm_prod_le_iff.mp hy).2; simpa [x, Real.norm_eq_abs] using this
    have h3 := hCb t ht
    rw [Real.norm_eq_abs] at h3
    obtain ⟨hk1, hk2⟩ := hKr t ht
    rw [abs_le] at h1 h2
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rw [abs_le]; constructor <;> linarith [neg_abs_le Cb,
      le_abs_self Cb, (abs_le.mp h3).1, (abs_le.mp h3).2]
  set Cm := |Cb| + r
  set L := LF + 1 + Cm * LF' + (|BF'| + ρ)
  have hLpos : 0 ≤ L := by positivity
  refine one_step_scheme_converges_along hl hT hr hLpos hsol ?_ ?_ ?_ hX hX0
  · -- continuity of `Φ ∘ x`
    have hKmap : MapsTo K (Icc 0 T) (Icc a b) := fun t ht =>
      ⟨by linarith [(hKr t ht).1], by linarith [(hKr t ht).2]⟩
    have hKc : ContinuousOn K (Icc 0 T) := continuous_fst.comp_continuousOn hxc
    have h1 : ContinuousOn (fun t => F (K t)) (Icc 0 T) := hFc.comp hKc hKmap
    have h2 : ContinuousOn (fun t => deriv F (K t)) (Icc 0 T) := hF'c.comp hKc hKmap
    exact (h1.sub hCc).prodMk (hCc.mul (h2.sub continuousOn_const))
  · -- Lipschitz bound along the tube
    intro y t ht hy
    obtain ⟨hy1, hy2⟩ := hab t ht y hy
    have hKt : K t ∈ Icc a b := ⟨by linarith [(hKr t ht).1], by linarith [(hKr t ht).2]⟩
    have hd1 : |y.1 - K t| ≤ ‖y - x t‖ := by
      have := norm_fst_le (y - x t); simpa [x, Real.norm_eq_abs] using this
    have hd2 : |y.2 - C t| ≤ ‖y - x t‖ := by
      have := norm_snd_le (y - x t); simpa [x, Real.norm_eq_abs] using this
    have hn0 := norm_nonneg (y - x t)
    have hF1 := hFL _ hy1 _ hKt
    have hF2 := hF'L _ hy1 _ hKt
    have hBt : |deriv F (K t) - ρ| ≤ |BF'| + ρ := by
      have := hBF' _ hKt; rw [Real.norm_eq_abs] at this
      calc |deriv F (K t) - ρ| ≤ |deriv F (K t)| + |ρ| := abs_sub _ _
        _ ≤ |BF'| + ρ := by rw [abs_of_nonneg hρ]; linarith [le_abs_self BF']
    rw [norm_prod_le_iff]
    simp only [ramseyField, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
    constructor
    · calc |F y.1 - y.2 - (F (x t).1 - (x t).2)| ≤ |F y.1 - F (K t)| + |y.2 - C t| := by
            simp only [x]
            rw [show F y.1 - y.2 - (F (K t) - C t) = (F y.1 - F (K t)) - (y.2 - C t) by ring]
            exact abs_sub _ _
        _ ≤ LF * ‖y - x t‖ + ‖y - x t‖ := by nlinarith
        _ ≤ L * ‖y - x t‖ := by
            apply le_of_sub_nonneg
            have : 0 ≤ (Cm * LF' + (|BF'| + ρ)) * ‖y - x t‖ := by positivity
            nlinarith
    · calc |y.2 * (deriv F y.1 - ρ) - (x t).2 * (deriv F (x t).1 - ρ)|
          ≤ |y.2| * |deriv F y.1 - deriv F (K t)| + |deriv F (K t) - ρ| * |y.2 - C t| := by
            simp only [x]
            rw [show y.2 * (deriv F y.1 - ρ) - C t * (deriv F (K t) - ρ) =
              y.2 * (deriv F y.1 - deriv F (K t)) + (deriv F (K t) - ρ) * (y.2 - C t) by ring]
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul]
        _ ≤ Cm * (LF' * ‖y - x t‖) + (|BF'| + ρ) * ‖y - x t‖ := by
            apply add_le_add
            · exact mul_le_mul hy2 (hF2.trans (mul_le_mul_of_nonneg_left hd1 hLF'))
                (abs_nonneg _) (by positivity)
            · exact mul_le_mul hBt hd2 (abs_nonneg _) (by positivity)
        _ ≤ L * ‖y - x t‖ := by
            apply le_of_sub_nonneg
            have : 0 ≤ (LF + 1) * ‖y - x t‖ := by positivity
            nlinarith
  · -- uniform consistency on the tube
    intro ε hε
    set B1 := |BF| + Cm
    set B2 := |BF'| + ρ
    have hB1 : 0 ≤ B1 := by positivity
    set hmax := min (r / (B1 + 1)) (ε / (Cm * (LF' * B1 + ρ * B2) + 1))
    have hhmax : 0 < hmax := lt_min (by positivity) (by positivity)
    have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo 0 hmax := Ioo_mem_nhdsGT hhmax
    filter_upwards [hev] with h hh y t ht hy
    obtain ⟨hy1, hy2⟩ := hab t ht y hy
    have hh0 : 0 < h := hh.1
    have hFy : |F y.1 - y.2| ≤ B1 := by
      have := hBF _ hy1; rw [Real.norm_eq_abs] at this
      calc |F y.1 - y.2| ≤ |F y.1| + |y.2| := abs_sub _ _
        _ ≤ B1 := by simp only [B1]; linarith [le_abs_self BF]
    have hK't : |y.1 + h * (F y.1 - y.2) - y.1| ≤ r := by
      rw [add_sub_cancel_left, abs_mul, abs_of_pos hh0]
      have h1 : h ≤ r / (B1 + 1) := hh.2.le.trans (min_le_left _ _)
      rw [le_div_iff₀ (by linarith)] at h1
      nlinarith
    have hy1' : y.1 + h * (F y.1 - y.2) ∈ Icc a b := by
      have hKt := hKr t ht
      have hd1 : |y.1 - K t| ≤ r := by
        have := norm_fst_le (y - x t); simp only [x, Prod.fst_sub, Real.norm_eq_abs] at this
        linarith
      rw [abs_le] at hK't hd1
      exact ⟨by linarith [hKt.1], by linarith [hKt.2]⟩
    have hρh : 1 ≤ 1 + ρ * h := by nlinarith
    rw [norm_prod_le_iff]
    simp only [ramseyFieldH, ramseyField, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero,
      Real.norm_eq_abs]
    refine ⟨hε.le, ?_⟩
    have hdiff := hF'L _ hy1' _ hy1
    have hBy : |deriv F y.1 - ρ| ≤ B2 := by
      have := hBF' _ hy1; rw [Real.norm_eq_abs] at this
      calc |deriv F y.1 - ρ| ≤ |deriv F y.1| + |ρ| := abs_sub _ _
        _ ≤ B2 := by simp only [B2]; rw [abs_of_nonneg hρ]; linarith [le_abs_self BF']
    have e : y.2 * (deriv F (y.1 + h * (F y.1 - y.2)) - ρ) / (1 + ρ * h) -
        y.2 * (deriv F y.1 - ρ) = y.2 * ((deriv F (y.1 + h * (F y.1 - y.2)) - deriv F y.1) -
          ρ * h * (deriv F y.1 - ρ)) / (1 + ρ * h) := by field_simp; ring
    rw [e, abs_div, abs_of_pos (show (0 : ℝ) < 1 + ρ * h by linarith), abs_mul]
    have hnum : |(deriv F (y.1 + h * (F y.1 - y.2)) - deriv F y.1) - ρ * h * (deriv F y.1 - ρ)| ≤
        h * (LF' * B1 + ρ * B2) := by
      have h1 : |deriv F (y.1 + h * (F y.1 - y.2)) - deriv F y.1| ≤ LF' * (h * B1) := by
        refine hdiff.trans (mul_le_mul_of_nonneg_left ?_ hLF')
        rw [add_sub_cancel_left, abs_mul, abs_of_pos hh0]
        exact mul_le_mul_of_nonneg_left hFy hh0.le
      have h2 : |ρ * h * (deriv F y.1 - ρ)| ≤ ρ * h * B2 := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left hBy (by positivity)
      calc _ ≤ |deriv F (y.1 + h * (F y.1 - y.2)) - deriv F y.1| + |ρ * h * (deriv F y.1 - ρ)| :=
            abs_sub _ _
        _ ≤ _ := by nlinarith
    have hh2 : h * (Cm * (LF' * B1 + ρ * B2) + 1) ≤ ε := by
      have := hh.2.le.trans (min_le_right _ _)
      rwa [le_div_iff₀ (by positivity)] at this
    rw [div_le_iff₀ (by linarith)]
    calc |y.2| * |(deriv F (y.1 + h * (F y.1 - y.2)) - deriv F y.1) - ρ * h * (deriv F y.1 - ρ)|
        ≤ Cm * (h * (LF' * B1 + ρ * B2)) := mul_le_mul hy2 hnum (abs_nonneg _) (by positivity)
      _ ≤ ε * 1 := by nlinarith
      _ ≤ ε * (1 + ρ * h) := mul_le_mul_of_nonneg_left hρh hε.le

/-- **The period-`h` Euler dynamics converge to the Ramsey ODE on compact intervals**
(O&R p. 510, `u = log`): the case `l = 𝓝[>] 0` of `ramsey_period_h_converges_along`. -/
theorem ramsey_period_h_converges (F : ℝ → ℝ) {ρ T a b r LF LF' : ℝ} (hρ : 0 ≤ ρ)
    (hT : 0 ≤ T) (hr : 0 < r) (hLF : 0 ≤ LF) (hLF' : 0 ≤ LF')
    (hFL : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |F u - F v| ≤ LF * |u - v|)
    (hF'L : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |deriv F u - deriv F v| ≤ LF' * |u - v|)
    {K C : ℝ → ℝ}
    (hsol : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => (K t, C t))
      (ramseyField F ρ (K t, C t)) (Icc 0 T) t)
    (hKr : ∀ t ∈ Icc 0 T, a + 2 * r ≤ K t ∧ K t ≤ b - 2 * r)
    {X : ℝ → ℕ → ℝ × ℝ} (hX : ∀ h j, X h (j + 1) = X h j + h • ramseyFieldH F ρ h (X h j))
    (hX0 : Tendsto (fun h => X h 0) (𝓝[>] 0) (𝓝 (K 0, C 0))) :
    ∀ ε > 0, ∀ᶠ h in 𝓝[>] 0, ∀ j : ℕ, (j : ℝ) * h ≤ T →
      ‖X h j - (K (j * h), C (j * h))‖ ≤ ε :=
  ramsey_period_h_converges_along F le_rfl hρ hT hr hLF hLF' hFL hF'L hsol hKr hX hX0

/-- **The period-`h` steady state is the continuous one for every `h`** (O&R p. 509): a rest
point of the period-`h` Euler equation with `C > 0` has `F'(K̄) = ρ`, and a rest point of
accumulation has `C̄ = F(K̄)`; so the period-`h` steady state does not depend on `h` and
trivially converges to the continuous-time steady state `F'(K̄) = ρ` of `u''Ċ = (ρ - F')u'`. -/
theorem period_h_ramsey_steady {F u : ℝ → ℝ} {ρ h K C : ℝ} (hh : 0 < h) (hρh : 0 < 1 + ρ * h)
    (hu : 0 < deriv u C) (heuler : deriv u C = (1 + h * deriv F K) * deriv u C / (1 + ρ * h))
    (hacc : K = K + h * F K - h * C) : deriv F K = ρ ∧ C = F K := by
  constructor
  · rw [eq_div_iff (ne_of_gt hρh)] at heuler
    have : deriv u C * (h * (ρ - deriv F K)) = 0 := by linear_combination heuler
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · linarith
      · linarith
  · have : h * (F K - C) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · linarith

/-! ## The continuous-time objective as the limit of period-`h` discounted sums -/

/-- The step function whose integral is the period-`h` discounted sum:
`s ↦ (1/(1+ρh))^{⌊s/h⌋} φ(h ⌊s/h⌋)`. -/
noncomputable def stepH (φ : ℝ → ℝ) (ρ h s : ℝ) : ℝ :=
  (1 / (1 + ρ * h)) ^ ⌊s / h⌋₊ * φ (h * ⌊s / h⌋₊)

/-- The grid point `h ⌊s/h⌋` lies in `(s - h, s]`. -/
theorem grid_bounds {h s : ℝ} (hh : 0 < h) (hs : 0 ≤ s) :
    h * ⌊s / h⌋₊ ≤ s ∧ s - h < h * ⌊s / h⌋₊ := by
  have h1 := Nat.floor_le (div_nonneg hs hh.le)
  have h2 := Nat.lt_floor_add_one (s / h)
  constructor
  · calc h * ⌊s / h⌋₊ ≤ h * (s / h) := mul_le_mul_of_nonneg_left h1 hh.le
      _ = s := by field_simp
  · have := mul_lt_mul_of_pos_left h2 hh
    rw [mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt hh)] at this
    linarith

/-- Discount factors decay exponentially: for `0 < ρh ≤ 1`,
`(1/(1+ρh))^N ≤ exp(-ρhN/2)`. -/
theorem disc_le_exp {ρ h : ℝ} (hρh : 0 < ρ * h) (hρh1 : ρ * h ≤ 1) (N : ℕ) :
    (1 / (1 + ρ * h)) ^ N ≤ Real.exp (-(ρ * h * N / 2)) := by
  have hpos : 0 < 1 + ρ * h := by linarith
  have hlog : ρ * h / 2 ≤ Real.log (1 + ρ * h) := by
    have := Real.one_sub_inv_le_log_of_pos hpos
    have e : 1 - (1 + ρ * h)⁻¹ = ρ * h / (1 + ρ * h) := by field_simp; ring
    rw [e] at this
    have : ρ * h / 2 ≤ ρ * h / (1 + ρ * h) := by
      rw [div_le_div_iff₀ (by norm_num) hpos]; nlinarith
    linarith
  have e : (1 / (1 + ρ * h)) ^ N = Real.exp (-(N * Real.log (1 + ρ * h))) := by
    rw [← Real.exp_log (div_pos one_pos hpos), ← Real.exp_nat_mul, one_div, Real.log_inv]
    ring_nf
  rw [e, Real.exp_le_exp]
  have := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith

/-- **Uniform exponential domination** of the step functions for `0 < h ≤ 1/ρ`. -/
theorem stepH_bound {φ : ℝ → ℝ} {ρ M h s : ℝ} (hρ : 0 < ρ) (hM : ∀ s, |φ s| ≤ M)
    (hh : 0 < h) (hh1 : ρ * h ≤ 1) (hs : 0 ≤ s) :
    |stepH φ ρ h s| ≤ M * Real.exp (1 / 2) * Real.exp (-(ρ / 2) * s) := by
  have hρh : 0 < ρ * h := mul_pos hρ hh
  have hd := disc_le_exp hρh hh1 ⌊s / h⌋₊
  obtain ⟨-, hlow⟩ := grid_bounds hh hs
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  unfold stepH
  rw [abs_mul, abs_of_pos (pow_pos (div_pos one_pos (by linarith)) _)]
  have hexp : Real.exp (-(ρ * h * ⌊s / h⌋₊ / 2)) ≤ Real.exp (1 / 2) * Real.exp (-(ρ / 2) * s) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith
  calc (1 / (1 + ρ * h)) ^ ⌊s / h⌋₊ * |φ (h * ⌊s / h⌋₊)|
      ≤ Real.exp (-(ρ * h * ⌊s / h⌋₊ / 2)) * M :=
        mul_le_mul hd (hM _) (abs_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (1 / 2) * Real.exp (-(ρ / 2) * s) * M := mul_le_mul_of_nonneg_right hexp hM0
    _ = _ := by ring

/-- **Pointwise convergence of the step functions**: for `s ≥ 0`,
`stepH φ ρ h s → e^{-ρs} φ(s)` as `h → 0⁺`. -/
theorem stepH_tendsto {φ : ℝ → ℝ} {ρ s : ℝ} (hφ : Continuous φ) (hs : 0 ≤ s) :
    Tendsto (fun h => stepH φ ρ h s) (𝓝[>] 0) (𝓝 (Real.exp (-ρ * s) * φ s)) := by
  -- grid points converge to `s`
  have hgrid : Tendsto (fun h : ℝ => h * ⌊s / h⌋₊) (𝓝[>] 0) (𝓝 s) := by
    have hlo : Tendsto (fun h : ℝ => s - h) (𝓝[>] 0) (𝓝 s) := by
      have hc : Continuous (fun h : ℝ => s - h) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with h hh using (grid_bounds hh hs).2.le
    · filter_upwards [self_mem_nhdsWithin] with h hh using (grid_bounds hh hs).1
  -- `log(1 + ρh)/h → ρ`
  have hlogd : HasDerivAt (fun h : ℝ => Real.log (1 + ρ * h)) ρ 0 := by
    have h1 : HasDerivAt (fun h : ℝ => 1 + ρ * h) ρ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul ρ).const_add 1
    have := h1.log (by norm_num)
    simpa using this
  have hslope := (hasDerivAt_iff_tendsto_slope_zero.mp hlogd).mono_left
    (nhdsWithin_mono _ (fun h (hh : h ∈ Ioi (0 : ℝ)) => ne_of_gt hh))
  simp only [zero_add, mul_zero, add_zero, Real.log_one, sub_zero, smul_eq_mul] at hslope
  have hprod : Tendsto (fun h : ℝ => (h * ⌊s / h⌋₊) * (h⁻¹ * Real.log (1 + ρ * h))) (𝓝[>] 0)
      (𝓝 (s * ρ)) := hgrid.mul hslope
  have hdisc : Tendsto (fun h : ℝ => (1 / (1 + ρ * h)) ^ ⌊s / h⌋₊) (𝓝[>] 0)
      (𝓝 (Real.exp (-ρ * s))) := by
    have := (Real.continuous_exp.tendsto _).comp hprod.neg
    rw [show -(s * ρ) = -ρ * s by ring] at this
    refine this.congr' ?_
    have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < 1 + ρ * h := by
      have hc : Continuous (fun h : ℝ => 1 + ρ * h) := by fun_prop
      exact ((hc.tendsto 0).mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds (by simp))
    filter_upwards [hev, self_mem_nhdsWithin] with h hpos hh
    have hh' : (0 : ℝ) < h := hh
    simp only [Function.comp_apply]
    rw [← Real.exp_log (div_pos one_pos hpos), ← Real.exp_nat_mul, one_div, Real.log_inv]
    congr 1
    field_simp
  exact hdisc.mul ((hφ.tendsto s).comp hgrid)

/-- **The step-function integral is the period-`h` discounted sum**:
`∫_{[0,∞)} stepH = ∑_j (1/(1+ρh))^j φ(jh) h`. -/
theorem integral_stepH {φ : ℝ → ℝ} {ρ M h : ℝ} (hρ : 0 < ρ) (hφ : Continuous φ)
    (hM : ∀ s, |φ s| ≤ M) (hh : 0 < h) (hh1 : ρ * h ≤ 1) :
    ∫ s in Ici 0, stepH φ ρ h s = ∑' j : ℕ, (1 / (1 + ρ * h)) ^ j * (φ (j * h) * h) := by
  set S : ℕ → Set ℝ := fun j => Ico (j * h) ((j + 1) * h)
  have hU : (⋃ j, S j) = Ici 0 := by
    ext s
    simp only [mem_iUnion, mem_Ico, mem_Ici, S]
    constructor
    · rintro ⟨j, hj, -⟩; exact le_trans (by positivity) hj
    · intro hs
      obtain ⟨h1, h2⟩ := grid_bounds hh hs
      exact ⟨⌊s / h⌋₊, by linarith, by linarith⟩
  have hfloor : ∀ j : ℕ, ∀ s ∈ S j, ⌊s / h⌋₊ = j := by
    intro j s hs
    rw [Nat.floor_eq_iff (div_nonneg (le_trans (by positivity) hs.1) hh.le)]
    constructor
    · rw [le_div_iff₀ hh]; exact hs.1
    · rw [div_lt_iff₀ hh]; linarith [hs.2]
  have hmeas : Measurable (stepH φ ρ h) := by
    unfold stepH
    have hfl : Measurable (fun s : ℝ => ⌊s / h⌋₊) := (measurable_id.div_const h).nat_floor
    exact ((measurable_const.pow hfl)).mul (hφ.measurable.comp
      (measurable_const.mul (measurable_from_nat.comp hfl)))
  have hint : IntegrableOn (stepH φ ρ h) (⋃ j, S j) := by
    rw [hU]
    have hb : IntegrableOn (fun s => M * Real.exp (1 / 2) * Real.exp (-(ρ / 2) * s)) (Ici 0) :=
      ((integrableOn_Ici_iff_integrableOn_Ioi).mpr (exp_neg_integrableOn_Ioi 0
        (by positivity))).const_mul _
    refine hb.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    rw [Real.norm_eq_abs]
    exact stepH_bound hρ hM hh hh1 hs
  rw [← hU, integral_iUnion (fun j => measurableSet_Ico) ?_ hint]
  · congr 1; ext j
    rw [setIntegral_congr_fun measurableSet_Ico (g := fun _ => (1 / (1 + ρ * h)) ^ j * φ (j * h))
      (fun s hs => by simp only [stepH, hfloor j s hs]; ring_nf), setIntegral_const,
      Real.volume_real_Ico_of_le (by nlinarith), smul_eq_mul]
    ring
  · intro i j hij
    simp only [Function.onFun]
    rw [Set.disjoint_iff]
    rintro s ⟨hi, hj⟩
    have := (hfloor i s hi).symm.trans (hfloor j s hj)
    exact hij this

/-- **The continuous-time objective is the limit of the period-`h` objectives** (O&R p. 510,
"in continuous time the dynasty's objective becomes `∫ u(C) e^{-ρ(s-t)} ds`", made precise):
for a continuous bounded flow utility `φ(s) = u(C(s))` and `ρ > 0`,
`∑_j (1/(1+ρh))^j φ(jh) h → ∫_0^∞ e^{-ρs} φ(s) ds` as `h → 0⁺`. -/
theorem discounted_sum_tendsto_integral {φ : ℝ → ℝ} {ρ M : ℝ} (hρ : 0 < ρ)
    (hφ : Continuous φ) (hM : ∀ s, |φ s| ≤ M) :
    Tendsto (fun h => ∑' j : ℕ, (1 / (1 + ρ * h)) ^ j * (φ (j * h) * h)) (𝓝[>] 0)
      (𝓝 (∫ s in Ici 0, Real.exp (-ρ * s) * φ s)) := by
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo 0 (1 / ρ) := Ioo_mem_nhdsGT (by positivity)
  have hlim : Tendsto (fun h => ∫ s in Ici 0, stepH φ ρ h s) (𝓝[>] 0)
      (𝓝 (∫ s in Ici 0, Real.exp (-ρ * s) * φ s)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun s => M * Real.exp (1 / 2) * Real.exp (-(ρ / 2) * s)) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall (fun h => ?_)
      unfold stepH
      have hfl : Measurable (fun s : ℝ => ⌊s / h⌋₊) := (measurable_id.div_const h).nat_floor
      exact (((measurable_const.pow hfl)).mul (hφ.measurable.comp
        (measurable_const.mul (measurable_from_nat.comp hfl)))).aestronglyMeasurable
    · filter_upwards [hev] with h hh
      filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
      rw [Real.norm_eq_abs]
      have hh1 : ρ * h ≤ 1 := by
        have := hh.2; rw [lt_div_iff₀ hρ] at this; linarith
      exact stepH_bound hρ hM hh.1 hh1 hs
    · exact ((integrableOn_Ici_iff_integrableOn_Ioi).mpr (exp_neg_integrableOn_Ioi 0
        (by positivity))).const_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
      exact stepH_tendsto hφ hs
  refine hlim.congr' ?_
  filter_upwards [hev] with h hh
  have hh1 : ρ * h ≤ 1 := by have := hh.2; rw [lt_div_iff₀ hρ] at this; linarith
  exact integral_stepH hρ hφ hM hh.1 hh1


/-! ## The isoelastic period-`h` Ramsey model as a one-step scheme -/

/-- **First-order expansion of `(1 + x)^p` at `0`** (used for the isoelastic period-`h` Euler
equation, O&R p. 509 with (21)): for every `ε > 0` there is `δ > 0` with
`|(1 + x)^p - 1 - p x| ≤ ε |x|` whenever `|x| < δ`. -/
theorem rpow_one_add_approx (p : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ x : ℝ, |x| < δ → |(1 + x) ^ p - 1 - p * x| ≤ ε * |x| := by
  have hd : HasDerivAt (fun x : ℝ => (1 + x) ^ p) p 0 := by
    have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := (hasDerivAt_id 0).const_add 1
    have h2 : HasDerivAt (fun x : ℝ => (1 + x) ^ p) (p * (1 + 0) ^ (p - 1) * 1) 0 :=
      (Real.hasDerivAt_rpow_const (x := 1 + 0) (p := p) (Or.inl (by norm_num))).comp 0 h1
    simpa using h2
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hd.isLittleO.def hε)
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have := hball (show dist x 0 < δ by simpa [Real.dist_eq] using hx)
  simp only [add_zero, Real.one_rpow, sub_zero, smul_eq_mul, Real.norm_eq_abs] at this
  rwa [mul_comm x p] at this

/-- The continuous-time Ramsey system with isoelastic utility `u = C^{1-σ}/(1-σ)`
(O&R p. 510 with (21)): `K̇ = F(K) - C`, `Ċ = C [F'(K) - ρ]/σ`. -/
noncomputable def ramseyFieldCRRA (F : ℝ → ℝ) (ρ σ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (F p.1 - p.2, p.2 * (deriv F p.1 - ρ) / σ)

/-- The period-`h` isoelastic Ramsey system (O&R p. 509 with (21)) written as `X + h Φ_h(X)`:
consumption grows by the factor `([1 + h F'(K_{s+h})]/(1 + ρh))^{1/σ}`. -/
noncomputable def ramseyFieldHCRRA (F : ℝ → ℝ) (ρ σ h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (F p.1 - p.2,
    p.2 * (((1 + h * deriv F (p.1 + h * (F p.1 - p.2))) / (1 + ρ * h)) ^ (1 / σ) - 1) / h)

/-- **The isoelastic period-`h` Ramsey equations are a one-step scheme** (O&R p. 509 with
(21)): with `K_{s+h} = K_s + h[F(K_s) - C_s]` and the period-`h` Euler equation
`C_s^{-σ} = [1 + h F'(K_{s+h})] C_{s+h}^{-σ}/(1 + ρh)`, the state moves by `h Φ_h`. -/
theorem period_h_crra_step (F : ℝ → ℝ) {ρ σ h K C K' C' : ℝ} (hσ : 0 < σ) (hh : 0 < h)
    (hρh : 0 < 1 + ρ * h) (hq : 0 < 1 + h * deriv F K') (hC : 0 < C) (hC' : 0 < C')
    (hK' : K' = K + h * (F K - C))
    (heuler : C ^ (-σ) = (1 + h * deriv F K') * C' ^ (-σ) / (1 + ρ * h)) :
    (K', C') = (K, C) + h • ramseyFieldHCRRA F ρ σ h (K, C) := by
  set q := (1 + h * deriv F K') / (1 + ρ * h)
  have hq0 : 0 < q := div_pos hq hρh
  have e1 : C' ^ (-σ) = C ^ (-σ) / q := by
    have h1 : 1 + ρ * h ≠ 0 := hρh.ne'
    have h2 : 1 + h * deriv F K' ≠ 0 := hq.ne'
    have h3 : 1 + h * ρ ≠ 0 := by rw [mul_comm]; exact h1
    rw [heuler]; simp only [q]; field_simp
  have hσ' : -σ ≠ 0 := by linarith
  have e2 : C' = C * q ^ (1 / σ) := by
    have := congrArg (fun z => z ^ (-σ)⁻¹) e1
    rw [Real.rpow_rpow_inv hC'.le hσ', Real.div_rpow (Real.rpow_nonneg hC.le _) hq0.le,
      Real.rpow_rpow_inv hC.le hσ', inv_neg, Real.rpow_neg hq0.le, div_inv_eq_mul] at this
    rw [this, one_div]
  simp only [ramseyFieldHCRRA, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, ← hK']
  refine Prod.ext rfl ?_
  change C' = C + h * (C * (q ^ (1 / σ) - 1) / h)
  rw [e2]
  field_simp
  ring

/-- **The one-step error of the isoelastic scheme** (O&R p. 509 with (21)): with
`x = h(A - ρ)/(1 + ρh)`, `|x| ≤ hB₂`, `|(A - A₀) - ρh(A₀ - ρ)| ≤ hM` and
`|Z - 1 - x/σ| ≤ ε'|x|` for `ε' = ε/(2(C_m B₂ + 1))`, the difference between the period-`h`
consumption increment `C(Z - 1)/h` and the continuous one `C(A₀ - ρ)/σ` is at most `ε`
provided `|C| ≤ C_m` and `h (2(C_m M/σ + 1)) ≤ ε`. -/
theorem crra_error_bound {σ ρ h y2 A A0 xq Z ε ε' B2 Cm M : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ)
    (hh0 : 0 < h) (hy2 : |y2| ≤ Cm) (hCm : 0 ≤ Cm) (hB2 : 0 ≤ B2) (hM : 0 ≤ M) (hε : 0 < ε)
    (hε' : ε' = ε / (2 * (Cm * B2 + 1))) (hxqd : xq = h * (A - ρ) / (1 + ρ * h))
    (hxq : |xq| ≤ h * B2) (hnum : |(A - A0) - ρ * h * (A0 - ρ)| ≤ h * M)
    (hh3 : h * (2 * (Cm * (1 / σ) * M + 1)) ≤ ε) (hZ : |Z - 1 - 1 / σ * xq| ≤ ε' * |xq|) :
    |y2 * (Z - 1) / h - y2 * (A0 - ρ) / σ| ≤ ε := by
  have hρh : 1 ≤ 1 + ρ * h := by nlinarith
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  have e : y2 * (Z - 1) / h - y2 * (A0 - ρ) / σ =
      y2 * ((Z - 1 - 1 / σ * xq) / h) +
        y2 * ((A - A0) - ρ * h * (A0 - ρ)) / (σ * (1 + ρ * h)) := by
    have h1 : 1 + ρ * h ≠ 0 := by linarith
    rw [hxqd]; field_simp; ring
  rw [e]
  have t1 : |y2 * ((Z - 1 - 1 / σ * xq) / h)| ≤ ε / 2 := by
    rw [abs_mul, abs_div, abs_of_pos hh0]
    have h1 : |Z - 1 - 1 / σ * xq| / h ≤ ε' * B2 := by
      rw [div_le_iff₀ hh0]
      have := mul_le_mul_of_nonneg_left hxq hε'0.le
      linarith
    have h2 : Cm * (ε' * B2) ≤ ε / 2 := by
      have e2 : Cm * (ε' * B2) = ε / 2 * (Cm * B2 / (Cm * B2 + 1)) := by
        rw [hε']; field_simp
      rw [e2]
      have : Cm * B2 / (Cm * B2 + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ ε / 2)
      linarith
    calc |y2| * (|Z - 1 - 1 / σ * xq| / h) ≤ Cm * (ε' * B2) :=
          mul_le_mul hy2 h1 (by positivity) hCm
      _ ≤ ε / 2 := h2
  have t2 : |y2 * ((A - A0) - ρ * h * (A0 - ρ)) / (σ * (1 + ρ * h))| ≤ ε / 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < σ * (1 + ρ * h)),
      div_le_iff₀ (by positivity)]
    have h1 : |y2| * |(A - A0) - ρ * h * (A0 - ρ)| ≤ Cm * (h * M) :=
      mul_le_mul hy2 hnum (abs_nonneg _) hCm
    have h2 : Cm * (h * M) ≤ ε / 2 * σ := by
      have e3 : h * (2 * (Cm * (1 / σ) * M + 1)) * σ = 2 * (Cm * (h * M)) + 2 * h * σ := by
        field_simp
      have := mul_le_mul_of_nonneg_right hh3 hσ.le
      have : 0 ≤ 2 * h * σ := by positivity
      linarith
    have h3 : ε / 2 * σ ≤ ε / 2 * (σ * (1 + ρ * h)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    linarith
  calc _ ≤ |y2 * ((Z - 1 - 1 / σ * xq) / h)| +
        |y2 * ((A - A0) - ρ * h * (A0 - ρ)) / (σ * (1 + ρ * h))| := abs_add_le _ _
    _ ≤ ε := by linarith

/-- **The isoelastic period-`h` Euler dynamics converge to the Ramsey ODE on compact
intervals** (O&R p. 510 with (21), `σ > 0`): if `(K, C)` solves `K̇ = F(K) - C`,
`Ċ = C[F'(K) - ρ]/σ` on `[0, T]` with `K` in `[a + 2r, b - 2r]`, `F` and `F'` Lipschitz on
`[a, b]` and `ρ ≥ 0`, then the period-`h` paths (feasibility plus the period-`h` isoelastic
Euler equation, `period_h_crra_step`) started from initial conditions converging to
`(K₀, C₀)` along a filter `l ≤ 𝓝[>] 0` converge to the solution uniformly on `[0, T]`. The
uniform consistency comes from the first-order expansion `rpow_one_add_approx`. -/
theorem crra_period_h_converges_along (F : ℝ → ℝ) {ρ σ T a b r LF LF' : ℝ} {l : Filter ℝ}
    (hl : l ≤ 𝓝[>] 0) (hρ : 0 ≤ ρ) (hσ : 0 < σ)
    (hT : 0 ≤ T) (hr : 0 < r) (hLF : 0 ≤ LF) (hLF' : 0 ≤ LF')
    (hFL : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |F u - F v| ≤ LF * |u - v|)
    (hF'L : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |deriv F u - deriv F v| ≤ LF' * |u - v|)
    {K C : ℝ → ℝ}
    (hsol : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => (K t, C t))
      (ramseyFieldCRRA F ρ σ (K t, C t)) (Icc 0 T) t)
    (hKr : ∀ t ∈ Icc 0 T, a + 2 * r ≤ K t ∧ K t ≤ b - 2 * r)
    {X : ℝ → ℕ → ℝ × ℝ} (hX : ∀ h j, X h (j + 1) = X h j + h • ramseyFieldHCRRA F ρ σ h (X h j))
    (hX0 : Tendsto (fun h => X h 0) l (𝓝 (K 0, C 0))) :
    ∀ ε > 0, ∀ᶠ h in l, ∀ j : ℕ, (j : ℝ) * h ≤ T →
      ‖X h j - (K (j * h), C (j * h))‖ ≤ ε := by
  set x : ℝ → ℝ × ℝ := fun t => (K t, C t)
  have hxc : ContinuousOn x (Icc 0 T) := fun t ht => (hsol t ht).continuousWithinAt
  have hCc : ContinuousOn C (Icc 0 T) := continuous_snd.comp_continuousOn hxc
  obtain ⟨Cb, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn hCc
  have hFc : ContinuousOn F (Icc a b) :=
    (LipschitzOnWith.of_dist_le' (K := LF) (fun u hu v hv => by
      simpa [Real.dist_eq] using hFL u hu v hv)).continuousOn
  have hF'c : ContinuousOn (deriv F) (Icc a b) :=
    (LipschitzOnWith.of_dist_le' (K := LF') (fun u hu v hv => by
      simpa [Real.dist_eq] using hF'L u hu v hv)).continuousOn
  -- bounds on `[a, b]`
  obtain ⟨BF, hBF⟩ := isCompact_Icc.exists_bound_of_continuousOn hFc
  obtain ⟨BF', hBF'⟩ := isCompact_Icc.exists_bound_of_continuousOn hF'c
  have hab : ∀ t ∈ Icc 0 T, ∀ y : ℝ × ℝ, ‖y - x t‖ ≤ r →
      y.1 ∈ Icc a b ∧ |y.2| ≤ |Cb| + r := by
    intro t ht y hy
    have h1 : |y.1 - K t| ≤ r := by
      have := (norm_prod_le_iff.mp hy).1; simpa [x, Real.norm_eq_abs] using this
    have h2 : |y.2 - C t| ≤ r := by
      have := (norm_prod_le_iff.mp hy).2; simpa [x, Real.norm_eq_abs] using this
    have h3 := hCb t ht
    rw [Real.norm_eq_abs] at h3
    obtain ⟨hk1, hk2⟩ := hKr t ht
    rw [abs_le] at h1 h2
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rw [abs_le]; constructor <;> linarith [neg_abs_le Cb,
      le_abs_self Cb, (abs_le.mp h3).1, (abs_le.mp h3).2]
  set Cm := |Cb| + r
  set L := LF + 1 + (Cm * LF' + (|BF'| + ρ)) / σ
  have hLpos : 0 ≤ L := add_nonneg (by positivity) (div_nonneg (by positivity) hσ.le)
  refine one_step_scheme_converges_along hl hT hr hLpos hsol ?_ ?_ ?_ hX hX0
  · -- continuity of `Φ ∘ x`
    have hKmap : MapsTo K (Icc 0 T) (Icc a b) := fun t ht =>
      ⟨by linarith [(hKr t ht).1], by linarith [(hKr t ht).2]⟩
    have hKc : ContinuousOn K (Icc 0 T) := continuous_fst.comp_continuousOn hxc
    have h1 : ContinuousOn (fun t => F (K t)) (Icc 0 T) := hFc.comp hKc hKmap
    have h2 : ContinuousOn (fun t => deriv F (K t)) (Icc 0 T) := hF'c.comp hKc hKmap
    exact (h1.sub hCc).prodMk ((hCc.mul (h2.sub continuousOn_const)).div_const σ)
  · -- Lipschitz bound along the tube
    intro y t ht hy
    obtain ⟨hy1, hy2⟩ := hab t ht y hy
    have hKt : K t ∈ Icc a b := ⟨by linarith [(hKr t ht).1], by linarith [(hKr t ht).2]⟩
    have hd1 : |y.1 - K t| ≤ ‖y - x t‖ := by
      have := norm_fst_le (y - x t); simpa [x, Real.norm_eq_abs] using this
    have hd2 : |y.2 - C t| ≤ ‖y - x t‖ := by
      have := norm_snd_le (y - x t); simpa [x, Real.norm_eq_abs] using this
    have hn0 := norm_nonneg (y - x t)
    have hF1 := hFL _ hy1 _ hKt
    have hF2 := hF'L _ hy1 _ hKt
    have hBt : |deriv F (K t) - ρ| ≤ |BF'| + ρ := by
      have := hBF' _ hKt; rw [Real.norm_eq_abs] at this
      calc |deriv F (K t) - ρ| ≤ |deriv F (K t)| + |ρ| := abs_sub _ _
        _ ≤ |BF'| + ρ := by rw [abs_of_nonneg hρ]; linarith [le_abs_self BF']
    rw [norm_prod_le_iff]
    simp only [ramseyFieldCRRA, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
    constructor
    · calc |F y.1 - y.2 - (F (x t).1 - (x t).2)| ≤ |F y.1 - F (K t)| + |y.2 - C t| := by
            simp only [x]
            rw [show F y.1 - y.2 - (F (K t) - C t) = (F y.1 - F (K t)) - (y.2 - C t) by ring]
            exact abs_sub _ _
        _ ≤ LF * ‖y - x t‖ + ‖y - x t‖ := by nlinarith
        _ ≤ L * ‖y - x t‖ := by
            apply le_of_sub_nonneg
            have : 0 ≤ (Cm * LF' + (|BF'| + ρ)) / σ * ‖y - x t‖ :=
              mul_nonneg (div_nonneg (by positivity) hσ.le) hn0
            nlinarith
    · rw [← sub_div, abs_div, abs_of_pos hσ, div_le_iff₀ hσ]
      calc |y.2 * (deriv F y.1 - ρ) - (x t).2 * (deriv F (x t).1 - ρ)|
          ≤ |y.2| * |deriv F y.1 - deriv F (K t)| + |deriv F (K t) - ρ| * |y.2 - C t| := by
            simp only [x]
            rw [show y.2 * (deriv F y.1 - ρ) - C t * (deriv F (K t) - ρ) =
              y.2 * (deriv F y.1 - deriv F (K t)) + (deriv F (K t) - ρ) * (y.2 - C t) by ring]
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul]
        _ ≤ Cm * (LF' * ‖y - x t‖) + (|BF'| + ρ) * ‖y - x t‖ := by
            apply add_le_add
            · exact mul_le_mul hy2 (hF2.trans (mul_le_mul_of_nonneg_left hd1 hLF'))
                (abs_nonneg _) (by positivity)
            · exact mul_le_mul hBt hd2 (abs_nonneg _) (by positivity)
        _ ≤ L * ‖y - x t‖ * σ := by
            have e : L * ‖y - x t‖ * σ = (LF + 1) * σ * ‖y - x t‖ +
                (Cm * LF' + (|BF'| + ρ)) * ‖y - x t‖ := by
              simp only [L]; field_simp
            rw [e]
            have : 0 ≤ (LF + 1) * σ * ‖y - x t‖ :=
              mul_nonneg (mul_nonneg (by linarith) hσ.le) hn0
            linarith
  · -- uniform consistency on the tube (first-order expansion of the `1/σ` power)
    intro ε hε
    set B1 := |BF| + Cm
    set B2 := |BF'| + ρ
    set M := LF' * B1 + ρ * B2
    have hp : 0 < 1 / σ := one_div_pos.mpr hσ
    have hB1 : 0 ≤ B1 := by positivity
    have hB2 : 0 ≤ B2 := by positivity
    have hM : 0 ≤ M := by positivity
    have hCm : 0 ≤ Cm := by positivity
    set ε' := ε / (2 * (Cm * B2 + 1))
    have hε' : 0 < ε' := by positivity
    obtain ⟨δ, hδ, hδx⟩ := rpow_one_add_approx (1 / σ) hε'
    set hmax := min (min (r / (B1 + 1)) (δ / (B2 + 1))) (ε / (2 * (Cm * (1 / σ) * M + 1)))
    have hhmax : 0 < hmax := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
    have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo 0 hmax := Ioo_mem_nhdsGT hhmax
    filter_upwards [hev] with h hh y t ht hy
    obtain ⟨hy1, hy2⟩ := hab t ht y hy
    have hh0 : 0 < h := hh.1
    have hFy : |F y.1 - y.2| ≤ B1 := by
      have := hBF _ hy1; rw [Real.norm_eq_abs] at this
      calc |F y.1 - y.2| ≤ |F y.1| + |y.2| := abs_sub _ _
        _ ≤ B1 := by simp only [B1]; linarith [le_abs_self BF]
    have hK't : |y.1 + h * (F y.1 - y.2) - y.1| ≤ r := by
      rw [add_sub_cancel_left, abs_mul, abs_of_pos hh0]
      have h1 : h ≤ r / (B1 + 1) := hh.2.le.trans ((min_le_left _ _).trans (min_le_left _ _))
      rw [le_div_iff₀ (by linarith)] at h1
      nlinarith
    have hy1' : y.1 + h * (F y.1 - y.2) ∈ Icc a b := by
      have hKt := hKr t ht
      have hd1 : |y.1 - K t| ≤ r := by
        have := norm_fst_le (y - x t); simp only [x, Prod.fst_sub, Real.norm_eq_abs] at this
        linarith
      rw [abs_le] at hK't hd1
      exact ⟨by linarith [hKt.1], by linarith [hKt.2]⟩
    have hρh : 1 ≤ 1 + ρ * h := by nlinarith
    rw [norm_prod_le_iff]
    simp only [ramseyFieldHCRRA, ramseyFieldCRRA, Prod.fst_sub, Prod.snd_sub, sub_self,
      norm_zero, Real.norm_eq_abs]
    refine ⟨hε.le, ?_⟩
    have hdiff := hF'L _ hy1' _ hy1
    set A := deriv F (y.1 + h * (F y.1 - y.2))
    set A0 := deriv F y.1
    have hBA : |A - ρ| ≤ B2 := by
      have := hBF' _ hy1'; rw [Real.norm_eq_abs] at this
      calc |A - ρ| ≤ |A| + |ρ| := abs_sub _ _
        _ ≤ B2 := by simp only [B2]; rw [abs_of_nonneg hρ]; linarith [le_abs_self BF']
    have hBy : |A0 - ρ| ≤ B2 := by
      have := hBF' _ hy1; rw [Real.norm_eq_abs] at this
      calc |A0 - ρ| ≤ |A0| + |ρ| := abs_sub _ _
        _ ≤ B2 := by simp only [B2]; rw [abs_of_nonneg hρ]; linarith [le_abs_self BF']
    set xq := h * (A - ρ) / (1 + ρ * h)
    have hq : (1 + h * A) / (1 + ρ * h) = 1 + xq := by
      simp only [xq]; field_simp; ring
    rw [hq]
    have hxq : |xq| ≤ h * B2 := by
      simp only [xq]
      rw [abs_div, abs_mul, abs_of_pos hh0, abs_of_pos (by linarith : (0 : ℝ) < 1 + ρ * h),
        div_le_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left hBA hh0.le
      have : 0 ≤ h * B2 * (ρ * h) := by positivity
      nlinarith
    have hxqδ : |xq| < δ := by
      have h1 : h ≤ δ / (B2 + 1) :=
        hh.2.le.trans ((min_le_left _ _).trans (min_le_right _ _))
      rw [le_div_iff₀ (by linarith)] at h1
      nlinarith
    have hnum : |(A - A0) - ρ * h * (A0 - ρ)| ≤ h * M := by
      have h1 : |A - A0| ≤ LF' * (h * B1) := by
        refine hdiff.trans (mul_le_mul_of_nonneg_left ?_ hLF')
        rw [add_sub_cancel_left, abs_mul, abs_of_pos hh0]
        exact mul_le_mul_of_nonneg_left hFy hh0.le
      have h2 : |ρ * h * (A0 - ρ)| ≤ ρ * h * B2 := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left hBy (by positivity)
      calc _ ≤ |A - A0| + |ρ * h * (A0 - ρ)| := abs_sub _ _
        _ ≤ _ := by simp only [M]; nlinarith
    have hh3 : h * (2 * (Cm * (1 / σ) * M + 1)) ≤ ε := by
      have := hh.2.le.trans (min_le_right _ _)
      rwa [le_div_iff₀ (by positivity)] at this
    exact crra_error_bound hσ hρ hh0 hy2 hCm hB2 hM hε rfl rfl hxq hnum hh3 (hδx xq hxqδ)

/-! ## Convergence of the period-`h` saddle choice -/

/-- **A grid point near the end of the interval** (O&R Appendix 7A): if period-`h` paths
converge uniformly on `[0, T]` to a continuous `x` along `l ≤ 𝓝[>] 0`, then eventually along
`l` some grid point `X^h_j` lies within `m` of `x(T)` (take `j = ⌊T/h⌋`). -/
theorem exists_grid_near_end {E : Type*} [NormedAddCommGroup E] {x : ℝ → E} {X : ℝ → ℕ → E}
    {T m : ℝ} {l : Filter ℝ} (hl : l ≤ 𝓝[>] 0) (hT : 0 ≤ T) (hm : 0 < m)
    (hxc : ContinuousOn x (Icc 0 T))
    (hconv : ∀ ε > 0, ∀ᶠ h in l, ∀ j : ℕ, (j : ℝ) * h ≤ T → ‖X h j - x (j * h)‖ ≤ ε) :
    ∀ᶠ h in l, ∃ j : ℕ, ‖X h j - x T‖ < m := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp
    (hxc T ⟨hT, le_rfl⟩) (m / 2) (half_pos hm)
  have hev : ∀ᶠ h in l, h ∈ Ioo 0 δ := hl (Ioo_mem_nhdsGT hδ)
  filter_upwards [hev, hconv (m / 4) (by positivity)] with h hh hc
  have hh0 : 0 < h := hh.1
  set j := ⌊T / h⌋₊
  have hj1 : (j : ℝ) * h ≤ T := by
    have := Nat.floor_le (div_nonneg hT hh0.le)
    rwa [le_div_iff₀ hh0] at this
  have hj2 : T < ((j : ℝ) + 1) * h := by
    have := Nat.lt_floor_add_one (T / h)
    rwa [div_lt_iff₀ hh0] at this
  refine ⟨j, ?_⟩
  have hjI : (j : ℝ) * h ∈ Icc 0 T := ⟨by positivity, hj1⟩
  have hd : dist ((j : ℝ) * h) T < δ := by
    rw [Real.dist_eq, abs_of_nonpos (by linarith)]
    linarith [hh.2]
  have h1 := hball hjI hd
  rw [dist_eq_norm] at h1
  calc ‖X h j - x T‖ ≤ ‖X h j - x (j * h)‖ + ‖x (j * h) - x T‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < m := by linarith [hc j hj1]

/-- **The saddle choice converges** (O&R Appendix 7A, the precise content of "the discrete
saddle path converges to the continuous one"): let the period-`h` paths `X^h` start at
`P(C_h)` (`P` continuous, e.g. `P c = (K₀, c)`) with `C_h ∈ [lo, hi]`, and stay in a set `S`
for ever (the discrete saddle paths). Suppose every other initial choice `c ≠ c*` is
*unstable in continuous time*: some point `z` at distance at least `m > 0` from `S` is
approached within `m` by the period-`h` paths from any initial conditions converging to
`P(c)`. Then `C_h → c*`. (Compactness gives a cluster value `c̃`; if `c̃ ≠ c*` the paths along
a subnet converging to `c̃` would leave `S`.) -/
theorem saddle_choice_converges {E : Type*} [NormedAddCommGroup E] {S : Set E} {P : ℝ → E}
    (hP : Continuous P) {C : ℝ → ℝ} {X : ℝ → ℕ → E} {lo hi cstar : ℝ}
    (hX0 : ∀ h, X h 0 = P (C h)) (hC : ∀ᶠ h in 𝓝[>] 0, C h ∈ Icc lo hi)
    (hS : ∀ᶠ h in 𝓝[>] 0, ∀ j, X h j ∈ S)
    (hexit : ∀ c ∈ Icc lo hi, c ≠ cstar → ∃ z : E, ∃ m, 0 < m ∧ (∀ y ∈ S, m ≤ ‖y - z‖) ∧
      ∀ l : Filter ℝ, l ≤ 𝓝[>] 0 → Tendsto (fun h => X h 0) l (𝓝 (P c)) →
        ∀ᶠ h in l, ∃ j : ℕ, ‖X h j - z‖ < m) :
    Tendsto C (𝓝[>] 0) (𝓝 cstar) := by
  by_contra hnot
  rw [Metric.tendsto_nhds] at hnot
  push Not at hnot
  obtain ⟨ε, hε, hfreq⟩ := hnot
  set l1 := 𝓝[>] (0 : ℝ) ⊓ 𝓟 {h | ε ≤ dist (C h) cstar}
  have : l1.NeBot := (frequently_iff_neBot).mp hfreq
  set Kset := Icc lo hi ∩ {c | ε ≤ dist c cstar}
  have hK : IsCompact Kset :=
    isCompact_Icc.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hmap : map C l1 ≤ 𝓟 Kset := by
    refine tendsto_principal.mpr ?_
    have h1 : ∀ᶠ h in l1, C h ∈ Icc lo hi := hC.filter_mono inf_le_left
    have h2 : ∀ᶠ h in l1, ε ≤ dist (C h) cstar := mem_inf_of_right (mem_principal_self _)
    filter_upwards [h1, h2] with h a b using ⟨a, b⟩
  obtain ⟨c, hcK, hcl⟩ := hK hmap
  set l2 := l1 ⊓ comap C (𝓝 c)
  have hl2 : l2.NeBot := by
    have : (map C l2).NeBot := by
      rw [show map C l2 = map C l1 ⊓ 𝓝 c from Filter.push_pull C l1 (𝓝 c), inf_comm]
      exact hcl
    exact this.of_map
  have hl2le : l2 ≤ 𝓝[>] 0 := inf_le_left.trans inf_le_left
  have hCc : Tendsto C l2 (𝓝 c) := tendsto_iff_comap.mpr inf_le_right
  have hne : c ≠ cstar := by
    intro h; have := hcK.2; simp only [mem_ofPred_eq, h, dist_self] at this; linarith
  obtain ⟨z, m, hm, hSz, hconv⟩ := hexit c hcK.1 hne
  have hX0l : Tendsto (fun h => X h 0) l2 (𝓝 (P c)) := by
    simp only [hX0]; exact (hP.tendsto c).comp hCc
  have hev := (hconv l2 hl2le hX0l).and (hS.filter_mono hl2le)
  obtain ⟨h, ⟨j, hj⟩, hSall⟩ := hev.exists
  linarith [hSz _ (hSall j)]

/-- **The period-`h` saddle choice converges to the continuous saddle value, `u = log`**
(O&R Appendix 7A, pp. 509–510): suppose the period-`h` Ramsey paths from `(K₀, C_h)`
(feasibility plus the period-`h` Euler equation, `period_h_ramsey_step`) stay in a set `S`
for ever, `C_h ∈ [lo, hi]`, and every continuous-time Ramsey path from `(K₀, c)` with
`c ≠ c*` in `[lo, hi]` reaches, within finite time `T` and inside a region where `F` and `F'`
are Lipschitz, a point at distance at least `m > 0` from `S` (the continuous-time saddle-path
property of `c*`). Then `C_h → c*` as `h → 0⁺`. -/
theorem ramsey_saddle_choice_converges (F : ℝ → ℝ) {ρ K0 lo hi cstar : ℝ} (hρ : 0 ≤ ρ)
    {X : ℝ → ℕ → ℝ × ℝ} (hX : ∀ h j, X h (j + 1) = X h j + h • ramseyFieldH F ρ h (X h j))
    {Ch : ℝ → ℝ} (hX0 : ∀ h, X h 0 = (K0, Ch h)) (hC : ∀ᶠ h in 𝓝[>] 0, Ch h ∈ Icc lo hi)
    {S : Set (ℝ × ℝ)} (hS : ∀ᶠ h in 𝓝[>] 0, ∀ j, X h j ∈ S)
    (hunst : ∀ c ∈ Icc lo hi, c ≠ cstar → ∃ (Kc Cc : ℝ → ℝ) (T m a b r LF LF' : ℝ),
      0 ≤ T ∧ 0 < m ∧ 0 < r ∧ 0 ≤ LF ∧ 0 ≤ LF' ∧ Kc 0 = K0 ∧ Cc 0 = c ∧
      (∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |F u - F v| ≤ LF * |u - v|) ∧
      (∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |deriv F u - deriv F v| ≤ LF' * |u - v|) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => (Kc t, Cc t))
        (ramseyField F ρ (Kc t, Cc t)) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, a + 2 * r ≤ Kc t ∧ Kc t ≤ b - 2 * r) ∧
      ∀ y ∈ S, m ≤ ‖y - (Kc T, Cc T)‖) :
    Tendsto Ch (𝓝[>] 0) (𝓝 cstar) := by
  refine saddle_choice_converges (P := fun c => (K0, c))
    (continuous_const.prodMk continuous_id) hX0 hC hS (fun c hc hne => ?_)
  obtain ⟨Kc, Cc, T, m, a, b, r, LF, LF', hT, hm, hr, hLF, hLF', hK0, hC0, hFL, hF'L, hsol,
    hKr, hSm⟩ := hunst c hc hne
  refine ⟨(Kc T, Cc T), m, hm, hSm, fun l hl hl0 => ?_⟩
  have hl0' : Tendsto (fun h => X h 0) l (𝓝 (Kc 0, Cc 0)) := by rw [hK0, hC0]; exact hl0
  have hconv := ramsey_period_h_converges_along F hl hρ hT hr hLF hLF' hFL hF'L hsol hKr hX hl0'
  have hxc : ContinuousOn (fun t => (Kc t, Cc t)) (Icc 0 T) :=
    fun t ht => (hsol t ht).continuousWithinAt
  exact exists_grid_near_end (x := fun t => (Kc t, Cc t)) hl hT hm hxc hconv

/-- **The isoelastic period-`h` Euler dynamics converge to the Ramsey ODE on compact
intervals** (O&R p. 510 with (21)): the case `l = 𝓝[>] 0` of
`crra_period_h_converges_along`. -/
theorem crra_period_h_converges (F : ℝ → ℝ) {ρ σ T a b r LF LF' : ℝ} (hρ : 0 ≤ ρ)
    (hσ : 0 < σ) (hT : 0 ≤ T) (hr : 0 < r) (hLF : 0 ≤ LF) (hLF' : 0 ≤ LF')
    (hFL : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |F u - F v| ≤ LF * |u - v|)
    (hF'L : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |deriv F u - deriv F v| ≤ LF' * |u - v|)
    {K C : ℝ → ℝ}
    (hsol : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => (K t, C t))
      (ramseyFieldCRRA F ρ σ (K t, C t)) (Icc 0 T) t)
    (hKr : ∀ t ∈ Icc 0 T, a + 2 * r ≤ K t ∧ K t ≤ b - 2 * r)
    {X : ℝ → ℕ → ℝ × ℝ}
    (hX : ∀ h j, X h (j + 1) = X h j + h • ramseyFieldHCRRA F ρ σ h (X h j))
    (hX0 : Tendsto (fun h => X h 0) (𝓝[>] 0) (𝓝 (K 0, C 0))) :
    ∀ ε > 0, ∀ᶠ h in 𝓝[>] 0, ∀ j : ℕ, (j : ℝ) * h ≤ T →
      ‖X h j - (K (j * h), C (j * h))‖ ≤ ε :=
  crra_period_h_converges_along F le_rfl hρ hσ hT hr hLF hLF' hFL hF'L hsol hKr hX hX0

/-- **The period-`h` saddle choice converges to the continuous saddle value, isoelastic
utility** (O&R Appendix 7A with (21), `σ > 0`): as `ramsey_saddle_choice_converges`, for the
isoelastic period-`h` Euler equation (`period_h_crra_step`) and `Ċ = C[F'(K) - ρ]/σ`. -/
theorem crra_saddle_choice_converges (F : ℝ → ℝ) {ρ σ K0 lo hi cstar : ℝ} (hρ : 0 ≤ ρ)
    (hσ : 0 < σ) {X : ℝ → ℕ → ℝ × ℝ}
    (hX : ∀ h j, X h (j + 1) = X h j + h • ramseyFieldHCRRA F ρ σ h (X h j))
    {Ch : ℝ → ℝ} (hX0 : ∀ h, X h 0 = (K0, Ch h)) (hC : ∀ᶠ h in 𝓝[>] 0, Ch h ∈ Icc lo hi)
    {S : Set (ℝ × ℝ)} (hS : ∀ᶠ h in 𝓝[>] 0, ∀ j, X h j ∈ S)
    (hunst : ∀ c ∈ Icc lo hi, c ≠ cstar → ∃ (Kc Cc : ℝ → ℝ) (T m a b r LF LF' : ℝ),
      0 ≤ T ∧ 0 < m ∧ 0 < r ∧ 0 ≤ LF ∧ 0 ≤ LF' ∧ Kc 0 = K0 ∧ Cc 0 = c ∧
      (∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |F u - F v| ≤ LF * |u - v|) ∧
      (∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |deriv F u - deriv F v| ≤ LF' * |u - v|) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => (Kc t, Cc t))
        (ramseyFieldCRRA F ρ σ (Kc t, Cc t)) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, a + 2 * r ≤ Kc t ∧ Kc t ≤ b - 2 * r) ∧
      ∀ y ∈ S, m ≤ ‖y - (Kc T, Cc T)‖) :
    Tendsto Ch (𝓝[>] 0) (𝓝 cstar) := by
  refine saddle_choice_converges (P := fun c => (K0, c))
    (continuous_const.prodMk continuous_id) hX0 hC hS (fun c hc hne => ?_)
  obtain ⟨Kc, Cc, T, m, a, b, r, LF, LF', hT, hm, hr, hLF, hLF', hK0, hC0, hFL, hF'L, hsol,
    hKr, hSm⟩ := hunst c hc hne
  refine ⟨(Kc T, Cc T), m, hm, hSm, fun l hl hl0 => ?_⟩
  have hl0' : Tendsto (fun h => X h 0) l (𝓝 (Kc 0, Cc 0)) := by rw [hK0, hC0]; exact hl0
  have hconv := crra_period_h_converges_along F hl hρ hσ hT hr hLF hLF' hFL hF'L hsol hKr hX
    hl0'
  have hxc : ContinuousOn (fun t => (Kc t, Cc t)) (Icc 0 T) :=
    fun t ht => (hsol t ht).continuousWithinAt
  exact exists_grid_near_end (x := fun t => (Kc t, Cc t)) hl hT hm hxc hconv

end ObstfeldRogoff.GlobalGrowth.ContinuousTimeLimits
