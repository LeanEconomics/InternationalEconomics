/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MoneyExchangeRates.CashInAdvance
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Continuous-time maximisation and the maximum principle

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, Supplement A to
Chapter 8 (pp. 745–753).

We prove:

* **A.1**: the period-`h` first-order conditions (3)–(5) give (35)–(36) at `h = 1`; the exact
  algebra behind (8), (9) and fn 1 and their limits as `h → 0` for right-differentiable paths;
  `(1+δh)^{−(s−t)/h} → e^{−δ(s−t)}`; (7) as the limit of (2)/h; and (10)–(11);
* **A.2, sufficiency (Mangasarian and Arrow)**: the book's box made precise — if the costate
  obeys `λ̇ = δλ − ∂H/∂Q`, `∂H/∂c = 0` and `H` is jointly concave (or the Arrow condition
  holds), then `∫₀^T e^{−δs}[u(c) − u(c^*)] ≤ e^{−δT}λ(T)(Q^*(T) − Q(T))` for every feasible
  rival, hence optimality whenever the boundary term is eventually small. The correct condition
  is therefore the transversality condition (15) for the candidate TOGETHER WITH a no-Ponzi
  condition on rivals: (15) alone is NOT sufficient (`ponzi_counterexample`);
* **necessity**: for the monetary problem (a linear-in-state problem) we derive (8), (3)+(9)
  and the transversality condition directly from optimality by compactly supported
  perturbations (`ct_money_foc`, `ct_costate_of_optimal`, `ct_tvc_of_optimal`), giving an exact
  characterisation of the optimum (`monetary_optimal_iff`). In general the transversality
  condition is NOT necessary: the Halkin (1974) example (`halkin_rival`, `halkin_candidate`);
* **A.3.1**: variation of constants and uniqueness for (11), (16), `λ(t) = λ(0)e^{(δ−r)t}`, the TVC
  in wealth form, (17), integration by parts for seignorage and (18), and (19);
* **A.3.2**: money demand (22), `u_C = γ^{1/σ}C^{−1/σ}(P^C)^{(θ−σ)/σ}`, the integrated Euler
  equation (23), its differential form, and (24)–(25), with the constant-rate and `θ = σ` cases;
* **A.3.3**: with `θ = 1`, `δ = r`, real balances are `K_m i^{−ζ}`, `ζ = γ + (1−γ)σ`; `x = 1/i`
  solves the UNSTABLE linear ODE `ζẋ = (r + g_M)x − 1`; the book's formula is its unique
  no-bubble solution (all others add `c e^{rt/ζ}M^{1/ζ}`); constant money growth gives
  `i = r + μ`; and `P^C → i^{1−γ}` as `θ → 1`.

Remarks on the box (p. 748): "λ must be nonnegative" is problem-specific (here `λ = u_C > 0`);
condition 1 presumes interior controls; existence of an optimum is not addressed.
-/

namespace ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple

open Real Filter Topology Set MeasureTheory
open ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility

/-! ## A.1 The period-`h` model and its continuous-time limit -/

/-- Shifting a right neighbourhood of `0` to a right neighbourhood of `s`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem tendsto_add_nhdsGT (s : ℝ) : Tendsto (fun h : ℝ => s + h) (𝓝[>] 0) (𝓝[>] s) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun h : ℝ => s + h) (𝓝 0) (𝓝 (s + 0)) :=
      tendsto_const_nhds.add tendsto_id
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [Set.mem_Ioi] at hh ⊢; linarith

/-- A right derivative as the limit of right difference quotients (fn 10 of Ch. 8).
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem slope_right_tendsto {P : ℝ → ℝ} {Pd s : ℝ} (hd : HasDerivWithinAt P Pd (Set.Ioi s) s) :
    Tendsto (fun h => (P (s + h) - P s) / h) (𝓝[>] 0) (𝓝 Pd) := by
  have h1 := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl s)).1 hd
  refine (h1.comp (tendsto_add_nhdsGT s)).congr fun h => ?_
  simp only [Function.comp_apply, slope_def_field, add_sub_cancel_left]

/-- Right continuity along `s + h`, `h → 0⁺`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem right_cont_tendsto {P : ℝ → ℝ} {Pd s : ℝ} (hd : HasDerivWithinAt P Pd (Set.Ioi s) s) :
    Tendsto (fun h => P (s + h)) (𝓝[>] 0) (𝓝 (P s)) :=
  (hd.continuousWithinAt.tendsto).comp (tendsto_add_nhdsGT s)


/-- **The period-`h` first-order conditions at `h = 1`** (O&R Supplement A, p. 746): with
`β = 1/(1+δ)`, conditions (3) `u_C = λ_s` and (5) `λ_s = ((1+r)/(1+δ))λ_{s+1}` give the Euler
equation (35) `u_C(s) = (1+r)β u_C(s+1)`, and (3)–(4) give the money Euler equation (36)
`u_C(s)/P_s = u_{M/P}(s)/P_s + β u_C(s+1)/P_{s+1}`. -/
theorem period_one_focs {r δ uCs uCs1 uMs lam0 lam1 P0 P1 : ℝ}
    (h3s : uCs = lam0) (h3s1 : uCs1 = lam1)
    (h4 : 1 / P0 * uMs * 1 = lam0 / P0 - (1 / (1 + δ * 1)) * lam1 / P1)
    (h5 : lam0 = (1 + r * 1) / (1 + δ * 1) * lam1) :
    uCs = (1 + r) * (1 / (1 + δ)) * uCs1 ∧
      uCs / P0 = uMs / P0 + 1 / (1 + δ) * uCs1 / P1 := by
  subst h3s h3s1
  simp only [mul_one] at h4 h5
  refine ⟨by rw [h5]; ring, ?_⟩
  rw [div_eq_mul_one_div uMs P0]
  linarith

/-- The algebra behind (8), O&R p. 746: from (3)–(5),
`u_{M/P}/u_C = (1/h)[1 − P_s/((1+rh)P_{s+h})] = r/(1+rh) + ((P_{s+h} − P_s)/h)/((1+rh)P_{s+h})`. -/
theorem mrs_period_h {r h Ps Psh : ℝ} (hh : h ≠ 0) (hrh : 1 + r * h ≠ 0) (hPsh : Psh ≠ 0) :
    1 / h * (1 - 1 / (1 + r * h) * (Ps / Psh)) =
      r / (1 + r * h) + (Psh - Ps) / h * (1 / ((1 + r * h) * Psh)) := by
  have hrh' : 1 + h * r ≠ 0 := by rwa [mul_comm] at hrh
  field_simp
  ring

/-- **(8) as the limit `h → 0`**, O&R p. 746: if the price path is right-differentiable at `s`
(`Ṗ` the right derivative, fn 10 of Ch. 8) and continuous from the right, then
`r/(1+rh) + ((P_{s+h} − P_s)/h)/((1+rh)P_{s+h}) → r + Ṗ/P = r + π = i`. -/
theorem mrs_limit {r Pd : ℝ} {P : ℝ → ℝ} {s : ℝ} (hP : 0 < P s)
    (hd : HasDerivWithinAt P Pd (Set.Ioi s) s) :
    Tendsto (fun h => r / (1 + r * h) + (P (s + h) - P s) / h * (1 / ((1 + r * h) * P (s + h))))
      (𝓝[>] 0) (𝓝 (r + Pd / P s)) := by
  have hslope : Tendsto (fun h => (P (s + h) - P s) / h) (𝓝[>] 0) (𝓝 Pd) :=
    slope_right_tendsto hd
  have hcont : Tendsto (fun h => P (s + h)) (𝓝[>] 0) (𝓝 (P s)) := right_cont_tendsto hd
  have hrh : Tendsto (fun h : ℝ => 1 + r * h) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun h : ℝ => 1 + r * h) (𝓝 0) (𝓝 (1 + r * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)
    rw [mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun h => r / (1 + r * h)) (𝓝[>] 0) (𝓝 (r / 1)) :=
    tendsto_const_nhds.div hrh one_ne_zero
  have h2 : Tendsto (fun h => 1 / ((1 + r * h) * P (s + h))) (𝓝[>] 0)
      (𝓝 (1 / (1 * P s))) :=
    tendsto_const_nhds.div (hrh.mul hcont) (by rw [one_mul]; exact hP.ne')
  have := h1.add (hslope.mul h2)
  simpa [div_eq_mul_one_div Pd (P s)] using this

/-- **(9) as the limit `h → 0`**, O&R p. 747: (5) is equivalent to
`(λ_{s+h} − λ_s)/h = λ_s(δ − r)/(1 + rh)`, whose limit is `λ_s(δ − r)`; so a
right-differentiable costate path satisfies `λ̇ = λ(δ − r)`. -/
theorem costate_period_h {r δ h lam0 lamh : ℝ} (hh : h ≠ 0) (hrh : 1 + r * h ≠ 0)
    (hδh : 1 + δ * h ≠ 0) (h5 : lam0 = (1 + r * h) / (1 + δ * h) * lamh) :
    (lamh - lam0) / h = lam0 * (δ - r) / (1 + r * h) := by
  have hl : lamh = (1 + δ * h) / (1 + r * h) * lam0 := by
    rw [h5, ← mul_assoc, div_mul_div_comm, mul_comm (1 + δ * h), div_self
      (mul_ne_zero hrh hδh), one_mul]
  rw [hl, div_mul_eq_mul_div, div_sub' hrh, div_div,
    div_eq_div_iff (mul_ne_zero hrh hh) hrh]
  ring

/-- **The costate equation (9)** (O&R p. 747): if the costate satisfies (5) for every small
period length `h > 0` and has right derivative `λ̇` at `s`, then `λ̇ = λ_s(δ − r)`. -/
theorem costate_limit {r δ lamd : ℝ} {lam : ℝ → ℝ} {s : ℝ}
    (hd : HasDerivWithinAt lam lamd (Set.Ioi s) s)
    (h5 : ∀ h, 0 < h → lam s = (1 + r * h) / (1 + δ * h) * lam (s + h))
    (hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 1 + r * h ≠ 0 ∧ 1 + δ * h ≠ 0) :
    lamd = lam s * (δ - r) := by
  have hslope : Tendsto (fun h => (lam (s + h) - lam s) / h) (𝓝[>] 0) (𝓝 lamd) :=
    slope_right_tendsto hd
  have hrh : Tendsto (fun h : ℝ => 1 + r * h) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun h : ℝ => 1 + r * h) (𝓝 0) (𝓝 (1 + r * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)
    rw [mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun h => lam s * (δ - r) / (1 + r * h)) (𝓝[>] 0)
      (𝓝 (lam s * (δ - r) / 1)) := tendsto_const_nhds.div hrh one_ne_zero
  rw [div_one] at h2
  refine tendsto_nhds_unique hslope (h2.congr' ?_)
  filter_upwards [hpos, self_mem_nhdsWithin] with h ⟨h1, h2⟩ hh
  exact (costate_period_h (ne_of_gt hh) h1 h2 (h5 h hh)).symm

/-- **Footnote 1** (O&R Supplement p. 746): with period length `h`, Fisher parity gives
`i_{s+h} = (1+rh)P_{s+h}/(hP_s) − 1/h = r P_{s+h}/P_s + (P_{s+h} − P_s)/(hP_s)`, which tends to
`r + π` as `h → 0` for a right-differentiable, right-continuous price path. -/
theorem fisher_period_h {r Pd : ℝ} {P : ℝ → ℝ} {s : ℝ} (hP : 0 < P s)
    (hd : HasDerivWithinAt P Pd (Set.Ioi s) s) :
    (∀ h, h ≠ 0 → (1 + r * h) * (P (s + h) / (h * P s)) - 1 / h =
      r * (P (s + h) / P s) + (P (s + h) - P s) / (h * P s)) ∧
    Tendsto (fun h => r * (P (s + h) / P s) + (P (s + h) - P s) / (h * P s)) (𝓝[>] 0)
      (𝓝 (r + Pd / P s)) := by
  refine ⟨fun h hh => by field_simp; ring, ?_⟩
  have hslope : Tendsto (fun h => (P (s + h) - P s) / h) (𝓝[>] 0) (𝓝 Pd) :=
    slope_right_tendsto hd
  have hcont : Tendsto (fun h => P (s + h)) (𝓝[>] 0) (𝓝 (P s)) := right_cont_tendsto hd
  have h1 : Tendsto (fun h => r * (P (s + h) / P s)) (𝓝[>] 0) (𝓝 (r * (P s / P s))) :=
    tendsto_const_nhds.mul (hcont.div_const _)
  rw [div_self hP.ne', mul_one] at h1
  have h2 := hslope.div_const (P s)
  refine (h1.add h2).congr fun h => ?_
  rw [div_div]

/-- **The continuous-time discount factor**, O&R p. 746:
`(1 + δh)^{−(s−t)/h} → e^{−δ(s−t)}` as `h → 0⁺`. -/
theorem discount_limit (δ a : ℝ) :
    Tendsto (fun h => (1 + δ * h) ^ (-(a / h))) (𝓝[>] 0) (𝓝 (Real.exp (-(δ * a)))) := by
  have hd : HasDerivAt (fun h : ℝ => Real.log (1 + δ * h)) δ 0 := by
    have h1 : HasDerivAt (fun h : ℝ => 1 + δ * h) δ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul δ).const_add 1
    have := h1.log (by simp)
    simpa using this
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  have hs' : Tendsto (fun h => Real.log (1 + δ * h) / h) (𝓝[>] 0) (𝓝 δ) := by
    refine (hslope.mono_left (nhdsWithin_mono _ fun h (hh : 0 < h) => ne_of_gt hh)).congr
      fun h => ?_
    simp [slope_def_field]
  have hexp : Tendsto (fun h => Real.exp (-(a * (Real.log (1 + δ * h) / h)))) (𝓝[>] 0)
      (𝓝 (Real.exp (-(a * δ)))) :=
    (Real.continuous_exp.tendsto _).comp ((hs'.const_mul a).neg)
  rw [mul_comm δ a]
  refine hexp.congr' ?_
  have hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < 1 + δ * h := by
    have : Tendsto (fun h : ℝ => 1 + δ * h) (𝓝 0) (𝓝 (1 + δ * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)
    rw [mul_zero, add_zero] at this
    exact (this.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds one_pos)
  filter_upwards [hpos] with h hh
  rw [rpow_def_of_pos hh]
  congr 1
  ring

/-- **The flow budget constraint (7) as the limit of (2)/h**, O&R p. 746: if the period-`h`
constraint (2), divided by `h`,
`(B_{s+h} − B_s)/h + (M_s − M_{s−h})/(hP_s) = rB_s + Y_s − C_s − T_s`, holds for every small
`h > 0` along a path with right derivative `Ḃ` and left derivative `Ṁ` at `s`, then
`Ḃ + Ṁ/P = rB + Y − T − C`. -/
theorem flow_budget_limit {B M : ℝ → ℝ} {Bd Md Ps r Y C T : ℝ} {s : ℝ}
    (hB : HasDerivWithinAt B Bd (Set.Ioi s) s) (hM : HasDerivWithinAt M Md (Set.Iio s) s)
    (h2 : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (B (s + h) - B s) / h + (M s - M (s - h)) / (h * Ps) = r * B s + Y - C - T) :
    Bd + Md / Ps = r * B s + Y - T - C := by
  have hBs := slope_right_tendsto hB
  have hMs : Tendsto (fun h => (M s - M (s - h)) / h) (𝓝[>] 0) (𝓝 Md) := by
    have h1 := (hasDerivWithinAt_iff_tendsto_slope' (show s ∉ Set.Iio s from lt_irrefl s)).1 hM
    have h3 : Tendsto (fun h : ℝ => s - h) (𝓝[>] 0) (𝓝[<] s) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun h : ℝ => s - h) (𝓝 0) (𝓝 (s - 0)) :=
          tendsto_const_nhds.sub tendsto_id
        rw [sub_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        simp only [Set.mem_Ioi, Set.mem_Iio] at hh ⊢; linarith
    refine (h1.comp h3).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h _
    simp only [Function.comp_apply, slope_def_field, show s - h - s = -h by ring]
    rw [div_neg, ← neg_div, neg_sub]
  have hlim := hBs.add (hMs.div_const Ps)
  have hc : Tendsto (fun h => (B (s + h) - B s) / h + (M s - M (s - h)) / h / Ps) (𝓝[>] 0)
      (𝓝 (r * B s + Y - C - T)) := tendsto_const_nhds.congr' (by
    filter_upwards [h2] with h hh
    rw [← hh, div_div, mul_comm h Ps])
  have := tendsto_nhds_unique hlim hc
  linarith

/-- **Financial wealth `Q = B + M/P` and (11)**, O&R p. 747: differentiating `Q = B + M/P`
gives `Q̇ = Ḃ + Ṁ/P − π M/P`, so the flow constraint (7) `Ḃ + Ṁ/P = rB + Y − T − C` is
equivalent to (11) `Q̇ = rQ + Y − T − C − i M/P` with `i = r + π`, `π = Ṗ/P`. -/
theorem wealth_flow_equiv {B M P : ℝ → ℝ} {Bd Md Pd r Y T C : ℝ} {s : ℝ} (hP : 0 < P s)
    (hB : HasDerivAt B Bd s) (hM : HasDerivAt M Md s) (hPd : HasDerivAt P Pd s) :
    HasDerivAt (fun t => B t + M t / P t) (Bd + Md / P s - Pd / P s * (M s / P s)) s ∧
      (Bd + Md / P s = r * B s + Y - T - C ↔
        Bd + Md / P s - Pd / P s * (M s / P s) =
          r * (B s + M s / P s) + Y - T - C - (r + Pd / P s) * (M s / P s)) := by
  refine ⟨?_, ?_⟩
  · have := hB.add (hM.div hPd hP.ne')
    refine this.congr_deriv ?_
    field_simp
    ring
  · constructor <;> intro h <;> linarith

/-! ## A.2 The maximum principle: sufficiency (Mangasarian/Arrow) -/

/-- The supporting-hyperplane inequality for a concave function on a real normed space
(generalising `MoneyInUtility.concave_le_tangent`): `U y ≤ U x + L (y − x)`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem concave_le_tangent_gen {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {U : V → ℝ} {S : Set V} (hU : ConcaveOn ℝ S U) {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    {L : V →L[ℝ] ℝ} (hL : HasFDerivAt U L x) : U y ≤ U x + L (y - x) := by
  set g : ℝ → ℝ := fun τ => U (x + τ • (y - x)) with hg
  have hline : HasDerivAt (fun τ : ℝ => x + τ • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hL' : HasFDerivAt U L (x + (0 : ℝ) • (y - x)) := by simpa using hL
  have hgd : HasDerivAt g (L (y - x)) 0 := hL'.comp_hasDerivAt (0 : ℝ) hline
  have hslope := hasDerivAt_iff_tendsto_slope.mp hgd
  have hslope' : Tendsto (slope g 0) (𝓝[>] 0) (𝓝 (L (y - x))) :=
    hslope.mono_left (nhdsWithin_mono _ (fun τ (hτ : 0 < τ) => ne_of_gt hτ))
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), U y - U x ≤ slope g 0 τ := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with τ hτ
    obtain ⟨h0, h1⟩ := hτ
    have hc := hU.2 hx hy (show (0 : ℝ) ≤ 1 - τ by linarith) h0.le (by ring)
    have heq : (1 - τ) • x + τ • y = x + τ • (y - x) := by
      rw [sub_smul, one_smul, smul_sub]; abel
    rw [heq, smul_eq_mul, smul_eq_mul] at hc
    rw [slope_def_field, hg]
    simp only [zero_smul, add_zero, sub_zero]
    rw [le_div_iff₀ h0]
    linarith
  have := ge_of_tendsto hslope' hev
  linarith

/-- The Hamiltonian of problem (12)–(14), O&R p. 748:
`H = u(c) + λ F(Q, c, s) − ν G(Q, c, s)` (current-value form). -/
def hamiltonian {E : Type*} (u : E → ℝ) (F G : ℝ → ℝ → E → ℝ) (lam ν : ℝ) (s : ℝ) (Q : ℝ)
    (c : E) : ℝ :=
  u c + lam * F s Q c - ν * G s Q c

/-- **The maximum principle as a sufficient condition, finite horizon** (Mangasarian 1966;
O&R p. 748 made precise). Let `(Q^*, c^*)` satisfy the state equation (13) and constraint (14),
let the costate obey `λ̇ = δλ − ∂H/∂Q` and `∂H/∂c = 0` (condition 1 of the book's box), and let
the Hamiltonian be jointly concave in `(Q, c)`. Then for every feasible rival `(Q, c)` with the
same initial state and every `T ≥ 0`,
`∫₀^T e^{−δs}[u(c) − u(c^*)] ds ≤ e^{−δT}λ(T)(Q^*(T) − Q(T))`. -/
theorem mangasarian_finite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {F G : ℝ → ℝ → E → ℝ} {δ : ℝ} {lam ν : ℝ → ℝ} {K : Set E}
    {Qs Q : ℝ → ℝ} {cs c : ℝ → E} {L : ℝ → (ℝ × E →L[ℝ] ℝ)}
    (hconc : ∀ s, 0 ≤ s → ConcaveOn ℝ (Set.univ ×ˢ K)
      (fun x : ℝ × E => hamiltonian u F G (lam s) (ν s) s x.1 x.2))
    (hdiff : ∀ s, 0 ≤ s → HasFDerivAt
      (fun x : ℝ × E => hamiltonian u F G (lam s) (ν s) s x.1 x.2) (L s) (Qs s, cs s))
    (hfoc : ∀ s, 0 ≤ s → ∀ e, L s (0, e) = 0)
    (hlam : ∀ s, HasDerivAt lam (δ * lam s - L s (1, 0)) s)
    (hQs : ∀ s, HasDerivAt Qs (F s (Qs s) (cs s)) s)
    (hGs : ∀ s, 0 ≤ s → G s (Qs s) (cs s) = 0) (hcs : ∀ s, 0 ≤ s → cs s ∈ K)
    (hQ : ∀ s, HasDerivAt Q (F s (Q s) (c s)) s) (hG : ∀ s, 0 ≤ s → G s (Q s) (c s) = 0)
    (hc : ∀ s, 0 ≤ s → c s ∈ K) (h0 : Q 0 = Qs 0) {T : ℝ} (hT : 0 ≤ T)
    (hint : IntervalIntegrable (fun s => Real.exp (-δ * s) * (u (c s) - u (cs s))) volume 0 T) :
    ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * (u (c s) - u (cs s)) ≤
      Real.exp (-δ * T) * lam T * (Qs T - Q T) := by
  set g : ℝ → ℝ := fun s => Real.exp (-δ * s) * lam s * (Qs s - Q s) with hg
  set g' : ℝ → ℝ := fun s => Real.exp (-δ * s) *
    (-(L s (1, 0)) * (Qs s - Q s) + lam s * (F s (Qs s) (cs s) - F s (Q s) (c s))) with hg'
  have hgd : ∀ s, HasDerivAt g (g' s) s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (-δ * s)) (Real.exp (-δ * s) * (-δ)) s := by
      have := ((hasDerivAt_id s).const_mul (-δ)).exp
      simp only [id, mul_one] at this
      exact this
    have := (he.mul (hlam s)).mul ((hQs s).sub (hQ s))
    refine this.congr_deriv ?_
    simp only [hg', Pi.mul_apply, Pi.sub_apply]
    ring
  have hle : ∀ s, 0 ≤ s → Real.exp (-δ * s) * (u (c s) - u (cs s)) ≤ g' s := by
    intro s hs
    have t := concave_le_tangent_gen (hconc s hs) (x := (Qs s, cs s)) (y := (Q s, c s))
      ⟨Set.mem_univ _, hcs s hs⟩ ⟨Set.mem_univ _, hc s hs⟩ (hdiff s hs)
    have hsplit : ((Q s, c s) - (Qs s, cs s) : ℝ × E) =
        (Q s - Qs s) • ((1 : ℝ), (0 : E)) + ((0 : ℝ), c s - cs s) := by
      ext <;> simp
    rw [hsplit, map_add, map_smul, hfoc s hs, add_zero, smul_eq_mul] at t
    simp only [hamiltonian, hGs s hs, hG s hs, mul_zero, sub_zero] at t
    have hepos := Real.exp_pos (-δ * s)
    simp only [hg']
    have : u (c s) - u (cs s) ≤ -(L s (1, 0)) * (Qs s - Q s) +
        lam s * (F s (Qs s) (cs s) - F s (Q s) (c s)) := by nlinarith
    exact mul_le_mul_of_nonneg_left this hepos.le
  have hint' : IntegrableOn (fun s => Real.exp (-δ * s) * (u (c s) - u (cs s))) (Set.Icc 0 T) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).2 ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1
      hint)
  have key := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hT
    (fun s _ => (hgd s).continuousAt.continuousWithinAt)
    (fun s _ => (hgd s).hasDerivWithinAt) hint' (fun s hs => hle s hs.1.le)
  have hg0 : g 0 = 0 := by simp [hg, h0]
  rw [hg0, sub_zero] at key
  exact key

/-- **Arrow's sufficiency theorem, finite horizon** (Arrow–Kurz 1970; the alternative concavity
condition of O&R p. 748): instead of joint concavity of `H`, suppose the Hamiltonian evaluated at
any state and feasible control is bounded by its value at the candidate plus a linear term,
`H(Q, c) ≤ H(Q^*, c^*) + H_Q (Q − Q^*)` — which holds when `c^*` maximises `H` and the maximised
Hamiltonian is concave in `Q` with supergradient `H_Q` — and let `λ̇ = δλ − H_Q`. Then the same
bound as in `mangasarian_finite` holds. -/
theorem arrow_finite {E : Type*} {u : E → ℝ} {F G : ℝ → ℝ → E → ℝ} {δ : ℝ} {lam ν LQ : ℝ → ℝ}
    {K : Set E} {Qs Q : ℝ → ℝ} {cs c : ℝ → E}
    (harrow : ∀ s, 0 ≤ s → ∀ q, ∀ x ∈ K, hamiltonian u F G (lam s) (ν s) s q x ≤
      hamiltonian u F G (lam s) (ν s) s (Qs s) (cs s) + LQ s * (q - Qs s))
    (hlam : ∀ s, HasDerivAt lam (δ * lam s - LQ s) s)
    (hQs : ∀ s, HasDerivAt Qs (F s (Qs s) (cs s)) s)
    (hGs : ∀ s, 0 ≤ s → G s (Qs s) (cs s) = 0) (hQ : ∀ s, HasDerivAt Q (F s (Q s) (c s)) s)
    (hG : ∀ s, 0 ≤ s → G s (Q s) (c s) = 0) (hc : ∀ s, 0 ≤ s → c s ∈ K) (h0 : Q 0 = Qs 0)
    {T : ℝ} (hT : 0 ≤ T)
    (hint : IntervalIntegrable (fun s => Real.exp (-δ * s) * (u (c s) - u (cs s))) volume 0 T) :
    ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * (u (c s) - u (cs s)) ≤
      Real.exp (-δ * T) * lam T * (Qs T - Q T) := by
  set g : ℝ → ℝ := fun s => Real.exp (-δ * s) * lam s * (Qs s - Q s) with hg
  set g' : ℝ → ℝ := fun s => Real.exp (-δ * s) *
    (-(LQ s) * (Qs s - Q s) + lam s * (F s (Qs s) (cs s) - F s (Q s) (c s))) with hg'
  have hgd : ∀ s, HasDerivAt g (g' s) s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (-δ * s)) (Real.exp (-δ * s) * (-δ)) s := by
      have := ((hasDerivAt_id s).const_mul (-δ)).exp
      simp only [id, mul_one] at this
      exact this
    have := (he.mul (hlam s)).mul ((hQs s).sub (hQ s))
    refine this.congr_deriv ?_
    simp only [hg', Pi.mul_apply, Pi.sub_apply]
    ring
  have hle : ∀ s, 0 ≤ s → Real.exp (-δ * s) * (u (c s) - u (cs s)) ≤ g' s := by
    intro s hs
    have t := harrow s hs (Q s) (c s) (hc s hs)
    simp only [hamiltonian, hGs s hs, hG s hs, mul_zero, sub_zero] at t
    simp only [hg']
    have : u (c s) - u (cs s) ≤ -(LQ s) * (Qs s - Q s) +
        lam s * (F s (Qs s) (cs s) - F s (Q s) (c s)) := by nlinarith
    exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
  have hint' : IntegrableOn (fun s => Real.exp (-δ * s) * (u (c s) - u (cs s))) (Set.Icc 0 T) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).2 ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1
      hint)
  have key := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hT
    (fun s _ => (hgd s).continuousAt.continuousWithinAt)
    (fun s _ => (hgd s).hasDerivWithinAt) hint' (fun s hs => hle s hs.1.le)
  have hg0 : g 0 = 0 := by simp [hg, h0]
  rw [hg0, sub_zero] at key
  exact key

/-- **The maximum principle as a sufficient condition, infinite horizon** (O&R p. 748, the box and
(15), made precise): under the hypotheses of `mangasarian_finite` for every horizon, if both
utility integrals converge and the boundary term satisfies
`∀ ε > 0, frequently e^{−δT}λ(T)(Q^*(T) − Q(T)) < ε`, then the candidate is at least as good as
the rival: `∫₀^∞ e^{−δs}u(c) ≤ ∫₀^∞ e^{−δs}u(c^*)`. -/
theorem mangasarian_infinite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {F G : ℝ → ℝ → E → ℝ} {δ : ℝ} {lam ν : ℝ → ℝ} {K : Set E}
    {Qs Q : ℝ → ℝ} {cs c : ℝ → E} {L : ℝ → (ℝ × E →L[ℝ] ℝ)} {U Us : ℝ}
    (hconc : ∀ s, 0 ≤ s → ConcaveOn ℝ (Set.univ ×ˢ K)
      (fun x : ℝ × E => hamiltonian u F G (lam s) (ν s) s x.1 x.2))
    (hdiff : ∀ s, 0 ≤ s → HasFDerivAt
      (fun x : ℝ × E => hamiltonian u F G (lam s) (ν s) s x.1 x.2) (L s) (Qs s, cs s))
    (hfoc : ∀ s, 0 ≤ s → ∀ e, L s (0, e) = 0)
    (hlam : ∀ s, HasDerivAt lam (δ * lam s - L s (1, 0)) s)
    (hQs : ∀ s, HasDerivAt Qs (F s (Qs s) (cs s)) s)
    (hGs : ∀ s, 0 ≤ s → G s (Qs s) (cs s) = 0) (hcs : ∀ s, 0 ≤ s → cs s ∈ K)
    (hQ : ∀ s, HasDerivAt Q (F s (Q s) (c s)) s) (hG : ∀ s, 0 ≤ s → G s (Q s) (c s) = 0)
    (hc : ∀ s, 0 ≤ s → c s ∈ K) (h0 : Q 0 = Qs 0)
    (hint1 : ∀ T, IntervalIntegrable (fun s => Real.exp (-δ * s) * u (c s)) volume 0 T)
    (hint2 : ∀ T, IntervalIntegrable (fun s => Real.exp (-δ * s) * u (cs s)) volume 0 T)
    (hU : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (c s)) atTop (𝓝 U))
    (hUs : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (cs s)) atTop (𝓝 Us))
    (hbd : ∀ ε > 0, ∃ᶠ T in atTop, Real.exp (-δ * T) * lam T * (Qs T - Q T) < ε) :
    U ≤ Us := by
  have hdiffT : ∀ T, 0 ≤ T → (∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (c s)) -
      ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (cs s) ≤
      Real.exp (-δ * T) * lam T * (Qs T - Q T) := by
    intro T hT
    rw [← intervalIntegral.integral_sub (hint1 T) (hint2 T)]
    have := mangasarian_finite hconc hdiff hfoc hlam hQs hGs hcs hQ hG hc h0 hT
      (by
        have := (hint1 T).sub (hint2 T)
        exact this.congr fun s _ => (mul_sub _ _ _).symm)
    refine le_trans (le_of_eq ?_) this
    congr 1; funext s; ring
  by_contra hlt
  push Not at hlt
  have hlim := hU.sub hUs
  obtain ⟨T, hT1, hT2, hT3⟩ := ((hbd ((U - Us) / 2) (by linarith)).and_eventually
    ((hlim.eventually (lt_mem_nhds (show (U - Us) / 2 < U - Us by linarith))).and
      (eventually_ge_atTop 0))).exists
  have := hdiffT T hT3
  linarith

/-- **The book's transversality condition (15) plus a no-Ponzi condition on rivals** give the
boundary condition of `mangasarian_infinite` (O&R p. 748): if `e^{−δT}λ(T)Q^*(T) → 0` and
`liminf e^{−δT}λ(T)Q(T) ≥ 0`, then `e^{−δT}λ(T)(Q^*(T) − Q(T)) < ε` eventually, for all `ε > 0`. -/
theorem boundary_of_tvc_noPonzi {δ : ℝ} {lam Qs Q : ℝ → ℝ}
    (htvc : Tendsto (fun T => Real.exp (-δ * T) * lam T * Qs T) atTop (𝓝 0))
    (hnp : ∀ ε > 0, ∀ᶠ T in atTop, -ε < Real.exp (-δ * T) * lam T * Q T) :
    ∀ ε > 0, ∃ᶠ T in atTop, Real.exp (-δ * T) * lam T * (Qs T - Q T) < ε := by
  intro ε hε
  refine ((htvc.eventually (gt_mem_nhds (half_pos hε))).and (hnp (ε / 2) (half_pos hε))).mono
    (fun T ⟨h1, h2⟩ => ?_) |>.frequently
  have : Real.exp (-δ * T) * lam T * (Qs T - Q T) =
      Real.exp (-δ * T) * lam T * Qs T - Real.exp (-δ * T) * lam T * Q T := by ring
  rw [this]
  linarith

/-! ### The costate path and the monetary problem -/

/-- **The costate path (A.3.1)**, O&R p. 750: the solution of `λ̇ = λ(δ − r)` is
`λ(t) = λ(0) e^{(δ−r)t}`; hence `e^{−δT}λ(T) = λ(0)e^{−rT}` (so the TVC (15) is
`λ(0) lim e^{−rT}Q(T) = 0`). -/
theorem costate_solution {r δ : ℝ} {lam : ℝ → ℝ}
    (hlam : ∀ s, HasDerivAt lam (lam s * (δ - r)) s) (t : ℝ) :
    lam t = lam 0 * Real.exp ((δ - r) * t) ∧
      Real.exp (-δ * t) * lam t = lam 0 * Real.exp (-r * t) := by
  have hw : ∀ s, HasDerivAt (fun s => lam s * Real.exp (-(δ - r) * s)) 0 s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (-(δ - r) * s)) (Real.exp (-(δ - r) * s) *
        (-(δ - r))) s := by
      have := ((hasDerivAt_id s).const_mul (-(δ - r))).exp
      simp only [id, mul_one] at this
      exact this
    have := (hlam s).mul he
    refine this.congr_deriv ?_
    ring
  have hconst : ∀ s, lam s * Real.exp (-(δ - r) * s) = lam 0 * Real.exp (-(δ - r) * 0) := by
    intro s
    exact is_const_of_deriv_eq_zero (fun s => (hw s).differentiableAt) (fun s => (hw s).deriv) s 0
  have h1 : lam t = lam 0 * Real.exp ((δ - r) * t) := by
    have := hconst t
    simp only [mul_zero, Real.exp_zero, mul_one] at this
    have he : Real.exp (-(δ - r) * t) * Real.exp ((δ - r) * t) = 1 := by
      rw [← Real.exp_add, show -(δ - r) * t + (δ - r) * t = 0 by ring, Real.exp_zero]
    calc lam t = lam t * (Real.exp (-(δ - r) * t) * Real.exp ((δ - r) * t)) := by rw [he, mul_one]
      _ = lam 0 * Real.exp ((δ - r) * t) := by rw [← mul_assoc, this]
  refine ⟨h1, ?_⟩
  rw [h1, mul_left_comm, ← Real.exp_add]
  congr 2
  ring

/-- **The book's Hamiltonian with money and bonds as separate controls** (O&R p. 749): with
`H = u(C, M/P) + λ(rQ + Y − T − C − iM/P) − ν(Q − B − M/P)`, the conditions `∂H/∂C = 0`,
`∂H/∂M = 0`, `∂H/∂B = 0` and `λ̇ = δλ − ∂H/∂Q` "boil down to" (3), (8) and (9): `ν = 0`,
`u_C = λ`, `u_{M/P} = λi`, `λ̇ = λ(δ − r)`. -/
theorem monetary_hamiltonian_focs {uC uM lam lamd ν i r δ P : ℝ} (hP : P ≠ 0)
    (hC : uC - lam = 0) (hM : 1 / P * (uM - lam * i + ν) = 0) (hB : ν = 0)
    (hQ : lamd = δ * lam - (lam * r - ν)) :
    ν = 0 ∧ uC = lam ∧ uM = lam * i ∧ lamd = lam * (δ - r) := by
  subst hB
  refine ⟨rfl, by linarith, ?_, by rw [hQ]; ring⟩
  have := (mul_eq_zero.1 hM).resolve_left (one_div_ne_zero hP)
  linarith

/-- The Hamiltonian of the monetary problem is jointly concave in wealth and the controls
`(C, M/P)` when `u` is concave (it is `u` plus an affine function), O&R p. 749. -/
theorem monetary_hamiltonian_concave {u : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)} (hK : Convex ℝ K)
    (hconc : ConcaveOn ℝ K u) (a r b c0 d : ℝ) :
    ConcaveOn ℝ (Set.univ ×ˢ K)
      (fun x : ℝ × (ℝ × ℝ) => u x.2 + a * (r * x.1 + b - x.2.1 - c0 * x.2.2) - d * 0) := by
  refine ⟨convex_univ.prod hK, fun x hx y hy α β hα hβ hαβ => ?_⟩
  have h1 := hconc.2 hx.2 hy.2 hα hβ hαβ
  simp only [smul_eq_mul, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] at h1 ⊢
  have hb : β = 1 - α := by linarith
  subst hb
  nlinarith [h1]

/-- **Sufficiency in the monetary problem** (O&R Supplement A.2–A.3, pp. 748–750, made
precise): with `u` concave and differentiable on the positive quadrant, a plan
`c^* = (C, M/P)` with wealth path `Q̇^* = rQ^* + y − C − iM/P` satisfying (3) `u_C = λ`, (8)
`u_{M/P} = λi`, (9) `λ̇ = λ(δ − r)` with `λ(0) > 0`, is at least as good as every feasible
rival with the same initial wealth (and a convergent utility integral) for which
`e^{−rT}(Q^*(T) − Q(T)) < ε` frequently, for every `ε > 0` — which holds when the candidate
satisfies the transversality condition and the rival the no-Ponzi condition
(`monetary_boundary`). -/
theorem monetary_sufficiency {u : ℝ × ℝ → ℝ} {uC um : ℝ × ℝ → ℝ} {r δ U Us : ℝ}
    {y i lam Qs Q : ℝ → ℝ} {cs c : ℝ → ℝ × ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) u)
    (hdiff : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), HasFDerivAt u (grad (uC p) (um p)) p)
    (hcs : ∀ s, 0 ≤ s → cs s ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
    (hc : ∀ s, 0 ≤ s → c s ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
    (hfocC : ∀ s, 0 ≤ s → uC (cs s) = lam s) (hfocM : ∀ s, 0 ≤ s → um (cs s) = lam s * i s)
    (hlam : ∀ s, HasDerivAt lam (lam s * (δ - r)) s) (hlam0 : 0 < lam 0)
    (hQs : ∀ s, HasDerivAt Qs (r * Qs s + y s - (cs s).1 - i s * (cs s).2) s)
    (hQ : ∀ s, HasDerivAt Q (r * Q s + y s - (c s).1 - i s * (c s).2) s) (h0 : Q 0 = Qs 0)
    (hbd' : ∀ ε > 0, ∃ᶠ T in atTop, Real.exp (-r * T) * (Qs T - Q T) < ε)
    (hint1 : ∀ T, IntervalIntegrable (fun s => Real.exp (-δ * s) * u (c s)) volume 0 T)
    (hint2 : ∀ T, IntervalIntegrable (fun s => Real.exp (-δ * s) * u (cs s)) volume 0 T)
    (hU : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (c s)) atTop (𝓝 U))
    (hUs : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (cs s)) atTop (𝓝 Us)) :
    U ≤ Us := by
  set F : ℝ → ℝ → ℝ × ℝ → ℝ := fun s q x => r * q + y s - x.1 - i s * x.2 with hF
  set G : ℝ → ℝ → ℝ × ℝ → ℝ := fun _ _ _ => 0 with hG
  have hK : Convex ℝ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := (convex_Ioi 0).prod (convex_Ioi 0)
  set L : ℝ → (ℝ × (ℝ × ℝ) →L[ℝ] ℝ) := fun s =>
    (grad (uC (cs s)) (um (cs s))).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
      lam s • ((r • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) -
        (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) -
        i s • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) with hL
  have hconcH : ∀ s, 0 ≤ s → ConcaveOn ℝ (Set.univ ×ˢ (Set.Ioi 0 ×ˢ Set.Ioi 0))
      (fun x : ℝ × (ℝ × ℝ) => hamiltonian u F G (lam s) 0 s x.1 x.2) := fun s _ =>
    monetary_hamiltonian_concave hK hconc (lam s) r (y s) (i s) 0
  have hdiffH : ∀ s, 0 ≤ s → HasFDerivAt
      (fun x : ℝ × (ℝ × ℝ) => hamiltonian u F G (lam s) 0 s x.1 x.2) (L s) (Qs s, cs s) := by
    intro s hs
    have h1 : HasFDerivAt (fun x : ℝ × (ℝ × ℝ) => u x.2)
        ((grad (uC (cs s)) (um (cs s))).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
        (Qs s, cs s) := (hdiff _ (hcs s hs)).comp (Qs s, cs s) hasFDerivAt_snd
    have h2 : HasFDerivAt (fun x : ℝ × (ℝ × ℝ) => r * x.1 + y s - x.2.1 - i s * x.2.2)
        ((r • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) -
          (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) -
          i s • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
        (Qs s, cs s) := by
      have a1 := ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt (x := (Qs s, cs s))).const_mul r
      have a2 := ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt (x := (Qs s, cs s))
      have a3 := (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt (x := (Qs s, cs s))).const_mul (i s)
      exact ((a1.add_const (y s)).sub a2).sub a3
    have h3 := (h1.add (h2.const_mul (lam s))).sub_const (0 * 0)
    exact h3
  have hfoc : ∀ s, 0 ≤ s → ∀ e, L s (0, e) = 0 := by
    intro s hs e
    simp [hL, grad_apply, hfocC s hs, hfocM s hs]
    ring
  have hlamL : ∀ s, HasDerivAt lam (δ * lam s - L s (1, 0)) s := by
    intro s
    refine (hlam s).congr_deriv ?_
    simp [hL, grad_apply]
    ring
  have hsol := costate_solution hlam
  refine mangasarian_infinite (G := G) (ν := fun _ => 0) (K := Set.Ioi 0 ×ˢ Set.Ioi 0)
    (L := L) hconcH hdiffH hfoc hlamL hQs (fun _ _ => rfl) hcs hQ (fun _ _ => rfl) hc h0
    hint1 hint2 hU hUs (fun ε hε => ?_)
  refine (hbd' (ε / lam 0) (div_pos hε hlam0)).mono fun T hT => ?_
  rw [(hsol T).2, mul_assoc]
  have := mul_lt_mul_of_pos_left hT hlam0
  rwa [mul_div_cancel₀ _ hlam0.ne'] at this

/-- **Sufficiency with the book's transversality condition (15)–(16) and a no-Ponzi condition on
rivals** (O&R p. 750): `e^{−rT}Q^*(T) → 0` and `liminf e^{−rT}Q(T) ≥ 0` give the boundary
condition of `monetary_sufficiency`. -/
theorem monetary_boundary {r : ℝ} {Qs Q : ℝ → ℝ}
    (htvc : ∀ ε > 0, ∃ᶠ T in atTop, Real.exp (-r * T) * Qs T < ε)
    (hnp : ∀ ε > 0, ∀ᶠ T in atTop, -ε < Real.exp (-r * T) * Q T) :
    ∀ ε > 0, ∃ᶠ T in atTop, Real.exp (-r * T) * (Qs T - Q T) < ε := by
  intro ε hε
  refine ((htvc (ε / 2) (half_pos hε)).and_eventually (hnp (ε / 2) (half_pos hε))).mono
    fun T ⟨h1, h2⟩ => ?_
  have : Real.exp (-r * T) * (Qs T - Q T) = Real.exp (-r * T) * Qs T -
      Real.exp (-r * T) * Q T := by ring
  rw [this]
  linarith

/-! ### Why the no-Ponzi condition on rivals is needed -/

/-- `∫₀^T e^{−rs} ds = (1 − e^{−rT})/r` for `r ≠ 0`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem integral_exp_neg_mul {r T : ℝ} (hr : r ≠ 0) :
    ∫ s in (0 : ℝ)..T, Real.exp (-r * s) = (1 - Real.exp (-r * T)) / r := by
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) T, HasDerivAt (fun s => -Real.exp (-r * s) / r)
      (Real.exp (-r * s)) s := by
    intro s _
    have := (((hasDerivAt_id s).const_mul (-r)).exp.neg).div_const r
    refine this.congr_deriv ?_
    simp only [id, mul_one]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable
      (μ := volume) _ _)]
  simp only [mul_zero, Real.exp_zero]
  field_simp
  ring

/-- **The transversality condition (15) alone is not sufficient** (a correction to the box on
O&R p. 748): with `u = log C`, `Q̇ = rQ − C`, `δ = r > 0` and `Q_0 > 0`, the plan
`C^* = rQ_0`, `Q^* ≡ Q_0` satisfies (13), `∂H/∂C = 0` with `λ ≡ 1/(rQ_0)`, the costate equation
and (15); but the Ponzi scheme `C ≡ rQ_0 + 1`, `Q(t) = Q_0 − (e^{rt} − 1)/r` is feasible and
yields strictly higher utility at every horizon and in the limit (`log(rQ_0+1)/r > log(rQ_0)/r`).
It violates the no-Ponzi condition: `e^{−rT}Q(T) → −1/r`. -/
theorem ponzi_counterexample {r Q0 : ℝ} (hr : 0 < r) (hQ0 : 0 < Q0) :
    (∀ t, HasDerivAt (fun _ : ℝ => Q0) (r * Q0 - r * Q0) t) ∧ (r * Q0)⁻¹ = 1 / (r * Q0) ∧
      (∀ t, HasDerivAt (fun _ : ℝ => 1 / (r * Q0)) (r * (1 / (r * Q0)) - 1 / (r * Q0) * r) t) ∧
      Tendsto (fun T => Real.exp (-r * T) * (1 / (r * Q0)) * Q0) atTop (𝓝 0) ∧
      (∀ t, HasDerivAt (fun t => Q0 - (Real.exp (r * t) - 1) / r)
        (r * (Q0 - (Real.exp (r * t) - 1) / r) - (r * Q0 + 1)) t) ∧
      (fun t => Q0 - (Real.exp (r * t) - 1) / r) 0 = Q0 ∧
      (∀ T, 0 < T → ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * Real.log (r * Q0) <
        ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * Real.log (r * Q0 + 1)) ∧
      Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * Real.log (r * Q0)) atTop
        (𝓝 (Real.log (r * Q0) / r)) ∧
      Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * Real.log (r * Q0 + 1)) atTop
        (𝓝 (Real.log (r * Q0 + 1) / r)) ∧
      Real.log (r * Q0) / r < Real.log (r * Q0 + 1) / r ∧
      Tendsto (fun T => Real.exp (-r * T) * (Q0 - (Real.exp (r * T) - 1) / r)) atTop
        (𝓝 (-(1 / r))) := by
  have hr0 := hr.ne'
  have hrQ : 0 < r * Q0 := mul_pos hr hQ0
  have hexp0 : Tendsto (fun T : ℝ => Real.exp (-r * T)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hr)
    refine this.congr fun T => ?_
    simp [neg_mul]
  have hint : ∀ (κ : ℝ) T, ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * κ =
      κ * ((1 - Real.exp (-r * T)) / r) := by
    intro κ T
    rw [intervalIntegral.integral_mul_const, integral_exp_neg_mul hr0]; ring
  have hlim : ∀ κ : ℝ, Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * κ) atTop
      (𝓝 (κ / r)) := by
    intro κ
    simp only [hint]
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hexp0).div_const r |>.const_mul κ
    rw [sub_zero] at this
    refine this.congr' (Eventually.of_forall fun T => rfl) |>.trans ?_
    rw [mul_one_div]
  have hlog : Real.log (r * Q0) < Real.log (r * Q0 + 1) :=
    Real.log_lt_log hrQ (by linarith)
  refine ⟨fun t => (hasDerivAt_const t Q0).congr_deriv (by ring), by rw [one_div],
    fun t => (hasDerivAt_const t (1 / (r * Q0))).congr_deriv (by ring), ?_, fun t => ?_, by simp,
    fun T hT => ?_,
    hlim _, hlim _, div_lt_div_of_pos_right hlog hr, ?_⟩
  · have := hexp0.mul_const (1 / (r * Q0) * Q0)
    rw [zero_mul] at this
    exact this.congr fun T => by ring
  · have := ((((hasDerivAt_id t).const_mul r).exp.sub_const 1).div_const r).const_sub Q0
    refine this.congr_deriv ?_
    simp only [id, mul_one]
    field_simp
    ring
  · rw [hint, hint]
    have h1 : 0 < (1 - Real.exp (-r * T)) / r := by
      apply div_pos _ hr
      have : Real.exp (-r * T) < 1 := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by nlinarith)
      linarith
    exact mul_lt_mul_of_pos_right hlog h1
  · have h1 : ∀ T, Real.exp (-r * T) * (Q0 - (Real.exp (r * T) - 1) / r) =
        Real.exp (-r * T) * Q0 + Real.exp (-r * T) / r - 1 / r := by
      intro T
      have : Real.exp (-r * T) * Real.exp (r * T) = 1 := by
        rw [← Real.exp_add]; simp
      calc Real.exp (-r * T) * (Q0 - (Real.exp (r * T) - 1) / r)
          = Real.exp (-r * T) * Q0 - (Real.exp (-r * T) * Real.exp (r * T) -
            Real.exp (-r * T)) / r := by ring
        _ = _ := by rw [this]; ring
    simp only [h1]
    have := ((hexp0.mul_const Q0).add (hexp0.div_const r)).sub_const (1 / r)
    simpa using this

/-! ### The Halkin counterexample: the transversality condition is not necessary -/

/-- **Halkin (1974): feasible paths of `ẋ = (1 − x)u`, `x(0) = 0`, `u ∈ [0, 1]` continuous**
never reach `x = 1`: `1 − x(t) = e^{−∫₀^t u}`; and the objective up to `T` is
`∫₀^T (1 − x)u = x(T) < 1`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem halkin_rival {x u : ℝ → ℝ} (hu : Continuous u)
    (hx : ∀ t, HasDerivAt x ((1 - x t) * u t) t) (hx0 : x 0 = 0) (T : ℝ) :
    ∫ s in (0 : ℝ)..T, (1 - x s) * u s = x T ∧ x T < 1 := by
  set Uu : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, u s with hUu
  have hUd : ∀ t, HasDerivAt Uu (u t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hu.intervalIntegrable (μ := volume) _ _)
      (hu.aestronglyMeasurable.stronglyMeasurableAtFilter) hu.continuousAt
  have hw : ∀ t, HasDerivAt (fun t => (1 - x t) * Real.exp (Uu t)) 0 t := by
    intro t
    have := ((hx t).const_sub 1).mul ((hUd t).exp)
    refine this.congr_deriv ?_
    ring
  have hconst : ∀ t, (1 - x t) * Real.exp (Uu t) = 1 := by
    intro t
    have := is_const_of_deriv_eq_zero (fun t => (hw t).differentiableAt)
      (fun t => (hw t).deriv) t 0
    rw [this, hx0]
    simp [hUu]
  have hpos : 0 < 1 - x T := by
    have h := hconst T
    by_contra hle
    push Not at hle
    have := Real.exp_pos (Uu T)
    nlinarith
  refine ⟨?_, by linarith⟩
  have hcont : Continuous fun s => (1 - x s) * u s := by
    have : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hx t)
    (hcont.intervalIntegrable (μ := volume) _ _), hx0, sub_zero]

/-- **Halkin's example: the candidate** (Halkin 1974; O&R p. 748 claims (15) necessary). The
control `u^* = 1/2` gives `x^*(t) = 1 − e^{−t/2}`, and its objective `∫₀^T (1 − x^*)u^* = x^*(T)`
converges to `1`, the supremum over all feasible paths (`halkin_rival`); so it is optimal.
With `H = (1 + λ)(1 − x)u`, the maximum-principle conditions `∂H/∂u = 0` and
`λ̇ = −∂H/∂x = (1+λ)u` hold for `λ ≡ −1`, and that is the ONLY costate satisfying `∂H/∂u = 0`;
yet `λ(T)x^*(T) → −1 ≠ 0`: the transversality condition fails at the optimum. -/
theorem halkin_candidate :
    (∀ t, HasDerivAt (fun t => 1 - Real.exp (-(t / 2)))
      ((1 - (1 - Real.exp (-(t / 2)))) * (1 / 2)) t) ∧
    Tendsto (fun T => ∫ s in (0 : ℝ)..T, (1 - (1 - Real.exp (-(s / 2)))) * (1 / 2)) atTop (𝓝 1) ∧
    (∀ t, (1 + (-1 : ℝ)) * (1 - (1 - Real.exp (-(t / 2)))) = 0) ∧
    (∀ t, HasDerivAt (fun _ : ℝ => (-1 : ℝ)) ((1 + (-1 : ℝ)) * (1 / 2)) t) ∧
    (∀ (lam : ℝ → ℝ) t, (1 + lam t) * (1 - (1 - Real.exp (-(t / 2)))) = 0 → lam t = -1) ∧
    Tendsto (fun T => (-1 : ℝ) * (1 - Real.exp (-(T / 2)))) atTop (𝓝 (-1)) := by
  have hx : ∀ t, HasDerivAt (fun t => 1 - Real.exp (-(t / 2)))
      ((1 - (1 - Real.exp (-(t / 2)))) * (1 / 2)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -(t / 2)) (-(1 / 2)) t :=
      ((hasDerivAt_id t).div_const 2).neg
    have := h1.exp.const_sub 1
    refine this.congr_deriv ?_
    ring
  have hexp : Tendsto (fun T : ℝ => Real.exp (-(T / 2))) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const two_pos)
    exact this.congr fun T => by simp
  refine ⟨hx, ?_, fun t => by ring, fun t => by simpa using hasDerivAt_const t (-1 : ℝ),
    fun lam t h => ?_, ?_⟩
  · have hint : ∀ T, ∫ s in (0 : ℝ)..T, (1 - (1 - Real.exp (-(s / 2)))) * (1 / 2) =
        1 - Real.exp (-(T / 2)) := by
      intro T
      have hcont : Continuous fun s : ℝ => (1 - (1 - Real.exp (-(s / 2)))) * (1 / 2) := by
        fun_prop
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hx t)
        (hcont.intervalIntegrable (μ := volume) _ _)]
      simp
    simp only [hint]
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub hexp
    rwa [sub_zero] at this
  · have h1 : 0 < 1 - (1 - Real.exp (-(t / 2))) := by
      have := Real.exp_pos (-(t / 2)); linarith
    have := (mul_eq_zero.1 h).resolve_right h1.ne'
    linarith
  · have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hexp).const_mul (-1 : ℝ)
    simpa using this

/-! ## A.3.1 The economy's consolidated budget constraint -/

/-- **Variation of constants** (O&R p. 749): for continuous net saving `f = Y − T − C − iM/P`,
`Q(T) = e^{rT}(Q_0 + ∫₀^T e^{−rs} f(s) ds)` solves (11) `Q̇ = rQ + f`, and it is the ONLY
differentiable solution with `Q(0) = Q_0`. -/
theorem variation_of_constants {r Q0 : ℝ} {f : ℝ → ℝ} (hf : Continuous f) :
    (∀ t, HasDerivAt (fun t => Real.exp (r * t) * (Q0 + ∫ s in (0 : ℝ)..t,
      Real.exp (-r * s) * f s)) (r * (Real.exp (r * t) * (Q0 + ∫ s in (0 : ℝ)..t,
        Real.exp (-r * s) * f s)) + f t) t) ∧
    ∀ Q : ℝ → ℝ, (∀ t, HasDerivAt Q (r * Q t + f t) t) → Q 0 = Q0 →
      ∀ t, Q t = Real.exp (r * t) * (Q0 + ∫ s in (0 : ℝ)..t, Real.exp (-r * s) * f s) := by
  have hg : Continuous fun s => Real.exp (-r * s) * f s := by fun_prop
  have hI : ∀ t, HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, Real.exp (-r * s) * f s)
      (Real.exp (-r * t) * f t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable (μ := volume) _ _)
      (hg.aestronglyMeasurable.stronglyMeasurableAtFilter) hg.continuousAt
  have he : ∀ (a t : ℝ), HasDerivAt (fun t => Real.exp (a * t)) (Real.exp (a * t) * a) t := by
    intro a t
    have := ((hasDerivAt_id t).const_mul a).exp
    simp only [id, mul_one] at this
    exact this
  have hsol : ∀ t, HasDerivAt (fun t => Real.exp (r * t) * (Q0 + ∫ s in (0 : ℝ)..t,
      Real.exp (-r * s) * f s)) (r * (Real.exp (r * t) * (Q0 + ∫ s in (0 : ℝ)..t,
        Real.exp (-r * s) * f s)) + f t) t := by
    intro t
    have := (he r t).mul ((hI t).const_add Q0)
    refine this.congr_deriv ?_
    have : Real.exp (r * t) * Real.exp (-r * t) = 1 := by rw [← Real.exp_add]; simp
    linear_combination f t * this
  refine ⟨hsol, fun Q hQ hQ0 t => ?_⟩
  have hw : ∀ t, HasDerivAt (fun t => Real.exp (-r * t) * (Q t - Real.exp (r * t) *
      (Q0 + ∫ s in (0 : ℝ)..t, Real.exp (-r * s) * f s))) 0 t := by
    intro t
    have := (he (-r) t).mul ((hQ t).sub (hsol t))
    refine this.congr_deriv ?_
    simp only [Pi.sub_apply]
    ring
  have hc := is_const_of_deriv_eq_zero (fun t => (hw t).differentiableAt) (fun t => (hw t).deriv)
    t 0
  simp only [mul_zero, Real.exp_zero, intervalIntegral.integral_same, add_zero, one_mul, hQ0,
    sub_self] at hc
  have hpos := Real.exp_pos (-r * t)
  have := (mul_eq_zero.1 hc).resolve_left hpos.ne'
  linarith

/-- **The finite-horizon constraint (16)**, O&R p. 750: a wealth path solving (11) satisfies
`∫₀^T e^{−rs}(C + iM/P) + e^{−rT}Q(T) = Q_0 + ∫₀^T e^{−rs}(Y − T) ds`. -/
theorem budget_16 {r : ℝ} {Q y e : ℝ → ℝ} (hy : Continuous y) (he : Continuous e)
    (hQ : ∀ t, HasDerivAt Q (r * Q t + y t - e t) t) (T : ℝ) :
    (∫ s in (0 : ℝ)..T, Real.exp (-r * s) * e s) + Real.exp (-r * T) * Q T =
      Q 0 + ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * y s := by
  have hf : Continuous fun s => y s - e s := hy.sub he
  have hsol := (variation_of_constants (Q0 := Q 0) (r := r) hf).2 Q
    (fun t => (hQ t).congr_deriv (by ring)) rfl T
  have h1 : ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (y s - e s) =
      (∫ s in (0 : ℝ)..T, Real.exp (-r * s) * y s) -
        ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * e s := by
    simp_rw [mul_sub]
    have c1 : Continuous fun s => Real.exp (-r * s) * y s := by fun_prop
    have c2 : Continuous fun s => Real.exp (-r * s) * e s := by fun_prop
    rw [intervalIntegral.integral_sub (c1.intervalIntegrable (μ := volume) 0 T)
      (c2.intervalIntegrable (μ := volume) 0 T)]
  have hQT : Q T = Real.exp (r * T) * (Q 0 + ((∫ s in (0 : ℝ)..T, Real.exp (-r * s) * y s) -
      ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * e s)) := by
    rw [hsol, h1]
  rw [hQT]
  have : Real.exp (-r * T) * Real.exp (r * T) = 1 := by rw [← Real.exp_add]; simp
  linear_combination (Q 0 + ((∫ s in (0 : ℝ)..T, Real.exp (-r * s) * y s) -
    ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * e s)) * this

/-- **The TVC in wealth form** (O&R p. 750): with `λ(t) = λ(0)e^{(δ−r)t}` and `λ(0) = u_C > 0`,
`e^{−δT}λ(T)Q(T) → 0` iff `e^{−rT}Q(T) → 0`. -/
theorem tvc_iff_wealth {r δ : ℝ} {lam Q : ℝ → ℝ}
    (hlam : ∀ s, HasDerivAt lam (lam s * (δ - r)) s) (hlam0 : 0 < lam 0) :
    Tendsto (fun T => Real.exp (-δ * T) * lam T * Q T) atTop (𝓝 0) ↔
      Tendsto (fun T => Real.exp (-r * T) * Q T) atTop (𝓝 0) := by
  have hs := costate_solution hlam
  have heq : ∀ T, Real.exp (-δ * T) * lam T * Q T = lam 0 * (Real.exp (-r * T) * Q T) := by
    intro T; rw [(hs T).2]; ring
  simp only [heq]
  constructor
  · intro h
    have := h.const_mul (lam 0)⁻¹
    rw [mul_zero] at this
    refine this.congr fun T => ?_
    field_simp
  · intro h
    have := h.const_mul (lam 0)
    rwa [mul_zero] at this

/-- **The infinite-horizon constraint (17)**, O&R p. 750: under the TVC `e^{−rT}Q(T) → 0`, if
the present value of disposable income converges to `Y_∞`, the present value of spending on
consumption and money services converges to `Q_0 + Y_∞`. -/
theorem budget_17 {r Yinf : ℝ} {Q y e : ℝ → ℝ} (hy : Continuous y) (he : Continuous e)
    (hQ : ∀ t, HasDerivAt Q (r * Q t + y t - e t) t)
    (htvc : Tendsto (fun T => Real.exp (-r * T) * Q T) atTop (𝓝 0))
    (hY : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * y s) atTop (𝓝 Yinf)) :
    Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * e s) atTop (𝓝 (Q 0 + Yinf)) := by
  have := ((tendsto_const_nhds (x := Q 0)).add hY).sub htvc
  rw [sub_zero] at this
  refine this.congr fun T => ?_
  have := budget_16 hy he hQ T
  linarith

/-- **Integration by parts for seignorage** (O&R p. 751): with `m = M/P` continuously
differentiable, `Ṁ/P = ṁ + πm`, so
`∫₀^T e^{−rs}(ṁ + πm) = e^{−rT}m(T) − m(0) + ∫₀^T e^{−rs}(r + π)m`. -/
theorem seignorage_by_parts {r : ℝ} {m md infl : ℝ → ℝ} (hm : ∀ s, HasDerivAt m (md s) s)
    (hmd : Continuous md) (hπ : Continuous infl) (T : ℝ) :
    ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (md s + infl s * m s) =
      Real.exp (-r * T) * m T - m 0 +
        ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * ((r + infl s) * m s) := by
  have hmc : Continuous m := continuous_iff_continuousAt.2 fun t => (hm t).continuousAt
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) T, HasDerivAt (fun s => Real.exp (-r * s) * m s)
      (Real.exp (-r * s) * md s - r * (Real.exp (-r * s) * m s)) s := by
    intro s _
    have h1 : HasDerivAt (fun s => Real.exp (-r * s)) (Real.exp (-r * s) * (-r)) s := by
      have := ((hasDerivAt_id s).const_mul (-r)).exp
      simpa using this
    exact (h1.mul (hm s)).congr_deriv (by ring)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun s => Real.exp (-r * s) * md s -
      r * (Real.exp (-r * s) * m s)).intervalIntegrable (μ := volume) _ _)
  simp only [mul_zero, Real.exp_zero, one_mul] at hint
  have c1 : Continuous fun s => Real.exp (-r * s) * md s - r * (Real.exp (-r * s) * m s) := by
    fun_prop
  have c2 : Continuous fun s => Real.exp (-r * s) * ((r + infl s) * m s) := by fun_prop
  have hsplit : ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (md s + infl s * m s) =
      (∫ s in (0 : ℝ)..T, (Real.exp (-r * s) * md s - r * (Real.exp (-r * s) * m s))) +
        ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * ((r + infl s) * m s) := by
    rw [← intervalIntegral.integral_add (c1.intervalIntegrable (μ := volume) _ _)
      (c2.intervalIntegrable (μ := volume) _ _)]
    congr 1; funext s; ring
  rw [hsplit, hint]

/-- **The government's intertemporal constraint (18) after integration by parts** (O&R
p. 751): under the no-hyperdeflation condition `e^{−rT}m(T) → 0`, if the present value of
taxes plus seignorage `T + Ṁ/P` converges to `X`, then the present value of taxes plus
`i m` (with `i = r + π`) converges to `X + m(0)`: `∫G = B^G − M/P + ∫(T + iM/P)`. -/
theorem government_18 {r X : ℝ} {m md infl tax : ℝ → ℝ} (hm : ∀ s, HasDerivAt m (md s) s)
    (hmd : Continuous md) (hπ : Continuous infl) (htax : Continuous tax)
    (hnhd : Tendsto (fun T => Real.exp (-r * T) * m T) atTop (𝓝 0))
    (hX : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (tax s + (md s + infl s * m s)))
      atTop (𝓝 X)) :
    Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (tax s + (r + infl s) * m s)) atTop
      (𝓝 (X + m 0)) := by
  have hmc : Continuous m := continuous_iff_continuousAt.2 fun t => (hm t).continuousAt
  have ct : Continuous fun s => Real.exp (-r * s) * tax s := by fun_prop
  have c1 : Continuous fun s => Real.exp (-r * s) * (md s + infl s * m s) := by fun_prop
  have c2 : Continuous fun s => Real.exp (-r * s) * ((r + infl s) * m s) := by fun_prop
  have key : ∀ T, ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (tax s + (r + infl s) * m s) =
      (∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (tax s + (md s + infl s * m s))) -
        Real.exp (-r * T) * m T + m 0 := by
    intro T
    have h1 : ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (tax s + (r + infl s) * m s) =
        (∫ s in (0 : ℝ)..T, Real.exp (-r * s) * tax s) +
          ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * ((r + infl s) * m s) := by
      rw [← intervalIntegral.integral_add (ct.intervalIntegrable (μ := volume) _ _)
        (c2.intervalIntegrable (μ := volume) _ _)]
      congr 1; funext s; ring
    have h2 : ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (tax s + (md s + infl s * m s)) =
        (∫ s in (0 : ℝ)..T, Real.exp (-r * s) * tax s) +
          ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (md s + infl s * m s) := by
      rw [← intervalIntegral.integral_add (ct.intervalIntegrable (μ := volume) _ _)
        (c1.intervalIntegrable (μ := volume) _ _)]
      congr 1; funext s; ring
    rw [h1, h2, seignorage_by_parts hm hmd hπ T]
    ring
  simp only [key]
  have := (hX.sub hnhd).add_const (m 0)
  rwa [sub_zero] at this

/-- **The economy's consolidated constraint (19)**, O&R p. 751: adding the private constraint
(17) (with private assets `B^p + M/P`) and the government's (18) (after integration by parts),
`∫₀^∞ (C + G)e^{−rs} = B + ∫₀^∞ Y e^{−rs}` with `B = B^p + B^G`: money services net out. -/
theorem consolidated_19 {Bp BG m0 Yinf Tinf Ginf Sinf Cinf : ℝ}
    (hpriv : Cinf + Sinf = Bp + m0 + (Yinf - Tinf)) (hgov : Ginf = BG - m0 + (Tinf + Sinf)) :
    Cinf + Ginf = (Bp + BG) + Yinf := by
  linarith

/-! ## A.3.2 Consumption as a function of nominal interest rates -/

/-- **Money demand (22)**, O&R p. 752: with CES-isoelastic preferences (20), condition (8)
`u_{M/P}/u_C = i` holds iff `M/P = ((1−γ)/γ) i^{−θ} C` (in continuous time the user cost of money
is the nominal rate itself). -/
theorem money_demand_22 {γ θ σ c k i : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ) (hc : 0 < c)
    (hk : 0 < k) (hi : 0 < i) :
    cesMargM γ θ σ c k = i * cesMargC γ θ σ c k ↔ k = (1 - γ) / γ * i ^ (-θ) * c :=
  ces_money_demand_iff hγ0 hγ1 hθ hc hk hi

/-- **Marginal utility along money demand**, O&R p. 752:
`u_C = γ^{1/σ} C^{−1/σ} (P^C)^{(θ−σ)/σ}` with `P^C = [γ + (1−γ)i^{1−θ}]^{1/(1−θ)}` (21). -/
theorem marginal_utility_on_demand {γ θ σ c i : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hσ : 0 < σ) (hc : 0 < c) (hi : 0 < i) :
    cesMargC γ θ σ c ((1 - γ) / γ * i ^ (-θ) * c) =
      γ ^ (1 / σ) * c ^ (-(1 / σ)) * cesPrice γ θ i ^ ((θ - σ) / σ) :=
  cesMargC_on_demand hγ0 hγ1 hθ hθ1 hσ hc hi rfl

/-- Solving `u_C = λ` for consumption: if `K C^{−1/σ} P^{a/σ} = L` then `C = K^σ P^a L^{−σ}`
(O&R p. 752). -/
theorem consumption_of_marginal {K σ a c P L : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hc : 0 < c)
    (hP : 0 < P) (h : K * c ^ (-(1 / σ)) * P ^ (a / σ) = L) :
    c = K ^ σ * P ^ a * L ^ (-σ) := by
  have h1 := congrArg (· ^ (-σ)) h
  rw [mul_rpow (by positivity) (by positivity), mul_rpow hK.le (by positivity),
    ← rpow_mul hc.le, ← rpow_mul hP.le, show -(1 / σ) * -σ = 1 by field_simp,
    show a / σ * -σ = -a by field_simp, rpow_one] at h1
  have e1 : K ^ (-σ) * K ^ σ = 1 := by rw [← rpow_add hK]; simp
  have e2 : P ^ (-a) * P ^ a = 1 := by rw [← rpow_add hP]; simp
  calc c = (K ^ (-σ) * c * P ^ (-a)) * (K ^ σ * P ^ a) := by
        linear_combination (-(c)) * (P ^ (-a) * P ^ a) * e1 - c * e2
    _ = _ := by rw [h1]; ring

/-- **The integrated Euler equation (23)**, O&R p. 752: if `u_C = λ(s) = λ_0 e^{(δ−r)s}` along
the money-demand curve, i.e. `γ^{1/σ}C^{−1/σ}(P^C)^{(θ−σ)/σ} = λ_0 e^{(δ−r)s}`, then
`C_s = C_t (P^C_s/P^C_t)^{θ−σ} e^{σ(r−δ)(s−t)}` — the book's
`C_s = C_t exp ∫_t^s [(θ − σ)Ṗ^C/P^C + σ(r − δ)]`. -/
theorem consumption_23 {γ θ σ lam0 δ r : ℝ} {C PC : ℝ → ℝ} (hγ0 : 0 < γ) (hσ : 0 < σ)
    (hC : ∀ s, 0 < C s) (hPC : ∀ s, 0 < PC s) (hlam0 : 0 < lam0)
    (hfoc : ∀ s, γ ^ (1 / σ) * C s ^ (-(1 / σ)) * PC s ^ ((θ - σ) / σ) =
      lam0 * Real.exp ((δ - r) * s)) (s t : ℝ) :
    C s = C t * (PC s / PC t) ^ (θ - σ) * Real.exp (σ * (r - δ) * (s - t)) := by
  have hK : (γ ^ (1 / σ)) ^ σ = γ := by rw [← rpow_mul hγ0.le, one_div_mul_cancel hσ.ne', rpow_one]
  have hform : ∀ u, C u = γ * PC u ^ (θ - σ) * Real.exp (-σ * ((δ - r) * u)) * lam0 ^ (-σ) := by
    intro u
    have := consumption_of_marginal (by positivity) hσ (hC u) (hPC u) (hfoc u)
    rw [this, hK, mul_rpow hlam0.le (Real.exp_pos _).le, ← Real.exp_mul]
    ring_nf
  rw [hform s, hform t, div_rpow (hPC s).le (hPC t).le]
  have h1 := rpow_pos_of_pos (hPC t) (θ - σ)
  have h2 : Real.exp (-σ * ((δ - r) * s)) = Real.exp (-σ * ((δ - r) * t)) *
      Real.exp (σ * (r - δ) * (s - t)) := by rw [← Real.exp_add]; ring_nf
  rw [h2]
  field_simp

/-- **The consumption Euler equation in differential form**, O&R p. 752:
`Ċ/C = (θ − σ)Ṗ^C/P^C + σ(r − δ)` for a differentiable consumption-price-index path. -/
theorem consumption_euler_ct {θ σ r δ A : ℝ} {PC PCd : ℝ → ℝ} (hPC : ∀ s, 0 < PC s)
    (hd : ∀ s, HasDerivAt PC (PCd s) s) (s : ℝ) :
    HasDerivAt (fun s => A * PC s ^ (θ - σ) * Real.exp (σ * (r - δ) * s))
      (A * PC s ^ (θ - σ) * Real.exp (σ * (r - δ) * s) *
        ((θ - σ) * (PCd s / PC s) + σ * (r - δ))) s := by
  have h1 := (hd s).rpow_const (p := θ - σ) (Or.inl (hPC s).ne')
  have h2 : HasDerivAt (fun s => Real.exp (σ * (r - δ) * s))
      (Real.exp (σ * (r - δ) * s) * (σ * (r - δ))) s := by
    have := ((hasDerivAt_id s).const_mul (σ * (r - δ))).exp
    simp only [id, mul_one] at this
    exact this
  have := (h1.const_mul A).mul h2
  refine this.congr_deriv ?_
  have hp := hPC s
  rw [rpow_sub_one hp.ne']
  field_simp

/-- **(24)–(25), consumption as a function of the price-index path**, O&R pp. 752–753: if
consumption follows (23) from `C_0 > 0` and the economy's constraint (19) gives
`∫₀^T e^{−rs}C_s ds → W`, then the denominator
`∫₀^T e^{[(σ−1)r − σδ]s} (P^C_0/P^C_s)^{σ−θ} ds` converges to `W/C_0`, i.e.
`C_0 = W / ∫₀^∞ e^{[(σ−1)r − σδ]s}(P^C_0/P^C_s)^{σ−θ} ds` (with `W > 0`). With a constant nominal
rate (constant `P^C`) or `θ = σ` the price-index factor is `1`: consumption is as in a model
without money. -/
theorem consumption_25 {θ σ r δ W : ℝ} {C PC : ℝ → ℝ} (hPC : ∀ s, 0 < PC s) (hC0 : 0 < C 0)
    (hpath : ∀ s, C s = C 0 * (PC s / PC 0) ^ (θ - σ) * Real.exp (σ * (r - δ) * s))
    (hW : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * C s) atTop (𝓝 W)) :
    Tendsto (fun T => ∫ s in (0 : ℝ)..T,
      Real.exp (((σ - 1) * r - σ * δ) * s) * (PC 0 / PC s) ^ (σ - θ)) atTop (𝓝 (W / C 0)) ∧
    (∀ T, (∀ s, PC s = PC 0) ∨ θ = σ → ∫ s in (0 : ℝ)..T,
      Real.exp (((σ - 1) * r - σ * δ) * s) * (PC 0 / PC s) ^ (σ - θ) =
        ∫ s in (0 : ℝ)..T, Real.exp (((σ - 1) * r - σ * δ) * s)) := by
  have hint : ∀ s, Real.exp (-r * s) * C s =
      C 0 * (Real.exp (((σ - 1) * r - σ * δ) * s) * (PC 0 / PC s) ^ (σ - θ)) := by
    intro s
    rw [hpath s]
    have h1 : (PC s / PC 0) ^ (θ - σ) = (PC 0 / PC s) ^ (σ - θ) := by
      rw [show θ - σ = -(σ - θ) by ring, rpow_neg (div_pos (hPC s) (hPC 0)).le,
        ← inv_rpow (div_pos (hPC s) (hPC 0)).le, inv_div]
    have h2 : Real.exp (-r * s) * Real.exp (σ * (r - δ) * s) =
        Real.exp (((σ - 1) * r - σ * δ) * s) := by rw [← Real.exp_add]; ring_nf
    rw [h1]
    linear_combination C 0 * (PC 0 / PC s) ^ (σ - θ) * h2
  refine ⟨?_, fun T h => ?_⟩
  · simp only [hint, intervalIntegral.integral_const_mul] at hW
    have := hW.const_mul (C 0)⁻¹
    refine (this.congr fun T => ?_).trans ?_
    · field_simp
    · rw [div_eq_inv_mul]
  · congr 1
    funext s
    rcases h with h | h
    · rw [h s, div_self (hPC 0).ne', one_rpow, mul_one]
    · rw [h, sub_self, rpow_zero, mul_one]

/-! ## A.3.3 A true reduced-form solution -/

/-- **Real balances as a power of the nominal rate** (O&R p. 753, `θ = 1`, `δ = r`): with
`u = [C^γ m^{1−γ}]^{1−1/σ}/(1−1/σ)` and a constant marginal utility of wealth `λ` (from (9) with
`δ = r`), `u_C = λ` along the money-demand curve `m = ((1−γ)/γ)C/i` gives
`C = K i^{(1−γ)(1−σ)}` and `m = K_m i^{−ζ}` with `ζ = γ + (1−γ)σ`. -/
theorem real_balances_power {γ σ lam c i : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hσ : 0 < σ)
    (hc : 0 < c) (hi : 0 < i)
    (hfoc : cdMargC γ σ c ((1 - γ) / γ * c / i) = lam) :
    c = (γ * ((1 - γ) / γ) ^ ((1 - γ) * (1 - 1 / σ))) ^ σ * lam ^ (-σ) *
        i ^ ((1 - γ) * (1 - σ)) ∧
      (1 - γ) / γ * c / i = (1 - γ) / γ * ((γ * ((1 - γ) / γ) ^ ((1 - γ) * (1 - 1 / σ))) ^ σ *
        lam ^ (-σ)) * i ^ (-(γ + (1 - γ) * σ)) := by
  have h1γ : 0 < 1 - γ := by linarith
  set K := γ * ((1 - γ) / γ) ^ ((1 - γ) * (1 - 1 / σ)) with hK
  have hK0 : 0 < K := by positivity
  rw [cdMargC_on_demand hγ0 hγ1 hσ hc hi, ← hK] at hfoc
  have hc' := consumption_of_marginal hK0 hσ hc (rpow_pos_of_pos hi (1 - γ))
    (a := 1 - σ) hfoc
  have hp : (i ^ (1 - γ)) ^ (1 - σ) = i ^ ((1 - γ) * (1 - σ)) := by rw [← rpow_mul hi.le]
  rw [hp] at hc'
  refine ⟨by rw [hc']; ring, ?_⟩
  rw [hc']
  have e : i ^ ((1 - γ) * (1 - σ)) / i = i ^ (-(γ + (1 - γ) * σ)) := by
    rw [← rpow_sub_one hi.ne']; congr 1; ring
  rw [← e]
  ring

/-- **The ODE for the inverse nominal rate** (O&R p. 753, made explicit): if real balances are
`M/P = K_m x^ζ` with `x = 1/i`, money grows at the instantaneous rate `g_M = Ṁ/M`, and Fisher
parity holds, `i = r + Ṗ/P`, then `ζ ẋ = (r + g_M) x − 1`. This equation is UNSTABLE forward
(its homogeneous solutions grow like `e^{rt/ζ}M^{1/ζ}`). -/
theorem inverse_rate_ode {r ζ Km : ℝ} {M x : ℝ → ℝ} {t Md xd Pd : ℝ} (hKm : 0 < Km)
    (hM : 0 < M t) (hx : 0 < x t) (hMd : HasDerivAt M Md t) (hxd : HasDerivAt x xd t)
    (hPd : HasDerivAt (fun t => M t / (Km * x t ^ ζ)) Pd t)
    (hfisher : 1 / x t = r + Pd / (M t / (Km * x t ^ ζ))) :
    ζ * xd = (r + Md / M t) * x t - 1 := by
  have hxz := rpow_pos_of_pos hx ζ
  have hq : HasDerivAt (fun t => M t / (Km * x t ^ ζ))
      ((Md * (Km * x t ^ ζ) - M t * (Km * (xd * ζ * x t ^ (ζ - 1)))) / (Km * x t ^ ζ) ^ 2) t :=
    hMd.div ((hxd.rpow_const (p := ζ) (Or.inl hx.ne')).const_mul Km) (by positivity)
  rw [hq.unique hPd |>.symm] at hfisher
  rw [rpow_sub_one hx.ne'] at hfisher
  field_simp at hfisher
  field_simp
  linarith [hfisher]

/-- The discounted money integrand `f(s) = e^{−rs/ζ} M(s)^{−1/ζ}` of A.3.3.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
noncomputable def rateKernel (r ζ : ℝ) (M : ℝ → ℝ) (s : ℝ) : ℝ :=
  Real.exp (-(r / ζ) * s) * M s ^ (-(1 / ζ))

/-- The no-bubble solution of the inverse-rate ODE, O&R p. 753:
`x^*(t) = (1/ζ) e^{rt/ζ} M(t)^{1/ζ} ∫_t^∞ e^{−rs/ζ} M(s)^{−1/ζ} ds`. -/
noncomputable def xStar (r ζ : ℝ) (M : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 / ζ * Real.exp ((r / ζ) * t) * M t ^ (1 / ζ) * ∫ s in Set.Ioi t, rateKernel r ζ M s

/-- **The book's formula** (O&R p. 753): `x^*(t) = (1/ζ)∫_t^∞ e^{−r(s−t)/ζ}[M(s)/M(t)]^{−1/ζ} ds`,
so `i_t = 1/x^*(t)` is exactly the displayed nominal-rate formula. -/
theorem xStar_eq_book {r ζ : ℝ} {M : ℝ → ℝ} (hM : ∀ s, 0 < M s) (t : ℝ) :
    xStar r ζ M t = 1 / ζ * ∫ s in Set.Ioi t,
      Real.exp (-(r * (s - t) / ζ)) * (M s / M t) ^ (-(1 / ζ)) := by
  unfold xStar
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1
  funext s
  unfold rateKernel
  rw [div_rpow (hM s).le (hM t).le, rpow_neg (hM t).le, div_inv_eq_mul]
  have e : Real.exp (r / ζ * t) * Real.exp (-(r / ζ) * s) = Real.exp (-(r * (s - t) / ζ)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← e]
  ring

/-- `∫_t^∞ f = ∫_0^∞ f − ∫_0^t f` for an integrable continuous kernel.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem tail_integral_eq {f : ℝ → ℝ} (hf : Continuous f) (hint : IntegrableOn f (Set.Ioi 0))
    (t : ℝ) : ∫ s in Set.Ioi t, f s = (∫ s in Set.Ioi 0, f s) - ∫ s in (0 : ℝ)..t, f s := by
  have := intervalIntegral.integral_interval_add_Ioi' (hf.intervalIntegrable (μ := volume) t 0)
    hint
  rw [intervalIntegral.integral_symm] at this
  linarith

/-- **The no-bubble solution solves the ODE** (O&R p. 753): for a positive, differentiable money
path with `Ṁ = g_M M` and an integrable kernel, `ζ ẋ^* = (r + g_M) x^* − 1` at every date. -/
theorem xStar_solves {r ζ : ℝ} {M gM : ℝ → ℝ} (hM : ∀ s, 0 < M s)
    (hMd : ∀ s, HasDerivAt M (gM s * M s) s) (hint : IntegrableOn (rateKernel r ζ M) (Set.Ioi 0))
    (t : ℝ) :
    HasDerivAt (xStar r ζ M) ((r + gM t) * xStar r ζ M t / ζ - 1 / ζ) t := by
  have hMc : Continuous M := continuous_iff_continuousAt.2 fun s => (hMd s).continuousAt
  have hf : Continuous (rateKernel r ζ M) := by
    unfold rateKernel
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (hMc.rpow_const fun s => Or.inl (hM s).ne')
  have hI : ∀ t, HasDerivAt (fun t => ∫ s in Set.Ioi t, rateKernel r ζ M s)
      (-rateKernel r ζ M t) t := by
    intro t
    have h1 := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable (μ := volume) 0 t)
      (hf.aestronglyMeasurable.stronglyMeasurableAtFilter) hf.continuousAt
    have h2 := h1.const_sub (∫ s in Set.Ioi 0, rateKernel r ζ M s)
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun u => tail_integral_eq hf hint u)
  have hE : HasDerivAt (fun t => Real.exp (r / ζ * t)) (Real.exp (r / ζ * t) * (r / ζ)) t := by
    have := ((hasDerivAt_id t).const_mul (r / ζ)).exp
    simp only [id, mul_one] at this
    exact this
  have hMp : HasDerivAt (fun t => M t ^ (1 / ζ)) (gM t * M t * (1 / ζ) * M t ^ (1 / ζ - 1)) t :=
    (hMd t).rpow_const (Or.inl (hM t).ne')
  have := (((hE.const_mul (1 / ζ)).mul hMp).mul (hI t))
  unfold xStar
  refine this.congr_deriv ?_
  have hk : rateKernel r ζ M t = Real.exp (-(r / ζ) * t) * M t ^ (-(1 / ζ)) := rfl
  rw [hk]
  have hMt := hM t
  have e1 : M t * M t ^ (1 / ζ - 1) = M t ^ (1 / ζ) := by
    rw [rpow_sub_one hMt.ne', mul_div_cancel₀ _ hMt.ne']
  have e2 : M t ^ (1 / ζ) * M t ^ (-(1 / ζ)) = 1 := by rw [← rpow_add hMt]; simp
  have e3 : Real.exp (r / ζ * t) * Real.exp (-(r / ζ) * t) = 1 := by
    rw [← Real.exp_add]; simp
  simp only [Pi.mul_apply]
  linear_combination (1 / ζ * (1 / ζ) * Real.exp (r / ζ * t) * gM t *
    ∫ s in Set.Ioi t, rateKernel r ζ M s) * e1 +
    (-(1 / ζ)) * (M t ^ (1 / ζ) * M t ^ (-(1 / ζ))) * e3 + (-(1 / ζ)) * e2

/-- **Every solution of the inverse-rate ODE is the no-bubble solution plus a bubble**, and the
no-bubble solution is the UNIQUE one along which `e^{−rt/ζ}M(t)^{−1/ζ}x(t) → 0` (O&R p. 753,
"one can then show", made precise; the analogue of the Cagan `b₀ = 0` selection):
`x(t) = x^*(t) + c e^{rt/ζ}M(t)^{1/ζ}`, with `c = 0` under the no-bubble condition. -/
theorem xStar_unique {r ζ : ℝ} {M gM x xd : ℝ → ℝ} (hζ : 0 < ζ) (hM : ∀ s, 0 < M s)
    (hMd : ∀ s, HasDerivAt M (gM s * M s) s) (hint : IntegrableOn (rateKernel r ζ M) (Set.Ioi 0))
    (hx : ∀ t, HasDerivAt x (xd t) t) (hode : ∀ t, ζ * xd t = (r + gM t) * x t - 1) :
    (∃ c, ∀ t, x t = xStar r ζ M t + c * (Real.exp ((r / ζ) * t) * M t ^ (1 / ζ))) ∧
    (Tendsto (fun t => Real.exp (-(r / ζ) * t) * M t ^ (-(1 / ζ)) * x t) atTop (𝓝 0) →
      ∀ t, x t = xStar r ζ M t) := by
  have hMc : Continuous M := continuous_iff_continuousAt.2 fun s => (hMd s).continuousAt
  have hf : Continuous (rateKernel r ζ M) := by
    unfold rateKernel
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (hMc.rpow_const fun s => Or.inl (hM s).ne')
  have hI : ∀ t, HasDerivAt (fun t => ∫ s in Set.Ioi t, rateKernel r ζ M s)
      (-rateKernel r ζ M t) t := by
    intro t
    have h1 := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable (μ := volume) 0 t)
      (hf.aestronglyMeasurable.stronglyMeasurableAtFilter) hf.continuousAt
    exact (h1.const_sub (∫ s in Set.Ioi 0, rateKernel r ζ M s)).congr_of_eventuallyEq
      (Eventually.of_forall fun u => tail_integral_eq hf hint u)
  set w : ℝ → ℝ := fun t => Real.exp (-(r / ζ) * t) * M t ^ (-(1 / ζ)) * x t -
    1 / ζ * ∫ s in Set.Ioi t, rateKernel r ζ M s with hw
  have hwd : ∀ t, HasDerivAt w 0 t := by
    intro t
    have hE : HasDerivAt (fun t => Real.exp (-(r / ζ) * t))
        (Real.exp (-(r / ζ) * t) * (-(r / ζ))) t := by
      have := ((hasDerivAt_id t).const_mul (-(r / ζ))).exp
      simp only [id, mul_one] at this
      exact this
    have hMp : HasDerivAt (fun t => M t ^ (-(1 / ζ)))
        (gM t * M t * (-(1 / ζ)) * M t ^ (-(1 / ζ) - 1)) t :=
      (hMd t).rpow_const (Or.inl (hM t).ne')
    have := ((hE.mul hMp).mul (hx t)).sub ((hI t).const_mul (1 / ζ))
    refine this.congr_deriv ?_
    have hk : rateKernel r ζ M t = Real.exp (-(r / ζ) * t) * M t ^ (-(1 / ζ)) := rfl
    rw [hk]
    have hMt := hM t
    have e1 : M t * M t ^ (-(1 / ζ) - 1) = M t ^ (-(1 / ζ)) := by
      rw [rpow_sub_one hMt.ne', mul_div_cancel₀ _ hMt.ne']
    have ho : xd t = ((r + gM t) * x t - 1) / ζ := by
      rw [eq_div_iff hζ.ne']; linarith [hode t]
    simp only [Pi.mul_apply]
    rw [ho]
    linear_combination (Real.exp (-(r / ζ) * t) * gM t * (-(1 / ζ)) * x t) * e1
  have hconst : ∀ t, w t = w 0 := fun t =>
    is_const_of_deriv_eq_zero (fun t => (hwd t).differentiableAt) (fun t => (hwd t).deriv) t 0
  have hsol : ∀ t, x t = xStar r ζ M t + ζ⁻¹ * ζ * w 0 * (Real.exp ((r / ζ) * t) *
      M t ^ (1 / ζ)) := by
    intro t
    have h : Real.exp (-(r / ζ) * t) * M t ^ (-(1 / ζ)) * x t -
        1 / ζ * ∫ s in Set.Ioi t, rateKernel r ζ M s = w 0 := hconst t
    have hMt := hM t
    have e2 : M t ^ (1 / ζ) * M t ^ (-(1 / ζ)) = 1 := by rw [← rpow_add hMt]; simp
    have e3 : Real.exp (r / ζ * t) * Real.exp (-(r / ζ) * t) = 1 := by
      rw [← Real.exp_add]; simp
    unfold xStar
    have hζ' := hζ.ne'
    calc x t = (Real.exp (r / ζ * t) * Real.exp (-(r / ζ) * t)) *
          (M t ^ (1 / ζ) * M t ^ (-(1 / ζ))) * x t := by rw [e2, e3]; ring
      _ = Real.exp (r / ζ * t) * M t ^ (1 / ζ) *
          (Real.exp (-(r / ζ) * t) * M t ^ (-(1 / ζ)) * x t) := by ring
      _ = Real.exp (r / ζ * t) * M t ^ (1 / ζ) *
          (w 0 + 1 / ζ * ∫ s in Set.Ioi t, rateKernel r ζ M s) := by
        rw [show Real.exp (-(r / ζ) * t) * M t ^ (-(1 / ζ)) * x t =
          w 0 + 1 / ζ * ∫ s in Set.Ioi t, rateKernel r ζ M s by linarith [h]]
      _ = _ := by field_simp; ring
  refine ⟨⟨ζ⁻¹ * ζ * w 0, hsol⟩, fun hbub t => ?_⟩
  have hItail : Tendsto (fun t => ∫ s in Set.Ioi t, rateKernel r ζ M s) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := ∫ s in Set.Ioi 0, rateKernel r ζ M s)).sub
      (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id)
    rw [sub_self] at this
    exact this.congr fun u => (tail_integral_eq hf hint u).symm
  have hw0 : w 0 = 0 := by
    have h1 : Tendsto w atTop (𝓝 (0 - 1 / ζ * 0)) := hbub.sub (hItail.const_mul (1 / ζ))
    rw [mul_zero, sub_zero] at h1
    have h2 : Tendsto w atTop (𝓝 (w 0)) :=
      tendsto_const_nhds.congr fun u => (hconst u).symm
    exact tendsto_nhds_unique h2 h1
  rw [hsol t, hw0]
  ring

/-- **Constant money growth**, O&R p. 753: with `M(s) = M_0 e^{μs}` and `r + μ > 0`, the
no-bubble nominal rate is `i = r + μ` at every date (`x^* ≡ 1/(r + μ)`), obtained by checking
that the constant satisfies the ODE and the no-bubble condition and invoking uniqueness. -/
theorem nominal_rate_constant_growth {r ζ μ M0 : ℝ} (hζ : 0 < ζ) (hM0 : 0 < M0)
    (hrμ : 0 < r + μ) (t : ℝ) :
    xStar r ζ (fun s => M0 * Real.exp (μ * s)) t = 1 / (r + μ) ∧
      1 / xStar r ζ (fun s => M0 * Real.exp (μ * s)) t = r + μ := by
  set M : ℝ → ℝ := fun s => M0 * Real.exp (μ * s) with hMdef
  have hM : ∀ s, 0 < M s := fun s => by simp only [hMdef]; positivity
  have hMd : ∀ s, HasDerivAt M (μ * M s) s := by
    intro s
    have := (((hasDerivAt_id s).const_mul μ).exp).const_mul M0
    simp only [id, mul_one] at this
    refine this.congr_deriv ?_
    simp only [hMdef]; ring
  have hker : ∀ s, rateKernel r ζ M s = M0 ^ (-(1 / ζ)) * Real.exp (-((r + μ) / ζ) * s) := by
    intro s
    unfold rateKernel
    simp only [hMdef]
    rw [mul_rpow hM0.le (Real.exp_pos _).le, ← Real.exp_mul]
    have : Real.exp (-(r / ζ) * s) * Real.exp (μ * s * -(1 / ζ)) =
        Real.exp (-((r + μ) / ζ) * s) := by rw [← Real.exp_add]; congr 1; ring
    rw [← this]; ring
  have hint : IntegrableOn (rateKernel r ζ M) (Set.Ioi 0) := by
    have h := (exp_neg_integrableOn_Ioi 0 (show 0 < (r + μ) / ζ by positivity)).const_mul
      (M0 ^ (-(1 / ζ)))
    exact IntegrableOn.congr_fun h (fun s _ => (hker s).symm) measurableSet_Ioi
  have hode : ∀ t : ℝ, ζ * (fun _ : ℝ => (0 : ℝ)) t =
      (r + μ) * (fun _ : ℝ => 1 / (r + μ)) t - 1 := by
    intro t; field_simp; ring
  have hbub : Tendsto (fun t => Real.exp (-(r / ζ) * t) * M t ^ (-(1 / ζ)) *
      (fun _ : ℝ => 1 / (r + μ)) t) atTop (𝓝 0) := by
    have hdec : Tendsto (fun t : ℝ => Real.exp (-((r + μ) / ζ) * t)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (show 0 < (r + μ) / ζ by positivity))
      exact this.congr fun u => by simp [neg_mul]
    have := (hdec.const_mul (M0 ^ (-(1 / ζ)))).mul_const (1 / (r + μ))
    rw [mul_zero, zero_mul] at this
    refine this.congr fun u => ?_
    have := hker u
    unfold rateKernel at this
    simp only
    rw [this]
  have h := (xStar_unique (x := fun _ => 1 / (r + μ)) (xd := fun _ => 0) hζ hM hMd hint
    (fun t => hasDerivAt_const t _) hode).2 hbub t
  refine ⟨h.symm, ?_⟩
  rw [← h]
  field_simp

/-- **The Cobb–Douglas price index** (O&R p. 753): as `θ → 1` the consumption-based price index
(21) `[γ + (1−γ)i^{1−θ}]^{1/(1−θ)}` converges to `i^{1−γ}`. -/
theorem priceIndex_cobbDouglas {γ i : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hi : 0 < i) :
    Tendsto (fun θ => cesPrice γ θ i) (𝓝[≠] 1) (𝓝 (i ^ (1 - γ))) :=
  cesPrice_tendsto_cobbDouglas hγ0 hγ1 hi

/-! ## Necessity of (3), (8), (9) and of the TVC in the monetary problem -/

/-- Financial wealth of a continuous-time plan `c = (C, M/P)` (O&R (11) solved by variation of
constants): `Q(T) = e^{rT}(Q_0 + ∫₀^T e^{−rs}(y_s − C_s − i_s m_s) ds)`. -/
noncomputable def ctWealth (r Q0 : ℝ) (y i : ℝ → ℝ) (c : ℝ → ℝ × ℝ) (T : ℝ) : ℝ :=
  Real.exp (r * T) * (Q0 + ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (y s - (c s).1 - i s * (c s).2))

/-- An admissible continuous-time plan with value `U` (O&R (6), (7), (10)–(11)): continuous,
with positive consumption and real balances (plans are defined on all of `ℝ`; dates before `0`
play no role), utility integral converging to `U`, and no Ponzi scheme
`liminf e^{−rT}Q(T) ≥ 0`. -/
def CTAdmissible (u : ℝ × ℝ → ℝ) (r δ Q0 : ℝ) (y i : ℝ → ℝ) (c : ℝ → ℝ × ℝ) (U : ℝ) : Prop :=
  Continuous c ∧ (∀ s, c s ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) ∧
    Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (c s)) atTop (𝓝 U) ∧
    ∀ ε > 0, ∀ᶠ T in atTop, -ε < Real.exp (-r * T) * ctWealth r Q0 y i c T

/-- An optimal continuous-time plan: admissible with value `U`, and every admissible plan has
value at most `U` (O&R p. 748). -/
def CTOptimal (u : ℝ × ℝ → ℝ) (r δ Q0 : ℝ) (y i : ℝ → ℝ) (c : ℝ → ℝ × ℝ) (U : ℝ) : Prop :=
  CTAdmissible u r δ Q0 y i c U ∧ ∀ c' U', CTAdmissible u r δ Q0 y i c' U' → U' ≤ U

/-- The wealth path of a plan solves (11): `Q̇ = rQ + y − C − i m`, with `Q(0) = Q_0`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem ctWealth_hasDerivAt {r Q0 : ℝ} {y i : ℝ → ℝ} {c : ℝ → ℝ × ℝ} (hy : Continuous y)
    (hi : Continuous i) (hc : Continuous c) (t : ℝ) :
    HasDerivAt (ctWealth r Q0 y i c)
      (r * ctWealth r Q0 y i c t + (y t - (c t).1 - i t * (c t).2)) t := by
  have hf : Continuous fun s => y s - (c s).1 - i s * (c s).2 := by
    have h1 : Continuous fun s => (c s).1 := continuous_fst.comp hc
    have h2 : Continuous fun s => (c s).2 := continuous_snd.comp hc
    fun_prop
  exact (variation_of_constants (r := r) (Q0 := Q0) hf).1 t

/-- **The first-order condition for a compactly supported perturbation** (the continuous-time
analogue of the one-period perturbations of §8.3.2): at an optimum, for every continuous
direction `Δ` vanishing outside `[a, b] ⊆ [0, ∞)` that leaves the wealth path unchanged from
some date on, `∫_a^b e^{−δs}(u_C Δ_C + u_{M/P} Δ_m) ds = 0`. Proof: optimality gives
`D(ε) := ∫_a^b e^{−δs}[u(c + εΔ) − u(c)] ≤ 0` for small `|ε|`; concavity gives
`D(ε) ≥ ε G(ε)`, `G(ε) = ∫_a^b e^{−δs}∇u(c + εΔ)·Δ`; and `G` is continuous.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem ct_foc_integral {u uC um : ℝ × ℝ → ℝ} {r δ Q0 U a b : ℝ} {y i : ℝ → ℝ}
    {c Δ : ℝ → ℝ × ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) u)
    (hdiff : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), HasFDerivAt u (grad (uC p) (um p)) p)
    (hcC : ContinuousOn uC (Set.Ioi 0 ×ˢ Set.Ioi 0))
    (hcM : ContinuousOn um (Set.Ioi 0 ×ˢ Set.Ioi 0))
    (hopt : CTOptimal u r δ Q0 y i c U) (hΔ : Continuous Δ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hsupp : ∀ s, s ∉ Set.Ioo a b → Δ s = 0)
    (hw : ∀ ε : ℝ, ∀ᶠ T in atTop,
      ctWealth r Q0 y i (fun s => c s + ε • Δ s) T = ctWealth r Q0 y i c T) :
    ∫ s in a..b, Real.exp (-δ * s) * (uC (c s) * (Δ s).1 + um (c s) * (Δ s).2) = 0 := by
  obtain ⟨⟨hc, hcpos, hU, hnp⟩, hmax⟩ := hopt
  set K := Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) with hK
  have hucont : ContinuousOn u K := fun p hp => (hdiff p hp).continuousAt.continuousWithinAt
  -- a uniform lower bound for the plan on `[a, b]` and a bound for `Δ`
  have hmin : Continuous fun s => min (c s).1 (c s).2 :=
    (continuous_fst.comp hc).min (continuous_snd.comp hc)
  obtain ⟨s1, -, hs1⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hab)
    hmin.continuousOn
  set κ := min (c s1).1 (c s1).2 with hκ
  have hκ0 : 0 < κ := lt_min (hcpos s1).1 (hcpos s1).2
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hΔ.continuousOn (s := Set.Icc a b))
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB a ⟨le_rfl, hab⟩)
  set ε0 := κ / (2 * (B + 1)) with hε0
  have hε00 : 0 < ε0 := by positivity
  have hε0B : ε0 * B < κ := by
    rw [hε0]
    have : κ / (2 * (B + 1)) * B ≤ κ / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hmem : ∀ e : ℝ, |e| ≤ ε0 → ∀ s, c s + e • Δ s ∈ K := by
    intro e he s
    by_cases hs : s ∈ Set.Icc a b
    · have h1 : |(Δ s).1| ≤ B := (norm_fst_le (Δ s)).trans (hB s hs)
      have h2 : |(Δ s).2| ≤ B := (norm_snd_le (Δ s)).trans (hB s hs)
      have hk1 : κ ≤ (c s).1 := (hs1 hs).trans (min_le_left _ _)
      have hk2 : κ ≤ (c s).2 := (hs1 hs).trans (min_le_right _ _)
      have e1 : |e * (Δ s).1| ≤ ε0 * B := by
        rw [abs_mul]; exact mul_le_mul he h1 (abs_nonneg _) hε00.le
      have e2 : |e * (Δ s).2| ≤ ε0 * B := by
        rw [abs_mul]; exact mul_le_mul he h2 (abs_nonneg _) hε00.le
      refine ⟨?_, ?_⟩ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, Set.mem_Ioi]
      · linarith [neg_abs_le (e * (Δ s).1)]
      · linarith [neg_abs_le (e * (Δ s).2)]
    · rw [hsupp s (fun h => hs (Set.Ioo_subset_Icc_self h)), smul_zero, add_zero]
      exact hcpos s
  -- the utility gain of a perturbation
  set D : ℝ → ℝ := fun e => ∫ s in a..b, Real.exp (-δ * s) * (u (c s + e • Δ s) - u (c s))
    with hD
  have hcontU : ∀ e : ℝ, |e| ≤ ε0 → Continuous fun s => u (c s + e • Δ s) := fun e he =>
    hucont.comp_continuous (hc.add (hΔ.const_smul e)) (hmem e he)
  have hcontU0 : Continuous fun s => u (c s) :=
    hucont.comp_continuous hc hcpos
  have hDle : ∀ e : ℝ, |e| ≤ ε0 → D e ≤ 0 := by
    intro e he
    have hge : ∀ T, b ≤ T → ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (c s + e • Δ s) =
        (∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (c s)) + D e := by
      intro T hT
      have i1 : ∀ x y, IntervalIntegrable (fun s => Real.exp (-δ * s) * u (c s + e • Δ s))
          volume x y := fun x y =>
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
          (hcontU e he)).intervalIntegrable x y
      have i2 : ∀ x y, IntervalIntegrable (fun s => Real.exp (-δ * s) * u (c s)) volume x y :=
        fun x y => ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
          hcontU0).intervalIntegrable x y
      have ig : ∀ x y, IntervalIntegrable (fun s => Real.exp (-δ * s) *
          (u (c s + e • Δ s) - u (c s))) volume x y := fun x y =>
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
          ((hcontU e he).sub hcontU0)).intervalIntegrable x y
      have hdiffint : ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * (u (c s + e • Δ s) - u (c s)) =
          D e := by
        have hz : ∀ x y, (∀ s ∈ Set.uIcc x y, s ∉ Set.Ioo a b) →
            ∫ s in x..y, Real.exp (-δ * s) * (u (c s + e • Δ s) - u (c s)) = 0 := by
          intro x y hxy
          rw [← intervalIntegral.integral_zero (a := x) (b := y) (μ := volume) (E := ℝ)]
          refine intervalIntegral.integral_congr fun s hs => ?_
          simp only [hsupp s (hxy s hs), smul_zero, add_zero, sub_self, mul_zero]
        rw [← intervalIntegral.integral_add_adjacent_intervals (ig 0 a) (ig a T),
          ← intervalIntegral.integral_add_adjacent_intervals (ig a b) (ig b T),
          hz 0 a (fun s hs h => by rw [Set.uIcc_of_le ha] at hs; linarith [hs.2, h.1]),
          hz b T (fun s hs h => by
            rw [Set.uIcc_of_le hT] at hs; linarith [hs.1, h.2])]
        simp [hD]
      rw [← hdiffint, ← intervalIntegral.integral_add (i2 0 T) (ig 0 T)]
      congr 1; funext s; ring
    have hlim : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (c s + e • Δ s))
        atTop (𝓝 (U + D e)) :=
      (hU.add_const (D e)).congr' (by
        filter_upwards [eventually_ge_atTop b] with T hT using (hge T hT).symm)
    have hadm : CTAdmissible u r δ Q0 y i (fun s => c s + e • Δ s) (U + D e) := by
      refine ⟨hc.add (hΔ.const_smul e), hmem e he, hlim, fun η hη => ?_⟩
      filter_upwards [hnp η hη, hw e] with T h1 h2
      rw [h2]; exact h1
    have := hmax _ _ hadm
    linarith
  -- the directional derivative of utility, `G`
  set F : ℝ → ℝ → ℝ := fun e s => Real.exp (-δ * s) *
    (uC (c s + e • Δ s) * (Δ s).1 + um (c s + e • Δ s) * (Δ s).2) with hF
  have hexpc : Continuous fun s : ℝ => Real.exp (-δ * s) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hFcont : ∀ e : ℝ, |e| ≤ ε0 → Continuous (F e) := by
    intro e he
    have h1 : Continuous fun s => uC (c s + e • Δ s) :=
      hcC.comp_continuous (hc.add (hΔ.const_smul e)) (hmem e he)
    have h2 : Continuous fun s => um (c s + e • Δ s) :=
      hcM.comp_continuous (hc.add (hΔ.const_smul e)) (hmem e he)
    exact hexpc.mul ((h1.mul (continuous_fst.comp hΔ)).add (h2.mul (continuous_snd.comp hΔ)))
  have hDG : ∀ e : ℝ, |e| ≤ ε0 → e * ∫ s in a..b, F e s ≤ D e := by
    intro e he
    have hpt : ∀ s, e * F e s ≤ Real.exp (-δ * s) * (u (c s + e • Δ s) - u (c s)) := by
      intro s
      have t := concave_le_tangent_gen hconc (hmem e he s) (hcpos s) (hdiff _ (hmem e he s))
      rw [grad_apply] at t
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul] at t
      have hep := Real.exp_pos (-δ * s)
      have : e * (uC (c s + e • Δ s) * (Δ s).1 + um (c s + e • Δ s) * (Δ s).2) ≤
          u (c s + e • Δ s) - u (c s) := by linarith
      calc e * F e s = Real.exp (-δ * s) *
            (e * (uC (c s + e • Δ s) * (Δ s).1 + um (c s + e • Δ s) * (Δ s).2)) := by
            simp only [hF]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this hep.le
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hab
      (((hFcont e he).const_smul e).intervalIntegrable a b)
      ((hexpc.mul ((hcontU e he).sub hcontU0)).intervalIntegrable a b) (fun s _ => hpt s)
  -- continuity of `G` at `0`, through a clamped parameter
  set cl : ℝ → ℝ := fun e => max (-ε0) (min ε0 e) with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_const.min continuous_id)
  have hclb : ∀ e, |cl e| ≤ ε0 := fun e => by
    rw [abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hFc : Continuous (Function.uncurry fun e s => F (cl e) s) := by
    have hpath : Continuous fun p : ℝ × ℝ => c p.2 + cl p.1 • Δ p.2 :=
      (hc.comp continuous_snd).add ((hclc.comp continuous_fst).smul (hΔ.comp continuous_snd))
    have hin : ∀ p : ℝ × ℝ, c p.2 + cl p.1 • Δ p.2 ∈ K := fun p => hmem _ (hclb p.1) p.2
    have h1 := hcC.comp_continuous hpath hin
    have h2 := hcM.comp_continuous hpath hin
    exact (hexpc.comp continuous_snd).mul ((h1.mul (continuous_fst.comp (hΔ.comp
      continuous_snd))).add (h2.mul (continuous_snd.comp (hΔ.comp continuous_snd))))
  have hGt := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hFc a b
  have hcl0 : ∀ᶠ e in 𝓝 (0 : ℝ), cl e = e := by
    filter_upwards [Ioo_mem_nhds (show -ε0 < 0 by linarith) hε00] with e he
    simp only [hcl]
    rw [min_eq_right he.2.le, max_eq_right he.1.le]
  have hGcont : ContinuousAt (fun e => ∫ s in a..b, F e s) 0 := by
    have h := hGt.continuousAt (x := 0)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hcl0] with e he
    simp only [he]
  have hG0 : (fun e => ∫ s in a..b, F e s) 0 =
      ∫ s in a..b, Real.exp (-δ * s) * (uC (c s) * (Δ s).1 + um (c s) * (Δ s).2) := by
    simp [hF]
  have hsmall : ∀ᶠ e in 𝓝 (0 : ℝ), |e| ≤ ε0 := by
    filter_upwards [Ioo_mem_nhds (show -ε0 < 0 by linarith) hε00] with e he
    rw [abs_le]; exact ⟨he.1.le, he.2.le⟩
  have hright : ∀ᶠ e in 𝓝[>] (0 : ℝ), (fun e => ∫ s in a..b, F e s) e ≤ 0 := by
    filter_upwards [nhdsWithin_le_nhds hsmall, self_mem_nhdsWithin] with e he hpos
    have h1 := (hDG e he).trans (hDle e he)
    simp only [Set.mem_Ioi] at hpos
    by_contra hc'
    push Not at hc'
    nlinarith
  have hleft : ∀ᶠ e in 𝓝[<] (0 : ℝ), 0 ≤ (fun e => ∫ s in a..b, F e s) e := by
    filter_upwards [nhdsWithin_le_nhds hsmall, self_mem_nhdsWithin] with e he hneg
    have h1 := (hDG e he).trans (hDle e he)
    simp only [Set.mem_Iio] at hneg
    by_contra hc'
    push Not at hc'
    nlinarith
  have h1 := le_of_tendsto (hGcont.tendsto.mono_left nhdsWithin_le_nhds) hright
  have h2 := ge_of_tendsto (hGcont.tendsto.mono_left nhdsWithin_le_nhds) hleft
  rw [← hG0]
  exact le_antisymm h1 h2


/-- A tent function, positive exactly on `(a, b)`: the bump used for the perturbations.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
noncomputable def tent (a b s : ℝ) : ℝ := max 0 (min (s - a) (b - s))

/-- The tent is continuous.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem tent_continuous (a b : ℝ) : Continuous (tent a b) :=
  continuous_const.max ((continuous_id.sub continuous_const).min
    (continuous_const.sub continuous_id))

/-- The tent is nonnegative.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem tent_nonneg (a b s : ℝ) : 0 ≤ tent a b s := le_max_left _ _

/-- The tent vanishes outside `(a, b)`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem tent_eq_zero {a b s : ℝ} (hs : s ∉ Set.Ioo a b) : tent a b s = 0 := by
  unfold tent
  apply max_eq_left
  simp only [Set.mem_Ioo, not_and_or, not_lt] at hs
  rcases hs with h | h
  · exact (min_le_left _ _).trans (by linarith)
  · exact (min_le_right _ _).trans (by linarith)

/-- The tent is positive on `(a, b)`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem tent_pos {a b s : ℝ} (hs : s ∈ Set.Ioo a b) : 0 < tent a b s :=
  lt_of_lt_of_le (lt_min (by linarith [hs.1]) (by linarith [hs.2])) (le_max_right _ _)

/-- A continuous function that is nonnegative on `[a, b]` and positive at an interior point has
positive integral over `[a, b]`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem integral_pos_of_pos_at {f : ℝ → ℝ} {a b s0 : ℝ} (hf : Continuous f)
    (hnn : ∀ s ∈ Set.Icc a b, 0 ≤ f s) (hs0 : s0 ∈ Set.Ioo a b) (hpos : 0 < f s0) :
    0 < ∫ s in a..b, f s := by
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1
    (hf.continuousAt.eventually (lt_mem_nhds hpos))
  set η' := min (η / 2) (min ((s0 - a) / 2) ((b - s0) / 2)) with hη'
  have hη'0 : 0 < η' := lt_min (by linarith) (lt_min (by linarith [hs0.1]) (by linarith [hs0.2]))
  have h1 : η' ≤ (s0 - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have h2 : η' ≤ (b - s0) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have h3 : η' ≤ η / 2 := min_le_left _ _
  have hsub : 0 < ∫ s in (s0 - η')..(s0 + η'), f s := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hf.intervalIntegrable _ _)
      (fun s hs => hball ?_) (by linarith)
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2]
  have hmono := intervalIntegral.integral_mono_interval (f := f) (μ := volume)
    (show a ≤ s0 - η' by linarith) (show s0 - η' ≤ s0 + η' by linarith)
    (show s0 + η' ≤ b by linarith)
    (by
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall fun s hs => hnn s ⟨hs.1.le, hs.2⟩)
    (hf.intervalIntegrable _ _)
  linarith

/-- **Necessity of (8), the money-demand condition** (O&R Supplement (8), p. 746, derived from
optimality rather than as the `h → 0` limit): at a continuous-time optimum,
`u_{M/P}(c_s) = i_s u_C(c_s)` at every date `s ≥ 0`. Proof: perturb along `(−i, 1)` with weight
`φ(s)(u_{M/P} − i u_C)(c_s)` (φ a tent); wealth is unchanged and `ct_foc_integral` gives
`∫ e^{−δs} φ (u_{M/P} − i u_C)² = 0`. -/
theorem ct_money_foc {u uC um : ℝ × ℝ → ℝ} {r δ Q0 U : ℝ} {y i : ℝ → ℝ} {c : ℝ → ℝ × ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) u)
    (hdiff : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), HasFDerivAt u (grad (uC p) (um p)) p)
    (hcC : ContinuousOn uC (Set.Ioi 0 ×ˢ Set.Ioi 0))
    (hcM : ContinuousOn um (Set.Ioi 0 ×ˢ Set.Ioi 0)) (hi : Continuous i)
    (hopt : CTOptimal u r δ Q0 y i c U) {s0 : ℝ} (hs0 : 0 ≤ s0) :
    um (c s0) = i s0 * uC (c s0) := by
  have hc := hopt.1.1
  have hcpos := hopt.1.2.1
  set g : ℝ → ℝ := fun s => um (c s) - i s * uC (c s) with hg
  have hgc : Continuous g :=
    (hcM.comp_continuous hc hcpos).sub (hi.mul (hcC.comp_continuous hc hcpos))
  have key : ∀ s0, 0 < s0 → g s0 = 0 := by
    intro s0 hs0
    have ha0 : 0 < s0 / 2 := by positivity
    set Δ : ℝ → ℝ × ℝ := fun s =>
      (tent (s0 / 2) (3 * s0 / 2) s * g s) • ((-i s, 1) : ℝ × ℝ) with hΔ
    have hΔc : Continuous Δ :=
      ((tent_continuous (s0 / 2) (3 * s0 / 2)).mul hgc).smul ((hi.neg).prodMk continuous_const)
    have hsupp : ∀ s, s ∉ Set.Ioo (s0 / 2) (3 * s0 / 2) → Δ s = 0 := fun s hs => by
      simp [hΔ, tent_eq_zero hs]
    have hw : ∀ ε : ℝ, ∀ᶠ T in atTop,
        ctWealth r Q0 y i (fun s => c s + ε • Δ s) T = ctWealth r Q0 y i c T := by
      intro ε
      refine Eventually.of_forall fun T => ?_
      unfold ctWealth
      congr 2
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [hΔ, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    have hfoc := ct_foc_integral hconc hdiff hcC hcM hopt hΔc ha0.le
      (by linarith) hsupp hw
    have heq : ∀ s, Real.exp (-δ * s) * (uC (c s) * (Δ s).1 + um (c s) * (Δ s).2) =
        Real.exp (-δ * s) * tent (s0 / 2) (3 * s0 / 2) s * g s ^ 2 := fun s => by
      simp only [hΔ, hg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    simp only [heq] at hfoc
    by_contra hne
    have hpos : 0 < Real.exp (-δ * s0) * tent (s0 / 2) (3 * s0 / 2) s0 * g s0 ^ 2 := by
      have := tent_pos (a := s0 / 2) (b := 3 * s0 / 2) (s := s0) ⟨by linarith, by linarith⟩
      have := pow_pos (abs_pos.2 hne) 2
      rw [sq_abs] at this
      positivity
    have hcont : Continuous fun s => Real.exp (-δ * s) * tent (s0 / 2) (3 * s0 / 2) s *
        g s ^ 2 :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (tent_continuous (s0 / 2) (3 * s0 / 2))).mul (hgc.pow 2)
    have := integral_pos_of_pos_at (a := s0 / 2) (b := 3 * s0 / 2) hcont
      (fun s _ => mul_nonneg (mul_nonneg (Real.exp_pos _).le (tent_nonneg _ _ s)) (sq_nonneg _))
      ⟨by linarith, by linarith⟩ hpos
    linarith
  rcases hs0.lt_or_eq with hlt | heq
  · have := key s0 hlt; simp only [hg] at this; linarith
  · subst heq
    have h1 : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := hgc.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
    have h2 : Tendsto g (𝓝[>] 0) (𝓝 0) := tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with s hs using (key s hs).symm)
    have := tendsto_nhds_unique h1 h2
    simp only [hg] at this
    linarith

/-- A continuous function vanishing outside `(a, b) ⊆ [0, T]` has the same integral over `[0, T]`
as over `[a, b]`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem integral_eq_of_vanish {g : ℝ → ℝ} {a b T : ℝ} (hg : Continuous g) (ha : 0 ≤ a)
    (hbT : b ≤ T) (hz : ∀ s, s ∉ Set.Ioo a b → g s = 0) :
    ∫ s in (0 : ℝ)..T, g s = ∫ s in a..b, g s := by
  have hz' : ∀ x y, (∀ s ∈ Set.uIcc x y, s ∉ Set.Ioo a b) → ∫ s in x..y, g s = 0 := by
    intro x y hxy
    rw [← intervalIntegral.integral_zero (a := x) (b := y) (μ := volume) (E := ℝ)]
    exact intervalIntegral.integral_congr fun s hs => hz s (hxy s hs)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable 0 a)
      (hg.intervalIntegrable a T),
    ← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable a b)
      (hg.intervalIntegrable b T),
    hz' 0 a (fun s hs h => by rw [Set.uIcc_of_le ha] at hs; linarith [hs.2, h.1]),
    hz' b T (fun s hs h => by rw [Set.uIcc_of_le hbT] at hs; linarith [hs.1, h.2])]
  ring

/-- **Necessity of (3)–(9), the costate equation** (O&R Supplement (9), p. 747, derived from
optimality): at a continuous-time optimum, `e^{(r−δ)s}u_C(c_s)` is constant on `[0, ∞)`, i.e.
the marginal utility of consumption `λ(s) = u_C(c_s)` equals `λ(0)e^{(δ−r)s}`, so
`λ̇ = λ(δ − r)`. Proof: perturb consumption by `e^{rs}φ(s)(h(s) − A)` with `∫φ(h − A) = 0`
(wealth unchanged after the perturbation), which by `ct_foc_integral` forces
`∫φ(h − A)² = 0`. -/
theorem ct_costate_of_optimal {u uC um : ℝ × ℝ → ℝ} {r δ Q0 U : ℝ} {y i : ℝ → ℝ}
    {c : ℝ → ℝ × ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) u)
    (hdiff : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), HasFDerivAt u (grad (uC p) (um p)) p)
    (hcC : ContinuousOn uC (Set.Ioi 0 ×ˢ Set.Ioi 0))
    (hcM : ContinuousOn um (Set.Ioi 0 ×ˢ Set.Ioi 0)) (hy : Continuous y) (hi : Continuous i)
    (hopt : CTOptimal u r δ Q0 y i c U) {s : ℝ} (hs : 0 ≤ s) :
    uC (c s) = uC (c 0) * Real.exp ((δ - r) * s) := by
  have hc := hopt.1.1
  have hcpos := hopt.1.2.1
  set h : ℝ → ℝ := fun s => Real.exp ((r - δ) * s) * uC (c s) with hh
  have hhc : Continuous h :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (hcC.comp_continuous hc hcpos)
  have hexpc : ∀ k : ℝ, Continuous fun s : ℝ => Real.exp (k * s) := fun k =>
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have claim : ∀ a b, 0 < a → a < b → ∀ s ∈ Set.Ioo a b,
      h s = (∫ t in a..b, tent a b t * h t) / ∫ t in a..b, tent a b t := by
    intro a b ha hab s hsab
    have hφc := tent_continuous a b
    have hΦ : 0 < ∫ t in a..b, tent a b t :=
      integral_pos_of_pos_at hφc (fun t _ => tent_nonneg a b t)
        ⟨show a < (a + b) / 2 by linarith, show (a + b) / 2 < b by linarith⟩
        (tent_pos ⟨by linarith, by linarith⟩)
    set A := (∫ t in a..b, tent a b t * h t) / ∫ t in a..b, tent a b t with hA
    set ψ : ℝ → ℝ := fun t => tent a b t * (h t - A) with hψ
    have hψc : Continuous ψ := hφc.mul (hhc.sub continuous_const)
    have hψz : ∀ t, t ∉ Set.Ioo a b → ψ t = 0 := fun t ht => by simp [hψ, tent_eq_zero ht]
    have hψint : ∫ t in a..b, ψ t = 0 := by
      have e : ∀ t, ψ t = tent a b t * h t - A * tent a b t := fun t => by simp only [hψ]; ring
      simp only [e]
      rw [show (∫ t in a..b, tent a b t * h t - A * tent a b t) =
          (∫ t in a..b, tent a b t * h t) - ∫ t in a..b, A * tent a b t from
        intervalIntegral.integral_sub ((hφc.mul hhc).intervalIntegrable a b)
          ((hφc.intervalIntegrable a b).const_mul A), intervalIntegral.integral_const_mul, hA]
      field_simp
      ring
    set Δ : ℝ → ℝ × ℝ := fun t => (Real.exp (r * t) * ψ t, 0) with hΔ
    have hΔc : Continuous Δ := ((hexpc r).mul hψc).prodMk continuous_const
    have hsupp : ∀ t, t ∉ Set.Ioo a b → Δ t = 0 := fun t ht => by
      simp [hΔ, hψz t ht]
    have hw : ∀ ε : ℝ, ∀ᶠ T in atTop,
        ctWealth r Q0 y i (fun t => c t + ε • Δ t) T = ctWealth r Q0 y i c T := by
      intro ε
      filter_upwards [eventually_ge_atTop b] with T hT
      unfold ctWealth
      have hcf : Continuous fun t => Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2) := by
        have h1 := continuous_fst.comp hc
        have h2 := continuous_snd.comp hc
        exact (hexpc (-r)).mul ((hy.sub h1).sub (hi.mul h2))
      have hpt : ∀ t, Real.exp (-r * t) * (y t - (c t + ε • Δ t).1 - i t * (c t + ε • Δ t).2) =
          Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2) - ε * ψ t := by
        intro t
        simp only [hΔ, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          mul_zero, add_zero]
        have : Real.exp (-r * t) * Real.exp (r * t) = 1 := by rw [← Real.exp_add]; simp
        linear_combination (-(ε * ψ t)) * this
      congr 2
      simp only [hpt]
      rw [show (∫ t in (0 : ℝ)..T, Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2) -
          ε * ψ t) = (∫ t in (0 : ℝ)..T, Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2)) -
          ∫ t in (0 : ℝ)..T, ε * ψ t from
        intervalIntegral.integral_sub (hcf.intervalIntegrable 0 T)
          ((hψc.intervalIntegrable 0 T).const_mul ε),
        intervalIntegral.integral_const_mul, integral_eq_of_vanish hψc ha.le hT hψz, hψint]
      ring
    have hfoc := ct_foc_integral hconc hdiff hcC hcM hopt hΔc ha.le hab.le hsupp hw
    have e1 : ∀ t, Real.exp (-δ * t) * (uC (c t) * (Δ t).1 + um (c t) * (Δ t).2) =
        h t * ψ t := fun t => by
      simp only [hΔ, hh, mul_zero, add_zero]
      have : Real.exp (-δ * t) * Real.exp (r * t) = Real.exp ((r - δ) * t) := by
        rw [← Real.exp_add]; ring_nf
      linear_combination uC (c t) * ψ t * this
    simp only [e1] at hfoc
    have hsq : ∫ t in a..b, tent a b t * (h t - A) ^ 2 = 0 := by
      have e2 : ∀ t, tent a b t * (h t - A) ^ 2 = h t * ψ t - A * ψ t := fun t => by
        simp only [hψ]; ring
      simp only [e2]
      rw [show (∫ t in a..b, h t * ψ t - A * ψ t) =
          (∫ t in a..b, h t * ψ t) - ∫ t in a..b, A * ψ t from
        intervalIntegral.integral_sub ((hhc.mul hψc).intervalIntegrable a b)
          ((hψc.intervalIntegrable a b).const_mul A), intervalIntegral.integral_const_mul, hfoc,
        hψint]
      ring
    by_contra hne
    have hpos : 0 < tent a b s * (h s - A) ^ 2 := by
      have := tent_pos hsab
      have := pow_pos (abs_pos.2 (sub_ne_zero.2 hne)) 2
      rw [sq_abs] at this
      positivity
    have hcont : Continuous fun t => tent a b t * (h t - A) ^ 2 :=
      hφc.mul ((hhc.sub continuous_const).pow 2)
    have := integral_pos_of_pos_at hcont
      (fun t _ => mul_nonneg (tent_nonneg a b t) (sq_nonneg _)) hsab hpos
    linarith
  -- `h` is constant on `(0, ∞)`
  have hconst : ∀ s1 s2, 0 < s1 → 0 < s2 → h s1 = h s2 := by
    intro s1 s2 h1 h2
    set a := min s1 s2 / 2
    set b := max s1 s2 + 1
    have ha : 0 < a := by positivity
    have hab : a < b := by
      have := min_le_max (a := s1) (b := s2)
      have := lt_min h1 h2
      simp only [a, b]; linarith
    have m1 : s1 ∈ Set.Ioo a b := ⟨by
      have := min_le_left s1 s2; have := lt_min h1 h2; simp only [a]; linarith, by
      have := le_max_left s1 s2; simp only [b]; linarith⟩
    have m2 : s2 ∈ Set.Ioo a b := ⟨by
      have := min_le_right s1 s2; have := lt_min h1 h2; simp only [a]; linarith, by
      have := le_max_right s1 s2; simp only [b]; linarith⟩
    rw [claim a b ha hab s1 m1, claim a b ha hab s2 m2]
  have h0 : h 0 = h 1 := by
    have t1 : Tendsto h (𝓝[>] 0) (𝓝 (h 0)) :=
      hhc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have t2 : Tendsto h (𝓝[>] 0) (𝓝 (h 1)) := tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with t ht using hconst 1 t one_pos ht)
    exact tendsto_nhds_unique t1 t2
  have hs' : h s = h 0 := by
    rcases hs.lt_or_eq with hlt | heq
    · rw [h0]; exact hconst s 1 hlt one_pos
    · rw [← heq]
  simp only [hh, mul_zero, Real.exp_zero, one_mul] at hs'
  have e : Real.exp ((r - δ) * s) * Real.exp ((δ - r) * s) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  calc uC (c s) = (Real.exp ((r - δ) * s) * uC (c s)) * Real.exp ((δ - r) * s) := by
        linear_combination (-(uC (c s))) * e
    _ = _ := by rw [hs']

/-- **Necessity of the transversality condition in the monetary problem** (O&R Supplement (15)–(16),
p. 750, derived from optimality): with `u_C > 0`, an optimal plan has
`liminf e^{−rT}Q(T) ≤ 0` (so, with the no-Ponzi condition, `liminf = 0`). Otherwise wealth would
eventually exceed `η > 0` in present value, and consuming `κφ(s)` more on `(0, 1)`
(`φ` a tent, `κ ∫₀¹e^{−rs}φ = η`) would keep the no-Ponzi condition and raise utility. -/
theorem ct_tvc_of_optimal {u uC um : ℝ × ℝ → ℝ} {r δ Q0 U : ℝ} {y i : ℝ → ℝ}
    {c : ℝ → ℝ × ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) u)
    (hdiff : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), HasFDerivAt u (grad (uC p) (um p)) p)
    (huC : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), 0 < uC p) (hy : Continuous y)
    (hi : Continuous i) (hopt : CTOptimal u r δ Q0 y i c U) :
    ∀ ε > 0, ∃ᶠ T in atTop, Real.exp (-r * T) * ctWealth r Q0 y i c T < ε := by
  obtain ⟨⟨hc, hcpos, hU, _⟩, hmax⟩ := hopt
  intro η hη
  by_contra hcon
  rw [not_frequently] at hcon
  set K := Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) with hK
  have hucont : ContinuousOn u K := fun p hp => (hdiff p hp).continuousAt.continuousWithinAt
  have hexpc : ∀ k : ℝ, Continuous fun s : ℝ => Real.exp (k * s) := fun k =>
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hφc := tent_continuous 0 1
  set Φ := ∫ s in (0 : ℝ)..1, Real.exp (-r * s) * tent 0 1 s with hΦ
  have hΦ0 : 0 < Φ := integral_pos_of_pos_at ((hexpc (-r)).mul hφc)
    (fun s _ => mul_nonneg (Real.exp_pos _).le (tent_nonneg 0 1 s))
    ⟨show (0 : ℝ) < 1 / 2 by norm_num, show (1 : ℝ) / 2 < 1 by norm_num⟩
    (mul_pos (Real.exp_pos _) (tent_pos ⟨by norm_num, by norm_num⟩))
  set κ := η / Φ with hκ
  have hκ0 : 0 < κ := div_pos hη hΦ0
  set c' : ℝ → ℝ × ℝ := fun s => c s + ((κ * tent 0 1 s, 0) : ℝ × ℝ) with hc'
  have hc'c : Continuous c' := hc.add ((continuous_const.mul hφc).prodMk continuous_const)
  have hc'pos : ∀ s, c' s ∈ K := fun s => by
    refine ⟨?_, ?_⟩ <;> simp only [hc', Prod.fst_add, Prod.snd_add, add_zero, Set.mem_Ioi]
    · have := (hcpos s).1; have := tent_nonneg 0 1 s; simp only [Set.mem_Ioi] at *; nlinarith
    · exact (hcpos s).2
  -- the rival's utility
  set g : ℝ → ℝ := fun s => Real.exp (-δ * s) * (u (c' s) - u (c s)) with hg
  have hgc : Continuous g :=
    (hexpc (-δ)).mul ((hucont.comp_continuous hc'c hc'pos).sub (hucont.comp_continuous hc hcpos))
  have hgz : ∀ s, s ∉ Set.Ioo 0 1 → g s = 0 := fun s hs => by
    simp [hg, hc', tent_eq_zero hs, Prod.mk_zero_zero]
  have hlim : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (c' s)) atTop
      (𝓝 (U + ∫ s in (0 : ℝ)..1, g s)) := by
    refine (hU.add_const _).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    have i1 : IntervalIntegrable (fun s => Real.exp (-δ * s) * u (c s)) volume 0 T :=
      ((hexpc (-δ)).mul (hucont.comp_continuous hc hcpos)).intervalIntegrable 0 T
    rw [← integral_eq_of_vanish hgc le_rfl hT hgz, ← intervalIntegral.integral_add i1
      (hgc.intervalIntegrable 0 T)]
    congr 1; funext s; simp only [hg]; ring
  -- the rival's wealth
  have hwealth : ∀ T, 1 ≤ T → Real.exp (-r * T) * ctWealth r Q0 y i c' T =
      Real.exp (-r * T) * ctWealth r Q0 y i c T - η := by
    intro T hT
    have hcf : Continuous fun t => Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2) :=
      (hexpc (-r)).mul ((hy.sub (continuous_fst.comp hc)).sub (hi.mul (continuous_snd.comp hc)))
    have hk : Continuous fun t => Real.exp (-r * t) * tent 0 1 t := (hexpc (-r)).mul hφc
    have hpt : ∀ t, Real.exp (-r * t) * (y t - (c' t).1 - i t * (c' t).2) =
        Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2) - κ * (Real.exp (-r * t) *
          tent 0 1 t) := fun t => by
      simp only [hc', Prod.fst_add, Prod.snd_add, add_zero]; ring
    have hvan : ∀ t, t ∉ Set.Ioo 0 1 → Real.exp (-r * t) * tent 0 1 t = 0 := fun t ht => by
      rw [tent_eq_zero ht, mul_zero]
    unfold ctWealth
    simp only [hpt]
    rw [show (∫ t in (0 : ℝ)..T, Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2) -
        κ * (Real.exp (-r * t) * tent 0 1 t)) =
        (∫ t in (0 : ℝ)..T, Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2)) -
        ∫ t in (0 : ℝ)..T, κ * (Real.exp (-r * t) * tent 0 1 t) from
      intervalIntegral.integral_sub (hcf.intervalIntegrable 0 T)
        ((hk.intervalIntegrable 0 T).const_mul κ),
      intervalIntegral.integral_const_mul, integral_eq_of_vanish hk le_rfl hT hvan, ← hΦ]
    have e : Real.exp (-r * T) * Real.exp (r * T) = 1 := by rw [← Real.exp_add]; simp
    have hκΦ : κ * Φ = η := by rw [hκ]; field_simp
    linear_combination (Q0 + (∫ t in (0 : ℝ)..T, Real.exp (-r * t) *
      (y t - (c t).1 - i t * (c t).2)) - κ * Φ) * e - hκΦ +
      (-(Q0 + ∫ t in (0 : ℝ)..T, Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2))) * e
  have hadm : CTAdmissible u r δ Q0 y i c' (U + ∫ s in (0 : ℝ)..1, g s) := by
    refine ⟨hc'c, hc'pos, hlim, fun e he => ?_⟩
    filter_upwards [hcon, eventually_ge_atTop 1] with T hT hT1
    push Not at hT
    rw [hwealth T hT1]
    linarith
  have hle := hmax _ _ hadm
  -- the utility gain is strictly positive
  have hgnn : ∀ s, 0 ≤ g s := by
    intro s
    have t := concave_le_tangent_gen hconc (hc'pos s) (hcpos s) (hdiff _ (hc'pos s))
    rw [grad_apply] at t
    simp only [hc', Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at t
    have h1 : 0 < uC (c s + (κ * tent 0 1 s, 0)) := huC _ (hc'pos s)
    have h2 := tent_nonneg 0 1 s
    simp only [hg]
    have : 0 ≤ u (c s + (κ * tent 0 1 s, 0)) - u (c s) := by
      nlinarith [mul_nonneg (mul_nonneg h1.le hκ0.le) h2]
    exact mul_nonneg (Real.exp_pos _).le this
  have hgpos : 0 < g (1 / 2) := by
    have t := concave_le_tangent_gen hconc (hc'pos (1 / 2)) (hcpos (1 / 2))
      (hdiff _ (hc'pos (1 / 2)))
    rw [grad_apply] at t
    simp only [hc', Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at t
    have h1 : 0 < uC (c (1 / 2) + (κ * tent 0 1 (1 / 2), 0)) := huC _ (hc'pos (1 / 2))
    have h2 := tent_pos (a := 0) (b := 1) (s := 1 / 2) ⟨by norm_num, by norm_num⟩
    simp only [hg]
    have : 0 < u (c (1 / 2) + (κ * tent 0 1 (1 / 2), 0)) - u (c (1 / 2)) := by
      have := mul_pos (mul_pos h1 hκ0) h2
      nlinarith
    exact mul_pos (Real.exp_pos _) this
  have := integral_pos_of_pos_at hgc (fun s _ => hgnn s)
    ⟨show (0 : ℝ) < 1 / 2 by norm_num, show (1 : ℝ) / 2 < 1 by norm_num⟩ hgpos
  linarith

/-- **The maximum principle for the monetary problem, necessary AND sufficient** (O&R Supplement
A.1–A.3, pp. 745–750, made precise): with `u` concave, continuously differentiable and
`u_C > 0` on the positive quadrant, an admissible continuous-time plan is optimal IFF, at every
date `s ≥ 0`, (8) `u_{M/P} = i u_C` and (3)+(9) `u_C(c_s) = u_C(c_0)e^{(δ−r)s}` hold, and the
transversality condition `liminf e^{−rT}Q(T) = 0` holds (the `≥` half being the no-Ponzi
condition built into admissibility). -/
theorem monetary_optimal_iff {u uC um : ℝ × ℝ → ℝ} {r δ Q0 U : ℝ} {y i : ℝ → ℝ}
    {c : ℝ → ℝ × ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) u)
    (hdiff : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), HasFDerivAt u (grad (uC p) (um p)) p)
    (hcC : ContinuousOn uC (Set.Ioi 0 ×ˢ Set.Ioi 0))
    (hcM : ContinuousOn um (Set.Ioi 0 ×ˢ Set.Ioi 0))
    (huC : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), 0 < uC p) (hy : Continuous y)
    (hi : Continuous i) (hadm : CTAdmissible u r δ Q0 y i c U) :
    CTOptimal u r δ Q0 y i c U ↔
      (∀ s, 0 ≤ s → um (c s) = i s * uC (c s)) ∧
      (∀ s, 0 ≤ s → uC (c s) = uC (c 0) * Real.exp ((δ - r) * s)) ∧
      ∀ ε > 0, ∃ᶠ T in atTop, Real.exp (-r * T) * ctWealth r Q0 y i c T < ε := by
  constructor
  · intro hopt
    exact ⟨fun s hs => ct_money_foc hconc hdiff hcC hcM hi hopt hs,
      fun s hs => ct_costate_of_optimal hconc hdiff hcC hcM hy hi hopt hs,
      ct_tvc_of_optimal hconc hdiff huC hy hi hopt⟩
  · rintro ⟨hM, hlamc, htvc⟩
    refine ⟨hadm, fun c' U' hadm' => ?_⟩
    obtain ⟨hc, hcpos, hU, _⟩ := hadm
    obtain ⟨hc', hc'pos, hU', hnp'⟩ := hadm'
    set lam : ℝ → ℝ := fun s => uC (c 0) * Real.exp ((δ - r) * s) with hlam
    have hlamd : ∀ s, HasDerivAt lam (lam s * (δ - r)) s := by
      intro s
      have := (((hasDerivAt_id s).const_mul (δ - r)).exp).const_mul (uC (c 0))
      simp only [id, mul_one] at this
      refine this.congr_deriv ?_
      simp only [hlam]; ring
    have hlam0 : 0 < lam 0 := by simp only [hlam, mul_zero, Real.exp_zero, mul_one]
                                 exact huC _ (hcpos 0)
    have hucont : ContinuousOn u (Set.Ioi 0 ×ˢ Set.Ioi 0) := fun p hp =>
      (hdiff p hp).continuousAt.continuousWithinAt
    have hexpc : Continuous fun s : ℝ => Real.exp (-δ * s) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    exact monetary_sufficiency (lam := lam) (y := y) (i := i) (r := r) (δ := δ)
      (Qs := ctWealth r Q0 y i c)
      (Q := ctWealth r Q0 y i c') hconc hdiff (fun s _ => hcpos s) (fun s _ => hc'pos s)
      (fun s hs => hlamc s hs) (fun s hs => by rw [hM s hs, hlamc s hs]; ring) hlamd hlam0
      (fun s => (ctWealth_hasDerivAt hy hi hc s).congr_deriv (by ring))
      (fun s => (ctWealth_hasDerivAt hy hi hc' s).congr_deriv (by ring))
      (by simp [ctWealth]) (monetary_boundary htvc hnp')
      (fun T => (hexpc.mul (hucont.comp_continuous hc' hc'pos)).intervalIntegrable 0 T)
      (fun T => (hexpc.mul (hucont.comp_continuous hc hcpos)).intervalIntegrable 0 T) hU' hU

end ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple
