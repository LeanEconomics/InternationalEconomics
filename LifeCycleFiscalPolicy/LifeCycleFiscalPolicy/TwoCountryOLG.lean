/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.IntermediateValue

/-!
# Public debt and the world interest rate in a two-country OLG model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §3.6,
pp. 167–174 (Figs 3.5–3.6), and Chapter 3 Exercise 4, p. 197.

Two countries share Cobb–Douglas technology `y = k^α` (`A = 1`), log preferences
and the population growth rate `n`; only the young are taxed.  With integrated
capital markets the capital-labour ratios equalise (O&R (3.50)) and the world
capital-labour ratio follows (O&R (3.52))
`k_{t+1} = Ψ(k_t) = β(1-α)/((1+n)(1+β)) · k_t^α`.
With Home government debt per worker `d̄` financed by taxes on the young
(`τ = (r - n)d̄`, O&R (3.54)) the law of motion becomes (p. 170)
`Ψ(k, d̄) = β[(1-α)k^α - x(αk^{α-1} - n)d̄]/((1+n)(1+β)) - x d̄`,
with `x` Home's share of world labour.

Main results:
* global monotone convergence of the debt-free map to `k̄` (Fig 3.5, proved here);
* `Ψ(·, d̄)` is strictly increasing and strictly concave; two positive steady states
  exist when `Ψ(k, d̄) > k` somewhere, the upper one attracts every orbit starting above
  the lower one; no positive steady state exists when the debt is large (a threshold the
  book omits);
* crowding out: debt lowers the upper steady state and raises the world interest rate.
  In fact `∂Ψ/∂d̄ < 0` at every `k > 0`, for any `r` (not only `r ≥ n`);
* §3.6.4: `r̄ ≤ n` exactly when `α` is below an explicit threshold, and `r̄ → 0` as `α → 0`;
* Exercise 4 (a precise piece): the steady-state lifetime utility of the untaxed Foreign
  young rises with `k` if and only if `β(1-α)r < α(1+β)(1+r)`; so when
  `α(1+β) ≥ β(1-α)` Home debt strictly lowers Foreign steady-state welfare, while for small
  `α` and high `r` it can raise it.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG

open Filter Topology Set

/-- The two-country OLG world of O&R §3.6.1, p. 167: capital share `α ∈ (0,1)`,
discount factor `β > 0`, common population growth `n > -1`, Home labour share
`x ∈ (0,1]` (p. 170). -/
structure TwoCountry where
  α : ℝ
  β : ℝ
  n : ℝ
  x : ℝ
  α_pos : 0 < α
  α_lt_one : α < 1
  β_pos : 0 < β
  n_gt : -1 < n
  x_pos : 0 < x
  x_le_one : x ≤ 1

/-! ## Generic monotone convergence of one-dimensional maps -/

/-- Monotone convergence from below (the staircase of O&R Fig 3.5, p. 169): if `f p = p`,
`k < f k < p` on `(a, p)` and `f` is continuous on `(a, p]`, then every orbit starting in
`(a, p]` is nondecreasing and converges to `p`. -/
theorem iterate_tendsto_of_below {f : ℝ → ℝ} {a p k0 : ℝ} (hfp : f p = p)
    (hbelow : ∀ k, a < k → k < p → k < f k ∧ f k < p)
    (hcont : ∀ k, a < k → k ≤ p → ContinuousAt f k) (ha : a < k0) (hp : k0 ≤ p) :
    Monotone (fun t : ℕ => f^[t] k0) ∧ Tendsto (fun t : ℕ => f^[t] k0) atTop (𝓝 p) := by
  have aux : ∀ y, k0 ≤ y → y ≤ p → y ≤ f y ∧ f y ≤ p := by
    intro y hy1 hy2
    rcases hy2.lt_or_eq with h | h
    · exact ⟨(hbelow y (ha.trans_le hy1) h).1.le, (hbelow y (ha.trans_le hy1) h).2.le⟩
    · rw [h, hfp]; exact ⟨le_rfl, le_rfl⟩
  have hmem : ∀ t : ℕ, k0 ≤ f^[t] k0 ∧ f^[t] k0 ≤ p := by
    intro t
    induction t with
    | zero => exact ⟨le_rfl, hp⟩
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨ih.1.trans (aux _ ih.1 ih.2).1, (aux _ ih.1 ih.2).2⟩
  have hmono : Monotone (fun t : ℕ => f^[t] k0) := by
    refine monotone_nat_of_le_succ fun t => ?_
    simp only [Function.iterate_succ_apply']
    exact (aux _ (hmem t).1 (hmem t).2).1
  refine ⟨hmono, ?_⟩
  have hbdd : BddAbove (range fun t : ℕ => f^[t] k0) := ⟨p, by
    rintro _ ⟨t, rfl⟩; exact (hmem t).2⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ t : ℕ, f^[t] k0 with hL
  have hLp : L ≤ p := ciSup_le fun t => (hmem t).2
  have hk0L : k0 ≤ L := le_ciSup_of_le hbdd 0 le_rfl
  have hshift : Tendsto (fun t : ℕ => f (f^[t] k0)) atTop (𝓝 L) := by
    have := hlim.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun t => ?_
    simp [Function.iterate_succ_apply']
  have hfL : f L = L :=
    tendsto_nhds_unique ((hcont L (ha.trans_le hk0L) hLp).tendsto.comp hlim) hshift
  rcases hLp.lt_or_eq with h | h
  · exact absurd hfL (hbelow L (ha.trans_le hk0L) h).1.ne'
  · rw [← h]; exact hlim

/-- Monotone convergence from above (O&R Fig 3.5, p. 169): if `f p = p`, `p < f k < k`
for `k > p` and `f` is continuous on `[p, ∞)`, every orbit starting at `k0 ≥ p` is
nonincreasing and converges to `p`. -/
theorem iterate_tendsto_of_above {f : ℝ → ℝ} {p k0 : ℝ} (hfp : f p = p)
    (habove : ∀ k, p < k → p < f k ∧ f k < k)
    (hcont : ∀ k, p ≤ k → ContinuousAt f k) (hp : p ≤ k0) :
    Antitone (fun t : ℕ => f^[t] k0) ∧ Tendsto (fun t : ℕ => f^[t] k0) atTop (𝓝 p) := by
  have aux : ∀ y, p ≤ y → f y ≤ y ∧ p ≤ f y := by
    intro y hy
    rcases hy.lt_or_eq with h | h
    · exact ⟨(habove y h).2.le, (habove y h).1.le⟩
    · rw [← h, hfp]; exact ⟨le_rfl, le_rfl⟩
  have hmem : ∀ t : ℕ, p ≤ f^[t] k0 := by
    intro t
    induction t with
    | zero => exact hp
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact (aux _ ih).2
  have hanti : Antitone (fun t : ℕ => f^[t] k0) := by
    refine antitone_nat_of_succ_le fun t => ?_
    simp only [Function.iterate_succ_apply']
    exact (aux _ (hmem t)).1
  refine ⟨hanti, ?_⟩
  have hbdd : BddBelow (range fun t : ℕ => f^[t] k0) := ⟨p, by
    rintro _ ⟨t, rfl⟩; exact hmem t⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ t : ℕ, f^[t] k0 with hL
  have hpL : p ≤ L := le_ciInf fun t => hmem t
  have hshift : Tendsto (fun t : ℕ => f (f^[t] k0)) atTop (𝓝 L) := by
    have := hlim.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun t => ?_
    simp [Function.iterate_succ_apply']
  have hfL : f L = L := tendsto_nhds_unique ((hcont L hpL).tendsto.comp hlim) hshift
  rcases hpL.lt_or_eq with h | h
  · exact absurd hfL (habove L h).2.ne
  · rw [h]; exact hlim

/-- Strict concavity on `(0, ∞)` in secant form: for `0 < a < z < b` the chord lies strictly
below the graph (used for the steady-state pattern of O&R Fig 3.6, p. 171). -/
theorem strictConcave_chord_lt {g : ℝ → ℝ} (hg : StrictConcaveOn ℝ (Ioi 0) g) {a z b : ℝ}
    (ha : 0 < a) (haz : a < z) (hzb : z < b) :
    (b - z) / (b - a) * g a + (z - a) / (b - a) * g b < g z := by
  have hba : 0 < b - a := by linarith
  have h := hg.2 (mem_Ioi.2 ha) (mem_Ioi.2 (ha.trans (haz.trans hzb))) (by linarith)
    (div_pos (by linarith : (0 : ℝ) < b - z) hba) (div_pos (by linarith : (0 : ℝ) < z - a) hba)
    (by field_simp; ring)
  have hz : (b - z) / (b - a) * a + (z - a) / (b - a) * b = z := by field_simp; ring
  simp only [smul_eq_mul] at h
  rwa [hz] at h

namespace TwoCountry

variable (e : TwoCountry)

/-! ## The debt-free world economy (O&R §3.6.2) -/

/-- The slope coefficient `β(1-α)/((1+n)(1+β))` of O&R (3.52), p. 169. -/
noncomputable def coef : ℝ := e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β))

/-- The debt-free law of motion `Ψ(k) = β(1-α)k^α/((1+n)(1+β))`, O&R (3.52), p. 169. -/
noncomputable def psi (k : ℝ) : ℝ := e.coef * k ^ e.α

/-- The positive steady state `k̄ = [β(1-α)/((1+n)(1+β))]^{1/(1-α)}`, O&R p. 169. -/
noncomputable def kbar : ℝ := e.coef ^ (1 / (1 - e.α))

/-- The world interest rate `r = αk^{α-1}`, O&R (3.50), p. 168. -/
noncomputable def rate (k : ℝ) : ℝ := e.α * k ^ (e.α - 1)

/-- The coefficient `β(1-α)/((1+n)(1+β))` is positive (O&R (3.52), p. 169). -/
theorem coef_pos : 0 < e.coef := by
  have := e.α_lt_one; have := e.β_pos; have := e.n_gt
  unfold coef
  apply div_pos (mul_pos e.β_pos (by linarith)) (mul_pos (by linarith) (by linarith))

/-- `k̄ > 0` (O&R p. 169). -/
theorem kbar_pos : 0 < e.kbar := Real.rpow_pos_of_pos e.coef_pos _

/-- The zero capital stock is a steady state, `Ψ(0) = 0` (O&R p. 169). -/
theorem psi_zero : e.psi 0 = 0 := by
  simp [psi, Real.zero_rpow e.α_pos.ne']

/-- `k̄` is a steady state of O&R (3.52), p. 169: `Ψ(k̄) = k̄`. -/
theorem psi_kbar : e.psi e.kbar = e.kbar := by
  have hc := e.coef_pos
  have h1 : 1 - e.α ≠ 0 := by have := e.α_lt_one; linarith
  unfold psi kbar
  rw [← Real.rpow_mul hc.le]
  conv_lhs => arg 1; rw [← Real.rpow_one e.coef]
  rw [← Real.rpow_add hc]
  congr 1
  field_simp
  ring

/-- `k̄` is the UNIQUE positive steady state of O&R (3.52), p. 169. -/
theorem psi_fixed_iff {k : ℝ} (hk : 0 < k) : e.psi k = k ↔ k = e.kbar := by
  refine ⟨fun h => ?_, fun h => h ▸ e.psi_kbar⟩
  have h1 : 1 - e.α ≠ 0 := by have := e.α_lt_one; linarith
  have hsplit : k = k ^ (1 - e.α) * k ^ e.α := by
    rw [← Real.rpow_add hk]; simp
  have hc : e.coef = k ^ (1 - e.α) := by
    have hpos : 0 < k ^ e.α := Real.rpow_pos_of_pos hk _
    unfold psi at h
    have : e.coef * k ^ e.α = k ^ (1 - e.α) * k ^ e.α := h.trans hsplit
    exact mul_right_cancel₀ hpos.ne' this
  unfold kbar
  rw [hc, ← Real.rpow_mul hk.le, mul_one_div_cancel h1, Real.rpow_one]

/-- `Ψ` is strictly increasing on `[0, ∞)` (O&R Fig 3.5, p. 169). -/
theorem psi_strictMonoOn : StrictMonoOn e.psi (Ici 0) := by
  intro a ha b _ hab
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow ha hab e.α_pos) e.coef_pos

/-- `coef · k̄^α / k̄ = 1`, a restatement of the fixed point (O&R p. 169). -/
theorem coef_kbar_div : e.coef * e.kbar ^ e.α / e.kbar = 1 := by
  have := e.psi_kbar
  unfold psi at this
  rw [this, div_self e.kbar_pos.ne']

/-- Below `k̄` capital rises but stays below `k̄`: `0 < k < k̄ ⇒ k < Ψ(k) < k̄`
(O&R Fig 3.5, p. 169). -/
theorem psi_between_below {k : ℝ} (hk : 0 < k) (hlt : k < e.kbar) :
    k < e.psi k ∧ e.psi k < e.kbar := by
  refine ⟨?_, e.psi_kbar ▸ e.psi_strictMonoOn (mem_Ici.2 hk.le) (mem_Ici.2 e.kbar_pos.le) hlt⟩
  have hdec : e.kbar ^ (e.α - 1) < k ^ (e.α - 1) :=
    Real.rpow_lt_rpow_of_neg hk hlt (by linarith [e.α_lt_one])
  rw [Real.rpow_sub_one hk.ne', Real.rpow_sub_one e.kbar_pos.ne'] at hdec
  have h1 : 1 < e.coef * k ^ e.α / k := by
    rw [← e.coef_kbar_div, mul_div_assoc, mul_div_assoc]
    exact mul_lt_mul_of_pos_left hdec e.coef_pos
  unfold psi
  rwa [lt_div_iff₀ hk, one_mul] at h1

/-- Above `k̄` capital falls but stays above `k̄`: `k̄ < k ⇒ k̄ < Ψ(k) < k`
(O&R Fig 3.5, p. 169). -/
theorem psi_between_above {k : ℝ} (hgt : e.kbar < k) :
    e.kbar < e.psi k ∧ e.psi k < k := by
  have hk : 0 < k := e.kbar_pos.trans hgt
  refine ⟨e.psi_kbar ▸ e.psi_strictMonoOn (mem_Ici.2 e.kbar_pos.le) (mem_Ici.2 hk.le) hgt, ?_⟩
  have hdec : k ^ (e.α - 1) < e.kbar ^ (e.α - 1) :=
    Real.rpow_lt_rpow_of_neg e.kbar_pos hgt (by linarith [e.α_lt_one])
  rw [Real.rpow_sub_one hk.ne', Real.rpow_sub_one e.kbar_pos.ne'] at hdec
  have h1 : e.coef * k ^ e.α / k < 1 := by
    rw [← e.coef_kbar_div, mul_div_assoc, mul_div_assoc]
    exact mul_lt_mul_of_pos_left hdec e.coef_pos
  unfold psi
  rwa [div_lt_iff₀ hk, one_mul] at h1

/-- `Ψ` is continuous (O&R (3.52), p. 169). -/
theorem psi_continuous : Continuous e.psi :=
  continuous_const.mul (Real.continuous_rpow_const e.α_pos.le)

/-- Global stability, O&R Fig 3.5, p. 169: from ANY `k_0 > 0` the world capital-labour ratio
converges to `k̄`, monotonically (increasing if `k_0 ≤ k̄`, decreasing if `k_0 ≥ k̄`). -/
theorem psi_global_convergence {k0 : ℝ} (hk0 : 0 < k0) :
    Tendsto (fun t : ℕ => e.psi^[t] k0) atTop (𝓝 e.kbar) ∧
      (k0 ≤ e.kbar → Monotone (fun t : ℕ => e.psi^[t] k0)) ∧
      (e.kbar ≤ k0 → Antitone (fun t : ℕ => e.psi^[t] k0)) := by
  have hbelow : ∀ k, 0 < k → k < e.kbar → k < e.psi k ∧ e.psi k < e.kbar :=
    fun k hk hlt => e.psi_between_below hk hlt
  have hcont : ∀ k : ℝ, ContinuousAt e.psi k := fun k => e.psi_continuous.continuousAt
  refine ⟨?_, fun h => (iterate_tendsto_of_below e.psi_kbar hbelow
      (fun k _ _ => hcont k) hk0 h).1,
    fun h => (iterate_tendsto_of_above e.psi_kbar (fun k hk => e.psi_between_above hk)
      (fun k _ => hcont k) h).1⟩
  rcases le_total k0 e.kbar with h | h
  · exact (iterate_tendsto_of_below e.psi_kbar hbelow (fun k _ _ => hcont k) hk0 h).2
  · exact (iterate_tendsto_of_above e.psi_kbar (fun k hk => e.psi_between_above hk)
      (fun k _ => hcont k) h).2

/-- The zero steady state is unstable (O&R p. 169): no orbit from `k_0 > 0` converges
to `0`. -/
theorem zero_unstable {k0 : ℝ} (hk0 : 0 < k0) :
    ¬ Tendsto (fun t : ℕ => e.psi^[t] k0) atTop (𝓝 0) := fun h =>
  e.kbar_pos.ne' (tendsto_nhds_unique (e.psi_global_convergence hk0).1 h)

/-- The steady-state interest rate as a function of the primitives, O&R (3.53), p. 169:
`r̄ = α(1+n)(1+β)/(β(1-α))`. -/
noncomputable def rbarOf (α β n : ℝ) : ℝ := α * (1 + n) * (1 + β) / (β * (1 - α))

/-- O&R (3.53), p. 169: the marginal product of capital at `k̄` is
`α(k̄)^{α-1} = α(1+n)(1+β)/(β(1-α))`. -/
theorem rate_kbar : e.rate e.kbar = rbarOf e.α e.β e.n := by
  have hc := e.coef_pos
  have h1 : 1 - e.α ≠ 0 := by have := e.α_lt_one; linarith
  have hpow : e.kbar ^ (e.α - 1) = e.coef⁻¹ := by
    unfold kbar
    rw [← Real.rpow_mul hc.le, ← Real.rpow_neg_one]
    congr 1
    field_simp
    ring
  have := e.β_pos; have := e.n_gt
  have h2 : (1 + e.n) ≠ 0 := by linarith
  have h3 : (1 + e.β) ≠ 0 := by linarith
  unfold rate rbarOf
  rw [hpow]
  unfold coef
  field_simp

/-! ## Public debt (O&R §3.6.3) -/

/-- O&R (3.54), p. 170: keeping government debt per worker constant at `d̄`
(`-B_t = d̄N_t`, `-B_{t+1} = d̄(1+n)N_t`) under the budget `B_{t+1} = (1+r)B_t + N_tτ`
requires the tax on each young worker `τ = (r - n)d̄`. -/
theorem tax_eq {B B' N τ r n d : ℝ} (hN : N ≠ 0) (hB : B = -(d * N))
    (hB' : B' = -(d * ((1 + n) * N))) (hbud : B' = (1 + r) * B + N * τ) :
    τ = (r - n) * d := by
  rw [hB, hB'] at hbud
  have h : N * (τ - (r - n) * d) = 0 := by linear_combination -hbud
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h hN
  · linarith

/-- The law of motion with Home debt, O&R p. 170:
`Ψ(k, d̄) = β[(1-α)k^α - x(αk^{α-1} - n)d̄]/((1+n)(1+β)) - x d̄`. -/
noncomputable def psiDebt (d k : ℝ) : ℝ :=
  e.β * ((1 - e.α) * k ^ e.α - e.x * (e.α * k ^ (e.α - 1) - e.n) * d) /
    ((1 + e.n) * (1 + e.β)) - e.x * d

/-- Derivation of the debt law of motion, O&R (3.55) and p. 170: with Home saving
`s = β[w - (r - n)d̄]/(1+β)`, Foreign saving `s* = βw/(1+β)`, `w = (1-α)k^α`,
`r = αk^{α-1}`, and world asset-market clearing `K' + K*' + d̄N_{t+1} = Ns + N*s*`, the
next-period world capital-labour ratio `(K'+K*')/((1+n)(N+N*))` equals `Ψ(k, d̄)` when
`x = N/(N+N*)`. -/
theorem law_of_motion_debt {d k N Ns Kw s sS : ℝ} (hN : 0 < N) (hNs : 0 < Ns)
    (hx : e.x = N / (N + Ns))
    (hs : s = e.β / (1 + e.β) *
      ((1 - e.α) * k ^ e.α - (e.α * k ^ (e.α - 1) - e.n) * d))
    (hsS : sS = e.β / (1 + e.β) * ((1 - e.α) * k ^ e.α))
    (hclear : Kw + d * ((1 + e.n) * N) = N * s + Ns * sS) :
    Kw / ((1 + e.n) * (N + Ns)) = e.psiDebt d k := by
  have := e.β_pos; have := e.n_gt
  have h1 : (1 + e.n) ≠ 0 := by linarith
  have h2 : (1 + e.β) ≠ 0 := by linarith
  have h3 : N + Ns ≠ 0 := by linarith
  have hK : Kw = N * s + Ns * sS - d * ((1 + e.n) * N) := by linarith
  unfold psiDebt
  rw [hK, hx, hs, hsS]
  field_simp
  ring

/-- With zero debt the law of motion reduces to O&R (3.52), p. 170: `Ψ(k, 0) = Ψ(k)`. -/
theorem psiDebt_zero (k : ℝ) : e.psiDebt 0 k = e.psi k := by
  unfold psiDebt psi coef
  ring

/-- Decomposition of the debt law of motion (O&R p. 170):
`Ψ(k, d̄) = Ψ(k) - x d̄ [1 + β(r - n)/((1+n)(1+β))]` with `r = αk^{α-1}`. -/
theorem psiDebt_eq (d k : ℝ) : e.psiDebt d k =
    e.psi k - e.x * d * (1 + e.β * (e.rate k - e.n) / ((1 + e.n) * (1 + e.β))) := by
  unfold psiDebt psi coef rate
  ring

/-- The crowding-out bracket is positive at every `k > 0` (O&R p. 171):
`1 + β(r - n)/((1+n)(1+β)) = (1 + n + β + βr)/((1+n)(1+β)) > 0`. This holds for any
`r > 0` and `n > -1`, not only when `r ≥ n`. -/
theorem crowding_bracket_pos {k : ℝ} (hk : 0 < k) :
    0 < 1 + e.β * (e.rate k - e.n) / ((1 + e.n) * (1 + e.β)) := by
  have := e.β_pos; have := e.n_gt
  have hr : 0 < e.rate k := mul_pos e.α_pos (Real.rpow_pos_of_pos hk _)
  have hD : 0 < (1 + e.n) * (1 + e.β) := mul_pos (by linarith) (by linarith)
  have h1 : (1 + e.n) ≠ 0 := by linarith
  have h2 : (1 + e.β) ≠ 0 := by linarith
  have heq : 1 + e.β * (e.rate k - e.n) / ((1 + e.n) * (1 + e.β)) =
      (1 + e.n + e.β + e.β * e.rate k) / ((1 + e.n) * (1 + e.β)) := by
    field_simp; ring
  rw [heq]
  exact div_pos (by nlinarith) hD

/-- O&R p. 171, as a derivative: `∂Ψ(k, d̄)/∂d̄ = -x[1 + β(r - n)/((1+n)(1+β))]`. -/
theorem psiDebt_hasDerivAt_debt (d k : ℝ) :
    HasDerivAt (fun d' => e.psiDebt d' k)
      (-(e.x * (1 + e.β * (e.rate k - e.n) / ((1 + e.n) * (1 + e.β))))) d := by
  have hfun : (fun d' => e.psiDebt d' k) = fun d' =>
      e.psi k - e.x * (d' * (1 + e.β * (e.rate k - e.n) / ((1 + e.n) * (1 + e.β)))) := by
    funext d'; rw [psiDebt_eq]; ring
  rw [hfun]
  have h := (((hasDerivAt_id d).mul_const
    (1 + e.β * (e.rate k - e.n) / ((1 + e.n) * (1 + e.β)))).const_mul e.x).const_sub (e.psi k)
  convert h using 1 <;> simp

/-- Debt shifts the law of motion down at every `k > 0` (O&R Fig 3.6, p. 171):
`d_1 < d_2 ⇒ Ψ(k, d_2) < Ψ(k, d_1)`. -/
theorem psiDebt_strictAnti_debt {k d1 d2 : ℝ} (hk : 0 < k) (hd : d1 < d2) :
    e.psiDebt d2 k < e.psiDebt d1 k := by
  rw [psiDebt_eq, psiDebt_eq]
  have hb := e.crowding_bracket_pos hk
  have : e.x * d1 * _ < e.x * d2 * _ :=
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hd e.x_pos) hb
  linarith

/-- Positive debt lies strictly below the debt-free map (O&R Fig 3.6, p. 171):
`d̄ > 0 ⇒ Ψ(k, d̄) < Ψ(k)`. -/
theorem psiDebt_lt_psi {k d : ℝ} (hk : 0 < k) (hd : 0 < d) : e.psiDebt d k < e.psi k := by
  rw [← e.psiDebt_zero k]; exact e.psiDebt_strictAnti_debt hk hd

/-- The derivative of the debt law of motion in `k` (O&R Fig 3.6, p. 171):
`∂Ψ/∂k = A α k^{α-1} + B (α-1) k^{α-2}` with `A = β(1-α)/((1+n)(1+β))` and
`B = -βxαd̄/((1+n)(1+β))`. -/
theorem psiDebt_hasDerivAt {d k : ℝ} (hk : 0 < k) :
    HasDerivAt (e.psiDebt d)
      (e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * (e.α * k ^ (e.α - 1)) +
        -(e.β * e.x * e.α * d) / ((1 + e.n) * (1 + e.β)) *
          ((e.α - 1) * k ^ (e.α - 1 - 1))) k := by
  have hfun : e.psiDebt d = fun y =>
      e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * y ^ e.α +
        -(e.β * e.x * e.α * d) / ((1 + e.n) * (1 + e.β)) * y ^ (e.α - 1) +
        (e.β * e.x * e.n * d / ((1 + e.n) * (1 + e.β)) - e.x * d) := by
    funext y; unfold psiDebt; ring
  rw [hfun]
  have h1 := Real.hasDerivAt_rpow_const (p := e.α) (Or.inl hk.ne')
  have h2 := Real.hasDerivAt_rpow_const (p := e.α - 1) (Or.inl hk.ne')
  exact ((h1.const_mul _).add (h2.const_mul _)).add_const _

/-- The derivative of `Ψ(·, d̄)` is strictly decreasing on `(0, ∞)` for `d̄ ≥ 0`
(the curvature of O&R Fig 3.6, p. 171). -/
theorem psiDebt_deriv_strictAnti {d a b : ℝ} (hd : 0 ≤ d) (ha : 0 < a) (hab : a < b) :
    e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * (e.α * b ^ (e.α - 1)) +
        -(e.β * e.x * e.α * d) / ((1 + e.n) * (1 + e.β)) * ((e.α - 1) * b ^ (e.α - 1 - 1)) <
      e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * (e.α * a ^ (e.α - 1)) +
        -(e.β * e.x * e.α * d) / ((1 + e.n) * (1 + e.β)) *
          ((e.α - 1) * a ^ (e.α - 1 - 1)) := by
  have := e.β_pos; have := e.n_gt; have := e.α_lt_one; have := e.α_pos; have := e.x_pos
  have hD : 0 < (1 + e.n) * (1 + e.β) := mul_pos (by linarith) (by linarith)
  have hA : 0 < e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * e.α :=
    mul_pos (div_pos (mul_pos e.β_pos (by linarith)) hD) e.α_pos
  have hB : 0 ≤ -(e.β * e.x * e.α * d) / ((1 + e.n) * (1 + e.β)) * (e.α - 1) := by
    rw [div_mul_eq_mul_div]
    apply div_nonneg _ hD.le
    have : 0 ≤ e.β * e.x * e.α * d := by positivity
    nlinarith
  have h1 : b ^ (e.α - 1) < a ^ (e.α - 1) := Real.rpow_lt_rpow_of_neg ha hab (by linarith)
  have h2 : b ^ (e.α - 1 - 1) < a ^ (e.α - 1 - 1) :=
    Real.rpow_lt_rpow_of_neg ha hab (by linarith)
  have e1 := mul_lt_mul_of_pos_left h1 hA
  have e2 := mul_le_mul_of_nonneg_left h2.le hB
  nlinarith

/-- `Ψ(·, d̄)` is strictly increasing on `(0, ∞)` for `d̄ ≥ 0` (O&R Fig 3.6, p. 171). -/
theorem psiDebt_strictMonoOn {d : ℝ} (hd : 0 ≤ d) : StrictMonoOn (e.psiDebt d) (Ioi 0) := by
  have := e.β_pos; have := e.n_gt; have := e.α_lt_one; have := e.α_pos; have := e.x_pos
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun k hk => (e.psiDebt_hasDerivAt hk).continuousAt.continuousWithinAt) fun k hk => ?_
  rw [interior_Ioi] at hk
  have hk : 0 < k := hk
  rw [(e.psiDebt_hasDerivAt hk).deriv]
  have hD : 0 < (1 + e.n) * (1 + e.β) := mul_pos (by linarith) (by linarith)
  have hA : 0 < e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * (e.α * k ^ (e.α - 1)) :=
    mul_pos (div_pos (mul_pos e.β_pos (by linarith)) hD)
      (mul_pos e.α_pos (Real.rpow_pos_of_pos hk _))
  have hB : 0 ≤ -(e.β * e.x * e.α * d) / ((1 + e.n) * (1 + e.β)) *
      ((e.α - 1) * k ^ (e.α - 1 - 1)) := by
    have hp : 0 < k ^ (e.α - 1 - 1) := Real.rpow_pos_of_pos hk _
    have : 0 ≤ e.β * e.x * e.α * d := by positivity
    rw [div_mul_eq_mul_div]
    apply div_nonneg _ hD.le
    have : 0 ≤ e.β * e.x * e.α * d * ((1 - e.α) * k ^ (e.α - 1 - 1)) :=
      mul_nonneg this (mul_nonneg (by linarith) hp.le)
    nlinarith
  linarith

/-- `Ψ(·, d̄)` is strictly concave on `(0, ∞)` for `d̄ ≥ 0` (the shape drawn in O&R
Fig 3.6, p. 171): `k^α` is concave and `-k^{α-1}` is concave. -/
theorem psiDebt_strictConcaveOn {d : ℝ} (hd : 0 ≤ d) :
    StrictConcaveOn ℝ (Ioi 0) (e.psiDebt d) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0)
    (fun k hk => (e.psiDebt_hasDerivAt hk).continuousAt.continuousWithinAt) ?_
  rw [interior_Ioi]
  intro a ha b hb hab
  rw [(e.psiDebt_hasDerivAt ha).deriv, (e.psiDebt_hasDerivAt hb).deriv]
  exact e.psiDebt_deriv_strictAnti hd ha hab

/-- The excess `Ψ(k, d̄) - k` is strictly concave on `(0, ∞)` for `d̄ ≥ 0`, so it has at most
two zeros (O&R Fig 3.6, p. 171). -/
theorem psiDebt_gap_strictConcaveOn {d : ℝ} (hd : 0 ≤ d) :
    StrictConcaveOn ℝ (Ioi 0) (fun k => e.psiDebt d k - k) := by
  have hder : ∀ k, 0 < k → HasDerivAt (fun k => e.psiDebt d k - k)
      (e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * (e.α * k ^ (e.α - 1)) +
        -(e.β * e.x * e.α * d) / ((1 + e.n) * (1 + e.β)) *
          ((e.α - 1) * k ^ (e.α - 1 - 1)) - 1) k :=
    fun k hk => (e.psiDebt_hasDerivAt hk).sub (hasDerivAt_id k)
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0)
    (fun k hk => (hder k hk).continuousAt.continuousWithinAt) ?_
  rw [interior_Ioi]
  intro a ha b hb hab
  rw [(hder a ha).deriv, (hder b hb).deriv]
  linarith [e.psiDebt_deriv_strictAnti hd ha hab]

/-- Steady-state pattern with debt (O&R Fig 3.6, p. 171): if `0 < l < u` are both steady
states of `Ψ(·, d̄)` with `d̄ ≥ 0`, then capital falls below `l`, rises between `l` and `u`,
and falls above `u`; in particular there are no other positive steady states. -/
theorem steady_state_pattern {d l u : ℝ} (hd : 0 ≤ d) (hl : 0 < l) (hlu : l < u)
    (hfl : e.psiDebt d l = l) (hfu : e.psiDebt d u = u) :
    (∀ k, 0 < k → k < l → e.psiDebt d k < k) ∧
      (∀ k, l < k → k < u → k < e.psiDebt d k) ∧
      (∀ k, u < k → e.psiDebt d k < k) := by
  have hg := e.psiDebt_gap_strictConcaveOn hd
  have hgl : e.psiDebt d l - l = 0 := by rw [hfl]; ring
  have hgu : e.psiDebt d u - u = 0 := by rw [hfu]; ring
  refine ⟨fun k hk hkl => ?_, fun k hlk hku => ?_, fun k huk => ?_⟩
  · have h := strictConcave_chord_lt hg hk hkl hlu
    simp only [hgl, hgu] at h
    have hpos : 0 < (l - k) / (u - k) := div_pos (by linarith) (by linarith)
    have : (u - l) / (u - k) * (e.psiDebt d k - k) < 0 := by linarith
    have hc : 0 < (u - l) / (u - k) := div_pos (by linarith) (by linarith)
    have := (mul_neg_iff.1 this).resolve_right (fun h' => (not_lt.2 hc.le) h'.1)
    linarith [this.2]
  · have h := strictConcave_chord_lt hg hl hlk hku
    simp only [hgl, hgu, mul_zero, add_zero] at h
    linarith
  · have h := strictConcave_chord_lt hg hl hlu huk
    simp only [hgl, hgu] at h
    have hc : 0 < (u - l) / (k - l) := div_pos (by linarith) (by linarith)
    have : (u - l) / (k - l) * (e.psiDebt d k - k) < 0 := by linarith
    have := (mul_neg_iff.1 this).resolve_right (fun h' => (not_lt.2 hc.le) h'.1)
    linarith [this.2]

/-- At most two positive steady states (O&R Fig 3.6, p. 171): with steady states `0 < l < u`
and `d̄ ≥ 0`, every positive steady state is `l` or `u`. -/
theorem steady_state_at_most_two {d l u k : ℝ} (hd : 0 ≤ d) (hl : 0 < l) (hlu : l < u)
    (hfl : e.psiDebt d l = l) (hfu : e.psiDebt d u = u) (hk : 0 < k)
    (hfk : e.psiDebt d k = k) : k = l ∨ k = u := by
  obtain ⟨h1, h2, h3⟩ := e.steady_state_pattern hd hl hlu hfl hfu
  rcases lt_trichotomy k l with h | h | h
  · exact absurd hfk (h1 k hk h).ne
  · exact Or.inl h
  rcases lt_trichotomy k u with h' | h' | h'
  · exact absurd hfk (h2 k h h').ne'
  · exact Or.inr h'
  · exact absurd hfk (h3 k h').ne

/-- Stability of the upper steady state (O&R Fig 3.6, p. 171): with steady states
`0 < l < u` and `d̄ ≥ 0`, every orbit starting above the unstable lower steady state `l`
converges monotonically to `u`. -/
theorem upper_steady_state_attracts {d l u k0 : ℝ} (hd : 0 ≤ d) (hl : 0 < l) (hlu : l < u)
    (hfl : e.psiDebt d l = l) (hfu : e.psiDebt d u = u) (hk0 : l < k0) :
    Tendsto (fun t : ℕ => (e.psiDebt d)^[t] k0) atTop (𝓝 u) := by
  obtain ⟨_, h2, h3⟩ := e.steady_state_pattern hd hl hlu hfl hfu
  have hmono := e.psiDebt_strictMonoOn hd
  have hcont : ∀ k, 0 < k → ContinuousAt (e.psiDebt d) k :=
    fun k hk => (e.psiDebt_hasDerivAt hk).continuousAt
  have hu : 0 < u := hl.trans hlu
  rcases le_total k0 u with h | h
  · refine (iterate_tendsto_of_below hfu (fun k hlk hku => ⟨h2 k hlk hku, ?_⟩)
      (fun k hk _ => hcont k (hl.trans hk)) hk0 h).2
    exact hfu ▸ hmono (mem_Ioi.2 (hl.trans hlk)) (mem_Ioi.2 hu) hku
  · refine (iterate_tendsto_of_above hfu (fun k huk => ⟨?_, h3 k huk⟩)
      (fun k hk => hcont k (hu.trans_le hk)) h).2
    exact hfu ▸ hmono (mem_Ioi.2 hu) (mem_Ioi.2 (hu.trans huk)) huk

/-- An upper (stable) steady state of `Ψ(·, d̄)` (O&R p. 171): a positive steady state above
which capital always falls. -/
def IsUpperSteadyState (d u : ℝ) : Prop :=
  0 < u ∧ e.psiDebt d u = u ∧ ∀ k, u < k → e.psiDebt d k < k

/-- Without debt `k̄` is the upper steady state (O&R p. 169). -/
theorem kbar_isUpper : e.IsUpperSteadyState 0 e.kbar := by
  refine ⟨e.kbar_pos, by rw [psiDebt_zero, psi_kbar], fun k hk => ?_⟩
  rw [psiDebt_zero]; exact (e.psi_between_above hk).2

/-- `Ψ(k) ≤ k + k̄` for every `k > 0` (bound used for the debt threshold, O&R p. 169). -/
theorem psi_le_add_kbar {k : ℝ} (hk : 0 < k) : e.psi k ≤ k + e.kbar := by
  rcases le_or_gt k e.kbar with h | h
  · rcases h.lt_or_eq with h' | h'
    · linarith [(e.psi_between_below hk h').2]
    · rw [h', psi_kbar]; linarith
  · linarith [(e.psi_between_above h).2, e.kbar_pos]

/-- Existence of steady states with debt (O&R Fig 3.6, p. 171, made precise): if
`d̄ > 0` and `Ψ(k*, d̄) > k*` for some `k* > 0`, there are exactly the two steady states
`0 < l < k* < u ≤ k̄` of the figure, and `u` is the upper (stable) one. The book assumes
this configuration silently; it fails for large debt
(see `no_steady_state_of_large_debt`). -/
theorem exists_two_steady_states {d ks : ℝ} (hd : 0 < d) (hks : 0 < ks)
    (hgap : ks < e.psiDebt d ks) :
    ∃ l u, 0 < l ∧ l < ks ∧ ks < u ∧ u ≤ e.kbar ∧ e.psiDebt d l = l ∧
      e.psiDebt d u = u ∧ e.IsUpperSteadyState d u := by
  have := e.β_pos; have := e.n_gt; have := e.α_lt_one; have := e.α_pos; have := e.x_pos
  have hcont : ContinuousOn (fun k => e.psiDebt d k - k) (Ioi 0) := fun k hk =>
    ((e.psiDebt_hasDerivAt hk).continuousAt.sub continuousAt_id).continuousWithinAt
  -- `ks < k̄`
  have hks_kbar : ks < e.kbar := by
    by_contra h
    push Not at h
    have hle : e.psi ks ≤ ks := by
      rcases h.lt_or_eq with h' | h'
      · exact (e.psi_between_above h').2.le
      · rw [← h', psi_kbar]
    linarith [e.psiDebt_lt_psi hks hd]
  -- upper steady state by the IVT on `[ks, k̄]`
  have hgk : e.psiDebt d e.kbar - e.kbar ≤ 0 := by
    linarith [e.psiDebt_lt_psi e.kbar_pos hd, e.psi_kbar]
  obtain ⟨u, ⟨hu1, hu2⟩, hu⟩ := intermediate_value_Icc' hks_kbar.le
    (hcont.mono fun k hk => hks.trans_le hk.1) ⟨hgk, by linarith⟩
  have hu' : e.psiDebt d u = u := by simp only at hu; linarith
  have hksu : ks < u := lt_of_le_of_ne hu1 (fun h => by rw [← h] at hu'; linarith)
  -- a point near zero with `Ψ(ε, d̄) < ε`
  have hD : 0 < (1 + e.n) * (1 + e.β) := mul_pos (by linarith) (by linarith)
  set Bc := e.β * e.x * e.α * d / ((1 + e.n) * (1 + e.β)) with hBc
  have hBpos : 0 < Bc := div_pos (by positivity) hD
  set M := (e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) +
    |e.β * e.x * e.n * d / ((1 + e.n) * (1 + e.β)) - e.x * d|) / Bc with hM
  have hev : ∀ᶠ k in 𝓝[>] (0 : ℝ), M < k ^ (e.α - 1) ∧ k ∈ Ioo 0 (min 1 ks) :=
    ((tendsto_rpow_neg_nhdsGT_zero (by linarith)).eventually_gt_atTop M).and
      (Ioo_mem_nhdsGT (lt_min one_pos hks))
  obtain ⟨ε, hεM, hε0, hε1⟩ := hev.exists
  have hε1' : ε < 1 := hε1.trans_le (min_le_left _ _)
  have hεks : ε < ks := hε1.trans_le (min_le_right _ _)
  have hgε : e.psiDebt d ε - ε ≤ 0 := by
    have hform : e.psiDebt d ε = e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * ε ^ e.α
        - Bc * ε ^ (e.α - 1) +
        (e.β * e.x * e.n * d / ((1 + e.n) * (1 + e.β)) - e.x * d) := by
      rw [hBc]; unfold psiDebt; ring
    have hpow : ε ^ e.α ≤ 1 := Real.rpow_le_one hε0.le hε1'.le e.α_pos.le
    have hA : 0 < e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) :=
      div_pos (mul_pos e.β_pos (by linarith)) hD
    have hMB : M * Bc = e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) +
        |e.β * e.x * e.n * d / ((1 + e.n) * (1 + e.β)) - e.x * d| := by
      rw [hM]; field_simp
    have h1 : M * Bc < ε ^ (e.α - 1) * Bc := mul_lt_mul_of_pos_right hεM hBpos
    have h2 := le_abs_self (e.β * e.x * e.n * d / ((1 + e.n) * (1 + e.β)) - e.x * d)
    have h3 : e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * ε ^ e.α ≤
        e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) := by
      nlinarith
    rw [hform]
    nlinarith
  obtain ⟨l, ⟨hl1, hl2⟩, hl⟩ := intermediate_value_Icc hεks.le
    (hcont.mono fun k hk => hε0.trans_le hk.1) ⟨hgε, by linarith⟩
  have hl' : e.psiDebt d l = l := by simp only at hl; linarith
  have hlks : l < ks := lt_of_le_of_ne hl2 (fun h => by rw [h] at hl'; linarith)
  have hl0 : 0 < l := hε0.trans_le hl1
  refine ⟨l, u, hl0, hlks, hksu, hu2, hl', hu', hl0.trans (hlks.trans hksu), hu', ?_⟩
  exact (e.steady_state_pattern hd.le hl0 (hlks.trans hksu) hl' hu').2.2

/-- Non-existence for large debt (a threshold O&R p. 171 omits): if
`x d̄ (1 + n + β)/((1+n)(1+β)) ≥ k̄` then `Ψ(k, d̄) < k` for every `k > 0`, so there is no
positive steady state and world capital cannot be sustained. -/
theorem no_steady_state_of_large_debt {d : ℝ} (hd : 0 < d)
    (hbig : e.kbar ≤ e.x * d * ((1 + e.n + e.β) / ((1 + e.n) * (1 + e.β)))) {k : ℝ}
    (hk : 0 < k) : e.psiDebt d k < k := by
  have := e.β_pos; have := e.n_gt; have := e.x_pos
  have hD : 0 < (1 + e.n) * (1 + e.β) := mul_pos (by linarith) (by linarith)
  have hr : 0 < e.rate k := mul_pos e.α_pos (Real.rpow_pos_of_pos hk _)
  have h1 : (1 + e.n) ≠ 0 := by linarith
  have h2 : (1 + e.β) ≠ 0 := by linarith
  have hsplit : 1 + e.β * (e.rate k - e.n) / ((1 + e.n) * (1 + e.β)) =
      (1 + e.n + e.β) / ((1 + e.n) * (1 + e.β)) +
        e.β * e.rate k / ((1 + e.n) * (1 + e.β)) := by
    field_simp; ring
  have hpos : 0 < e.x * d * (e.β * e.rate k / ((1 + e.n) * (1 + e.β))) :=
    mul_pos (mul_pos e.x_pos hd) (div_pos (mul_pos e.β_pos hr) hD)
  rw [psiDebt_eq, hsplit, mul_add]
  linarith [e.psi_le_add_kbar hk]

/-- Crowding out, O&R p. 171: raising Home debt from `d_1` to `d_2` pushes every positive
steady state `u_2` of `Ψ(·, d_2)` strictly below the upper steady state `u_1` of
`Ψ(·, d_1)`; world capital falls in BOTH countries since `k = k* = k^W` (O&R (3.50)). -/
theorem crowding_out {d1 d2 u1 u2 : ℝ} (hd : d1 < d2) (hu1 : e.IsUpperSteadyState d1 u1)
    (hu2 : 0 < u2) (hfu2 : e.psiDebt d2 u2 = u2) : u2 < u1 := by
  have hlt := e.psiDebt_strictAnti_debt hu2 hd
  rw [hfu2] at hlt
  by_contra h
  push Not at h
  rcases h.lt_or_eq with h' | h'
  · linarith [hu1.2.2 u2 h']
  · rw [← h', hu1.2.1] at hlt; exact lt_irrefl _ hlt

/-- Debt lowers capital below the debt-free level (O&R p. 171): with `d̄ > 0` every positive
steady state lies strictly below `k̄`. -/
theorem steady_state_lt_kbar {d u : ℝ} (hd : 0 < d) (hu : 0 < u)
    (hfu : e.psiDebt d u = u) : u < e.kbar :=
  e.crowding_out hd e.kbar_isUpper hu hfu

/-- The world interest rate rises with debt, O&R p. 171: under the hypotheses of
`crowding_out`, `α u_1^{α-1} < α u_2^{α-1}`. -/
theorem rate_rises {d1 d2 u1 u2 : ℝ} (hd : d1 < d2) (hu1 : e.IsUpperSteadyState d1 u1)
    (hu2 : 0 < u2) (hfu2 : e.psiDebt d2 u2 = u2) : e.rate u1 < e.rate u2 :=
  mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg hu2 (e.crowding_out hd hu1 hu2 hfu2)
    (by linarith [e.α_lt_one])) e.α_pos

/-! ## Dynamic inefficiency (O&R §3.6.4) -/

/-- O&R §3.6.4, p. 171: for `n ≥ 0`, `β > 0`, `0 < α < 1`, the steady-state rate of (3.53)
satisfies `r̄ ≤ n` exactly when `α ≤ nβ/((1+n)(1+β) + nβ)`. -/
theorem rbar_le_n_iff {α β n : ℝ} (hα1 : α < 1) (hβ : 0 < β) (hn : 0 ≤ n) :
    rbarOf α β n ≤ n ↔ α ≤ n * β / ((1 + n) * (1 + β) + n * β) := by
  have hden : 0 < β * (1 - α) := mul_pos hβ (by linarith)
  have hden2 : 0 < (1 + n) * (1 + β) + n * β := by positivity
  unfold rbarOf
  rw [div_le_iff₀ hden, le_div_iff₀ hden2]
  constructor <;> intro h <;> nlinarith

/-- O&R §3.6.4, p. 171: `r̄ ≤ n` is possible — for every `n > 0` and `β > 0` some capital
share `α ∈ (0,1)` gives `r̄ ≤ n`. -/
theorem exists_alpha_rbar_le_n {β n : ℝ} (hβ : 0 < β) (hn : 0 < n) :
    ∃ α, 0 < α ∧ α < 1 ∧ rbarOf α β n ≤ n := by
  have hden2 : 0 < (1 + n) * (1 + β) + n * β := by positivity
  refine ⟨n * β / ((1 + n) * (1 + β) + n * β), by positivity, ?_, ?_⟩
  · rw [div_lt_one hden2]; nlinarith
  · have h1 : n * β / ((1 + n) * (1 + β) + n * β) < 1 := by
      rw [div_lt_one hden2]; nlinarith
    exact (rbar_le_n_iff h1 hβ hn.le).2 le_rfl

/-- O&R §3.6.4, p. 171: `r̄ → 0` as `α → 0⁺` ("making `α` sufficiently small"). -/
theorem rbar_tendsto_zero {β n : ℝ} (hβ : 0 < β) :
    Tendsto (fun α => rbarOf α β n) (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt (fun α => rbarOf α β n) 0 := by
    unfold rbarOf
    exact ((continuousAt_id.mul continuousAt_const).mul continuousAt_const).div
      (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)) (by simp [hβ.ne'])
  have h0 : rbarOf 0 β n = 0 := by simp [rbarOf]
  have ht := hc.tendsto
  rw [h0] at ht
  exact tendsto_nhdsWithin_of_tendsto_nhds ht

/-- O&R §3.6.4, p. 171 with (3.54): if `r ≤ n` then the tax needed to hold debt per worker at
`d̄ ≥ 0` is non-positive, `τ = (r - n)d̄ ≤ 0`. -/
theorem tax_nonpos_of_rate_le {r n d : ℝ} (hr : r ≤ n) (hd : 0 ≤ d) : (r - n) * d ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (by linarith) hd

/-! ## Exercise 4: the untaxed Foreign young (O&R p. 197) -/

/-- Steady-state lifetime utility of a Foreign young agent (untaxed) at world capital `k`,
O&R Exercise 4, p. 197, with log preferences (3.9): `log c^Y + β log c^O`,
`c^Y = w/(1+β)`, `c^O = (1+r)βw/(1+β)`, `w = (1-α)k^α`, `r = αk^{α-1}`. -/
noncomputable def foreignUtility (k : ℝ) : ℝ :=
  Real.log ((1 - e.α) * k ^ e.α / (1 + e.β)) +
    e.β * Real.log ((1 + e.α * k ^ (e.α - 1)) * e.β * ((1 - e.α) * k ^ e.α) / (1 + e.β))

/-- O&R Exercise 4, p. 197: the marginal effect of world capital on Foreign steady-state
welfare, `dV/dk = [α(1+β) - β(1-α) r/(1+r)]/k` with `r = αk^{α-1}` — wage gain versus the
loss of interest income. -/
theorem foreignUtility_hasDerivAt {k : ℝ} (hk : 0 < k) :
    HasDerivAt e.foreignUtility
      ((e.α * (1 + e.β) - e.β * (1 - e.α) * (e.rate k / (1 + e.rate k))) / k) k := by
  have := e.β_pos; have := e.α_lt_one; have := e.α_pos
  have h1 := Real.hasDerivAt_rpow_const (p := e.α) (Or.inl hk.ne')
  have h2 := Real.hasDerivAt_rpow_const (p := e.α - 1) (Or.inl hk.ne')
  have hP : 0 < k ^ e.α := Real.rpow_pos_of_pos hk _
  have hQ : 0 < k ^ (e.α - 1) := Real.rpow_pos_of_pos hk _
  have hw := (h1.const_mul (1 - e.α)).div_const (1 + e.β)
  have hR := ((((h2.const_mul e.α).const_add 1).mul_const e.β).mul
    (h1.const_mul (1 - e.α))).div_const (1 + e.β)
  have hne1 : (1 - e.α) * k ^ e.α / (1 + e.β) ≠ 0 := by
    have : 0 < (1 - e.α) * k ^ e.α / (1 + e.β) := div_pos (mul_pos (by linarith) hP)
      (by linarith)
    exact this.ne'
  have hne2 : (1 + e.α * k ^ (e.α - 1)) * e.β * ((1 - e.α) * k ^ e.α) / (1 + e.β) ≠ 0 := by
    have : 0 < (1 + e.α * k ^ (e.α - 1)) * e.β * ((1 - e.α) * k ^ e.α) / (1 + e.β) := by
      apply div_pos _ (by linarith)
      exact mul_pos (mul_pos (by nlinarith) e.β_pos) (mul_pos (by linarith) hP)
    exact this.ne'
  have h := (hw.log hne1).add ((hR.log hne2).const_mul e.β)
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  unfold rate
  rw [Real.rpow_sub_one hk.ne' (e.α - 1), Real.rpow_sub_one hk.ne' e.α]
  have hk' : k ≠ 0 := hk.ne'
  have hP' : k ^ e.α ≠ 0 := hP.ne'
  have h1a : 1 - e.α ≠ 0 := by linarith
  have h1b : 1 + e.β ≠ 0 := by linarith
  have h1c : k + e.α * k ^ e.α ≠ 0 := by nlinarith
  have h1d : 1 + e.α * (k ^ e.α / k) ≠ 0 := by
    rw [show 1 + e.α * (k ^ e.α / k) = (k + e.α * k ^ e.α) / k by field_simp]
    exact div_ne_zero h1c hk'
  field_simp
  ring

/-- O&R Exercise 4, p. 197: Foreign steady-state welfare rises with world capital at `k`
exactly when `β(1-α) r < α(1+β)(1+r)`, `r = αk^{α-1}`. -/
theorem foreignUtility_deriv_pos_iff {k : ℝ} (hk : 0 < k) :
    0 < deriv e.foreignUtility k ↔
      e.β * (1 - e.α) * e.rate k < e.α * (1 + e.β) * (1 + e.rate k) := by
  have hr : 0 < e.rate k := mul_pos e.α_pos (Real.rpow_pos_of_pos hk _)
  rw [(e.foreignUtility_hasDerivAt hk).deriv, div_pos_iff_of_pos_right hk, sub_pos,
    mul_div_assoc', div_lt_iff₀ (by linarith)]

/-- O&R Exercise 4, p. 197 (the answer can be yes): Foreign steady-state welfare FALLS with
world capital at `k`, so a debt-induced fall in `k` benefits Foreign generations, exactly when
`α(1+β)(1+r) < β(1-α) r` — possible when `α` is small and `r = αk^{α-1}` is high. -/
theorem foreignUtility_deriv_neg_iff {k : ℝ} (hk : 0 < k) :
    deriv e.foreignUtility k < 0 ↔
      e.α * (1 + e.β) * (1 + e.rate k) < e.β * (1 - e.α) * e.rate k := by
  have hr : 0 < e.rate k := mul_pos e.α_pos (Real.rpow_pos_of_pos hk _)
  rw [(e.foreignUtility_hasDerivAt hk).deriv, div_neg_iff, sub_neg, mul_div_assoc',
    lt_div_iff₀ (by linarith)]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact absurd h (not_lt.2 hk.le)
    · exact h
  · intro h; exact Or.inr ⟨h, hk⟩

/-- O&R Exercise 4, p. 197: if `α(1+β) ≥ β(1-α)` then Foreign steady-state welfare is strictly
increasing in world capital on `(0, ∞)`. -/
theorem foreignUtility_strictMonoOn (hαβ : e.β * (1 - e.α) ≤ e.α * (1 + e.β)) :
    StrictMonoOn e.foreignUtility (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun k hk => (e.foreignUtility_hasDerivAt hk).continuousAt.continuousWithinAt)
    fun k hk => ?_
  rw [interior_Ioi] at hk
  have hk : 0 < k := hk
  have hr : 0 < e.rate k := mul_pos e.α_pos (Real.rpow_pos_of_pos hk _)
  have hb : 0 < e.β * (1 - e.α) := mul_pos e.β_pos (by linarith [e.α_lt_one])
  rw [e.foreignUtility_deriv_pos_iff hk]
  nlinarith

/-- O&R Exercise 4, p. 197 (a precise answer for Foreign): when `α(1+β) ≥ β(1-α)`, raising
Home debt from `d_1` to `d_2` strictly lowers the steady-state lifetime utility of every
Foreign generation (compare an upper steady state `u_1` with any positive steady state
`u_2` under the higher debt). -/
theorem foreign_welfare_falls_with_debt (hαβ : e.β * (1 - e.α) ≤ e.α * (1 + e.β))
    {d1 d2 u1 u2 : ℝ} (hd : d1 < d2) (hu1 : e.IsUpperSteadyState d1 u1) (hu2 : 0 < u2)
    (hfu2 : e.psiDebt d2 u2 = u2) : e.foreignUtility u2 < e.foreignUtility u1 :=
  e.foreignUtility_strictMonoOn hαβ (mem_Ioi.2 hu2) (mem_Ioi.2 hu1.1)
    (e.crowding_out hd hu1 hu2 hfu2)

end TwoCountry

end ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG
