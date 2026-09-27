/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SmallOpenEconomyDynamics.PresentValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Optimal consumption over an infinite horizon

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§2.1, pp. 60–73, and Supplement A.1, pp. 715–718. A consumer with time-separable
utility `Σ β^s u(C_s)` (O&R (2.11), p. 63) chooses a consumption path whose present
value does not exceed lifetime wealth `W`. Investment and government spending
are netted out of `W`, as the intertemporal budget constraint (2.14) allows.

The book assumes an optimum exists (p. 63) and reads off the Euler equation
(2.5). We prove:
* **sufficiency** (`isOptimal_of_euler`): if `u` is concave, a positive path that
  satisfies the Euler equation `u'(C_s) = (1 + r) β u'(C_{s+1})` and exhausts wealth
  is optimal among all admissible paths. Iterating the Euler equation gives
  `β^s u'(C_s) = u'(C_0)(1 + r)^{-s}`, so the gain from any deviation is bounded by
  `u'(C_0)` times its present-value cost;
* **strict optimality** when `u` is strictly concave: any other admissible path is
  strictly worse, so the optimum is unique;
* **necessity**: at an optimum the budget constraint binds
  (`pv_eq_of_optimal`, the book's transversality property) and the Euler equation
  holds (`euler_of_optimal`, by moving consumption between adjacent dates);
* **the consumption tilt** (p. 71): consumption rises, stays flat or falls as
  `β(1 + r)` is above, equal to or below one;
* **dynamic consistency** (§2.1.4, p. 72): the continuation of an optimal plan is
  optimal given the wealth it leaves;
* **Strotz** (p. 73): with the quasi-hyperbolic weight `(1 + γ)` on current utility,
  the marginal rate of substitution between two future dates changes once the
  first of them arrives.

Admissible paths are positive, have a summable present value and summable
lifetime utility: the explicit counterpart of the book's convergence assumption.
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality

open PresentValue Filter Topology Set Finset

/-- The tangent line of a concave function lies weakly above its graph (copied from the
`IntertemporalTrade` project so that this project builds on its own). -/
theorem concave_le_tangent' {f : ℝ → ℝ} {S : Set ℝ} (hf : ConcaveOn ℝ S f) {x y d : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f d x) : f y ≤ f x + d * (y - x) := by
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · have h := hf.le_slope_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    linarith
  · simp
  · have h := hf.slope_le_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    linarith

/-- The strict tangent inequality for a strictly concave function. -/
theorem strictConcave_lt_tangent {f : ℝ → ℝ} {S : Set ℝ} (hf : StrictConcaveOn ℝ S f)
    {x y d : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hxy : y ≠ x) (hd : HasDerivAt f d x) :
    f y < f x + d * (y - x) := by
  rcases lt_or_gt_of_ne hxy with hyx | hxy
  · have h := hf.lt_slope_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field, lt_div_iff₀ (by linarith)] at h
    linarith
  · have h := hf.slope_lt_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field, div_lt_iff₀ (by linarith)] at h
    linarith

/-- Lifetime utility `Σ_{s≥0} β^s u(C_s)`, O&R (2.11), p. 63. -/
noncomputable def lifetimeUtility (u : ℝ → ℝ) (β : ℝ) (C : ℕ → ℝ) : ℝ := ∑' s, β ^ s * u (C s)

/-- An admissible consumption path at interest rate `r` and wealth `W`: positive, with summable
present value and lifetime utility, and present value at most `W` (O&R (2.14)). -/
def Admissible (u : ℝ → ℝ) (β r W : ℝ) (C : ℕ → ℝ) : Prop :=
  (∀ s, 0 < C s) ∧ Summable (fun s => disc r ^ s * C s) ∧
    Summable (fun s => β ^ s * u (C s)) ∧ pv r C ≤ W

/-- An optimal path: admissible and at least as good as every admissible path. -/
def IsOptimal (u : ℝ → ℝ) (β r W : ℝ) (C : ℕ → ℝ) : Prop :=
  Admissible u β r W C ∧ ∀ D, Admissible u β r W D → lifetimeUtility u β D ≤ lifetimeUtility u β C

/-- **Iterated Euler equation**, Supplement A (SA(3)), p. 717: if `u'(C_s) = (1 + r) β u'(C_{s+1})`
for all `s`, then `(β(1 + r))^s u'(C_s) = u'(C_0)`. -/
theorem euler_iterate {u' : ℝ → ℝ} {β r : ℝ} {C : ℕ → ℝ}
    (he : ∀ s, u' (C s) = (1 + r) * β * u' (C (s + 1))) (s : ℕ) :
    (β * (1 + r)) ^ s * u' (C s) = u' (C 0) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [← ih, he s, pow_succ]
    ring

/-- The discounted marginal utility equals `u'(C₀)` times the market discount factor:
`β^s u'(C_s) = u'(C₀)(1 + r)^{-s}` (Supplement A, p. 717). -/
theorem discounted_marginal_utility {u' : ℝ → ℝ} {β r : ℝ} (hr : 0 < 1 + r) {C : ℕ → ℝ}
    (he : ∀ s, u' (C s) = (1 + r) * β * u' (C (s + 1))) (s : ℕ) :
    β ^ s * u' (C s) = u' (C 0) * disc r ^ s := by
  have h := euler_iterate he s
  rw [mul_pow] at h
  have hd : (1 + r) ^ s * disc r ^ s = 1 := by rw [← mul_pow, one_add_mul_disc hr, one_pow]
  calc β ^ s * u' (C s) = β ^ s * (1 + r) ^ s * u' (C s) * disc r ^ s := by
        linear_combination (-(β ^ s * u' (C s))) * hd
    _ = u' (C 0) * disc r ^ s := by rw [h]

/-- A finite modification of a summable sequence: if `g` agrees with `f` off a finite set `S`,
then `g` is summable and `Σ g = Σ f + Σ_{t∈S} (g t − f t)`. -/
theorem tsum_eq_add_of_eqOn_compl {f g : ℕ → ℝ} (hf : Summable f) (S : Finset ℕ)
    (hfg : ∀ t, t ∉ S → g t = f t) :
    Summable g ∧ ∑' t, g t = ∑' t, f t + ∑ t ∈ S, (g t - f t) := by
  have hd : Summable fun t => g t - f t :=
    summable_of_ne_finset_zero (s := S) fun t ht => by rw [hfg t ht, sub_self]
  have hg : g = fun t => f t + (g t - f t) := by funext t; ring
  refine ⟨hg ▸ hf.add hd, ?_⟩
  have h1 : ∑' t, (g t - f t) = ∑ t ∈ S, (g t - f t) :=
    tsum_eq_sum (f := fun t => g t - f t) (s := S) fun t ht => by rw [hfg t ht, sub_self]
  calc ∑' t, g t = ∑' t, (f t + (g t - f t)) := tsum_congr fun t => by ring
    _ = _ := by rw [hf.tsum_add hd, h1]

/-- **Sufficiency of the Euler equation**, O&R pp. 62–65 and Supplement A: with `u` concave and
differentiable and `β > 0`, a positive path satisfying the Euler equation and exhausting wealth,
`PV(C) = W`, is optimal. The proof bounds the utility gain of any admissible `D` by
`u'(C₀)(PV(D) − PV(C)) ≤ 0`. -/
theorem isOptimal_of_euler {u u' : ℝ → ℝ} {β r W : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    (hconc : ConcaveOn ℝ (Ioi 0) u) (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    {C : ℕ → ℝ} (hC : Admissible u β r W C) (hbind : pv r C = W) (hpos : 0 ≤ u' (C 0))
    (he : ∀ s, u' (C s) = (1 + r) * β * u' (C (s + 1))) :
    IsOptimal u β r W C := by
  refine ⟨hC, fun D hD => ?_⟩
  obtain ⟨hCpos, hCpv, hCu, -⟩ := hC
  obtain ⟨hDpos, hDpv, hDu, hDW⟩ := hD
  have hterm : ∀ s, β ^ s * u (D s) ≤
      β ^ s * u (C s) + u' (C 0) * (disc r ^ s * D s - disc r ^ s * C s) := by
    intro s
    have t := concave_le_tangent' hconc (mem_Ioi.2 (hCpos s)) (mem_Ioi.2 (hDpos s))
      (hu _ (hCpos s))
    have key : β ^ s * (u' (C s) * (D s - C s)) =
        u' (C 0) * (disc r ^ s * D s - disc r ^ s * C s) := by
      rw [← mul_assoc, discounted_marginal_utility hr he s]
      ring
    have := mul_le_mul_of_nonneg_left t (pow_nonneg hβ.le s)
    linarith
  have hsum : Summable fun s => β ^ s * u (C s) + u' (C 0) *
      (disc r ^ s * D s - disc r ^ s * C s) := hCu.add ((hDpv.sub hCpv).mul_left _)
  have hle := hDu.tsum_le_tsum hterm hsum
  rw [hCu.tsum_add ((hDpv.sub hCpv).mul_left _), tsum_mul_left, hDpv.tsum_sub hCpv] at hle
  unfold lifetimeUtility
  have hpvD : ∑' s, disc r ^ s * D s ≤ ∑' s, disc r ^ s * C s := by
    have := hDW
    unfold pv at this hbind
    linarith
  nlinarith

/-- **Strict optimality and uniqueness**: with `u` strictly concave, every admissible path other
than the Euler path is strictly worse. -/
theorem lifetimeUtility_lt_of_euler {u u' : ℝ → ℝ} {β r W : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    (hconc : StrictConcaveOn ℝ (Ioi 0) u) (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    {C : ℕ → ℝ} (hC : Admissible u β r W C) (hbind : pv r C = W) (hpos : 0 ≤ u' (C 0))
    (he : ∀ s, u' (C s) = (1 + r) * β * u' (C (s + 1))) {D : ℕ → ℝ}
    (hD : Admissible u β r W D) (hne : D ≠ C) :
    lifetimeUtility u β D < lifetimeUtility u β C := by
  obtain ⟨hCpos, hCpv, hCu, -⟩ := hC
  obtain ⟨hDpos, hDpv, hDu, hDW⟩ := hD
  obtain ⟨k, hk⟩ : ∃ k, D k ≠ C k := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have key : ∀ s, β ^ s * (u' (C s) * (D s - C s)) =
      u' (C 0) * (disc r ^ s * D s - disc r ^ s * C s) := fun s => by
    rw [← mul_assoc, discounted_marginal_utility hr he s]
    ring
  have hterm : ∀ s, β ^ s * u (D s) ≤
      β ^ s * u (C s) + u' (C 0) * (disc r ^ s * D s - disc r ^ s * C s) := by
    intro s
    have t := concave_le_tangent' hconc.concaveOn (mem_Ioi.2 (hCpos s)) (mem_Ioi.2 (hDpos s))
      (hu _ (hCpos s))
    have := mul_le_mul_of_nonneg_left t (pow_nonneg hβ.le s)
    linarith [key s]
  have hstrict : β ^ k * u (D k) <
      β ^ k * u (C k) + u' (C 0) * (disc r ^ k * D k - disc r ^ k * C k) := by
    have t := strictConcave_lt_tangent hconc (mem_Ioi.2 (hCpos k)) (mem_Ioi.2 (hDpos k)) hk
      (hu _ (hCpos k))
    have := mul_lt_mul_of_pos_left t (pow_pos hβ k)
    linarith [key k]
  have hsum : Summable fun s => β ^ s * u (C s) + u' (C 0) *
      (disc r ^ s * D s - disc r ^ s * C s) := hCu.add ((hDpv.sub hCpv).mul_left _)
  have hlt := hDu.tsum_lt_tsum hterm hstrict hsum
  rw [hCu.tsum_add ((hDpv.sub hCpv).mul_left _), tsum_mul_left, hDpv.tsum_sub hCpv] at hlt
  unfold lifetimeUtility
  have hpvD : ∑' s, disc r ^ s * D s ≤ ∑' s, disc r ^ s * C s := by
    have := hDW
    unfold pv at this hbind
    linarith
  nlinarith

/-- **The budget constraint binds at an optimum** (O&R pp. 64–65, footnote 4; Supplement A,
SA(4)): with `u` strictly increasing and `β > 0`, an optimal path exhausts wealth. -/
theorem pv_eq_of_optimal {u : ℝ → ℝ} {β r W : ℝ}
    (hmono : StrictMonoOn u (Ioi 0)) {C : ℕ → ℝ} (hC : IsOptimal u β r W C) :
    pv r C = W := by
  obtain ⟨⟨hCpos, hCpv, hCu, hCW⟩, hmax⟩ := hC
  by_contra hne
  have hlt : pv r C < W := lt_of_le_of_ne hCW hne
  set δ := W - pv r C with hδ
  have hδpos : 0 < δ := by linarith
  set D : ℕ → ℝ := fun s => if s = 0 then C 0 + δ else C s with hD
  have hoff : ∀ t, t ∉ ({0} : Finset ℕ) → D t = C t := fun t ht => by
    simp only [Finset.mem_singleton] at ht
    simp [hD, ht]
  obtain ⟨hDpv, hDpv_eq⟩ := tsum_eq_add_of_eqOn_compl hCpv {0}
    (g := fun t => disc r ^ t * D t) fun t ht => by simp only [hoff t ht]
  obtain ⟨hDu, hDu_eq⟩ := tsum_eq_add_of_eqOn_compl hCu {0}
    (g := fun t => β ^ t * u (D t)) fun t ht => by simp only [hoff t ht]
  have hDpos : ∀ s, 0 < D s := fun s => by
    by_cases hs : s = 0
    · simp only [hD, hs]; simp only [↓reduceIte]; linarith [hCpos 0]
    · simp only [hD, hs]; simp only [↓reduceIte]; exact hCpos s
  have hDW : pv r D ≤ W := by
    unfold pv
    rw [hDpv_eq]
    simp [hD]
    unfold pv at hδ
    linarith
  have hgain := hmax D ⟨hDpos, hDpv, hDu, hDW⟩
  unfold lifetimeUtility at hgain
  rw [hDu_eq] at hgain
  have hu0 : u (C 0) < u (C 0 + δ) :=
    hmono (mem_Ioi.2 (hCpos 0)) (mem_Ioi.2 (by linarith [hCpos 0])) (by linarith)
  simp [hD] at hgain
  linarith

/-- **Euler equation**, O&R (2.5), p. 61: at an optimum with differentiable `u`,
`u'(C_s) = (1 + r) β u'(C_{s+1})` for every `s`. The proof moves `ε` of consumption from date
`s` to date `s + 1`, which leaves the present value unchanged. -/
theorem euler_of_optimal {u u' : ℝ → ℝ} {β r W : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) {C : ℕ → ℝ} (hC : IsOptimal u β r W C)
    (s : ℕ) : u' (C s) = (1 + r) * β * u' (C (s + 1)) := by
  obtain ⟨⟨hCpos, hCpv, hCu, hCW⟩, hmax⟩ := hC
  -- the perturbed path
  let D : ℝ → ℕ → ℝ := fun ε t =>
    if t = s then C s - ε else if t = s + 1 then C (s + 1) + (1 + r) * ε else C t
  have hoff : ∀ ε t, t ∉ ({s, s + 1} : Finset ℕ) → D ε t = C t := fun ε t ht => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    simp [D, ht.1, ht.2]
  have hne : s + 1 ≠ s := Nat.succ_ne_self s
  have hDs : ∀ ε, D ε s = C s - ε := fun ε => by simp [D]
  have hDs1 : ∀ ε, D ε (s + 1) = C (s + 1) + (1 + r) * ε := fun ε => by simp [D]
  -- present value is unchanged
  have hpvD : ∀ ε, Summable (fun t => disc r ^ t * D ε t) ∧ pv r (D ε) = pv r C := by
    intro ε
    obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hCpv {s, s + 1}
      (g := fun t => disc r ^ t * D ε t) fun t ht => by simp only [hoff ε t ht]
    refine ⟨h1, ?_⟩
    unfold pv
    rw [h2, Finset.sum_pair hne.symm, hDs, hDs1, pow_succ]
    have := one_add_mul_disc hr
    linear_combination (disc r ^ s * ε) * this
  -- utility changes only at s and s + 1
  have huD : ∀ ε, Summable (fun t => β ^ t * u (D ε t)) ∧ lifetimeUtility u β (D ε) =
      lifetimeUtility u β C + (β ^ s * u (C s - ε) - β ^ s * u (C s)) +
        (β ^ (s + 1) * u (C (s + 1) + (1 + r) * ε) - β ^ (s + 1) * u (C (s + 1))) := by
    intro ε
    obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hCu {s, s + 1}
      (g := fun t => β ^ t * u (D ε t)) fun t ht => by simp only [hoff ε t ht]
    refine ⟨h1, ?_⟩
    unfold lifetimeUtility
    rw [h2, Finset.sum_pair hne.symm, hDs, hDs1]
    ring
  -- for small ε the perturbed path is positive, hence admissible
  have hcont1 : Continuous fun ε : ℝ => C s - ε := by fun_prop
  have hcont2 : Continuous fun ε : ℝ => C (s + 1) + (1 + r) * ε := by fun_prop
  have hev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C s - ε :=
    (hcont1.tendsto 0).eventually (lt_mem_nhds (by simpa using hCpos s))
  have hev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C (s + 1) + (1 + r) * ε :=
    (hcont2.tendsto 0).eventually (lt_mem_nhds (by simpa using hCpos (s + 1)))
  set φ : ℝ → ℝ := fun ε => β ^ s * u (C s - ε) + β ^ (s + 1) * u (C (s + 1) + (1 + r) * ε)
  have hloc : IsLocalMax φ 0 := by
    filter_upwards [hev1, hev2] with ε h1 h2
    have hpos : ∀ t, 0 < D ε t := fun t => by
      by_cases ht : t = s
      · rw [ht, hDs]; exact h1
      by_cases ht1 : t = s + 1
      · rw [ht1, hDs1]; exact h2
      rw [hoff ε t (by simp [ht, ht1])]
      exact hCpos t
    have hadm : Admissible u β r W (D ε) :=
      ⟨hpos, (hpvD ε).1, (huD ε).1, by rw [(hpvD ε).2]; exact hCW⟩
    have := hmax _ hadm
    rw [(huD ε).2] at this
    simp only [φ, sub_zero, mul_zero, add_zero]
    linarith
  have hd1 : HasDerivAt (fun ε : ℝ => C s - ε) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub (C s)
  have hd2 : HasDerivAt (fun ε : ℝ => C (s + 1) + (1 + r) * ε) (1 + r) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 + r)).const_add (C (s + 1))
  have hA : HasDerivAt (fun ε => β ^ s * u (C s - ε)) (β ^ s * (u' (C s) * (-1))) 0 := by
    have h1 : HasDerivAt u (u' (C s)) ((fun ε : ℝ => C s - ε) 0) := by
      simpa using hu _ (hCpos s)
    exact (h1.comp (0 : ℝ) hd1).const_mul _
  have hB : HasDerivAt (fun ε => β ^ (s + 1) * u (C (s + 1) + (1 + r) * ε))
      (β ^ (s + 1) * (u' (C (s + 1)) * (1 + r))) 0 := by
    have h1 : HasDerivAt u (u' (C (s + 1))) ((fun ε : ℝ => C (s + 1) + (1 + r) * ε) 0) := by
      simpa using hu _ (hCpos (s + 1))
    exact (h1.comp (0 : ℝ) hd2).const_mul _
  have h0 := hloc.hasDerivAt_eq_zero (hA.add hB)
  rw [pow_succ] at h0
  have hβs : 0 < β ^ s := pow_pos hβ s
  have : β ^ s * (u' (C s) - (1 + r) * β * u' (C (s + 1))) = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_left hβs.ne'
  linarith

/-- The derivative of a strictly concave function is strictly decreasing (copied from the
`IntertemporalTrade` project). -/
theorem deriv_lt_of_strictConcave' {f : ℝ → ℝ} {S : Set ℝ} (hf : StrictConcaveOn ℝ S f)
    {x y dx dy : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hdx : HasDerivAt f dx x)
    (hdy : HasDerivAt f dy y) : dy < dx :=
  (hf.lt_slope_of_hasDerivAt hx hy hxy hdy).trans (hf.slope_lt_of_hasDerivAt hx hy hxy hdx)

/-- **Consumption tilts up** (O&R p. 71): if `β(1 + r) > 1` and `u' > 0`, a path satisfying the
Euler equation is strictly increasing. -/
theorem tilt_up {u u' : ℝ → ℝ} {β r : ℝ} (hconc : StrictConcaveOn ℝ (Ioi 0) u)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hβr : 1 < β * (1 + r)) {C : ℕ → ℝ} (hCpos : ∀ s, 0 < C s)
    (he : ∀ s, u' (C s) = (1 + r) * β * u' (C (s + 1))) (s : ℕ) : C s < C (s + 1) := by
  have hp := hpos _ (hCpos (s + 1))
  have hgt : u' (C (s + 1)) < u' (C s) := by rw [he s]; nlinarith
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · exact absurd hgt (deriv_lt_of_strictConcave' hconc (mem_Ioi.2 (hCpos _))
      (mem_Ioi.2 (hCpos _)) hlt (hu _ (hCpos _)) (hu _ (hCpos _))).not_gt
  · rw [heq] at hgt
    exact lt_irrefl _ hgt

/-- **Consumption tilts down** (O&R p. 71): if `β(1 + r) < 1`, a path satisfying the Euler equation
is strictly decreasing. -/
theorem tilt_down {u u' : ℝ → ℝ} {β r : ℝ} (hconc : StrictConcaveOn ℝ (Ioi 0) u)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hβr : β * (1 + r) < 1) {C : ℕ → ℝ} (hCpos : ∀ s, 0 < C s)
    (he : ∀ s, u' (C s) = (1 + r) * β * u' (C (s + 1))) (s : ℕ) : C (s + 1) < C s := by
  have hp := hpos _ (hCpos (s + 1))
  have hlt' : u' (C s) < u' (C (s + 1)) := by rw [he s]; nlinarith
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · exact absurd hlt' (deriv_lt_of_strictConcave' hconc (mem_Ioi.2 (hCpos _))
      (mem_Ioi.2 (hCpos _)) hlt (hu _ (hCpos _)) (hu _ (hCpos _))).not_gt
  · rw [heq] at hlt'
    exact lt_irrefl _ hlt'

/-- **Flat consumption** (O&R p. 62): if `β(1 + r) = 1`, a path satisfying the Euler equation is
constant. -/
theorem flat_of_beta_mul {u u' : ℝ → ℝ} {β r : ℝ} (hconc : StrictConcaveOn ℝ (Ioi 0) u)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hβr : β * (1 + r) = 1) {C : ℕ → ℝ}
    (hCpos : ∀ s, 0 < C s) (he : ∀ s, u' (C s) = (1 + r) * β * u' (C (s + 1))) (s : ℕ) :
    C s = C 0 := by
  have step : ∀ t, C (t + 1) = C t := by
    intro t
    have heq : u' (C t) = u' (C (t + 1)) := by
      rw [he t]; linear_combination u' (C (t + 1)) * hβr
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd heq (deriv_lt_of_strictConcave' hconc (mem_Ioi.2 (hCpos _))
        (mem_Ioi.2 (hCpos _)) hlt (hu _ (hCpos _)) (hu _ (hCpos _))).ne
    · exact absurd heq (deriv_lt_of_strictConcave' hconc (mem_Ioi.2 (hCpos _))
        (mem_Ioi.2 (hCpos _)) hlt (hu _ (hCpos _)) (hu _ (hCpos _))).ne'
  induction s with
  | zero => rfl
  | succ s ih => rw [step s, ih]

/-- **Dynamic consistency**, O&R §2.1.4, p. 72: the continuation of a date-0 optimal plan is optimal
at date 1 given the wealth it leaves, `W₁ = (1 + r)(W − C₀)` (Supplement A, SA(5)). -/
theorem continuation_optimal {u : ℝ → ℝ} {β r W : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    {C : ℕ → ℝ} (hC : IsOptimal u β r W C) :
    IsOptimal u β r ((1 + r) * (W - C 0)) (fun s => C (s + 1)) := by
  obtain ⟨⟨hCpos, hCpv, hCu, hCW⟩, hmax⟩ := hC
  have hd := one_add_mul_disc hr
  have hpv_tail : Summable fun s => disc r ^ s * C (s + 1) := by
    have := (summable_nat_add_iff 1).2 hCpv
    have h2 : Summable fun s => disc r * (disc r ^ s * C (s + 1)) := by
      simpa [pow_succ, mul_comm, mul_assoc, mul_left_comm] using this
    have h3 := h2.mul_left (1 + r)
    simpa [← mul_assoc, hd] using h3
  have hu_tail : Summable fun s => β ^ s * u (C (s + 1)) := by
    have := (summable_nat_add_iff 1).2 hCu
    have h2 : Summable fun s => β * (β ^ s * u (C (s + 1))) := by
      simpa [pow_succ, mul_comm, mul_assoc, mul_left_comm] using this
    have h3 := h2.mul_left β⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ hβ.ne'] using h3
  have hsplit_pv : pv r C = C 0 + disc r * pv r (fun s => C (s + 1)) := pv_eq_head_add hCpv
  have hsplit_u : lifetimeUtility u β C =
      u (C 0) + β * lifetimeUtility u β (fun s => C (s + 1)) := by
    unfold lifetimeUtility
    rw [hCu.tsum_eq_zero_add, ← tsum_mul_left]
    simp only [pow_zero, one_mul]
    congr 1
    exact tsum_congr fun s => by rw [pow_succ]; ring
  refine ⟨⟨fun s => hCpos (s + 1), hpv_tail, hu_tail, ?_⟩, fun D hD => ?_⟩
  · have : disc r * pv r (fun s => C (s + 1)) ≤ W - C 0 := by linarith
    have h1 := mul_le_mul_of_nonneg_left this hr.le
    rwa [← mul_assoc, hd, one_mul] at h1
  · obtain ⟨hDpos, hDpv, hDu, hDW⟩ := hD
    -- prepend C₀ to D
    set E : ℕ → ℝ := fun s => Nat.casesOn s (C 0) D with hE
    have hE0 : E 0 = C 0 := rfl
    have hEs : ∀ s, E (s + 1) = D s := fun s => rfl
    have hEpv : Summable fun s => disc r ^ s * E s := by
      rw [← summable_nat_add_iff 1]
      simpa [hEs, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hDpv.mul_left (disc r)
    have hEu : Summable fun s => β ^ s * u (E s) := by
      rw [← summable_nat_add_iff 1]
      simpa [hEs, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hDu.mul_left β
    have hEpos : ∀ s, 0 < E s := fun s => by
      cases s with
      | zero => exact hCpos 0
      | succ s => exact hDpos s
    have hEsplit : pv r E = C 0 + disc r * pv r D := by
      rw [pv_eq_head_add hEpv]
      rfl
    have hEW : pv r E ≤ W := by
      rw [hEsplit]
      have h1 := mul_le_mul_of_nonneg_left hDW (disc_pos hr).le
      have : disc r * ((1 + r) * (W - C 0)) = W - C 0 := by
        rw [← mul_assoc, mul_comm (disc r), hd, one_mul]
      linarith
    have hle := hmax E ⟨hEpos, hEpv, hEu, hEW⟩
    have hEsplit_u : lifetimeUtility u β E = u (C 0) + β * lifetimeUtility u β D := by
      unfold lifetimeUtility
      rw [hEu.tsum_eq_zero_add, ← tsum_mul_left]
      simp only [pow_zero, one_mul, hE0]
      congr 1
      exact tsum_congr fun s => by rw [pow_succ, hEs]; ring
    rw [hEsplit_u, hsplit_u] at hle
    have := (mul_le_mul_iff_of_pos_left hβ).1 (by linarith : β * lifetimeUtility u β D ≤
      β * lifetimeUtility u β (fun s => C (s + 1)))
    exact this

/-- **Strotz's time inconsistency**, O&R p. 73: with quasi-hyperbolic utility
`(1 + γ) u(C_t) + Σ_{s>t} β^{s−t} u(C_s)`, the marginal rate of substitution between dates 1 and 2
is `u'(C₁)/(β u'(C₂))` as seen from date 0 but `(1 + γ) u'(C₁)/(β u'(C₂))` once date 1 arrives. The
two differ whenever `γ ≠ 0`, so the date-0 plan is not carried out. -/
theorem strotz_mrs_differ {β γ du1 du2 : ℝ} (hβ : 0 < β) (h1 : 0 < du1) (h2 : 0 < du2)
    (hγ : γ ≠ 0) : β * du1 / (β ^ 2 * du2) ≠ (1 + γ) * du1 / (β * du2) := by
  intro heq
  have hβ2 : β * du1 / (β ^ 2 * du2) = du1 / (β * du2) := by
    field_simp
  rw [hβ2, eq_div_iff (by positivity), div_mul_cancel₀ _ (by positivity)] at heq
  have : γ * du1 = 0 := by linarith
  exact hγ ((mul_eq_zero.1 this).resolve_right h1.ne')

end ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionOptimality
