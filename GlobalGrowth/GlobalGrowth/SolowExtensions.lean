/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GlobalGrowth.SolowModel

/-!
# Extensions of the Solow model: human capital, credit-constrained open economies,
and the shape of transition dynamics

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§7.1.1.2 (pp. 437–439), fn 5 (p. 437), §7.2.2.1 (pp. 462–463, fn 24) and
§7.2.2.2 (pp. 464–467).

* The Mankiw–Romer–Weil human-capital model (13)–(17): the unique interior steady state,
  the estimating equation (with the typesetting error of p. 439 corrected), a new exact
  result (`s_K h - s_H k` contracts geometrically, so the ray `h = (s_H/s_K) k` is invariant)
  and **global convergence of the two-dimensional system from every positive initial
  condition**, by sandwiching between two orbits on the invariant ray.
* The Barro–Mankiw–Sala-i-Martin open economy (46)–(51): capital is pinned by the world
  rate, human capital follows a Solow equation with exponent `ν = φ/(1-α)`, with global
  convergence and the speed ordering stated on p. 467; the wealth identity shows that the
  p. 466 display `H' - H = s(Y - rK)` omits `- δH`.
* p. 462 corrected: the increment `Δk` is *not* larger when `k` is further below `k̄`
  (counterexample); the growth rate `Δk/k` is strictly decreasing everywhere.
* fn 5 interest-rate arithmetic and fn 24 (the log-deviation rate equals `μ`).
* The Solow model without `δ ≤ 1`: the steady state exists and is unique for every `δ`;
  capital can turn negative when `δ > 1`; `G'(k̄) < 1` always, so orbits near `k̄` converge iff
  (up to the boundary case) `G'(k̄) > -1`, and never converge when `G'(k̄) < -1`; a Lyapunov
  criterion for (possibly oscillating) global convergence; monotone convergence on `(0, b]`
  where the map is increasing, with an explicit Cobb–Douglas condition `δ - 1 ≤ α(z + δ)`.
-/

namespace ObstfeldRogoff.GlobalGrowth.SolowExtensions

open Set Filter Topology
open ObstfeldRogoff.GlobalGrowth.SolowModel

variable {f : ℝ → ℝ}

/-! ## Preliminaries -/

/-- A positive multiple of a neoclassical technology is neoclassical (used for the
reduced technologies of the MRW ray and of the BMS model, O&R pp. 439, 466). -/
theorem Neoclassical.const_mul (hf : Neoclassical f) {c : ℝ} (hc : 0 < c) :
    Neoclassical (fun k => c * f k) where
  cont := continuousOn_const.mul hf.cont
  zero := by simp [hf.zero]
  strictMono := fun _ ha _ hb hab => mul_lt_mul_of_pos_left (hf.strictMono ha hb hab) hc
  strictConcave := ⟨convex_Ici 0, fun x hx y hy hne a b ha hb hab => by
    have h := mul_lt_mul_of_pos_left (hf.strictConcave.2 hx hy hne ha hb hab) hc
    simp only [smul_eq_mul] at h ⊢
    linarith⟩
  diff := fun k hk => (hf.diff k hk).const_mul c

/-- **Global convergence of the Cobb–Douglas Solow model** (O&R (43), p. 462): from every
`k₀ > 0` the path of (43) converges monotonically to `k̄ = (s/(z+δ))^{1/(1-α)}`. -/
theorem cobbDouglas_global_convergence {α s δ z : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (P : SolowParams s δ z) {k : ℕ → ℝ} (h0 : 0 < k 0)
    (hrec : ∀ t, k (t + 1) = solowMap (fun k => k ^ α) s δ z (k t)) :
    Tendsto k atTop (𝓝 ((s / (z + δ)) ^ (1 / (1 - α)))) ∧ (Monotone k ∨ Antitone k) := by
  have hk := Real.rpow_pos_of_pos (div_pos P.saving_pos P.dilution_pos) (1 / (1 - α))
  have hss := cobbDouglas_steady hα1 P.saving_pos P.dilution_pos
  have h := (solow_monotoneMap (neoclassical_rpow hα hα1) P hk hss).orbit_tendsto hrec h0
  exact ⟨h.1, h.2.1⟩

/-! ## The Mankiw–Romer–Weil human-capital model (O&R pp. 438–439) -/

/-- Output per efficiency worker, eq. (13): `y = k^α h^φ`. -/
noncomputable def mrwOutput (α φ k h : ℝ) : ℝ := k ^ α * h ^ φ

/-- Physical-capital accumulation, eq. (15). -/
noncomputable def mrwK (α φ sK δ z k h : ℝ) : ℝ := ((1 - δ) * k + sK * mrwOutput α φ k h) / (1 + z)

/-- Human-capital accumulation, eq. (14). -/
noncomputable def mrwH (α φ sH δ z k h : ℝ) : ℝ := ((1 - δ) * h + sH * mrwOutput α φ k h) / (1 + z)

/-- Normalising `Y = K^α H^φ (EL)^{1-α-φ}` by `EL` gives eq. (13) (O&R p. 438). -/
theorem mrw_intensive {α φ K H N : ℝ} (hK : 0 < K) (hH : 0 < H) (hN : 0 < N) :
    K ^ α * H ^ φ * N ^ (1 - α - φ) / N = mrwOutput α φ (K / N) (H / N) := by
  unfold mrwOutput
  rw [Real.div_rpow hK.le hN.le, Real.div_rpow hH.le hN.le,
    show 1 - α - φ = 1 - (α + φ) by ring, Real.rpow_sub hN, Real.rpow_one, Real.rpow_add hN]
  field_simp

/-- Steady-state physical capital, eq. (16): `k̄ = [s_K^{1-φ} s_H^φ/(z+δ)]^{1/(1-α-φ)}`. -/
noncomputable def mrwSteadyK (α φ sK sH m : ℝ) : ℝ :=
  (sK ^ (1 - φ) * sH ^ φ / m) ^ (1 / (1 - α - φ))

/-- Steady-state human capital, eq. (17): `h̄ = [s_H^{1-α} s_K^α/(z+δ)]^{1/(1-α-φ)}`. -/
noncomputable def mrwSteadyH (α φ sK sH m : ℝ) : ℝ :=
  (sH ^ (1 - α) * sK ^ α / m) ^ (1 / (1 - α - φ))

/-- In the MRW steady state `h̄/k̄ = s_H/s_K` (from (16)–(17)). -/
theorem mrwSteadyH_eq {α φ sK sH m : ℝ} (hφα : α + φ < 1) (hK : 0 < sK) (hH : 0 < sH)
    (hm : 0 < m) : mrwSteadyH α φ sK sH m = sH / sK * mrwSteadyK α φ sK sH m := by
  unfold mrwSteadyH mrwSteadyK
  have he : 1 - α - φ ≠ 0 := by linarith
  have hA : 0 < sK ^ (1 - φ) * sH ^ φ / m := by positivity
  have hr : 0 < sH / sK := div_pos hH hK
  have hρ : sH / sK = ((sH / sK) ^ (1 - α - φ)) ^ (1 / (1 - α - φ)) := by
    rw [← Real.rpow_mul hr.le, mul_one_div_cancel he, Real.rpow_one]
  rw [hρ, ← Real.mul_rpow (by positivity) hA.le]
  congr 1
  rw [Real.div_rpow hH.le hK.le]
  have e1 : sH ^ (1 - α) = sH ^ (1 - α - φ) * sH ^ φ := by
    rw [← Real.rpow_add hH]; ring_nf
  have e2 : sK ^ (1 - φ) = sK ^ (1 - α - φ) * sK ^ α := by
    rw [← Real.rpow_add hK]; ring_nf
  rw [e1, e2]
  have : 0 < sK ^ (1 - α - φ) := Real.rpow_pos_of_pos hK _
  field_simp

/-- The ray identity used repeatedly: `s_K k^α (ρ k)^φ = (s_K ρ^φ) k^{α+φ}`. -/
theorem mrw_ray_output {α φ sK ρ k : ℝ} (hρ : 0 < ρ) (hk : 0 < k) :
    sK * mrwOutput α φ k (ρ * k) = sK * ρ ^ φ * k ^ (α + φ) := by
  unfold mrwOutput
  rw [Real.mul_rpow hρ.le hk.le, Real.rpow_add hk]
  ring

/-- `s_K (s_H/s_K)^φ = s_K^{1-φ} s_H^φ`. -/
theorem mrw_ray_coeff {φ sK sH : ℝ} (hK : 0 < sK) (hH : 0 < sH) :
    sK * (sH / sK) ^ φ = sK ^ (1 - φ) * sH ^ φ := by
  rw [Real.div_rpow hH.le hK.le, Real.rpow_sub hK, Real.rpow_one]
  have : 0 < sK ^ φ := Real.rpow_pos_of_pos hK _
  field_simp

/-- **The MRW steady state (16)–(17)** (O&R p. 439): the pair `(k̄, h̄)` satisfies both
steady-state conditions `s_K y = (z+δ) k` and `s_H y = (z+δ) h`. -/
theorem mrw_steady_spec {α φ sK sH m : ℝ} (hφα : α + φ < 1)
    (hK : 0 < sK) (hH : 0 < sH) (hm : 0 < m) :
    0 < mrwSteadyK α φ sK sH m ∧ 0 < mrwSteadyH α φ sK sH m ∧
      sK * mrwOutput α φ (mrwSteadyK α φ sK sH m) (mrwSteadyH α φ sK sH m) =
        m * mrwSteadyK α φ sK sH m ∧
      sH * mrwOutput α φ (mrwSteadyK α φ sK sH m) (mrwSteadyH α φ sK sH m) =
        m * mrwSteadyH α φ sK sH m := by
  set kb := mrwSteadyK α φ sK sH m
  have hA : 0 < sK ^ (1 - φ) * sH ^ φ := by positivity
  have hkb : 0 < kb := Real.rpow_pos_of_pos (div_pos hA hm) _
  have hρ : 0 < sH / sK := div_pos hH hK
  have hhb := mrwSteadyH_eq hφα hK hH hm
  have hcd : sK ^ (1 - φ) * sH ^ φ * kb ^ (α + φ) = m * kb := by
    have := cobbDouglas_steady (α := α + φ) (by linarith) hA hm
    rw [show 1 - (α + φ) = 1 - α - φ by ring] at this
    exact this
  have hy : sK * mrwOutput α φ kb (sH / sK * kb) = m * kb := by
    rw [mrw_ray_output hρ hkb, mrw_ray_coeff hK hH, hcd]
  refine ⟨hkb, by rw [hhb]; positivity, by rw [hhb]; exact hy, ?_⟩
  rw [hhb]
  have : sH * mrwOutput α φ kb (sH / sK * kb) = sH / sK * (sK * mrwOutput α φ kb (sH / sK * kb)) :=
    by field_simp
  rw [this, hy]
  ring

/-- **Uniqueness of the interior MRW steady state** (O&R p. 439): any positive pair with
`s_K y = (z+δ) k` and `s_H y = (z+δ) h` is `(k̄, h̄)`. -/
theorem mrw_steady_unique {α φ sK sH m k h : ℝ} (hα : 0 < α) (hφ : 0 < φ) (hφα : α + φ < 1)
    (hK : 0 < sK) (hH : 0 < sH) (hm : 0 < m) (hk : 0 < k)
    (e1 : sK * mrwOutput α φ k h = m * k) (e2 : sH * mrwOutput α φ k h = m * h) :
    k = mrwSteadyK α φ sK sH m ∧ h = mrwSteadyH α φ sK sH m := by
  have hρ : 0 < sH / sK := div_pos hH hK
  have hray : h = sH / sK * k := by
    field_simp
    have : sK * (sH * mrwOutput α φ k h) = sH * (sK * mrwOutput α φ k h) := by ring
    rw [e2, e1] at this
    nlinarith
  have hA : 0 < sK ^ (1 - φ) * sH ^ φ := by positivity
  have hcd : sK ^ (1 - φ) * sH ^ φ * k ^ (α + φ) = m * k := by
    rw [← mrw_ray_coeff hK hH, ← e1, hray, mrw_ray_output hρ hk]
  have hk' : k = mrwSteadyK α φ sK sH m := by
    have := cobbDouglas_steady_unique (α := α + φ) (by linarith) (by linarith) hA hm hk hcd
    rw [this, show 1 - (α + φ) = 1 - α - φ by ring]
    rfl
  exact ⟨hk', by rw [hray, mrwSteadyH_eq hφα hK hH hm, hk']⟩

/-- **The MRW estimating equation** (O&R p. 439), exact form: with `E_t = E₀(1+g)^t`,
`log(Y/L) = log E₀ + t log(1+g) + α/(1-α-φ) log s_K + φ/(1-α-φ) log s_H
 - (α+φ)/(1-α-φ) log(z+δ)`. The book prints the last term as
`-log[(α+φ)/(1-α-φ)](n+g+δ)`, a typesetting error: the coefficient multiplies the log. -/
theorem mrw_estimating_equation {α φ sK sH m E0 g : ℝ} (hφα : α + φ < 1) (hK : 0 < sK)
    (hH : 0 < sH) (hm : 0 < m) (hE0 : 0 < E0) (hg : 0 < 1 + g) (t : ℕ) :
    Real.log (E0 * (1 + g) ^ t * mrwOutput α φ (mrwSteadyK α φ sK sH m)
      (mrwSteadyH α φ sK sH m)) =
      Real.log E0 + t * Real.log (1 + g) + α / (1 - α - φ) * Real.log sK +
        φ / (1 - α - φ) * Real.log sH - (α + φ) / (1 - α - φ) * Real.log m := by
  have he : 1 - α - φ ≠ 0 := by linarith
  have hA : 0 < sK ^ (1 - φ) * sH ^ φ / m := by positivity
  have hB : 0 < sH ^ (1 - α) * sK ^ α / m := by positivity
  unfold mrwOutput mrwSteadyK mrwSteadyH
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow,
    ← Real.rpow_mul hA.le, ← Real.rpow_mul hB.le, Real.log_rpow hA, Real.log_rpow hB,
    Real.log_div (by positivity) (ne_of_gt hm), Real.log_div (by positivity) (ne_of_gt hm),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hK, Real.log_rpow hH, Real.log_rpow hK, Real.log_rpow hH]
  field_simp
  ring

/-- **Ray invariance** (new exact lemma, O&R (14)–(15)): `w = s_K h - s_H k` satisfies
`w' = ((1-δ)/(1+z)) w` for every `(k, h)`. -/
theorem mrw_gap_contracts {α φ sK sH δ z k h : ℝ} (hz : 1 + z ≠ 0) :
    sK * mrwH α φ sH δ z k h - sH * mrwK α φ sK δ z k h =
      (1 - δ) / (1 + z) * (sK * h - sH * k) := by
  unfold mrwH mrwK
  field_simp
  ring

/-- Along any MRW path `w_t = ((1-δ)/(1+z))^t w₀`, which tends to zero when `δ ≤ 1` and
`z + δ > 0`: the capital ratio `h/k` approaches `s_H/s_K` geometrically. -/
theorem mrw_gap_tendsto {α φ sK sH δ z : ℝ} (hδ : δ ≤ 1) (hzd : 0 < z + δ) (hz : 0 < 1 + z)
    {k h : ℕ → ℝ} (hk : ∀ t, k (t + 1) = mrwK α φ sK δ z (k t) (h t))
    (hh : ∀ t, h (t + 1) = mrwH α φ sH δ z (k t) (h t)) :
    (∀ t, sK * h t - sH * k t = ((1 - δ) / (1 + z)) ^ t * (sK * h 0 - sH * k 0)) ∧
      Tendsto (fun t => sK * h t - sH * k t) atTop (𝓝 0) := by
  have hstep : ∀ t, sK * h t - sH * k t = ((1 - δ) / (1 + z)) ^ t * (sK * h 0 - sH * k 0) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hk t, hh t, mrw_gap_contracts (ne_of_gt hz), ih, pow_succ]
      ring
  refine ⟨hstep, ?_⟩
  have hq0 : 0 ≤ (1 - δ) / (1 + z) := div_nonneg (by linarith) hz.le
  have hq1 : (1 - δ) / (1 + z) < 1 := by rw [div_lt_one hz]; linarith
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (sK * h 0 - sH * k 0)
  rw [zero_mul] at this
  exact this.congr (fun t => (hstep t).symm)

/-- The MRW maps are monotone in both capital stocks when `δ ≤ 1` (a cooperative system). -/
theorem mrw_monotone {α φ s δ z k k' h h' : ℝ} (hα : 0 < α) (hφ : 0 < φ) (hs : 0 < s)
    (hδ : δ ≤ 1) (hz : 0 < 1 + z) (hk : 0 < k) (hh : 0 < h) (hkk : k ≤ k') (hhh : h ≤ h') :
    mrwK α φ s δ z k h ≤ mrwK α φ s δ z k' h' ∧ mrwH α φ s δ z k h ≤ mrwH α φ s δ z k' h' := by
  have hy : mrwOutput α φ k h ≤ mrwOutput α φ k' h' := by
    unfold mrwOutput
    exact mul_le_mul (Real.rpow_le_rpow hk.le hkk hα.le) (Real.rpow_le_rpow hh.le hhh hφ.le)
      (Real.rpow_nonneg hh.le _) (Real.rpow_nonneg (hk.le.trans hkk) _)
  have h1 := mul_le_mul_of_nonneg_left hy hs.le
  have h2 := mul_le_mul_of_nonneg_left hkk (sub_nonneg.mpr hδ)
  have h3 := mul_le_mul_of_nonneg_left hhh (sub_nonneg.mpr hδ)
  exact ⟨div_le_div_of_nonneg_right (by linarith) hz.le,
    div_le_div_of_nonneg_right (by linarith) hz.le⟩

/-- On the ray `h = ρ k`, `ρ = s_H/s_K`, the MRW system is a one-dimensional Solow model
with technology `ρ^φ k^{α+φ}` (O&R p. 439). -/
theorem mrw_on_ray {α φ sK sH δ z a : ℝ} (hK : 0 < sK) (hH : 0 < sH) (ha : 0 < a) :
    mrwK α φ sK δ z a (sH / sK * a) =
        solowMap (fun k => (sH / sK) ^ φ * k ^ (α + φ)) sK δ z a ∧
      mrwH α φ sH δ z a (sH / sK * a) =
        sH / sK * solowMap (fun k => (sH / sK) ^ φ * k ^ (α + φ)) sK δ z a := by
  have hρ : 0 < sH / sK := div_pos hH hK
  have hy := mrw_ray_output (α := α) (φ := φ) (sK := 1) hρ ha
  simp only [one_mul] at hy
  unfold mrwK mrwH solowMap
  rw [hy]
  refine ⟨by ring, ?_⟩
  field_simp

/-- **Global convergence of the MRW model** (the precise version of the book's steady-state
analysis, O&R pp. 438–439, which does not argue stability): with `α, φ > 0`, `α + φ < 1`,
`δ ≤ 1`, `z + δ > 0` and positive saving rates, every path from positive `(k₀, h₀)`
converges to `(k̄, h̄)` of (16)–(17). Proof: sandwich the path between two orbits on the
invariant ray, which is a Cobb–Douglas Solow model with exponent `α + φ`. -/
theorem mrw_global_convergence {α φ sK sH δ z : ℝ} (hα : 0 < α) (hφ : 0 < φ)
    (hφα : α + φ < 1) (hK : 0 < sK) (hH : 0 < sH) (hδ : δ ≤ 1) (hzd : 0 < z + δ)
    (hz : 0 < 1 + z) {k h : ℕ → ℝ} (hk0 : 0 < k 0) (hh0 : 0 < h 0)
    (hk : ∀ t, k (t + 1) = mrwK α φ sK δ z (k t) (h t))
    (hh : ∀ t, h (t + 1) = mrwH α φ sH δ z (k t) (h t)) :
    Tendsto k atTop (𝓝 (mrwSteadyK α φ sK sH (z + δ))) ∧
      Tendsto h atTop (𝓝 (mrwSteadyH α φ sK sH (z + δ))) := by
  set ρ := sH / sK with hρdef
  have hρ : 0 < ρ := div_pos hH hK
  set G := solowMap (fun k => ρ ^ φ * k ^ (α + φ)) sK δ z
  have P : SolowParams sK δ z := ⟨hK, hδ, hzd, hz⟩
  have hαφ : 0 < α + φ := by linarith
  have hneo : Neoclassical (fun k => ρ ^ φ * k ^ (α + φ)) :=
    Neoclassical.const_mul (neoclassical_rpow hαφ hφα) (Real.rpow_pos_of_pos hρ φ)
  obtain ⟨hkb, -, hss, -⟩ := mrw_steady_spec hφα hK hH hzd
  set kb := mrwSteadyK α φ sK sH (z + δ)
  have hbar : sK * (ρ ^ φ * kb ^ (α + φ)) = (z + δ) * kb := by
    rw [mrwSteadyH_eq hφα hK hH hzd, mrw_ray_output hρ hkb] at hss
    linarith
  have hG := solow_monotoneMap hneo P hkb hbar
  -- the two ray orbits
  set a := min (k 0) (h 0 / ρ)
  set b := max (k 0) (h 0 / ρ)
  have ha : 0 < a := lt_min hk0 (div_pos hh0 hρ)
  have hb : 0 < b := lt_of_lt_of_le hk0 (le_max_left _ _)
  let lo : ℕ → ℝ := fun t => G^[t] a
  let hi : ℕ → ℝ := fun t => G^[t] b
  have hlo : ∀ t, lo (t + 1) = G (lo t) := fun t => Function.iterate_succ_apply' G t a
  have hhi : ∀ t, hi (t + 1) = G (hi t) := fun t => Function.iterate_succ_apply' G t b
  have hlopos : ∀ t, 0 < lo t := by
    intro t; induction t with
    | zero => exact ha
    | succ t ih => rw [hlo t]; exact hG.pos _ ih
  have hhipos : ∀ t, 0 < hi t := by
    intro t; induction t with
    | zero => exact hb
    | succ t ih => rw [hhi t]; exact hG.pos _ ih
  -- the sandwich
  have hsand : ∀ t, lo t ≤ k t ∧ ρ * lo t ≤ h t ∧ k t ≤ hi t ∧ h t ≤ ρ * hi t := by
    intro t
    induction t with
    | zero =>
      refine ⟨min_le_left _ _, ?_, le_max_left _ _, ?_⟩
      · have : a ≤ h 0 / ρ := min_le_right _ _
        change ρ * a ≤ h 0
        rw [le_div_iff₀ hρ] at this; linarith
      · have : h 0 / ρ ≤ b := le_max_right _ _
        change h 0 ≤ ρ * b
        rw [div_le_iff₀ hρ] at this; linarith
    | succ t ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      have hL := mrw_monotone (s := sK) hα hφ hK hδ hz (hlopos t) (mul_pos hρ (hlopos t)) h1 h2
      have hL' := mrw_monotone (s := sH) hα hφ hH hδ hz (hlopos t) (mul_pos hρ (hlopos t)) h1 h2
      have hU := mrw_monotone (s := sK) hα hφ hK hδ hz (lt_of_lt_of_le (hlopos t) h1)
        (lt_of_lt_of_le (mul_pos hρ (hlopos t)) h2) h3 h4
      have hU' := mrw_monotone (s := sH) hα hφ hH hδ hz (lt_of_lt_of_le (hlopos t) h1)
        (lt_of_lt_of_le (mul_pos hρ (hlopos t)) h2) h3 h4
      obtain ⟨rl1, rl2⟩ := mrw_on_ray (α := α) (φ := φ) (δ := δ) (z := z) hK hH (hlopos t)
      obtain ⟨ru1, ru2⟩ := mrw_on_ray (α := α) (φ := φ) (δ := δ) (z := z) hK hH (hhipos t)
      rw [hk t, hh t, hlo t, hhi t]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact le_trans (le_of_eq rl1.symm) hL.1
      · exact le_trans (le_of_eq rl2.symm) hL'.2
      · exact le_trans hU.1 (le_of_eq ru1)
      · exact le_trans hU'.2 (le_of_eq ru2)
  have hloT := (hG.orbit_tendsto hlo ha).1
  have hhiT := (hG.orbit_tendsto hhi hb).1
  refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le hloT hhiT (fun t => (hsand t).1)
    (fun t => (hsand t).2.2.1), ?_⟩
  rw [mrwSteadyH_eq hφα hK hH hzd]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (hloT.const_mul ρ) (hhiT.const_mul ρ)
    (fun t => (hsand t).2.1) (fun t => (hsand t).2.2.2)

/-! ## The Barro–Mankiw–Sala-i-Martin open economy (O&R pp. 464–467) -/

/-- **Eq. (46)** (O&R p. 465): if the net marginal product of physical capital equals the
world rate, `r = α k^{α-1} h^φ`, then `k = α y/r`, so `K/Y` is constant along the path. -/
theorem bms_capital_output {α φ k h r : ℝ} (hk : 0 < k) (hh : 0 < h)
    (hr : r = α * k ^ (α - 1) * h ^ φ) (hr0 : 0 < r) : k = α * mrwOutput α φ k h / r := by
  rw [eq_div_iff (ne_of_gt hr0), hr]
  unfold mrwOutput
  rw [Real.rpow_sub hk, Real.rpow_one]
  have : 0 < k ^ α := Real.rpow_pos_of_pos hk α
  field_simp

/-- Capital as a function of human capital under (46): `k = (α h^φ/r)^{1/(1-α)}`. -/
noncomputable def bmsCapital (α φ r h : ℝ) : ℝ := (α * h ^ φ / r) ^ (1 / (1 - α))

/-- `bmsCapital` equates the marginal product of capital to the world rate. -/
theorem bmsCapital_spec {α φ r h : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r) (hh : 0 < h) :
    0 < bmsCapital α φ r h ∧ α * bmsCapital α φ r h ^ (α - 1) * h ^ φ = r := by
  have hx : 0 < α * h ^ φ / r := by positivity
  refine ⟨Real.rpow_pos_of_pos hx _, ?_⟩
  have h1α : 1 - α ≠ 0 := by linarith
  unfold bmsCapital
  rw [← Real.rpow_mul hx.le, show 1 / (1 - α) * (α - 1) = -1 by field_simp; ring,
    Real.rpow_neg_one]
  have : 0 < h ^ φ := Real.rpow_pos_of_pos hh φ
  field_simp

/-- **Eq. (47)** (O&R p. 465): output is `y = χ h^ν` with `ν = φ/(1-α)` and
`χ = (α/r)^{α/(1-α)}`. -/
theorem bms_output {α φ r h : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r) (hh : 0 < h) :
    mrwOutput α φ (bmsCapital α φ r h) h = (α / r) ^ (α / (1 - α)) * h ^ (φ / (1 - α)) := by
  have hx : 0 < α / r := div_pos hα hr
  have h1α : 1 - α ≠ 0 := by linarith
  unfold mrwOutput bmsCapital
  rw [mul_div_right_comm, Real.mul_rpow hx.le (Real.rpow_nonneg hh.le _),
    Real.mul_rpow (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg (Real.rpow_nonneg hh.le _) _),
    ← Real.rpow_mul hx.le, ← Real.rpow_mul (Real.rpow_nonneg hh.le _),
    ← Real.rpow_mul hh.le, mul_assoc, ← Real.rpow_add hh]
  congr 2
  · ring
  · field_simp; ring

/-- Output net of interest on foreign-financed capital is `(1-α) y` (O&R p. 466, using
(46): `r k = α y`). -/
theorem bms_net_output {α φ r h : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r) (hh : 0 < h) :
    mrwOutput α φ (bmsCapital α φ r h) h - r * bmsCapital α φ r h =
      (1 - α) * mrwOutput α φ (bmsCapital α φ r h) h := by
  obtain ⟨hk, hmp⟩ := bmsCapital_spec (φ := φ) hα hα1 hr hh
  have := bms_capital_output hk hh hmp.symm hr
  have e : r * bmsCapital α φ r h = α * mrwOutput α φ (bmsCapital α φ r h) h := by
    conv_lhs => rw [this]
    field_simp
  rw [e]; ring

/-- **The wealth identity with a binding collateral constraint** (O&R p. 466): from
`H' - H + K' - K + B' - B = Y + rB - C - δH` with `B = -K` at both dates and the Solovian
consumption rule `C = (1-s)(Y - rK)`, human capital obeys `H' - H = s(Y - rK) - δH`.
The book's display `H' - H = s(Y - rK)` omits the depreciation term `-δH`
(eq. (48) itself includes it). -/
theorem bms_human_capital_accumulation {H H' K K' B B' Y C r s δ : ℝ}
    (hw : H' - H + (K' - K) + (B' - B) = Y + r * B - C - δ * H) (hB : B = -K)
    (hB' : B' = -K') (hC : C = (1 - s) * (Y - r * K)) :
    H' - H = s * (Y - r * K) - δ * H := by
  subst hB hB' hC; linarith

/-- **Eq. (48)** (O&R p. 466): in efficiency units, human capital follows the Solow map
with exponent `ν = φ/(1-α)` and effective saving rate `s' = s(1-α)χ`. -/
theorem bms_human_capital_map {α φ r s δ z h h' : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r)
    (hh : 0 < h) (hz : 0 < 1 + z)
    (hacc : (1 + z) * h' = (1 - δ) * h +
      s * (mrwOutput α φ (bmsCapital α φ r h) h - r * bmsCapital α φ r h)) :
    h' = solowMap (fun h => h ^ (φ / (1 - α))) (s * (1 - α) * (α / r) ^ (α / (1 - α))) δ z h := by
  rw [bms_net_output hα hα1 hr hh, bms_output hα hα1 hr hh] at hacc
  unfold solowMap
  rw [eq_div_iff (ne_of_gt hz)]
  linarith

/-- Dividing a levels accumulation equation `X' = (1-δ)X + s V` by `E'L' = (1+z) E L` gives
`x' = [(1-δ)x + s v]/(1+z)` in efficiency units (the normalisation used for (14), (15), (48)). -/
theorem efficiency_units_accumulation {X X' V s δ N N' z : ℝ} (hN : 0 < N)
    (hN' : N' = (1 + z) * N) (hz : 0 < 1 + z) (hacc : X' = (1 - δ) * X + s * V) :
    X' / N' = ((1 - δ) * (X / N) + s * (V / N)) / (1 + z) := by
  rw [hN', hacc]
  field_simp

/-- **Eq. (49)–(51)** (O&R p. 467): the BMS steady state `h̄ = (s'/(z+δ))^{1/(1-ν)}` and
convergence factor `μ' = [1 + νz + (ν-1)δ]/(1+z)`, requiring `ν < 1`, i.e. `α + φ < 1`. -/
theorem bms_steady_and_speed {α φ s' δ z : ℝ} (hφ : 0 < φ) (hφα : α + φ < 1)
    (hs : 0 < s') (hzd : 0 < z + δ) :
    s' * ((s' / (z + δ)) ^ (1 / (1 - φ / (1 - α)))) ^ (φ / (1 - α)) =
        (z + δ) * (s' / (z + δ)) ^ (1 / (1 - φ / (1 - α))) ∧
      HasDerivAt (solowMap (fun h => h ^ (φ / (1 - α))) s' δ z)
        ((1 + φ / (1 - α) * z + (φ / (1 - α) - 1) * δ) / (1 + z))
        ((s' / (z + δ)) ^ (1 / (1 - φ / (1 - α)))) := by
  have hν : 0 < φ / (1 - α) := div_pos hφ (by linarith)
  have hν1 : φ / (1 - α) < 1 := by rw [div_lt_one (by linarith)]; linarith
  exact ⟨cobbDouglas_steady hν1 hs hzd, cobbDouglas_mu hν hν1 hs hzd⟩

/-- **Global convergence in the BMS economy** (O&R p. 467, "isomorphic to (43)"): from
every `h₀ > 0` human capital converges monotonically to `h̄` of (49). -/
theorem bms_global_convergence {α φ s' δ z : ℝ} (hφ : 0 < φ) (hφα : α + φ < 1)
    (P : SolowParams s' δ z) {h : ℕ → ℝ} (h0 : 0 < h 0)
    (hrec : ∀ t, h (t + 1) = solowMap (fun h => h ^ (φ / (1 - α))) s' δ z (h t)) :
    Tendsto h atTop (𝓝 ((s' / (z + δ)) ^ (1 / (1 - φ / (1 - α))))) ∧
      (Monotone h ∨ Antitone h) := by
  have hν : 0 < φ / (1 - α) := div_pos hφ (by linarith)
  have hν1 : φ / (1 - α) < 1 := by rw [div_lt_one (by linarith)]; linarith
  exact cobbDouglas_global_convergence hν hν1 P h0 hrec

/-- **The exponent ordering** (O&R p. 467): `φ < ν = φ/(1-α) < φ + α`. -/
theorem bms_exponent_order {α φ : ℝ} (hα : 0 < α) (hφ : 0 < φ) (hφα : α + φ < 1) :
    φ < φ / (1 - α) ∧ φ / (1 - α) < φ + α := by
  have h1α : 0 < 1 - α := by linarith
  constructor
  · rw [lt_div_iff₀ h1α]; nlinarith
  · rw [div_lt_iff₀ h1α]; nlinarith

/-- **The speed ordering** (O&R p. 467): convergence in the BMS economy (`1 - μ'`) is slower
than in a closed economy with capital share `φ` but faster than with share `α + φ`. -/
theorem bms_speed_order {α φ δ z : ℝ} (hα : 0 < α) (hφ : 0 < φ) (hφα : α + φ < 1)
    (hzd : 0 < z + δ) (hz : 0 < 1 + z) :
    1 - (1 + (φ + α) * z + (φ + α - 1) * δ) / (1 + z) <
        1 - (1 + φ / (1 - α) * z + (φ / (1 - α) - 1) * δ) / (1 + z) ∧
      1 - (1 + φ / (1 - α) * z + (φ / (1 - α) - 1) * δ) / (1 + z) <
        1 - (1 + φ * z + (φ - 1) * δ) / (1 + z) := by
  obtain ⟨h1, h2⟩ := bms_exponent_order hα hφ hφα
  have e1 := mu_strictMono_alpha (δ := δ) hzd hz h1
  have e2 := mu_strictMono_alpha (δ := δ) hzd hz h2
  constructor <;> linarith

/-! ## The shape of transition dynamics (O&R p. 462, fn 24) -/

/-- **p. 462 is false for the level increment** (flag): with `α = 1/2`, `s = 1`, `z = 0`,
`δ = 1` (so `k̄ = 1`), capital `0.01` lies further below `k̄` than `0.25`, yet its increment
`Δk = 0.09` is smaller than `Δk = 0.25`. -/
theorem increment_not_larger_further_below :
    solowMap (fun k => k ^ (1 / 2 : ℝ)) 1 1 0 1 = 1 ∧
      solowMap (fun k => k ^ (1 / 2 : ℝ)) 1 1 0 (1 / 4) - 1 / 4 = 1 / 4 ∧
      solowMap (fun k => k ^ (1 / 2 : ℝ)) 1 1 0 (1 / 100) - 1 / 100 = 9 / 100 := by
  have e1 : (1 / 4 : ℝ) ^ (1 / 2 : ℝ) = 1 / 2 := by
    rw [← Real.sqrt_eq_rpow, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have e2 : (1 / 100 : ℝ) ^ (1 / 2 : ℝ) = 1 / 10 := by
    rw [← Real.sqrt_eq_rpow, show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  unfold solowMap
  refine ⟨by simp, ?_, ?_⟩
  · norm_num [e1]
  · norm_num [e2]

/-- **p. 462 corrected, below the steady state**: the *growth rate* `Δk/k` is strictly
decreasing in `k` on all of `(0, ∞)`, so it is larger the further `k` lies below `k̄`. -/
theorem growth_rate_strictAnti (hf : Neoclassical f) {s δ z : ℝ} (P : SolowParams s δ z) :
    StrictAntiOn (fun k => (solowMap f s δ z k - k) / k) (Ioi 0) := by
  intro a ha b hb hab
  have h := solowMap_ratio_anti hf P ha hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  simp only at h ⊢
  rw [sub_div, sub_div, div_self (ne_of_gt ha'), div_self (ne_of_gt hb')]
  linarith

/-- **p. 462 above the steady state** (true as stated): for `k̄ ≤ a < b`, capital falls
faster from `b` than from `a`: `G(b) - b < G(a) - a`. -/
theorem increment_strictAnti_above (hf : Neoclassical f) {s δ z kbar : ℝ}
    (P : SolowParams s δ z) (hk : 0 < kbar) (hss : s * f kbar = (z + δ) * kbar) {a b : ℝ}
    (ha : kbar ≤ a) (hab : a < b) : solowMap f s δ z b - b < solowMap f s δ z a - a := by
  have ha0 : 0 < a := lt_of_lt_of_le hk ha
  have hz := P.growth_pos
  rw [solowMap_sub s δ z b (ne_of_gt hz), solowMap_sub s δ z a (ne_of_gt hz)]
  apply div_lt_div_of_pos_right _ hz
  have ht := hf.tangent_le ha0 (ha0.trans hab).le
  have hmp := hf.deriv_mul_lt ha0
  have havg : f a / a ≤ f kbar / kbar := hf.avg_strictAnti.antitoneOn hk ha0 ha
  have hkb : f kbar / kbar = (z + δ) / s := by
    rw [div_eq_div_iff (ne_of_gt hk) (ne_of_gt P.saving_pos)]; linarith
  have hd : s * deriv f a < z + δ := by
    have h1 : deriv f a < f a / a := by rw [lt_div_iff₀ ha0]; exact hmp
    have h2 : f a / a ≤ (z + δ) / s := hkb ▸ havg
    have h3 := lt_of_lt_of_le h1 h2
    rw [lt_div_iff₀ P.saving_pos] at h3
    linarith
  have := mul_le_mul_of_nonneg_left ht P.saving_pos.le
  nlinarith

/-- **fn 5** (O&R p. 437): with `r = α A k^{α-1}` everywhere, the rate-of-return ratio of two
economies is `(k₁/k₂)^{α-1}`. -/
theorem return_ratio {α A k1 k2 : ℝ} (hA : 0 < A) (hα : 0 < α) (h1 : 0 < k1) (h2 : 0 < k2) :
    (α * A * k1 ^ (α - 1)) / (α * A * k2 ^ (α - 1)) = (k1 / k2) ^ (α - 1) := by
  rw [Real.div_rpow h1.le h2.le]
  have : 0 < k2 ^ (α - 1) := Real.rpow_pos_of_pos h2 _
  field_simp

/-- **fn 5 numbers** (O&R p. 437): an eightfold capital ratio gives a return ratio
`8^{-2/3} = 1/4` at `α = 1/3` and `8^{-1/3} = 1/2` at `α = 2/3`. -/
theorem return_ratio_numbers :
    (8 : ℝ) ^ ((1 : ℝ) / 3 - 1) = 1 / 4 ∧ (8 : ℝ) ^ ((2 : ℝ) / 3 - 1) = 1 / 2 := by
  have h8 : (8 : ℝ) = 2 ^ (3 : ℝ) := by norm_num
  constructor
  · rw [h8, ← Real.rpow_mul (by norm_num)]
    norm_num
  · rw [h8, ← Real.rpow_mul (by norm_num)]
    norm_num

/-- **fn 24** (O&R p. 463): the logarithmic deviation shrinks at the same asymptotic rate:
`(log k_{t+1} - log k̄)/(log k_t - log k̄) → μ = G'(k̄)`. -/
theorem log_ratio_tendsto (hf : Neoclassical f) {s δ z kbar : ℝ} (P : SolowParams s δ z)
    (hk : 0 < kbar) (hss : s * f kbar = (z + δ) * kbar) {k : ℕ → ℝ}
    (hrec : ∀ t, k (t + 1) = solowMap f s δ z (k t)) (h0 : 0 < k 0) (hne : k 0 ≠ kbar) :
    Tendsto (fun t => (Real.log (k (t + 1)) - Real.log kbar) / (Real.log (k t) - Real.log kbar))
      atTop (𝓝 (((1 - δ) + s * deriv f kbar) / (1 + z))) := by
  have hG := solow_monotoneMap hf P hk hss
  have hL := (hG.orbit_tendsto hrec h0).1
  have hne' : ∀ t, k t ≠ kbar := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact fun t => ne_of_lt ((hG.orbit_below hrec h0 hlt).2.1 t)
    · exact fun t => ne_of_gt ((hG.orbit_above hrec hgt).2.1 t)
  have hpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih => rw [hrec t]; exact hG.pos _ ih
  have hratio := solow_ratio_tendsto hf P hk hss hrec h0 hne
  have hslope := hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_log (ne_of_gt hk))
  have hk' : Tendsto k atTop (𝓝[≠] kbar) :=
    tendsto_nhdsWithin_iff.mpr ⟨hL, Eventually.of_forall hne'⟩
  have hk1 : Tendsto (fun t => k (t + 1)) atTop (𝓝[≠] kbar) :=
    hk'.comp (tendsto_add_atTop_nat 1)
  have hs0 := hslope.comp hk'
  have hs1 := hslope.comp hk1
  have hinv : kbar⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hk)
  have hlim := (hs1.mul hratio).div hs0 hinv
  rw [show kbar⁻¹ * (((1 - δ) + s * deriv f kbar) / (1 + z)) / kbar⁻¹ =
    ((1 - δ) + s * deriv f kbar) / (1 + z) by field_simp] at hlim
  refine hlim.congr (fun t => ?_)
  have hd0 : k t - kbar ≠ 0 := sub_ne_zero.mpr (hne' t)
  have hd1 : k (t + 1) - kbar ≠ 0 := sub_ne_zero.mpr (hne' (t + 1))
  have hl0 : Real.log (k t) - Real.log kbar ≠ 0 := by
    intro h
    have := Real.log_injOn_pos (hpos t) hk (by linarith)
    exact hne' t this
  simp only [Pi.div_apply, Function.comp_apply, slope_def_field]
  field_simp


/-! ## The Solow model without `δ ≤ 1` (flag on Fig. 7.1) -/

/-- `G(k)/k` is strictly decreasing for every depreciation rate (only `s > 0`, `1 + z > 0`). -/
theorem solowMap_ratio_anti_any (hf : Neoclassical f) {s δ z : ℝ} (hs : 0 < s)
    (hz : 0 < 1 + z) : StrictAntiOn (fun k => solowMap f s δ z k / k) (Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have heq : ∀ x : ℝ, 0 < x → solowMap f s δ z x / x = ((1 - δ) + s * (f x / x)) / (1 + z) := by
    intro x hx
    unfold solowMap
    field_simp
  simp only [heq a ha', heq b hb']
  have := mul_lt_mul_of_pos_left (hf.avg_strictAnti ha hb hab) hs
  exact div_lt_div_of_pos_right (by linarith) hz

/-- **The steady state exists and is unique for every `δ`** (only `z + δ > 0` is needed):
Inada conditions give a unique `k̄ > 0` with `s f(k̄) = (z + δ) k̄`. -/
theorem solow_steady_existsUnique_any (hf : Neoclassical f) {s δ z : ℝ} (hs : 0 < s)
    (hzd : 0 < z + δ) (hz : 0 < 1 + z) (h0 : Tendsto (deriv f) (𝓝[>] 0) atTop)
    (hinf : Tendsto (deriv f) atTop (𝓝 0)) : ∃! k, 0 < k ∧ s * f k = (z + δ) * k := by
  have htarget : 0 < (z + δ) / s := div_pos hzd hs
  have hev0 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi 0 := eventually_mem_nhdsWithin
  obtain ⟨a, ha, hfa⟩ := (hev0.and ((hf.avg_tendsto_atTop h0).eventually
    (eventually_gt_atTop ((z + δ) / s)))).exists
  have ha' : (0 : ℝ) < a := ha
  obtain ⟨b, hb, hfb⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    ((hf.avg_tendsto_zero hinf).eventually (gt_mem_nhds htarget))).exists
  rw [div_lt_div_iff₀ hs ha'] at hfa
  rw [div_lt_div_iff₀ hb hs] at hfb
  have hfix : ∀ k, solowMap f s δ z k = k ↔ s * f k = (z + δ) * k := by
    intro k; unfold solowMap; rw [div_eq_iff (ne_of_gt hz)]
    constructor <;> intro h <;> linarith
  have hGa : a < solowMap f s δ z a := by
    unfold solowMap; rw [lt_div_iff₀ hz]; linarith
  have hGb : solowMap f s δ z b < b := by
    unfold solowMap; rw [div_lt_iff₀ hz]; linarith
  obtain ⟨k, ⟨hk, hk'⟩, hu⟩ := fixed_point_existsUnique (solowMap_continuousOn hf s δ z)
    (solowMap_ratio_anti_any hf hs hz) ha' hGa hb hGb
  exact ⟨k, ⟨hk, (hfix k).mp hk'⟩, fun y hy => hu y ⟨hy.1, (hfix y).mpr hy.2⟩⟩

/-- **With `δ > 1` capital can turn negative** (why Fig. 7.1 needs `δ ≤ 1`): if the average
product tends to zero, some `k > 0` is mapped to a negative capital stock. -/
theorem solow_negative_of_delta_gt_one (hf : Neoclassical f) {s δ z : ℝ} (hs : 0 < s)
    (hδ : 1 < δ) (hz : 0 < 1 + z) (hinf : Tendsto (deriv f) atTop (𝓝 0)) :
    ∃ k, 0 < k ∧ solowMap f s δ z k < 0 := by
  have htarget : 0 < (δ - 1) / s := div_pos (by linarith) hs
  obtain ⟨b, hb, hfb⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    ((hf.avg_tendsto_zero hinf).eventually (gt_mem_nhds htarget))).exists
  rw [div_lt_div_iff₀ hb hs] at hfb
  refine ⟨b, hb, ?_⟩
  unfold solowMap
  apply div_neg_of_neg_of_pos _ hz
  linarith

/-- **The slope at the steady state is always below one**: `G'(k̄) = [(1-δ) + s f'(k̄)]/(1+z) < 1`
(for any `δ`), since `s f'(k̄) < s f(k̄)/k̄ = z + δ`. -/
theorem solow_slope_lt_one (hf : Neoclassical f) {s δ z kbar : ℝ} (hs : 0 < s)
    (hz : 0 < 1 + z) (hk : 0 < kbar) (hss : s * f kbar = (z + δ) * kbar) :
    ((1 - δ) + s * deriv f kbar) / (1 + z) < 1 := by
  rw [div_lt_one hz]
  have h := hf.deriv_mul_lt hk
  have : s * (deriv f kbar * kbar) < s * f kbar := mul_lt_mul_of_pos_left h hs
  have : s * deriv f kbar * kbar < (z + δ) * kbar := by nlinarith
  have := lt_of_mul_lt_mul_right this hk.le
  linarith

/-- **Local convergence from the derivative** (generic): if `G(k̄) = k̄` and `|G'(k̄)| < 1`, every
orbit starting close enough to `k̄` converges to it (geometrically). -/
theorem local_convergence_of_deriv {G : ℝ → ℝ} {kbar μ : ℝ} (hd : HasDerivAt G μ kbar)
    (hfix : G kbar = kbar) (hμ : |μ| < 1) :
    ∃ ε > 0, ∀ k : ℕ → ℝ, (∀ t, k (t + 1) = G (k t)) → |k 0 - kbar| < ε →
      Tendsto k atTop (𝓝 kbar) := by
  set lam := (|μ| + 1) / 2
  have hlam : |μ| < lam := by simp only [lam]; linarith
  have hlam1 : lam < 1 := by simp only [lam]; linarith
  have hlam0 : 0 ≤ lam := by simp only [lam]; positivity
  have hs := hasDerivAt_iff_tendsto_slope.mp hd
  have hev : ∀ᶠ x in 𝓝[≠] kbar, |slope G kbar x| < lam :=
    (continuous_abs.tendsto μ).comp hs |>.eventually (gt_mem_nhds hlam)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  refine ⟨ε, hε, fun k hk h0 => ?_⟩
  -- one-step contraction inside the ball
  have hstep : ∀ x, |x - kbar| < ε → |G x - kbar| ≤ lam * |x - kbar| := by
    intro x hx
    by_cases hxk : x = kbar
    · subst hxk; simp [hfix]
    · have h := hball (by rw [Real.dist_eq]; exact hx) hxk
      rw [slope_def_field, hfix, abs_div] at h
      have hpos : 0 < |x - kbar| := abs_pos.mpr (sub_ne_zero.mpr hxk)
      rw [div_lt_iff₀ hpos] at h
      linarith
  have hbound : ∀ t, |k t - kbar| ≤ lam ^ t * |k 0 - kbar| := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hin : |k t - kbar| < ε := lt_of_le_of_lt ih (by
        calc lam ^ t * |k 0 - kbar| ≤ 1 * |k 0 - kbar| :=
              mul_le_mul_of_nonneg_right (pow_le_one₀ hlam0 hlam1.le) (abs_nonneg _)
          _ < ε := by rw [one_mul]; exact h0)
      rw [hk t, pow_succ]
      calc |G (k t) - kbar| ≤ lam * |k t - kbar| := hstep _ hin
        _ ≤ lam * (lam ^ t * |k 0 - kbar|) := mul_le_mul_of_nonneg_left ih hlam0
        _ = lam ^ t * lam * |k 0 - kbar| := by ring
  have hgeo := (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0 hlam1).mul_const |k 0 - kbar|
  rw [zero_mul] at hgeo
  have habs : Tendsto (fun t => |k t - kbar|) atTop (𝓝 0) :=
    squeeze_zero (fun t => abs_nonneg _) hbound hgeo
  have := (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  simpa using this.add_const kbar

/-- **No convergence when `|G'(k̄)| > 1`** (generic): an orbit that never lands exactly on `k̄`
cannot converge to it. -/
theorem no_convergence_of_deriv {G : ℝ → ℝ} {kbar μ : ℝ} (hd : HasDerivAt G μ kbar)
    (hfix : G kbar = kbar) (hμ : 1 < |μ|) {k : ℕ → ℝ} (hk : ∀ t, k (t + 1) = G (k t))
    (hne : ∀ t, k t ≠ kbar) : ¬ Tendsto k atTop (𝓝 kbar) := by
  intro hL
  have hr := ratio_tendsto_deriv hd hfix hk hne hL
  have hev := ((continuous_abs.tendsto μ).comp hr).eventually (lt_mem_nhds hμ)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  have hgrow : ∀ n, |k T - kbar| ≤ |k (T + n) - kbar| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hT (T + n) (by omega)
      simp only [Function.comp_apply, abs_div] at h
      have hpos : 0 < |k (T + n) - kbar| := abs_pos.mpr (sub_ne_zero.mpr (hne _))
      rw [lt_div_iff₀ hpos, one_mul] at h
      rw [show T + (n + 1) = T + n + 1 by ring]
      linarith
  have hpos : 0 < |k T - kbar| := abs_pos.mpr (sub_ne_zero.mpr (hne T))
  have habs : Tendsto (fun t => |k t - kbar|) atTop (𝓝 0) := by
    have := (hL.sub_const kbar)
    rw [sub_self] at this
    have h2 := (continuous_abs.tendsto 0).comp this
    rw [abs_zero] at h2
    exact h2
  obtain ⟨N, hN⟩ := eventually_atTop.mp (habs.eventually (gt_mem_nhds hpos))
  have := hN (T + N) (by omega)
  have := hgrow N
  linarith

/-- **Global convergence under a Lyapunov condition** (generic): if `G` is continuous on a
compact invariant interval `[a, b] ∋ k̄` and strictly reduces the distance to `k̄` at every other
point, every orbit starting in `[a, b]` converges to `k̄` (possibly oscillating). -/
theorem lyapunov_convergence {G : ℝ → ℝ} {a b kbar : ℝ} (hcont : ContinuousOn G (Icc a b))
    (hinv : ∀ x ∈ Icc a b, G x ∈ Icc a b) (hfix : G kbar = kbar)
    (hdec : ∀ x ∈ Icc a b, x ≠ kbar → |G x - kbar| < |x - kbar|) {k : ℕ → ℝ}
    (hk : ∀ t, k (t + 1) = G (k t)) (h0 : k 0 ∈ Icc a b) : Tendsto k atTop (𝓝 kbar) := by
  have hin : ∀ t, k t ∈ Icc a b := by
    intro t; induction t with
    | zero => exact h0
    | succ t ih => rw [hk t]; exact hinv _ ih
  have hanti : Antitone (fun t => |k t - kbar|) := by
    refine antitone_nat_of_succ_le (fun t => ?_)
    by_cases h : k t = kbar
    · rw [hk t, h, hfix]
    · rw [hk t]; exact (hdec _ (hin t) h).le
  obtain ⟨d, hd⟩ : ∃ d, Tendsto (fun t => |k t - kbar|) atTop (𝓝 d) :=
    ⟨_, tendsto_atTop_ciInf hanti ⟨0, by rintro _ ⟨t, rfl⟩; exact abs_nonneg _⟩⟩
  obtain ⟨x, hx, φ, hφ, hsub⟩ := isCompact_Icc.tendsto_subseq hin
  have h1 : Tendsto (fun j => |k (φ j) - kbar|) atTop (𝓝 |x - kbar|) :=
    ((continuous_abs.tendsto _).comp (hsub.sub_const kbar))
  have h2 : Tendsto (fun j => |k (φ j) - kbar|) atTop (𝓝 d) := hd.comp hφ.tendsto_atTop
  have hxd : |x - kbar| = d := tendsto_nhds_unique h1 h2
  have h3 : Tendsto (fun j => |k (φ j + 1) - kbar|) atTop (𝓝 |G x - kbar|) := by
    have hG : Tendsto (fun j => G (k (φ j))) atTop (𝓝 (G x)) :=
      ((hcont x hx).tendsto).comp (tendsto_nhdsWithin_iff.mpr ⟨hsub,
        Eventually.of_forall (fun j => hin _)⟩)
    refine ((continuous_abs.tendsto _).comp (hG.sub_const kbar)).congr (fun j => ?_)
    simp only [Function.comp_apply, hk]
  have h4 : Tendsto (fun j => |k (φ j + 1) - kbar|) atTop (𝓝 d) :=
    hd.comp ((tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop)
  have hGxd : |G x - kbar| = d := tendsto_nhds_unique h3 h4
  have hx0 : x = kbar := by
    by_contra hne
    have := hdec x hx hne
    linarith
  rw [hx0, sub_self, abs_zero] at hxd
  rw [← hxd] at hd
  have := (tendsto_zero_iff_abs_tendsto_zero _).mpr hd
  simpa using this.add_const kbar

/-- **Local stability of the Solow steady state for any `δ`, characterised**: at `k̄`,
`G'(k̄) < 1` always, so orbits near `k̄` converge whenever `G'(k̄) > -1`, while for
`G'(k̄) < -1` no orbit converges to `k̄` unless it lands on it exactly. -/
theorem solow_local_stability (hf : Neoclassical f) {s δ z kbar : ℝ} (hs : 0 < s)
    (hz : 0 < 1 + z) (hk : 0 < kbar) (hss : s * f kbar = (z + δ) * kbar) :
    (-1 < ((1 - δ) + s * deriv f kbar) / (1 + z) →
      ∃ ε > 0, ∀ k : ℕ → ℝ, (∀ t, k (t + 1) = solowMap f s δ z (k t)) →
        |k 0 - kbar| < ε → Tendsto k atTop (𝓝 kbar)) ∧
    (((1 - δ) + s * deriv f kbar) / (1 + z) < -1 → ∀ k : ℕ → ℝ,
      (∀ t, k (t + 1) = solowMap f s δ z (k t)) → (∀ t, k t ≠ kbar) →
        ¬ Tendsto k atTop (𝓝 kbar)) := by
  have hd := solowMap_hasDerivAt hf s δ z hk
  have hfix : solowMap f s δ z kbar = kbar := by
    unfold solowMap; rw [div_eq_iff (ne_of_gt hz)]; linarith
  have h1 := solow_slope_lt_one hf hs hz hk hss
  refine ⟨fun hlo => local_convergence_of_deriv hd hfix (abs_lt.mpr ⟨hlo, h1⟩),
    fun hhi k hk hne => no_convergence_of_deriv hd hfix ?_ hk hne⟩
  rw [lt_abs]; right; linarith

/-- **Global monotone convergence on `(0, b]` for any `δ`** when the Solow map is strictly
increasing on `(0, b]` with `k̄ ≤ b` (for `δ > 1` this is the region `s f'(k) ≥ δ - 1`): every
orbit starting in `(0, b]` stays there and converges monotonically to `k̄`. -/
theorem solow_convergence_on_interval (hf : Neoclassical f) {s δ z kbar b : ℝ} (hs : 0 < s)
    (hz : 0 < 1 + z) (hk : 0 < kbar) (hkb : kbar ≤ b) (hss : s * f kbar = (z + δ) * kbar)
    (hmono : StrictMonoOn (solowMap f s δ z) (Ioc 0 b)) {k : ℕ → ℝ}
    (hrec : ∀ t, k (t + 1) = solowMap f s δ z (k t)) (h0 : k 0 ∈ Ioc 0 b) :
    Tendsto k atTop (𝓝 kbar) ∧ (Monotone k ∨ Antitone k) := by
  set G := solowMap f s δ z
  have hfix : G kbar = kbar := by
    simp only [G]; unfold solowMap; rw [div_eq_iff (ne_of_gt hz)]; linarith
  have hratio := solowMap_ratio_anti_any hf (δ := δ) hs hz
  have hbelow : ∀ x, 0 < x → x < kbar → x < G x ∧ G x < kbar := by
    intro x hx hxk
    refine ⟨?_, ?_⟩
    · have h := hratio hx hk hxk
      simp only [G, hfix, div_self (ne_of_gt hk)] at h ⊢
      have h' : 1 < solowMap f s δ z x / x := by simpa [G, hfix, div_self (ne_of_gt hk)] using h
      rwa [lt_div_iff₀ hx, one_mul] at h'
    · have h := hmono ⟨hx, (hxk.trans_le hkb).le⟩ ⟨hk, hkb⟩ hxk
      rwa [hfix] at h
  have habove : ∀ x, kbar < x → x ≤ b → G x < x ∧ kbar < G x := by
    intro x hxk hxb
    have hx : 0 < x := hk.trans hxk
    refine ⟨?_, ?_⟩
    · have h := hratio hk hx hxk
      have h' : solowMap f s δ z x / x < 1 := by simpa [G, hfix, div_self (ne_of_gt hk)] using h
      rwa [div_lt_iff₀ hx, one_mul] at h'
    · have h := hmono ⟨hk, hkb⟩ ⟨hx, hxb⟩ hxk
      rwa [hfix] at h
  have hGc : ContinuousAt G kbar := (solowMap_continuousOn hf s δ z).continuousAt
    (Ioi_mem_nhds hk)
  rcases lt_trichotomy (k 0) kbar with hlt | heq | hgt
  · have hin : ∀ t, 0 < k t ∧ k t < kbar := by
      intro t; induction t with
      | zero => exact ⟨h0.1, hlt⟩
      | succ t ih =>
        rw [hrec t]; exact ⟨ih.1.trans (hbelow _ ih.1 ih.2).1, (hbelow _ ih.1 ih.2).2⟩
    have hsm : StrictMono k := strictMono_nat_of_lt_succ fun t => by
      rw [hrec t]; exact (hbelow _ (hin t).1 (hin t).2).1
    have hL := tendsto_atTop_ciSup hsm.monotone ⟨kbar, by rintro _ ⟨t, rfl⟩; exact (hin t).2.le⟩
    set L := ⨆ t, k t
    have hLk : L ≤ kbar := ciSup_le fun t => (hin t).2.le
    have hLpos : 0 < L := lt_of_lt_of_le (hin 0).1 (le_ciSup ⟨kbar, by
      rintro _ ⟨t, rfl⟩; exact (hin t).2.le⟩ 0)
    have hGL : ContinuousAt G L := (solowMap_continuousOn hf s δ z).continuousAt
      (Ioi_mem_nhds hLpos)
    have hfixL : G L = L := tendsto_nhds_unique ((hGL.tendsto.comp hL).congr
      (fun t => (hrec t).symm)) (hL.comp (tendsto_add_atTop_nat 1))
    have : L = kbar := by
      by_contra hne
      have := (hbelow L hLpos (lt_of_le_of_ne hLk hne)).1
      linarith
    exact ⟨this ▸ hL, Or.inl hsm.monotone⟩
  · have hconst : ∀ t, k t = kbar := by
      intro t; induction t with
      | zero => exact heq
      | succ t ih => rw [hrec t, ih, hfix]
    refine ⟨?_, Or.inl ?_⟩
    · rw [show k = fun _ => kbar from funext hconst]; exact tendsto_const_nhds
    · intro a c _; rw [hconst, hconst]
  · have hin : ∀ t, kbar < k t ∧ k t ≤ b := by
      intro t; induction t with
      | zero => exact ⟨hgt, h0.2⟩
      | succ t ih =>
        rw [hrec t]
        exact ⟨(habove _ ih.1 ih.2).2, ((habove _ ih.1 ih.2).1.le.trans ih.2)⟩
    have hsa : StrictAnti k := strictAnti_nat_of_succ_lt fun t => by
      rw [hrec t]; exact (habove _ (hin t).1 (hin t).2).1
    have hL := tendsto_atTop_ciInf hsa.antitone ⟨kbar, by rintro _ ⟨t, rfl⟩; exact (hin t).1.le⟩
    set L := ⨅ t, k t
    have hLk : kbar ≤ L := le_ciInf fun t => (hin t).1.le
    have hLpos : 0 < L := hk.trans_le hLk
    have hGL : ContinuousAt G L := (solowMap_continuousOn hf s δ z).continuousAt
      (Ioi_mem_nhds hLpos)
    have hfixL : G L = L := tendsto_nhds_unique ((hGL.tendsto.comp hL).congr
      (fun t => (hrec t).symm)) (hL.comp (tendsto_add_atTop_nat 1))
    have hLb : L ≤ b := (ciInf_le ⟨kbar, by rintro _ ⟨t, rfl⟩; exact (hin t).1.le⟩ 0).trans
      (hin 0).2
    have : L = kbar := by
      by_contra hne
      have := (habove L (lt_of_le_of_ne hLk (Ne.symm hne)) hLb).1
      linarith
    exact ⟨this ▸ hL, Or.inr hsa.antitone⟩

/-- **Cobb–Douglas with `δ > 1`**: the Solow map `[(1-δ)k + s k^α]/(1+z)` is strictly increasing
on `(0, b]`, `b = (sα/(δ-1))^{1/(1-α)}` (where `s f'(k) ≥ δ - 1`). -/
theorem cobbDouglas_mono_region {α s δ z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s)
    (hδ : 1 < δ) (hz : 0 < 1 + z) :
    StrictMonoOn (solowMap (fun k => k ^ α) s δ z)
      (Ioc 0 ((s * α / (δ - 1)) ^ (1 / (1 - α)))) := by
  set b := (s * α / (δ - 1)) ^ (1 / (1 - α))
  have hb : 0 < b := Real.rpow_pos_of_pos (div_pos (mul_pos hs hα) (by linarith)) _
  have hcont : ContinuousOn (solowMap (fun k => k ^ α) s δ z) (Ioc 0 b) :=
    (solowMap_continuousOn (neoclassical_rpow hα hα1) s δ z).mono (fun x hx => hx.1)
  refine strictMonoOn_of_deriv_pos (convex_Ioc 0 b) hcont (fun x hx => ?_)
  rw [interior_Ioc] at hx
  have hx0 : 0 < x := hx.1
  rw [(solowMap_hasDerivAt (neoclassical_rpow hα hα1) s δ z hx0).deriv, deriv_rpow hx0]
  apply div_pos _ hz
  -- `x < b` gives `s α x^{α-1} > δ - 1`
  have hbpow : b ^ (α - 1) = (δ - 1) / (s * α) := by
    have h1α : 1 - α ≠ 0 := by linarith
    simp only [b]
    rw [← Real.rpow_mul (div_pos (mul_pos hs hα) (by linarith)).le,
      show 1 / (1 - α) * (α - 1) = -1 by field_simp; ring, Real.rpow_neg_one, inv_div]
  have hxb : b ^ (α - 1) < x ^ (α - 1) := Real.rpow_lt_rpow_of_neg hx0 hx.2 (by linarith)
  rw [hbpow] at hxb
  have : δ - 1 < s * α * x ^ (α - 1) := by
    rw [div_lt_iff₀ (mul_pos hs hα)] at hxb; linarith
  nlinarith

/-- **Cobb–Douglas with `δ > 1`, global statement**: if `δ - 1 ≤ α(z + δ)` (equivalently
`G'(k̄) ≥ 0`) then `k̄ = (s/(z+δ))^{1/(1-α)} ≤ b`, and every orbit from `(0, b]` converges
monotonically to `k̄`. -/
theorem cobbDouglas_delta_gt_one_convergence {α s δ z : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hs : 0 < s) (hδ : 1 < δ) (hz : 0 < 1 + z) (hcond : δ - 1 ≤ α * (z + δ)) {k : ℕ → ℝ}
    (hrec : ∀ t, k (t + 1) = solowMap (fun k => k ^ α) s δ z (k t))
    (h0 : k 0 ∈ Ioc 0 ((s * α / (δ - 1)) ^ (1 / (1 - α)))) :
    Tendsto k atTop (𝓝 ((s / (z + δ)) ^ (1 / (1 - α)))) ∧ (Monotone k ∨ Antitone k) := by
  have hzd : 0 < z + δ := by linarith
  have hkb : (s / (z + δ)) ^ (1 / (1 - α)) ≤ (s * α / (δ - 1)) ^ (1 / (1 - α)) := by
    have h1α : 0 < 1 - α := by linarith
    apply Real.rpow_le_rpow (div_pos hs hzd).le _ (by positivity)
    rw [div_le_div_iff₀ hzd (by linarith)]
    nlinarith
  exact solow_convergence_on_interval (neoclassical_rpow hα hα1) hs hz
    (Real.rpow_pos_of_pos (div_pos hs hzd) _) hkb (cobbDouglas_steady hα1 hs hzd)
    (cobbDouglas_mono_region hα hα1 hs hδ hz) hrec h0

end ObstfeldRogoff.GlobalGrowth.SolowExtensions
