/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SmallOpenEconomyDynamics.FundamentalCurrentAccount
import SmallOpenEconomyDynamics.ConsumptionOptimality
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Consumption functions

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §2.1 (pp. 60–73),
§2.5.3 (pp. 114–116), Chapter 2 Exercise 2 (p. 125) and Supplement A.2 to Chapter 2
(pp. 718–721). Date 0 stands for the book's date `t`.

* **Finite horizon** (O&R (2.9), p. 62): with `β(1 + r) = 1` the constant consumption level that
  exhausts the budget over `T + 1` dates, and its limit (2.10) as `T → ∞`.
* **Annuity value** (footnote 2, p. 62): `C = rW/(1 + r)` is the only rule that keeps wealth
  constant under `W_{t+1} = (1 + r)(W_t − C_t)`.
* **Isoelastic utility** (O&R (2.15)–(2.16), pp. 70–71): derivative and strict concavity of
  `C^{1−1/σ}/(1 − 1/σ)` via `Real.rpow`; the Euler equation is equivalent to the growth rule
  `C_{s+1} = (1 + r)^σβ^σ C_s`; the consumption function
  `C = [1 − (1 + r)^{σ−1}β^σ]W = (r + ϑ)W/(1 + r)`; the Euler path is **optimal** (via
  `isOptimal_of_euler`) when `(1 + r)^{σ−1}β^σ < 1`, and **no optimum exists** when
  `(1 + r)^{σ−1}β^σ ≥ 1` (footnote 8), which requires `σ > 1`; consumption falls with `β`.
  The logarithmic case `σ = 1` is proved separately.
* **Dynamic programming** (Supplement A.2): `J(W) = Θ W^{1−1/σ}/(1 − 1/σ)` satisfies the Bellman
  equation, the maximum being attained uniquely at `C = [1 − β^σ(1 + r)^{σ−1}]W`. This is the
  fixed-point identity only; that `J` is the true value function is not claimed.
* **Endogenous labour** (§2.5.3): the partial derivatives of
  `[C^γ(L̄ − L)^{1−γ}]^{1−1/σ}/(1 − 1/σ)`, the leisure rule `L̄ − L = (1 − γ)C/(γw)`, the
  consumption-growth equation, and the upward tilt under rising wages when `σ < 1`, even with
  `β(1 + r) = 1`.
* **Uncertain lifetimes** (Exercise 2): `Σ_T φ^T(1 − φ)Σ_{s≤T} β^s u(C_s) = Σ_s (φβ)^s u(C_s)`,
  by an honest interchange of summation under absolute summability.
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions

open PresentValue FundamentalCurrentAccount ConsumptionOptimality Filter Topology Set Finset

/-! ### Finite horizon with `β(1 + r) = 1` (O&R (2.8)–(2.10)) -/

/-- **Finite-horizon consumption**, O&R (2.9), p. 62: a constant consumption level `C̄` that
satisfies the finite-horizon budget constraint (2.8) over dates `0, …, T`, with net output
`N = Y − G − I`, is `C̄ = [1/(1 − (1 + r)^{-(T+1)})] (r/(1 + r)) [(1 + r)B₀ + Σ (1 + r)^{-s} N_s]`.
Here `disc r ^ (T + 1) = (1 + r)^{-(T+1)}`. -/
theorem finite_horizon_consumption {r B0 Cbar : ℝ} (hr : 0 < r) (N : ℕ → ℝ) (T : ℕ)
    (hibc : ∑ s ∈ range (T + 1), disc r ^ s * Cbar =
      (1 + r) * B0 + ∑ s ∈ range (T + 1), disc r ^ s * N s) :
    Cbar = 1 / (1 - disc r ^ (T + 1)) * (r / (1 + r)) *
      ((1 + r) * B0 + ∑ s ∈ range (T + 1), disc r ^ s * N s) := by
  rw [← Finset.sum_mul, sum_range_disc_pow hr] at hibc
  rw [← hibc]
  have h1 : disc r ^ (T + 1) < 1 := pow_lt_one₀ (disc_pos (by linarith)).le (disc_lt_one hr)
    (Nat.succ_ne_zero T)
  have h2 : 1 - disc r ^ (T + 1) ≠ 0 := by linarith
  have h3 : (1 : ℝ) + r ≠ 0 := by linarith
  field_simp

/-- **The infinite-horizon limit**, O&R (2.9) → (2.10), p. 62: if `C_T` is the constant consumption
level that exhausts the budget over dates `0, …, T`, then as `T → ∞`, `C_T → rW₀/(1 + r)`, the
annuity value of wealth. Summability of discounted net output is assumed explicitly. -/
theorem finite_horizon_tendsto {r B0 : ℝ} (hr : 0 < r) {Y G I : ℕ → ℝ}
    (hN : Summable fun s => disc r ^ s * (Y s - G s - I s)) {C : ℕ → ℝ}
    (hC : ∀ T, ∑ s ∈ range (T + 1), disc r ^ s * C T =
      (1 + r) * B0 + ∑ s ∈ range (T + 1), disc r ^ s * (Y s - G s - I s)) :
    Tendsto C atTop (𝓝 (r / (1 + r) * wealth r B0 Y G I)) := by
  have hC' : C = fun T => 1 / (1 - disc r ^ (T + 1)) * (r / (1 + r)) *
      ((1 + r) * B0 + ∑ s ∈ range (T + 1), disc r ^ s * (Y s - G s - I s)) :=
    funext fun T => finite_horizon_consumption hr _ T (hC T)
  rw [hC']
  have hd0 : 0 ≤ disc r := (disc_pos (by linarith)).le
  have hpow : Tendsto (fun T : ℕ => disc r ^ (T + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hd0 (disc_lt_one hr)).comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun T : ℕ => 1 / (1 - disc r ^ (T + 1))) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hpow).inv₀ (by norm_num)
    simpa using this
  have hsum : Tendsto (fun T : ℕ => ∑ s ∈ range (T + 1), disc r ^ s * (Y s - G s - I s)) atTop
      (𝓝 (pv r fun s => Y s - G s - I s)) :=
    hN.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have := (hinv.mul_const (r / (1 + r))).mul ((tendsto_const_nhds (x := (1 + r) * B0)).add hsum)
  simpa [wealth] using this

/-! ### Annuity value keeps wealth constant (O&R footnote 2, p. 62) -/

/-- **Only the annuity rule keeps wealth unchanged**, O&R footnote 2, p. 62: with the wealth
transition `W_{t+1} = (1 + r)(W_t − C_t)` (Supplement A, SA(5)), next period's wealth equals
current wealth if and only if `C_t = rW_t/(1 + r)`. -/
theorem wealth_unchanged_iff {r W C : ℝ} (hr : 0 < 1 + r) :
    (1 + r) * (W - C) = W ↔ C = r / (1 + r) * W := by
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- **The annuity rule keeps wealth constant forever**, O&R footnote 2, p. 62: if
`W_{t+1} = (1 + r)(W_t − C_t)` and `C_t = rW_t/(1 + r)` at every date, then `W_t = W₀`. -/
theorem annuity_wealth_constant {r : ℝ} (hr : 0 < 1 + r) {W C : ℕ → ℝ}
    (hlaw : ∀ t, W (t + 1) = (1 + r) * (W t - C t)) (hC : ∀ t, C t = r / (1 + r) * W t)
    (t : ℕ) : W t = W 0 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [hlaw t, (wealth_unchanged_iff hr).2 (hC t), ih]

/-! ### Isoelastic (CRRA) utility (O&R (2.15)–(2.16), p. 70–71) -/

/-- Isoelastic period utility `u(C) = C^{1−1/σ}/(1 − 1/σ)`, O&R p. 70 (for `σ ≠ 1`). -/
noncomputable def crra (σ c : ℝ) : ℝ := c ^ (1 - σ⁻¹) / (1 - σ⁻¹)

/-- Marginal utility of the isoelastic utility, `u'(C) = C^{−1/σ}`, O&R p. 70. -/
noncomputable def crraMU (σ c : ℝ) : ℝ := c ^ (-σ⁻¹)

/-- Gross consumption growth `(1 + r)^σ β^σ` along the isoelastic Euler path, O&R (2.15). -/
noncomputable def crraGrowth (σ r β : ℝ) : ℝ := (1 + r) ^ σ * β ^ σ

/-- The ratio `(1 + r)^{σ−1} β^σ` of consumption growth to `1 + r`, O&R p. 71; it must be
below one for the consumption function (2.16) to be defined. -/
noncomputable def crraTilt (σ r β : ℝ) : ℝ := (1 + r) ^ (σ - 1) * β ^ σ

/-- The derivative of the isoelastic utility, O&R p. 70: `u'(C) = C^{−1/σ}` for `C > 0`,
`σ ≠ 1`. -/
theorem crra_hasDerivAt {σ c : ℝ} (hσ1 : σ ≠ 1) (hc : 0 < c) :
    HasDerivAt (crra σ) (crraMU σ c) c := by
  have hp : 1 - σ⁻¹ ≠ 0 := by
    intro h
    have : σ⁻¹ = 1 := by linarith
    exact hσ1 (by simpa using congrArg (·⁻¹) this)
  have h := (Real.hasDerivAt_rpow_const (p := 1 - σ⁻¹) (Or.inl hc.ne')).div_const (1 - σ⁻¹)
  unfold crra crraMU
  convert h using 1
  rw [mul_div_cancel_left₀ _ hp]
  ring_nf

/-- The isoelastic utility is strictly concave on `(0, ∞)` for every `σ > 0`, `σ ≠ 1`
(O&R p. 70): its derivative `C^{−1/σ}` is strictly decreasing. -/
theorem crra_strictConcaveOn {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) :
    StrictConcaveOn ℝ (Ioi 0) (crra σ) := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0)
  · intro x hx
    exact (crra_hasDerivAt hσ1 hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro x hx y hy hxy
    rw [(crra_hasDerivAt hσ1 hx).deriv, (crra_hasDerivAt hσ1 hy).deriv]
    exact Real.rpow_lt_rpow_of_neg hx hxy (by simpa using inv_pos.2 hσ)

/-- **Isoelastic Euler equation**, O&R (2.15), p. 70: for positive consumption levels,
`u'(C_s) = (1 + r)β u'(C_{s+1})` holds if and only if `C_{s+1} = (1 + r)^σ β^σ C_s`. -/
theorem crra_euler_iff {σ r β c c' : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hc : 0 < c) (hc' : 0 < c') :
    crraMU σ c = (1 + r) * β * crraMU σ c' ↔ c' = crraGrowth σ r β * c := by
  unfold crraMU crraGrowth
  have hg : 0 < (1 + r) ^ σ * β ^ σ * c := by positivity
  have hσ' : σ ≠ 0 := hσ.ne'
  constructor
  · intro h
    have hl := congrArg Real.log h
    rw [Real.log_rpow hc, Real.log_mul (by positivity) (by positivity), Real.log_rpow hc',
      Real.log_mul hr.ne' hβ.ne'] at hl
    apply Real.log_injOn_pos (mem_Ioi.2 hc') (mem_Ioi.2 hg)
    rw [Real.log_mul (by positivity) hc.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hr, Real.log_rpow hβ]
    field_simp at hl
    linarith
  · intro h
    apply Real.log_injOn_pos (mem_Ioi.2 (by positivity)) (mem_Ioi.2 (by positivity))
    rw [Real.log_rpow hc, Real.log_mul (by positivity) (by positivity), Real.log_rpow hc',
      Real.log_mul hr.ne' hβ.ne', h, Real.log_mul (by positivity) hc.ne',
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hr, Real.log_rpow hβ]
    field_simp
    ring

/-- The isoelastic Euler path is geometric, O&R (2.15), p. 70: a positive path satisfies the Euler
equation at every date if and only if `C_s = ((1 + r)^σ β^σ)^s C₀`. -/
theorem crra_euler_path_iff {σ r β : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    {C : ℕ → ℝ} (hC : ∀ s, 0 < C s) :
    (∀ s, crraMU σ (C s) = (1 + r) * β * crraMU σ (C (s + 1))) ↔
      ∀ s, C s = crraGrowth σ r β ^ s * C 0 := by
  constructor
  · intro h s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [(crra_euler_iff hσ hr hβ (hC s) (hC (s + 1))).1 (h s), ih, pow_succ]
      ring
  · intro h s
    refine (crra_euler_iff hσ hr hβ (hC s) (hC (s + 1))).2 ?_
    rw [h (s + 1), h s, pow_succ]
    ring

/-- Consumption growth over `1 + r`: `(1 + r)^σ β^σ = (1 + r) · (1 + r)^{σ−1} β^σ`. -/
theorem crraGrowth_eq {σ r β : ℝ} (hr : 0 < 1 + r) :
    crraGrowth σ r β = (1 + r) * crraTilt σ r β := by
  unfold crraGrowth crraTilt
  rw [Real.rpow_sub_one hr.ne']
  field_simp

/-- **The isoelastic consumption function**, O&R (2.16), p. 71: if consumption follows the Euler
path `C_s = ((1 + r)^σ β^σ)^s C₀`, `(1 + r)^{σ−1}β^σ < 1` and the budget constraint
`PV(C) = W₀` holds, then `C₀ = [1 − (1 + r)^{σ−1}β^σ] W₀ = (r + ϑ)W₀/(1 + r)` with
`ϑ = 1 − (1 + r)^σ β^σ`. Derived from `geometric_consumption_level`. -/
theorem crra_consumption_function {σ r β C0 W : ℝ} (hr : 0 < 1 + r) (hβ : 0 ≤ β)
    (htilt : crraTilt σ r β < 1) (hibc : pv r (fun s => crraGrowth σ r β ^ s * C0) = W) :
    C0 = (1 - crraTilt σ r β) * W ∧ C0 = (r + (1 - crraGrowth σ r β)) / (1 + r) * W := by
  have hγ0 : 0 ≤ crraGrowth σ r β :=
    mul_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hβ _)
  have hγr : crraGrowth σ r β < 1 + r := by
    rw [crraGrowth_eq hr]
    nlinarith
  have h := geometric_consumption_level hr hγ0 hγr hibc
  refine ⟨?_, ?_⟩
  · rw [h, crraGrowth_eq hr]
    field_simp
  · rw [h]
    ring_nf

/-- **The isoelastic Euler path is optimal**, O&R (2.15)–(2.16), pp. 70–71: with `β > 0`,
`1 + r > 0`, `σ > 0`, `σ ≠ 1`, `(1 + r)^{σ−1}β^σ < 1` and `W₀ > 0`, the path
`C_s = ((1 + r)^σ β^σ)^s [1 − (1 + r)^{σ−1}β^σ] W₀` is optimal among all admissible paths.
Its lifetime utility is summable because `β u(C_{s+1})/u(C_s)`-ratios equal
`β((1 + r)^σβ^σ)^{1−1/σ} = (1 + r)^{σ−1}β^σ < 1`; the proof applies `isOptimal_of_euler`. -/
theorem crra_isOptimal {σ r β W : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hr : 0 < 1 + r) (hβ : 0 < β)
    (htilt : crraTilt σ r β < 1) (hW : 0 < W) :
    IsOptimal (crra σ) β r W (fun s => crraGrowth σ r β ^ s * ((1 - crraTilt σ r β) * W)) := by
  set γ := crraGrowth σ r β with hγdef
  set κ := crraTilt σ r β with hκdef
  set C0 := (1 - κ) * W with hC0
  have hγ : 0 < γ := mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hβ _)
  have hκpos : 0 < κ := mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hβ _)
  have hκ0 : 0 ≤ κ := hκpos.le
  have hC0pos : 0 < C0 := mul_pos (by linarith) hW
  have hd : ∀ s : ℕ, disc r ^ s * (γ ^ s * C0) = κ ^ s * C0 := by
    intro s
    have hγeq : γ = (1 + r) * κ := crraGrowth_eq hr
    have h1 := one_add_mul_disc hr
    calc disc r ^ s * (γ ^ s * C0) = ((1 + r) * disc r) ^ s * κ ^ s * C0 := by
          rw [hγeq, mul_pow, mul_pow]; ring
      _ = κ ^ s * C0 := by rw [h1, one_pow, one_mul]
  -- utility along the path is geometric with ratio `κ`
  have hβγ : β * γ ^ (1 - σ⁻¹) = κ := by
    apply Real.log_injOn_pos (mem_Ioi.2 (mul_pos hβ (Real.rpow_pos_of_pos hγ _)))
      (mem_Ioi.2 hκpos)
    rw [hγdef, hκdef]
    unfold crraGrowth crraTilt
    rw [Real.log_mul hβ.ne' (by positivity), Real.log_rpow (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hr, Real.log_rpow hβ,
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hr, Real.log_rpow hβ]
    field_simp
    ring
  have hu : ∀ s : ℕ, β ^ s * crra σ (γ ^ s * C0) = κ ^ s * (C0 ^ (1 - σ⁻¹) / (1 - σ⁻¹)) := by
    intro s
    have hpow : (γ ^ s) ^ (1 - σ⁻¹) = (γ ^ (1 - σ⁻¹)) ^ s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hγ.le, mul_comm, Real.rpow_mul hγ.le,
        Real.rpow_natCast]
    unfold crra
    rw [Real.mul_rpow (pow_nonneg hγ.le s) hC0pos.le, hpow, ← hβγ, mul_pow]
    ring
  have hpv : Summable fun s => disc r ^ s * (γ ^ s * C0) := by
    simp_rw [hd]
    exact (summable_geometric_of_lt_one hκ0 htilt).mul_right _
  refine isOptimal_of_euler (u' := crraMU σ) hβ hr (crra_strictConcaveOn hσ hσ1).concaveOn
    (fun c hc => crra_hasDerivAt hσ1 hc) ⟨fun s => by positivity, hpv, ?_, ?_⟩ ?_ ?_ ?_
  · simp_rw [hu]
    exact (summable_geometric_of_lt_one hκ0 htilt).mul_right _
  · exact le_of_eq (by
      unfold pv
      simp_rw [hd]
      rw [tsum_mul_right, tsum_geometric_of_lt_one hκ0 htilt, hC0]
      field_simp [show (1 : ℝ) - κ ≠ 0 by linarith])
  · unfold pv
    simp_rw [hd]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hκ0 htilt, hC0]
    field_simp [show (1 : ℝ) - κ ≠ 0 by linarith]
  · exact Real.rpow_nonneg (by positivity) _
  · exact (crra_euler_path_iff hσ hr hβ (fun s => by positivity)).2 fun s => by
      simp only [pow_zero, one_mul, hγdef]

/-- **No optimum when `(1 + r)^{σ−1}β^σ ≥ 1`**, O&R p. 71 and footnote 8: then no admissible path
is optimal, for any wealth. An optimum would satisfy the Euler equation, so
`C_s = ((1 + r)^σβ^σ)^s C₀`, and its discounted terms `((1 + r)^{σ−1}β^σ)^s C₀ ≥ C₀ > 0` would not
be summable: "it is always possible to do a little better". -/
theorem crra_no_optimum {σ r β W : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hr : 0 < 1 + r) (hβ : 0 < β)
    (htilt : 1 ≤ crraTilt σ r β) (C : ℕ → ℝ) : ¬ IsOptimal (crra σ) β r W C := by
  intro hopt
  have he := euler_of_optimal (u' := crraMU σ) hβ hr (fun c hc => crra_hasDerivAt hσ1 hc) hopt
  obtain ⟨⟨hCpos, hCpv, -, -⟩, -⟩ := hopt
  have hpath := (crra_euler_path_iff hσ hr hβ hCpos).1 he
  have hge : ∀ s : ℕ, C 0 ≤ disc r ^ s * C s := by
    intro s
    have h1 := one_add_mul_disc hr
    have e : disc r ^ s * C s = crraTilt σ r β ^ s * C 0 := by
      calc disc r ^ s * C s = ((1 + r) * disc r) ^ s * crraTilt σ r β ^ s * C 0 := by
            rw [hpath s, crraGrowth_eq hr, mul_pow, mul_pow]; ring
        _ = crraTilt σ r β ^ s * C 0 := by rw [h1, one_pow, one_mul]
    rw [e]
    exact le_mul_of_one_le_left (hCpos 0).le (one_le_pow₀ htilt)
  have ht := hCpv.tendsto_atTop_zero
  have := ge_of_tendsto ht (Eventually.of_forall hge)
  linarith [hCpos 0]

/-- **O&R footnote 8, p. 71**: with `0 < β < 1`, `r > 0` and `σ > 0`, the inequality
`(1 + r)^{σ−1}β^σ ≥ 1` (in particular the book's `> 1`) is possible only if `σ > 1`. -/
theorem one_lt_sigma_of_one_le_tilt {σ r β : ℝ} (hσ : 0 < σ) (hr : 0 < r) (hβ0 : 0 < β)
    (hβ1 : β < 1) (htilt : 1 ≤ crraTilt σ r β) : 1 < σ := by
  by_contra h
  push Not at h
  have h1 : (1 + r) ^ (σ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
    (by linarith)
  have h2 : β ^ σ < 1 := Real.rpow_lt_one hβ0.le hβ1 hσ
  have h3 : 0 ≤ (1 + r) ^ (σ - 1) := Real.rpow_nonneg (by linarith) _
  unfold crraTilt at htilt
  nlinarith [Real.rpow_nonneg hβ0.le σ]

/-- **Consumption falls with patience**, O&R p. 71: given `r` (and hence wealth `W₀ > 0`),
isoelastic consumption `C₀ = [1 − (1 + r)^{σ−1}β^σ] W₀` is strictly decreasing in `β > 0`. -/
theorem crra_consumption_strictAnti_beta {σ r W : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hW : 0 < W) : StrictAntiOn (fun β => (1 - crraTilt σ r β) * W) (Ioi 0) := by
  intro β1 hβ1 β2 _ h12
  have h := Real.rpow_lt_rpow (le_of_lt hβ1) h12 hσ
  have hp : 0 < (1 + r) ^ (σ - 1) := Real.rpow_pos_of_pos hr _
  simp only [crraTilt]
  nlinarith [mul_lt_mul_of_pos_left h hp]

/-- **The logarithmic case `σ = 1`**, O&R pp. 63 and 70–71: with `u = log`, `0 < β < 1` and
`W₀ > 0`, the path `C_s = ((1 + r)β)^s (1 − β) W₀` is optimal. This is the limit `σ → 1` of
(2.16): consumption is the fraction `1 − β` of wealth, whatever `r`. -/
theorem log_isOptimal {r β W : ℝ} (hr : 0 < 1 + r) (hβ0 : 0 < β) (hβ1 : β < 1) (hW : 0 < W) :
    IsOptimal Real.log β r W (fun s => ((1 + r) * β) ^ s * ((1 - β) * W)) := by
  set C0 := (1 - β) * W with hC0
  have hC0pos : 0 < C0 := mul_pos (by linarith) hW
  have hk : 0 < (1 + r) * β := mul_pos hr hβ0
  have hd : ∀ s : ℕ, disc r ^ s * (((1 + r) * β) ^ s * C0) = β ^ s * C0 := by
    intro s
    have h1 := one_add_mul_disc hr
    calc disc r ^ s * (((1 + r) * β) ^ s * C0) = ((1 + r) * disc r) ^ s * β ^ s * C0 := by
          rw [mul_pow, mul_pow]; ring
      _ = β ^ s * C0 := by rw [h1, one_pow, one_mul]
  have hu : ∀ s : ℕ, β ^ s * Real.log (((1 + r) * β) ^ s * C0) =
      Real.log ((1 + r) * β) * ((s : ℝ) ^ 1 * β ^ s) + Real.log C0 * β ^ s := by
    intro s
    rw [Real.log_mul (pow_pos hk s).ne' hC0pos.ne', Real.log_pow]
    ring
  have hg := summable_geometric_of_lt_one hβ0.le hβ1
  have hpv : Summable fun s => disc r ^ s * (((1 + r) * β) ^ s * C0) := by
    simp_rw [hd]
    exact hg.mul_right _
  have hpveq : pv r (fun s => ((1 + r) * β) ^ s * C0) = W := by
    unfold pv
    simp_rw [hd]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0.le hβ1, hC0]
    field_simp [show (1 : ℝ) - β ≠ 0 by linarith]
  refine isOptimal_of_euler (u' := fun c => c⁻¹) hβ0 hr strictConcaveOn_log_Ioi.concaveOn
    (fun c hc => Real.hasDerivAt_log hc.ne') ⟨fun s => by positivity, hpv, ?_, hpveq.le⟩ hpveq
    (by positivity) ?_
  · simp_rw [hu]
    have hnorm : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
    have hn : Summable fun n : ℕ => (n : ℝ) ^ 1 * β ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
    exact (hn.mul_left _).add (hg.mul_left _)
  · intro s
    rw [pow_succ]
    field_simp

/-! ### Dynamic programming: the isoelastic value function (Supplement A.2, pp. 718–721) -/

/-- Discounted utility of consumption growth: `β((1 + r)^σβ^σ)^{1−1/σ} = (1 + r)^{σ−1}β^σ`
(Supplement A.2, p. 721, and O&R p. 71). -/
theorem beta_mul_crraGrowth_rpow {σ r β : ℝ} (hσ : σ ≠ 0) (hr : 0 < 1 + r) (hβ : 0 < β) :
    β * crraGrowth σ r β ^ (1 - σ⁻¹) = crraTilt σ r β := by
  unfold crraGrowth crraTilt
  apply Real.log_injOn_pos (mem_Ioi.2 (by positivity)) (mem_Ioi.2 (by positivity))
  rw [Real.log_mul hβ.ne' (by positivity), Real.log_rpow (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hr, Real.log_rpow hβ,
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hr, Real.log_rpow hβ]
  field_simp
  ring

/-- The marginal-utility counterpart: `(1 + r)β((1 + r)^σβ^σ)^{−1/σ} = 1`. -/
theorem crraGrowth_rpow_neg_inv {σ r β : ℝ} (hσ : σ ≠ 0) (hr : 0 < 1 + r) (hβ : 0 < β) :
    (1 + r) * β * crraGrowth σ r β ^ (-σ⁻¹) = 1 := by
  unfold crraGrowth
  apply Real.log_injOn_pos (mem_Ioi.2 (by positivity)) (mem_Ioi.2 one_pos)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hr.ne' hβ.ne',
    Real.log_rpow (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hr, Real.log_rpow hβ, Real.log_one]
  field_simp
  ring

/-- The coefficient `Θ = [1 − β^σ(1 + r)^{σ−1}]^{−1/σ}` of the isoelastic value function,
Supplement A.2, p. 721. -/
noncomputable def crraTheta (σ r β : ℝ) : ℝ := (1 - crraTilt σ r β) ^ (-σ⁻¹)

/-- The conjectured value function `J(W) = Θ W^{1−1/σ}/(1 − 1/σ)`, Supplement A.2, p. 720. -/
noncomputable def crraValue (σ r β W : ℝ) : ℝ := crraTheta σ r β * crra σ W

/-- **The Bellman right-hand side at the policy**, Supplement A.2, SA(7) and p. 721: with
`C = [1 − β^σ(1 + r)^{σ−1}]W`, `u(C) + βJ((1 + r)(W − C)) = J(W)` for `W > 0`. -/
theorem crra_bellman_fixed_point {σ r β W : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (htilt : crraTilt σ r β < 1) (hW : 0 < W) :
    crra σ ((1 - crraTilt σ r β) * W) +
      β * crraValue σ r β ((1 + r) * (W - (1 - crraTilt σ r β) * W)) = crraValue σ r β W := by
  set κ := 1 - crraTilt σ r β with hκ
  have hκpos : 0 < κ := by linarith
  have hγ : 0 < crraGrowth σ r β :=
    mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hβ _)
  have hD : (1 + r) * (W - κ * W) = crraGrowth σ r β * W := by
    rw [crraGrowth_eq hr, hκ]; ring
  have hκp : κ ^ (1 - σ⁻¹) = κ * crraTheta σ r β := by
    unfold crraTheta
    rw [← hκ, sub_eq_add_neg, Real.rpow_add hκpos, Real.rpow_one]
  have hb := beta_mul_crraGrowth_rpow hσ.ne' hr hβ
  unfold crraValue crra
  rw [hD, Real.mul_rpow hκpos.le hW.le, Real.mul_rpow hγ.le hW.le, hκp]
  have e : β * (crraTheta σ r β * (crraGrowth σ r β ^ (1 - σ⁻¹) * W ^ (1 - σ⁻¹) / (1 - σ⁻¹)))
      = crraTheta σ r β * (β * crraGrowth σ r β ^ (1 - σ⁻¹)) * (W ^ (1 - σ⁻¹) / (1 - σ⁻¹)) := by
    ring
  rw [e, hb]
  have e2 : crraTilt σ r β = 1 - κ := by rw [hκ]; ring
  rw [e2]
  ring

/-- **The policy strictly maximises the Bellman right-hand side**, Supplement A.2, SA(6)–SA(8):
for `0 < C < W`, `C ≠ [1 − β^σ(1 + r)^{σ−1}]W`, `u(C) + βJ((1 + r)(W − C)) < J(W)`. The proof uses
the tangent-line inequality of the strictly concave `u` at `C*` and at `(1 + r)(W − C*)`, and the
first-order condition SA(8) `u'(C*) = (1 + r)βJ'((1 + r)(W − C*))`. -/
theorem crra_bellman_strict_max {σ r β W C : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hr : 0 < 1 + r)
    (hβ : 0 < β) (htilt : crraTilt σ r β < 1) (hW : 0 < W) (hC0 : 0 < C) (hCW : C < W)
    (hne : C ≠ (1 - crraTilt σ r β) * W) :
    crra σ C + β * crraValue σ r β ((1 + r) * (W - C)) < crraValue σ r β W := by
  rw [← crra_bellman_fixed_point hσ hr hβ htilt hW]
  set κ := 1 - crraTilt σ r β with hκ
  set γ := crraGrowth σ r β with hγdef
  set Θ := crraTheta σ r β with hΘ
  have hκpos : 0 < κ := by linarith
  have hγ : 0 < γ := mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hβ _)
  have hΘpos : 0 < Θ := Real.rpow_pos_of_pos hκpos _
  have hCs : 0 < κ * W := mul_pos hκpos hW
  have hDs : (1 + r) * (W - κ * W) = γ * W := by
    rw [hγdef, crraGrowth_eq hr, hκ]; ring
  have hDspos : 0 < γ * W := mul_pos hγ hW
  have hDpos : 0 < (1 + r) * (W - C) := mul_pos hr (by linarith)
  have hconc := crra_strictConcaveOn hσ hσ1
  have t1 := strictConcave_lt_tangent hconc (mem_Ioi.2 hCs) (mem_Ioi.2 hC0) hne
    (crra_hasDerivAt hσ1 hCs)
  have t2 := concave_le_tangent' hconc.concaveOn (mem_Ioi.2 hDspos) (mem_Ioi.2 hDpos)
    (crra_hasDerivAt hσ1 hDspos)
  -- the first-order condition SA(8)
  have hfoc : crraMU σ (κ * W) = (1 + r) * β * Θ * crraMU σ (γ * W) := by
    unfold crraMU
    rw [Real.mul_rpow hκpos.le hW.le, Real.mul_rpow hγ.le hW.le]
    have h := crraGrowth_rpow_neg_inv hσ.ne' hr hβ
    rw [← hγdef] at h
    calc κ ^ (-σ⁻¹) * W ^ (-σ⁻¹) = Θ * W ^ (-σ⁻¹) := by rw [hΘ]; rfl
      _ = (1 + r) * β * γ ^ (-σ⁻¹) * Θ * W ^ (-σ⁻¹) := by rw [h, one_mul]
      _ = _ := by ring
  unfold crraValue
  rw [← hΘ, hDs]
  have t2' := mul_le_mul_of_nonneg_left t2 (mul_pos hβ hΘpos).le
  have key : crraMU σ (κ * W) * (C - κ * W) +
      β * Θ * (crraMU σ (γ * W) * ((1 + r) * (W - C) - γ * W)) = 0 := by
    rw [hfoc, ← hDs]; ring
  linarith

/-- **The isoelastic value function solves the Bellman equation**, Supplement A.2, SA(6)–SA(7),
p. 721: for `W > 0`, `J(W) = max_{0<C<W} {u(C) + βJ((1 + r)(W − C))}`, the maximum being attained
(uniquely, by `crra_bellman_strict_max`) at `C = [1 − β^σ(1 + r)^{σ−1}]W`. This is the fixed-point
identity only: that `J` is the true value function needs a separate verification argument. -/
theorem crra_bellman_isGreatest {σ r β W : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hr : 0 < 1 + r)
    (hβ : 0 < β) (htilt : crraTilt σ r β < 1) (hW : 0 < W) :
    IsGreatest {v | ∃ C, 0 < C ∧ C < W ∧ v = crra σ C + β * crraValue σ r β ((1 + r) * (W - C))}
      (crraValue σ r β W) := by
  have hκ0 : 0 < crraTilt σ r β :=
    mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hβ _)
  refine ⟨⟨(1 - crraTilt σ r β) * W, mul_pos (by linarith) hW, by nlinarith,
    (crra_bellman_fixed_point hσ hr hβ htilt hW).symm⟩, ?_⟩
  rintro v ⟨C, hC0, hCW, rfl⟩
  by_cases hne : C = (1 - crraTilt σ r β) * W
  · rw [hne, crra_bellman_fixed_point hσ hr hβ htilt hW]
  · exact (crra_bellman_strict_max hσ hσ1 hr hβ htilt hW hC0 hCW hne).le

/-- The book's form of the policy, Supplement A.2, SA(10): with `Θ` as above,
`W/(1 + β^σ(1 + r)^{σ−1}Θ^σ) = [1 − β^σ(1 + r)^{σ−1}]W`. -/
theorem crra_policy_formula {σ r β W : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (htilt : crraTilt σ r β < 1) :
    W / (1 + crraTilt σ r β * crraTheta σ r β ^ σ) = (1 - crraTilt σ r β) * W := by
  have hκpos : 0 < 1 - crraTilt σ r β := by linarith
  have hΘ : crraTheta σ r β ^ σ = (1 - crraTilt σ r β)⁻¹ := by
    unfold crraTheta
    rw [← Real.rpow_mul hκpos.le, neg_mul, inv_mul_cancel₀ hσ.ne', Real.rpow_neg_one]
  have hκ0 : 0 < crraTilt σ r β :=
    mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hβ _)
  rw [hΘ]
  field_simp
  ring

/-! ### Endogenous labour supply (O&R §2.5.3, pp. 114–116) -/

/-- Isoelastic utility over consumption and leisure `ℓ = L̄ − L`,
`u(C, ℓ) = [C^γ ℓ^{1−γ}]^{1−1/σ}/(1 − 1/σ)`, O&R p. 115. -/
noncomputable def labourUtility (σ γ C ℓ : ℝ) : ℝ :=
  (C ^ γ * ℓ ^ (1 - γ)) ^ (1 - σ⁻¹) / (1 - σ⁻¹)

/-- Marginal utility of consumption `u_C = γ C^{γ(1−1/σ)−1} ℓ^{(1−γ)(1−1/σ)}`, O&R (2.72). -/
noncomputable def labourMUC (σ γ C ℓ : ℝ) : ℝ :=
  γ * C ^ (γ * (1 - σ⁻¹) - 1) * ℓ ^ ((1 - γ) * (1 - σ⁻¹))

/-- Marginal utility of leisure `u_ℓ = (1 − γ) C^{γ(1−1/σ)} ℓ^{(1−γ)(1−1/σ)−1}`, O&R (2.73). -/
noncomputable def labourMUL (σ γ C ℓ : ℝ) : ℝ :=
  (1 - γ) * C ^ (γ * (1 - σ⁻¹)) * ℓ ^ ((1 - γ) * (1 - σ⁻¹) - 1)

/-- For positive arguments the utility factorises, `u = C^{γ(1−1/σ)} ℓ^{(1−γ)(1−1/σ)}/(1 − 1/σ)`. -/
theorem labourUtility_eq {σ γ C ℓ : ℝ} (hC : 0 < C) (hℓ : 0 < ℓ) :
    labourUtility σ γ C ℓ =
      C ^ (γ * (1 - σ⁻¹)) * ℓ ^ ((1 - γ) * (1 - σ⁻¹)) / (1 - σ⁻¹) := by
  unfold labourUtility
  rw [Real.mul_rpow (Real.rpow_nonneg hC.le _) (Real.rpow_nonneg hℓ.le _),
    ← Real.rpow_mul hC.le, ← Real.rpow_mul hℓ.le]

/-- `u_C` is the partial derivative of `u` in `C`, O&R p. 115 (for `C, ℓ > 0`, `σ ≠ 1`). -/
theorem labourUtility_hasDerivAt_C {σ γ C ℓ : ℝ} (hσ1 : σ ≠ 1) (hC : 0 < C) (hℓ : 0 < ℓ) :
    HasDerivAt (fun x => labourUtility σ γ x ℓ) (labourMUC σ γ C ℓ) C := by
  have hp : 1 - σ⁻¹ ≠ 0 := by
    intro h
    have : σ⁻¹ = 1 := by linarith
    exact hσ1 (by simpa using congrArg (·⁻¹) this)
  have h := ((Real.hasDerivAt_rpow_const (p := γ * (1 - σ⁻¹)) (Or.inl hC.ne')).mul_const
    (ℓ ^ ((1 - γ) * (1 - σ⁻¹)))).div_const (1 - σ⁻¹)
  have hev : (fun x => labourUtility σ γ x ℓ) =ᶠ[𝓝 C]
      fun x => x ^ (γ * (1 - σ⁻¹)) * ℓ ^ ((1 - γ) * (1 - σ⁻¹)) / (1 - σ⁻¹) := by
    filter_upwards [lt_mem_nhds hC] with x hx
    exact labourUtility_eq hx hℓ
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  unfold labourMUC
  rw [div_eq_iff hp]
  ring

/-- `u_ℓ` is the partial derivative of `u` in leisure `ℓ`, O&R p. 115. -/
theorem labourUtility_hasDerivAt_leisure {σ γ C ℓ : ℝ} (hσ1 : σ ≠ 1) (hC : 0 < C)
    (hℓ : 0 < ℓ) : HasDerivAt (fun y => labourUtility σ γ C y) (labourMUL σ γ C ℓ) ℓ := by
  have hp : 1 - σ⁻¹ ≠ 0 := by
    intro h
    have : σ⁻¹ = 1 := by linarith
    exact hσ1 (by simpa using congrArg (·⁻¹) this)
  have h := ((Real.hasDerivAt_rpow_const (p := (1 - γ) * (1 - σ⁻¹)) (Or.inl hℓ.ne')).const_mul
    (C ^ (γ * (1 - σ⁻¹)))).div_const (1 - σ⁻¹)
  have hev : (fun y => labourUtility σ γ C y) =ᶠ[𝓝 ℓ]
      fun y => C ^ (γ * (1 - σ⁻¹)) * y ^ ((1 - γ) * (1 - σ⁻¹)) / (1 - σ⁻¹) := by
    filter_upwards [lt_mem_nhds hℓ] with y hy
    exact labourUtility_eq hC hy
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  unfold labourMUL
  rw [div_eq_iff hp]
  ring

/-- **Intratemporal first-order condition**, O&R (2.73) and p. 115: with `0 < γ < 1`, wage
`w > 0` and `C, ℓ > 0`, `u_ℓ(C, ℓ) = u_C(C, ℓ) w` holds if and only if
`L̄ − L = ℓ = (1 − γ)C/(γw)`. -/
theorem labour_intratemporal_iff {σ γ C ℓ w : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hw : 0 < w)
    (hC : 0 < C) (hℓ : 0 < ℓ) :
    labourMUL σ γ C ℓ = labourMUC σ γ C ℓ * w ↔ ℓ = (1 - γ) * C / (γ * w) := by
  have hM : 0 < labourMUC σ γ C ℓ := by unfold labourMUC; positivity
  have h1γ : (1 : ℝ) - γ ≠ 0 := by linarith
  have key : labourMUL σ γ C ℓ = labourMUC σ γ C ℓ * ((1 - γ) * C / (γ * ℓ)) := by
    unfold labourMUL labourMUC
    rw [Real.rpow_sub_one hC.ne', Real.rpow_sub_one hℓ.ne']
    field_simp
  rw [key]
  constructor
  · intro h
    have h2 := mul_left_cancel₀ hM.ne' h
    field_simp at h2 ⊢
    linarith
  · intro h
    congr 1
    rw [h]
    field_simp

/-- **Consumption growth with endogenous labour**, O&R pp. 115: combining the Euler equation
(2.72) `u_C(C_s, ℓ_s) = (1 + r)β u_C(C_{s+1}, ℓ_{s+1})` with the leisure rule
`ℓ = (1 − γ)C/(γw)` gives `C_{s+1} = (w_s/w_{s+1})^{(1−γ)(σ−1)} (1 + r)^σ β^σ C_s`. -/
theorem labour_consumption_growth {σ γ r β C0 C1 ℓ0 ℓ1 w0 w1 : ℝ} (hσ : 0 < σ) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hr : 0 < 1 + r) (hβ : 0 < β) (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hℓ0 : ℓ0 = (1 - γ) * C0 / (γ * w0))
    (hℓ1 : ℓ1 = (1 - γ) * C1 / (γ * w1))
    (heuler : labourMUC σ γ C0 ℓ0 = (1 + r) * β * labourMUC σ γ C1 ℓ1) :
    C1 = (w0 / w1) ^ ((1 - γ) * (σ - 1)) * (1 + r) ^ σ * β ^ σ * C0 := by
  have h1γ : 0 < 1 - γ := by linarith
  subst hℓ0 hℓ1
  unfold labourMUC at heuler
  have hl := congrArg Real.log heuler
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hγ0.ne' (by positivity),
    Real.log_rpow hC0, Real.log_rpow (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_mul h1γ.ne' hC0.ne', Real.log_mul hγ0.ne' hw0.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul hγ0.ne' (by positivity),
    Real.log_rpow hC1,
    Real.log_rpow (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_mul h1γ.ne' hC1.ne', Real.log_mul hγ0.ne' hw1.ne'] at hl
  apply Real.log_injOn_pos (mem_Ioi.2 hC1) (mem_Ioi.2 (by positivity))
  rw [Real.log_mul (by positivity) hC0.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity),
    Real.log_rpow hr, Real.log_rpow hβ, Real.log_div hw0.ne' hw1.ne']
  field_simp at hl
  linear_combination hl

/-- **Rising wages tilt consumption up**, O&R p. 115: if `σ < 1`, `γ < 1`, `β = 1/(1 + r)` and
the real wage rises, `w_{s+1} > w_s`, then the growth equation of `labour_consumption_growth`
gives `C_{s+1} > C_s`: a flat path is no longer optimal. -/
theorem labour_tilt_up_of_wage_growth {σ γ r β C0 C1 w0 w1 : ℝ} (hσ1 : σ < 1)
    (hγ1 : γ < 1) (hr : 0 < 1 + r) (hβ : 0 < β) (hβr : β * (1 + r) = 1)
    (hC0 : 0 < C0) (hw0 : 0 < w0) (hw : w0 < w1)
    (hgrowth : C1 = (w0 / w1) ^ ((1 - γ) * (σ - 1)) * (1 + r) ^ σ * β ^ σ * C0) :
    C0 < C1 := by
  have hk : (1 + r) ^ σ * β ^ σ = 1 := by
    rw [← Real.mul_rpow hr.le hβ.le, mul_comm, hβr, Real.one_rpow]
  have hq : 1 < (w0 / w1) ^ ((1 - γ) * (σ - 1)) :=
    Real.one_lt_rpow_of_pos_of_lt_one_of_neg (div_pos hw0 (by linarith))
      ((div_lt_one (by linarith)).2 hw) (mul_neg_of_pos_of_neg (by linarith) (by linarith))
  rw [hgrowth, mul_assoc _ ((1 + r) ^ σ), hk, mul_one]
  nlinarith

/-! ### Uncertain lifetimes (O&R Chapter 2, Exercise 2, p. 125) -/

/-- Survival weights summed over lifetimes of length `T ≥ s`:
`Σ_T [s ≤ T] φ^T (1 − φ) c = φ^s c` for `0 ≤ φ < 1` (O&R Exercise 2(b), p. 125). -/
theorem hasSum_survival_weights {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (s : ℕ) (c : ℝ) :
    HasSum (fun T => if s ≤ T then φ ^ T * (1 - φ) * c else 0) (φ ^ s * c) := by
  rw [← hasSum_nat_add_iff' s]
  have h0 : ∑ i ∈ range s, (if s ≤ i then φ ^ i * (1 - φ) * c else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [ite_eq_right (by simpa using Finset.mem_range.1 hi)]
  rw [h0, sub_zero]
  have hg := (hasSum_geometric_of_lt_one hφ0 hφ1).mul_left (φ ^ s * (1 - φ) * c)
  have hne : (1 : ℝ) - φ ≠ 0 := by linarith
  convert hg using 1
  · funext n
    rw [ite_eq_left (Nat.le_add_left s n), pow_add]
    ring
  · field_simp

/-- **Expected utility with uncertain lifetimes**, O&R Chapter 2, Exercise 2, p. 125: if the
individual survives each period with probability `0 ≤ φ < 1`, expected utility
`Σ_T φ^T(1 − φ) Σ_{s=0}^{T} a_s` equals `Σ_s φ^s a_s`, where `a_s = β^s u(C_s)`. The interchange of
the two sums is justified by the explicit absolute-summability hypothesis
`Σ φ^s |a_s| < ∞`. -/
theorem uncertain_lifetime_sum {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) {a : ℕ → ℝ}
    (ha : Summable fun s => φ ^ s * |a s|) :
    ∑' T, φ ^ T * (1 - φ) * ∑ s ∈ range (T + 1), a s = ∑' s, φ ^ s * a s := by
  set F : ℕ × ℕ → ℝ := fun p => if p.1 ≤ p.2 then φ ^ p.2 * (1 - φ) * a p.1 else 0 with hF
  have h1φ : 0 ≤ 1 - φ := by linarith
  have habs : ∀ p : ℕ × ℕ, |F p| = if p.1 ≤ p.2 then φ ^ p.2 * (1 - φ) * |a p.1| else 0 := by
    intro p
    simp only [hF]
    split_ifs
    · rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hφ0 _), abs_of_nonneg h1φ]
    · simp
  have hsumabs : Summable fun p => |F p| := by
    rw [summable_prod_of_nonneg (fun p => abs_nonneg (F p))]
    refine ⟨fun s => ?_, ?_⟩
    · simp_rw [habs]
      exact (hasSum_survival_weights hφ0 hφ1 s |a s|).summable
    · simp_rw [habs]
      simpa only [(hasSum_survival_weights hφ0 hφ1 _ _).tsum_eq] using ha
  have hsum : Summable F := hsumabs.of_abs
  have hcomm := hsum.tsum_comm (f := fun s T => F (s, T))
  simp only [hF] at hcomm
  have hL : ∀ T, ∑' s, (if s ≤ T then φ ^ T * (1 - φ) * a s else 0) =
      φ ^ T * (1 - φ) * ∑ s ∈ range (T + 1), a s := by
    intro T
    rw [tsum_eq_sum (s := range (T + 1)), Finset.mul_sum]
    · refine Finset.sum_congr rfl fun s hs => ?_
      rw [ite_eq_left (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))]
    · intro s hs
      rw [ite_eq_right]
      simpa [Nat.lt_succ_iff] using hs
  have hR : ∀ s, ∑' T, (if s ≤ T then φ ^ T * (1 - φ) * a s else 0) = φ ^ s * a s :=
    fun s => (hasSum_survival_weights hφ0 hφ1 s (a s)).tsum_eq
  simp_rw [hL, hR] at hcomm
  exact hcomm

/-- **The survival-adjusted discount factor**, O&R Chapter 2, Exercise 2(b), p. 125: with
survival probability `0 ≤ φ < 1` and `β ≥ 0`,
`E U = Σ_T φ^T(1 − φ) Σ_{s=0}^{T} β^s u(C_s) = Σ_s (φβ)^s u(C_s)`, provided
`Σ (φβ)^s |u(C_s)| < ∞`. -/
theorem expected_utility_uncertain_lifetime {φ β : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hβ : 0 ≤ β)
    (u : ℝ → ℝ) (C : ℕ → ℝ) (hsum : Summable fun s => (φ * β) ^ s * |u (C s)|) :
    ∑' T, φ ^ T * (1 - φ) * ∑ s ∈ range (T + 1), β ^ s * u (C s) =
      ∑' s, (φ * β) ^ s * u (C s) := by
  have ha : Summable fun s => φ ^ s * |β ^ s * u (C s)| := by
    refine hsum.congr fun s => ?_
    rw [abs_mul, abs_of_nonneg (pow_nonneg hβ _), mul_pow, mul_assoc]
  rw [uncertain_lifetime_sum hφ0 hφ1 ha]
  exact tsum_congr fun s => by rw [mul_pow, mul_assoc]

end ObstfeldRogoff.SmallOpenEconomyDynamics.ConsumptionFunctions
