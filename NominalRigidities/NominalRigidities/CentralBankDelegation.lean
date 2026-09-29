/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.BarroGordon
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Institutional resolutions: the conservative central banker and the Walsh contract

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §9.5.2
(pp. 641–644), eqs. (40)–(44), Exercise 4 (p. 658) and the application "Central bank
independence and inflation" (pp. 646–647).

* (40)–(41): a banker with weight `c = χᶜᴮ > 0` produces the unique equilibrium
  `πᵉ = k/c`, `π = k/c + z/(1 + c)`; society's expected loss is
  `L(c) = k² + χk²/c² + (c² + χ)σ²/(1 + c)²`, with
  `L′(c) = 2σ²(c − χ)/(1 + c)³ − 2χk²/c³`.
* Rogoff's theorem (p. 642), in full: for `k > 0`, `σ² > 0`, `L` has a **unique** global
  minimiser `c*` on `(0, ∞)`, and `χ < c* < ∞`; `L` is strictly decreasing on `(0, c*]` and
  strictly increasing on `[c*, ∞)` (the unimodality proof goes through the strictly
  increasing function `h(c) = (c − χ)c³/(1 + c)³` and the intermediate value theorem);
  `c*` is characterised by `σ²h(c*) = χk²` and increases with `k²/σ²`;
  `L(c*) < L(χ) = V_D` and `L(c*) < lim_{c→∞} L = k² + σ²`, but `L(c) > V_C` for every `c`.
  Degenerate cases: `k = 0` gives `c* = χ`; `σ² = 0` gives `L` strictly decreasing with
  infimum `k²` not attained ("`χᶜᴮ = ∞`").
* Walsh (42)–(44): the linear contract `2ωπ` shifts the equilibrium to
  `πᵉ = (k − ω)/χ`, `π = (k − ω)/χ + z/(1 + χ)`; society's loss is `V_C + (k − ω)²/χ`, so
  `ω = k` is the unique optimal contract and implements the commitment rule (36).
* Exercise 4: with a random weight `λ` on the bonus (`E λ = 1`, `Var λ = σ_λ²`, `λ`
  uncorrelated with `z`): unique equilibrium, expected social loss
  `k² + (k − ω)²/χ + χσ_z²/(1 + χ) + ω²σ_λ²/(1 + χ)`, unique optimum
  `ω* = k(1 + χ)/(1 + χ + χσ_λ²) < k`.
* CBI regression (p. 646): the slope's t-ratio `6.02/2.35` exceeds the 5% critical value
  `2.131` (15 degrees of freedom), so "significant" is correct.
-/

namespace ObstfeldRogoff.NominalRigidities.CentralBankDelegation

open Filter Topology Set
open ObstfeldRogoff.NominalRigidities.BarroGordon

variable {S : Type*} [Fintype S]

/-! ## The conservative central banker, (40)–(41) -/

/-- O&R (40)–(41), pp. 641–642: with a banker of weight `c > 0` the one-shot equilibrium is
unique: `πᵉ = k/c` and `π = k/c + z/(1 + c)`. -/
theorem conservative_eqm_iff (p z : S → ℝ) (c k : ℝ) (hc : 0 < c) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) (π : S → ℝ) (πe : ℝ) :
    IsOneShotEqm p z c k π πe ↔ πe = k / c ∧ ∀ s, π s = k / c + z s / (1 + c) :=
  oneShot_eqm_iff p z c k hc h1 hz π πe

/-- O&R p. 642: society's expected loss when the banker has weight `c`,
`L(c) = k² + χk²/c² + (c² + χ)σ²/(1 + c)²`. -/
noncomputable def socialLoss (χ k σ2 c : ℝ) : ℝ :=
  k ^ 2 + χ * k ^ 2 / c ^ 2 + (c ^ 2 + χ) * σ2 / (1 + c) ^ 2

/-- O&R (41), p. 642: society's expected loss (31) under the banker's equilibrium policy is
`socialLoss`. -/
theorem expLoss_conservative (p z : S → ℝ) (χ k c : ℝ) (hc : 0 < c) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    expLoss p z χ k (discretionRule c k z) = socialLoss χ k (varZ p z) c := by
  have hc1 : 0 < 1 + c := by linarith
  have hE : expect p (discretionRule c k z) = k / c := by
    have : expect p (discretionRule c k z) =
        expect p (fun s => k / c + (1 / (1 + c)) * z s) := by
      unfold expect discretionRule
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, expect_add, expect_const p h1, expect_const_mul, hz, mul_zero, add_zero]
  rw [expLoss_decomp p z χ k h1 hz, hE]
  have e1 : expect p (fun s => (discretionRule c k z s - k / c - z s) ^ 2) =
      c ^ 2 / (1 + c) ^ 2 * varZ p z := by
    unfold varZ
    rw [← expect_const_mul]
    unfold expect discretionRule
    refine Finset.sum_congr rfl fun s _ => ?_
    field_simp
    ring
  have e2 : expect p (fun s => (discretionRule c k z s - k / c) ^ 2) =
      1 / (1 + c) ^ 2 * varZ p z := by
    unfold varZ
    rw [← expect_const_mul]
    unfold expect discretionRule
    refine Finset.sum_congr rfl fun s _ => ?_
    field_simp
    ring
  rw [e1, e2]
  unfold socialLoss
  field_simp
  ring

/-- O&R p. 642: society's own weight (`c = χ`) reproduces discretion, `L(χ) = V_D`. -/
theorem socialLoss_self (χ k σ2 : ℝ) (hχ : 0 < χ) :
    socialLoss χ k σ2 χ = valueDiscretion χ k σ2 := by
  unfold socialLoss valueDiscretion
  have : (0 : ℝ) < 1 + χ := by linarith
  field_simp
  ring

/-- O&R p. 642: the derivative `L′(c) = 2σ²(c − χ)/(1 + c)³ − 2χk²/c³` for `c > 0`. -/
theorem hasDerivAt_socialLoss (χ k σ2 c : ℝ) (hc : 0 < c) :
    HasDerivAt (socialLoss χ k σ2)
      (2 * σ2 * (c - χ) / (1 + c) ^ 3 - 2 * χ * k ^ 2 / c ^ 3) c := by
  have hc1 : 0 < 1 + c := by linarith
  have hA : HasDerivAt (fun x : ℝ => χ * k ^ 2 / x ^ 2)
      (-(χ * k ^ 2 * (2 * c)) / (c ^ 2) ^ 2) c :=
    ((hasDerivAt_const c (χ * k ^ 2)).div (hasDerivAt_pow 2 c)
      (pow_ne_zero 2 hc.ne')).congr_deriv (by norm_num)
  have hn : HasDerivAt (fun x : ℝ => (x ^ 2 + χ) * σ2) ((2 * c) * σ2) c :=
    (((hasDerivAt_pow 2 c).add_const χ).mul_const σ2).congr_deriv (by norm_num)
  have hd : HasDerivAt (fun x : ℝ => (1 + x) ^ 2) (2 * (1 + c)) c :=
    (((hasDerivAt_id' c).const_add 1).fun_pow 2).congr_deriv (by norm_num)
  have hB := hn.div hd (pow_ne_zero 2 hc1.ne')
  have h := (hA.const_add (k ^ 2)).add hB
  exact h.congr_deriv (by field_simp; ring)

/-- O&R p. 642: the sign function `g(c) = σ²(c − χ)c³ − χk²(1 + c)³`, with
`L′(c) = 2g(c)/(c³(1 + c)³)`. -/
noncomputable def signFn (χ k σ2 c : ℝ) : ℝ := σ2 * (c - χ) * c ^ 3 - χ * k ^ 2 * (1 + c) ^ 3

/-- O&R p. 642: `L′(c) = 2g(c)/(c³(1 + c)³)`. -/
theorem deriv_eq_signFn (χ k σ2 c : ℝ) (hc : 0 < c) :
    2 * σ2 * (c - χ) / (1 + c) ^ 3 - 2 * χ * k ^ 2 / c ^ 3 =
      2 * signFn χ k σ2 c / (c ^ 3 * (1 + c) ^ 3) := by
  have hc1 : 0 < 1 + c := by linarith
  unfold signFn
  field_simp

/-- O&R p. 642 (the envelope heuristic): `L′(χ) = −2k²/χ² < 0`, so raising the banker's
weight above society's is first-order beneficial. -/
theorem deriv_at_chi (χ k σ2 : ℝ) (hχ : 0 < χ) :
    2 * σ2 * (χ - χ) / (1 + χ) ^ 3 - 2 * χ * k ^ 2 / χ ^ 3 = -(2 * k ^ 2 / χ ^ 2) := by
  field_simp
  ring

/-- The unimodality proof (T20): `h(c) = (c − χ)c³/(1 + c)³`. -/
noncomputable def hFn (χ c : ℝ) : ℝ := (c - χ) * (c / (1 + c)) ^ 3

/-- T20: `h` is strictly increasing on `[χ, ∞)` (product of the nonnegative increasing `c − χ`
and the positive strictly increasing `(c/(1 + c))³`). -/
theorem hFn_strictMonoOn (χ : ℝ) (hχ : 0 < χ) : StrictMonoOn (hFn χ) (Ici χ) := by
  intro a ha b hb hab
  simp only [mem_Ici] at ha hb
  have ha0 : 0 < a := lt_of_lt_of_le hχ ha
  have hb0 : 0 < b := by linarith
  have hq : a / (1 + a) < b / (1 + b) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hqa : 0 < a / (1 + a) := div_pos ha0 (by linarith)
  have h3 : (a / (1 + a)) ^ 3 < (b / (1 + b)) ^ 3 := by
    exact pow_lt_pow_left₀ hq hqa.le (by norm_num)
  unfold hFn
  calc (a - χ) * (a / (1 + a)) ^ 3 ≤ (a - χ) * (b / (1 + b)) ^ 3 :=
        mul_le_mul_of_nonneg_left h3.le (by linarith)
    _ < (b - χ) * (b / (1 + b)) ^ 3 :=
        mul_lt_mul_of_pos_right (by linarith) (by positivity)

/-- T20: `g(c) = (1 + c)³(σ²h(c) − χk²)`. -/
theorem signFn_eq_hFn (χ k σ2 c : ℝ) (hc : 0 < c) :
    signFn χ k σ2 c = (1 + c) ^ 3 * (σ2 * hFn χ c - χ * k ^ 2) := by
  have hc1 : 0 < 1 + c := by linarith
  unfold signFn hFn
  field_simp

/-- T20: `h` is continuous on `[0, ∞)`. -/
theorem hFn_continuousOn (χ : ℝ) : ContinuousOn (hFn χ) (Ici 0) := by
  unfold hFn
  refine ContinuousOn.mul (continuousOn_id.sub continuousOn_const) ?_
  refine ContinuousOn.pow (ContinuousOn.div continuousOn_id
    (continuousOn_const.add continuousOn_id) fun x hx => ?_) 3
  simp only [mem_Ici] at hx
  change (1 : ℝ) + x ≠ 0
  have : 0 < 1 + x := by linarith
  exact this.ne'

/-- T20 (existence of the optimum's characterisation): for `k > 0`, `σ² > 0` there is
`c* > χ` with `σ²h(c*) = χk²`. -/
theorem exists_root (χ k σ2 : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 < σ2) :
    ∃ cstar, χ < cstar ∧ σ2 * hFn χ cstar = χ * k ^ 2 := by
  set c1 := 1 + χ + 8 * χ * k ^ 2 / σ2 with hc1
  have hq : 0 < 8 * χ * k ^ 2 / σ2 := by positivity
  have hχc1 : χ ≤ c1 := by linarith
  have hcont : ContinuousOn (hFn χ) (Icc χ c1) :=
    (hFn_continuousOn χ).mono fun x hx => by simp only [mem_Icc] at hx; simp; linarith
  have hlow : hFn χ χ = 0 := by simp [hFn]
  have hhigh : χ * k ^ 2 / σ2 ≤ hFn χ c1 := by
    unfold hFn
    have h1 : (1 : ℝ) ≤ c1 := by linarith
    have h2 : 1 / 2 ≤ c1 / (1 + c1) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      linarith
    have h3 : (1 / 2 : ℝ) ^ 3 ≤ (c1 / (1 + c1)) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
    have h4 : c1 - χ = 1 + 8 * χ * k ^ 2 / σ2 := by rw [hc1]; ring
    rw [h4]
    have h5 : 8 * (χ * k ^ 2 / σ2) = 8 * χ * k ^ 2 / σ2 := by ring
    nlinarith [h3, hq]
  obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc hχc1 hcont
    (show χ * k ^ 2 / σ2 ∈ Icc (hFn χ χ) (hFn χ c1) from ⟨by rw [hlow]; positivity, hhigh⟩)
  refine ⟨c, ?_, ?_⟩
  · rcases (mem_Icc.1 hc).1.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, hlow] at hcv
      have : 0 < χ * k ^ 2 / σ2 := by positivity
      linarith
  · rw [hcv]
    field_simp

/-- T20: on `(0, c*)` the derivative is negative. -/
theorem signFn_neg (χ k σ2 cstar c : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 ≤ σ2)
    (hstar : χ < cstar) (hroot : σ2 * hFn χ cstar = χ * k ^ 2) (hc : 0 < c)
    (hcs : c < cstar) : signFn χ k σ2 c < 0 := by
  rcases le_or_gt c χ with h | h
  · unfold signFn
    have : σ2 * (c - χ) * c ^ 3 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hσ (by linarith))
        (by positivity)
    have : 0 < χ * k ^ 2 * (1 + c) ^ 3 := by positivity
    linarith
  · rw [signFn_eq_hFn χ k σ2 c hc]
    have hh := hFn_strictMonoOn χ hχ (mem_Ici.2 h.le) (mem_Ici.2 hstar.le) hcs
    have hσ' : 0 < σ2 := by
      rcases hσ.lt_or_eq with h' | h'
      · exact h'
      · rw [← h'] at hroot
        have : 0 < χ * k ^ 2 := by positivity
        linarith
    have : σ2 * hFn χ c - χ * k ^ 2 < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg (by positivity) this

/-- T20: on `(c*, ∞)` the derivative is positive. -/
theorem signFn_pos (χ k σ2 cstar c : ℝ) (hχ : 0 < χ) (hσ : 0 < σ2) (hstar : χ < cstar)
    (hroot : σ2 * hFn χ cstar = χ * k ^ 2) (hcs : cstar < c) : 0 < signFn χ k σ2 c := by
  have hc : 0 < c := by linarith
  rw [signFn_eq_hFn χ k σ2 c hc]
  have hh := hFn_strictMonoOn χ hχ (mem_Ici.2 hstar.le) (mem_Ici.2 (by linarith)) hcs
  have : 0 < σ2 * hFn χ c - χ * k ^ 2 := by nlinarith
  positivity

/-- T20: `L` is continuous on `(0, ∞)`. -/
theorem socialLoss_continuousOn (χ k σ2 : ℝ) : ContinuousOn (socialLoss χ k σ2) (Ioi 0) :=
  fun c hc => (hasDerivAt_socialLoss χ k σ2 c hc).continuousAt.continuousWithinAt

/-- O&R p. 642, Rogoff (1985b), unimodality: `L` is strictly decreasing on `(0, c*]`. -/
theorem socialLoss_strictAntiOn (χ k σ2 cstar : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 ≤ σ2)
    (hstar : χ < cstar) (hroot : σ2 * hFn χ cstar = χ * k ^ 2) :
    StrictAntiOn (socialLoss χ k σ2) (Ioc 0 cstar) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioc 0 cstar)
    ((socialLoss_continuousOn χ k σ2).mono Ioc_subset_Ioi_self) fun c hc => ?_
  rw [interior_Ioc] at hc
  rw [(hasDerivAt_socialLoss χ k σ2 c hc.1).deriv, deriv_eq_signFn χ k σ2 c hc.1]
  have := signFn_neg χ k σ2 cstar c hχ hk hσ hstar hroot hc.1 hc.2
  have : 0 < c ^ 3 * (1 + c) ^ 3 := by have := hc.1; positivity
  exact div_neg_of_neg_of_pos (by linarith) this

/-- O&R p. 642, Rogoff (1985b), unimodality: `L` is strictly increasing on `[c*, ∞)`. -/
theorem socialLoss_strictMonoOn (χ k σ2 cstar : ℝ) (hχ : 0 < χ) (hσ : 0 < σ2)
    (hstar : χ < cstar) (hroot : σ2 * hFn χ cstar = χ * k ^ 2) :
    StrictMonoOn (socialLoss χ k σ2) (Ici cstar) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici cstar)
    ((socialLoss_continuousOn χ k σ2).mono fun x hx => ?_) fun c hc => ?_
  · simp only [mem_Ici] at hx
    simp only [mem_Ioi]
    linarith
  · rw [interior_Ici] at hc
    have hc0 : 0 < c := by simp only [mem_Ioi] at hc; linarith
    rw [(hasDerivAt_socialLoss χ k σ2 c hc0).deriv, deriv_eq_signFn χ k σ2 c hc0]
    have := signFn_pos χ k σ2 cstar c hχ hσ hstar hroot hc
    have : 0 < c ^ 3 * (1 + c) ^ 3 := by positivity
    positivity

/-- O&R p. 642, Rogoff's theorem (T20): for `k > 0` and `σ² > 0` the optimal degree of
conservatism exists, is unique and strictly exceeds society's: there is `c* > χ` with
`L(c*) < L(c)` for every other `c > 0`, characterised by `σ²(c* − χ)c*³ = χk²(1 + c*)³`. -/
theorem rogoff_optimal (χ k σ2 : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 < σ2) :
    ∃ cstar, χ < cstar ∧ σ2 * (cstar - χ) * cstar ^ 3 = χ * k ^ 2 * (1 + cstar) ^ 3 ∧
      ∀ c, 0 < c → c ≠ cstar → socialLoss χ k σ2 cstar < socialLoss χ k σ2 c := by
  obtain ⟨cstar, hstar, hroot⟩ := exists_root χ k σ2 hχ hk hσ
  have hc0 : 0 < cstar := by linarith
  refine ⟨cstar, hstar, ?_, fun c hc hne => ?_⟩
  · have := signFn_eq_hFn χ k σ2 cstar hc0
    rw [hroot, sub_self, mul_zero] at this
    unfold signFn at this
    linarith
  · rcases lt_or_gt_of_ne hne with h | h
    · exact socialLoss_strictAntiOn χ k σ2 cstar hχ hk hσ.le hstar hroot ⟨hc, h.le⟩
        ⟨hc0, le_rfl⟩ h
    · exact socialLoss_strictMonoOn χ k σ2 cstar hχ hσ hstar hroot (mem_Ici.2 le_rfl)
        (mem_Ici.2 h.le) h

/-- O&R p. 642 (T20): the optimal weight is the unique global minimiser of `L` on
`(0, ∞)`. -/
theorem rogoff_existsUnique (χ k σ2 : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 < σ2) :
    ∃! cstar, 0 < cstar ∧ ∀ c, 0 < c → socialLoss χ k σ2 cstar ≤ socialLoss χ k σ2 c := by
  obtain ⟨cstar, hstar, -, hmin⟩ := rogoff_optimal χ k σ2 hχ hk hσ
  refine ⟨cstar, ⟨by linarith, fun c hc => ?_⟩, fun c' ⟨hc', hle⟩ => ?_⟩
  · rcases eq_or_ne c cstar with h | h
    · rw [h]
    · exact (hmin c hc h).le
  · by_contra hne
    have := hmin c' hc' hne
    have := hle cstar (by linarith)
    linarith

/-- O&R p. 642 (T20): any minimiser satisfies the first-order characterisation
`σ²h(c) = χk²` and exceeds `χ`. -/
theorem minimizer_char (χ k σ2 c : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 < σ2) (hc : 0 < c)
    (hmin : ∀ c', 0 < c' → socialLoss χ k σ2 c ≤ socialLoss χ k σ2 c') :
    χ < c ∧ σ2 * hFn χ c = χ * k ^ 2 := by
  obtain ⟨cstar, hstar, -, hopt⟩ := rogoff_optimal χ k σ2 hχ hk hσ
  have hceq : c = cstar := by
    by_contra hne
    have := hopt c hc hne
    have := hmin cstar (by linarith)
    linarith
  obtain ⟨c2, hc2, hroot⟩ := exists_root χ k σ2 hχ hk hσ
  have hc2eq : c2 = cstar := by
    by_contra hne
    have h2 := hopt c2 (by linarith) hne
    -- `c2` is also a minimiser: it is the turning point of the unimodal `L`
    rcases lt_or_gt_of_ne hne with h | h
    · have := socialLoss_strictMonoOn χ k σ2 c2 hχ hσ hc2 hroot (mem_Ici.2 le_rfl)
        (mem_Ici.2 h.le) h
      linarith
    · have := socialLoss_strictAntiOn χ k σ2 c2 hχ hk hσ.le hc2 hroot
        ⟨by linarith, h.le⟩ ⟨by linarith, le_rfl⟩ h
      linarith
  rw [hceq, ← hc2eq]
  exact ⟨hc2, hroot⟩

/-- O&R p. 642 (T20): the optimal banker is strictly better than one with society's own
weight: `L(c*) < L(χ) = V_D`. -/
theorem rogoff_beats_discretion (χ k σ2 : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 < σ2) :
    ∃ cstar, χ < cstar ∧ socialLoss χ k σ2 cstar < valueDiscretion χ k σ2 := by
  obtain ⟨cstar, hstar, -, hmin⟩ := rogoff_optimal χ k σ2 hχ hk hσ
  exact ⟨cstar, hstar, by
    rw [← socialLoss_self χ k σ2 hχ]
    exact hmin χ hχ hstar.ne⟩

/-- O&R p. 642: as `c → ∞` (a pure inflation targeter) the loss tends to `k² + σ²`. -/
theorem socialLoss_tendsto_atTop (χ k σ2 : ℝ) :
    Tendsto (socialLoss χ k σ2) atTop (𝓝 (k ^ 2 + σ2)) := by
  set G : ℝ → ℝ := fun u => k ^ 2 + χ * k ^ 2 * u ^ 2 + σ2 * ((1 + χ * u ^ 2) / (1 + u) ^ 2)
  have hG : ContinuousAt G 0 := by
    have : (1 + (0 : ℝ)) ^ 2 ≠ 0 := by norm_num
    fun_prop (disch := assumption)
  have hG0 : G 0 = k ^ 2 + σ2 := by simp [G]
  have hlim : Tendsto (fun c : ℝ => G c⁻¹) atTop (𝓝 (k ^ 2 + σ2)) := by
    rw [← hG0]
    exact hG.tendsto.comp tendsto_inv_atTop_zero
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  simp only [G, socialLoss]
  field_simp
  ring

/-- O&R p. 642: the optimal banker also beats the pure inflation targeter:
`L(c*) < k² + σ²`. -/
theorem rogoff_beats_infinite (χ k σ2 : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 < σ2) :
    ∃ cstar, χ < cstar ∧ socialLoss χ k σ2 cstar < k ^ 2 + σ2 := by
  obtain ⟨cstar, hstar, hroot⟩ := exists_root χ k σ2 hχ hk hσ
  have hmono := socialLoss_strictMonoOn χ k σ2 cstar hχ hσ hstar hroot
  refine ⟨cstar, hstar, ?_⟩
  have h1 : socialLoss χ k σ2 cstar < socialLoss χ k σ2 (cstar + 1) :=
    hmono (mem_Ici.2 le_rfl) (mem_Ici.2 (by linarith)) (by linarith)
  have h2 : socialLoss χ k σ2 (cstar + 1) ≤ k ^ 2 + σ2 := by
    refine ge_of_tendsto (socialLoss_tendsto_atTop χ k σ2) ?_
    filter_upwards [eventually_ge_atTop (cstar + 1)] with c hc
    rcases hc.lt_or_eq with h | h
    · exact (hmono (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) h).le
    · rw [h]
  linarith

/-- O&R p. 642: no conservative banker attains the commitment value:
`L(c) ≥ V_C + χk²/c² > V_C` (`k > 0`). -/
theorem socialLoss_gt_commit (χ k σ2 c : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 ≤ σ2)
    (hc : 0 < c) : valueCommit χ k σ2 + χ * k ^ 2 / c ^ 2 ≤ socialLoss χ k σ2 c ∧
      valueCommit χ k σ2 < socialLoss χ k σ2 c := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hc1 : 0 < 1 + c := by linarith
  have key : socialLoss χ k σ2 c - (valueCommit χ k σ2 + χ * k ^ 2 / c ^ 2) =
      σ2 * (c - χ) ^ 2 / ((1 + χ) * (1 + c) ^ 2) := by
    unfold socialLoss valueCommit
    field_simp
    ring
  have h1 : 0 ≤ σ2 * (c - χ) ^ 2 / ((1 + χ) * (1 + c) ^ 2) := by positivity
  have h2 : 0 < χ * k ^ 2 / c ^ 2 := by positivity
  constructor <;> linarith

/-- O&R p. 642: with no inflation bias (`k = 0`) society's own weight is the unique optimum
(`σ² > 0`). -/
theorem no_bias_optimum (χ σ2 c : ℝ) (hχ : 0 < χ) (hσ : 0 < σ2) (hc : 0 < c) (hne : c ≠ χ) :
    socialLoss χ 0 σ2 χ < socialLoss χ 0 σ2 c := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hc1 : 0 < 1 + c := by linarith
  have key : socialLoss χ 0 σ2 c - socialLoss χ 0 σ2 χ =
      σ2 * (c - χ) ^ 2 / ((1 + χ) * (1 + c) ^ 2) := by
    unfold socialLoss
    field_simp
    ring
  have : 0 < σ2 * (c - χ) ^ 2 / ((1 + χ) * (1 + c) ^ 2) := by
    have : 0 < (c - χ) ^ 2 := by positivity
    positivity
  linarith

/-- O&R p. 642: with no supply shocks (`σ² = 0`) and `k > 0`, the loss is strictly
decreasing in the banker's weight, always above `k²`, and tends to `k²`: the optimum is
"`χᶜᴮ = ∞`" (not attained). -/
theorem no_shock_limit (χ k : ℝ) (hχ : 0 < χ) (hk : 0 < k) :
    StrictAntiOn (socialLoss χ k 0) (Ioi 0) ∧ (∀ c, 0 < c → k ^ 2 < socialLoss χ k 0 c) ∧
      Tendsto (socialLoss χ k 0) atTop (𝓝 (k ^ 2)) := by
  refine ⟨fun a ha b _ hab => ?_, fun c hc => ?_, by
    simpa using socialLoss_tendsto_atTop χ k 0⟩
  · simp only [mem_Ioi] at ha
    unfold socialLoss
    simp only [mul_zero, zero_div, add_zero]
    have : χ * k ^ 2 / b ^ 2 < χ * k ^ 2 / a ^ 2 :=
      div_lt_div_of_pos_left (by positivity) (by positivity) (by nlinarith)
    linarith
  · unfold socialLoss
    simp only [mul_zero, zero_div, add_zero]
    have : 0 < χ * k ^ 2 / c ^ 2 := by positivity
    linarith

/-- O&R p. 642 (T20, comparative statics): the optimal weight rises with `k²/σ²`: if
`σ₁²h(c₁) = χk₁²` and `σ₂²h(c₂) = χk₂²` with `c₁, c₂ ≥ χ` and `k₁²/σ₁² < k₂²/σ₂²`, then
`c₁ < c₂`. -/
theorem optimum_mono_ratio (χ k1 k2 s1 s2 c1 c2 : ℝ) (hχ : 0 < χ) (hs1 : 0 < s1)
    (hs2 : 0 < s2) (hc1 : χ ≤ c1) (hc2 : χ ≤ c2) (hr1 : s1 * hFn χ c1 = χ * k1 ^ 2)
    (hr2 : s2 * hFn χ c2 = χ * k2 ^ 2) (hratio : k1 ^ 2 / s1 < k2 ^ 2 / s2) : c1 < c2 := by
  have e1 : hFn χ c1 = χ * (k1 ^ 2 / s1) := by
    field_simp
    linarith
  have e2 : hFn χ c2 = χ * (k2 ^ 2 / s2) := by
    field_simp
    linarith
  have hlt : hFn χ c1 < hFn χ c2 := by
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left hratio hχ
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with h | h
  · have := hFn_strictMonoOn χ hχ (mem_Ici.2 hc2) (mem_Ici.2 hc1) h
    linarith
  · rw [h] at hlt
    exact lt_irrefl _ hlt

/-! ## The Walsh contract, (42)–(44) -/

/-- O&R (42), p. 643: the banker's loss with the linear inflation penalty `2ωπ`. -/
def walshLoss (χ k ω π πe z : ℝ) : ℝ := bgLoss χ k π πe z + 2 * ω * π

/-- O&R (42): the contract term is equivalent to lowering the wedge to `k − ω`:
`L_W(π) = L(π; k − ω) + 2ω(πᵉ + z + k) − ω²`, a constant shift. -/
theorem walshLoss_eq (χ k ω π πe z : ℝ) :
    walshLoss χ k ω π πe z = bgLoss χ (k - ω) π πe z + (2 * ω * (πe + z + k) - ω ^ 2) := by
  unfold walshLoss bgLoss
  ring

/-- O&R (43)–(44), p. 643: the one-shot equilibrium under the Walsh contract is unique:
`πᵉ = (k − ω)/χ`, `π = (k − ω)/χ + z/(1 + χ)`. -/
theorem walsh_eqm_iff (p z : S → ℝ) (χ k ω : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) (π : S → ℝ) (πe : ℝ) :
    ((∀ s x, walshLoss χ k ω (π s) πe (z s) ≤ walshLoss χ k ω x πe (z s)) ∧
        πe = expect p π) ↔
      πe = (k - ω) / χ ∧ ∀ s, π s = (k - ω) / χ + z s / (1 + χ) := by
  have : (∀ s x, walshLoss χ k ω (π s) πe (z s) ≤ walshLoss χ k ω x πe (z s)) ↔
      ∀ s x, bgLoss χ (k - ω) (π s) πe (z s) ≤ bgLoss χ (k - ω) x πe (z s) := by
    simp only [walshLoss_eq, add_le_add_iff_right]
  rw [this]
  exact oneShot_eqm_iff p z χ (k - ω) hχ h1 hz π πe

/-- O&R (44): society's expected loss under the Walsh contract is `V_C + (k − ω)²/χ`. -/
theorem walsh_social_loss (p z : S → ℝ) (χ k ω : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    expLoss p z χ k (discretionRule χ (k - ω) z) =
      valueCommit χ k (varZ p z) + (k - ω) ^ 2 / χ := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hE : expect p (discretionRule χ (k - ω) z) = (k - ω) / χ := by
    have : expect p (discretionRule χ (k - ω) z) =
        expect p (fun s => (k - ω) / χ + (1 / (1 + χ)) * z s) := by
      unfold expect discretionRule
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, expect_add, expect_const p h1, expect_const_mul, hz, mul_zero, add_zero]
  rw [expLoss_eq_commit_add p z χ k hχ1 h1 hz, hE]
  have : expect p (fun s => (discretionRule χ (k - ω) z s - (k - ω) / χ - z s / (1 + χ)) ^ 2)
      = 0 := by
    unfold expect discretionRule
    simp
  rw [this]
  field_simp
  ring

/-- O&R p. 643: `ω = k` is the unique optimal linear contract; it attains the commitment
value `V_C` and implements the commitment rule (36). -/
theorem walsh_optimal (p z : S → ℝ) (χ k ω : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    expLoss p z χ k (discretionRule χ (k - k) z) = valueCommit χ k (varZ p z) ∧
      discretionRule χ (k - k) z = commitRule χ z ∧
      (ω ≠ k → valueCommit χ k (varZ p z) < expLoss p z χ k (discretionRule χ (k - ω) z)) := by
  refine ⟨?_, ?_, fun hne => ?_⟩
  · rw [walsh_social_loss p z χ k k hχ h1 hz]
    simp
  · funext s
    simp [discretionRule, commitRule]
  · rw [walsh_social_loss p z χ k ω hχ h1 hz]
    have : 0 < (k - ω) ^ 2 / χ := div_pos (by
      have : k - ω ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
      positivity) hχ
    linarith

/-! ## Exercise 4: a random weight on the bonus -/

/-- O&R Ex. 4, p. 658: the banker's loss `L + 2λωπ`. -/
def walshLossLam (χ k ω lam π πe z : ℝ) : ℝ := bgLoss χ k π πe z + 2 * lam * ω * π

/-- O&R Ex. 4(a): the banker's best response given `λ` is that of a wedge `k − λω`. -/
theorem walshLossLam_eq (χ k ω lam π πe z : ℝ) :
    walshLossLam χ k ω lam π πe z =
      bgLoss χ (k - lam * ω) π πe z + (2 * lam * ω * (πe + z + k) - (lam * ω) ^ 2) := by
  unfold walshLossLam bgLoss
  ring

/-- O&R Ex. 4(a): the one-shot equilibrium is unique: `πᵉ = (k − ω)/χ` and
`π = (k − ω)/χ + (z − (λ − 1)ω)/(1 + χ)` (with `E λ = 1`). -/
theorem ex4_eqm_iff (p z lam : S → ℝ) (χ k ω : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) (hlam : expect p lam = 1) (π : S → ℝ) (πe : ℝ) :
    ((∀ s x, walshLossLam χ k ω (lam s) (π s) πe (z s) ≤ walshLossLam χ k ω (lam s) x πe (z s))
        ∧ πe = expect p π) ↔
      πe = (k - ω) / χ ∧ ∀ s, π s = (k - ω) / χ + (z s - (lam s - 1) * ω) / (1 + χ) := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hopt : (∀ s x, walshLossLam χ k ω (lam s) (π s) πe (z s) ≤
      walshLossLam χ k ω (lam s) x πe (z s)) ↔
      ∀ s, π s = bestResponse χ (k - lam s * ω) πe (z s) := by
    simp only [walshLossLam_eq, add_le_add_iff_right]
    constructor
    · intro h s
      exact eq_bestResponse_of_le χ _ _ _ _ hχ1 (h s _)
    · intro h s x
      rw [h s]
      exact bestResponse_isMin χ _ x πe (z s) hχ1
  rw [hopt]
  have hE : ∀ e, expect p (fun s => bestResponse χ (k - lam s * ω) e (z s)) =
      (k - ω + e) / (1 + χ) := by
    intro e
    have : expect p (fun s => bestResponse χ (k - lam s * ω) e (z s)) =
        expect p (fun s => (k + e) / (1 + χ) + ((1 / (1 + χ)) * z s +
          (-(ω / (1 + χ))) * lam s)) := by
      unfold expect bestResponse
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, expect_add, expect_add, expect_const p h1, expect_const_mul, expect_const_mul, hz,
      hlam]
    ring
  constructor
  · rintro ⟨hπ, hre⟩
    have h2 : πe = (k - ω + πe) / (1 + χ) :=
      hre.trans ((congrArg (expect p) (funext hπ)).trans (hE πe))
    have hpe : πe = (k - ω) / χ := by
      rw [eq_div_iff hχ1.ne'] at h2
      rw [eq_div_iff hχ.ne']
      linarith
    refine ⟨hpe, fun s => ?_⟩
    rw [hπ s, hpe]
    unfold bestResponse
    field_simp
    ring
  · rintro ⟨hpe, hπ⟩
    have hbr : ∀ s, π s = bestResponse χ (k - lam s * ω) πe (z s) := by
      intro s
      rw [hπ s, hpe]
      unfold bestResponse
      field_simp
      ring
    refine ⟨hbr, ?_⟩
    rw [show π = fun s => bestResponse χ (k - lam s * ω) πe (z s) from funext hbr, hE, hpe]
    field_simp
    ring

/-- O&R Ex. 4(b): with `E λ = 1`, `Var λ = σ_λ²` and `E[λz] = 0` (λ uncorrelated with `z`),
society's expected loss is `k² + (k − ω)²/χ + χσ_z²/(1 + χ) + ω²σ_λ²/(1 + χ)`. -/
theorem ex4_social_loss (p z lam : S → ℝ) (χ k ω : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) (hlam : expect p lam = 1)
    (hcov : expect p (fun s => z s * lam s) = 0) :
    expLoss p z χ k (fun s => (k - ω) / χ + (z s - (lam s - 1) * ω) / (1 + χ)) =
      k ^ 2 + (k - ω) ^ 2 / χ + χ * varZ p z / (1 + χ) +
        ω ^ 2 * expect p (fun s => (lam s - 1) ^ 2) / (1 + χ) := by
  have hχ1 : 0 < 1 + χ := by linarith
  set π : S → ℝ := fun s => (k - ω) / χ + (z s - (lam s - 1) * ω) / (1 + χ)
  have hE : expect p π = (k - ω) / χ := by
    unfold expect at hz hlam ⊢
    have : ∑ s, p s * π s = ∑ s, (p s * ((k - ω) / χ + ω / (1 + χ)) +
        1 / (1 + χ) * (p s * z s) + (-(ω / (1 + χ))) * (p s * lam s)) :=
      Finset.sum_congr rfl fun s _ => by simp only [π]; ring
    rw [this, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, ← Finset.mul_sum, h1, hz, hlam]
    ring
  rw [expLoss_decomp p z χ k h1 hz, hE]
  have hV : expect p (fun s => (lam s - 1) ^ 2) =
      expect p (fun s => lam s ^ 2) - 2 * expect p lam + 1 := by
    have : expect p (fun s => (lam s - 1) ^ 2) = expect p (fun s => lam s ^ 2 +
        ((-2) * lam s + 1)) := by
      unfold expect
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, expect_add, expect_add, expect_const_mul, expect_const p h1]
    ring
  have e1 : expect p (fun s => (π s - (k - ω) / χ - z s) ^ 2) =
      (χ ^ 2 * varZ p z + ω ^ 2 * expect p (fun s => (lam s - 1) ^ 2)) / (1 + χ) ^ 2 := by
    have : expect p (fun s => (π s - (k - ω) / χ - z s) ^ 2) =
        expect p (fun s => (χ ^ 2 / (1 + χ) ^ 2) * z s ^ 2 +
          ((2 * χ * ω / (1 + χ) ^ 2) * (z s * lam s) +
            ((-(2 * χ * ω / (1 + χ) ^ 2)) * z s +
              (ω ^ 2 / (1 + χ) ^ 2) * (lam s - 1) ^ 2))) := by
      unfold expect
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [π]
      field_simp
      ring
    rw [this, expect_add, expect_add, expect_add, expect_const_mul, expect_const_mul,
      expect_const_mul, expect_const_mul, hcov, hz]
    unfold varZ
    field_simp
    ring
  have e2 : expect p (fun s => (π s - (k - ω) / χ) ^ 2) =
      (varZ p z + ω ^ 2 * expect p (fun s => (lam s - 1) ^ 2)) / (1 + χ) ^ 2 := by
    have : expect p (fun s => (π s - (k - ω) / χ) ^ 2) =
        expect p (fun s => (1 / (1 + χ) ^ 2) * z s ^ 2 +
          ((-(2 * ω / (1 + χ) ^ 2)) * (z s * lam s) +
            ((2 * ω / (1 + χ) ^ 2) * z s +
              (ω ^ 2 / (1 + χ) ^ 2) * (lam s - 1) ^ 2))) := by
      unfold expect
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [π]
      field_simp
      ring
    rw [this, expect_add, expect_add, expect_add, expect_const_mul, expect_const_mul,
      expect_const_mul, expect_const_mul, hcov, hz]
    unfold varZ
    field_simp
    ring
  rw [e1, e2]
  field_simp
  ring

/-- O&R Ex. 4(c): the ω-dependent part of the loss, `(k − ω)²/χ + ω²σ_λ²/(1 + χ)`, equals
its minimum plus `A(ω − ω*)²` with `ω* = k(1 + χ)/(1 + χ + χσ_λ²)` and
`A = (1 + χ + χσ_λ²)/(χ(1 + χ))`. -/
theorem ex4_complete_square (χ k ω sl : ℝ) (hχ : 0 < χ) (hsl : 0 ≤ sl) :
    (k - ω) ^ 2 / χ + ω ^ 2 * sl / (1 + χ) =
      ((k - k * (1 + χ) / (1 + χ + χ * sl)) ^ 2 / χ +
        (k * (1 + χ) / (1 + χ + χ * sl)) ^ 2 * sl / (1 + χ)) +
      (1 + χ + χ * sl) / (χ * (1 + χ)) * (ω - k * (1 + χ) / (1 + χ + χ * sl)) ^ 2 := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hD : 0 < 1 + χ + χ * sl := by positivity
  field_simp
  ring

/-- O&R Ex. 4(c): `ω* = k(1 + χ)/(1 + χ + χσ_λ²)` is the unique minimiser of the expected
social loss over `ω`, and it corrects the inflation bias only partially: `ω* < k` iff
`σ_λ² > 0` (for `k > 0`). -/
theorem ex4_optimal (χ k sl : ℝ) (hχ : 0 < χ) (hsl : 0 ≤ sl) (hk : 0 < k) :
    (∀ ω, ω ≠ k * (1 + χ) / (1 + χ + χ * sl) →
      (k - k * (1 + χ) / (1 + χ + χ * sl)) ^ 2 / χ +
          (k * (1 + χ) / (1 + χ + χ * sl)) ^ 2 * sl / (1 + χ) <
        (k - ω) ^ 2 / χ + ω ^ 2 * sl / (1 + χ)) ∧
      (k * (1 + χ) / (1 + χ + χ * sl) < k ↔ 0 < sl) := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hD : 0 < 1 + χ + χ * sl := by positivity
  refine ⟨fun ω hne => ?_, ?_⟩
  · rw [ex4_complete_square χ k ω sl hχ hsl]
    have : 0 < (1 + χ + χ * sl) / (χ * (1 + χ)) *
        (ω - k * (1 + χ) / (1 + χ + χ * sl)) ^ 2 := by
      have : ω - k * (1 + χ) / (1 + χ + χ * sl) ≠ 0 := sub_ne_zero.2 hne
      positivity
    linarith
  · rw [div_lt_iff₀ hD]
    constructor
    · intro h
      have : 0 < k * χ * sl := by nlinarith
      exact pos_of_mul_pos_right this (by positivity)
    · intro h
      nlinarith [mul_pos (mul_pos hk hχ) h]

/-! ## Application: central bank independence and inflation (p. 646) -/

/-- O&R p. 646: the CBI slope `−6.02` (s.e. `2.35`) has t-ratio in `(2.56, 2.57)`, above the
two-sided 5% critical value `2.131` of Student's t with `17 − 2 = 15` degrees of freedom, so
the slope is significant with the hypothesised (negative) sign. -/
theorem cbi_slope_significant :
    (2.131 : ℝ) < 6.02 / 2.35 ∧ (6.02 : ℝ) / 2.35 < 2.57 ∧ (2.56 : ℝ) < 6.02 / 2.35 ∧
      (-6.02 : ℝ) < 0 := by
  norm_num

end ObstfeldRogoff.NominalRigidities.CentralBankDelegation
