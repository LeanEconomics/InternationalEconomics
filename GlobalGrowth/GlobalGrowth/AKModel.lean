/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp

/-!
# The AK model and learning by doing

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §7.3.1
(pp. 474–478), equations (61)–(68) and footnotes 32–33.

Everything is proved over the genuine infinite horizon, with isoelastic utility (61) for
every `σ > 0` (logarithmic at `σ = 1`).

* **Supporting-hyperplane verification.** For any budget `k_{t+1} = R k_t + w_t - p c_t`, a
  candidate satisfying the Euler condition `βᵗ u'(c*_t) = λ p R^{-t}` beats every feasible
  rival with `k ≥ 0` on partial sums, up to the transversality term `λ R R^{-T} k*_T`. The
  rival's utility need not be summable.
* **Finite utility.** Along the balanced path, utility is finite iff `ḡ < A` (exactly), i.e.
  `β^σ(1+A)^{σ-1} < 1`.
* **AK planner (fn 32).** When `ḡ < A` the balanced plan `c_t = (A - ḡ)k_t` is optimal and
  unique: every optimal plan is on the balanced path from date 0 (no transition). When
  `ḡ ≥ A` there is no optimum at all.
* **Competitive equilibrium.** The firm's interior demand forces `r = A` (64), and the
  equilibrium equals the planner's optimum (p. 476).
* **Learning by doing (66)–(68).** The private marginal product is `αA`, the firm optimum
  pays the labour share `(1-α)Ak` (fn 33), and the competitive equilibrium exists and is
  unique. It is derived from the necessity of the Euler equation (a one-period perturbation)
  and a no-wasted-wealth argument. Market growth `[β(1+αA)]^σ` is below the social
  `[β(1+A)]^σ`. The output subsidy `(1-α)/α`, financed by a constant consumption tax,
  implements the optimum.

Corrections to the book: the planner's finiteness condition `β^σ(1+A)^{σ-1} < 1` is not
implied by the market's when `σ > 1` (explicit counterexample), and the reverse implication
fails when `σ < 1`. The book's condition `β(1+A) > 1` is needed only for *positive* growth;
optimality and uniqueness hold whenever `ḡ < A`.
-/

namespace ObstfeldRogoff.GlobalGrowth.AKModel

open Filter Topology Finset

/-! ## CRRA utility (61) -/

/-- Isoelastic period utility of O&R (61), p. 474: `c^{1-1/σ}/(1-1/σ)`, with the
logarithmic limit `log c` at `σ = 1`. -/
noncomputable def crra (σ c : ℝ) : ℝ :=
  if σ = 1 then Real.log c else c ^ (1 - 1 / σ) / (1 - 1 / σ)

/-- Marginal utility `c^{-1/σ}` of the isoelastic utility (61), O&R p. 474. -/
noncomputable def crraMU (σ c : ℝ) : ℝ := c ^ (-(1 / σ))

/-- Marginal utility is positive, O&R (61). -/
theorem crraMU_pos (σ : ℝ) {c : ℝ} (hc : 0 < c) : 0 < crraMU σ c :=
  Real.rpow_pos_of_pos hc _

/-- The derivative of (61) is `c^{-1/σ}`, O&R p. 474 (used for the Euler equation (62)). -/
theorem crra_hasDerivAt {σ c : ℝ} (hc : 0 < c) :
    HasDerivAt (crra σ) (crraMU σ c) c := by
  unfold crra crraMU
  by_cases h1 : σ = 1
  · simp only [h1, ↓reduceIte]
    have := Real.hasDerivAt_log hc.ne'
    convert this using 1
    rw [div_one, Real.rpow_neg hc.le, Real.rpow_one]
  · simp only [h1, ↓reduceIte]
    have hp : (1 - 1 / σ) ≠ 0 := by
      intro h
      apply h1
      have : 1 / σ = 1 := by linarith
      rw [one_div] at this
      exact inv_eq_one.mp this
    have hd := (Real.hasDerivAt_rpow_const (p := 1 - 1 / σ) (Or.inl hc.ne')).div_const
      (1 - 1 / σ)
    convert hd using 1
    rw [mul_div_assoc, mul_comm, div_mul_cancel₀ _ hp]
    congr 1
    ring

/-- Bernoulli-type bound behind the concavity of (61): for `x > 0` and `p ≠ 0`,
`(x^p - 1)/p ≤ x - 1`, strictly when `x ≠ 1`. -/
theorem rpow_sub_one_div_le {x p : ℝ} (hx : 0 < x) (hp : p ≠ 0) (hp1 : p < 1) :
    (x ^ p - 1) / p ≤ x - 1 := by
  rcases lt_or_gt_of_ne hp with hneg | hpos
  · have hlog := Real.log_le_sub_one_of_pos hx
    have hexp : 1 + p * Real.log x ≤ x ^ p := by
      rw [Real.rpow_def_of_pos hx]
      have := Real.add_one_le_exp (Real.log x * p)
      linarith [mul_comm p (Real.log x)]
    have : 1 + p * (x - 1) ≤ x ^ p := by nlinarith
    rw [div_le_iff_of_neg hneg]
    nlinarith
  · have hb := rpow_one_add_le_one_add_mul_self (s := x - 1) (by linarith) hpos.le hp1.le
    simp only [add_sub_cancel] at hb
    rw [div_le_iff₀ hpos]
    nlinarith

/-- Strict version of `rpow_sub_one_div_le` for `x ≠ 1`. -/
theorem rpow_sub_one_div_lt {x p : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) (hp : p ≠ 0) (hp1 : p < 1) :
    (x ^ p - 1) / p < x - 1 := by
  rcases lt_or_gt_of_ne hp with hneg | hpos
  · have hlog := Real.log_lt_sub_one_of_pos hx hx1
    have hexp : 1 + p * Real.log x ≤ x ^ p := by
      rw [Real.rpow_def_of_pos hx]
      have := Real.add_one_le_exp (Real.log x * p)
      linarith [mul_comm p (Real.log x)]
    have : 1 + p * (x - 1) < x ^ p := by nlinarith
    rw [div_lt_iff_of_neg hneg]
    nlinarith
  · have hs : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    have hb := rpow_one_add_lt_one_add_mul_self (s := x - 1) (by linarith) hs hpos hp1
    simp only [add_sub_cancel] at hb
    rw [div_lt_iff₀ hpos]
    nlinarith

/-- **Supporting hyperplane for (61)**, O&R p. 474: the isoelastic utility lies below its
tangent, `u(c) ≤ u(c*) + u'(c*)(c - c*)`, with strict inequality when `c ≠ c*`. -/
theorem crra_support {σ c cs : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hcs : 0 < cs) :
    crra σ c ≤ crra σ cs + crraMU σ cs * (c - cs) := by
  unfold crra crraMU
  by_cases h1 : σ = 1
  · simp only [h1, ↓reduceIte, div_one]
    rw [Real.rpow_neg hcs.le, Real.rpow_one]
    have h := Real.log_le_sub_one_of_pos (div_pos hc hcs)
    rw [Real.log_div hc.ne' hcs.ne'] at h
    have : c / cs - 1 = cs⁻¹ * (c - cs) := by field_simp
    linarith
  · simp only [h1, ↓reduceIte]
    set p := 1 - 1 / σ with hpdef
    have hp : p ≠ 0 := by
      intro h
      apply h1
      have : 1 / σ = 1 := by linarith
      rw [one_div] at this
      exact inv_eq_one.mp this
    have hp1 : p < 1 := by have : 0 < 1 / σ := by positivity
                           linarith
    have key := rpow_sub_one_div_le (div_pos hc hcs) hp hp1
    rw [Real.div_rpow hc.le hcs.le] at key
    have hcsp : 0 < cs ^ p := Real.rpow_pos_of_pos hcs p
    have hmu : cs ^ (-(1 / σ)) = cs ^ p / cs := by
      rw [show -(1 / σ) = p - 1 by rw [hpdef]; ring, Real.rpow_sub hcs, Real.rpow_one]
    rw [hmu]
    have e1 : (c ^ p / cs ^ p - 1) / p = (c ^ p / p - cs ^ p / p) / cs ^ p := by
      field_simp
    rw [e1, div_le_iff₀ hcsp] at key
    have e2 : cs ^ p / cs * (c - cs) = (c / cs - 1) * cs ^ p := by field_simp
    linarith

/-- Strict supporting hyperplane for (61) when `c ≠ c*`, O&R p. 474. -/
theorem crra_support_strict {σ c cs : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hcs : 0 < cs)
    (hne : c ≠ cs) :
    crra σ c < crra σ cs + crraMU σ cs * (c - cs) := by
  have hx1 : c / cs ≠ 1 := by
    intro h
    apply hne
    field_simp at h
    exact h
  unfold crra crraMU
  by_cases h1 : σ = 1
  · simp only [h1, ↓reduceIte, div_one]
    rw [Real.rpow_neg hcs.le, Real.rpow_one]
    have h := Real.log_lt_sub_one_of_pos (div_pos hc hcs) hx1
    rw [Real.log_div hc.ne' hcs.ne'] at h
    have : c / cs - 1 = cs⁻¹ * (c - cs) := by field_simp
    linarith
  · simp only [h1, ↓reduceIte]
    set p := 1 - 1 / σ with hpdef
    have hp : p ≠ 0 := by
      intro h
      apply h1
      have : 1 / σ = 1 := by linarith
      rw [one_div] at this
      exact inv_eq_one.mp this
    have hp1 : p < 1 := by have : 0 < 1 / σ := by positivity
                           linarith
    have key := rpow_sub_one_div_lt (div_pos hc hcs) hx1 hp hp1
    rw [Real.div_rpow hc.le hcs.le] at key
    have hcsp : 0 < cs ^ p := Real.rpow_pos_of_pos hcs p
    have hmu : cs ^ (-(1 / σ)) = cs ^ p / cs := by
      rw [show -(1 / σ) = p - 1 by rw [hpdef]; ring, Real.rpow_sub hcs, Real.rpow_one]
    rw [hmu]
    have e1 : (c ^ p / cs ^ p - 1) / p = (c ^ p / p - cs ^ p / p) / cs ^ p := by
      field_simp
    rw [e1, div_lt_iff₀ hcsp] at key
    have e2 : cs ^ p / cs * (c - cs) = (c / cs - 1) * cs ^ p := by field_simp
    linarith

/-- The isoelastic utility (61) is strictly increasing on `(0, ∞)`, O&R p. 474. -/
theorem crra_strictMonoOn {σ : ℝ} (hσ : 0 < σ) : StrictMonoOn (crra σ) (Set.Ioi 0) := by
  intro a ha b hb hab
  have h := crra_support_strict hσ (Set.mem_Ioi.mp ha) (Set.mem_Ioi.mp hb) hab.ne
  have := crraMU_pos σ (Set.mem_Ioi.mp hb)
  nlinarith

/-! ## Budget arithmetic and the supporting-hyperplane verification -/

/-- An asset path obeying `k_{t+1} = R k_t + w_t - p c_t`: the AK resource constraint of
O&R fn 32 (`w = 0`, `p = 1`), the household budget of fn 33 (labour income `w`), and the
budget with a consumption tax (`p = 1 + τ`, p. 478). -/
def Budget (R p : ℝ) (w c k : ℕ → ℝ) : Prop := ∀ t, k (t + 1) = R * k t + w t - p * c t

/-- **Present-value budget identity** (O&R §2.1.3 applied to (63)–(64)): along any path
obeying `Budget`, `∑_{t<T} R^{-t} p c_t = R k_0 + ∑_{t<T} R^{-t} w_t - R·R^{-T} k_T`. -/
theorem budget_pv {R p : ℝ} {w c k : ℕ → ℝ} (hR : R ≠ 0) (hb : Budget R p w c k) (T : ℕ) :
    ∑ t ∈ range T, (R ^ t)⁻¹ * (p * c t) =
      R * k 0 + ∑ t ∈ range T, (R ^ t)⁻¹ * w t - R * ((R ^ T)⁻¹ * k T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, sum_range_succ, ih, hb T, pow_succ]
    field_simp
    ring

/-- **Welfare-gap identity** (supporting-hyperplane argument, O&R §7.3.1): if a candidate
`c*` satisfies the Euler condition `β^t u'(c*_t) = λ p R^{-t}`, then for any other path with
the same budget and initial assets, the utility shortfall on `[0, T)` plus the (nonnegative
when `u` is concave) tangent gaps equals `λ R R^{-T} (k*_T - k_T)`. -/
theorem welfare_gap_identity {u u' : ℝ → ℝ} {β R p lam : ℝ} {w c k cs ks : ℕ → ℝ}
    (hR : R ≠ 0) (heuler : ∀ t, β ^ t * u' (cs t) = lam * p * (R ^ t)⁻¹)
    (hb : Budget R p w c k) (hbs : Budget R p w cs ks) (h0 : k 0 = ks 0) (T : ℕ) :
    ∑ t ∈ range T, β ^ t * u (c t) +
        ∑ t ∈ range T, β ^ t * (u (cs t) + u' (cs t) * (c t - cs t) - u (c t)) =
      ∑ t ∈ range T, β ^ t * u (cs t) +
        lam * (R * ((R ^ T)⁻¹ * ks T) - R * ((R ^ T)⁻¹ * k T)) := by
  have e : ∀ t ∈ range T, β ^ t * u (c t) +
      β ^ t * (u (cs t) + u' (cs t) * (c t - cs t) - u (c t)) =
      β ^ t * u (cs t) + lam * ((R ^ t)⁻¹ * (p * c t)) - lam * ((R ^ t)⁻¹ * (p * cs t)) := by
    intro t _
    linear_combination (c t - cs t) * heuler t
  rw [← sum_add_distrib, sum_congr rfl e, sum_sub_distrib, sum_add_distrib, ← mul_sum,
    ← mul_sum, budget_pv hR hb, budget_pv hR hbs, h0]
  ring

/-- **Verification on partial sums** (O&R §7.3.1): under the Euler condition and the tangent
inequality, any rival path with nonnegative terminal assets satisfies
`∑_{t<T} βᵗ u(c_t) ≤ ∑_{t<T} βᵗ u(c*_t) + λ R R^{-T} k*_T` — no summability of the rival is
needed. -/
theorem welfare_partial_le {u u' : ℝ → ℝ} {β R p lam : ℝ} {w c k cs ks : ℕ → ℝ}
    (hβ : 0 ≤ β) (hR : 0 < R) (hlam : 0 ≤ lam)
    (hsupp : ∀ t, u (c t) ≤ u (cs t) + u' (cs t) * (c t - cs t))
    (heuler : ∀ t, β ^ t * u' (cs t) = lam * p * (R ^ t)⁻¹)
    (hb : Budget R p w c k) (hbs : Budget R p w cs ks) (h0 : k 0 = ks 0)
    (T : ℕ) (hkT : 0 ≤ k T) :
    ∑ t ∈ range T, β ^ t * u (c t) ≤
      ∑ t ∈ range T, β ^ t * u (cs t) + lam * (R * ((R ^ T)⁻¹ * ks T)) := by
  have hid := welfare_gap_identity (u := u) hR.ne' heuler hb hbs h0 T
  have hgap : 0 ≤ ∑ t ∈ range T, β ^ t * (u (cs t) + u' (cs t) * (c t - cs t) - u (c t)) :=
    sum_nonneg fun t _ => mul_nonneg (pow_nonneg hβ t) (by linarith [hsupp t])
  have : 0 ≤ lam * (R * ((R ^ T)⁻¹ * k T)) := by positivity
  nlinarith

/-- Strict version of `welfare_partial_le`: a strict tangent gap at date `t₀ < T` lowers the
rival's partial welfare by at least `β^{t₀}` times that gap (O&R §7.3.1, uniqueness). -/
theorem welfare_partial_lt {u u' : ℝ → ℝ} {β R p lam : ℝ} {w c k cs ks : ℕ → ℝ}
    (hβ : 0 ≤ β) (hR : 0 < R) (hlam : 0 ≤ lam)
    (hsupp : ∀ t, u (c t) ≤ u (cs t) + u' (cs t) * (c t - cs t))
    (heuler : ∀ t, β ^ t * u' (cs t) = lam * p * (R ^ t)⁻¹)
    (hb : Budget R p w c k) (hbs : Budget R p w cs ks) (h0 : k 0 = ks 0)
    {t₀ T : ℕ} (hT : t₀ < T) (hkT : 0 ≤ k T) :
    ∑ t ∈ range T, β ^ t * u (c t) +
        β ^ t₀ * (u (cs t₀) + u' (cs t₀) * (c t₀ - cs t₀) - u (c t₀)) ≤
      ∑ t ∈ range T, β ^ t * u (cs t) + lam * (R * ((R ^ T)⁻¹ * ks T)) := by
  have hid := welfare_gap_identity (u := u) hR.ne' heuler hb hbs h0 T
  have hsingle := single_le_sum (f := fun t => β ^ t *
      (u (cs t) + u' (cs t) * (c t - cs t) - u (c t)))
    (fun t _ => mul_nonneg (pow_nonneg hβ t) (by linarith [hsupp t]))
    (mem_range.mpr hT)
  have : 0 ≤ lam * (R * ((R ^ T)⁻¹ * k T)) := by positivity
  nlinarith

/-- Passing a partial-sum comparison to the limit (genuine infinite horizon): if
`∑_{t<T} f + δ ≤ ∑_{t<T} g + e_T` for all large `T`, `e_T → 0`, and both series converge, then
`∑ f + δ ≤ ∑ g`. -/
theorem tsum_add_le_of_partial {f g e : ℕ → ℝ} {δ : ℝ} {N : ℕ} (hf : Summable f)
    (hg : Summable g) (he : Tendsto e atTop (𝓝 0))
    (h : ∀ T, N ≤ T → ∑ t ∈ range T, f t + δ ≤ ∑ t ∈ range T, g t + e T) :
    ∑' t, f t + δ ≤ ∑' t, g t := by
  have h1 := hf.hasSum.tendsto_sum_nat.add_const δ
  have h2 := hg.hasSum.tendsto_sum_nat.add he
  rw [add_zero] at h2
  exact le_of_tendsto_of_tendsto h1 h2 (eventually_atTop.2 ⟨N, h⟩)

/-! ## Balanced growth paths -/

/-- Raising `(βR)^σ` to `-1/σ` gives `(βR)^{-1}` (O&R (62) inverted). -/
theorem growth_rpow_neg_inv {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    (x ^ σ) ^ (-(1 / σ)) = x⁻¹ := by
  rw [← Real.rpow_mul hx.le, show σ * -(1 / σ) = -1 by field_simp, Real.rpow_neg_one]

/-- Raising `(βR)^σ` to `1/σ` gives back `βR`: the Euler equation (62) along (65). -/
theorem growth_rpow_inv {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    (x ^ σ) ^ (1 / σ) = x := by
  rw [← Real.rpow_mul hx.le, mul_one_div_cancel hσ.ne', Real.rpow_one]

/-- Marginal utility along a geometric consumption path `x Gᵗ`. -/
theorem crraMU_geom {σ x G : ℝ} (hx : 0 < x) (hG : 0 < G) (t : ℕ) :
    crraMU σ (x * G ^ t) = crraMU σ x * (G ^ (-(1 / σ))) ^ t := by
  unfold crraMU
  rw [Real.mul_rpow hx.le (pow_nonneg hG.le t), Real.rpow_pow_comm hG.le]

/-- **Euler condition along the balanced path** (O&R (62), (65)): with `G = (βR)^σ`,
`βᵗ u'(x Gᵗ) = u'(x) R^{-t}`, i.e. the discounted marginal utility falls at the interest
rate. -/
theorem balanced_euler {σ β R x : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hR : 0 < R) (hx : 0 < x)
    (t : ℕ) :
    β ^ t * crraMU σ (x * ((β * R) ^ σ) ^ t) = crraMU σ x * 1 * (R ^ t)⁻¹ := by
  have hβR : 0 < β * R := mul_pos hβ hR
  rw [crraMU_geom hx (Real.rpow_pos_of_pos hβR σ), growth_rpow_neg_inv hσ hβR, mul_one,
    ← inv_pow, mul_left_comm, ← mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ hβ.ne',
    one_mul, inv_pow]

/-- Consumption growth implied by the Euler equation (62): `c_{t+1}/c_t = [β(1+r)]^σ`. -/
theorem balanced_growth_euler {σ β R : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hR : 0 < R) :
    R = (1 / β) * ((β * R) ^ σ) ^ (1 / σ) := by
  rw [growth_rpow_inv hσ (mul_pos hβ hR)]
  field_simp

/-- Utility along a geometric path, `σ ≠ 1`: `u(x Gᵗ) = (G^{1-1/σ})ᵗ u(x)`. -/
theorem crra_geom {σ x G : ℝ} (h1 : σ ≠ 1) (hx : 0 < x) (hG : 0 < G) (t : ℕ) :
    crra σ (x * G ^ t) = (G ^ (1 - 1 / σ)) ^ t * crra σ x := by
  unfold crra
  simp only [h1, ↓reduceIte]
  rw [Real.mul_rpow hx.le (pow_nonneg hG.le t), Real.rpow_pow_comm hG.le]
  ring

/-- Logarithmic utility along a geometric path: `log(x Gᵗ) = log x + t log G`. -/
theorem crra_one_geom {x G : ℝ} (hx : 0 < x) (hG : 0 < G) (t : ℕ) :
    crra 1 (x * G ^ t) = Real.log x + t * Real.log G := by
  unfold crra
  simp only [↓reduceIte]
  rw [Real.log_mul hx.ne' (pow_ne_zero t hG.ne'), Real.log_pow]

/-- The key identity behind O&R p. 476: with `G = (βR)^σ`, `β G^{1-1/σ} = G/R`. -/
theorem discount_growth_eq {σ β R : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hR : 0 < R) :
    β * ((β * R) ^ σ) ^ (1 - 1 / σ) = (β * R) ^ σ / R := by
  have hβR : 0 < β * R := mul_pos hβ hR
  have hG := Real.rpow_pos_of_pos hβR σ
  rw [show (1 : ℝ) - 1 / σ = 1 + -(1 / σ) by ring, Real.rpow_add hG, Real.rpow_one,
    growth_rpow_neg_inv hσ hβR]
  field_simp

/-- A nonzero geometric term sequence `qᵗ C` with `q ≥ 1` is not summable. -/
theorem not_summable_geom_mul {q C : ℝ} (hq : 1 ≤ q) (hC : C ≠ 0) :
    ¬ Summable (fun t : ℕ => q ^ t * C) := by
  intro hs
  have hev := (hs.tendsto_atTop_zero.norm).eventually
    (gt_mem_nhds (a := ‖C‖) (by rw [norm_zero]; exact norm_pos_iff.mpr hC))
  obtain ⟨t, ht⟩ := hev.exists
  have h1 : 1 ≤ q ^ t := one_le_pow₀ hq
  have : ‖C‖ ≤ ‖q ^ t * C‖ := by
    rw [norm_mul, Real.norm_eq_abs (q ^ t), abs_of_nonneg (by linarith)]
    nlinarith [norm_nonneg C]
  linarith

/-- **Finite utility along a constant-growth path, `σ ≠ 1`** (O&R p. 476 and §2.1.3):
`∑ βᵗ u(x Gᵗ)` converges iff `β G^{1-1/σ} < 1`. -/
theorem summable_geom_iff {σ β x G : ℝ} (h1 : σ ≠ 1) (hβ : 0 < β) (hx : 0 < x)
    (hG : 0 < G) :
    Summable (fun t : ℕ => β ^ t * crra σ (x * G ^ t)) ↔ β * G ^ (1 - 1 / σ) < 1 := by
  have hfun : (fun t : ℕ => β ^ t * crra σ (x * G ^ t)) =
      fun t : ℕ => (β * G ^ (1 - 1 / σ)) ^ t * crra σ x := by
    funext t
    rw [crra_geom h1 hx hG, mul_pow]
    ring
  have hq : 0 ≤ β * G ^ (1 - 1 / σ) := by positivity
  have hC : crra σ x ≠ 0 := by
    unfold crra
    simp only [h1, ↓reduceIte]
    have hp : (1 - 1 / σ) ≠ 0 := by
      intro h
      apply h1
      have : 1 / σ = 1 := by linarith
      rw [one_div] at this
      exact inv_eq_one.mp this
    exact div_ne_zero (Real.rpow_pos_of_pos hx _).ne' hp
  rw [hfun]
  constructor
  · intro hs
    by_contra hge
    exact not_summable_geom_mul (not_lt.mp hge) hC hs
  · intro hlt
    exact (summable_geometric_of_lt_one hq hlt).mul_right _

/-- Logarithmic utility along any geometric path is summable when `0 ≤ β < 1`. -/
theorem summable_geom_log {β x G : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (hx : 0 < x) (hG : 0 < G) :
    Summable (fun t : ℕ => β ^ t * crra 1 (x * G ^ t)) := by
  have hfun : (fun t : ℕ => β ^ t * crra 1 (x * G ^ t)) =
      fun t : ℕ => β ^ t * Real.log x + ((t : ℝ) ^ 1 * β ^ t) * Real.log G := by
    funext t
    rw [crra_one_geom hx hG]
    ring
  rw [hfun]
  have hn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hβ]; exact hβ1
  exact ((summable_geometric_of_lt_one hβ hβ1).mul_right _).add
    ((summable_pow_mul_geometric_of_norm_lt_one 1 hn).mul_right _)

/-- **Utility is finite on the balanced path iff `ḡ < r`** (O&R p. 476: "for eq. (61) to
converge, we must assume that `r = A > ḡ`"), exactly, for every `σ > 0` when `0 < β < 1`:
with `1 + ḡ = (β(1+r))^σ`, `∑ βᵗ u(x (1+ḡ)ᵗ) < ∞ ⟺ 1 + ḡ < 1 + r`. -/
theorem summable_balanced_iff {σ β R x : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hβ1 : β < 1)
    (hR : 0 < R) (hx : 0 < x) :
    Summable (fun t : ℕ => β ^ t * crra σ (x * ((β * R) ^ σ) ^ t)) ↔ (β * R) ^ σ < R := by
  have hβR : 0 < β * R := mul_pos hβ hR
  by_cases h1 : σ = 1
  · subst h1
    rw [Real.rpow_one]
    constructor
    · intro _
      nlinarith
    · intro _
      exact summable_geom_log hβ.le hβ1 hx hβR
  · rw [summable_geom_iff h1 hβ hx (Real.rpow_pos_of_pos hβR σ),
      discount_growth_eq hσ hβ hR, div_lt_one hR]

/-- Equivalent forms of the finiteness condition (O&R p. 476, cf. (23)):
`(β(1+A))^σ < 1+A ⟺ β^σ (1+A)^{σ-1} < 1`. -/
theorem growth_lt_iff {σ β R : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    (β * R) ^ σ < R ↔ β ^ σ * R ^ (σ - 1) < 1 := by
  rw [Real.mul_rpow hβ.le hR.le, Real.rpow_sub hR, Real.rpow_one, ← mul_div_assoc,
    div_lt_one hR]

/-- Positive balanced growth (O&R p. 476): `1 + ḡ = (β(1+A))^σ > 1 ⟺ β(1+A) > 1`. -/
theorem one_lt_growth_iff {σ β R : ℝ} (hσ : 0 < σ) (hβR : 0 < β * R) :
    1 < (β * R) ^ σ ↔ 1 < β * R :=
  Real.one_lt_rpow_iff_of_pos hβR |>.trans (by
    constructor
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · exact h
      · exact absurd h (not_lt.mpr hσ.le)
    · intro h
      exact Or.inl ⟨h, hσ⟩)

/-- **Patience raises growth permanently** (O&R p. 476): `1 + ḡ = (β(1+A))^σ` is strictly
increasing in `β`. -/
theorem growth_strictMono_beta {σ R : ℝ} (hσ : 0 < σ) (hR : 0 < R) :
    StrictMonoOn (fun β : ℝ => (β * R) ^ σ) (Set.Ioi 0) := by
  intro a ha b _ hab
  exact Real.rpow_lt_rpow (mul_pos (Set.mem_Ioi.mp ha) hR).le
    (mul_lt_mul_of_pos_right hab hR) hσ

/-! ## Household optimality, and competitive equilibrium with `w_t = (Q - R) k_t` -/

/-- A household plan `(a, c)` is **optimal** at gross return `R` and labour-income stream `w`
(O&R (61)–(62), fn 33): it is feasible (`a ≥ 0`, `c > 0`, budget), has finite utility, and
no feasible plan with finite utility from the same initial assets does better. -/
structure HouseholdOptimal (σ β R : ℝ) (w a c : ℕ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ a t
  pos : ∀ t, 0 < c t
  budget : Budget R 1 w c a
  summable : Summable (fun t => β ^ t * crra σ (c t))
  optimal : ∀ a' c' : ℕ → ℝ, a' 0 = a 0 → (∀ t, 0 ≤ a' t) → (∀ t, 0 < c' t) →
    Budget R 1 w c' a' → Summable (fun t => β ^ t * crra σ (c' t)) →
    ∑' t, β ^ t * crra σ (c' t) ≤ ∑' t, β ^ t * crra σ (c t)

/-- **The balanced plan is optimal** (O&R §7.3.1, genuine infinite horizon). Let
`Q ≥ R > 0`, `G = (βR)^σ < R`, and labour income `w_t = (Q - R) k₀ Gᵗ`. Then
`a_t = k₀ Gᵗ`, `c_t = (Q - G) k₀ Gᵗ` is an optimal household plan. With `Q = R = 1 + A` this is
the AK planner's problem (fn 32); with `Q = 1 + A`, `R = 1 + αA` it is the learning-by-doing
household (fn 33). The proof is the supporting-hyperplane argument with the transversality
term `λ R (G/R)^T k₀ → 0`. -/
theorem balanced_optimal {σ β Q R k₀ : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hβ1 : β < 1)
    (hR : 0 < R) (hQR : R ≤ Q) (hk₀ : 0 < k₀) (hG : (β * R) ^ σ < R) :
    HouseholdOptimal σ β R (fun t => (Q - R) * (k₀ * ((β * R) ^ σ) ^ t))
      (fun t => k₀ * ((β * R) ^ σ) ^ t) (fun t => (Q - (β * R) ^ σ) * k₀ * ((β * R) ^ σ) ^ t) := by
  set G := (β * R) ^ σ with hGdef
  have hGpos : 0 < G := Real.rpow_pos_of_pos (mul_pos hβ hR) σ
  have hx : 0 < (Q - G) * k₀ := mul_pos (by linarith) hk₀
  have hbs : Budget R 1 (fun t => (Q - R) * (k₀ * G ^ t)) (fun t => (Q - G) * k₀ * G ^ t)
      (fun t => k₀ * G ^ t) := by
    intro t
    simp only
    rw [pow_succ]
    ring
  have hsum : Summable (fun t => β ^ t * crra σ ((Q - G) * k₀ * G ^ t)) :=
    (summable_balanced_iff hσ hβ hβ1 hR hx).mpr hG
  refine ⟨fun t => by positivity, fun t => by positivity, hbs, hsum, ?_⟩
  intro a' c' h0 ha' hc' hb' hs'
  have heuler : ∀ t, β ^ t * crraMU σ ((Q - G) * k₀ * G ^ t) =
      crraMU σ ((Q - G) * k₀) * 1 * (R ^ t)⁻¹ := fun t => balanced_euler hσ hβ hR hx t
  have htail : Tendsto (fun T : ℕ => crraMU σ ((Q - G) * k₀) * (R * ((R ^ T)⁻¹ *
      (k₀ * G ^ T)))) atTop (𝓝 0) := by
    have hr : Tendsto (fun T : ℕ => (G / R) ^ T) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hR).mpr hG)
    have := hr.const_mul (crraMU σ ((Q - G) * k₀) * R * k₀)
    rw [mul_zero] at this
    refine this.congr fun T => ?_
    rw [div_pow]
    field_simp
  have := tsum_add_le_of_partial (δ := 0) (N := 0) hs' hsum htail fun T _ => by
    rw [add_zero]
    exact welfare_partial_le hβ.le hR (crraMU_pos σ hx).le
      (fun t => crra_support hσ (hc' t) (by positivity)) heuler hb' hbs h0 T (ha' T)
  rwa [add_zero] at this

/-- Consumption growth from the Euler equation (62): if `u'(x) = βR u'(y)` then
`y = (βR)^σ x`. -/
theorem cons_growth_of_euler {σ β R x y : ℝ} (hσ : 0 < σ) (hβR : 0 < β * R) (hx : 0 < x)
    (hy : 0 < y) (h : crraMU σ x = β * R * crraMU σ y) : y = (β * R) ^ σ * x := by
  unfold crraMU at h
  have h2 := congrArg (fun z => z ^ (-σ)) h
  rw [← Real.rpow_mul hx.le, Real.mul_rpow hβR.le (Real.rpow_pos_of_pos hy _).le,
    ← Real.rpow_mul hy.le, show -(1 / σ) * -σ = 1 by field_simp, Real.rpow_one,
    Real.rpow_one, Real.rpow_neg hβR.le] at h2
  rw [h2, ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hβR σ).ne', one_mul]

/-- Changing a summable sequence at one date shifts its sum by the change. -/
theorem tsum_update_one {f : ℕ → ℝ} (hf : Summable f) (t : ℕ) (x : ℝ) :
    Summable (fun s => f s + if s = t then x else 0) ∧
      ∑' s, (f s + if s = t then x else 0) = ∑' s, f s + x := by
  have h1 := hasSum_ite_eq t x
  exact ⟨hf.add h1.summable, by rw [hf.tsum_add h1.summable, h1.tsum_eq]⟩

/-- Changing a summable sequence at two dates shifts its sum by the two changes. -/
theorem tsum_update_two {f : ℕ → ℝ} (hf : Summable f) (t t' : ℕ) (x y : ℝ) :
    Summable (fun s => f s + ((if s = t then x else 0) + if s = t' then y else 0)) ∧
      ∑' s, (f s + ((if s = t then x else 0) + if s = t' then y else 0)) =
        ∑' s, f s + (x + y) := by
  have h1 := hasSum_ite_eq t x
  have h2 := hasSum_ite_eq t' y
  have h12 := h1.add h2
  exact ⟨hf.add h12.summable, by rw [hf.tsum_add h12.summable, h12.tsum_eq]⟩

/-- **The Euler equation (62) is necessary** (O&R p. 474): at a household optimum with
positive assets at `t + 1`, `u'(c_t) = β R u'(c_{t+1})`. Proof: the one-period perturbation
`c_t - ε`, `c_{t+1} + Rε`, `a_{t+1} + ε` is feasible for small `|ε|`, so
`φ(ε) = u(c_t - ε) + β u(c_{t+1} + Rε)` has a local maximum at `0`. -/
theorem HouseholdOptimal.euler {σ β R : ℝ} {w a c : ℕ → ℝ} (hβ : 0 < β) (hR : 0 < R)
    (h : HouseholdOptimal σ β R w a c) (t : ℕ) (ha : 0 < a (t + 1)) :
    crraMU σ (c t) = β * R * crraMU σ (c (t + 1)) := by
  set φ : ℝ → ℝ := fun ε => crra σ (c t - ε) + β * crra σ (c (t + 1) + R * ε) with hφ
  have hmax : IsLocalMax φ 0 := by
    have hδ : 0 < min (c t) (min (a (t + 1)) (c (t + 1) / R)) :=
      lt_min (h.pos t) (lt_min ha (div_pos (h.pos _) hR))
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with ε hε
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hε
    have h1 : |ε| < c t := lt_of_lt_of_le hε (min_le_left _ _)
    have h2 : |ε| < a (t + 1) :=
      lt_of_lt_of_le hε ((min_le_right _ _).trans (min_le_left _ _))
    have h3 : |ε| < c (t + 1) / R :=
      lt_of_lt_of_le hε ((min_le_right _ _).trans (min_le_right _ _))
    have h3' : |ε| * R < c (t + 1) := (lt_div_iff₀ hR).mp h3
    have e1 := neg_abs_le ε
    have e2 := le_abs_self ε
    set c' : ℕ → ℝ := fun s =>
      if s = t then c t - ε else if s = t + 1 then c (t + 1) + R * ε else c s with hc'
    set a' : ℕ → ℝ := fun s => if s = t + 1 then a (t + 1) + ε else a s with ha'
    have hc'pos : ∀ s, 0 < c' s := by
      intro s
      simp only [hc']
      split_ifs
      · linarith
      · nlinarith
      · exact h.pos s
    have ha'nn : ∀ s, 0 ≤ a' s := by
      intro s
      simp only [ha']
      split_ifs
      · linarith
      · exact h.nonneg s
    have hb' : Budget R 1 w c' a' := by
      intro s
      have hb := h.budget s
      rcases (by omega : s = t ∨ s = t + 1 ∨ (s ≠ t ∧ s ≠ t + 1)) with hs | hs | ⟨hs1, hs2⟩
      · subst hs
        simp [hc', ha']
        linarith
      · subst hs
        simp [hc', ha']
        linarith
      · have hs3 : s + 1 ≠ t + 1 := by omega
        simp [hc', ha', hs1, hs2]
        linarith
    have h0 : a' 0 = a 0 := by simp [ha']
    have hdec : (fun s => β ^ s * crra σ (c' s)) = fun s => β ^ s * crra σ (c s) +
        ((if s = t then β ^ t * (crra σ (c t - ε) - crra σ (c t)) else 0) +
          if s = t + 1 then β ^ (t + 1) * (crra σ (c (t + 1) + R * ε) - crra σ (c (t + 1)))
          else 0) := by
      funext s
      rcases (by omega : s = t ∨ s = t + 1 ∨ (s ≠ t ∧ s ≠ t + 1)) with hs | hs | ⟨hs1, hs2⟩
      · subst hs
        simp [hc']
        ring
      · subst hs
        simp [hc']
        ring
      · simp [hc', hs1, hs2]
    obtain ⟨hsum', htsum'⟩ := tsum_update_two h.summable t (t + 1)
      (β ^ t * (crra σ (c t - ε) - crra σ (c t)))
      (β ^ (t + 1) * (crra σ (c (t + 1) + R * ε) - crra σ (c (t + 1))))
    rw [← hdec] at hsum' htsum'
    have hopt := h.optimal a' c' h0 ha'nn hc'pos hb' hsum'
    rw [htsum'] at hopt
    have hβt : 0 < β ^ t := pow_pos hβ t
    have key : β ^ t * (φ ε - φ 0) ≤ 0 := by
      simp only [hφ, sub_zero, mul_zero, add_zero]
      rw [pow_succ] at hopt
      nlinarith
    by_contra hcon
    push Not at hcon
    have := mul_pos hβt (sub_pos.mpr hcon)
    linarith
  have d1 : HasDerivAt (fun ε : ℝ => crra σ (c t - ε)) (crraMU σ (c t) * (-1)) 0 := by
    have hs : HasDerivAt (fun ε : ℝ => c t - ε) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub (c t)
    have hc0 : HasDerivAt (crra σ) (crraMU σ (c t)) (c t - 0) := by
      rw [sub_zero]
      exact crra_hasDerivAt (h.pos t)
    exact hc0.comp 0 hs
  have d2 : HasDerivAt (fun ε : ℝ => crra σ (c (t + 1) + R * ε))
      (crraMU σ (c (t + 1)) * R) 0 := by
    have hs : HasDerivAt (fun ε : ℝ => c (t + 1) + R * ε) R 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul R).const_add (c (t + 1))
    have hc0 : HasDerivAt (crra σ) (crraMU σ (c (t + 1))) (c (t + 1) + R * 0) := by
      rw [mul_zero, add_zero]
      exact crra_hasDerivAt (h.pos (t + 1))
    exact hc0.comp 0 hs
  have hd : HasDerivAt φ (crraMU σ (c t) * (-1) + β * (crraMU σ (c (t + 1)) * R)) 0 :=
    d1.add (d2.const_mul β)
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-- **Uniqueness of competitive equilibrium: the economy is on its balanced path from date
0** (O&R p. 476: "there is no transition period"; p. 478 for learning by doing). Let
`0 < R ≤ Q`, `0 < β < 1`, and suppose `(k, c)` is an equilibrium: the household's optimal plan
at gross return `R` with labour income `w_t = (Q - R) k_t` (so that the budget is the resource
constraint `k_{t+1} = Q k_t - c_t`). Then necessarily `G = (βR)^σ < R`, and
`k_t = k_0 Gᵗ`, `c_t = (Q - G) k_t` for all `t`. The proof derives the Euler equation from
optimality, rules out `c_0 > (Q - G) k_0` by feasibility, and rules out `c_0 < (Q - G) k_0`
by exhibiting a feasible plan that consumes the unused wealth at date 0. -/
theorem equilibrium_unique {σ β Q R : ℝ} {k c : ℕ → ℝ} (hσ : 0 < σ) (hβ : 0 < β)
    (hβ1 : β < 1) (hR : 0 < R) (hQR : R ≤ Q)
    (h : HouseholdOptimal σ β R (fun t => (Q - R) * k t) k c) :
    (β * R) ^ σ < R ∧ ∀ t, k t = k 0 * ((β * R) ^ σ) ^ t ∧
      c t = (Q - (β * R) ^ σ) * k t := by
  set G := (β * R) ^ σ with hGdef
  have hβR : 0 < β * R := mul_pos hβ hR
  have hGpos : 0 < G := Real.rpow_pos_of_pos hβR σ
  have hQ : 0 < Q := lt_of_lt_of_le hR hQR
  have hres : ∀ t, k (t + 1) = Q * k t - c t := fun t => by
    rw [h.budget t]
    ring
  have hkpos : ∀ t, 0 < k (t + 1) := by
    intro t
    have h1 := hres (t + 1)
    have h2 := h.nonneg (t + 2)
    have h3 := h.pos (t + 1)
    by_contra hk
    push Not at hk
    nlinarith
  have hgrow : ∀ t, c (t + 1) = G * c t := fun t =>
    cons_growth_of_euler hσ hβR (h.pos t) (h.pos (t + 1)) (h.euler hβ hR t (hkpos t))
  have hc : ∀ t, c t = c 0 * G ^ t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [hgrow t, ih, pow_succ]; ring
  have hGR : G < R := by
    have hs := h.summable
    have hfun : (fun t => β ^ t * crra σ (c t)) = fun t => β ^ t * crra σ (c 0 * G ^ t) := by
      funext t
      rw [hc t]
    rw [hfun] at hs
    exact (summable_balanced_iff hσ hβ hβ1 hR (h.pos 0)).mp hs
  have hQG : 0 < Q - G := by linarith
  set D := k 0 - c 0 / (Q - G) with hD
  have hclosed : ∀ T, k T = D * Q ^ T + c 0 / (Q - G) * G ^ T := by
    intro T
    induction T with
    | zero => simp [hD]
    | succ T ih =>
      rw [hres T, ih, hc T, pow_succ, pow_succ]
      field_simp
      ring
  have hDnn : 0 ≤ D := by
    by_contra hneg
    push Not at hneg
    have hlim : Tendsto (fun T : ℕ => D + c 0 / (Q - G) * (G / Q) ^ T) atTop (𝓝 D) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (r := G / Q) (by positivity)
        ((div_lt_one hQ).mpr (by linarith))).const_mul (c 0 / (Q - G))).const_add D
      simpa using this
    obtain ⟨T, hT⟩ := (hlim.eventually (gt_mem_nhds hneg)).exists
    have hkT := h.nonneg T
    rw [hclosed T] at hkT
    have : D * Q ^ T + c 0 / (Q - G) * G ^ T = Q ^ T * (D + c 0 / (Q - G) * (G / Q) ^ T) := by
      rw [div_pow]
      field_simp
    rw [this] at hkT
    have := pow_pos hQ T
    nlinarith
  have hDnp : D ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set c' : ℕ → ℝ := fun s => if s = 0 then c 0 + D * R else c s with hc'
    set a' : ℕ → ℝ := fun s => if s = 0 then k 0 else k s - D * R ^ s with ha'
    have hc'pos : ∀ s, 0 < c' s := by
      intro s
      simp only [hc']
      split_ifs
      · have := h.pos 0
        positivity
      · exact h.pos s
    have hlow : ∀ s, D * R ^ s ≤ k s := by
      intro s
      rw [hclosed s]
      have h1 : R ^ s ≤ Q ^ s := pow_le_pow_left₀ hR.le hQR s
      have h2 : 0 ≤ c 0 / (Q - G) * G ^ s := by
        have := h.pos 0
        positivity
      nlinarith
    have ha'nn : ∀ s, 0 ≤ a' s := by
      intro s
      simp only [ha']
      split_ifs
      · exact h.nonneg 0
      · linarith [hlow s]
    have hb' : Budget R 1 (fun t => (Q - R) * k t) c' a' := by
      intro s
      have hb := h.budget s
      rcases Nat.eq_zero_or_pos s with hs | hs
      · subst hs
        simp [hc', ha']
        simp at hb
        linarith
      · have hs1 : s ≠ 0 := by omega
        simp only [hc', ha', hs1, Nat.add_one_ne_zero, ↓reduceIte, one_mul]
        simp only [one_mul] at hb
        rw [pow_succ]
        linarith
    have hdec : (fun s => β ^ s * crra σ (c' s)) = fun s => β ^ s * crra σ (c s) +
        if s = 0 then crra σ (c 0 + D * R) - crra σ (c 0) else 0 := by
      funext s
      rcases Nat.eq_zero_or_pos s with hs | hs
      · subst hs
        simp [hc']
      · have hs1 : s ≠ 0 := by omega
        simp [hc', hs1]
    obtain ⟨hsum', htsum'⟩ := tsum_update_one h.summable 0
      (crra σ (c 0 + D * R) - crra σ (c 0))
    rw [← hdec] at hsum' htsum'
    have hopt := h.optimal a' c' (by simp [ha']) ha'nn hc'pos hb' hsum'
    rw [htsum'] at hopt
    have hinc : crra σ (c 0) < crra σ (c 0 + D * R) :=
      crra_strictMonoOn hσ (Set.mem_Ioi.mpr (h.pos 0))
        (Set.mem_Ioi.mpr (by have := h.pos 0; positivity)) (by nlinarith)
    linarith
  have hD0 : D = 0 := le_antisymm hDnp hDnn
  have hk0 : k 0 = c 0 / (Q - G) := by linarith [hD]
  refine ⟨hGR, fun t => ⟨?_, ?_⟩⟩
  · rw [hclosed t, hD0, hk0]
    ring
  · rw [hc t, hclosed t, hD0]
    field_simp
    ring

/-- Existence and uniqueness together: when `(βR)^σ < R` the balanced plan is the unique
equilibrium; when `(βR)^σ ≥ R` there is no equilibrium at all (utility cannot be finite),
O&R p. 476. -/
theorem no_equilibrium_of_growth_ge {σ β Q R : ℝ} {k c : ℕ → ℝ} (hσ : 0 < σ) (hβ : 0 < β)
    (hβ1 : β < 1) (hR : 0 < R) (hQR : R ≤ Q) (hGR : R ≤ (β * R) ^ σ) :
    ¬ HouseholdOptimal σ β R (fun t => (Q - R) * k t) k c := fun h =>
  absurd (equilibrium_unique hσ hβ hβ1 hR hQR h).1 (not_lt.mpr hGR)

/-- The transversality term of the balanced plan vanishes: `λ R R^{-T} k₀ Gᵀ → 0` when
`0 < G < R` (O&R p. 476, the condition `A > ḡ`). -/
theorem balanced_tail {R G k₀ lam : ℝ} (hR : 0 < R) (hG : 0 < G) (hGR : G < R) :
    Tendsto (fun T : ℕ => lam * (R * ((R ^ T)⁻¹ * (k₀ * G ^ T)))) atTop (𝓝 0) := by
  have hr : Tendsto (fun T : ℕ => (G / R) ^ T) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hR).mpr hGR)
  have := hr.const_mul (lam * R * k₀)
  rw [mul_zero] at this
  refine this.congr fun T => ?_
  rw [div_pow]
  field_simp

/-! ## The AK model (63)–(65) -/

/-- Gross balanced growth rate of the AK model, O&R (65), p. 475: `1 + ḡ = [β(1+A)]^σ`. -/
noncomputable def akGrowth (β A σ : ℝ) : ℝ := (β * (1 + A)) ^ σ

/-- O&R (62), (64)–(65), p. 475: at `r = A` the Euler equation gives
`1 + A = (1/β)(1 + ḡ)^{1/σ}` with `1 + ḡ = [β(1+A)]^σ`. -/
theorem ak_euler (σ β A : ℝ) (hσ : 0 < σ) (hβ : 0 < β) (hA : 0 < 1 + A) :
    1 + A = (1 / β) * akGrowth β A σ ^ (1 / σ) :=
  balanced_growth_euler hσ hβ hA

/-- **Finite utility iff `ḡ < A`** (O&R p. 476, exact for every `σ > 0`): along the
balanced path `c_t = c₀ (1+ḡ)ᵗ`, `∑ βᵗ u(c_t) < ∞ ⟺ 1 + ḡ < 1 + A`, equivalently
`β^σ (1+A)^{σ-1} < 1`. -/
theorem ak_finite_utility_iff {σ β A c₀ : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hβ1 : β < 1)
    (hA : 0 < 1 + A) (hc₀ : 0 < c₀) :
    (Summable (fun t : ℕ => β ^ t * crra σ (c₀ * akGrowth β A σ ^ t)) ↔
      akGrowth β A σ - 1 < A) ∧
    (akGrowth β A σ < 1 + A ↔ β ^ σ * (1 + A) ^ (σ - 1) < 1) := by
  refine ⟨(summable_balanced_iff hσ hβ hβ1 hA hc₀).trans ?_, growth_lt_iff hβ hA⟩
  unfold akGrowth
  constructor <;> intro h <;> linarith

/-- **The AK planner's optimum** (O&R fn 32, p. 476, genuine infinite horizon): if
`1 + ḡ = [β(1+A)]^σ < 1 + A`, the plan `k_t = k₀(1+ḡ)ᵗ`, `c_t = (A - ḡ) k_t` maximises
`∑ βᵗ u(c_t)` subject to `k_{t+1} = (1+A)k_t - c_t`, `k_t ≥ 0`. -/
theorem ak_planner_optimal {σ β A k₀ : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hβ1 : β < 1)
    (hA : 0 < 1 + A) (hk₀ : 0 < k₀) (hG : akGrowth β A σ < 1 + A) :
    HouseholdOptimal σ β (1 + A) (fun _ => 0) (fun t => k₀ * akGrowth β A σ ^ t)
      (fun t => (1 + A - akGrowth β A σ) * k₀ * akGrowth β A σ ^ t) := by
  have := balanced_optimal (Q := 1 + A) hσ hβ hβ1 hA le_rfl hk₀ hG
  have hw : (fun t => (1 + A - (1 + A)) * (k₀ * ((β * (1 + A)) ^ σ) ^ t)) = fun _ => (0 : ℝ) := by
    funext t
    ring
  rw [hw] at this
  exact this

/-- **Uniqueness and no transition dynamics in the AK model** (O&R p. 476): every optimal
plan of the AK planner is the balanced plan, `k_t = k₀(1+ḡ)ᵗ` and `c_t = (A - ḡ) k_t`, and
optimality forces `ḡ < A`. -/
theorem ak_planner_unique {σ β A : ℝ} {k c : ℕ → ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hβ1 : β < 1)
    (hA : 0 < 1 + A) (h : HouseholdOptimal σ β (1 + A) (fun _ => 0) k c) :
    akGrowth β A σ < 1 + A ∧ ∀ t, k t = k 0 * akGrowth β A σ ^ t ∧
      c t = (1 + A - akGrowth β A σ) * k t := by
  have hw : (fun _ : ℕ => (0 : ℝ)) = fun t => (1 + A - (1 + A)) * k t := by
    funext t
    ring
  rw [hw] at h
  exact equilibrium_unique hσ hβ hβ1 hA le_rfl h

/-- When `[β(1+A)]^σ ≥ 1 + A` (utility unbounded along the candidate path) the AK planner has
no optimal plan at all (O&R p. 476, "we must assume that `A > ḡ`"). -/
theorem ak_no_optimum {σ β A : ℝ} {k c : ℕ → ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hβ1 : β < 1)
    (hA : 0 < 1 + A) (hG : 1 + A ≤ akGrowth β A σ) :
    ¬ HouseholdOptimal σ β (1 + A) (fun _ => 0) k c := fun h =>
  absurd (ak_planner_unique hσ hβ hβ1 hA h).1 (not_lt.mpr hG)

/-- Investment and consumption shares on the AK balanced path (O&R p. 476):
`i_t = k_{t+1} - k_t = ḡ k_t = (ḡ/A) y_t` and `c_t = ((A - ḡ)/A) y_t`, with `y_t = A k_t`. -/
theorem ak_shares {A g k : ℝ} (hA : A ≠ 0) :
    k * (1 + g) - k = g / A * (A * k) ∧ (1 + A - (1 + g)) * k = (A - g) / A * (A * k) := by
  constructor <;> field_simp <;> ring

/-- Firms' capital demand (O&R (64), p. 475): the profit `(A - r) k` from renting `k ≥ 0` is
bounded above iff `r ≥ A` ("at any interest rate other than `A`, firms would want to invest
either an infinite amount or zero"). -/
theorem ak_firm_bounded_iff {A r : ℝ} :
    (∃ M, ∀ k, 0 ≤ k → (A - r) * k ≤ M) ↔ A ≤ r := by
  constructor
  · rintro ⟨M, hM⟩
    by_contra hlt
    push Not at hlt
    have hpos : 0 < A - r := by linarith
    have := hM ((|M| + 1) / (A - r)) (by positivity)
    rw [mul_div_cancel₀ _ hpos.ne'] at this
    linarith [le_abs_self M]
  · intro h
    exact ⟨0, fun k hk => mul_nonpos_of_nonpos_of_nonneg (by linarith) hk⟩

/-- O&R (64): firms demand a positive, finite capital stock (an interior profit maximum) iff
`r = A`. -/
theorem ak_firm_interior_iff {A r : ℝ} :
    (∃ k, 0 < k ∧ ∀ k', 0 ≤ k' → (A - r) * k' ≤ (A - r) * k) ↔ r = A := by
  constructor
  · rintro ⟨k, hk, hmax⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := hmax (2 * k) (by linarith)
      nlinarith
    · have := hmax 0 le_rfl
      nlinarith
  · intro h
    exact ⟨1, one_pos, fun k' _ => by rw [h, sub_self, zero_mul, zero_mul]⟩

/-- **The market outcome is Pareto optimal** (O&R p. 476): in a competitive equilibrium the
firm's interior demand forces `r = A`, profits are zero (fn 33: nothing is left for labour),
and the household's optimal plan is then exactly the planner's unique optimum. -/
theorem ak_competitive_eq_planner {σ β A r : ℝ} {k c : ℕ → ℝ} (hσ : 0 < σ) (hβ : 0 < β)
    (hβ1 : β < 1) (hA : 0 < 1 + A)
    (hfirm : ∃ K, 0 < K ∧ ∀ K', 0 ≤ K' → (A - r) * K' ≤ (A - r) * K)
    (h : HouseholdOptimal σ β (1 + r) (fun _ => 0) k c) :
    r = A ∧ ∀ t, k t = k 0 * akGrowth β A σ ^ t ∧ c t = (1 + A - akGrowth β A σ) * k t := by
  have hr := ak_firm_interior_iff.mp hfirm
  subst hr
  exact ⟨rfl, (ak_planner_unique hσ hβ hβ1 hA h).2⟩

/-! ## Learning by doing (66)–(68) -/

/-- Firm output with a learning-by-doing externality, O&R (66), p. 476:
`y^j = A (k^j)^α k^{1-α}`. -/
noncomputable def lbdOutput (A α kj k : ℝ) : ℝ := A * kj ^ α * k ^ (1 - α)

/-- **Private marginal product** O&R (67), p. 477: `∂y^j/∂k^j = αA (k/k^j)^{1-α}`. -/
theorem lbd_private_mpk {A α kj k : ℝ} (hkj : 0 < kj) (hk : 0 < k) :
    HasDerivAt (fun x => lbdOutput A α x k) (α * A * (k / kj) ^ (1 - α)) kj := by
  unfold lbdOutput
  have h := ((Real.hasDerivAt_rpow_const (p := α) (Or.inl hkj.ne')).const_mul A).mul_const
    (k ^ (1 - α))
  convert h using 1
  rw [Real.div_rpow hk.le hkj.le, show α - 1 = -(1 - α) by ring, Real.rpow_neg hkj.le]
  field_simp

/-- O&R (68), p. 477: in the symmetric equilibrium `k^j = k` the private marginal product
(the market interest rate) is `αA`, independent of `k`. -/
theorem lbd_market_rate {A α k : ℝ} (hk : 0 < k) : α * A * (k / k) ^ (1 - α) = α * A := by
  rw [div_self hk.ne', Real.one_rpow, mul_one]

/-- **Firm optimality at `r = αA`** (O&R (67)–(68) and fn 33): taking aggregate `k` as
given, the firm's profit `A (k^j)^α k^{1-α} - αA k^j` is maximised at `k^j = k`, where it
equals the labour share `(1-α) A k` — "payments to capital no longer exhaust output". -/
theorem lbd_firm_optimal {A α k : ℝ} (hA : 0 < A) (hα : 0 < α) (hα1 : α < 1) (hk : 0 < k) :
    (∀ x, 0 ≤ x → lbdOutput A α x k - α * A * x ≤ lbdOutput A α k k - α * A * k) ∧
      lbdOutput A α k k - α * A * k = (1 - α) * A * k := by
  have hkk : lbdOutput A α k k = A * k := by
    unfold lbdOutput
    rw [mul_assoc, ← Real.rpow_add hk, show α + (1 - α) = 1 by ring, Real.rpow_one]
  refine ⟨fun x hx => ?_, by rw [hkk]; ring⟩
  rw [hkk]
  unfold lbdOutput
  have hgm := Real.geom_mean_le_arith_mean2_weighted hα.le (by linarith : 0 ≤ 1 - α) hx hk.le
    (by ring)
  nlinarith

/-- **Learning-by-doing competitive equilibrium: existence and uniqueness** (O&R pp. 477–478).
Households earn `r = αA` on capital and the labour share `w_t = (1-α)A k_t` (fn 33), so
the equilibrium is `equilibrium_unique` with `Q = 1 + A`, `R = 1 + αA`. If
`1 + ḡ = [β(1+αA)]^σ < 1 + αA` the balanced path `k_t = k₀(1+ḡ)ᵗ`, `c_t = (A - ḡ)k_t` is an
equilibrium, and every equilibrium is this path. -/
theorem lbd_equilibrium {σ β A α k₀ : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hβ1 : β < 1)
    (hA : 0 < A) (hα : 0 < α) (hα1 : α < 1) (hk₀ : 0 < k₀)
    (hG : (β * (1 + α * A)) ^ σ < 1 + α * A) :
    HouseholdOptimal σ β (1 + α * A)
        (fun t => (1 + A - (1 + α * A)) * (k₀ * ((β * (1 + α * A)) ^ σ) ^ t))
        (fun t => k₀ * ((β * (1 + α * A)) ^ σ) ^ t)
        (fun t => (1 + A - (β * (1 + α * A)) ^ σ) * k₀ * ((β * (1 + α * A)) ^ σ) ^ t) ∧
      ∀ k c : ℕ → ℝ,
        HouseholdOptimal σ β (1 + α * A) (fun t => (1 + A - (1 + α * A)) * k t) k c →
        ∀ t, k t = k 0 * ((β * (1 + α * A)) ^ σ) ^ t ∧
          c t = (1 + A - (β * (1 + α * A)) ^ σ) * k t := by
  have hR : 0 < 1 + α * A := by positivity
  have hQR : 1 + α * A ≤ 1 + A := by nlinarith
  exact ⟨balanced_optimal hσ hβ hβ1 hR hQR hk₀ hG,
    fun k c h => (equilibrium_unique hσ hβ hβ1 hR hQR h).2⟩

/-- **Market growth is suboptimally low** (O&R Fig. 7.13, p. 478):
`[β(1+αA)]^σ < [β(1+A)]^σ` for `0 < α < 1`, `A > 0`. -/
theorem lbd_market_growth_lt_social {σ β A α : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hA : 0 < A)
    (hα1 : α < 1) (hα : 0 < α) :
    (β * (1 + α * A)) ^ σ < akGrowth β A σ := by
  unfold akGrowth
  exact Real.rpow_lt_rpow (by positivity) (mul_lt_mul_of_pos_left (by nlinarith) hβ) hσ

/-- The finiteness conditions differ (O&R p. 478 omits the planner's): for `σ ≥ 1` a finite
planner problem implies a finite market problem, `β^σ(1+A)^{σ-1} < 1 ⇒ β^σ(1+αA)^{σ-1} < 1`. -/
theorem lbd_finite_market_of_planner {σ β A α : ℝ} (hσ : 1 ≤ σ) (hβ : 0 < β) (hA : 0 < A)
    (hα : 0 < α) (hα1 : α < 1) (h : β ^ σ * (1 + A) ^ (σ - 1) < 1) :
    β ^ σ * (1 + α * A) ^ (σ - 1) < 1 := by
  have : (1 + α * A) ^ (σ - 1) ≤ (1 + A) ^ (σ - 1) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
  have hb : 0 < β ^ σ := Real.rpow_pos_of_pos hβ σ
  nlinarith

/-- For `σ ≤ 1` the implication reverses: a finite market problem implies a finite planner
problem (O&R p. 478). -/
theorem lbd_finite_planner_of_market {σ β A α : ℝ} (hσ : σ ≤ 1) (hβ : 0 < β) (hA : 0 < A)
    (hα : 0 < α) (hα1 : α < 1) (h : β ^ σ * (1 + α * A) ^ (σ - 1) < 1) :
    β ^ σ * (1 + A) ^ (σ - 1) < 1 := by
  have : (1 + A) ^ (σ - 1) ≤ (1 + α * A) ^ (σ - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)
  have hb : 0 < β ^ σ := Real.rpow_pos_of_pos hβ σ
  nlinarith

/-- **Counterexample: the planner needs its own finiteness condition** (O&R p. 478): with
`σ = 2`, `β = 9/10`, `A = 1/2`, `α = 1/5`, the market problem is finite
(`[β(1+αA)]^σ = 0.9801 < 1.1 = 1+αA`) but the planner's is not
(`[β(1+A)]^σ = 1.8225 ≥ 1.5 = 1+A`), so the social optimum does not exist. -/
theorem lbd_planner_infinite_example :
    ((9 / 10 : ℝ) * (1 + 1 / 5 * (1 / 2))) ^ (2 : ℝ) < 1 + 1 / 5 * (1 / 2) ∧
      (1 + 1 / 2 : ℝ) ≤ akGrowth (9 / 10) (1 / 2) 2 := by
  unfold akGrowth
  rw [Real.rpow_two, Real.rpow_two]
  constructor <;> norm_num

/-- **The optimal subsidy** (O&R p. 478): an output subsidy at rate `s = (1-α)/α` raises the
firms' private return `(1+s)αA` to the social return `A`. -/
theorem lbd_subsidy_rate {A α : ℝ} (hα : 0 < α) : (1 + (1 - α) / α) * α * A = A := by
  field_simp
  ring

/-- **The subsidised equilibrium implements the social optimum, financed by a neutral
consumption tax** (O&R p. 478). With subsidy `s = (1-α)/α` (so `r = A`), wage
`w_t = (1+s)(1-α)A k_t`, and a constant consumption tax `τ = sA/(1+A-ḡ)` balancing the
government budget `τ c_t = s y_t`, the planner's path satisfies the household budget
`k_{t+1} = (1+A)k_t + w_t - (1+τ)c_t` and is the household's optimum among all feasible plans:
the constant tax leaves the Euler equation unchanged. -/
theorem lbd_subsidy_implements_optimum {σ β A α k₀ : ℝ} (hσ : 0 < σ) (hβ : 0 < β)
    (hβ1 : β < 1) (hA : 0 < A) (hα : 0 < α) (hα1 : α < 1) (hk₀ : 0 < k₀)
    (hG : akGrowth β A σ < 1 + A) :
    let G := akGrowth β A σ
    let s := (1 - α) / α
    let τ := s * A / (1 + A - G)
    let k := fun t : ℕ => k₀ * G ^ t
    let c := fun t : ℕ => (1 + A - G) * k₀ * G ^ t
    let w := fun t : ℕ => (1 + s) * (1 - α) * A * k t
    (∀ t, τ * c t = s * (A * k t)) ∧ Budget (1 + A) (1 + τ) w c k ∧
      ∀ a' c' : ℕ → ℝ, a' 0 = k₀ → (∀ t, 0 ≤ a' t) → (∀ t, 0 < c' t) →
        Budget (1 + A) (1 + τ) w c' a' → Summable (fun t => β ^ t * crra σ (c' t)) →
        ∑' t, β ^ t * crra σ (c' t) ≤ ∑' t, β ^ t * crra σ (c t) := by
  intro G s τ k c w
  have hR : 0 < 1 + A := by linarith
  have hGpos : 0 < G := Real.rpow_pos_of_pos (mul_pos hβ hR) σ
  have hQG : 0 < 1 + A - G := by linarith
  have hx : 0 < (1 + A - G) * k₀ := mul_pos hQG hk₀
  have hs : 0 ≤ s := div_nonneg (by linarith) hα.le
  have hτ : 0 ≤ τ := by positivity
  have hgov : ∀ t, τ * c t = s * (A * k t) := by
    intro t
    simp only [τ, c, k]
    field_simp
  have hτ' : τ * (1 + A - G) = s * A := by
    simp only [τ]
    field_simp
  have hsα : s * α = 1 - α := by
    simp only [s]
    field_simp
  have hbud : Budget (1 + A) (1 + τ) w c k := by
    intro t
    simp only [w, k, c]
    rw [pow_succ]
    linear_combination (k₀ * G ^ t) * hτ' + (k₀ * G ^ t * A) * hsα
  refine ⟨hgov, hbud, ?_⟩
  intro a' c' h0 ha' hc' hb' hs'
  have hsum : Summable (fun t => β ^ t * crra σ (c t)) :=
    (summable_balanced_iff hσ hβ hβ1 hR hx).mpr hG
  have heuler : ∀ t, β ^ t * crraMU σ (c t) =
      crraMU σ ((1 + A - G) * k₀) / (1 + τ) * (1 + τ) * ((1 + A) ^ t)⁻¹ := by
    intro t
    rw [div_mul_cancel₀ _ (by positivity : (1 + τ) ≠ 0)]
    have := balanced_euler hσ hβ hR hx t
    rw [mul_one] at this
    exact this
  have := tsum_add_le_of_partial (δ := 0) (N := 0) hs' hsum
    (balanced_tail (lam := crraMU σ ((1 + A - G) * k₀) / (1 + τ)) (k₀ := k₀) hR hGpos hG)
    fun T _ => by
      rw [add_zero]
      exact welfare_partial_le hβ.le hR (div_nonneg (crraMU_pos σ hx).le (by positivity))
        (fun t => crra_support hσ (hc' t) (by positivity)) heuler hb' hbud (by rw [h0]; simp [k])
        T (ha' T)
  rwa [add_zero] at this

end ObstfeldRogoff.GlobalGrowth.AKModel
