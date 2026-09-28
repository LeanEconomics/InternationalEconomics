/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The debt ceiling under direct sanctions

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §6.2.1.1,
pp. 379–387 (eqs. (23)–(30), footnotes 31–37).

A small country with utility `u(C₁) + βu(C₂)` borrows `D` on date 1, invests `K`
(`K₁ = 0`, no depreciation, capital "eaten" at the end), so `C₁ = Y₁ + D − K` and
`C₂ = F(K) + K − ℜ` with the repayment (23) `ℜ = min{(1+r)D, η[F(K)+K]}`. After the loan the
sovereign maximises (24) over `K`.

We prove:
* (24) is the maximum of the *repay* objective and the *default* objective ("max of max"),
  so the sovereign's value is the larger of the two maxima; default happens exactly when the
  default maximum is strictly larger (ties repay), and the repay optimum then honours (23);
* the key point of p. 385 and footnote 37, in general: at an interior, differentiable repay
  optimum that is (weakly) preferred to default — in particular at the ceiling `D̄` where the
  sovereign is indifferent — sanctions are *strictly* more than sufficient,
  `η[F(K^B)+K^B] > (1+r)D`, the repay and default optima are distinct, and the "kink"
  investment `K̄` with `η[F(K̄)+K̄] = (1+r)D̄` lies strictly below `K^B`: the literature's
  characterisation of `D̄` by `η[F(K(D̄))+K(D̄)] = (1+r)D̄` is wrong;
* the log-linear example (`u = log`, `F = αK`): the optima (27), (29), the maximised utilities,
  the gap `U^D − U^N` of p. 384 and its strict monotonicity in `D₂/Y₁`, the ceiling (30), its
  positivity under (25) (footnote 33), the comparative statics claimed on p. 384 (`D̄` rises
  with `η`, `β`, `α`, falls with `r`), the downward investment jump at `D̄`, continuity of the
  sovereign's value, the loci of footnote 36, and the strict slack of (23) at `D̄`;
* the *repayment-set interval property* that §6.2.1.2 uses ("for any `D₂ ≤ D̄` the sovereign
  repays"). It is not proved in the book. We prove it (the repay-preferred set is an initial
  segment) (a) for every CRRA utility and every linear technology, whether or not (25) holds, by
  a scaling argument, and (b) for EVERY strictly increasing, concave, differentiable `u` and
  concave differentiable `F`, given optimal plans, under the analogue of (25) at the repay
  optimum, `η(1 + F′(K^N)) < 1 + r` (`repay_interval_of_ineq25`: an envelope/real-induction
  argument). Without that condition it FAILS: an explicit counterexample with strictly
  increasing, strictly concave `u` and `F` has the sovereign default at `D = 1/2` but repay at
  `D = 5/2`. (The tempting envelope argument "`d(U^N − U^D)/dD = −β(1+r)u′(C₂ᴺ) < 0`" is wrong:
  the date-1 marginal utilities are evaluated at different investment levels and do not cancel.)

Feasibility means strictly positive consumption on both dates (the book ignores `K ≥ 0`,
footnote 31 and p. 383; with `F(K) + K > 0 ⇔ K > 0` for the technologies used here it is
implied).
-/

namespace ObstfeldRogoff.CapitalMarketImperfections.DebtCeiling

open Real Set Filter Topology

/-! ## General structure: (23), (24) and the max-of-max -/

/-- The repayment (23), O&R p. 380: `ℜ = min{(1+r)D, η[F(K)+K]}` (full repayment on a tie). -/
def repayment (F : ℝ → ℝ) (r η D K : ℝ) : ℝ := min ((1 + r) * D) (η * (F K + K))

/-- The sovereign's post-loan objective (24), O&R p. 381:
`u(Y₁ + D − K) + βu(F(K) + K − min{(1+r)D, η[F(K)+K]})`. -/
def sovereignObjective (u F : ℝ → ℝ) (Y₁ r η β D K : ℝ) : ℝ :=
  u (Y₁ + D - K) + β * u (F K + K - repayment F r η D K)

/-- The objective when the sovereign repays in full (the problem defining `U^N`),
O&R p. 383: `u(Y₁ + D − K) + βu(F(K) + K − (1+r)D)` (the GNPᴺ locus). -/
def repayObjective (u F : ℝ → ℝ) (Y₁ r β D K : ℝ) : ℝ :=
  u (Y₁ + D - K) + β * u (F K + K - (1 + r) * D)

/-- The objective when the sovereign defaults (the problem defining `U^D`), O&R p. 383:
`u(Y₁ + D − K) + βu((1−η)[F(K) + K])` (the GNPᴰ locus). -/
def defaultObjective (u F : ℝ → ℝ) (Y₁ η β D K : ℝ) : ℝ :=
  u (Y₁ + D - K) + β * u ((1 - η) * (F K + K))

/-- Full repayment under (23), O&R p. 380: `ℜ = (1+r)D` iff `(1+r)D ≤ η[F(K)+K]`
(ties repay); otherwise the country pays the sanction `η[F(K)+K] < (1+r)D`. -/
theorem repayment_eq_full_iff (F : ℝ → ℝ) (r η D K : ℝ) :
    repayment F r η D K = (1 + r) * D ↔ (1 + r) * D ≤ η * (F K + K) := by
  unfold repayment
  constructor
  · intro h
    rw [← h]
    exact min_le_right _ _
  · intro h
    exact min_eq_left h

/-- "Max of max", O&R (24), p. 381 and Figure 6.3: when `u` is increasing on the positive reals
and both candidate date-2 consumptions are positive, the objective (24) is the upper envelope
of the repay and default objectives (the outer envelope of GNPᴺ and GNPᴰ). -/
theorem sovereignObjective_eq_max {u F : ℝ → ℝ} (hu : MonotoneOn u (Ioi 0))
    {Y₁ r η β D K : ℝ} (hβ : 0 ≤ β) (hN : 0 < F K + K - (1 + r) * D)
    (hD : 0 < (1 - η) * (F K + K)) :
    sovereignObjective u F Y₁ r η β D K =
      max (repayObjective u F Y₁ r β D K) (defaultObjective u F Y₁ η β D K) := by
  unfold sovereignObjective repayObjective defaultObjective repayment
  rcases le_total ((1 + r) * D) (η * (F K + K)) with h | h
  · rw [min_eq_left h, eq_comm, max_eq_left]
    have : u ((1 - η) * (F K + K)) ≤ u (F K + K - (1 + r) * D) :=
      hu (mem_Ioi.mpr hD) (mem_Ioi.mpr hN) (by linarith)
    nlinarith
  · rw [min_eq_right h, show F K + K - η * (F K + K) = (1 - η) * (F K + K) by ring, eq_comm,
      max_eq_right]
    have : u (F K + K - (1 + r) * D) ≤ u ((1 - η) * (F K + K)) :=
      hu (mem_Ioi.mpr hN) (mem_Ioi.mpr hD) (by linarith)
    nlinarith

/-- The sovereign's value is the larger of the two maxima, O&R p. 383 ("the utility maxima …
are compared"): if `K^N` maximises the repay objective and `K^D` the default objective on a
set `S` of plans on which (24) is the envelope, then (24) is bounded on `S` by
`max(U^N, U^D)`. -/
theorem sovereignObjective_le_max {u F : ℝ → ℝ} (hu : MonotoneOn u (Ioi 0))
    {Y₁ r η β D : ℝ} (hβ : 0 ≤ β) {S : Set ℝ}
    (hpos : ∀ K ∈ S, 0 < F K + K - (1 + r) * D ∧ 0 < (1 - η) * (F K + K)) {KN KD : ℝ}
    (hN : IsMaxOn (repayObjective u F Y₁ r β D) S KN)
    (hD : IsMaxOn (defaultObjective u F Y₁ η β D) S KD) :
    ∀ K ∈ S, sovereignObjective u F Y₁ r η β D K ≤
      max (repayObjective u F Y₁ r β D KN) (defaultObjective u F Y₁ η β D KD) := by
  intro K hK
  rw [sovereignObjective_eq_max hu hβ (hpos K hK).1 (hpos K hK).2]
  exact max_le_max (isMaxOn_iff.mp hN K hK) (isMaxOn_iff.mp hD K hK)

/-- Repayment when `U^N ≥ U^D`, O&R p. 384 ("in a tie, repays"): if the repay maximum is at
least the default maximum, the repay optimum `K^N` also maximises (24), the sovereign's value
is `U^N`, and at `K^N` full repayment is incentive compatible, `(1+r)D ≤ η[F(K^N)+K^N]`
(`u` strictly increasing, `β > 0`). -/
theorem repay_optimal_of_value_ge {u F : ℝ → ℝ} (hu : StrictMonoOn u (Ioi 0))
    {Y₁ r η β D : ℝ} (hβ : 0 < β) {S : Set ℝ}
    (hpos : ∀ K ∈ S, 0 < F K + K - (1 + r) * D ∧ 0 < (1 - η) * (F K + K)) {KN KD : ℝ}
    (hKN : KN ∈ S) (hN : IsMaxOn (repayObjective u F Y₁ r β D) S KN)
    (hD : IsMaxOn (defaultObjective u F Y₁ η β D) S KD)
    (hge : defaultObjective u F Y₁ η β D KD ≤ repayObjective u F Y₁ r β D KN) :
    IsMaxOn (sovereignObjective u F Y₁ r η β D) S KN ∧
      sovereignObjective u F Y₁ r η β D KN = repayObjective u F Y₁ r β D KN ∧
      (1 + r) * D ≤ η * (F KN + KN) := by
  have hle := sovereignObjective_le_max hu.monotoneOn hβ.le hpos hN hD
  rw [max_eq_left hge] at hle
  have hdef : defaultObjective u F Y₁ η β D KN ≤ repayObjective u F Y₁ r β D KN :=
    (isMaxOn_iff.mp hD KN hKN).trans hge
  have heq : sovereignObjective u F Y₁ r η β D KN = repayObjective u F Y₁ r β D KN := by
    rw [sovereignObjective_eq_max hu.monotoneOn hβ.le (hpos KN hKN).1 (hpos KN hKN).2,
      max_eq_left hdef]
  refine ⟨isMaxOn_iff.mpr fun K hK => ?_, heq, ?_⟩
  · rw [heq]
    exact hle K hK
  · by_contra hlt
    push Not at hlt
    have hc : F KN + KN - (1 + r) * D < (1 - η) * (F KN + KN) := by linarith
    have := hu (mem_Ioi.mpr (hpos KN hKN).1) (mem_Ioi.mpr (hpos KN hKN).2) hc
    unfold defaultObjective repayObjective at hdef
    nlinarith

/-- Default when `U^D > U^N`, O&R p. 384: if the default maximum strictly exceeds the repay
maximum, then at every maximiser of (24) the sovereign actually defaults,
`η[F(K)+K] < (1+r)D` (`u` strictly increasing, `β > 0`). -/
theorem default_at_optimum_of_value_gt {u F : ℝ → ℝ} (hu : StrictMonoOn u (Ioi 0))
    {Y₁ r η β D : ℝ} (hβ : 0 < β) {S : Set ℝ}
    (hpos : ∀ K ∈ S, 0 < F K + K - (1 + r) * D ∧ 0 < (1 - η) * (F K + K)) {KN KD : ℝ}
    (hKD : KD ∈ S) (hN : IsMaxOn (repayObjective u F Y₁ r β D) S KN)
    (hgt : repayObjective u F Y₁ r β D KN < defaultObjective u F Y₁ η β D KD)
    {K : ℝ} (hK : K ∈ S) (hopt : IsMaxOn (sovereignObjective u F Y₁ r η β D) S K) :
    η * (F K + K) < (1 + r) * D := by
  have h1 : sovereignObjective u F Y₁ r η β D KD ≤ sovereignObjective u F Y₁ r η β D K :=
    isMaxOn_iff.mp hopt KD hKD
  rw [sovereignObjective_eq_max hu.monotoneOn hβ.le (hpos KD hKD).1 (hpos KD hKD).2,
    sovereignObjective_eq_max hu.monotoneOn hβ.le (hpos K hK).1 (hpos K hK).2] at h1
  have hNK : repayObjective u F Y₁ r β D K < defaultObjective u F Y₁ η β D K := by
    by_contra hcon
    push Not at hcon
    rw [max_eq_left hcon] at h1
    linarith [le_max_right (repayObjective u F Y₁ r β D KD) (defaultObjective u F Y₁ η β D KD),
      isMaxOn_iff.mp hN K hK]
  by_contra hge
  push Not at hge
  have hc : (1 - η) * (F K + K) ≤ F K + K - (1 + r) * D := by linarith
  have := hu.monotoneOn (mem_Ioi.mpr (hpos K hK).2) (mem_Ioi.mpr (hpos K hK).1) hc
  unfold defaultObjective repayObjective at hNK
  nlinarith

/-! ## Footnote 37: the repay optimum at the ceiling has strict slack -/

/-- Derivative of the repay objective, O&R §6.2.1.2 first-order conditions: at `K`,
`d/dK [u(Y₁+D−K) + βu(F(K)+K−(1+r)D)] = −u′(C₁) + βu′(C₂)(1 + F′(K))`. -/
theorem hasDerivAt_repayObjective {u F : ℝ → ℝ} {Y₁ r β D K u₁ u₂ f₁ : ℝ}
    (hu₁ : HasDerivAt u u₁ (Y₁ + D - K)) (hu₂ : HasDerivAt u u₂ (F K + K - (1 + r) * D))
    (hF : HasDerivAt F f₁ K) :
    HasDerivAt (repayObjective u F Y₁ r β D) (-u₁ + β * (u₂ * (f₁ + 1))) K := by
  have h1 : HasDerivAt (fun K => Y₁ + D - K) (-1) K := by
    simpa using (hasDerivAt_id K).const_sub (Y₁ + D)
  have h2 : HasDerivAt (fun K => F K + K - (1 + r) * D) (f₁ + 1) K :=
    (hF.add (hasDerivAt_id K)).sub_const _
  exact HasDerivAt.congr_deriv (HasDerivAt.add (hu₁.comp K h1) ((hu₂.comp K h2).const_mul β))
    (by ring)

/-- Derivative of the default objective: at `K`,
`d/dK [u(Y₁+D−K) + βu((1−η)(F(K)+K))] = −u′(C₁) + βu′(C₂)(1−η)(1 + F′(K))`.
(O&R §6.2.1, pp. 381–387.) -/
theorem hasDerivAt_defaultObjective {u F : ℝ → ℝ} {Y₁ η β D K u₁ u₂ f₁ : ℝ}
    (hu₁ : HasDerivAt u u₁ (Y₁ + D - K)) (hu₂ : HasDerivAt u u₂ ((1 - η) * (F K + K)))
    (hF : HasDerivAt F f₁ K) :
    HasDerivAt (defaultObjective u F Y₁ η β D) (-u₁ + β * (u₂ * ((1 - η) * (f₁ + 1)))) K := by
  have h1 : HasDerivAt (fun K => Y₁ + D - K) (-1) K := by
    simpa using (hasDerivAt_id K).const_sub (Y₁ + D)
  have h2 : HasDerivAt (fun K => (1 - η) * (F K + K)) ((1 - η) * (f₁ + 1)) K :=
    (hF.add (hasDerivAt_id K)).const_mul _
  exact HasDerivAt.congr_deriv (HasDerivAt.add (hu₁.comp K h1) ((hu₂.comp K h2).const_mul β))
    (by ring)

/-- Strict slack of the sanction constraint at a preferred repay optimum, O&R p. 385 and
footnote 37 (in general, no functional forms). Let `K^B` maximise the repay objective on a set
`S` that is a neighbourhood of `K^B`, and suppose repaying at `K^B` is at least as good as
defaulting at every `K ∈ S` (as at the ceiling `D̄`, where the sovereign is indifferent). If
`η > 0`, `β > 0`, `u` is strictly increasing with `u′(C₂) > 0`, and `1 + F′(K^B) > 0`, then
`η[F(K^B)+K^B] > (1+r)D` *strictly*: "creditor sanctions appear superficially more than
sufficient". (If the constraint held with equality, `K^B` would also maximise the default
objective, and the two first-order conditions would differ by `βu′(C₂)η(1+F′) ≠ 0`.)
No concavity is needed. -/
theorem repayment_slack_strict {u F : ℝ → ℝ} (hu : StrictMonoOn u (Ioi 0))
    {Y₁ r η β D KB u₁ u₂ f₁ : ℝ} (hβ : 0 < β) (hη : 0 < η) {S : Set ℝ} (hS : S ∈ 𝓝 KB)
    (hN : IsMaxOn (repayObjective u F Y₁ r β D) S KB)
    (hpref : ∀ K ∈ S, defaultObjective u F Y₁ η β D K ≤ repayObjective u F Y₁ r β D KB)
    (hc₂ : 0 < F KB + KB - (1 + r) * D) (hc₂' : 0 < (1 - η) * (F KB + KB))
    (hu₁ : HasDerivAt u u₁ (Y₁ + D - KB)) (hu₂ : HasDerivAt u u₂ (F KB + KB - (1 + r) * D))
    (hF : HasDerivAt F f₁ KB) (hu₂pos : 0 < u₂) (hf₁ : 0 < 1 + f₁) :
    (1 + r) * D < η * (F KB + KB) := by
  by_contra hle
  push Not at hle
  have hKB : KB ∈ S := mem_of_mem_nhds hS
  have hge : F KB + KB - (1 + r) * D ≤ (1 - η) * (F KB + KB) := by linarith
  have hdef : repayObjective u F Y₁ r β D KB ≤ defaultObjective u F Y₁ η β D KB := by
    unfold repayObjective defaultObjective
    have := hu.monotoneOn (mem_Ioi.mpr hc₂) (mem_Ioi.mpr hc₂') hge
    nlinarith
  have heqv : repayObjective u F Y₁ r β D KB = defaultObjective u F Y₁ η β D KB :=
    le_antisymm hdef (hpref KB hKB)
  have heqc : F KB + KB - (1 + r) * D = (1 - η) * (F KB + KB) := by
    unfold repayObjective defaultObjective at heqv
    have h' : u (F KB + KB - (1 + r) * D) = u ((1 - η) * (F KB + KB)) := by
      have := mul_left_cancel₀ hβ.ne' (add_left_cancel heqv)
      exact this
    exact hu.injOn (mem_Ioi.mpr hc₂) (mem_Ioi.mpr hc₂') h'
  have hDmax : IsMaxOn (defaultObjective u F Y₁ η β D) S KB :=
    isMaxOn_iff.mpr fun K hK => (hpref K hK).trans heqv.le
  have hu₂' : HasDerivAt u u₂ ((1 - η) * (F KB + KB)) := heqc ▸ hu₂
  have d1 := (hN.isLocalMax hS).hasDerivAt_eq_zero (hasDerivAt_repayObjective hu₁ hu₂ hF)
  have d2 := (hDmax.isLocalMax hS).hasDerivAt_eq_zero
    (hasDerivAt_defaultObjective (β := β) hu₁ hu₂' hF)
  have hprod : 0 < β * (u₂ * (η * (f₁ + 1))) := by
    have : 0 < f₁ + 1 := by linarith
    positivity
  nlinarith

/-- The repay and default optima are distinct at the ceiling, O&R p. 385 (points `B` and `B′`
of Figure 6.4): under the hypotheses of `repayment_slack_strict`, if `K^D` maximises the
default objective on `S` and the sovereign is indifferent (`U^D = U^N`), then `K^D ≠ K^B`. -/
theorem default_optimum_ne_repay_optimum {u F : ℝ → ℝ} (hu : StrictMonoOn u (Ioi 0))
    {Y₁ r η β D KB KD u₁ u₂ f₁ : ℝ} (hβ : 0 < β) (hη : 0 < η) {S : Set ℝ} (hS : S ∈ 𝓝 KB)
    (hN : IsMaxOn (repayObjective u F Y₁ r β D) S KB)
    (hD : IsMaxOn (defaultObjective u F Y₁ η β D) S KD)
    (hind : defaultObjective u F Y₁ η β D KD = repayObjective u F Y₁ r β D KB)
    (hc₂ : 0 < F KB + KB - (1 + r) * D) (hc₂' : 0 < (1 - η) * (F KB + KB))
    (hu₁ : HasDerivAt u u₁ (Y₁ + D - KB)) (hu₂ : HasDerivAt u u₂ (F KB + KB - (1 + r) * D))
    (hF : HasDerivAt F f₁ KB) (hu₂pos : 0 < u₂) (hf₁ : 0 < 1 + f₁) :
    KD ≠ KB := by
  have hpref : ∀ K ∈ S, defaultObjective u F Y₁ η β D K ≤ repayObjective u F Y₁ r β D KB :=
    fun K hK => (isMaxOn_iff.mp hD K hK).trans hind.le
  have hslack := repayment_slack_strict hu hβ hη hS hN hpref hc₂ hc₂' hu₁ hu₂ hF hu₂pos hf₁
  intro hEq
  subst hEq
  have hlt : (1 - η) * (F KD + KD) < F KD + KD - (1 + r) * D := by linarith
  have := hu (mem_Ioi.mpr hc₂') (mem_Ioi.mpr hc₂) hlt
  unfold defaultObjective repayObjective at hind
  nlinarith

/-- Footnote 37: the literature's characterisation is wrong. Under the hypotheses of
`repayment_slack_strict`, with date-2 resources `F(K) + K` strictly increasing, the investment
level `K̄` at the kink of the GNPᴰ–GNPᴺ envelope, `η[F(K̄)+K̄] = (1+r)D`, lies strictly below
the repay optimum `K^B`: `K̄ < K^B`, so `η[F(K(D̄))+K(D̄)] = (1+r)D̄` does not characterise the
sovereign's choice at the ceiling. -/
theorem kink_investment_lt_repay_optimum {u F : ℝ → ℝ} (hu : StrictMonoOn u (Ioi 0))
    (hG : StrictMono fun K => F K + K)
    {Y₁ r η β D KB Kbar u₁ u₂ f₁ : ℝ} (hβ : 0 < β) (hη : 0 < η) {S : Set ℝ} (hS : S ∈ 𝓝 KB)
    (hN : IsMaxOn (repayObjective u F Y₁ r β D) S KB)
    (hpref : ∀ K ∈ S, defaultObjective u F Y₁ η β D K ≤ repayObjective u F Y₁ r β D KB)
    (hc₂ : 0 < F KB + KB - (1 + r) * D) (hc₂' : 0 < (1 - η) * (F KB + KB))
    (hu₁ : HasDerivAt u u₁ (Y₁ + D - KB)) (hu₂ : HasDerivAt u u₂ (F KB + KB - (1 + r) * D))
    (hF : HasDerivAt F f₁ KB) (hu₂pos : 0 < u₂) (hf₁ : 0 < 1 + f₁)
    (hkink : η * (F Kbar + Kbar) = (1 + r) * D) :
    Kbar < KB := by
  have hslack := repayment_slack_strict hu hβ hη hS hN hpref hc₂ hc₂' hu₁ hu₂ hF hu₂pos hf₁
  have : F Kbar + Kbar < F KB + KB := by
    by_contra h
    push Not at h
    nlinarith
  exact hG.lt_iff_lt.mp this

/-! ## The log-linear example, eqs. (25)–(30) -/

/-- Two-period log-utility optimum on a linear budget line, used for (27) and (29): if
`W, R, β > 0` and `c₁ + c₂/R = W` with `c₁, c₂ > 0`, then
`log c₁ + β log c₂ ≤ (1+β) log(W/(1+β)) + β log(Rβ)`, with equality at
`c₁ = W/(1+β)`, `c₂ = RβW/(1+β)`. Proved by the tangent-line inequality `log x ≤ x − 1`.
(O&R §6.2.1, pp. 381–387.) -/
theorem log_two_period_le {W R β c₁ c₂ : ℝ} (hW : 0 < W) (hR : 0 < R) (hβ : 0 < β)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hbud : c₁ + c₂ / R = W) :
    log c₁ + β * log c₂ ≤ (1 + β) * log (W / (1 + β)) + β * log (R * β) := by
  set s₁ := W / (1 + β) with hs₁
  set s₂ := R * β * (W / (1 + β)) with hs₂
  have hs₁p : 0 < s₁ := by positivity
  have hs₂p : 0 < s₂ := by positivity
  have h1 : log c₁ - log s₁ ≤ c₁ / s₁ - 1 := by
    rw [← log_div hc₁.ne' hs₁p.ne']
    exact log_le_sub_one_of_pos (div_pos hc₁ hs₁p)
  have h2 : log c₂ - log s₂ ≤ c₂ / s₂ - 1 := by
    rw [← log_div hc₂.ne' hs₂p.ne']
    exact log_le_sub_one_of_pos (div_pos hc₂ hs₂p)
  have h2' := mul_le_mul_of_nonneg_left h2 hβ.le
  have key : c₁ / s₁ - 1 + β * (c₂ / s₂ - 1) = 0 := by
    subst hbud
    rw [hs₁, hs₂]
    field_simp
    ring
  have hlog2 : log s₂ = log (R * β) + log s₁ := by
    rw [hs₂, log_mul (by positivity) hs₁p.ne']
  nlinarith

/-- The value attained at the log-utility optimum: with `c₁ = W/(1+β)` and
`c₂ = RβW/(1+β)`, `log c₁ + β log c₂ = (1+β) log(W/(1+β)) + β log(Rβ)`.
(O&R §6.2.1, pp. 381–387.) -/
theorem log_two_period_value {W R β : ℝ} (hW : 0 < W) (hR : 0 < R) (hβ : 0 < β) :
    log (W / (1 + β)) + β * log (R * β * (W / (1 + β))) =
      (1 + β) * log (W / (1 + β)) + β * log (R * β) := by
  rw [log_mul (by positivity) (by positivity)]
  ring

/-- Wealth on the repay locus, the right-hand side of (26), O&R p. 383:
`Y₁ + (α − r)D₂/(1 + α)`. -/
noncomputable def repayWealth (Y₁ α r D : ℝ) : ℝ := Y₁ + (α - r) / (1 + α) * D

/-- The repay-optimal investment, O&R p. 384 (from (27)):
`K^N = β(Y₁ + D₂)/(1+β) + (1+r)D₂/((1+β)(1+α))`. -/
noncomputable def repayInvestment (Y₁ α r β D : ℝ) : ℝ :=
  β * (Y₁ + D) / (1 + β) + (1 + r) * D / ((1 + β) * (1 + α))

/-- The default-optimal investment, O&R p. 385 (from (29)): `K^D = β(Y₁ + D₂)/(1+β)`. -/
noncomputable def defaultInvestment (Y₁ β D : ℝ) : ℝ := β * (Y₁ + D) / (1 + β)

/-- The maximised repay utility, O&R p. 383:
`U^N = (1+β) log{[Y₁ + (α−r)D₂/(1+α)]/(1+β)} + β log[(1+α)β]`. -/
noncomputable def repayValue (Y₁ α r β D : ℝ) : ℝ :=
  (1 + β) * log (repayWealth Y₁ α r D / (1 + β)) + β * log ((1 + α) * β)

/-- The maximised default utility, O&R p. 383:
`U^D = (1+β) log[(Y₁ + D₂)/(1+β)] + β log[(1−η)(1+α)β]`. -/
noncomputable def defaultValue (Y₁ α η β D : ℝ) : ℝ :=
  (1 + β) * log ((Y₁ + D) / (1 + β)) + β * log ((1 - η) * (1 + α) * β)

/-- The repay locus GNPᴺ (26), O&R p. 383, for `F = αK`: every plan satisfies
`C₁ + C₂/(1+α) = Y₁ + (α−r)D₂/(1+α)`. -/
theorem repay_budget (Y₁ α r D K : ℝ) (hα : 0 < 1 + α) :
    (Y₁ + D - K) + (α * K + K - (1 + r) * D) / (1 + α) = repayWealth Y₁ α r D := by
  unfold repayWealth
  field_simp
  ring

/-- The default locus GNPᴰ (28), O&R p. 383, for `F = αK`: every plan satisfies
`C₁ + C₂/[(1−η)(1+α)] = Y₁ + D₂`. -/
theorem default_budget (Y₁ α η D K : ℝ) (hα : 0 < 1 + α) (hη : η < 1) :
    (Y₁ + D - K) + (1 - η) * (α * K + K) / ((1 - η) * (1 + α)) = Y₁ + D := by
  have : (1 - η) ≠ 0 := by linarith
  field_simp
  ring

/-- The repay optimum (27), O&R p. 383, for `u = log`, `F = αK`: with positive repay wealth,
`K^N` gives `C₁ = W/(1+β)`, `C₂ = (1+α)βW/(1+β)` (both positive), it maximises the repay
objective over all plans with positive consumption, and the maximum is `U^N`. -/
theorem logLinear_repay_optimum {Y₁ α r β D : ℝ} (hα : 0 < 1 + α) (hβ : 0 < β)
    (hW : 0 < repayWealth Y₁ α r D) :
    Y₁ + D - repayInvestment Y₁ α r β D = repayWealth Y₁ α r D / (1 + β) ∧
      α * repayInvestment Y₁ α r β D + repayInvestment Y₁ α r β D - (1 + r) * D =
        (1 + α) * β * (repayWealth Y₁ α r D / (1 + β)) ∧
      (∀ K, 0 < Y₁ + D - K → 0 < α * K + K - (1 + r) * D →
        repayObjective log (fun K => α * K) Y₁ r β D K ≤
          repayObjective log (fun K => α * K) Y₁ r β D (repayInvestment Y₁ α r β D)) ∧
      repayObjective log (fun K => α * K) Y₁ r β D (repayInvestment Y₁ α r β D) =
        repayValue Y₁ α r β D := by
  have hC1 : Y₁ + D - repayInvestment Y₁ α r β D = repayWealth Y₁ α r D / (1 + β) := by
    unfold repayInvestment repayWealth
    field_simp
    ring
  have hC2 : α * repayInvestment Y₁ α r β D + repayInvestment Y₁ α r β D - (1 + r) * D =
      (1 + α) * β * (repayWealth Y₁ α r D / (1 + β)) := by
    unfold repayInvestment repayWealth
    field_simp
    ring
  have hval : repayObjective log (fun K => α * K) Y₁ r β D (repayInvestment Y₁ α r β D) =
      repayValue Y₁ α r β D := by
    unfold repayObjective
    rw [hC1, hC2, repayValue, log_two_period_value hW hα hβ]
  refine ⟨hC1, hC2, fun K h1 h2 => ?_, hval⟩
  rw [hval, repayValue]
  exact log_two_period_le hW hα hβ h1 h2 (repay_budget Y₁ α r D K hα)

/-- The default optimum (29), O&R p. 383, for `u = log`, `F = αK`, `0 ≤ η < 1`: `K^D` gives
`C₁ = (Y₁+D₂)/(1+β)`, `C₂ = (1−η)(1+α)β(Y₁+D₂)/(1+β)`, it maximises the default objective over
all plans with positive consumption, and the maximum is `U^D`. -/
theorem logLinear_default_optimum {Y₁ α η β D : ℝ} (hα : 0 < 1 + α) (hβ : 0 < β)
    (hη : η < 1) (hW : 0 < Y₁ + D) :
    Y₁ + D - defaultInvestment Y₁ β D = (Y₁ + D) / (1 + β) ∧
      (1 - η) * (α * defaultInvestment Y₁ β D + defaultInvestment Y₁ β D) =
        (1 - η) * (1 + α) * β * ((Y₁ + D) / (1 + β)) ∧
      (∀ K, 0 < Y₁ + D - K → 0 < (1 - η) * (α * K + K) →
        defaultObjective log (fun K => α * K) Y₁ η β D K ≤
          defaultObjective log (fun K => α * K) Y₁ η β D (defaultInvestment Y₁ β D)) ∧
      defaultObjective log (fun K => α * K) Y₁ η β D (defaultInvestment Y₁ β D) =
        defaultValue Y₁ α η β D := by
  have hR : 0 < (1 - η) * (1 + α) := mul_pos (by linarith) hα
  have hC1 : Y₁ + D - defaultInvestment Y₁ β D = (Y₁ + D) / (1 + β) := by
    unfold defaultInvestment
    field_simp
    ring
  have hC2 : (1 - η) * (α * defaultInvestment Y₁ β D + defaultInvestment Y₁ β D) =
      (1 - η) * (1 + α) * β * ((Y₁ + D) / (1 + β)) := by
    unfold defaultInvestment
    field_simp
    ring
  have hval : defaultObjective log (fun K => α * K) Y₁ η β D (defaultInvestment Y₁ β D) =
      defaultValue Y₁ α η β D := by
    unfold defaultObjective
    rw [hC1, hC2, defaultValue, log_two_period_value hW hR hβ]
  refine ⟨hC1, hC2, fun K h1 h2 => ?_, hval⟩
  rw [hval, defaultValue]
  exact log_two_period_le hW hR hβ h1 h2 (default_budget Y₁ α η D K hα hη)

/-- The default–repay utility gap as a function of `x = D₂/Y₁`, O&R p. 384:
`(1+β) log[(1+x)/(1+ax)] + β log(1−η)` with `a = (α−r)/(1+α)`. -/
noncomputable def utilityGap (β η a x : ℝ) : ℝ :=
  (1 + β) * log ((1 + x) / (1 + a * x)) + β * log (1 - η)

/-- The gap formula of p. 384: `U^D − U^N = (1+β) log[(1 + D₂/Y₁)/(1 + (α−r)/(1+α) · D₂/Y₁)]
+ β log(1−η)` (for `Y₁ > 0`, positive repay wealth, `Y₁ + D₂ > 0`, `η < 1`, `1+α, β > 0`). -/
theorem defaultValue_sub_repayValue {Y₁ α r η β D : ℝ} (hY : 0 < Y₁) (hα : 0 < 1 + α)
    (hβ : 0 < β) (hη : η < 1) (hW : 0 < repayWealth Y₁ α r D) (hWD : 0 < Y₁ + D) :
    defaultValue Y₁ α η β D - repayValue Y₁ α r β D =
      utilityGap β η ((α - r) / (1 + α)) (D / Y₁) := by
  have h1b : (0 : ℝ) < 1 + β := by linarith
  have hx1 : 1 + D / Y₁ = (Y₁ + D) / Y₁ := by field_simp
  have hx2 : 1 + (α - r) / (1 + α) * (D / Y₁) = repayWealth Y₁ α r D / Y₁ := by
    unfold repayWealth
    field_simp
  unfold defaultValue repayValue utilityGap
  rw [hx1, hx2, div_div_div_cancel_right₀ hY.ne', log_div hWD.ne' hW.ne',
    log_div hWD.ne' h1b.ne', log_div hW.ne' h1b.ne',
    show (1 - η) * (1 + α) * β = (1 - η) * ((1 + α) * β) by ring,
    log_mul (by linarith) (by positivity)]
  ring

/-- The gap is strictly increasing in the debt–output ratio, O&R p. 384 ("it rises as
`D₂/Y₁` rises"): for `0 ≤ a < 1` and `β > −1`, `x ↦ utilityGap β η a x` is strictly increasing
on `[0, ∞)`. (No use of (25): `a < 1` holds for every `r > −1`.) -/
theorem utilityGap_strictMonoOn {β η a : ℝ} (hβ : -1 < β) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    StrictMonoOn (utilityGap β η a) (Ici 0) := by
  intro x hx y hy hxy
  rw [mem_Ici] at hx hy
  unfold utilityGap
  have hr : (1 + x) / (1 + a * x) < (1 + y) / (1 + a * y) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have := log_lt_log (by positivity) hr
  have hb : 0 < 1 + β := by linarith
  nlinarith

/-- The factor `k = [1/(1−η)]^{β/(1+β)}` of (30), O&R p. 384. -/
noncomputable def ceilingFactor (β η : ℝ) : ℝ := (1 / (1 - η)) ^ (β / (1 + β))

/-- The debt ceiling (30), O&R p. 384:
`D̄ = {[1/(1−η)]^{β/(1+β)} − 1} / {1 − [(α−r)/(1+α)][1/(1−η)]^{β/(1+β)}} · Y₁`. -/
noncomputable def debtCeiling (Y₁ α r β η : ℝ) : ℝ :=
  (ceilingFactor β η - 1) / (1 - (α - r) / (1 + α) * ceilingFactor β η) * Y₁

/-- `(1+β) log k + β log(1−η) = 0` for the factor `k` of (30) (`η < 1`, `β > −1`).
(O&R §6.2.1, pp. 381–387.) -/
theorem log_ceilingFactor {β η : ℝ} (hβ : -1 < β) (hη : η < 1) :
    (1 + β) * log (ceilingFactor β η) + β * log (1 - η) = 0 := by
  have h1 : (0 : ℝ) < 1 - η := by linarith
  have hb : (1 + β) ≠ 0 := by linarith
  unfold ceilingFactor
  rw [log_rpow (by positivity), one_div, log_inv]
  field_simp
  ring

/-- `k ≥ 1`, and `k > 1` when `η > 0`, `β > 0` (O&R p. 384). -/
theorem one_le_ceilingFactor {β η : ℝ} (hβ : 0 ≤ β) (hη0 : 0 ≤ η) (hη : η < 1) :
    1 ≤ ceilingFactor β η := by
  unfold ceilingFactor
  apply one_le_rpow _ (by positivity)
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- `k > 1` when `0 < η < 1` and `β > 0`. (O&R §6.2.1, pp. 381–387.) -/
theorem one_lt_ceilingFactor {β η : ℝ} (hβ : 0 < β) (hη0 : 0 < η) (hη : η < 1) :
    1 < ceilingFactor β η := by
  unfold ceilingFactor
  apply one_lt_rpow _ (by positivity)
  rw [lt_div_iff₀ (by linarith)]
  linarith

/-- The gap vanishes at the ceiling ratio, O&R p. 384 (the exponentiated indifference
condition): if `a < 1` and `a·k < 1` then `utilityGap β η a ((k−1)/(1−ak)) = 0`. -/
theorem utilityGap_ceiling {β η a : ℝ} (hβ : -1 < β) (hη : η < 1) (ha1 : a < 1)
    (hak : a * ceilingFactor β η < 1) :
    utilityGap β η a ((ceilingFactor β η - 1) / (1 - a * ceilingFactor β η)) = 0 := by
  set k := ceilingFactor β η with hk
  have hd : 0 < 1 - a * k := by linarith
  have h1a : 0 < 1 - a := by linarith
  have hd' : 1 - a * k ≠ 0 := hd.ne'
  have hd'' : 1 - k * a ≠ 0 := by rw [mul_comm]; exact hd'
  have h1a' : 1 - a ≠ 0 := h1a.ne'
  have hratio : (1 + (k - 1) / (1 - a * k)) / (1 + a * ((k - 1) / (1 - a * k))) = k := by
    have e1 : 1 + (k - 1) / (1 - a * k) = k * (1 - a) / (1 - a * k) := by
      field_simp
      ring
    have e2 : 1 + a * ((k - 1) / (1 - a * k)) = (1 - a) / (1 - a * k) := by
      field_simp
      ring
    rw [e1, e2, div_div_div_cancel_right₀ hd', mul_div_assoc, div_self h1a', mul_one]
  unfold utilityGap
  rw [hratio]
  exact log_ceilingFactor hβ hη

/-- The ceiling (30) characterises repayment, O&R pp. 384 and 387 — the interval property in
the log-linear example: with `Y₁ > 0`, `−1 < r ≤ α`, `0 < η < 1`, `β > 0`, and
`a·k < 1` (implied by (25), footnote 33), for every `D₂ ≥ 0`, the sovereign (weakly) prefers
repaying, `U^D ≤ U^N`, if and only if `D₂ ≤ D̄`. -/
theorem repay_iff_le_debtCeiling {Y₁ α r β η D : ℝ} (hY : 0 < Y₁) (hr : -1 < r) (hrα : r ≤ α)
    (hβ : 0 < β) (hη0 : 0 < η) (hη : η < 1)
    (hak : (α - r) / (1 + α) * ceilingFactor β η < 1) (hD : 0 ≤ D) :
    defaultValue Y₁ α η β D ≤ repayValue Y₁ α r β D ↔ D ≤ debtCeiling Y₁ α r β η := by
  have hα : 0 < 1 + α := by linarith
  have ha0 : 0 ≤ (α - r) / (1 + α) := div_nonneg (by linarith) hα.le
  have ha1 : (α - r) / (1 + α) < 1 := by rw [div_lt_one hα]; linarith
  have hW : 0 < repayWealth Y₁ α r D := by unfold repayWealth; positivity
  have hgap := defaultValue_sub_repayValue hY hα hβ hη hW (by linarith : 0 < Y₁ + D)
  have hk := one_le_ceilingFactor hβ.le hη0.le hη
  have hxbar : 0 ≤ (ceilingFactor β η - 1) / (1 - (α - r) / (1 + α) * ceilingFactor β η) :=
    div_nonneg (by linarith) (by linarith)
  have hmono := utilityGap_strictMonoOn (η := η) (by linarith : (-1 : ℝ) < β) ha0 ha1
  have hz := utilityGap_ceiling (by linarith : (-1 : ℝ) < β) hη ha1 hak
  rw [← sub_nonpos, hgap, ← hz, hmono.le_iff_le (mem_Ici.mpr (div_nonneg hD hY.le))
    (mem_Ici.mpr hxbar), div_le_iff₀ hY]
  rfl

/-- Default is strictly preferred exactly above the ceiling, O&R p. 385: under the hypotheses of
`repay_iff_le_debtCeiling`, `U^N < U^D ↔ D̄ < D₂`. -/
theorem default_iff_gt_debtCeiling {Y₁ α r β η D : ℝ} (hY : 0 < Y₁) (hr : -1 < r)
    (hrα : r ≤ α) (hβ : 0 < β) (hη0 : 0 < η) (hη : η < 1)
    (hak : (α - r) / (1 + α) * ceilingFactor β η < 1) (hD : 0 ≤ D) :
    repayValue Y₁ α r β D < defaultValue Y₁ α η β D ↔ debtCeiling Y₁ α r β η < D := by
  rw [← not_le, ← not_le, repay_iff_le_debtCeiling hY hr hrα hβ hη0 hη hak hD]

/-- Without a finite ceiling the sovereign never defaults, O&R p. 384 (the case (30) excludes):
if `(α−r)/(1+α) · k ≥ 1` (possible only when (25) fails), then `U^D < U^N` for every
`D₂ ≥ 0`. -/
theorem never_default_of_ceilingFactor_ge {Y₁ α r β η D : ℝ} (hY : 0 < Y₁) (hr : -1 < r)
    (hβ : 0 < β) (hη : η < 1) (hα : 0 < 1 + α)
    (hak : 1 ≤ (α - r) / (1 + α) * ceilingFactor β η) (hD : 0 ≤ D) :
    defaultValue Y₁ α η β D < repayValue Y₁ α r β D := by
  set a := (α - r) / (1 + α) with ha
  set k := ceilingFactor β η with hkdef
  have hk0 : 0 < k := by rw [hkdef]; unfold ceilingFactor; apply rpow_pos_of_pos; bound
  have ha1 : a < 1 := by rw [ha, div_lt_one hα]; linarith
  have hapos : 0 < a := by
    by_contra h
    push Not at h
    nlinarith
  have hW : 0 < repayWealth Y₁ α r D := by unfold repayWealth; rw [← ha]; positivity
  have hgap := defaultValue_sub_repayValue hY hα hβ hη hW (by linarith : 0 < Y₁ + D)
  rw [← ha] at hgap
  have hx : 0 ≤ D / Y₁ := div_nonneg hD hY.le
  have hr1 : (1 + D / Y₁) / (1 + a * (D / Y₁)) < k := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hl := log_lt_log (by positivity) hr1
  have h0 := log_ceilingFactor (by linarith : (-1 : ℝ) < β) hη
  rw [← hkdef] at h0
  have : utilityGap β η a (D / Y₁) < 0 := by
    unfold utilityGap
    nlinarith
  linarith

/-- Footnote 33, first part: for `1 + α > 0`, inequality (25) `1 + r > η(1+α)` holds iff
`(α−r)/(1+α) < 1 − η`. -/
theorem ineq25_iff {α r η : ℝ} (hα : 0 < 1 + α) :
    η * (1 + α) < 1 + r ↔ (α - r) / (1 + α) < 1 - η := by
  rw [div_lt_iff₀ hα]
  constructor <;> intro h <;> linarith

/-- Footnote 33, second part: (25) makes the ceiling (30) finite and positive. With
`0 < η < 1`, `β > 0`, `1 + α > 0`, (25) implies `(α−r)/(1+α) · k < 1` (because
`1 − η < (1−η)^{β/(1+β)} = 1/k`). -/
theorem ceiling_denominator_pos_of_ineq25 {α r β η : ℝ} (hα : 0 < 1 + α) (hβ : 0 < β)
    (hη0 : 0 < η) (hη : η < 1) (h25 : η * (1 + α) < 1 + r) :
    (α - r) / (1 + α) * ceilingFactor β η < 1 := by
  have h1 : (α - r) / (1 + α) < 1 - η := (ineq25_iff hα).mp h25
  have hpos : (0 : ℝ) < 1 - η := by linarith
  have he : β / (1 + β) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h2 : 1 - η < (1 - η) ^ (β / (1 + β)) := by
    have := rpow_lt_rpow_of_exponent_gt hpos (by linarith) he
    rwa [rpow_one] at this
  have hk : ceilingFactor β η = ((1 - η) ^ (β / (1 + β)))⁻¹ := by
    unfold ceilingFactor
    rw [one_div, inv_rpow hpos.le]
  have hkpos : 0 < (1 - η) ^ (β / (1 + β)) := rpow_pos_of_pos hpos _
  rw [hk, ← div_eq_mul_inv, div_lt_one hkpos]
  linarith

/-- The ceiling is positive, O&R p. 384 ("a positive number in view of inequality (25)"):
under `Y₁ > 0`, `0 < η < 1`, `β > 0`, `1 + α > 0` and (25), `D̄ > 0`. -/
theorem debtCeiling_pos {Y₁ α r β η : ℝ} (hY : 0 < Y₁) (hα : 0 < 1 + α) (hβ : 0 < β)
    (hη0 : 0 < η) (hη : η < 1) (h25 : η * (1 + α) < 1 + r) :
    0 < debtCeiling Y₁ α r β η := by
  have hak := ceiling_denominator_pos_of_ineq25 hα hβ hη0 hη h25
  have hk := one_lt_ceilingFactor hβ hη0 hη
  unfold debtCeiling
  apply mul_pos (div_pos (by linarith) (by linarith)) hY

/-- The ceiling ratio `(k−1)/(1−ak)` is strictly increasing in `k`, O&R p. 384 (used for the
comparative statics in `η` and `β`): for `0 ≤ a < 1`, `k < k'`, `ak' < 1`. -/
theorem ceilingRatio_lt_of_factor_lt {a k k' : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hkk : k < k') (hak : a * k' < 1) :
    (k - 1) / (1 - a * k) < (k' - 1) / (1 - a * k') := by
  have h1 : 0 < 1 - a * k := by nlinarith
  have h2 : 0 < 1 - a * k' := by linarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith

/-- The ceiling ratio `(k−1)/(1−ak)` is strictly increasing in `a`, O&R p. 384 (used for the
comparative statics in `α` and `r`): for `k > 1`, `a < a'`, `a'k < 1`. -/
theorem ceilingRatio_lt_of_slope_lt {a a' k : ℝ} (hk : 1 < k) (haa : a < a')
    (hak : a' * k < 1) :
    (k - 1) / (1 - a * k) < (k - 1) / (1 - a' * k) := by
  have h2 : 0 < 1 - a' * k := by linarith
  have h1 : 1 - a' * k < 1 - a * k := by nlinarith
  exact div_lt_div_of_pos_left (by linarith) h2 h1

/-- Comparative statics in `η`, O&R p. 384 ("making the force of sanctions greater (raising `η`)
increases the borrowing limit"): for `Y₁ > 0`, `−1 < r ≤ α`, `β > 0`, `η < η′ < 1` and a
finite ceiling at `η′`, `D̄(η) < D̄(η′)`. -/
theorem debtCeiling_strictMono_eta {Y₁ α r β η η' : ℝ} (hY : 0 < Y₁) (hr : -1 < r)
    (hrα : r ≤ α) (hβ : 0 < β) (hηη : η < η') (hη' : η' < 1)
    (hak : (α - r) / (1 + α) * ceilingFactor β η' < 1) :
    debtCeiling Y₁ α r β η < debtCeiling Y₁ α r β η' := by
  have hα : 0 < 1 + α := by linarith
  have ha0 : 0 ≤ (α - r) / (1 + α) := div_nonneg (by linarith) hα.le
  have ha1 : (α - r) / (1 + α) < 1 := by rw [div_lt_one hα]; linarith
  have hkk : ceilingFactor β η < ceilingFactor β η' := by
    unfold ceilingFactor
    apply rpow_lt_rpow (by bound) _ (by positivity)
    exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  unfold debtCeiling
  exact mul_lt_mul_of_pos_right (ceilingRatio_lt_of_factor_lt ha0 ha1 hkk hak) hY

/-- Comparative statics in `β`, O&R p. 384 ("as does greater patience (higher `β`)"): for
`Y₁ > 0`, `−1 < r ≤ α`, `0 < η < 1`, `0 < β < β′` and a finite ceiling at `β′`,
`D̄(β) < D̄(β′)`. -/
theorem debtCeiling_strictMono_beta {Y₁ α r β β' η : ℝ} (hY : 0 < Y₁) (hr : -1 < r)
    (hrα : r ≤ α) (hβ : 0 < β) (hββ : β < β') (hη0 : 0 < η) (hη : η < 1)
    (hak : (α - r) / (1 + α) * ceilingFactor β' η < 1) :
    debtCeiling Y₁ α r β η < debtCeiling Y₁ α r β' η := by
  have hα : 0 < 1 + α := by linarith
  have ha0 : 0 ≤ (α - r) / (1 + α) := div_nonneg (by linarith) hα.le
  have ha1 : (α - r) / (1 + α) < 1 := by rw [div_lt_one hα]; linarith
  have hkk : ceilingFactor β η < ceilingFactor β' η := by
    unfold ceilingFactor
    apply rpow_lt_rpow_of_exponent_lt
    · rw [lt_div_iff₀ (by linarith)]
      linarith
    · rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      linarith
  unfold debtCeiling
  exact mul_lt_mul_of_pos_right (ceilingRatio_lt_of_factor_lt ha0 ha1 hkk hak) hY

/-- Comparative statics in `α`, O&R p. 384 ("and more productive domestic capital (higher
`α`)"): for `Y₁ > 0`, `r > −1`, `1 + α > 0`, `α < α′`, `0 < η < 1`, `β > 0` and a finite
ceiling at `α′`, `D̄(α) < D̄(α′)`. -/
theorem debtCeiling_strictMono_alpha {Y₁ α α' r β η : ℝ} (hY : 0 < Y₁) (hr : -1 < r)
    (hα : 0 < 1 + α) (hαα : α < α') (hβ : 0 < β) (hη0 : 0 < η) (hη : η < 1)
    (hak : (α' - r) / (1 + α') * ceilingFactor β η < 1) :
    debtCeiling Y₁ α r β η < debtCeiling Y₁ α' r β η := by
  have hα' : 0 < 1 + α' := by linarith
  have haa : (α - r) / (1 + α) < (α' - r) / (1 + α') := by
    rw [div_lt_div_iff₀ hα hα']
    nlinarith
  unfold debtCeiling
  exact mul_lt_mul_of_pos_right
    (ceilingRatio_lt_of_slope_lt (one_lt_ceilingFactor hβ hη0 hη) haa hak) hY

/-- Comparative statics in `r`, O&R p. 384 ("a higher world interest rate `r`, by making default
more attractive, lowers `D̄`"): for `Y₁ > 0`, `−1 < r < r′`, `1 + α > 0`, `0 < η < 1`,
`β > 0` and a finite ceiling at `r`, `D̄(r′) < D̄(r)`. -/
theorem debtCeiling_strictAnti_r {Y₁ α r r' β η : ℝ} (hY : 0 < Y₁) (hα : 0 < 1 + α)
    (hrr : r < r') (hβ : 0 < β) (hη0 : 0 < η) (hη : η < 1)
    (hak : (α - r) / (1 + α) * ceilingFactor β η < 1) :
    debtCeiling Y₁ α r' β η < debtCeiling Y₁ α r β η := by
  have haa : (α - r') / (1 + α) < (α - r) / (1 + α) :=
    div_lt_div_of_pos_right (by linarith) hα
  unfold debtCeiling
  exact mul_lt_mul_of_pos_right
    (ceilingRatio_lt_of_slope_lt (one_lt_ceilingFactor hβ hη0 hη) haa hak) hY

/-- The investment crash at the ceiling, O&R pp. 384–385 and Figure 6.5: at every debt level
`K^N − K^D = (1+r)D₂/[(1+β)(1+α)]`, so moving from repayment to default at `D̄ > 0` makes
investment jump down by `(1+r)D̄/[(1+β)(1+α)] > 0` (`r > −1`, `β > −1`, `1+α > 0`). -/
theorem investment_drop {Y₁ α r β D : ℝ} (hr : -1 < r) (hβ : -1 < β) (hα : 0 < 1 + α)
    (hD : 0 < D) :
    repayInvestment Y₁ α r β D - defaultInvestment Y₁ β D =
        (1 + r) * D / ((1 + β) * (1 + α)) ∧
      0 < repayInvestment Y₁ α r β D - defaultInvestment Y₁ β D := by
  have e : repayInvestment Y₁ α r β D - defaultInvestment Y₁ β D =
      (1 + r) * D / ((1 + β) * (1 + α)) := by
    unfold repayInvestment defaultInvestment
    ring
  refine ⟨e, ?_⟩
  rw [e]
  have : 0 < 1 + β := by linarith
  have : 0 < 1 + r := by linarith
  positivity

/-- The sovereign's utility is continuous in debt despite the investment jump, O&R p. 385
("higher borrowing raises the sovereign's utility level continuously"): with `Y₁ > 0`,
`r ≤ α`, `1 + α > 0`, `β > −1`, the value `max(U^N, U^D)` is continuous on `D₂ ≥ 0`. -/
theorem sovereignValue_continuousOn {Y₁ α r β η : ℝ} (hY : 0 < Y₁) (hrα : r ≤ α)
    (hα : 0 < 1 + α) (hβ : -1 < β) :
    ContinuousOn (fun D => max (repayValue Y₁ α r β D) (defaultValue Y₁ α η β D)) (Ici 0) := by
  have hb : 0 < 1 + β := by linarith
  have ha0 : 0 ≤ (α - r) / (1 + α) := div_nonneg (by linarith) hα.le
  apply ContinuousOn.sup
  · unfold repayValue repayWealth
    apply ContinuousOn.add _ continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.log (by fun_prop)
    intro D hD
    rw [mem_Ici] at hD
    positivity
  · unfold defaultValue
    apply ContinuousOn.add _ continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.log (by fun_prop)
    intro D hD
    rw [mem_Ici] at hD
    positivity

/-- The loci of footnote 36, O&R p. 385: for every `K`, with `C₁ = Y₁ + D₂ − K`, the repay
locus is `C₂ = −(1+α)C₁ + (1+α)Y₁ + (α−r)D₂` and the default locus is
`C₂ = −(1−η)(1+α)C₁ + (1−η)(1+α)(Y₁ + D₂)`. -/
theorem footnote36_loci (Y₁ α r η D K : ℝ) :
    α * K + K - (1 + r) * D = -(1 + α) * (Y₁ + D - K) + (1 + α) * Y₁ + (α - r) * D ∧
      (1 - η) * (α * K + K) =
        -(1 - η) * (1 + α) * (Y₁ + D - K) + (1 - η) * (1 + α) * (Y₁ + D) := by
  constructor <;> ring

/-- Footnote 36's comparison: a rise `ΔD > 0` shifts the GNPᴺ intercept up by `(α−r)ΔD` and
the GNPᴰ intercept by `(1−η)(1+α)ΔD`; the default locus shifts by more iff (25) holds. -/
theorem footnote36_shift_iff {α r η ΔD : ℝ} (hΔ : 0 < ΔD) :
    (α - r) * ΔD < (1 - η) * (1 + α) * ΔD ↔ η * (1 + α) < 1 + r := by
  rw [mul_lt_mul_iff_left₀ hΔ]
  constructor <;> intro h <;> linarith

/-- The strict slack of (23) at the ceiling in the log-linear example, O&R p. 385 (point `B`):
under (25) with `Y₁ > 0`, `−1 < r ≤ α`, `0 < η < 1`, `β > 0`, at `D̄` the repay-optimal
investment satisfies `η(1+α)K^N > (1+r)D̄`, although the sovereign is indifferent. An
application of the general `repayment_slack_strict`. -/
theorem logLinear_slack_at_ceiling {Y₁ α r β η : ℝ} (hY : 0 < Y₁) (hr : -1 < r)
    (hrα : r ≤ α) (hβ : 0 < β) (hη0 : 0 < η) (hη : η < 1) (h25 : η * (1 + α) < 1 + r) :
    (1 + r) * debtCeiling Y₁ α r β η <
      η * (α * repayInvestment Y₁ α r β (debtCeiling Y₁ α r β η) +
        repayInvestment Y₁ α r β (debtCeiling Y₁ α r β η)) := by
  have hα : 0 < 1 + α := by linarith
  set D := debtCeiling Y₁ α r β η with hDdef
  set KN := repayInvestment Y₁ α r β D with hKN
  have hD : 0 ≤ D := (debtCeiling_pos hY hα hβ hη0 hη h25).le
  have ha0 : 0 ≤ (α - r) / (1 + α) := div_nonneg (by linarith) hα.le
  have hW : 0 < repayWealth Y₁ α r D := by unfold repayWealth; positivity
  obtain ⟨hC1, hC2, hmax, hval⟩ := logLinear_repay_optimum (r := r) hα hβ hW
  have hWD : 0 < Y₁ + D := by linarith
  obtain ⟨-, -, hdmax, hdval⟩ := logLinear_default_optimum (η := η) (α := α) hα hβ hη hWD
  have hak := ceiling_denominator_pos_of_ineq25 hα hβ hη0 hη h25
  have hle : defaultValue Y₁ α η β D ≤ repayValue Y₁ α r β D :=
    (repay_iff_le_debtCeiling hY hr hrα hβ hη0 hη hak hD).mpr le_rfl
  have hc1 : 0 < Y₁ + D - KN := by rw [hC1]; positivity
  have hc2 : 0 < α * KN + KN - (1 + r) * D := by rw [hC2]; positivity
  set S := Ioo ((1 + r) * D / (1 + α)) (Y₁ + D) with hS
  have hSmem : ∀ K ∈ S, 0 < Y₁ + D - K ∧ 0 < α * K + K - (1 + r) * D := by
    intro K hK
    rw [hS, mem_Ioo, div_lt_iff₀ hα] at hK
    constructor <;> linarith [hK.1, hK.2]
  have hKNS : S ∈ 𝓝 KN := by
    apply Ioo_mem_nhds
    · rw [div_lt_iff₀ hα]; linarith
    · linarith
  have hN : IsMaxOn (repayObjective log (fun K => α * K) Y₁ r β D) S KN :=
    isMaxOn_iff.mpr fun K hK => hmax K (hSmem K hK).1 (hSmem K hK).2
  have hpref : ∀ K ∈ S, defaultObjective log (fun K => α * K) Y₁ η β D K ≤
      repayObjective log (fun K => α * K) Y₁ r β D KN := by
    intro K hK
    obtain ⟨h1, h2⟩ := hSmem K hK
    have hK0 : 0 < α * K + K := by nlinarith
    have := hdmax K h1 (mul_pos (by linarith) hK0)
    rw [hdval] at this
    rw [hval]
    linarith
  have hc2' : 0 < (1 - η) * (α * KN + KN) := mul_pos (by linarith) (by nlinarith)
  have hF : HasDerivAt (fun K => α * K) α KN := by
    simpa using (hasDerivAt_id KN).const_mul α
  exact repayment_slack_strict strictMonoOn_log hβ hη0 hKNS hN hpref hc2 hc2'
    (hasDerivAt_log hc1.ne') (hasDerivAt_log hc2.ne') hF (inv_pos.mpr hc2) (by linarith)

/-! ## The repayment-set interval property (assumed in §6.2.1.2)

The book asserts (p. 387) that creditors set `D̄` "so that for any `D₂ ≤ D̄`" the sovereign
repays, i.e. that the set of debt levels at which repayment is (weakly) preferred is an
interval `[0, D̄]`. We call a debt level *repay-preferred* if some repay-feasible plan is at
least as good as every default-feasible plan, and *default-preferred* if some default-feasible
plan is strictly better than every repay-feasible plan. -/

/-- Repayment is (weakly) preferred at debt `D` (ties repay), O&R p. 384: some plan with
positive consumption under full repayment is at least as good as every plan with positive
consumption under default. -/
def RepayPreferred (u F : ℝ → ℝ) (Y₁ r η β D : ℝ) : Prop :=
  ∃ K, 0 < Y₁ + D - K ∧ 0 < F K + K - (1 + r) * D ∧
    ∀ K', 0 < Y₁ + D - K' → 0 < (1 - η) * (F K' + K') →
      defaultObjective u F Y₁ η β D K' ≤ repayObjective u F Y₁ r β D K

/-- Default is strictly preferred at debt `D`, O&R p. 385: some plan with positive consumption
under default is strictly better than every plan with positive consumption under repayment. -/
def DefaultPreferred (u F : ℝ → ℝ) (Y₁ r η β D : ℝ) : Prop :=
  ∃ K', 0 < Y₁ + D - K' ∧ 0 < (1 - η) * (F K' + K') ∧
    ∀ K, 0 < Y₁ + D - K → 0 < F K + K - (1 + r) * D →
      repayObjective u F Y₁ r β D K < defaultObjective u F Y₁ η β D K'

/-- The two regimes are exclusive (O&R p. 384). -/
theorem not_defaultPreferred_of_repayPreferred {u F : ℝ → ℝ} {Y₁ r η β D : ℝ}
    (h : RepayPreferred u F Y₁ r η β D) : ¬ DefaultPreferred u F Y₁ r η β D := by
  rintro ⟨K', h1, h2, hK'⟩
  obtain ⟨K, k1, k2, hK⟩ := h
  exact absurd (hK K' h1 h2) (not_le.mpr (hK' K k1 k2))

/-- With no debt the sovereign never strictly prefers default, O&R p. 384 ("for `D₂` close to
zero … `β log(1−η) < 0`"), for any increasing `u`, any `F`, `β ≥ 0` and `0 ≤ η < 1`: at
`D = 0` repaying with the same investment gives weakly more date-2 consumption. -/
theorem not_defaultPreferred_zero {u F : ℝ → ℝ} (hu : MonotoneOn u (Ioi 0)) {Y₁ r η β : ℝ}
    (hβ : 0 ≤ β) (hη0 : 0 ≤ η) (hη : η < 1) : ¬ DefaultPreferred u F Y₁ r η β 0 := by
  rintro ⟨K', h1, h2, hK'⟩
  have hG : 0 < F K' + K' := by
    by_contra h
    push Not at h
    nlinarith
  have h3 : 0 < F K' + K' - (1 + r) * 0 := by linarith
  have := hK' K' h1 h3
  unfold repayObjective defaultObjective at this
  have hle : u ((1 - η) * (F K' + K')) ≤ u (F K' + K' - (1 + r) * 0) :=
    hu (mem_Ioi.mpr h2) (mem_Ioi.mpr h3) (by nlinarith)
  nlinarith

/-- CRRA utility `u(C) = C^{1−ρ}/(1−ρ)`, `ρ > 0`, `ρ ≠ 1` (Chapter 2). (O&R §6.2.1, pp. 381–387.) -/
noncomputable def crra (ρ c : ℝ) : ℝ := c ^ (1 - ρ) / (1 - ρ)

/-- Homogeneity of CRRA utility: `u(λc) = λ^{1−ρ}u(c)` for `λ, c > 0`. (O&R §6.2.1, pp. 381–387.) -/
theorem crra_mul {ρ l c : ℝ} (hl : 0 < l) (hc : 0 < c) :
    crra ρ (l * c) = l ^ (1 - ρ) * crra ρ c := by
  unfold crra
  rw [mul_rpow hl.le hc.le]
  ring

/-- The rescaling identities behind the interval property (linear technology `F = αK`,
`1 + α > 0`). Given a repay plan `K` at debt `D′` and `l = W(D)/W(D′)` (ratio of repay wealths
(26)), the plan `K₀ = Y₁ + D − l(Y₁ + D′ − K)` at debt `D` has consumptions `l·C₁`, `l·C₂`.
(O&R §6.2.1, pp. 381–387.) -/
theorem repay_rescale {Y₁ α r D D' K l : ℝ} (hα : 0 < 1 + α)
    (hl : l * repayWealth Y₁ α r D' = repayWealth Y₁ α r D) :
    Y₁ + D - (Y₁ + D - l * (Y₁ + D' - K)) = l * (Y₁ + D' - K) ∧
      α * (Y₁ + D - l * (Y₁ + D' - K)) + (Y₁ + D - l * (Y₁ + D' - K)) - (1 + r) * D =
        l * (α * K + K - (1 + r) * D') := by
  have e1 : (1 + α) * repayWealth Y₁ α r D = (1 + α) * (Y₁ + D) - (1 + r) * D := by
    unfold repayWealth; field_simp; ring
  have e1' : (1 + α) * repayWealth Y₁ α r D' = (1 + α) * (Y₁ + D') - (1 + r) * D' := by
    unfold repayWealth; field_simp; ring
  refine ⟨by ring, ?_⟩
  linear_combination -e1 + l * e1' - (1 + α) * hl

/-- The rescaling identities for default plans (linear technology): given a default plan `K′`
at debt `D` and `m = (Y₁ + D)/(Y₁ + D′)`, the plan `K″ = Y₁ + D′ − (Y₁ + D − K′)/m` at `D′` has
consumptions `C₁/m`, `C₂/m`. (O&R §6.2.1, pp. 381–387.) -/
theorem default_rescale {Y₁ α η D D' K' m : ℝ} (hm : m ≠ 0)
    (hmD : m * (Y₁ + D') = Y₁ + D) :
    Y₁ + D' - (Y₁ + D' - (Y₁ + D - K') / m) = (Y₁ + D - K') / m ∧
      (1 - η) * (α * (Y₁ + D' - (Y₁ + D - K') / m) + (Y₁ + D' - (Y₁ + D - K') / m)) =
        (1 - η) * (α * K' + K') / m := by
  refine ⟨by ring, ?_⟩
  field_simp
  linear_combination (1 - η) * (1 + α) * hmD

/-- Shared ratio facts for the interval property: with `Y₁ > 0`, `r > −1`, `1 + α > 0`,
`0 ≤ D ≤ D′` and positive repay wealth at `D′`, the repay wealth at `D` is positive and
`m = (Y₁+D)/(Y₁+D′) ≤ l = W(D)/W(D′)`. (O&R §6.2.1, pp. 381–387.) -/
theorem wealth_ratio_le {Y₁ α r D D' : ℝ} (hY : 0 < Y₁) (hr : -1 < r) (hα : 0 < 1 + α)
    (hD : 0 ≤ D) (hDD : D ≤ D') (hW' : 0 < repayWealth Y₁ α r D') :
    0 < repayWealth Y₁ α r D ∧
      (Y₁ + D) / (Y₁ + D') ≤ repayWealth Y₁ α r D / repayWealth Y₁ α r D' := by
  have hW : 0 < repayWealth Y₁ α r D := by
    unfold repayWealth at hW' ⊢
    rcases le_total 0 ((α - r) / (1 + α)) with h | h
    · positivity
    · nlinarith
  refine ⟨hW, ?_⟩
  rw [div_le_div_iff₀ (by linarith) hW']
  have e : repayWealth Y₁ α r D * (Y₁ + D') - (Y₁ + D) * repayWealth Y₁ α r D' =
      Y₁ * ((1 + r) / (1 + α)) * (D' - D) := by
    unfold repayWealth
    field_simp
    ring
  have : 0 ≤ Y₁ * ((1 + r) / (1 + α)) * (D' - D) := by
    have : 0 < (1 + r) / (1 + α) := div_pos (by linarith) hα
    have : 0 ≤ D' - D := by linarith
    positivity
  linarith

/-- The interval property for CRRA utility and a linear technology, proved here (not in the
book): for `u(C) = C^{1−ρ}/(1−ρ)` (any `ρ ≠ 1`; `ρ > 0` is not needed), `F = αK`
(`1 + α > 0`), `r > −1`, `β ≥ 0`, `Y₁ > 0`: if repayment is preferred at `D′` then it is
preferred at every `0 ≤ D ≤ D′`. So the repay-preferred debt levels form an initial segment
of `[0, ∞)`. No use of (25). Proof: rescale the repay optimum at `D′` by `l = W(D)/W(D′)`
and every default plan at `D` by `1/m`, `m = (Y₁+D)/(Y₁+D′) ≤ l`, and use homogeneity of
`u`. (O&R §6.2.1, pp. 381–387.) -/
theorem repayPreferred_of_le_crra {ρ α r η β Y₁ D D' : ℝ} (hρ1 : ρ ≠ 1)
    (hβ : 0 ≤ β) (hr : -1 < r) (hα : 0 < 1 + α) (hY : 0 < Y₁) (hD : 0 ≤ D) (hDD : D ≤ D')
    (h : RepayPreferred (crra ρ) (fun K => α * K) Y₁ r η β D') :
    RepayPreferred (crra ρ) (fun K => α * K) Y₁ r η β D := by
  obtain ⟨K, hc1, hc2, hK⟩ := h
  simp only at hc2
  have hW' : 0 < repayWealth Y₁ α r D' := by
    rw [← repay_budget Y₁ α r D' K hα]; positivity
  obtain ⟨hW, hml⟩ := wealth_ratio_le hY hr hα hD hDD hW'
  set l := repayWealth Y₁ α r D / repayWealth Y₁ α r D' with hldef
  set m := (Y₁ + D) / (Y₁ + D') with hmdef
  have hl : 0 < l := div_pos hW hW'
  have hm : 0 < m := div_pos (by linarith) (by linarith)
  have hlW : l * repayWealth Y₁ α r D' = repayWealth Y₁ α r D := div_mul_cancel₀ _ hW'.ne'
  have hmD : m * (Y₁ + D') = Y₁ + D := div_mul_cancel₀ _ (by linarith)
  obtain ⟨e1, e2⟩ := repay_rescale (K := K) (r := r) hα hlW
  refine ⟨Y₁ + D - l * (Y₁ + D' - K), ?_, ?_, ?_⟩
  · rw [e1]; positivity
  · simp only
    rw [e2]; positivity
  intro K' h1 h2
  simp only at h2
  obtain ⟨f1, f2⟩ := default_rescale (α := α) (η := η) (K' := K') hm.ne' hmD
  have hK'' := hK (Y₁ + D' - (Y₁ + D - K') / m) (by rw [f1]; positivity)
    (by simp only; rw [f2]; positivity)
  unfold defaultObjective repayObjective at hK'' ⊢
  simp only at hK'' ⊢
  rw [f1, f2] at hK''
  rw [e1, e2, crra_mul hl hc1, crra_mul hl hc2]
  have hC1 : Y₁ + D - K' = m * ((Y₁ + D - K') / m) := by field_simp
  have hC2 : (1 - η) * (α * K' + K') = m * ((1 - η) * (α * K' + K') / m) := by field_simp
  rw [hC1, hC2, crra_mul hm (by positivity), crra_mul hm (by positivity)]
  set X := crra ρ (Y₁ + D' - K) + β * crra ρ (α * K + K - (1 + r) * D')
  set Z := crra ρ ((Y₁ + D - K') / m) + β * crra ρ ((1 - η) * (α * K' + K') / m)
  have hmZ : m ^ (1 - ρ) * Z ≤ m ^ (1 - ρ) * X :=
    mul_le_mul_of_nonneg_left hK'' (rpow_pos_of_pos hm _).le
  have goal : m ^ (1 - ρ) * X ≤ l ^ (1 - ρ) * X := by
    rcases lt_or_gt_of_ne hρ1 with hlt | hgt
    · have hX : 0 < X := by
        have h1ρ : 0 < 1 - ρ := by linarith
        have a1 : 0 < crra ρ (Y₁ + D' - K) := by unfold crra; positivity
        have a2 : 0 < crra ρ (α * K + K - (1 + r) * D') := by unfold crra; positivity
        positivity
      exact mul_le_mul_of_nonneg_right (rpow_le_rpow hm.le hml (by linarith)) hX.le
    · have hX : X < 0 := by
        have h1ρ : 1 - ρ < 0 := by linarith
        have a1 : crra ρ (Y₁ + D' - K) < 0 := by
          unfold crra; exact div_neg_of_pos_of_neg (by positivity) h1ρ
        have a2 : crra ρ (α * K + K - (1 + r) * D') < 0 := by
          unfold crra; exact div_neg_of_pos_of_neg (by positivity) h1ρ
        nlinarith
      exact mul_le_mul_of_nonpos_right (rpow_le_rpow_of_nonpos hm hml (by linarith)) hX.le
  have : m ^ (1 - ρ) * Z = m ^ (1 - ρ) * crra ρ ((Y₁ + D - K') / m) +
      β * (m ^ (1 - ρ) * crra ρ ((1 - η) * (α * K' + K') / m)) := by ring
  have : l ^ (1 - ρ) * X = l ^ (1 - ρ) * crra ρ (Y₁ + D' - K) +
      β * (l ^ (1 - ρ) * crra ρ (α * K + K - (1 + r) * D')) := by ring
  linarith

/-- The interval property for log utility and a linear technology, proved here: for
`u = log`, `F = αK` (`1 + α > 0`), `r > −1`, `β ≥ 0`, `Y₁ > 0`, if repayment is preferred at
`D′` then it is preferred at every `0 ≤ D ≤ D′` (same rescaling argument; no use of (25)).
(O&R §6.2.1, pp. 381–387.) -/
theorem repayPreferred_of_le_log {α r η β Y₁ D D' : ℝ}
    (hβ : 0 ≤ β) (hr : -1 < r) (hα : 0 < 1 + α) (hY : 0 < Y₁) (hD : 0 ≤ D) (hDD : D ≤ D')
    (h : RepayPreferred log (fun K => α * K) Y₁ r η β D') :
    RepayPreferred log (fun K => α * K) Y₁ r η β D := by
  obtain ⟨K, hc1, hc2, hK⟩ := h
  simp only at hc2
  have hW' : 0 < repayWealth Y₁ α r D' := by
    rw [← repay_budget Y₁ α r D' K hα]; positivity
  obtain ⟨hW, hml⟩ := wealth_ratio_le hY hr hα hD hDD hW'
  set l := repayWealth Y₁ α r D / repayWealth Y₁ α r D' with hldef
  set m := (Y₁ + D) / (Y₁ + D') with hmdef
  have hl : 0 < l := div_pos hW hW'
  have hm : 0 < m := div_pos (by linarith) (by linarith)
  have hlW : l * repayWealth Y₁ α r D' = repayWealth Y₁ α r D := div_mul_cancel₀ _ hW'.ne'
  have hmD : m * (Y₁ + D') = Y₁ + D := div_mul_cancel₀ _ (by linarith)
  obtain ⟨e1, e2⟩ := repay_rescale (K := K) (r := r) hα hlW
  refine ⟨Y₁ + D - l * (Y₁ + D' - K), ?_, ?_, ?_⟩
  · rw [e1]; positivity
  · simp only
    rw [e2]; positivity
  intro K' h1 h2
  simp only at h2
  obtain ⟨f1, f2⟩ := default_rescale (α := α) (η := η) (K' := K') hm.ne' hmD
  have hp1 : 0 < (Y₁ + D - K') / m := by positivity
  have hp2 : 0 < (1 - η) * (α * K' + K') / m := by positivity
  have hK'' := hK (Y₁ + D' - (Y₁ + D - K') / m) (by rw [f1]; positivity)
    (by simp only; rw [f2]; positivity)
  unfold defaultObjective repayObjective at hK'' ⊢
  simp only at hK'' ⊢
  rw [f1, f2] at hK''
  rw [e1, e2, log_mul hl.ne' hc1.ne', log_mul hl.ne' hc2.ne']
  have hC1 : Y₁ + D - K' = m * ((Y₁ + D - K') / m) := by field_simp
  have hC2 : (1 - η) * (α * K' + K') = m * ((1 - η) * (α * K' + K') / m) := by field_simp
  rw [hC1, hC2, log_mul hm.ne' hp1.ne', log_mul hm.ne' hp2.ne']
  have hlog : log m ≤ log l := log_le_log hm hml
  nlinarith

/-! ### The interval property fails in general: an explicit counterexample -/

/-- Counterexample utility: `u(C) = min(C, 3/2) + C/4 − C²/100` (strictly concave on `ℝ`,
strictly increasing for `C ≤ 12`). (O&R §6.2.1, pp. 381–387.) -/
noncomputable def counterUtility (c : ℝ) : ℝ := min c (3 / 2) + c / 4 - c ^ 2 / 100

/-- Counterexample technology: `F(K) = K − K²/100` (strictly concave, `F(0) = 0`, strictly
increasing with `F′ > 0` for `K < 50`). (O&R §6.2.1, pp. 381–387.) -/
noncomputable def counterTechnology (K : ℝ) : ℝ := K - K ^ 2 / 100

/-- The counterexample utility is strictly concave (O&R's standing assumption `u″ < 0`, in the
form of strict concavity). -/
theorem counterUtility_strictConcaveOn : StrictConcaveOn ℝ univ counterUtility := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, counterUtility]
  have hmin : a * min x (3 / 2) + b * min y (3 / 2) ≤ min (a * x + b * y) (3 / 2) :=
    le_min (by nlinarith [min_le_left x (3 / 2 : ℝ), min_le_left y (3 / 2 : ℝ)])
      (by nlinarith [min_le_right x (3 / 2 : ℝ), min_le_right y (3 / 2 : ℝ)])
  have hsq : 0 < a * b * (x - y) ^ 2 := by
    have : 0 < (x - y) ^ 2 := by
      have : x - y ≠ 0 := sub_ne_zero.mpr hxy
      positivity
    positivity
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith

/-- The counterexample utility is strictly increasing on consumption levels `C ≤ 12` (all
feasible consumptions in the counterexample are below `7`). (O&R §6.2.1, pp. 381–387.) -/
theorem counterUtility_strictMonoOn : StrictMonoOn counterUtility (Iic 12) := by
  intro x hx y hy hxy
  rw [mem_Iic] at hx hy
  unfold counterUtility
  have := min_le_min_right (3 / 2 : ℝ) hxy.le
  nlinarith

/-- The counterexample technology is strictly concave (`F″ < 0`). (O&R §6.2.1, pp. 381–387.) -/
theorem counterTechnology_strictConcaveOn : StrictConcaveOn ℝ univ counterTechnology := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, counterTechnology]
  have hsq : 0 < a * b * (x - y) ^ 2 := by
    have : 0 < (x - y) ^ 2 := by
      have : x - y ≠ 0 := sub_ne_zero.mpr hxy
      positivity
    positivity
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith

/-- The counterexample technology is strictly increasing on `K ≤ 50`, with `F(0) = 0` and
`F′(K) = 1 − K/50 > 0` there. (O&R §6.2.1, pp. 381–387.) -/
theorem counterTechnology_props :
    StrictMonoOn counterTechnology (Iic 50) ∧ counterTechnology 0 = 0 ∧
      ∀ K, HasDerivAt counterTechnology (1 - K / 50) K := by
  refine ⟨fun x hx y hy hxy => ?_, by norm_num [counterTechnology], fun K => ?_⟩
  · rw [mem_Iic] at hx hy
    unfold counterTechnology
    nlinarith
  · have h := HasDerivAt.sub (hasDerivAt_id' K) ((hasDerivAt_pow 2 K).div_const 100)
    unfold counterTechnology
    refine h.congr_deriv ?_
    norm_num
    ring

/-- In the counterexample the analogue of (25) fails at low investment:
`η(1 + F′(0)) = 3/2 > 1 = 1 + r` (with `η = 3/4`, `r = 0`). (O&R §6.2.1, pp. 381–387.) -/
theorem counterexample_violates_ineq25 :
    (1 + (0 : ℝ)) < 3 / 4 * (1 + (1 - (0 : ℝ) / 50)) := by norm_num

/-- The sovereign strictly prefers default at `D = 1/2` in the counterexample
(`Y₁ = 1`, `r = 0`, `η = 3/4`, `β = 1/2`): defaulting with `K′ = 1/100` beats every
repay-feasible plan (whose utility is at most `25/16`). (O&R §6.2.1, pp. 381–387.) -/
theorem counterexample_default_at_half :
    DefaultPreferred counterUtility counterTechnology 1 0 (3 / 4) (1 / 2) (1 / 2) := by
  refine ⟨1 / 100, by norm_num, by norm_num [counterTechnology], fun K h1 h2 => ?_⟩
  have hv : (25 / 16 : ℝ) <
      defaultObjective counterUtility counterTechnology 1 (3 / 4) (1 / 2) (1 / 2) (1 / 100) := by
    norm_num [defaultObjective, counterUtility, counterTechnology, min_def]
  refine lt_of_le_of_lt ?_ hv
  unfold repayObjective counterUtility counterTechnology
  have m1 := min_le_left (1 + 1 / 2 - K) (3 / 2 : ℝ)
  have m2 := min_le_left (K - K ^ 2 / 100 + K - (1 + 0) * (1 / 2)) (3 / 2 : ℝ)
  nlinarith [sq_nonneg K, sq_nonneg (1 + 1 / 2 - K),
    sq_nonneg (K - K ^ 2 / 100 + K - (1 + 0) * (1 / 2))]

/-- The sovereign strictly prefers repayment at `D = 5/2` in the counterexample: repaying with
`K = 2` gives utility `2.754…`, while every default-feasible plan gives at most `5/2`.
(O&R §6.2.1, pp. 381–387.) -/
theorem counterexample_repay_at_five_halves :
    RepayPreferred counterUtility counterTechnology 1 0 (3 / 4) (1 / 2) (5 / 2) := by
  refine ⟨2, by norm_num, by norm_num [counterTechnology], fun K' h1 h2 => ?_⟩
  have hv : (5 / 2 : ℝ) <
      repayObjective counterUtility counterTechnology 1 0 (1 / 2) (5 / 2) 2 := by
    norm_num [repayObjective, counterUtility, counterTechnology, min_def]
  refine le_trans ?_ hv.le
  unfold defaultObjective counterUtility counterTechnology
  have m1 := min_le_left (1 + 5 / 2 - K') (3 / 2 : ℝ)
  have m1' := min_le_right (1 + 5 / 2 - K') (3 / 2 : ℝ)
  have m2 := min_le_left ((1 - 3 / 4) * (K' - K' ^ 2 / 100 + K')) (3 / 2 : ℝ)
  nlinarith [sq_nonneg K', sq_nonneg (1 + 5 / 2 - K'),
    sq_nonneg ((1 - 3 / 4) * (K' - K' ^ 2 / 100 + K'))]

/-- The repayment-set interval property of §6.2.1.2 FAILS in general, O&R p. 387: with the
strictly increasing (on all feasible consumption), strictly concave `u = counterUtility` and
the strictly increasing, strictly concave `F = counterTechnology` (and `Y₁ = 1`, `r = 0`,
`η = 3/4`, `β = 1/2`), repayment is strictly preferred at `D = 5/2` but default is strictly
preferred at `D = 1/2`: the repay-preferred debt levels are not an initial segment, so no `D̄`
has "repay for every `D ≤ D̄`". -/
theorem repaySet_not_interval :
    ¬ (∀ D D' : ℝ, 0 ≤ D → D ≤ D' →
        RepayPreferred counterUtility counterTechnology 1 0 (3 / 4) (1 / 2) D' →
        RepayPreferred counterUtility counterTechnology 1 0 (3 / 4) (1 / 2) D) := by
  intro h
  exact not_defaultPreferred_of_repayPreferred
    (h (1 / 2) (5 / 2) (by norm_num) (by norm_num) counterexample_repay_at_five_halves)
    counterexample_default_at_half

/-! ### The interval property under the analogue of (25)

The counterexample above violates `η(1 + F′) < 1 + r`. Under that condition (only at the repay
optimum) the interval property holds for every strictly increasing, concave, differentiable `u`
and concave differentiable `F`, whenever optimal plans exist. Proof: with
`Φ(D) = U^D(D) − U^N(D)`, (i) `Φ` is "right-closed" (`Φ ≤ 0` just to the right of `t` forces
`Φ(t) ≤ 0`, by the supergradient of the concave repay value); (ii) wherever repayment is weakly
preferred, `Φ < 0` just to the left, because the envelope slope
`u′(C₁ᴰ) − u′(C₁ᴺ) + β(1+r)u′(C₂ᴺ)` is positive there (this is where the condition is used);
(iii) a real-induction argument. (The naive envelope claim `d(U^N − U^D)/dD =
−β(1+r)u′(C₂ᴺ) < 0` is wrong: the date-1 marginal utilities `u′(C₁ᴺ)`, `u′(C₁ᴰ)` are evaluated
at different investment levels and do not cancel — which is why the counterexample exists.) -/

/-- Repay feasibility (positive consumption on both dates), O&R p. 383. -/
def RepayFeasible (F : ℝ → ℝ) (Y₁ r D K : ℝ) : Prop :=
  0 < Y₁ + D - K ∧ 0 < F K + K - (1 + r) * D

/-- Default feasibility (positive consumption on both dates), O&R p. 383. -/
def DefaultFeasible (F : ℝ → ℝ) (Y₁ η D K : ℝ) : Prop :=
  0 < Y₁ + D - K ∧ 0 < (1 - η) * (F K + K)

/-- The tangent-line inequality for a concave function (used for the supergradients of the
value functions, O&R p. 384): `f(y) ≤ f(x₀) + f′(x₀)(y − x₀)`. -/
theorem tangent_le_of_concaveOn {f : ℝ → ℝ} {S : Set ℝ} (hf : ConcaveOn ℝ S f) {x₀ y d : ℝ}
    (hx : x₀ ∈ S) (hy : y ∈ S) (hd : HasDerivAt f d x₀) : f y ≤ f x₀ + d * (y - x₀) := by
  rcases lt_trichotomy x₀ y with h | h | h
  · have := hf.slope_le_of_hasDerivAt hx hy h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith
  · subst h
    simp
  · have := hf.le_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith

/-- Derivatives of a concave function are antitone: `x ≤ y` ⇒ `f′(y) ≤ f′(x)`.
(O&R §6.2.1, pp. 381–387.) -/
theorem deriv_antitone_of_concaveOn {f : ℝ → ℝ} {S : Set ℝ} (hf : ConcaveOn ℝ S f)
    {x y a b : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≤ y) (ha : HasDerivAt f a x)
    (hb : HasDerivAt f b y) : b ≤ a := by
  rcases hxy.lt_or_eq with h | h
  · exact (hf.le_slope_of_hasDerivAt hx hy h hb).trans (hf.slope_le_of_hasDerivAt hx hy h ha)
  · subst h; exact le_of_eq (hb.unique ha)

/-- The supergradient of the default value, O&R p. 384 (the envelope derivative `u′(C₁ᴰ)` of
`U^D` is a supergradient because the default problem is jointly concave in `(D, K)`): if `K^D`
is default-feasible at `D₀` and satisfies the first-order condition
`u′(C₁) = β(1−η)u′(C₂)(1 + F′(K^D))`, then for every default-feasible `(D, K)`,
`U^D(D, K) ≤ U^D(D₀, K^D) + u′(C₁ᴰ)(D − D₀)`. -/
theorem default_supergradient {u F : ℝ → ℝ} (hu : ConcaveOn ℝ (Ioi 0) u)
    (hG : ConcaveOn ℝ univ fun K => F K + K) {Y₁ η β D₀ KD u₁ u₂ f₁ : ℝ} (hβ : 0 ≤ β)
    (hη : η < 1) (hfeas : DefaultFeasible F Y₁ η D₀ KD)
    (hu₁ : HasDerivAt u u₁ (Y₁ + D₀ - KD)) (hu₂ : HasDerivAt u u₂ ((1 - η) * (F KD + KD)))
    (hF : HasDerivAt F f₁ KD) (hu₂0 : 0 ≤ u₂) (hfoc : u₁ = β * (u₂ * ((1 - η) * (f₁ + 1))))
    {D K : ℝ} (h : DefaultFeasible F Y₁ η D K) :
    defaultObjective u F Y₁ η β D K ≤ defaultObjective u F Y₁ η β D₀ KD + u₁ * (D - D₀) := by
  unfold defaultObjective
  have t1 := tangent_le_of_concaveOn hu (mem_Ioi.mpr hfeas.1) (mem_Ioi.mpr h.1) hu₁
  have t2 := tangent_le_of_concaveOn hu (mem_Ioi.mpr hfeas.2) (mem_Ioi.mpr h.2) hu₂
  have t3 := tangent_le_of_concaveOn hG (mem_univ KD) (mem_univ K) (hF.add (hasDerivAt_id KD))
  have t3' := mul_le_mul_of_nonneg_left t3 (mul_nonneg (mul_nonneg hβ hu₂0)
    (by linarith : (0 : ℝ) ≤ 1 - η))
  have t2' := mul_le_mul_of_nonneg_left t2 hβ
  have e : u₁ * (K - KD) = β * u₂ * (1 - η) * (f₁ + 1) * (K - KD) := by rw [hfoc]; ring
  linarith

/-- The supergradient of the repay value, O&R p. 384 (the repay problem is jointly concave in
`(D, K)`): if `K^N` is repay-feasible at `D₀` and satisfies `u′(C₁) = βu′(C₂)(1 + F′(K^N))`,
then for every repay-feasible `(D, K)`,
`U^N(D, K) ≤ U^N(D₀, K^N) + [u′(C₁ᴺ) − β(1+r)u′(C₂ᴺ)](D − D₀)`. -/
theorem repay_supergradient {u F : ℝ → ℝ} (hu : ConcaveOn ℝ (Ioi 0) u)
    (hG : ConcaveOn ℝ univ fun K => F K + K) {Y₁ r β D₀ KN u₁ u₂ f₁ : ℝ} (hβ : 0 ≤ β)
    (hfeas : RepayFeasible F Y₁ r D₀ KN)
    (hu₁ : HasDerivAt u u₁ (Y₁ + D₀ - KN)) (hu₂ : HasDerivAt u u₂ (F KN + KN - (1 + r) * D₀))
    (hF : HasDerivAt F f₁ KN) (hu₂0 : 0 ≤ u₂) (hfoc : u₁ = β * (u₂ * (f₁ + 1)))
    {D K : ℝ} (h : RepayFeasible F Y₁ r D K) :
    repayObjective u F Y₁ r β D K ≤
      repayObjective u F Y₁ r β D₀ KN + (u₁ - β * (1 + r) * u₂) * (D - D₀) := by
  unfold repayObjective
  have t1 := tangent_le_of_concaveOn hu (mem_Ioi.mpr hfeas.1) (mem_Ioi.mpr h.1) hu₁
  have t2 := tangent_le_of_concaveOn hu (mem_Ioi.mpr hfeas.2) (mem_Ioi.mpr h.2) hu₂
  have t3 := tangent_le_of_concaveOn hG (mem_univ KN) (mem_univ K) (hF.add (hasDerivAt_id KN))
  have t3' := mul_le_mul_of_nonneg_left t3 (mul_nonneg hβ hu₂0)
  have t2' := mul_le_mul_of_nonneg_left t2 hβ
  have e : u₁ * (K - KN) = β * u₂ * (f₁ + 1) * (K - KN) := by rw [hfoc]; ring
  linarith

/-- The envelope slope of `U^D − U^N` is positive wherever repayment is weakly preferred, under
the analogue of (25) at the repay optimum, O&R pp. 383–384: with FOCs at both optima, `u`
concave and strictly increasing with `u′ > 0`, `F + K` concave, `η < 1`, `β > 0`, `r > −1`,
`η(1 + F′(K^N)) < 1 + r` and `U^D(D₀) ≤ U^N(D₀)`:
`0 < u′(C₁ᴰ) − u′(C₁ᴺ) + β(1+r)u′(C₂ᴺ)`. -/
theorem envelope_slope_pos {u F u' F' : ℝ → ℝ} (hu : ConcaveOn ℝ (Ioi 0) u)
    (hum : StrictMonoOn u (Ioi 0)) (hu' : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hu'p : ∀ c, 0 < c → 0 < u' c) (hF : ∀ K, HasDerivAt F (F' K) K)
    (hG : ConcaveOn ℝ univ fun K => F K + K) {Y₁ r η β D₀ KN KD : ℝ} (hβ : 0 < β)
    (hη : η < 1) (hr : -1 < r) (h25 : η * (1 + F' KN) < 1 + r)
    (hN : RepayFeasible F Y₁ r D₀ KN) (hD : DefaultFeasible F Y₁ η D₀ KD)
    (hfN : u' (Y₁ + D₀ - KN) = β * (u' (F KN + KN - (1 + r) * D₀) * (F' KN + 1)))
    (hfD : u' (Y₁ + D₀ - KD) = β * (u' ((1 - η) * (F KD + KD)) * ((1 - η) * (F' KD + 1))))
    (hpref : defaultObjective u F Y₁ η β D₀ KD ≤ repayObjective u F Y₁ r β D₀ KN) :
    0 < u' (Y₁ + D₀ - KD) - u' (Y₁ + D₀ - KN) +
      β * (1 + r) * u' (F KN + KN - (1 + r) * D₀) := by
  set cN := Y₁ + D₀ - KN
  set cD := Y₁ + D₀ - KD
  set C2N := F KN + KN - (1 + r) * D₀
  set C2D := (1 - η) * (F KD + KD)
  have hC2N := hu'p C2N hN.2
  have h1r : 0 < 1 + r := by linarith
  rcases le_or_gt cD cN with hc | hc
  · have := deriv_antitone_of_concaveOn hu (mem_Ioi.mpr hD.1) (mem_Ioi.mpr hN.1) hc
      (hu' cD hD.1) (hu' cN hN.1)
    have : 0 < β * (1 + r) * u' C2N := by positivity
    linarith
  · -- `c^D > c^N`: then `K^D < K^N` and, by weak preference, `C₂ᴰ < C₂ᴺ`
    have hK : KD < KN := by
      simp only [cD, cN] at hc; linarith
    have hucl : u cN < u cD := hum (mem_Ioi.mpr hN.1) (mem_Ioi.mpr hD.1) hc
    have hC2 : C2D ≤ C2N := by
      by_contra h
      push Not at h
      have := hum (mem_Ioi.mpr hN.2) (mem_Ioi.mpr hD.2) h
      unfold defaultObjective repayObjective at hpref
      nlinarith
    have hu2 := deriv_antitone_of_concaveOn hu (mem_Ioi.mpr hD.2) (mem_Ioi.mpr hN.2) hC2
      (hu' C2D hD.2) (hu' C2N hN.2)
    have hf := deriv_antitone_of_concaveOn hG (mem_univ KD) (mem_univ KN) hK.le
      ((hF KD).add (hasDerivAt_id KD)) ((hF KN).add (hasDerivAt_id KN))
    have hfN1 : 0 < F' KN + 1 := by
      have := hu'p cN hN.1
      rw [hfN] at this
      by_contra h
      push Not at h
      have : β * (u' C2N * (F' KN + 1)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hβ.le (mul_nonpos_of_nonneg_of_nonpos hC2N.le h)
      linarith
    have hprod : u' C2N * (F' KN + 1) ≤ u' C2D * (F' KD + 1) :=
      mul_le_mul hu2 hf hfN1.le (hC2N.le.trans hu2)
    have h1η : 0 < 1 - η := by linarith
    have hD' : β * (1 - η) * (u' C2N * (F' KN + 1)) ≤ u' cD := by
      rw [hfD]
      have := mul_le_mul_of_nonneg_left hprod (mul_nonneg hβ.le h1η.le)
      linarith
    have key : 0 < β * u' C2N * (1 + r - η * (1 + F' KN)) := by
      have : 0 < 1 + r - η * (1 + F' KN) := by linarith
      positivity
    rw [hfN]
    nlinarith

/-- A first-order condition from optimality over an open feasible set: if `K*` maximises the
repay objective over the repay-feasible plans, `F` is continuous and `u`, `F` differentiable at
the relevant points, then `u′(C₁) = βu′(C₂)(1 + F′(K*))` (O&R §6.2.1.2). -/
theorem repay_foc_of_max {u F u' F' : ℝ → ℝ} (hu' : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hF : ∀ K, HasDerivAt F (F' K) K) {Y₁ r β D KN : ℝ} (hN : RepayFeasible F Y₁ r D KN)
    (hmax : ∀ K, RepayFeasible F Y₁ r D K →
      repayObjective u F Y₁ r β D K ≤ repayObjective u F Y₁ r β D KN) :
    u' (Y₁ + D - KN) = β * (u' (F KN + KN - (1 + r) * D) * (F' KN + 1)) := by
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun K => (hF K).continuousAt
  have hopen : IsOpen {K | RepayFeasible F Y₁ r D K} := by
    have e : {K | RepayFeasible F Y₁ r D K} =
        {K | (0 : ℝ) < Y₁ + D - K} ∩ {K | (0 : ℝ) < F K + K - (1 + r) * D} := rfl
    rw [e]
    exact (isOpen_lt continuous_const (by fun_prop)).inter
      (isOpen_lt continuous_const (by fun_prop))
  have hloc : IsLocalMax (repayObjective u F Y₁ r β D) KN :=
    (isMaxOn_iff.mpr fun K hK => hmax K hK).isLocalMax (hopen.mem_nhds hN)
  have := hloc.hasDerivAt_eq_zero (hasDerivAt_repayObjective (β := β) (hu' _ hN.1) (hu' _ hN.2)
    (hF KN))
  linarith

/-- A first-order condition for the default optimum over its open feasible set:
`u′(C₁) = β(1−η)u′(C₂)(1 + F′(K*))` (O&R p. 383). -/
theorem default_foc_of_max {u F u' F' : ℝ → ℝ} (hu' : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hF : ∀ K, HasDerivAt F (F' K) K) {Y₁ η β D KD : ℝ} (hD : DefaultFeasible F Y₁ η D KD)
    (hmax : ∀ K, DefaultFeasible F Y₁ η D K →
      defaultObjective u F Y₁ η β D K ≤ defaultObjective u F Y₁ η β D KD) :
    u' (Y₁ + D - KD) = β * (u' ((1 - η) * (F KD + KD)) * ((1 - η) * (F' KD + 1))) := by
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun K => (hF K).continuousAt
  have hopen : IsOpen {K | DefaultFeasible F Y₁ η D K} := by
    have e : {K | DefaultFeasible F Y₁ η D K} =
        {K | (0 : ℝ) < Y₁ + D - K} ∩ {K | (0 : ℝ) < (1 - η) * (F K + K)} := rfl
    rw [e]
    exact (isOpen_lt continuous_const (by fun_prop)).inter
      (isOpen_lt continuous_const (by fun_prop))
  have hloc : IsLocalMax (defaultObjective u F Y₁ η β D) KD :=
    (isMaxOn_iff.mpr fun K hK => hmax K hK).isLocalMax (hopen.mem_nhds hD)
  have := hloc.hasDerivAt_eq_zero (hasDerivAt_defaultObjective (β := β) (hu' _ hD.1)
    (hu' _ hD.2) (hF KD))
  linarith

/-- The default-minus-repay value gap `Φ(D) = U^D(D) − U^N(D)` along given optimal plans
`K^N(D)`, `K^D(D)` (O&R p. 384). -/
noncomputable def valueGap (u F : ℝ → ℝ) (Y₁ r η β : ℝ) (KN KD : ℝ → ℝ) (D : ℝ) : ℝ :=
  defaultObjective u F Y₁ η β D (KD D) - repayObjective u F Y₁ r β D (KN D)

/-- Optimal repay plans on `[a, b]`: `K^N(D)` is repay-feasible and maximises the repay
objective over all repay-feasible plans (O&R p. 383). -/
def RepayOptimal (u F : ℝ → ℝ) (Y₁ r β a b : ℝ) (KN : ℝ → ℝ) : Prop :=
  ∀ D ∈ Icc a b, RepayFeasible F Y₁ r D (KN D) ∧
    ∀ K, RepayFeasible F Y₁ r D K → repayObjective u F Y₁ r β D K ≤
      repayObjective u F Y₁ r β D (KN D)

/-- Optimal default plans on `[a, b]` (O&R p. 383). -/
def DefaultOptimal (u F : ℝ → ℝ) (Y₁ η β a b : ℝ) (KD : ℝ → ℝ) : Prop :=
  ∀ D ∈ Icc a b, DefaultFeasible F Y₁ η D (KD D) ∧
    ∀ K, DefaultFeasible F Y₁ η D K → defaultObjective u F Y₁ η β D K ≤
      defaultObjective u F Y₁ η β D (KD D)

/-- The repay objective's derivative in debt at fixed investment:
`∂U^N/∂D = u′(C₁) − (1+r)βu′(C₂)` (O&R p. 384). -/
theorem hasDerivAt_repayObjective_debt {u F : ℝ → ℝ} {Y₁ r β D K u₁ u₂ : ℝ}
    (hu₁ : HasDerivAt u u₁ (Y₁ + D - K)) (hu₂ : HasDerivAt u u₂ (F K + K - (1 + r) * D)) :
    HasDerivAt (fun D => repayObjective u F Y₁ r β D K) (u₁ - (1 + r) * β * u₂) D := by
  have h1 : HasDerivAt (fun D => Y₁ + D - K) 1 D := by
    simpa using ((hasDerivAt_id D).const_add Y₁).sub_const K
  have h2 : HasDerivAt (fun D => F K + K - (1 + r) * D) (-(1 + r)) D := by
    simpa using ((hasDerivAt_id D).const_mul (1 + r)).const_sub (F K + K)
  unfold repayObjective
  exact HasDerivAt.congr_deriv (HasDerivAt.add (hu₁.comp D h1) ((hu₂.comp D h2).const_mul β))
    (by ring)

/-- A left-sided first-order bound: if `g′(t) = d` and `e > 0`, then
`g(x) ≥ g(t) + d(x − t) − e(t − x)` for all `x < t` close to `t`. (O&R §6.2.1, pp. 381–387.) -/
theorem eventually_left_lower {g : ℝ → ℝ} {t d e : ℝ} (hg : HasDerivAt g d t) (he : 0 < e) :
    ∀ᶠ x in 𝓝[<] t, g t + d * (x - t) - e * (t - x) ≤ g x := by
  have ht : Tendsto (slope g t) (𝓝[<] t) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope.mp hg).mono_left
      (nhdsWithin_mono _ fun y (hy : y < t) => hy.ne)
  filter_upwards [ht.eventually (gt_mem_nhds (by linarith : d < d + e)), self_mem_nhdsWithin]
    with x hx hx'
  rw [mem_Iio] at hx'
  rw [slope_def_field, div_lt_iff_of_neg (by linarith)] at hx
  nlinarith

/-- Right-closedness of the repay-preferred set (O&R p. 387): if repayment is weakly preferred
at every `x` just to the right of `t ∈ [a, b)`, it is weakly preferred at `t`. -/
theorem valueGap_nonpos_of_right {u F u' F' : ℝ → ℝ} (hu : ConcaveOn ℝ (Ioi 0) u)
    (hum : StrictMonoOn u (Ioi 0)) (hu' : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hu'p : ∀ c, 0 < c → 0 < u' c) (hF : ∀ K, HasDerivAt F (F' K) K)
    (hG : ConcaveOn ℝ univ fun K => F K + K) {Y₁ r η β a b : ℝ} (hβ : 0 < β)
    {KN KD : ℝ → ℝ} (hNo : RepayOptimal u F Y₁ r β a b KN)
    (hDo : DefaultOptimal u F Y₁ η β a b KD) {t : ℝ} (ht : t ∈ Ico a b)
    (hright : ∀ᶠ x in 𝓝[>] t, valueGap u F Y₁ r η β KN KD x ≤ 0) :
    valueGap u F Y₁ r η β KN KD t ≤ 0 := by
  have htI : t ∈ Icc a b := Ico_subset_Icc_self ht
  obtain ⟨hNf, hNm⟩ := hNo t htI
  obtain ⟨hDf, -⟩ := hDo t htI
  have hfoc := repay_foc_of_max hu' hF hNf hNm
  set c := u' (Y₁ + t - KN t) - β * (1 + r) * u' (F (KN t) + KN t - (1 + r) * t)
  have hbound : ∀ᶠ x in 𝓝[>] t, valueGap u F Y₁ r η β KN KD t ≤ c * (x - t) := by
    filter_upwards [hright, self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds ht.2)]
      with x hx hxt hxb
    rw [mem_Ioi] at hxt
    rw [mem_Iio] at hxb
    have hxI : x ∈ Icc a b := ⟨ht.1.trans hxt.le, hxb.le⟩
    obtain ⟨hNfx, -⟩ := hNo x hxI
    obtain ⟨-, hDmx⟩ := hDo x hxI
    have hfeas : DefaultFeasible F Y₁ η x (KD t) := ⟨by linarith [hDf.1], hDf.2⟩
    have h1 : defaultObjective u F Y₁ η β t (KD t) ≤ defaultObjective u F Y₁ η β x (KD t) := by
      unfold defaultObjective
      have := hum.monotoneOn (mem_Ioi.mpr hDf.1) (mem_Ioi.mpr hfeas.1) (by linarith)
      linarith
    have h2 := hDmx (KD t) hfeas
    have h3 := repay_supergradient hu hG hβ.le hNf (hu' _ hNf.1) (hu' _ hNf.2) (hF (KN t))
      (hu'p _ hNf.2).le hfoc hNfx
    unfold valueGap at hx ⊢
    linarith
  have hlim : Tendsto (fun x => c * (x - t)) (𝓝[>] t) (𝓝 0) := by
    have : Tendsto (fun x => c * (x - t)) (𝓝 t) (𝓝 (c * (t - t))) :=
      (continuous_const.mul (continuous_id.sub continuous_const)).tendsto t
    rw [sub_self, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim hbound

/-- Repayment is strictly preferred just to the left of any point where it is weakly preferred,
under the analogue of (25) at the repay optimum (O&R pp. 384–385). -/
theorem valueGap_neg_left {u F u' F' : ℝ → ℝ} (hu : ConcaveOn ℝ (Ioi 0) u)
    (hum : StrictMonoOn u (Ioi 0)) (hu' : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hu'p : ∀ c, 0 < c → 0 < u' c) (hF : ∀ K, HasDerivAt F (F' K) K)
    (hG : ConcaveOn ℝ univ fun K => F K + K) {Y₁ r η β a b : ℝ} (hβ : 0 < β) (hη : η < 1)
    (hr : -1 < r) {KN KD : ℝ → ℝ} (hNo : RepayOptimal u F Y₁ r β a b KN)
    (hDo : DefaultOptimal u F Y₁ η β a b KD) {t : ℝ} (ht : t ∈ Ioc a b)
    (h25 : η * (1 + F' (KN t)) < 1 + r) (h0 : valueGap u F Y₁ r η β KN KD t ≤ 0) :
    ∀ᶠ x in 𝓝[<] t, valueGap u F Y₁ r η β KN KD x < 0 := by
  have htI : t ∈ Icc a b := Ioc_subset_Icc_self ht
  obtain ⟨hNf, hNm⟩ := hNo t htI
  obtain ⟨hDf, hDm⟩ := hDo t htI
  have hfN := repay_foc_of_max hu' hF hNf hNm
  have hfD := default_foc_of_max hu' hF hDf hDm
  have hS := envelope_slope_pos hu hum hu' hu'p hF hG hβ hη hr h25 hNf hDf hfN hfD
    (by unfold valueGap at h0; linarith)
  set S := u' (Y₁ + t - KD t) - u' (Y₁ + t - KN t) +
    β * (1 + r) * u' (F (KN t) + KN t - (1 + r) * t) with hSdef
  have hderiv := hasDerivAt_repayObjective_debt (β := β) (hu' _ hNf.1) (hu' _ hNf.2)
  have hlow := eventually_left_lower hderiv (half_pos hS)
  have hc1 : ∀ᶠ x in 𝓝[<] t, 0 < Y₁ + x - KN t := by
    have : ContinuousAt (fun x => Y₁ + x - KN t) t := by fun_prop
    exact nhdsWithin_le_nhds (this.eventually (lt_mem_nhds hNf.1))
  filter_upwards [hlow, hc1, self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds ht.1)]
    with x hx hx1 hxt hxa
  rw [mem_Iio] at hxt
  rw [mem_Ioi] at hxa
  have hxI : x ∈ Icc a b := ⟨hxa.le, hxt.le.trans ht.2⟩
  obtain ⟨-, hNmx⟩ := hNo x hxI
  obtain ⟨hDfx, -⟩ := hDo x hxI
  have hfeasN : RepayFeasible F Y₁ r x (KN t) := ⟨hx1, by nlinarith [hNf.2]⟩
  have h1 := hNmx (KN t) hfeasN
  have h2 := default_supergradient hu hG hβ.le hη hDf (hu' _ hDf.1) (hu' _ hDf.2) (hF (KD t))
    (hu'p _ hDf.2).le hfD hDfx
  unfold valueGap at h0 ⊢
  have : 0 < S / 2 * (t - x) := mul_pos (half_pos hS) (by linarith)
  nlinarith

/-- THE REPAYMENT-SET INTERVAL PROPERTY under the analogue of (25), O&R §6.2.1.2, p. 387
(asserted, not proved, in the book): let `u` be strictly increasing and concave on `(0, ∞)` with
positive derivative `u′`, `F` differentiable with `F + K` concave, `β > 0`, `η < 1`, `r > −1`,
and let `K^N(D)`, `K^D(D)` be optimal repay and default plans for every `D ∈ [a, b]`. If
`η(1 + F′(K^N(D))) < 1 + r` for all `D ∈ [a, b]`, then the set of debt levels in `[a, b]` at
which repayment is weakly preferred is an initial segment: repayment preferred at `D′` implies
repayment preferred at every `D ∈ [a, D′]`. (`repaySet_not_interval` shows the condition cannot
be dropped.) -/
theorem repay_interval_of_ineq25 {u F u' F' : ℝ → ℝ} (hu : ConcaveOn ℝ (Ioi 0) u)
    (hum : StrictMonoOn u (Ioi 0)) (hu' : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hu'p : ∀ c, 0 < c → 0 < u' c) (hF : ∀ K, HasDerivAt F (F' K) K)
    (hG : ConcaveOn ℝ univ fun K => F K + K) {Y₁ r η β a b : ℝ} (hβ : 0 < β) (hη : η < 1)
    (hr : -1 < r) {KN KD : ℝ → ℝ} (hNo : RepayOptimal u F Y₁ r β a b KN)
    (hDo : DefaultOptimal u F Y₁ η β a b KD)
    (h25 : ∀ D ∈ Icc a b, η * (1 + F' (KN D)) < 1 + r) {D D' : ℝ} (haD : a ≤ D)
    (hDD : D ≤ D') (hD'b : D' ≤ b) (hD' : valueGap u F Y₁ r η β KN KD D' ≤ 0) :
    valueGap u F Y₁ r η β KN KD D ≤ 0 := by
  set Φ := valueGap u F Y₁ r η β KN KD with hΦ
  set T := {x | x ∈ Icc D D' ∧ ∀ y ∈ Icc x D', Φ y ≤ 0} with hT
  have hD'T : D' ∈ T := ⟨⟨hDD, le_rfl⟩, fun y hy => by rw [le_antisymm hy.2 hy.1]; exact hD'⟩
  have hTne : T.Nonempty := ⟨D', hD'T⟩
  have hTbdd : BddBelow T := ⟨D, fun x hx => hx.1.1⟩
  set t := sInf T with htdef
  have hDt : D ≤ t := le_csInf hTne fun x hx => hx.1.1
  have htD' : t ≤ D' := csInf_le hTbdd hD'T
  -- every `y ∈ (t, D']` has `Φ y ≤ 0`
  have hgt : ∀ y, t < y → y ≤ D' → Φ y ≤ 0 := by
    intro y hty hyD'
    obtain ⟨x, hxT, hxy⟩ := exists_lt_of_csInf_lt hTne hty
    exact hxT.2 y ⟨hxy.le, hyD'⟩
  have htI : t ∈ Icc a b := ⟨haD.trans hDt, htD'.trans hD'b⟩
  have hΦt : Φ t ≤ 0 := by
    rcases htD'.lt_or_eq with hlt | heq
    · apply valueGap_nonpos_of_right hu hum hu' hu'p hF hG hβ hNo hDo
        ⟨htI.1, lt_of_lt_of_le hlt hD'b⟩
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hlt)] with y hy hy'
      exact hgt y hy (le_of_lt hy')
    · rw [heq]; exact hD'
  have htT : t ∈ T := ⟨⟨hDt, htD'⟩, fun y hy => by
    rcases hy.1.lt_or_eq with h | h
    · exact hgt y h hy.2
    · rw [← h]; exact hΦt⟩
  rcases hDt.lt_or_eq with hlt | heq
  · exfalso
    have hleft := valueGap_neg_left hu hum hu' hu'p hF hG hβ hη hr hNo hDo
      ⟨lt_of_le_of_lt haD hlt, htI.2⟩ (h25 t htI) hΦt
    obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hleft
    rw [mem_Iio] at hl
    set x := max ((l + t) / 2) D with hx
    have hxt : x < t := max_lt (by linarith) hlt
    have hlx : l < x := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hxT : x ∈ T := ⟨⟨le_max_right _ _, hxt.le.trans htD'⟩, fun y hy => by
      rcases lt_or_ge y t with h | h
      · exact (hsub ⟨lt_of_lt_of_le hlx hy.1, h⟩).le
      · exact htT.2 y ⟨h, hy.2⟩⟩
    have := csInf_le hTbdd hxT
    linarith
  · rw [heq]; exact hΦt

end ObstfeldRogoff.CapitalMarketImperfections.DebtCeiling
