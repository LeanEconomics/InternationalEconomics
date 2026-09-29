/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InternationalFinancialMarkets.PortfolioDiversification
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Spanning and completeness

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, Appendix 5A,
pp. 335–337, the spanning discussion on p. 304, and equation (7), p. 273.

`R` is the `S × (N + 1)` matrix of gross ex post returns (one column per asset: the riskless
bond and the `N` country funds). A portfolio `a` (amounts invested in each asset) pays
`R a` across states.

* The spanning condition (77), `rank R = S`, holds iff every state-contingent payoff is
  attainable; for square invertible `R` the Arrow–Debreu securities are `R⁻¹ 1ₛ`.
* `rank R ≤ min(S, N + 1)`, so spanning requires `S ≤ N + 1`; with more states than assets
  it fails.
* With linear (Arrow–Debreu) pricing of assets, attainable consumption plans are budget
  feasible; under spanning the attainable set *equals* the complete-markets budget set, and
  the Arrow–Debreu prices are uniquely determined by asset prices.
* The book's "Pareto efficiency can be ensured only when `S ≤ N + 1`" (p. 304) is imprecise:
  `S ≤ N + 1` is necessary for spanning but not sufficient (explicit counterexample), and it
  is not necessary for efficiency — the CRRA equilibrium of §5.3.2 is efficient for any `S`.
* Bond redundancy (7): the bond is replicated by `1 + r` units of every Arrow–Debreu security,
  so no arbitrage forces `Σ p(s) = 1`.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.Spanning

open Matrix Finset

variable {S A : Type} [Fintype S] [Fintype A]

/-- **The spanning condition**, O&R (77), p. 336: `rank R = S` iff every payoff vector
`c : S → ℝ` is attained by some portfolio, `R a = c`. -/
theorem spans_iff_rank (R : Matrix S A ℝ) :
    Function.Surjective R.mulVec ↔ R.rank = Fintype.card S := by
  have hsurj : Function.Surjective R.mulVec ↔ LinearMap.range R.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]; rfl
  rw [hsurj, Matrix.rank]
  constructor
  · intro h
    rw [h, finrank_top, Module.finrank_fintype_fun_eq_card]
  · intro h
    exact Submodule.eq_top_of_finrank_eq (h.trans (Module.finrank_fintype_fun_eq_card ℝ).symm)

/-- **The rank bound**, O&R p. 336: `rank R ≤ min(S, N + 1)`. -/
theorem rank_le_min (R : Matrix S A ℝ) :
    R.rank ≤ min (Fintype.card S) (Fintype.card A) :=
  le_min (Matrix.rank_le_card_height R) (Matrix.rank_le_card_width R)

/-- **Spanning needs at least as many assets as states**, O&R p. 336: if every payoff is
attainable then `S ≤ N + 1`. -/
theorem card_le_of_spans {R : Matrix S A ℝ} (h : Function.Surjective R.mulVec) :
    Fintype.card S ≤ Fintype.card A := by
  rw [← (spans_iff_rank R).1 h]
  exact Matrix.rank_le_card_width R

/-- **With more states than assets spanning fails**, O&R p. 336 ("(77) couldn't possibly hold
were `N + 1 < S`"): some state-contingent payoff is not attainable. -/
theorem not_spans_of_card_lt {R : Matrix S A ℝ} (h : Fintype.card A < Fintype.card S) :
    ¬ Function.Surjective R.mulVec := fun hs => absurd (card_le_of_spans hs) (not_le.2 h)

/-- **Synthesising Arrow–Debreu securities**, O&R p. 336: if the square return matrix is
invertible, the portfolio `aₛ = R⁻¹1ₛ` pays one unit in state `s` and nothing otherwise. -/
theorem ad_security_replication [DecidableEq S] {R : Matrix S S ℝ} (h : IsUnit R.det)
    (s : S) : R *ᵥ (R⁻¹ *ᵥ Pi.single s 1) = Pi.single s 1 := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv R h, Matrix.one_mulVec]

/-- For a square return matrix, spanning is equivalent to invertibility, O&R p. 336. -/
theorem spans_iff_isUnit_det [DecidableEq S] (R : Matrix S S ℝ) :
    Function.Surjective R.mulVec ↔ IsUnit R.det := by
  rw [Matrix.mulVec_surjective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]

/-- **`S ≤ N + 1` is not sufficient for spanning**, correcting O&R p. 304: with two states
and two assets — the bond with gross return `1 + r = 2` and a fund whose gross return is also
`2` in both states (a riskless country output) — the return matrix has rank one and the
Arrow–Debreu security for state 0 cannot be synthesised. -/
theorem card_le_not_sufficient :
    ∃ R : Matrix (Fin 2) (Fin 2) ℝ, Fintype.card (Fin 2) ≤ Fintype.card (Fin 2) ∧
      ¬ Function.Surjective R.mulVec := by
  refine ⟨Matrix.of fun _ _ => 2, le_refl _, fun h => ?_⟩
  obtain ⟨a, ha⟩ := h (Pi.single 0 1)
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  linarith

/-- The cost of every asset per unit invested is one; asset prices are linear in
Arrow–Debreu prices `q` when `Σ_s q(s) R(s, j) = 1` for every asset `j` (O&R §5.4.1.1 and
p. 336). -/
def LinearPricing (q : S → ℝ) (R : Matrix S A ℝ) : Prop := ∀ j, ∑ s, q s * R s j = 1

/-- **Attainable plans are budget feasible**: under linear pricing, a portfolio costing
`Σ_j a(j)` finances a payoff with Arrow–Debreu value `Σ_s q(s)(Ra)(s) = Σ_j a(j)`. -/
theorem value_of_payoff {q : S → ℝ} {R : Matrix S A ℝ} (hq : LinearPricing q R) (a : A → ℝ) :
    ∑ s, q s * (R *ᵥ a) s = ∑ j, a j := by
  have h := Matrix.dotProduct_mulVec q R a
  simp only [dotProduct] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (q ᵥ* R) j = 1 := hq j
  rw [this, one_mul]

/-- **Spanning makes asset markets complete**, O&R Appendix 5A, p. 336: under spanning and
linear pricing, the set of payoffs attainable with wealth `w`,
`{c | ∃ a, Ra = c, Σ_j a(j) = w}`, equals the complete-markets budget set
`{c | Σ_s q(s)c(s) = w}`. -/
theorem attainable_eq_budget {q : S → ℝ} {R : Matrix S A ℝ} (hq : LinearPricing q R)
    (hs : Function.Surjective R.mulVec) (w : ℝ) :
    {c : S → ℝ | ∃ a : A → ℝ, R *ᵥ a = c ∧ ∑ j, a j = w} =
      {c : S → ℝ | ∑ s, q s * c s = w} := by
  ext c
  constructor
  · rintro ⟨a, rfl, hw⟩
    change ∑ s, q s * (R *ᵥ a) s = w
    rw [value_of_payoff hq, hw]
  · intro hc
    obtain ⟨a, ha⟩ := hs c
    refine ⟨a, ha, ?_⟩
    change ∑ s, q s * c s = w at hc
    rw [← value_of_payoff hq, ha, hc]

/-- **Arrow–Debreu prices are pinned down under spanning**: two state-price vectors that both
price all assets linearly coincide when `R` spans. -/
theorem pricing_unique {q q' : S → ℝ} {R : Matrix S A ℝ} (hq : LinearPricing q R)
    (hq' : LinearPricing q' R) (hs : Function.Surjective R.mulVec) : q = q' := by
  classical
  funext s
  obtain ⟨a, ha⟩ := hs (Pi.single s 1)
  have h1 := value_of_payoff hq a
  have h2 := value_of_payoff hq' a
  rw [ha] at h1 h2
  simpa [Pi.single_apply] using h1.trans h2.symm

/-- **Bond redundancy**, O&R (7), p. 273: with a full set of Arrow–Debreu securities (payoff
matrix the identity, which spans), the bond's payoff `1 + r` in every state is replicated by
`1 + r` units of every Arrow–Debreu security, whose cost at prices `p(s)/(1 + r)` is `Σ_s p(s)`;
the law of one price (bond price `1`) therefore forces `Σ_s p(s) = 1`. -/
theorem bond_redundant [DecidableEq S] {p : S → ℝ} {r : ℝ} (hr : 1 + r ≠ 0) :
    Function.Surjective (1 : Matrix S S ℝ).mulVec ∧
      (1 : Matrix S S ℝ) *ᵥ (fun _ => 1 + r) = (fun _ => 1 + r) ∧
      ∑ s, p s / (1 + r) * (1 + r) = ∑ s, p s := by
  refine ⟨fun c => ⟨c, Matrix.one_mulVec c⟩, Matrix.one_mulVec _, ?_⟩
  exact Finset.sum_congr rfl fun s _ => div_mul_cancel₀ _ hr

/-! ## Spanning is not necessary for efficiency -/

/-- The gross-return matrix of the §5.3 economy, O&R p. 336: the bond column pays `1 + r`,
and country `m`'s column pays `1 + rᵐ(s) = Y₂ᵐ(s)/V₁ᵐ`. -/
noncomputable def returnMatrix {ι : Type} (r : ℝ) (V : ι → ℝ) (Y2 : ι → S → ℝ) :
    Matrix S (Option ι) ℝ :=
  Matrix.of fun s j => Option.elim j (1 + r) fun m => Y2 m s / V m

omit [Fintype S] in
/-- The payoff of a portfolio in the §5.3 economy, O&R p. 336: investing `a₀` in bonds and
`aₘ` in country `m`'s fund (a share `aₘ/V₁ᵐ` of its output) pays
`(1 + r)a₀ + Σₘ (aₘ/V₁ᵐ) Y₂ᵐ(s)`. -/
theorem returnMatrix_mulVec {ι : Type} [Fintype ι] (r : ℝ) (V : ι → ℝ) (Y2 : ι → S → ℝ)
    (a : Option ι → ℝ) (s : S) :
    (returnMatrix r V Y2 *ᵥ a) s = (1 + r) * a none + ∑ m, a (some m) / V m * Y2 m s := by
  simp only [Matrix.mulVec, dotProduct, returnMatrix, Matrix.of_apply, Fintype.sum_option,
    Option.elim]
  exact congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun m _ => by ring)

/-- **Efficiency without spanning**, O&R §5.3.3 (p. 303) versus p. 304: in the CRRA economy
of §5.3.2 with more states than assets (`S > N + 1`), bonds and shares cannot span the
state space — some payoffs are unattainable — yet the equilibrium allocation satisfies all
the complete-markets Euler equations at the Arrow–Debreu prices (30) (and the complete-markets
budget constraints, `PortfolioEconomy.ad_budget`). So `S ≤ N + 1` is not necessary for
Pareto efficiency. -/
theorem efficient_without_spanning {ι : Type} [Fintype ι]
    (P : PortfolioDiversification.PortfolioEconomy ι S)
    (hS : Fintype.card ι + 1 < Fintype.card S) :
    ¬ Function.Surjective (returnMatrix P.R P.V P.Y2).mulVec ∧
      ∀ n s, PortfolioDiversification.adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s * P.C1 n ^ (-P.ρ) =
        P.Ω.prob s * P.β * P.C2 n s ^ (-P.ρ) := by
  refine ⟨not_spans_of_card_lt ?_, fun n s => P.ad_euler n s⟩
  rw [Fintype.card_option]
  exact hS

end ObstfeldRogoff.InternationalFinancialMarkets.Spanning
