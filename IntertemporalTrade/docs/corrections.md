# Corrections to the source

Places where a claim in Chapter 1 of Obstfeld and Rogoff (1996) is false,
imprecise, or relies on an unstated hypothesis. In each case the Lean statement
proves the corrected version and cites the original.

## Claims that are wrong or need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| Ex 8(b), p. 58 | At the optimal tax, Foreign's import elasticity satisfies `ζ* > 1`. | The first-order conditions give `MRS = (1 + τ)R = Rζ*/(ζ* − 1) > 0`. That yields `ζ* > 1` **or** `ζ* < 0`; the second case is a strongly backward-bending Foreign import demand with `τ ∈ (−1, 0)`. Proved: `ζ* > 1` given `ζ* ≥ 0` (`OptimalTax.ex8_elasticity_gt_one`), and `ζ* > 1` when Home borrows and Foreign saving slopes up (`OptimalTax.ex8_elasticity_gt_one_of_supply`). Whether `ζ* < 0` can occur at a global planner optimum is not settled. |
| Ex 8, p. 57 | Refers to “section 1.5's model”. | Should be §1.4 (§1.5 is international labour movements). The tax is additive in §1.4, `1 + r^τ + τ`, but ad valorem in Ex 8, `(1 + τ)(1 + r^τ)`; each is formalised in its own form. |
| Ex 5 | For the general model, a rise in `Y₁` or `Y₁*` lowers `r` and a rise in `Y₂` or `Y₂*` raises it. | Not true for general utility without a Walrasian stability or uniqueness hypothesis, which the book does not state (it notes on p. 30 that equilibria can be multiple). Proved for log utility from the closed form: `WorldEquilibrium.logGrossRate_anti_Y1` and its three siblings. |
| §1.3.2, p. 29 | For a lender, `dC₁/dr < 0` “only if `r` is not too far from `r^A`”. | Not a theorem as stated. Proved instead: `dC₁/dr < 0` whenever `C₁ ≥ Y₁` (`Isoelastic.deriv_consC1_neg_of_borrower`). |
| p. 22 | With consumption normal on both dates, a temporary rise in `G₁` gives a deficit and a rise in `G₂` a surplus. | Stronger than needed: the `G₁` result needs only date-2 consumption to be normal, and the `G₂` result only date-1 consumption (`Investment.temporary_G1_deficit`, `Investment.future_G2_surplus`). |
| p. 45 | A small country's optimal tax is zero. | Proved in two senses: exactly, when the foreign offer curve is a straight line (`OptimalTax.small_country_zero_tax`); and as a limit, the tax wedge at a fixed `C₁` tends to zero as Foreign's endowments grow (`OptimalTax.Foreign.tendsto_optimalTax_scale`). The limit along the moving planner optimum is not proved. |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| Throughout | `r > −1`, positive endowments, interior optima. The Inada condition appears only in footnotes 1, 9 and 23. | Explicit hypotheses wherever used. The Inada condition is used only for existence (`Consumer.Household.exists_optimal`, `WorldEquilibrium.exists_equilibrium`); elsewhere interiority is assumed directly. |
| (1.3), p. 3; pp. 9–10 | Uniqueness of the optimum and the Euler characterisation need strict concavity; the trade-pattern and welfare claims use uniqueness. | `Consumer.Household` requires `u` strictly increasing and strictly concave on `(0, ∞)`. The revealed-preference results need nothing more; the strict versions add a derivative `u' > 0`. |
| p. 19 | Fisher separation: uniqueness of `K₂` needs `F` strictly concave; otherwise it is the *set* of profit maximisers that is independent of preferences. | `Investment.fisher_separation` (set version), `Investment.profit_maximizer_unique`. |
| p. 23, Fig. 1.5 | The world rate lies between the autarky rates; the figure assumes upward-sloping saving curves. | Not needed: `WorldEquilibrium.rate_between_autarky` uses only the saving-sign lemma. |
| (1.28)–(1.31), pp. 40–41 | The chain rule in the Slutsky derivation needs the expenditure function and Marshallian demand to be jointly (Fréchet) differentiable; partial derivatives are not enough. | Joint differentiability is a hypothesis of `Duality.ExpenditureSystem.slutsky` and `total_effect`, and is proved for isoelastic utility (`Duality.Iso.hasFDerivAt_C1M`). |
| p. 42 | The isoelastic Hicksian demand formula requires `(1 − 1/σ)U > 0` and `σ ≠ 1`. | The attainable utility set in `Duality.Iso.system`. |
| p. 48 | `k(w)` exists only for wages in the range of `k ↦ f(k) − kf'(k)`; its derivative needs `w` interior to that range. | `LabourMobility.Technology.wageRange`, hypotheses of `hasDerivAt_kOf`. |
| §1.4, p. 43 | The foreign offer curve is defined and concave only where `(1 + β*)(Y₁ − C₁) + β*Y₁* > 0`. | Domain hypothesis of `OptimalTax.Foreign.offer_strictConcaveOn`. |
| Ex 7, p. 57 | CARA utility violates the chapter's standing Inada condition and allows `C < 0`. | Formalised on its own terms; Ex 7(e) needs `C₂ ≠ 0`. |

## Not formalised

* Global uniqueness of the world equilibrium: false in general (the book says so on p. 30).
* Immiserizing growth and “Home investment can fall” (pp. 25, 34): possibility claims with no example given.
* Exercise 6: open-ended comparative statics under a stability hypothesis.
* Heterogeneous agents with side payments (p. 50) and the empirical applications.
* Existence of the tax planner's optimum in §1.4: the results take it as a named hypothesis.
