# Dynamics of small open economies in Lean

This is the `SmallOpenEconomyDynamics/` proof project in
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Run the commands below from this directory: `cd SmallOpenEconomyDynamics` from the repository
root. [Return to the library index](../README.md).

A checked formalisation of Obstfeld and Rogoff (1996), *Foundations of
International Macroeconomics*, Chapter 2, “Dynamics of Small Open Economies”
(pp. 59–128), and the Supplements to Chapter 2, A–C (pp. 715–741).

The library contains **379 theorems** and audits **441 declarations**, covering
the whole chapter, its appendices, Supplements A–C and the provable exercises.
Probability uses Mathlib's conditional expectation with respect to a filtration.

Headline results, in the namespace `ObstfeldRogoff.SmallOpenEconomyDynamics`:
* **The intertemporal budget constraint.** The period constraints plus the
  transversality condition are equivalent to the intertemporal budget constraint,
  O&R (2.13) ⇔ (2.14) (`BudgetConstraint.transversality_iff_ibc`). A single
  discounted-telescoping lemma underlies this and the asset-pricing forward
  solution (`PresentValue.discounted_tendsto_zero_iff`,
  `PresentValue.forward_solution_iff`).
* **Optimal consumption without assuming an optimum exists.** With concave
  utility, the Euler equation plus a binding budget constraint is sufficient
  (`ConsumptionOptimality.isOptimal_of_euler`); at an optimum both are necessary
  (`pv_eq_of_optimal`, `euler_of_optimal`). The CRRA path is optimal exactly when
  `(1 + r)^{σ−1}β^σ < 1` (`ConsumptionFunctions.crra_isOptimal`,
  `crra_no_optimum`).
* **The fundamental current-account equation**
  `CA = (Y − Ỹ) − (I − Ĩ) − (G − G̃)`, O&R (2.18), with its tilted and
  variable-rate forms (`FundamentalCurrentAccount.fundamental_current_account`).
* **Uncertainty.** Hall's random walk: with quadratic utility consumption is a
  martingale (`StochasticConsumption.hall_martingale`). Campbell's present-value
  form of the current account, with the interchange of conditional expectation and
  infinite sum proved rather than assumed (`PresentValueTest.Stochastic.campbell_eq_43`).
* **Tobin's q.** The saddle-path theorem: real roots `0 < ω₂ < 1 < ω₁`, and the
  saddle path is the unique bounded solution (`TobinQ.omega_saddle`,
  `TobinQ.saddle_path_unique`). Marginal q equals average q
  (`TobinQ.marginal_q_eq_average_q`).

See the [source map](docs/source-map.md) for the correspondence with the book.
[Corrections](docs/corrections.md) records where the printed text is wrong. Most
notably, the forward solution (2.65) for `q` has an index error: as printed it
sums to `q_{t+1}`, not `q_t`. Exercise 5's Campbell test is not an equivalence
without a no-bubble condition. And Exercise 1(b)'s “for any `ξ > 0`” fails for
`ξ ≥ 2 + 2/r`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Model](SmallOpenEconomyDynamics/Model.lean) | 1 | Many-period economy, current account (2.2), period-constraint forms (2.2) ⇔ (2.3) |
| [PresentValue](SmallOpenEconomyDynamics/PresentValue.lean) | 31 | Discounted telescoping, transversality ⇔ IBC, no-Ponzi, forward solution and bubbles, permanent value (2.17), geometric sums, growth below `r`, variable rates and fn 13 |
| [BudgetConstraint](SmallOpenEconomyDynamics/BudgetConstraint.lean) | 32 | (2.4), (2.13) ⇔ (2.14), no-Ponzi, debt limit, trade-surplus solvency, steady debt ratio, naive limit (2.12), Ex 1 |
| [ConsumptionOptimality](SmallOpenEconomyDynamics/ConsumptionOptimality.lean) | 15 | Euler sufficiency and strict optimality, binding budget, Euler necessity, tilt, dynamic consistency, Strotz |
| [FundamentalCurrentAccount](SmallOpenEconomyDynamics/FundamentalCurrentAccount.lean) | 12 | (2.10), fundamental equation (2.18), permanent vs temporary shocks, tilted (2.20) and variable-rate (2.26) forms |
| [ConsumptionFunctions](SmallOpenEconomyDynamics/ConsumptionFunctions.lean) | 30 | (2.9), fn 2, CRRA (2.15)–(2.16) optimality and non-existence, fn 8, CRRA Bellman fixed point (SA.2), endogenous labour, Ex 2 |
| [StochasticConsumption](SmallOpenEconomyDynamics/StochasticConsumption.lean) | 44 | Hall martingale (2.31), certainty equivalence (2.32), AR(1) and nonstationary output (2.33)–(2.38), risky capital (2.40), precautionary saving, SA.3, Ex 3, Ex 4 |
| [PresentValueTest](SmallOpenEconomyDynamics/PresentValueTest.lean) | 35 | Campbell (2.43) with the expectation–sum interchange proved, corrected Ex 5, Ex 6, VAR forecast (2.45), fn 29 |
| [Durables](SmallOpenEconomyDynamics/Durables.lean) | 22 | Euler equations, user cost (2.47), durables budget (2.48), (2.49)–(2.51) |
| [FirmsAndWealth](SmallOpenEconomyDynamics/FirmsAndWealth.lean) | 33 | Share arbitrage (2.53), (2.55)–(2.57), firm FOCs (2.58), V = K (2.59), (2.60)–(2.61), Modigliani–Miller, Appendix 2B |
| [LinearDifferenceEquations](SmallOpenEconomyDynamics/LinearDifferenceEquations.lean) | 56 | Supplement C: scalar backward/forward solutions and bubble-free uniqueness, 2×2 diagonalisation, steady state, saddle-path existence and uniqueness, companion form |
| [TobinQ](SmallOpenEconomyDynamics/TobinQ.lean) | 45 | (2.62)–(2.70): FOCs, corrected forward solution, exact dynamics, linearisation, saddle-path theorem, marginal = average q, bubbles, Ex 9 |
| [TrendGrowth](SmallOpenEconomyDynamics/TrendGrowth.lean) | 23 | Appendix 2A: (2.74)–(2.77), convergence and divergence of the debt ratio, the book's numbers; Supplement B steady state |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
