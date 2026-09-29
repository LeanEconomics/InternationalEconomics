# International financial markets under uncertainty in Lean

This is the `InternationalFinancialMarkets/` proof project in
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Run the commands below from this directory: `cd InternationalFinancialMarkets` from the repository
root. [Return to the library index](../README.md).

A checked formalisation of Obstfeld and Rogoff (1996), *Foundations of
International Macroeconomics*, Chapter 5, “Uncertainty and International
Financial Markets” (pp. 269–348), with its appendices, the Supplement to
Chapter 5 (pp. 742–744) and the provable exercises. Uncertainty is a finite set
of states, so expectations are finite sums. The library contains
**503 theorems** and audits **715 declarations**.

Headline results, in the namespace `ObstfeldRogoff.InternationalFinancialMarkets`:
* **Complete markets for a small country.** Full insurance iff prices are
  actuarially fair (`SmallCountry.full_insurance_iff_fair`); no arbitrage iff
  `Σ p = 1` and `p ≥ 0`; comparative advantage for arbitrary transitive, locally
  non-satiated preferences (`ComparativeAdvantage.comparative_advantage`).
* **Global risk sharing.** Consumption shares are constant across states and equal
  wealth shares, and the equilibrium solves a planner's problem
  (`GlobalEquilibrium.GlobalEqm.planner_optimal`).
* **Spanning.** Markets span iff the return matrix has rank `S`
  (`Spanning.spans_iff_rank`); the book's `S ≤ N+1` criterion is neither sufficient
  nor necessary for efficiency (`card_le_not_sufficient`, `efficient_without_spanning`).
* **Asset pricing.** The consumption CAPM, the Hansen–Jagannathan bound, and
  Lucas's welfare cost of consumption variability, which simplifies exactly to
  `exp(ρV/2) − 1` (`AssetPricing.lucas_tau_simplifies`).
* **Infinite-horizon asset pricing on an event tree.** The price is the present-value
  series iff there is no bubble; bounded prices are unique
  (`InfiniteHorizonPricing.price_eq_fundamental_iff`, `unique_bounded_price`).
* **Event trees.** Arrow–Debreu equilibrium over an infinite horizon, constant CRRA
  shares, and dynamic consistency (`EventTree.crra_equilibrium_infinite`,
  `dynamic_consistency_infinite`).
* **Consumption and portfolio choice** (the Supplement). The Bellman equation is
  solved exactly, an optimal portfolio exists under no arbitrage, and `C = μW` is
  optimal over the infinite horizon, also with history-dependent returns
  (`ConsumptionPortfolio.verification_crra_of_noArbitrage`, `verification_varying_returns`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for where the printed text is wrong or
imprecise.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Model](InternationalFinancialMarkets/Model.lean) | 2 | Finite state space, expectations |
| [Probability](InternationalFinancialMarkets/Probability.lean) | 16 | Covariance, variance, correlation, Cauchy–Schwarz |
| [SmallCountry](InternationalFinancialMarkets/SmallCountry.lean) | 54 | §5.1: AD securities, no arbitrage, first-order conditions necessary and sufficient, full insurance, CRRA and log demands; Appendix 5B; Ex 1, 3 |
| [ComparativeAdvantage](InternationalFinancialMarkets/ComparativeAdvantage.lean) | 6 | §5.1.7: Walras's law, revealed preference, comparative advantage |
| [TwoStageBudgeting](InternationalFinancialMarkets/TwoStageBudgeting.lean) | 46 | §5.1.8: CES risk index, `P ≤ 1`, stage-1 and stage-2 optimality, Epstein–Zin (26), the current account |
| [GlobalEquilibrium](InternationalFinancialMarkets/GlobalEquilibrium.lean) | 41 | §5.2: world prices, risk sharing, planner, investment; Ex 2 |
| [Aggregation](InternationalFinancialMarkets/Aggregation.lean) | 6 | §5.2.3: HARA and geometric aggregation |
| [PortfolioDiversification](InternationalFinancialMarkets/PortfolioDiversification.lean) | 33 | §5.3: bonds and shares replicate complete markets; Ex 4, 5 |
| [Spanning](InternationalFinancialMarkets/Spanning.lean) | 13 | Appendix 5A: spanning and rank |
| [AssetPricing](InternationalFinancialMarkets/AssetPricing.lean) | 29 | §5.4: CCAPM, Hansen–Jagannathan, equity premium; Lucas's welfare cost |
| [Nontradables](InternationalFinancialMarkets/Nontradables.lean) | 22 | §5.5: efficiency in tradables, CES–CRRA, home bias |
| [EventTree](InternationalFinancialMarkets/EventTree.lean) | 57 | Appendices 5C–5D over an infinite horizon: optimality, CRRA and log equilibria, dynamic consistency |
| [ConsumptionPortfolio](InternationalFinancialMarkets/ConsumptionPortfolio.lean) | 95 | Supplement: portfolio condition, existence, Bellman equation, verification (i.i.d. and history-dependent returns) |
| [InfiniteHorizonPricing](InternationalFinancialMarkets/InfiniteHorizonPricing.lean) | 70 | §5.4.3 stochastic (59)–(61), bubbles; Ex 3(a), Ex 6 over an infinite horizon |
| [OLGRiskSharing](InternationalFinancialMarkets/OLGRiskSharing.lean) | 13 | §5.6; Ex 6 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
