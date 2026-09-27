# Real exchange rate and the terms of trade in Lean

This is the `RealExchangeRate/` proof project in
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Run the commands below from this directory: `cd RealExchangeRate` from the
repository root. [Return to the library index](../README.md).

A checked formalisation of Obstfeld and Rogoff (1996), *Foundations of
International Macroeconomics*, Chapter 4, “The Real Exchange Rate and the Terms
of Trade” (pp. 199–267), with both appendices and the provable exercises. The
library contains **281 theorems** and audits **367 declarations**.

Headline results, in the namespace `ObstfeldRogoff.RealExchangeRate`:
* **Balassa–Samuelson.** With internationally mobile capital the relative price of
  nontradables is fixed by supply alone (`BalassaSamuelson.supplyEqm_existsUnique`).
  Its log-linear response to productivity and the interest rate is proved as an
  exact derivative of logs (`logPrice_path_hasDerivAt`). The book's sign claims
  hold only with non-negative productivity growth (`bs_price_rises`,
  `bs_sign_counterexample`).
* **The CES price index** is the least cost of a unit of real consumption
  (`CESIndex.cesPrice_isLeast_cost`) and tends to the Cobb–Douglas index as `θ → 1`.
* **The Dornbusch–Fischer–Samuelson model.** A unique specialisation cutoff exists
  (`DFSStatic.cutoff_exists_unique`), with its comparative statics and real-wage
  effects, dynamics after a productivity shock, and transport costs with a
  nontraded band.
* **Costly capital** (Appendix 4B): the linearised dynamics are a saddle for every
  `r, χ > 0` (`CostlyCapital.saddle_point`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for where the printed text is wrong or
imprecise.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Model](RealExchangeRate/Model.lean) | 2 | Cobb–Douglas price index |
| [PriceLevels](RealExchangeRate/PriceLevels.lean) | 6 | Real exchange rate, PPP, law of one price, price-level ratio |
| [CRSProduction](RealExchangeRate/CRSProduction.lean) | 33 | CRS production, capital–labour ratio from Inada, factor-price frontier, zero maximum profit |
| [BalassaSamuelson](RealExchangeRate/BalassaSamuelson.lean) | 36 | Unique supply equilibrium, comparative statics, exact log-derivative (4.8)–(4.9), corrected Balassa–Samuelson and HBS signs |
| [BSExtensions](RealExchangeRate/BSExtensions.lean) | 23 | Three factors, immobile capital, Ex 1, 2, 6 |
| [LongRunGDPGNP](RealExchangeRate/LongRunGDPGNP.lean) | 9 | GDP and GNP lines (4.10)–(4.11), fn 18–19, wealth and the trade balance |
| [ManufacturingEmployment](RealExchangeRate/ManufacturingEmployment.lean) | 7 | (4.12), (4.17)–(4.18): productivity growth and nontradables employment |
| [CESIndex](RealExchangeRate/CESIndex.lean) | 25 | CES index and price index, duality, θ → 1 limits, Ex 8(a) |
| [ConsumptionDynamics](RealExchangeRate/ConsumptionDynamics.lean) | 34 | Consumption-based real rate (4.25)–(4.36), Ex 3, Ex 4 |
| [EndogenousLabour](RealExchangeRate/EndogenousLabour.lean) | 6 | Appendix 4A, Ex 5 |
| [CostlyCapital](RealExchangeRate/CostlyCapital.lean) | 13 | Appendix 4B: short-run equilibrium, steady state, saddle-point stability |
| [DFSStatic](RealExchangeRate/DFSStatic.lean) | 22 | DFS continuum: unique cutoff, comparative statics, real wages |
| [DFSCurrentAccount](RealExchangeRate/DFSCurrentAccount.lean) | 31 | DFS dynamics (4.46)–(4.59), temporary shock, Ex 7 |
| [DFSTransportCosts](RealExchangeRate/DFSTransportCosts.lean) | 26 | Transport costs (4.60)–(4.66), transfer effect, price ratios |
| [DFSPriceIndex](RealExchangeRate/DFSPriceIndex.lean) | 8 | The price index as least cost; the cutoff derivative of P/P* |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
