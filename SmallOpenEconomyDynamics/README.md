# Dynamics of small open economies in Lean

This is the `SmallOpenEconomyDynamics/` proof project in
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Run the commands below from this directory: `cd SmallOpenEconomyDynamics` from the repository
root. [Return to the library index](../README.md).

A checked formalisation of Obstfeld and Rogoff (1996), *Foundations of
International Macroeconomics*, Chapter 2, “Dynamics of Small Open Economies” (pp. 59–128), and the Supplements to Chapter 2, A–C (pp. 715–741).

The infinite-horizon small open economy: the intertemporal budget
constraint and transversality, consumption functions, the fundamental
current-account equation, Hall's random walk and the present-value test of the
current account, durables, firms and asset pricing, Tobin's q, trend growth,
and the supporting methods of Supplements A–C (intertemporal optimisation,
nonadditive preferences, linear difference equations).

**Status: phase 0 scaffold.** The library currently contains **1 theorem**,
the model primitives the chapter builds on. The planned modules are listed
below. See the [source map](docs/source-map.md) for the correspondence with the
book, and [corrections](docs/corrections.md) for the places where a printed
claim is false or imprecise and the Lean statement differs.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Model](SmallOpenEconomyDynamics/Model.lean) | 1 | Many-period economy, current account (2.2), period constraint forms (2.2) ⇔ (2.3) |

## Planned modules

| Module | Contents |
| --- | --- |
| PresentValue | Summable-guarded present values, permanent value (2.17), recursion + tail → 0 ⇒ PV identity, Σ R_{t,s} r_s = 1 |
| BudgetConstraint | Finite IBC (2.4), (2.2) + (2.13) ⇔ (2.14), no-Ponzi inequality, solvency, naive limit (2.12), Ex 1 |
| ConsumptionOptimality | Euler necessity, sufficiency under concavity, tilt, uniqueness, SA.1, dynamic consistency, Strotz, Ex 2 |
| ConsumptionFunctions | (2.9), (2.10), CRRA (2.15)–(2.16), fn 8, SA.2 closed form, endogenous labour |
| FundamentalCurrentAccount | (2.18), (2.20), variable rates (2.25)–(2.26) |
| StochasticConsumption | Hall martingale (2.31), certainty equivalence (2.32), AR(1) (2.33)–(2.38), (2.40), precautionary saving, Ex 3, Ex 4 |
| PresentValueTest | Campbell (2.43), Ex 5, Ex 6, VAR forecast (2.45) |
| Durables | User cost (2.47), (2.48)–(2.51) |
| FirmsAndWealth | Asset pricing (2.53)–(2.57), V = K (2.59), (2.60)–(2.61), Modigliani–Miller |
| TobinQ | (2.63)–(2.67), corrected (2.65), saddle path, marginal q = average q (2.70), Ex 9 |
| LinearDifferenceEquations | Supplement C: scalar and 2×2 systems, saddle solutions |
| TrendGrowth | Appendix 2A (2.74)–(2.77), Appendix 2B (2.78), Supplement B steady state |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
