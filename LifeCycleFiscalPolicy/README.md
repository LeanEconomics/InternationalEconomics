# Life-cycle fiscal policy and the current account in Lean

This is the `LifeCycleFiscalPolicy/` proof project in
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Run the commands below from this directory: `cd LifeCycleFiscalPolicy` from the repository
root. [Return to the library index](../README.md).

A checked formalisation of Obstfeld and Rogoff (1996), *Foundations of
International Macroeconomics*, Chapter 3, “The Life Cycle, Tax Policy, and the Current Account” (pp. 129–197).

Ricardian equivalence and its failure with overlapping generations:
deficits in the two-period OLG economy, demographics and saving, the small open
and two-country Diamond models, gains from trade across generations, public debt
and the world interest rate, Weil's infinitely lived vintages, and dynamic
inefficiency.

**Status: phase 0 scaffold.** The library currently contains **2 theorems**,
the model primitives the chapter builds on. The planned modules are listed
below. See the [source map](docs/source-map.md) for the correspondence with the
book, and [corrections](docs/corrections.md) for the places where a printed
claim is false or imprecise and the Lean statement differs.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Model](LifeCycleFiscalPolicy/Model.lean) | 2 | Log-utility two-period OLG demands (3.12)–(3.13), budget (3.10), Euler (3.11) |

## Planned modules

| Module | Contents |
| --- | --- |
| RicardianEquivalence | §3.1 two-period and infinite-horizon versions, Barro altruism (3.56)–(3.60), Gale non-uniqueness |
| TwoPeriodOLG | (3.9)–(3.23), failure of Ricardian equivalence, Box 3.1 generational accounts |
| DeficitTransfer | Debt-financed transfer (3.24)–(3.32), transitory shocks |
| DemographicsSaving | Growth and saving, (3.33), fn 24–25, Ex 1 |
| SmallOpenDiamond | Factor prices (3.36)–(3.39), factor-price frontier, (3.40)–(3.46) |
| OLGGainsFromTrade | (3.47), aggregate compensation, open-economy variant, Ex 2(a), corrected Ex 2(b) |
| TwoCountryOLG | (3.52)–(3.53) global stability, debt map with existence under a small-debt bound, crowding out |
| PerpetualYouth | Weil aggregation (3.64)–(3.68), dynamics (3.69)–(3.73), debt is net wealth iff n > 0 (3.74)–(3.75), Ex 3, Ex 5 |
| DynamicInefficiency | Golden rule (3.77)–(3.78), Pareto improvement when f′(k̄) < z, Ponzi and bubble lemmas |
| TaxSmoothing | Ex 6, Barro tax smoothing |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
