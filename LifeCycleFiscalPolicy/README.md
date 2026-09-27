# Life-cycle fiscal policy and the current account in Lean

This is the `LifeCycleFiscalPolicy/` proof project in
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Run the commands below from this directory: `cd LifeCycleFiscalPolicy` from the repository
root. [Return to the library index](../README.md).

A checked formalisation of Obstfeld and Rogoff (1996), *Foundations of
International Macroeconomics*, Chapter 3, “The Life Cycle, Tax Policy, and the
Current Account” (pp. 129–197), including its appendix and the provable
exercises. The library contains **288 theorems** and audits **365
declarations**.

Headline results, in the namespace `ObstfeldRogoff.LifeCycleFiscalPolicy`:
* **Ricardian equivalence and its failure.** With infinitely lived consumers the tax
  path and the split of assets between private and public sectors are irrelevant
  (`RicardianEquivalence.privatePVSet_eq_of_government_ibc`). With overlapping
  generations aggregate consumption depends on the youth tax and on government
  assets (`TwoPeriodOLG.consumption_depends_on_youth_tax`). In Weil's model debt is
  net wealth iff the population grows (`PerpetualYouth.weil_ricardian_iff`).
* **Barro altruism.** Bequests offset a transfer one-for-one when they are interior
  (`RicardianEquivalence.interior_bequest_neutrality`). Gale's point that the
  dynastic recursion does not pin down utility is made exact
  (`RicardianEquivalence.gale_solutions_differ`).
* **The two-country OLG model.** Global monotone convergence, argued in the book only
  from a figure (`TwoCountryOLG.TwoCountry.psi_global_convergence`). With public
  debt: at most two steady states, the upper one stable, debt crowding out capital
  in both countries, and a debt threshold beyond which no steady state exists
  (`no_steady_state_of_large_debt`).
* **Dynamic inefficiency.** When `r̄ < z`, a feasible reallocation raises consumption at
  every date (`DynamicInefficiency.pareto_improvement_of_dynamically_inefficient`).
* **Tax smoothing.** Constant taxes are uniquely optimal (`TaxSmoothing.constant_tax_optimal`).

See the [source map](docs/source-map.md) for the correspondence with the book.
[Corrections](docs/corrections.md) records where the printed text is wrong or
imprecise. Most notably, Exercise 2(b)'s claim that opening a dynamically
inefficient economy to trade makes everyone worse off is false, because the young
gain at low enough world rates. The corrected local statement is proved.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Model](LifeCycleFiscalPolicy/Model.lean) | 2 | Log-utility OLG demands (3.12)–(3.13), budget (3.10), Euler (3.11) |
| [RicardianEquivalence](LifeCycleFiscalPolicy/RicardianEquivalence.lean) | 41 | §3.1 two-period and infinite-horizon Ricardian equivalence; Barro altruism, Gale's non-uniqueness, bequest neutrality and its failure |
| [TwoPeriodOLG](LifeCycleFiscalPolicy/TwoPeriodOLG.lean) | 12 | Failure of Ricardian equivalence, saving accounting (3.17)–(3.23), generational accounting (Box 3.1) |
| [DeficitTransfer](LifeCycleFiscalPolicy/DeficitTransfer.lean) | 20 | Debt-financed transfer (3.24)–(3.32), fn 9–10, balanced transfers, transitory shocks |
| [DemographicsSaving](LifeCycleFiscalPolicy/DemographicsSaving.lean) | 16 | Growth, demographics and saving (3.33), Ex 1 |
| [SmallOpenDiamond](LifeCycleFiscalPolicy/SmallOpenDiamond.lean) | 33 | Small open Diamond economy (3.34)–(3.46), factor-price frontier, comparative statics |
| [OLGGainsFromTrade](LifeCycleFiscalPolicy/OLGGainsFromTrade.lean) | 29 | (3.47), compensation, open-economy gains, Ex 2(a), refutation and correction of Ex 2(b) |
| [TwoCountryOLG](LifeCycleFiscalPolicy/TwoCountryOLG.lean) | 48 | Global stability (3.52), debt map, steady-state existence threshold, crowding out, r ≤ n, Ex 4 |
| [PerpetualYouth](LifeCycleFiscalPolicy/PerpetualYouth.lean) | 64 | Weil aggregation (3.64)–(3.68), dynamics (3.69)–(3.73), debt as net wealth, Ex 3 (Blanchard), Ex 5 |
| [DynamicInefficiency](LifeCycleFiscalPolicy/DynamicInefficiency.lean) | 14 | Golden rule, Pareto improvement when r < z, Ponzi games, bubbles, profit-share criterion |
| [TaxSmoothing](LifeCycleFiscalPolicy/TaxSmoothing.lean) | 9 | Ex 6: Barro tax smoothing |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
