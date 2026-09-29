# Sticky-price models in Lean

This is the `StickyPriceModels/` proof project in
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Run the commands below from this directory: `cd StickyPriceModels` from the repository
root. [Return to the library index](../README.md).

A checked formalisation of Obstfeld and Rogoff (1996), *Foundations of
International Macroeconomics*, Chapter 10, “Sticky-Price Models of Output, the
Exchange Rate, and the Current Account” (pp. 659–714), with the exercises. The
library contains **597 theorems** and audits **1023 declarations**.

Headline results, in the namespace `ObstfeldRogoff.StickyPriceModels`:
* **The two-country model.** Household optimality over a genuine infinite horizon; the
  steady state exists and is unique for every asset position; the log-linear system is
  exactly the derivative of the nonlinear steady-state map; no overshooting, exactly
  (`ReduxPrimitives.HouseholdEnv.isOptimal_iff`, `ReduxSteadyState.exists_unique_steady`,
  `ReduxLinearisationLink.linearisation_link_system`, `ReduxMoneyShocks.no_overshooting_exact`).
* **Welfare.** The exact threshold behind “`χ` not too large”, with a counterexample; closed
  forms for productivity and government spending (`ReduxWelfare.foreign_shock_welfare_pos_iff`,
  `ReduxFiscalProductivity.productivity_welfare`).
* **Nontradables.** Overshooting iff `ε > 1` in the exact nonlinear model, with (99) as its
  derivative (`NontradablesOvershooting.overshoot_iff`, `hasDerivAt_impact`).
* **Pricing to market.** The markup rule, the law of one price iff equal elasticities, and
  pass-through below one half with linear demand (`PassThrough.ptm_loop_iff`,
  `lin_passThrough_bounds`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for where the printed text is wrong or
imprecise.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Model](StickyPriceModels/Model.lean) | 2 | CES demand for a differentiated good |
| [ReduxPrimitives](StickyPriceModels/ReduxPrimitives.lean) | 77 | §10.1.1–10.1.4: CES duality, the household problem, aggregation |
| [ReduxSteadyState](StickyPriceModels/ReduxSteadyState.lean) | 59 | §10.1.4–10.1.6: steady-state existence and uniqueness, the planner, flexible prices |
| [ReduxLogLinear](StickyPriceModels/ReduxLogLinear.lean) | 24 | §10.1.5–10.1.7: the log-linear system as exact derivatives |
| [ReduxMoneyShocks](StickyPriceModels/ReduxMoneyShocks.lean) | 47 | §10.1.7–10.1.8: money shocks, no overshooting, equiproportionate shocks; Ex 1 |
| [ReduxWelfare](StickyPriceModels/ReduxWelfare.lean) | 49 | §10.1.8: welfare, the χ threshold, menu costs, taxes; Ex 3 |
| [ReduxFiscalProductivity](StickyPriceModels/ReduxFiscalProductivity.lean) | 32 | §10.3: productivity and government spending |
| [ReduxPresetWages](StickyPriceModels/ReduxPresetWages.lean) | 20 | §10.4.2: two-country preset wages, (144) |
| [ReduxLinearisationLink](StickyPriceModels/ReduxLinearisationLink.lean) | 32 | The linear system as the derivative of the steady-state map |
| [NontradablesModel](StickyPriceModels/NontradablesModel.lean) | 59 | §10.2.1–10.2.3: the small open economy with nontradables |
| [NontradablesOvershooting](StickyPriceModels/NontradablesOvershooting.lean) | 56 | §10.2.4: exact overshooting, welfare; Ex 2 |
| [PresetWagesSmallCountry](StickyPriceModels/PresetWagesSmallCountry.lean) | 21 | §10.4.1: preset wages in the small country |
| [CashInAdvanceCredibility](StickyPriceModels/CashInAdvanceCredibility.lean) | 27 | Ex 4: cash in advance and credibility |
| [PassThrough](StickyPriceModels/PassThrough.lean) | 58 | §10.4.2: pricing to market and pass-through |
| [StickyPriceEvidence](StickyPriceModels/StickyPriceEvidence.lean) | 34 | Boxes 10.1–10.2, the p. 694 regression, Table 10.1 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
