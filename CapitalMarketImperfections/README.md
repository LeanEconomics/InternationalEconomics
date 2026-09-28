# Imperfections in international capital markets in Lean

This is the `CapitalMarketImperfections/` proof project in
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Run the commands below from this directory: `cd CapitalMarketImperfections` from the repository
root. [Return to the library index](../README.md).

A checked formalisation of Obstfeld and Rogoff (1996), *Foundations of
International Macroeconomics*, Chapter 6, “Imperfections in International
Capital Markets” (pp. 349–428), with Appendices 6A–6B and the provable
exercises. The library contains **738 theorems** and audits **1021 declarations**.

Headline results, in the namespace `ObstfeldRogoff.CapitalMarketImperfections`:
* **Optimal contracts under sovereign risk.** With direct sanctions the optimal
  incentive-compatible contract is `C = max(c̄, (1−η)Y)` for every utility function,
  with and without saving (`DirectSanctionsInsurance.optimal_ic_contract`,
  `SanctionsWithSaving.optimal_saving_contract`).
* **Reputation.** Default is a stopping time on an infinite tree; trigger strategies
  are subgame perfect iff the sustainability condition holds
  (`ReputationTrigger.Trigger.trigger_iff`, `SubgamePerfection.triggerSPE_iff`).
* **Bulow–Rogoff** on a general event tree, and **Worrall convergence** with a geometric
  rate (`BulowRogoff.Theorem.bulow_rogoff`, `Worrall.prob_below_steady_state_tendsto`).
* **Debt and investment.** The debt ceiling, debt overhang without calculus, an explicit
  declining Laffer curve, and Rubinstein bargaining with a unique equilibrium
  (`DebtOverhangLaffer.investment_antitone`, `example_laffer_declines`,
  `SovereignBargaining.rubinstein_exists_unique`).
* **Private information.** The optimal hidden-information contract exists and is unique;
  with moral hazard the two-country equilibrium exists and is unique, and the richer
  country always lends (`HiddenInformation.optimal_contract_exists_unique`,
  `MoralHazardTwoCountry.eqm_exists_unique`, `richer_country_lends`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for where the printed text is wrong or
imprecise.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Model](CapitalMarketImperfections/Model.lean) | 2 | Finite state space, expectations |
| [SovereignRiskPrimitives](CapitalMarketImperfections/SovereignRiskPrimitives.lean) | 33 | Utility class, expectations, Jensen, clamp optimality |
| [DirectSanctionsInsurance](CapitalMarketImperfections/DirectSanctionsInsurance.lean) | 54 | §6.1.1: the optimal contract, uniform and continuous-density examples |
| [SanctionsWithSaving](CapitalMarketImperfections/SanctionsWithSaving.lean) | 38 | Appendix 6B; Ex 1, 2 |
| [ReputationTrigger](CapitalMarketImperfections/ReputationTrigger.lean) | 126 | §6.1.2–6.1.3: trigger strategies, Table 6.1, partial insurance, subgame perfection; Ex 3 |
| [BulowRogoff](CapitalMarketImperfections/BulowRogoff.lean) | 72 | Bulow–Rogoff, collateral, Worrall convergence, §6.2.2 |
| [DebtCeiling](CapitalMarketImperfections/DebtCeiling.lean) | 67 | §6.2.1: the debt ceiling, the repayment set |
| [PrecommitmentInvestment](CapitalMarketImperfections/PrecommitmentInvestment.lean) | 25 | §6.2.1: Kuhn–Tucker with and without precommitment |
| [DebtOverhangLaffer](CapitalMarketImperfections/DebtOverhangLaffer.lean) | 57 | §6.2.3–6.2.5: overhang, Laffer curve, buybacks; Ex 6 |
| [SovereignBargaining](CapitalMarketImperfections/SovereignBargaining.lean) | 43 | Appendix 6A: Rubinstein bargaining |
| [HiddenInformation](CapitalMarketImperfections/HiddenInformation.lean) | 68 | §6.3 |
| [MoralHazardSmallCountry](CapitalMarketImperfections/MoralHazardSmallCountry.lean) | 100 | §6.4.1, §6.4.3; Ex 4, 5 |
| [MoralHazardTwoCountry](CapitalMarketImperfections/MoralHazardTwoCountry.lean) | 53 | §6.4.2; Ex 4(b) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
