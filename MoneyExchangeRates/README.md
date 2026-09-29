# Money and exchange rates under flexible prices in Lean

This is the `MoneyExchangeRates/` proof project in
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Run the commands below from this directory: `cd MoneyExchangeRates` from the repository
root. [Return to the library index](../README.md).

A checked formalisation of Obstfeld and Rogoff (1996), *Foundations of
International Macroeconomics*, Chapter 8, “Money and Exchange Rates under
Flexible Prices” (pp. 513–604), with Appendices 8A–8B, the exercises, and the
Supplement to Chapter 8 on the maximum principle (pp. 745–753). The library
contains **820 theorems** and audits **1046 declarations**.

Headline results, in the namespace `ObstfeldRogoff.MoneyExchangeRates`:
* **The Cagan model.** Every solution is the no-bubble solution plus a bubble; the
  no-bubble solution is the unique bounded one, in discrete and continuous time and on
  a Markov chain (`CaganModel.isCaganPath_iff_bubble`, `existsUnique_markovEqm`,
  `CaganContinuous.existsUnique_noBubble`).
* **Speculative attacks and target zones.** The attack equilibrium exists and is unique;
  the smooth-pasting target zone exists and is unique, and its lattice version converges
  to it (`SpeculativeAttack.attackEqm_unique`, `TargetZone.existsUnique_symmetric_zone`,
  `lattice_converges`).
* **Money in utility.** The first-order conditions plus transversality characterise the
  optimum; the dichotomy holds iff `σ = θ`; transversality rules out deflationary bubbles
  iff `Σ v′(m_t) = ∞` (`MoneyInUtility.isOptimal_iff`, `dichotomy_iff`,
  `MonetaryBubbles.tvc_iff_not_summable`).
* **Nominal asset pricing.** Euler equations plus transversality give whole-plan
  optimality on the event tree, and the equilibrium is the unique bounded solution
  (`NominalAssetPricing.Household.household_sufficiency`, `Solutions.unique_bounded`).
* **The maximum principle.** Mangasarian and Arrow sufficiency, with the Ponzi and Halkin
  counterexamples (`MaximumPrinciple.mangasarian_infinite`, `halkin_candidate`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for where the printed text is wrong or
imprecise.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Model](MoneyExchangeRates/Model.lean) | 2 | The Cagan money-demand equation |
| [CaganModel](MoneyExchangeRates/CaganModel.lean) | 120 | §8.2, §8.4: Cagan (deterministic and stochastic), seignorage, the monetary model, pegs; Ex 1 |
| [CaganContinuous](MoneyExchangeRates/CaganContinuous.lean) | 43 | §8.2.5: continuous time and the period-h limit |
| [SpeculativeAttack](MoneyExchangeRates/SpeculativeAttack.lean) | 38 | §8.4.2: speculative attacks |
| [TargetZone](MoneyExchangeRates/TargetZone.lean) | 111 | §8.5–8.6: target zones, the lattice model and its limit; Ex 5 |
| [MoneyInUtility](MoneyExchangeRates/MoneyInUtility.lean) | 125 | §8.3: money in utility, CES, dollarization, fiscal fixing; Ex 3 |
| [MonetaryBubbles](MoneyExchangeRates/MonetaryBubbles.lean) | 72 | §8.3.5: bubbles, deflations, hyperinflations; Ex 2 |
| [CashInAdvance](MoneyExchangeRates/CashInAdvance.lean) | 32 | §8.3.6, App. 8A–8B: cash in advance; Ex 4 |
| [MaximumPrinciple](MoneyExchangeRates/MaximumPrinciple.lean) | 59 | Supplement: the maximum principle |
| [NominalAssetPricing](MoneyExchangeRates/NominalAssetPricing.lean) | 146 | §8.7: nominal asset pricing, whole-plan optimality, the equilibrium |
| [ForwardPremium](MoneyExchangeRates/ForwardPremium.lean) | 72 | §8.7: CIP, Siegel, Fama, risk premia; Ex 6–8 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
