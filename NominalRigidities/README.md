# Nominal price rigidities in Lean

This is the `NominalRigidities/` proof project in
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Run the commands below from this directory: `cd NominalRigidities` from the repository
root. [Return to the library index](../README.md).

A checked formalisation of Obstfeld and Rogoff (1996), *Foundations of
International Macroeconomics*, Chapter 9, “Nominal Price Rigidities: Empirical
Facts and Basic Open-Economy Models” (pp. 605–658), with the exercises. The
library contains **567 theorems** and audits **776 declarations**.

Headline results, in the namespace `ObstfeldRogoff.NominalRigidities`:
* **Dornbusch overshooting.** The saddle path is exact and global: a path converges iff
  it is bounded iff it has no bubble iff it lies on the saddle path; overshooting iff
  `φδ < 1`; the stochastic model has a unique no-bubble solution
  (`DornbuschModel.saddle_path_theorem`, `DornbuschShocks.overshooting_iff`,
  `DornbuschExtensions.Stochastic.stoch_exists_unique_no_bubble`).
* **Credibility.** The commitment rule is the unique optimum among all rules; reputation
  sustains exactly the inflation rates `[π̲(β), k/χ]` in an infinite-horizon repeated game;
  Rogoff's optimal conservative central banker exists and is unique
  (`BarroGordon.commitRule_optimal`, `ReputationEquilibria.trigger_eqm_iff_bounds`,
  `CentralBankDelegation.rogoff_existsUnique`).
* **Regime choice.** The optimal feedback rule exists and is unique, and the peg is only a
  limit (`PooleRegimeChoice.exists_unique_optimal_rule`, `feedback_peg_only_limit`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for where the printed text is wrong or
imprecise.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Model](NominalRigidities/Model.lean) | 2 | The Barro–Gordon loss |
| [DornbuschModel](NominalRigidities/DornbuschModel.lean) | 71 | §9.2: the model, the exact global saddle path, the forward solution |
| [DornbuschShocks](NominalRigidities/DornbuschShocks.lean) | 45 | §9.2: money, real and growth shocks, overshooting; Ex 1 |
| [DornbuschExtensions](NominalRigidities/DornbuschExtensions.lean) | 55 | Ex 2; pegs and money-demand shocks (p. 631–632); the stochastic model |
| [DornbuschContinuousTime](NominalRigidities/DornbuschContinuousTime.lean) | 29 | The continuous-time Dornbusch model (not in the book) |
| [BarroGordon](NominalRigidities/BarroGordon.lean) | 56 | §9.5.1–9.5.2: one-shot, commitment, partisan, secrecy; Ex 5 |
| [ReputationEquilibria](NominalRigidities/ReputationEquilibria.lean) | 69 | §9.5.2: reputation as an infinite-horizon repeated game |
| [CentralBankDelegation](NominalRigidities/CentralBankDelegation.lean) | 35 | §9.5.3: Rogoff and Walsh; Ex 4 |
| [EscapeClausePeg](NominalRigidities/EscapeClausePeg.lean) | 46 | §9.5.4: the escape-clause peg |
| [PooleRegimeChoice](NominalRigidities/PooleRegimeChoice.lean) | 91 | §9.4.1, Ex 3: Poole, the optimal feedback rule, determinacy |
| [PolicyCoordination](NominalRigidities/PolicyCoordination.lean) | 30 | §9.5.5: Nash and planner |
| [ExchangeRateFacts](NominalRigidities/ExchangeRateFacts.lean) | 38 | §9.1, §9.3: volatility, half-life, regressions |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
