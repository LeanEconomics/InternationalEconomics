# Source map

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Chapter 8, “Money and Exchange Rates under Flexible Prices” (pp. 513–604), and
the Supplement to Chapter 8, “Continuous-Time Maximization and the Maximum
Principle” (pp. 745–753). Equation numbers are the book's, cited as (n); page
numbers are book pages. Lean names are relative to
`ObstfeldRogoff.MoneyExchangeRates`; the rows list the main declarations, and
each module's docstring maps its remaining results. Where a statement adds a
hypothesis the book leaves implicit, or departs from the printed claim, see
[corrections](corrections.md).

## §8.2 The Cagan model (pp. 515–530)

| Book | Claim | Lean |
| --- | --- | --- |
| (6)–(9), fn 6, pp. 517–518 | The forward iteration; the no-bubble solution exists and is unique | `CaganModel.isCaganPath_iff`, `forward_iteration`, `caganSummable_of_growth`, `existsUnique_noBubble` |
| (11), p. 520 | Every solution is the fundamental plus a bubble; bubbles explode | `CaganModel.isCaganPath_iff_bubble`, `abs_tendsto_atTop_of_bubble` |
| (10), fn 8, Fig. 8.1 | Neutrality; `p = m + ημ`; the announced money increase | `CaganModel.fundamental_add_const`, `fundamental_linear`, `fundamental_stepMoney_le`, `stepMoney_strictly_convex` |
| (12)–(14), p. 521 | Stochastic Cagan model on a Markov chain and an event tree: existence, uniqueness among bounded solutions, bubbles | `CaganModel.existsUnique_markovEqm`, `treeEqm_iff_bubble`, `treeEqm_bounded_eq_fundamental`, `markovFundamental_eigen` |
| (15)–(19), fn 9–11 | Continuous time: the fundamental solves (15); unique without bubbles; the affine case | `CaganContinuous.contFundamental_isSol`, `isCaganSolOn_iff`, `existsUnique_noBubble`, `contFundamental_affine` |
| (17), p. 522 | The period-`h` model converges to continuous time | `CaganContinuous.periodH_equation_limit`, `periodHPrice_tendsto` |
| (20)–(23), fn 13 | Seignorage; `μ = 1/η` is the unique global maximum | `CaganModel.seignorage_constant_growth`, `seignorage_lt_max`, `seignorage_decomposition` |
| (24)–(32), pp. 526–529 | The monetary model of the exchange rate: existence, uniqueness, comparative statics, persistent growth | `CaganModel.monetary_model_iff`, `exchange_rate_existsUnique`, `exchange_rate_comparative_statics`, `exchange_rate_persistent_growth` |

## §8.3 Money in the utility function (pp. 530–554)

| Book | Claim | Lean |
| --- | --- | --- |
| (34)–(38), pp. 532–534 | The budget; the first-order conditions plus transversality characterise the optimum | `MoneyInUtility.wealth_of_budget`, `isOptimal_iff`, `euler_of_optimal`, `money_foc_of_optimal`, `transversality_of_optimal`, `intertemporal_budget` |
| (39)–(40), p. 535 | Cobb–Douglas and CES money demand; the CES utility is jointly concave | `MoneyInUtility.cd_money_demand_iff`, `ces_money_demand_iff`, `cesIndex_concaveOn`, `cesUtility_concaveOn` |
| p. 536, Ex 3 | Consumption formulas (existence of the optimum); the dichotomy iff `σ = θ` | `MoneyInUtility.ces_isOptimal_of_closedForm`, `logCD_isOptimal`, `dichotomy_iff`, `cd_equilibrium_consumption` |
| fn 26, (42)–(44) | Government and national budgets; steady consumption | `MoneyInUtility.government_pv`, `national_budget`, `steady_consumption_iff` |
| (45)–(50), Fig. 8.2 | Real-balance dynamics; equilibrium iff dynamics plus transversality; unique for log with `μ ≥ 0`; a continuum when `β < 1+μ < 1` | `MonetaryBubbles.bubble_dynamics_iff`, `equilibrium_iff`, `equilibrium_iff_of_bounded`, `log_equilibrium_unique`, `log_equilibria_multiple` |
| fn 32 | Transversality rules out a deflation iff `Σ v′(m_t) = ∞`; counterexamples | `MonetaryBubbles.tvc_iff_not_summable`, `bounded_rules_out_deflation`, `logInt_deflation_equilibrium` |
| (51)–(54), fn 34, Fig. 8.3 | Hyperinflations: collapse paths, fn 34 necessary but not sufficient, backing | `MonetaryBubbles.backOrbit_iterate`, `backOrbit_unique`, `fn34_tendsto_atBot`, `vSlow_counterexample`, `backing_rules_out_hyperinflation` |
| Ex 2 | Money in the production function | `MonetaryBubbles.ex2_steady_state`, `ex2_no_deflation`, `ex2_hyperinflation_possible` |
| (55)–(60), Ex 4 | Cash in advance: the constraint binds; the optimum; the Euler equation with `r_{s+1}` | `CashInAdvance.cia_binds`, `cia_optimal_iff`, `euler_60_iff`, `budget_59` |
| (61)–(67), pp. 551–553 | Dollarization: the two-money problem, first-order conditions necessary and sufficient, (67) with its corner | `MoneyInUtility.dollar_optimal_iff`, `dollar_foreign_kkt_of_optimal`, `dollar_demand_of_optimal`, `dollar_67_of_optimal` |

## §8.4 Nominal exchange-rate regimes (pp. 554–569)

| Book | Claim | Lean |
| --- | --- | --- |
| (68)–(69), fn 44 | Fixed and crawling pegs; interest-rate pegs are indeterminate; fiscal fixing | `CaganModel.fixed_rate_money`, `crawling_peg_interest`, `interestPeg_indeterminate`, `MoneyInUtility.fiscal_fixing_iff` |
| (71)–(77), pp. 558–566 | **Speculative attacks**: the shadow rate; the attack equilibrium exists and is unique; attack exactly `η` before exhaustion; reserves at attack; the corrected (77) | `SpeculativeAttack.shadowRate_eq_fundamental`, `attackEqm_exists`, `attackEqm_unique`, `attackTime_eq_exhaustion_sub`, `reserves_at_attack`, `attackTime_corrected` |
| p. 564 | Bubbles; `μ = 0` | `SpeculativeAttack.bubbleAttackEqm_exists`, `no_attack_without_growth`, `attack_without_growth_any_date` |
| (78), Ex 1 | Two-country pegs; announced future fixing | `CaganModel.twoCountry_fixed_iff`, `futureFix_existsUnique`, `stochFutureFix_unique` |

## §8.5–8.6 Target zones (pp. 569–579)

| Book | Claim | Lean |
| --- | --- | --- |
| (80)–(85), pp. 570–575 | The ODE and all its solutions; the smooth-pasting solution exists and is unique; honeymoon effect | `TargetZone.zone_ode_no_drift`, `existsUnique_symmetric_zone`, `honeymoon`, `edge_bounds` |
| §8.5, discrete | The lattice target zone: existence, uniqueness, smooth pasting; equals the Markov Cagan price and (80); converges to the continuous solution | `TargetZone.latticeEqm_existsUnique`, `latticeSol_smooth_pasting`, `lattice_eq_markovFundamental`, `lattice_eq_80`, `lattice_converges`, `lattice_edge_converges` |
| (88)–(90), pp. 577–579 | One-sided zones and speculative attacks; reserves are exhausted with probability 1 | `TargetZone.credible_zone_existsUnique`, `attack_impossible_iff`, `interventions_infinitely_often`, `reserves_exhausted_almost_surely` |
| Ex 5 | The band with drift: unique solution for every band | `TargetZone.driftBand_existsUnique`, `bandWidth_strictMonoOn` |
| §8.5.6, fn 60 | Interest-rate bounds in a band | `TargetZone.band_interest_bounds` |

## §8.7 A stochastic model with nominal assets (pp. 579–595)

| Book | Claim | Lean |
| --- | --- | --- |
| (91)–(98) | Euler equations necessary and sufficient; with transversality, sufficient for whole-plan optimality on the event tree; Fisher iff zero covariance | `NominalAssetPricing.isLocalMax_moneyValue_iff`, `Household.household_sufficiency`, `Household.household_euler_necessary`, `fisher_iff_cov_zero` |
| (99)–(101), pp. 582–583 | Exact linearity in real balances; the unique bounded solution; transversality; the equilibrium is optimal for each household | `NominalAssetPricing.eq99_iff_linearMoneyEq`, `Solutions.unique_bounded`, `unique_of_TVC`, `Equilibrium87.equilibrium_optimal` |
| (103)–(106) | Cash in advance; covered interest parity; Siegel's paradox | `NominalAssetPricing.cia_price_level`, `ForwardPremium.cip_of_statePrices`, `siegel_iff`, `Gaussian.log_forward_gaussian` |
| (107)–(119) | Forward rates, Fama's regression, the general-equilibrium risk premium (finite states and joint normality) | `ForwardPremium.forward_exact_decomposition`, `JointGaussian.eq109_gaussian`, `Fama.fama_slope`, `forward_euler_iff`, `JointGaussian.eq119_gaussian` |
| Ex 6–8, App. 8A–8B | Engel price indexes; overlapping forecasts; the two-country cash-in-advance model; sterilised intervention | `ForwardPremium.Engel.marginal_index_eq_relative_price`, `ex8a_overlap`, `CashInAdvance.relative_price_131`, `CashInAdvance.sterilised_is_swap` |

## Supplement to Chapter 8 (pp. 745–753)

| Book | Claim | Lean |
| --- | --- | --- |
| (7)–(11), p. 746 | Period-`h` conditions and their limits | `MaximumPrinciple.mrs_limit`, `costate_limit`, `flow_budget_limit` |
| p. 748 | Mangasarian and Arrow sufficiency; the transversality condition alone is insufficient (Ponzi) and not necessary (Halkin) | `MaximumPrinciple.mangasarian_infinite`, `arrow_finite`, `ponzi_counterexample`, `halkin_candidate` |
| A.3, (16)–(25) | The monetary problem: conditions necessary and sufficient; budgets; CES consumption | `MaximumPrinciple.monetary_optimal_iff`, `consolidated_19`, `consumption_25` |
| A.3.3 | The nominal-rate formula is the unique no-bubble solution | `MaximumPrinciple.xStar_eq_book`, `xStar_unique`, `nominal_rate_constant_growth` |
