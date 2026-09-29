# Source map

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Chapter 9, “Nominal Price Rigidities: Empirical Facts and Basic Open-Economy
Models” (pp. 605–658). Equation numbers are the book's, cited as (n); page
numbers are book pages. Lean names are relative to
`ObstfeldRogoff.NominalRigidities`; the rows list the main declarations, and each
module's docstring maps its remaining results. Where a statement adds a
hypothesis the book leaves implicit, or departs from the printed claim, see
[corrections](corrections.md).

## §9.1 Sticky prices and exchange rates (pp. 605–609)

| Book | Claim | Lean |
| --- | --- | --- |
| (4), p. 606 | Real and nominal exchange-rate volatility are nearly equal | `ExchangeRateFacts.abs_sd_real_sub_sd_nominal_le`, `order_of_magnitude`, `corr_real_nominal_ge` |
| p. 606, Fig. 9.2 | Under a peg `sd q = sd(p* − p)`; first differences | `ExchangeRateFacts.sd_real_of_peg`, `abs_sd_diff_le` |

## §9.2 The Mundell–Fleming–Dornbusch model (pp. 609–621)

| Book | Claim | Lean |
| --- | --- | --- |
| (1)–(9), p. 612 | Reduction of the structural model; the forward form | `DornbuschModel.phillips_five_iff_six`, `structural_to_reduced`, `money_market_iff_nine`, `forward_form` |
| (10), p. 613 | Unique steady state; long-run neutrality | `DornbuschModel.steady_state_iff`, `steady_state_neutral` |
| (13), p. 612 | Real exchange-rate dynamics; convergence iff `0 < ψδ < 2` | `DornbuschModel.q_closed_form`, `q_tendsto`, `q_oscillates`, `q_diverges` |
| p. 613, Fig. 9.4 | **The saddle path, exact and global**: convergent = bounded = no-bubble = on the saddle path | `DornbuschModel.saddle_path_theorem`, `converges_iff_on_saddle`, `bounded_iff_on_saddle`, `no_bubble_iff_on_saddle` |
| (14)–(19), pp. 616–618 | The forward solution; existence and uniqueness; `e − e^flex = κ(q − q̄)` | `DornbuschModel.forward_solution`, `exists_unique_no_bubble`, `eighteen`, `eflex_eq_qbar_add_pflex` |
| p. 614 | The saddle path is shallower than `Δe = 0` | `DornbuschModel.saddle_shallower`, `κ_lt_one` |
| (11)–(17), Figs. 9.5–9.6 | Permanent money shock: impact, overshooting iff `φδ < 1`, the path, output, interest | `DornbuschShocks.perm_shock_impact`, `overshooting_iff`, `perm_shock_path`, `perm_shock_output_pos`, `perm_shock_interest` |
| fn 11 | A real shock is absorbed at once | `DornbuschShocks.real_shock` |
| (20)–(25), pp. 618–621 | General money processes; amplification; growth shocks; real interest rates | `DornbuschShocks.twenty`, `twenty_one`, `amplification_iff`, `twenty_two`, `twenty_four`, `twenty_five` |
| p. 619 | The stochastic model: the no-bubble solution exists and is unique; bubbles exist; conditional variance | `DornbuschExtensions.Stochastic.stoch_exists_unique_no_bubble`, `stoch_exists_unique_bounded`, `stoch_bubble_solutions`, `stoch_conditional_variance` |
| Ex 1–2, p. 657 | Disinflation; anticipated real depreciation | `DornbuschShocks.disinflation_no_slump_iff`, `DornbuschExtensions.anticipated_impact`, `anticipated_exists_unique` |
| (not in the book) | The continuous-time Dornbusch model: saddle path and overshooting | `DornbuschContinuousTime.ct_saddle_path_theorem`, `ct_perm_shock_impact`, `ct_overshooting_iff` |

## §9.3 Empirical evidence (pp. 621–631)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 624 | The half-life of deviations | `ExchangeRateFacts.halfLife_spec`, `halfLife_bounds` |
| p. 628, Fig. 9.10 | The regression: t-statistics, elasticity, and the variables' correct reading | `ExchangeRateFacts.gd_slope_tstat`, `gd_elasticity`, `gd_ratio_reading_inconsistent`, `gd_index_reading_consistent` |

## §9.4 Choice of the exchange-rate regime (pp. 631–634)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 631 | A peg insulates output from money-demand shocks | `DornbuschExtensions.accommodation_insulates`, `peg_requires_accommodation` |
| p. 632 | A peg with a real shock (sign corrected) | `DornbuschExtensions.peg_real_appreciation_boom`, `peg_real_depreciation_slump` |
| Ex 3, pp. 657–658 | Poole: float and peg equilibria; the exact comparison; the unique optimal feedback rule; the peg only as a limit; determinacy and sunspots | `PooleRegimeChoice.float_eqm_unique`, `peg_eqm_unique`, `peg_le_float_iff`, `exists_unique_optimal_rule`, `feedback_peg_only_limit`, `feedback_eqm_unique`, `bounded_eqm_output_unique_iff`, `boundary_sunspot_eqm` |

## §9.5 Credibility in monetary policy (pp. 634–657)

| Book | Claim | Lean |
| --- | --- | --- |
| (26)–(35), pp. 636–638 | The loss; the best response; the unique one-shot equilibrium | `BarroGordon.loss_derivation`, `isMin_iff_foc`, `oneShot_eqm_iff` |
| (36), p. 639 | The commitment rule is the unique optimum among all rules; loss rankings | `BarroGordon.commitRule_optimal`, `commitRule_unique`, `valueDiscretion_sub_valueCommit` |
| (37)–(39), pp. 639–641 | **Reputation as an infinite-horizon repeated game**: trigger equilibrium iff `β ≥ χ/(1+2χ)`; the exact sustainable set; shocks; one-period punishments; the finite horizon unravels | `ReputationEquilibria.trigger_zero_iff`, `trigger_eqm_iff_bounds`, `trigger_eqm_iff`, `onePeriod_eqm_iff_bounds`, `finite_eqm_unique` |
| (40)–(44), pp. 642–643 | Rogoff's conservative central banker (unique optimum `χ < c* < ∞`); the Walsh contract | `CentralBankDelegation.rogoff_optimal`, `rogoff_existsUnique`, `walsh_optimal` |
| (45)–(48), p. 645 | Partisan equilibrium | `BarroGordon.partisan_eqm_iff`, `partisan_surprises` |
| p. 646 | Central bank independence regression | `CentralBankDelegation.cbi_slope_significant`, `ExchangeRateFacts.cbi_fitted_values` |
| (49)–(58), pp. 648–652 | The escape-clause peg: optimal policy, expected depreciation as an integral, slopes | `EscapeClausePeg.govPolicy_optimal`, `integral_govPolicy`, `hasDerivAt_expDep_A` |
| Fig. 9.12, fn 40 | At most three equilibria; exactly three; existence; the float regime | `EscapeClausePeg.at_most_three`, `exactly_three`, `eqm_exists`, `float_eqm_iff` |
| pp. 654–657, fn 42 | Nash and planner policies; coordination gains | `PolicyCoordination.nash_iff_closed_form`, `planner_iff_closed_form`, `planner_response_compare`, `planner_lt_nash` |
| Ex 4–5, p. 658 | Walsh with multiplicative shocks; secrecy | `CentralBankDelegation.ex4_optimal`, `BarroGordon.secrecy_two_point` |
