# Source map

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Chapter 10, “Sticky-Price Models of Output, the Exchange Rate, and the Current
Account” (pp. 659–714). Equation numbers are the book's, cited as (n); page
numbers are book pages. Lean names are relative to
`ObstfeldRogoff.StickyPriceModels`; the rows list the main declarations, and each
module's docstring maps its remaining results. Where a statement adds a
hypothesis the book leaves implicit, or departs from the printed claim, see
[corrections](corrections.md).

## §10.1 A two-country model of monetary transmission (pp. 660–689)

| Book | Claim | Lean |
| --- | --- | --- |
| (2)–(7), fn 4, fn 6 | The CES price index is the minimum cost of a unit of consumption; demands; the law of one price gives PPP | `ReduxPrimitives.ces_minimum_cost`, `ces_expenditure_eq_iff`, `ces_utility_max`, `ppp_of_loop`, `bloc_ppp` |
| (10)–(11), p. 665 | World demand; revenue; choosing output is choosing price | `ReduxPrimitives.world_demand`, `revenue_on_demand`, `demand_iff_price` |
| (8), (12)–(16) | **The household problem**: first-order conditions plus transversality are necessary and sufficient | `ReduxPrimitives.HouseholdEnv.isOptimal_iff`, `book_tvc_iff` |
| (18)–(21), (26) | Goods-market clearing; the steady-state interest rate, income and real balances | `ReduxPrimitives.world_goods_market`, `steady_state_rate`, `steady_state_budget`, `steady_state_real_balances` |
| (22)–(25), p. 668 | **The steady state exists and is unique for every net foreign asset position**; the symmetric case; the planner's output exceeds the market's | `ReduxSteadyState.exists_unique_steady`, `isSteadyState_zero_iff`, `steady_creditor`, `planner_max`, `ybar0_lt_plannerOutput` |
| pp. 671, 677 | No transitional dynamics under flexible prices | `ReduxSteadyState.flexible_path_is_steady` |
| (27)–(41) | Each log-linear equation is an exact derivative (or exact in logs) | `ReduxLogLinear.linearise_27`, `log_demand_exact`, `labour_log_exact`, `ppp_log_exact` |
| (42)–(57) | The steady-state and short-run linear systems: unique solutions; exact (57) | `ReduxLogLinear.steadyLinear_iff`, `steadyLinear_consequences`, `shortRun_ca`, `eq57_exact` |
| (58)–(61) | **No overshooting, exactly**; the forward solution | `ReduxMoneyShocks.no_overshooting_exact`, `nominal_rate_exact`, `forward_solution_unique` |
| (62)–(74) | The GG schedule and closed forms; world aggregates; comparative statics | `ReduxMoneyShocks.gg_schedule`, `moneyShock_iff`, `moneyShock_closed_forms`, `moneyShock_world`, `exchangeRateCoef_strictAntiOn` |
| fn 16, p. 681 | Temporary shocks leave a permanent appreciation | `ReduxMoneyShocks.temporary_shock`, `temporary_shock_appreciation` |
| §10.1.8.1, pp. 683–684 | Equiproportionate money shock, exactly: unique equilibrium, welfare gain, the demand-determination bound | `ReduxMoneyShocks.equiproportionate_unique`, `equiproportionate_exists`, `equiGain_pos`, `equiproportionate_demand_bound` |
| p. 688 | Country size and the current account | `ReduxMoneyShocks.country_size_correction` |
| Ex 1, p. 713 | Money growth | `ReduxMoneyShocks.ex1_growth_shock`, `ex1_growth_shock_late` |
| (75)–(76), pp. 684–685 | Welfare as the derivative of lifetime utility; the exchange-rate terms cancel; `dUᴿ = mᵂ/θ` | `ReduxWelfare.welfare_eq75`, `welfare_e_cancels`, `welfare_eq76` |
| p. 684, fn 19 | The exact “`χ` not too large” threshold, and a counterexample | `ReduxWelfare.foreign_shock_welfare_pos_iff`, `welfare_threshold`, `no_threshold_of_le`, `counterexample_theta6` |
| p. 674 | Menu costs: the gain from adjusting is second order; meeting demand iff price ≥ marginal cost | `ReduxWelfare.menu_cost_second_order`, `menu_cost_rationale`, `meet_demand_iff` |
| (77)–(81), p. 688 | Labour-income taxes: (81) with its exact sign; the small-country limit | `ReduxWelfare.welfare_eq81`, `welfare81_neg_iff`, `welfare81_large_theta`, `small_country_limit` |
| Ex 3, p. 713 | The nonlinear steady state exists and is unique; the linear solution; welfare | `ReduxWelfare.ex3_steady_existsUnique`, `ex3_iff`, `ex3_welfare_zero` |
| T10–T11 | **The linear steady-state system is exactly the derivative of the nonlinear steady-state map** at zero net foreign assets | `ReduxLinearisationLink.linearisation_link`, `linearisation_link_system` |

## §10.2 Nontradables with preset prices: overshooting revisited (pp. 689–696)

| Book | Claim | Lean |
| --- | --- | --- |
| (83)–(90), p. 691 | The CPI is the minimum cost; the household's conditions are necessary and sufficient | `NontradablesModel.cpi_isMinCost`, `budget84_iff_wealth`, `householdOptimal_iff` |
| (91)–(93), p. 692 | Tradables consumption and the no-bubble condition; the unique steady state | `NontradablesModel.cT_eq_endowment_iff`, `output_93`, `steadyState_unique`, `steadyState_isEquilibrium` |
| (92), (99), p. 693 | **Overshooting iff `ε > 1`, exactly**; (99) is the derivative of the exact impact | `NontradablesOvershooting.impact_exists_unique`, `overshoot_iff`, `exchangeRate_overshoots_iff`, `hasDerivAt_impact`, `loglinear_99` |
| (95)–(98), p. 694 | Output, real balances and welfare rise, exactly; long-run neutrality | `NontradablesOvershooting.shock_output_rises`, `realBalances_rise`, `welfare_gain_eq`, `longRun_neutral` |
| pp. 674, 692 | Output is demand-determined iff `x² ≤ θ/(θ−1)` | `NontradablesOvershooting.shock_equilibrium_iff`, `shock_markup_iff` |
| p. 694 | The wealth-effect regression; Table 10.1 | `StickyPriceEvidence.wealth_significance`, `wealth_implied_rSquared`, `caResponse_unique_sign_change` |
| Ex 2, p. 713 | Real interest parity, exactly | `NontradablesOvershooting.real_interest_parity`, `ex2_real_depreciation` |

## §10.3 Government spending and productivity shocks (pp. 696–706)

| Book | Claim | Lean |
| --- | --- | --- |
| (100)–(104), fn 24 | Productivity: exact labour condition; the long-run system | `ReduxFiscalProductivity.labour_log_exact_kappa`, `linearise_100`, `fn24_world`, `fiscalSteadyLinear_iff` |
| (105)–(107), p. 698 | The short-run system is uniquely solved; appreciation, deficit, interest rate | `ReduxFiscalProductivity.fiscalShock_iff`, `fiscal_gg`, `productivity_eq106_107`, `productivity_corollaries` |
| p. 699 | The nominal interest rate is unchanged | `ReduxFiscalProductivity.fiscal_nominal_rate_unchanged` |
| p. 697, fn 25, p. 700 | Temporary and anticipated productivity shocks; welfare in both countries (closed forms) | `ReduxFiscalProductivity.fiscal_zero_iff_money`, `fn25_welfare_hasDerivAt`, `productivity_welfare` |
| (108)–(130) | Government spending: demand, budget, long and short run | `ReduxFiscalProductivity.world_demand_with_gov`, `gov_budget_combined`, `gov_eq122`, `gov_eq128_129`, `fiscal_world` |
| pp. 703–706 | Temporary spending gives a deficit, permanent a surplus; welfare (closed forms) | `ReduxFiscalProductivity.gov_current_account`, `gov_temporary_welfare`, `gov_permanent_welfare`, `gov_future_welfare` |

## §10.4 Nominal wage rigidities; pricing to market (pp. 706–714)

| Book | Claim | Lean |
| --- | --- | --- |
| (131)–(140), pp. 707–708 | Small country with preset wages: cost minimisation, zero profit, the worker's conditions | `PresetWagesSmallCountry.labor_cost_ge`, `firm_price_eq_wageIndex`, `worker_136`, `laborSupply_140` |
| p. 709 | The short run is as with preset prices; overshooting and welfare | `PresetWagesSmallCountry.presetWage_equilibrium_iff`, `presetWage_overshoots_iff`, `presetWage_welfare_gain_pos` |
| (144), pp. 710–711 | Pricing to market: the markup price is the unique optimum; the law of one price iff equal elasticities; complete pass-through | `PassThrough.ce_optimal_price_iff`, `ptm_optimal_prices_iff`, `ptm_loop_iff`, `ce_passThrough_elasticity` |
| p. 711 | Independence of the two markets iff production is linear | `PassThrough.segmented_optimum_iff`, `convexCost_foreign_price_depends_on_home_demand` |
| p. 712 | Linear demand: pass-through below one half; markups and nominal rigidity; distribution costs | `PassThrough.lin_passThrough_bounds`, `markup_invariant_to_nominal_scaling`, `lin_markup_strictMonoOn_rigid_wage`, `retail_passThrough_bounds` |
| pp. 674–675 | Producer- vs local-currency pricing; the menu-cost envelope | `PassThrough.pcp_passThrough_elasticity`, `lcp_passThrough_elasticity`, `lcp_meets_demand_iff`, `lcp_menu_cost_neighbourhood` |
| Boxes 10.1–10.2 | Kurtosis; markups | `StickyPriceEvidence.pearson_inequality`, `kashyap_kurtosis_comparison`, `PassThrough.ce_lerner_index` |
| (141)–(143), p. 710 | Two-country preset wages: cost minimisation, markup pricing, the worker's problem, `ȳ₀` with two distortions | `ReduxPresetWages.firm_min_cost`, `markup_isGreatest`, `worker_isOptimal_iff`, `wageParams_ybar0` |
| p. 710 | The same results as §10.1 for money shocks | `ReduxPresetWages.presetWage_iff_money`, `presetWage_labour_log_exact` |
| (144), p. 711 | Pricing to market in the two-country model | `ReduxPresetWages.ptm_optimal`, `ptm_pass_through` |

## Exercise 4 (pp. 713–714)

| Book | Claim | Lean |
| --- | --- | --- |
| Ex 4(a)–(c) | Cash in advance: the optimum, the planner, preset output (finite states) | `CashInAdvanceCredibility.ciaOptimal_iff`, `planner_unique`, `ybarN_lt_yPlan`, `preset_output_finite_state` |
| Ex 4(d)–(e) | The one-shot game: unique equilibrium; the `(π−1)²` variant; commitment | `CashInAdvanceCredibility.book_equilibrium`, `conventional_equilibrium`, `commitment_gross_no_optimum` |
