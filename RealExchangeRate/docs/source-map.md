# Source map

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Chapter 4, “The Real Exchange Rate and the Terms of Trade” (pp. 199–267).
Equation numbers are the book's, cited as (4.n); page numbers are book pages.
Lean names are relative to `ObstfeldRogoff.RealExchangeRate`; the rows list the
main declarations, and each module's docstring maps its remaining results. Where
a statement adds a hypothesis the book leaves implicit, or departs from the
printed claim, see [corrections](corrections.md).

## §4.1 International price levels (pp. 199–202)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 200; fn 1 | Real exchange rate; absolute and relative PPP; law of one price | `PriceLevels.realExchangeRate`, `absolute_ppp_iff`, `relative_ppp_const`, `lop_ratio` |
| §4.1 | Cobb–Douglas price index, homogeneous of degree one | `CobbDouglasIndex.price`, `price_homogeneous`, `price_numeraire` |

## §4.2 The price of nontraded goods with mobile capital (pp. 202–216)

| Book | Claim | Lean |
| --- | --- | --- |
| (4.1), p. 205 | CRS intensive form | `CRSProduction.crs_intensive_form` |
| (4.2), p. 206 | Unique capital–labour ratio from `A_T f′(k_T) = r` (IVT, Inada) | `CRSProduction.IntensiveTech.existsUnique_fp_eq`, `kstar_foc`, `kstar_unique` |
| p. 206 | `∂k_T/∂r = 1/(A_T f″)` | `CRSProduction.IntensiveTech.kstar_hasDerivAt_r` |
| (4.6), p. 206 | Factor-price frontier; `∂w/∂r = −k_T`, `∂w/∂A_T = f(k_T)` | `CRSProduction.IntensiveTech.wage_frontier`, `wage_hasDerivAt_r`, `wage_hasDerivAt_A` |
| (4.7), p. 208; fn 19 | Zero profit; CRS maximum profit is zero, attained iff `K/L = k` | `CRSProduction.IntensiveTech.zero_profit`, `crs_profit_le`, `crs_profit_eq_iff` |
| (4.2)–(4.5), p. 206 | **Unique supply equilibrium: `p` is independent of demand** | `BalassaSamuelson.supplyEqm_existsUnique`, `CRSProduction.IntensiveTech.existsUnique_wageRental_eq` |
| p. 208 | A rise in `A_T` raises `p` and `k_N`; a rise in `A_N` leaves `k_N` and `pA_N` unchanged | `BalassaSamuelson.eqmPrice_strictMonoOn_AT`, `eqm_kN_strictMonoOn_AT`, `eqm_AN_neutral` |
| (4.8)–(4.9), pp. 208–209 | Log-linear wage and price equations, as exact derivatives of logs | `BalassaSamuelson.logWage_path_hasDerivAt`, `logPrice_path_hasDerivAt`, `logPrice_hat_eq9`, `logPrice_hat_r`, `muKN_sub_muKT` |
| p. 208 | **Balassa–Samuelson sign (corrected)** and counterexample | `BalassaSamuelson.bs_price_rises`, `bs_sign_counterexample`, `eqm_logPrice_deriv_pos` |
| p. 209 | A rise in `r` lowers `p` iff `μ_LN > μ_LT` (strict) | `BalassaSamuelson.price_falls_with_r`, `price_r_boundary`, `r_elasticity_neg_iff` |
| pp. 211–212 | **Harrod–Balassa–Samuelson** price-level ratio and differential, general and under common shares | `PriceLevels.price_level_ratio`, `log_price_level_ratio`, `BalassaSamuelson.hbs_log_ratio`, `hbs_path_hasDerivAt`, `hbs_common_shares`, `hbs_sign` |
| §4.2.4, pp. 214–216 | Three factors; immobile capital | `BSExtensions.threeFactor_unique`, `threeFactor_price`, `immobileCapital_unique`, `immobileCapital_degenerate`, `immobileCapital_price` |

## §4.3 Consumption and production in the long run (pp. 216–225)

| Book | Claim | Lean |
| --- | --- | --- |
| (4.10), p. 218 | GDP line; steeper than GNP iff `k_T > k_N` | `LongRunGDPGNP.gdp_line`, `gdp_slope_gt_one_iff`, `gdp_eq_factor_income` |
| (4.11), p. 219; fn 18 | GNP line; `Y_T − C_T = −rB` | `LongRunGDPGNP.trade_balance_long_run` |
| p. 220 | A rise in wealth raises foreign assets by more than itself | `LongRunGDPGNP.foreign_asset_change`, `wealth_rise_trade_balance`, `tradables_output_falls` |
| fn 19, p. 219 | The autarky frontier lies inside the GNP line | `LongRunGDPGNP.autarky_frontier_inside_gnp`, `autarky_frontier_eq_gnp_iff` |
| (4.12), (4.17)–(4.18), pp. 221–224 | Productivity growth and nontradables employment | `ManufacturingEmployment.employment_growth`, `hasDerivAt_log_cesDemandN`, `wealth_growth`, `employment_effect`, `employment_effect_unit`, `psi_lt_one_iff`, `employment_falls` |
| (4.13)–(4.16), pp. 222–223 | CES index and demands | `CESIndex.cesIndex`, `cesDemand_budget`, `cesDemand_ratio`, `cesDemandT_eq`, `cesDemandN_eq` |

## §4.4 Consumption dynamics, the price level and the real interest rate (pp. 225–235)

| Book | Claim | Lean |
| --- | --- | --- |
| (4.20)–(4.22), pp. 227–228 | CES price index; `C = Z/P`; **duality**: `P` is the least cost of one unit of `Ω` | `CESIndex.cesPrice`, `cesIndex_demand`, `cesDemand_eq_price_form`, `cesIndex_le_div_price`, `cesPrice_isLeast_cost`, `cesPrice_strictMonoOn` |
| fn 26; fn 22; fn 13 | `P̂ = (1 − γ)p̂` at `p = 1`; `θ → 1` Cobb–Douglas limits; MRS | `CESIndex.cesPrice_logDeriv_at_one`, `cesPrice_tendsto_cobbDouglas`, `cesPrice_tendsto_model`, `cesIndex_tendsto_cobbDouglas`, `cesDemand_elasticity`, `cobbDouglas_mrs` |
| (4.25)–(4.29), pp. 230–232 | Consumption-based real rate, real budget, isoelastic consumption function; future prices have no wealth effect | `ConsumptionDynamics.grossRealRate`, `realDiscount_eq`, `euler_real_rate`, `real_budget`, `consumption_function`, `consumption_function_price_form`, `real_wealth_independent_of_future_prices` |
| (4.30)–(4.36), pp. 232–234; fn 30 | National and tradables budgets; tradables Euler equation and consumption function; current account | `ConsumptionDynamics.capital_eq_present_value`, `national_budget`, `tradables_budget`, `euler_isoelastic`, `euler_tradables`, `tradables_consumption_function`, `current_account_tradables` |
| p. 235 | A rising price level raises current tradables consumption iff `σ > θ` | `ConsumptionDynamics.tradables_consumption_gt_constant_price`, `tradables_consumption_lt_constant_price` |

## §4.5 The terms of trade in a dynamic Ricardian model (pp. 235–257)

| Book | Claim | Lean |
| --- | --- | --- |
| (4.41)–(4.45), pp. 238–241 | DFS schedules; **unique cutoff** `z̄ ∈ (0, 1)`; prices | `DFSStatic.relProductivity_strictAntiOn`, `relWage_of_market_clearing`, `relWageSchedule_strictMonoOn`, `cutoff_exists_unique`, `freeTradePrice_home`, `freeTradePrice_foreign` |
| pp. 240–242 | Comparative statics; real wages after labour and productivity shocks | `DFSStatic.labour_rise_statics`, `productivity_rise_statics`, `labour_rise_home_realWage_own`, `labour_rise_home_realWage_other`, `labour_rise_foreign_realWage_homeGoods`, `labour_rise_foreign_realWage_relocated`, `productivity_rise_home_realWage`, `productivity_rise_foreign_realWage` |
| pp. 237–238, 246; fn 36 | The price index is the least cost; moving-cutoff derivative (4.54) | `DFSPriceIndex.priceIndex_le_cost`, `priceIndex_attained`, `logPriceIndex_hasDerivAt` |
| (4.46)–(4.59), pp. 243–248 | Current account, Euler equation, steady state; the temporary productivity shock | `DFSCurrentAccount.currentAccount_home_eq_neg_foreign`, `euler_foc_iff`, `steady_rate_iff`, `steady_consumption`, `TemporaryShock.eq55`, `eq57`, `eq58`, `current_account_deficit`, `eq59`, `half_annuity` |
| (4.60)–(4.66), pp. 249–252; fn 41 | Transport costs: cutoff ordering, nontraded band, relative wage, the exponential example, monotonicity condition | `DFSTransportCosts.cutoff_order`, `nontraded_band`, `relWage_transport`, `cutoff_link_exp`, `interior_cutoffs_bound`, `relWage_eq_Btilde`, `Btilde_strictMonoOn_iff`, `log_realExchangeRate` |
| p. 251 | The effect of the cutoff on `P/P*`: zero to first order at equilibrium | `DFSPriceIndex.logRERInCutoff_deriv_zero_at_cutoff`, `logRERInCutoff_decreases` |
| pp. 253–255, Fig. 4.13 | Transfer effect; labour and productivity shocks with transport costs; price ratios rise for every good | `DFSTransportCosts.transfer_effect`, `labour_rise_transport`, `productivity_rise_transport`, `productivity_rise_termsOfTrade`, `priceRatio_mono`, `fifth_class_priceRatio` |

## Appendices (pp. 258–264)

| Book | Claim | Lean |
| --- | --- | --- |
| App. 4A, pp. 258–259 | Leisure as the nontraded good; (4.67)–(4.68) | `EndogenousLabour.wage_rpow_eq`, `leisure_demand`, `labour_income_rewrite`, `tradables_consumption_67`, `tradables_consumption_68` |
| App. 4B, pp. 260–263 | Short-run equilibrium (4.73)–(4.74); steady state; linearisation; **saddle-point stability** | `CostlyCapital.employment_nontradables`, `price_nontradables`, `price_strictAnti_capital`, `value_marginal_product`, `steady_state_iff`, `steady_capital_labour`, `hasDerivAt_qDrift_q`, `hasDerivAt_qDrift_K`, `saddle_point` |

## Exercises (pp. 264–267)

| Book | Claim | Lean |
| --- | --- | --- |
| Ex 1 | Labour-augmenting productivity | `BSExtensions.ex1_zero_max_profit`, `ex1_wage_hat`, `ex1_labour_reallocation` |
| Ex 2 | A rise in `r` | `BSExtensions.ex2_rise_in_r`, `ex2_price_falls_iff` |
| Ex 3 | Alternative real-units budget and consumption function | `ConsumptionDynamics.ex3_gross_rate_identity`, `ex3_alternative_budget`, `ex3_alternative_consumption`, `ex3_real_current_account` |
| Ex 4 | Constant and step changes in nontradables supply | `ConsumptionDynamics.ex4a_constant`, `ex4a_level`, `ex4b_step`, `ex4b_current_account_surplus` |
| Ex 5 | (4.67) derived from (4.29), (4.22), (4.33) | `EndogenousLabour.exercise5_tradables_consumption` |
| Ex 6 | Human capital and schooling | `BSExtensions.ex6_optimal_schooling`, `ex6_relative_wage`, `ex6_dlogw_dalpha`, `ex6_w_increasing_in_alpha_iff`, `ex6_w_strictMono_A`, `ex6_w_strictAnti_r`, `ex6_w_strictAnti_pi` |
| Ex 7 | Welfare after the temporary shock | `DFSCurrentAccount.TemporaryShock.home_welfare_pos_iff`, `foreign_welfare_pos` |
| Ex 8(a) | Cobb–Douglas price index | `CESIndex.cobbDouglas_price_exercise8a` |
