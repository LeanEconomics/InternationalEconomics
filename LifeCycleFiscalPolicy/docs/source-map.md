# Source map

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Chapter 3, “The Life Cycle, Tax Policy, and the Current Account” (pp. 129–197).
Equation numbers are the book's; page numbers are book pages. Lean names are
relative to `ObstfeldRogoff.LifeCycleFiscalPolicy`. Where a statement adds a
hypothesis the book leaves implicit or departs from the printed claim, see
[corrections](corrections.md).

## §3.1 Government budget policy without overlapping generations (pp. 130–133)

| Book | Claim | Lean |
| --- | --- | --- |
| (3.1)–(3.2), p. 130 | Substituting the government budget eliminates taxes; equal-PV tax paths give the same budget set and optimum | `RicardianEquivalence.two_period_merged_constraint`, `two_period_budgetSet_eq_of_pv_eq`, `two_period_budgetSet_eq_government`, `two_period_optimum_invariant` |
| p. 131 | A retiming of taxes: private saving moves by exactly minus government saving; national saving is unchanged | `RicardianEquivalence.retiming_pv_eq`, `retiming_saving_date_one`, `retiming_saving_date_two` |
| (3.3)–(3.6), p. 132 | Private and government flow constraints plus transversality give the intertemporal budget constraints | `RicardianEquivalence.ric_discounted_telescope`, `ric_transversality_iff_ibc`, `private_ibc_of_flow`, `government_ibc_of_flow` |
| (3.7)–(3.8), p. 133 | **Ricardian equivalence**: neither the tax path nor the private/public split of assets matters | `RicardianEquivalence.merged_ibc`, `privatePVSet_eq_of_government_ibc`, `private_optimum_invariant` |

## §3.2 Government budget deficits in an OLG model (pp. 133–147)

| Book | Claim | Lean |
| --- | --- | --- |
| (3.9)–(3.13), pp. 134–135 | Log-utility demands exhaust lifetime wealth and satisfy the Euler equation | `LogOLG.youngC`, `LogOLG.oldC`, `LogOLG.budget`, `LogOLG.euler`, `TwoPeriodOLG.lifetimeWealth` |
| pp. 135–136 | Steady-state aggregate consumption; it depends on the youth tax and government assets, so **Ricardian equivalence fails** | `TwoPeriodOLG.aggregate_consumption_steady`, `aggregate_consumption_government`, `consumption_depends_on_youth_tax`, `consumption_increasing_in_government_assets` |
| (3.17)–(3.21), pp. 136–137 | The current account is private plus government saving; the old dissave their youthful saving | `TwoPeriodOLG.current_account_split`, `old_saving`, `private_saving` |
| (3.22)–(3.23), p. 137 | Saving with `β(1 + r) = 1` | `TwoPeriodOLG.young_saving_flat`, `private_saving_flat` |
| (3.24)–(3.27), pp. 138–139 | Debt-financed transfer: the date-0 old, the date-0 young, date-0 consumption rises by less than `d`, the date-1 old | `DeficitTransfer.youngWealthChange_eq`, `young0_consumption_change`, `consumption0_change`, `consumption0_change_lt`, `old1_consumption_change` |
| (3.28)–(3.30), p. 139; fn 9 | Later generations lose; date-1 consumption changes by an amount of **ambiguous sign** (both signs occur) | `DeficitTransfer.laterWealthChange_eq`, `later_young_consumption_change`, `later_old_consumption_change`, `consumption1_change`, `consumption1_rises_iff`, `consumption1_sign_ambiguous` |
| p. 139; fn 10 | Consumption falls from date 2; by `rd` in the flat case | `DeficitTransfer.consumption_later_falls`, `consumption_later_change`, `consumption_later_change_flat`, `share_of_flat` |
| (3.31)–(3.32), p. 140 | The current account worsens at dates 0 and 1 and then returns to its path | `DeficitTransfer.current_account1_change`, `current_account_later_zero` |
| p. 141 | A balanced-budget transfer from young to old worsens the current account | `DeficitTransfer.balanced_transfer_consumption` |
| Box 3.1, pp. 142–144 | Generational accounting: shifting taxes within a generation changes the deficit but nothing real | `TwoPeriodOLG.generational_account_invariant`, `generational_account_consumption`, `taxes_by_generation` |

## §3.3 Output fluctuations, demographics and the life cycle (pp. 147–156)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 148 | A transitory output shock moves the current account for two periods only | `DeficitTransfer.transitory_shock_current_account` |
| pp. 149–150 | `S^P/Y = −β/(1 + β) · eg/(2 + e + g)`; falls with `e`, rises with `g` iff `e < 0` | `DemographicsSaving.saving_rate_growth`, `savingRate`, `hasDerivAt_savingRate_e`, `savingRate_e_deriv_neg`, `hasDerivAt_savingRate_g`, `savingRate_g_deriv_pos_iff` |
| (3.33), p. 151 | Population growth raises the saving rate when the young save | `DemographicsSaving.saving_rate_population`, `hasDerivAt_saving_rate_population` |

## §3.4 Investment and growth (pp. 156–161)

| Book | Claim | Lean |
| --- | --- | --- |
| (3.36)–(3.39), p. 157 | Capital and wage as functions of the world rate; factor-price frontier `dw/dr = −k` | `SmallOpenDiamond.capLabour`, `mpk_capLabour`, `capLabour_unique`, `wageOf`, `mpl_capLabour`, `wage_hasDerivAt` |
| (3.40)–(3.42), p. 158 | Saving of the young finances capital and foreign assets; steady-state `b̄` | `SmallOpenDiamond.young_saving_per_capita`, `steady_foreign_assets`, `steady_current_account_sign` |
| p. 159; fn 24–25 | Per-capita saving and investment and their derivatives in `n` | `SmallOpenDiamond.savingPerCapita`, `saving_per_capita_eq`, `savingPerCapita_hasDerivAt`, `savingPerCapita_deriv_pos`, `investPerCapita`, `invest_per_capita_eq`, `investPerCapita_hasDerivAt`, `investPerCapita_deriv_pos_iff` |
| (3.43)–(3.44), p. 160; fn 27 | `K/Y = α/r` at every date; output growth; `I/Y = (n + g + ng)α/r` | `SmallOpenDiamond.Growth.capital_output_ratio_of_mpk`, `capital_output_ratio`, `output_eq_labour_mul`, `output_closed_form`, `output_growth`, `investment_share`, `wage_bill_share` |
| (3.45)–(3.46), pp. 160–161 | Log-utility saving; `S/Y`, `B/Y` and `CA/Y = (n + g + ng)B/Y`; comparative statics | `SmallOpenDiamond.Growth.log_young_saving`, `log_old_saving`, `young_saving_closed_form`, `youngSaving_share`, `saving_share`, `asset_share`, `current_account_share`, `savingRate_strictMono_n`, `savingRate_strictMono_g`, `investShare_strictMono`, `assetRatio_strictMono_beta`, `assetRatio_strictMono_r`, `assetRatio_neg_iff` |

## §3.5 Aggregate and intergenerational gains from trade (pp. 164–167)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 165; fn 32 | Lifetime utility as a function of `r`; factor-price frontier | `OLGGainsFromTrade.lifetimeUtility`, `hasDerivAt_lifetimeUtility`, `hasDerivAt_lifetimeUtility_frontier`, `wageCD`, `capitalCD`, `hasDerivAt_wageCD`, `capitalCD_div_wageCD`, `wageCD_pos` |
| (3.47), p. 165 | At autarky `dU/dr = −βr/(1 + r) < 0`; the old gain `k·dr` | `OLGGainsFromTrade.hasDerivAt_lifetimeUtility_autarky`, `autarky_utility_slope_neg`, `old_income_hasDerivAt` |
| pp. 165–166 | Income equivalent; the PV of generational losses exactly offsets the old's gain; the compensation scheme | `OLGGainsFromTrade.income_equivalent_autarky`, `pv_generation_losses`, `aggregate_first_order_zero`, `compensation_scheme` |
| pp. 166–167 | An economy already open: every generation gains iff `b > rk`; economy-wide gain `(1 + r)b·dr/r` | `OLGGainsFromTrade.hasDerivAt_lifetimeUtility_open`, `income_equivalent_open`, `open_generation_gains_iff`, `open_economywide_gain` |
| — | Timing: with predetermined capital the date-`t` young gain | `OLGGainsFromTrade.dateT_young_predetermined_hasDerivAt` |

## §3.6 Public debt and the world interest rate (pp. 167–174)

| Book | Claim | Lean |
| --- | --- | --- |
| (3.52)–(3.53), p. 169; Fig. 3.5 | Unique positive steady state and **global monotone convergence**; zero is unstable; `r̄` | `TwoCountryOLG.TwoCountry`, `psi`, `kbar`, `psi_fixed_iff`, `psi_strictMonoOn`, `psi_global_convergence`, `iterate_tendsto_of_below`, `iterate_tendsto_of_above`, `zero_unstable`, `rate_kbar` |
| (3.54)–(3.55), p. 170 | Taxes on the young service the debt; the law of motion with debt | `TwoCountryOLG.TwoCountry.tax_eq`, `psiDebt`, `law_of_motion_debt`, `psiDebt_eq` |
| p. 171; Fig. 3.6 | The debt map is increasing and strictly concave: at most two steady states, the upper one attracting; debt lowers the map | `TwoCountryOLG.TwoCountry.psiDebt_strictMonoOn`, `psiDebt_strictConcaveOn`, `steady_state_pattern`, `steady_state_at_most_two`, `upper_steady_state_attracts`, `psiDebt_strictAnti_debt`, `crowding_bracket_pos` |
| p. 171 | Existence of the two steady states for small debt, **none for large debt** | `TwoCountryOLG.TwoCountry.exists_two_steady_states`, `no_steady_state_of_large_debt` |
| p. 171 | Debt crowds out capital in both countries and raises the world rate | `TwoCountryOLG.TwoCountry.crowding_out`, `steady_state_lt_kbar`, `rate_rises` |
| §3.6.4, p. 171 | `r̄ ≤ n` for small `α`; then debt needs no taxes | `TwoCountryOLG.TwoCountry.rbar_le_n_iff`, `exists_alpha_rbar_le_n`, `rbar_tendsto_zero`, `tax_nonpos_of_rate_le` |

## §3.7 Integrating OLG and representative-consumer models (pp. 174–191)

| Book | Claim | Lean |
| --- | --- | --- |
| (3.56)–(3.60), pp. 175–176; fn 38 | Barro dynasty: budget constraint, iterated utility, (3.60) iff the remainder vanishes | `RicardianEquivalence.dynasty_ibc`, `utility_iterate`, `tendsto_utility_remainder`, `utility_eq_tsum_iff` |
| fn 39, pp. 176–177 | **Gale**: the recursion does not pin down utility (solutions differ by `Kβ^{−t}`); the miser | `RicardianEquivalence.gale_shift_solution`, `gale_solutions_differ`, `gale_shift_limit`, `gale_shift_ne_tsum`, `miserUtility`, `miser_recursion`, `miser_limit`, `miser_ne_tsum` |
| p. 177 | Neutrality with interior bequests: a transfer is offset one-for-one | `RicardianEquivalence.bequestPath`, `bequestPath_transfer_one`, `dynastyPVSet_transfer`, `interior_bequest_neutrality` |
| pp. 177–178 | Non-neutrality when the bequest constraint binds | `RicardianEquivalence.transfer_relaxes_binding_bequest`, `binding_bequest_feasible_ssubset` |
| (3.62)–(3.64), p. 182 | Weil: vintage budget constraint and consumption function | `PerpetualYouth.perpetual_finite_budget`, `perpetual_ibc_of_flow`, `perpetual_consumption_of_euler`, `weil_consumption_function` |
| (3.65)–(3.68), pp. 183–184 | Aggregation over vintages; the generational-turnover term | `PerpetualYouth.vintageSize`, `sum_vintageSize`, `vintageAgg`, `weil_aggregate_consumption_general`, `weil_aggregate_consumption`, `weil_aggregate_accumulation`, `weil_law_of_motion` |
| (3.69)–(3.71), pp. 184–186; fn 49, 52 | Dynamics with constant output: stability iff `(1 + r)β < 1 + n`; `b̄`, `c̄` and their comparative statics | `PerpetualYouth.weil_law_of_motion_const`, `weilSteadyB_fixed`, `weilSteadyB_unique`, `weil_converges`, `weil_not_converges`, `weil_stable_of_impatient`, `weilSteadyB_pos_iff`, `weil_steady_consumption`, `weilSteadyC_closed`, `weilSteadyC_slope_pos_iff`, `weilSteadyC_zero_growth`, `weilSteadyC_neg_of_unstable`, `weilSteadyB_falls`, `weilSteadyC_rises` |
| (3.72), p. 187 | A transitory shock and the return to steady state | `PerpetualYouth.weil_transitory_jump`, `weil_transitory_return` |
| (3.73), p. 188 | Growth: law of motion for `b/y`; NFA > 0 iff `β(1 + r) > 1 + g`; **faster growth lowers `b/y`** | `PerpetualYouth.weil_growth_law`, `weil_growth_ratio_law`, `growthSteadyRatio_fixed`, `growthSteadyRatio_pos_iff`, `growthSteadyRatio_strictAntiOn` |
| §3.7.6, pp. 189–191 | `(1 + r)β = 1`; debt is net wealth iff `n > 0` | `PerpetualYouth.weil_unit_tilt_law`, `weil_unit_tilt_zero_growth`, `weil_transitory_consumption_jump`, `weil_debt_tax`, `weil_debt_consumption`, `weil_debt_consumption_change`, `weil_ricardian_iff` |

## Appendix 3A Dynamic inefficiency (pp. 191–195)

| Book | Claim | Lean |
| --- | --- | --- |
| (3.77)–(3.78), p. 192 | Steady-state consumption and the golden rule | `DynamicInefficiency.steadyConsumption`, `steady_state_iff`, `golden_rule_max`, `hasDerivAt_steadyConsumption` |
| pp. 192–193 | **Dynamic inefficiency implies Pareto inefficiency**: a feasible path raises consumption at every date; with `r̄ > z` any change hurts some date | `DynamicInefficiency.pareto_improvement_of_dynamically_inefficient`, `exists_lower_capital`, `steadyConsumption_ge_of_lower`, `transition_gain`, `transition_loss_of_more_capital`, `steadyConsumption_lt_of_lower_efficient` |
| §3A.2, pp. 193–194 | Ponzi debt shrinks relative to output iff `r < z`; bubbles are sustainable iff `r ≤ z` | `DynamicInefficiency.ponzi_ratio_tendsto_zero`, `ponzi_ratio_ge`, `bubble_affordable`, `bubble_unaffordable` |
| §3A.3, p. 194 | `r > z` iff the profit share exceeds the investment share | `DynamicInefficiency.efficiency_iff_profit_share` |

## Exercises (pp. 195–197)

| Book | Claim | Lean |
| --- | --- | --- |
| Ex 1 | Three-period lives with a borrowing-constrained young: optimality, saving by generation, saving rates, and the effect of `e` reversing sign when the constraint binds | `DemographicsSaving.three_period_optimal`, `ex1_unconstrained_saving`, `ex1_constraint_binds_iff`, `ex1_constrained_saving`, `ex1_saving_rate_unconstrained`, `ex1_saving_rate_constrained`, `ex1_unconstrained_rate_anti_e`, `ex1_constrained_rate_mono_e`, `ex1d_saving` |
| Ex 2(a) | With `r^A < n`, a rise in `r` benefits every generation | `OLGGainsFromTrade.hasDerivAt_lifetimeUtility_growth`, `growth_slope_pos_iff`, `capitalCD_autarky`, `autarkyRateCD` |
| Ex 2(b) | **False as stated**: refuted, and the corrected local version proved | `OLGGainsFromTrade.lifetimeUtility_wageCD`, `hasDerivAt_lifetimeUtility_CD`, `slope_CD_pos_iff`, `lifetimeUtility_CD_strictMonoOn`, `lifetimeUtility_CD_strictAntiOn`, `everyone_worse_off_corrected`, `lifetimeUtility_CD_tendsto_atTop`, `exists_rate_below_autarky_young_gain`, `counterexample_everyone_worse_off` |
| Ex 3 | Blanchard's perpetual youth: population, annuities, budget constraint, aggregate dynamics, the effect of debt | `PerpetualYouth.blanchard_population`, `blanchard_annuity_zero_profit`, `blanchard_budget`, `blanchard_consumption_function`, `blanchard_aggregate_accumulation`, `blanchard_aggregate_consumption`, `blanchard_law_of_motion`, `blanchard_debt_tax`, `blanchardSteadyB_debt`, `blanchard_debt_lowers`, `blanchard_steady_consumption`, `blanchardSteadyB_ricardian` |
| Ex 4 | Debt and Foreign steady-state welfare | `TwoCountryOLG.TwoCountry.foreignUtility`, `foreignUtility_hasDerivAt`, `foreignUtility_deriv_pos_iff`, `foreignUtility_deriv_neg_iff`, `foreign_welfare_falls_with_debt` |
| Ex 5 | Weil consumption with an arbitrary debt path | `PerpetualYouth.weil_debt_path_consumption`, `weil_debt_path_consumption_book` |
| Ex 6 | Barro tax smoothing: taxes matter only through their distortions; constant taxes are uniquely optimal; deficits track temporary spending | `TaxSmoothing.consolidated_wealth`, `consumption_lower_of_distortion`, `pv_sq_ge_of_pv_eq`, `pv_sq_gt_of_pv_eq`, `constant_tax_optimal`, `constant_tax_level`, `deficit_eq_spending_gap`, `government_assets_constant` |
