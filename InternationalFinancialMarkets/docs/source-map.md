# Source map

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Chapter 5, “Uncertainty and International Financial Markets” (pp. 269–348), and
the Supplement to Chapter 5 (pp. 742–744). Equation numbers are the book's, cited
as (5.n) or (n); page numbers are book pages. Lean names are relative to
`ObstfeldRogoff.InternationalFinancialMarkets`; the rows list the main
declarations, and each module's docstring maps its remaining results. Where a
statement adds a hypothesis the book leaves implicit, or departs from the printed
claim, see [corrections](corrections.md).

Uncertainty is a finite set of states with probabilities (`StateSpace`, in
`Model`); expectations, covariances and correlations are finite sums
(`Probability`).

## Moments (used throughout)

| Book | Claim | Lean |
| --- | --- | --- |
| (5.52) | `E[XY] = E[X]E[Y] + Cov(X, Y)` | `StateSpace.expect_mul_eq` |
| fn 32, p. 308 | `Cov(a + X, Y) = Cov(X, Y)` | `StateSpace.cov_const_add` |
| fn 38 | Cauchy–Schwarz for covariances | `StateSpace.cov_sq_le`, `abs_cov_le`, `abs_corr_le_one` |
| fn 18, p. 290 | Positive affine functions have correlation one | `StateSpace.corr_affine` |

## §5.1 A small country facing complete markets

| Book | Claim | Lean |
| --- | --- | --- |
| §5.1.2, p. 272 | Arrow–Debreu securities span every payoff; bonds are redundant | `SmallCountry.ad_span`, `bond_redundant` |
| (7), p. 277 | No arbitrage iff `Σ p = 1` and `p ≥ 0` | `SmallCountry.noArbitrage_iff` |
| (2), (3), (4), (18) | The period budgets, the present-value budget and (18) are equivalent | `SmallCountry.budget_iff`, `budget_pv_iff` |
| (5), (6), (8), (9) | First-order conditions: MRS = price, bond Euler equation, ratio form; sufficiency under concavity | `SmallCountry.mrs_eq_price`, `bond_euler`, `mrs_ratio_eq_price_ratio`, `foc_sufficient` |
| (5), (6), (8), (9), pp. 276–277 | **Necessity**: any interior optimum satisfies the first-order conditions (equality or ≤ budget); the budget binds | `SmallCountry.foc_of_isPlanOptimum`, `foc_necessary`, `mrs_eq_price_of_optimum`, `bond_euler_of_optimum`, `mrs_ratio_of_optimum`, `budget_binds_of_optimum` |
| (4), (18) | For concave differentiable `u`: optimum iff first-order conditions | `SmallCountry.optimum_iff_foc_budget_eq`, `optimum_iff_foc_budget_le`, `foc_iff` |
| (10), p. 277 | Full insurance iff prices are actuarially fair | `SmallCountry.full_insurance_iff_fair`, `full_insurance_iff_fair_ratio` |
| (11)–(13), pp. 278–279 | CRRA: log-ratio of state consumptions; Arrow–Pratt coefficient `ρ` | `SmallCountry.crra_log_ratio`, `crra_arrow_pratt` |
| (15)–(17), fn 9, p. 280 | Log utility: consumption demands and the current account | `SmallCountry.log_consumption_demands`, `log_current_account` |
| fn 10, p. 280 | `Σ p Y₂ = E Y₂` iff `p = π` (corrected) | `SmallCountry.value_eq_expectation_iff`, `value_eq_expectation_two_iff` |
| (18), (19), p. 281 | Walras's law; revealed preference | `ComparativeAdvantage.walras_law`, `revealed_preference` |
| §5.1.7, pp. 281–282 | **Comparative advantage for arbitrary preferences**; one state gives the Chapter 1 result | `ComparativeAdvantage.comparative_advantage`, `comparative_advantage_utility`, `comparative_advantage_one_state` |
| (23)–(25), p. 283 | CES demands cost `Z₂` and attain `Z₂/P`; stage-2 optimality | `TwoStageBudgeting.demand_cost`, `cesIndex_demand`, `cesIndex_le`, `lifetime_le_two_stage` |
| p. 285 | `P ≤ 1`, with equality iff `p = π` | `TwoStageBudgeting.priceIndex_le_one` |
| (27), p. 284 | First-stage Euler equation and the consumption function | `TwoStageBudgeting.euler_27`, `consumption_27` |
| (21)–(22), (27), pp. 282–284 | Stage 1 solved exactly by (27): sufficiency, necessity, uniqueness | `TwoStageBudgeting.stageOne_optimal`, `stageOne_unique`, `stageOne_maximiser_iff_27` |
| (20), pp. 282–284 | The two-stage plan is the unique maximiser of (20) over all state-contingent plans | `TwoStageBudgeting.two_stage_optimal_of_index` |
| fn 13, p. 284 | The log cases `ρ = 1`, `σ = 1` | `TwoStageBudgeting.geo_stage_two`, `risk_stage_two`, `isoU` |
| (26), pp. 283–284 | **Epstein–Zin / Kreps–Porteus preferences**: as printed; unique two-stage optimum | `TwoStageBudgeting.ezUtility_eq_printed`, `ez_two_stage_optimal` |
| p. 284 | (26) equals expected utility when `σ = 1/ρ`, and ranks plans like it only then | `TwoStageBudgeting.ez_eq_expectedUtility`, `ez_le_iff_expectedUtility`, `ez_same_ordering_iff` |
| fn 14, p. 285 | Current account under (26) | `TwoStageBudgeting.ez_current_account_sign`, `ez_consumption_vs_certainty` |
| fn 14, p. 285 | The sign of the current account against `r^CA` | `TwoStageBudgeting.current_account_sign_rCA` |
| pp. 284–285 | Consumption against the certainty benchmark (`σ ≷ 1`); special cases | `TwoStageBudgeting.consumption_vs_certainty`, `consumption_sigma_one`, `consumption_fair_prices`, `current_account_fair_rate` |

## §5.2 Global equilibrium

| Book | Claim | Lean |
| --- | --- | --- |
| (30)–(33), pp. 286–287 | AD prices, relative prices, `p(s)` and the world interest rate | `GlobalEquilibrium.GlobalEqm.ad_price`, `price_ratio`, `price_formula`, `interest_formula` |
| p. 287 | Prices are fair iff there is no aggregate risk | `GlobalEquilibrium.GlobalEqm.fair_iff_no_aggregate_risk` |
| (35)–(36), p. 288 | Constant consumption shares across states; equal consumption growth | `GlobalEquilibrium.GlobalEqm.C2_eq`, `consumption_ratio_across_states`, `growth_eq`, `growth_eq_world` |
| p. 289, fn 16 | The share is the wealth share; closed form | `GlobalEquilibrium.GlobalEqm.share_eq_wealth_share`, `share_closed_form` |
| fn 17, p. 289 | The equilibrium solves a planner's problem | `GlobalEquilibrium.planner_foc`, `GlobalEqm.planner_optimal` |
| (37), fn 18, p. 290 | Different `ρ`, `β`: log growth relation and correlation one | `GlobalEquilibrium.log_growth_relation`, `corr_growth_eq_one` |
| (39), p. 293 | HARA aggregation of the per-capita Euler equation and budget | `Aggregation.hara_aggregation`, `perCapita_budget` |
| p. 294 | Geometric-mean aggregation with harmonic-mean `ρ̃` | `Aggregation.geometric_aggregation` |
| fn 21, p. 293 | With bonds only, aggregation fails | `Aggregation.bonds_only_aggregation_fails` |
| (40)–(41), p. 298 | Investment first-order condition, `Σ p A F′ = r`, investment Euler equation | `GlobalEquilibrium.investment_foc`, `investment_rate`, `investment_euler` |
| §5.2.4.1, pp. 298–299 | Log utility and linear production: prices and world investment | `GlobalEquilibrium.log_investment_price`, `log_linear_world_investment` |
| Ex 2, p. 345 | Equilibrium; indeterminacy of the date-2 allocation | `GlobalEquilibrium.exercise2`, `exercise2_indeterminate` |

## §5.3 Portfolio diversification and spanning

| Book | Claim | Lean |
| --- | --- | --- |
| (42)–(43), pp. 302–303 | Budget constraints with bonds and shares | `PortfolioDiversification.PortfolioEconomy.budget_date1`, `budget_date2` |
| (44), (49)–(50), pp. 302–303 | Bond and share Euler equations at the equilibrium prices; market clearing | `PortfolioDiversification.PortfolioEconomy.bond_euler`, `share_euler`, `market_clearing` |
| §5.3.3, p. 303 | Share values are AD values; complete-markets conditions hold | `PortfolioDiversification.PortfolioEconomy.V_eq_ad_value`, `ad_euler`, `ad_budget`, `ad_prices_normalised` |
| Ex 4, p. 346 | Log utility: (89)–(90), prices, budgets, clearing | `PortfolioDiversification.PortfolioEconomy.logV_eq_sharePrice`, `log_budgets`, `log_eulers`, `log_clearing` |
| Ex 5, p. 347 | CARA: complete markets, half shares plus a loan, linear sharing | `PortfolioDiversification.Exercise5.exercise5a`, `exercise5b`, `exercise5b_efficient`, `exercise5c_sharing`, `exercise5c_support` |
| (77), p. 336 | Spanning iff `rank R = S` | `Spanning.spans_iff_rank` |
| p. 336 | `rank R ≤ min(S, N+1)`; AD securities replicated by `R⁻¹` | `Spanning.rank_le_min`, `not_spans_of_card_lt`, `ad_security_replication` |
| p. 304 | **`S ≤ N+1` is neither sufficient nor necessary** (corrected) | `Spanning.card_le_not_sufficient`, `efficient_without_spanning` |

## §5.4 Asset pricing

| Book | Claim | Lean |
| --- | --- | --- |
| (51)–(53), pp. 306–307 | `V = E[MY]`, bond price `E[M] = 1/(1+r)`, `V = E[Y]/(1+r) + Cov(M, Y)`, consumption CAPM | `AssetPricing.price_eq_expect_sdf`, `expect_sdf_eq_bond_price`, `price_eq_discounted_mean_add_cov`, `consumption_capm` |
| §5.4.1.3, pp. 308–309 | Incomplete markets: common `Cov(Mⁿ, rᵐ)`; investment valued identically by every owner | `AssetPricing.cov_sdf_return_incomplete`, `investment_value_invariant`, `investment_value_hasDerivAt` |
| fn 38 | Hansen–Jagannathan bound | `AssetPricing.hansen_jagannathan`, `hansen_jagannathan_div` |
| p. 311 | Equity premium, exact for the linearised discount factor; Mankiw–Zeldes `ρ` | `AssetPricing.equity_premium_linear_sdf`, `mankiw_zeldes_rho` |
| p. 313 | Lognormal riskless rate; the 3.34 percent figure | `AssetPricing.log_riskless_rate_lognormal`, `riskless_rate_mehra_prescott` |
| (59)–(61), pp. 316–317 | Infinite-horizon pricing (deterministic economy): truncated identity and limit under no bubbles; CRRA form | `AssetPricing.price_truncated`, `price_eq_present_value`, `price_crra_world_output`, `truncated_price_decomposition` |
| (57), p. 315 | Euler equation at every history of an event tree; conditional expectations and iterated expectations | `InfiniteHorizonPricing.EulerEq`, `condE.add_eq_iter`, `condE_eq_sum_condProb`, `condE_root_eq_sum_histProb` |
| (59), p. 316 | **Stochastic infinite horizon**: K-step identity; price = present-value series under no bubbles; the series solves (57) | `InfiniteHorizonPricing.price_k_step`, `price_eq_series`, `price_hasSum`, `euler_of_series` |
| p. 316 | Bubbles: price = fundamental iff no bubble; non-uniqueness otherwise | `InfiniteHorizonPricing.bubble_recursion`, `price_eq_fundamental_iff`, `euler_nonunique_without_noBubble` |
| p. 316 | No bubbles derived: bounded `u′V` and `β < 1`; unique bounded price, series convergent | `InfiniteHorizonPricing.noBubble_of_bounded`, `unique_bounded_price` |
| (60), fn 44, pp. 316–317 | Riskless discounting plus covariances; `k`-period bond prices | `InfiniteHorizonPricing.price_eq_riskless_plus_cov`, `price_k_step_riskless_cov`, `bond_price_eq_discountR` |
| (61), p. 317 | CRRA pricing off world output, with `C = μY^W` derived from all countries' first-order conditions | `InfiniteHorizonPricing.price_crra_world_output_derived`, `price_crra_world_output_bounded` |

## §5.5 Nontradables, and the cost of consumption variability

| Book | Claim | Lean |
| --- | --- | --- |
| (64)–(67), pp. 320–321 | Efficiency in tradables from the Euler equations and nontradables clearing | `Nontradables.efficiency_tradables`, `euler_nontradables_of_intratemporal` |
| (68)–(69), p. 322 | Claim prices do not depend on whose MRS is used | `Nontradables.claim_price_any_country`, `claim_price_independent` |
| (70)–(71), p. 323 | Preference shocks | `Nontradables.efficiency_preference_shocks` |
| (74), p. 326; fn 48 | Additive utility: tradables growth equalised; home-bias portfolio | `Nontradables.additive_tradables_growth_equal`, `additive_tradables_growth_world`, `home_bias_equilibrium` |
| (72)–(73), pp. 324–328 | CES–CRRA: derivatives, cross-partial sign, additive iff `θρ = 1`, revenue, (73) exactly | `Nontradables.cesCross_sign`, `cesCrra_additive_iff`, `ces_revenue_strictMono_iff`, `ces_loglinear_exact` |
| pp. 328–329 | Cobb–Douglas: payoffs perfectly correlated, portfolios indeterminate | `Nontradables.cd_revenue`, `cd_payoff_corr_one` |
| (75), p. 330 | Lucas's welfare cost: closed forms, **exact simplification**, bounds, `≈ 0.35%` | `AssetPricing.lucas_lifetime_utility`, `lucas_tau_simplifies`, `lucas_tau_iff`, `lucas_tau_bounds`, `lucas_tau_numeric` |

## §5.6 Overlapping generations and risk sharing

| Book | Claim | Lean |
| --- | --- | --- |
| p. 333 | The young agent's plan is optimal (log utility) | `OLGRiskSharing.young_plan_optimal` |
| p. 334 | The cohort share `μ_t`, interest rate and prices satisfy the first-order conditions and budget; `μ + μ* = 1`, `Σ p = 1` | `OLGRiskSharing.cohort_equilibrium`, `cohortShare_add`, `cohortPrice_sum` |
| p. 334; fn 16 | Every within-cohort equilibrium has the book's `μ_t` and prices | `OLGRiskSharing.cohort_equilibrium_unique` |
| (76), p. 334 | Aggregate consumption | `OLGRiskSharing.aggregate_consumption` |
| p. 334 | The half-of-world-output example | `OLGRiskSharing.cohortShare_half` |
| Ex 6(b), p. 347 | Lucas two-good model: `C_X = X/2`, `C_Y = Y/2`, `p = u_Y/u_X` | `OLGRiskSharing.lucas_allocation` |
| Ex 6(a), (c), p. 347 | Claim prices as truncated present values on a finite Markov chain; the limit | `OLGRiskSharing.lucas_claim_price`, `lucas_claim_price_limit` |
| Ex 6(d), p. 347 | Riskless bond prices | `OLGRiskSharing.lucas_riskless_prices` |
| Ex 6(a), p. 347 | Infinite horizon: finance constraint and Euler equations | `InfiniteHorizonPricing.lucas_perturbation_feasible`, `lucas_euler_equations` |
| Ex 6(b), p. 347 | No trade is globally optimal among admissible plans (transversality proved); every equilibrium allocation is `(X/2, Y/2)` | `InfiniteHorizonPricing.lucas_noTrade_optimal`, `lucas_allocation_unique` |
| Ex 6(c)–(d), p. 347 | Claim prices are the unique bounded solutions and equal convergent series; riskless rates | `InfiniteHorizonPricing.markov_price_unique`, `lucas_claim_prices_infinite`, `lucas_riskless_rates` |

## Appendix 5B Autarky interest rates and the current account

| Book | Claim | Lean |
| --- | --- | --- |
| (78)–(79), p. 338 | `r^CA` and the autarky rate | `SmallCountry.rCA_formula`, `rA_formula` |
| fn 50–51, p. 338 | Sign of `CA₁` is that of `r − r^CA`, not `r − r^A` (counterexample) | `SmallCountry.current_account_sign_iff`, `current_account_sign_not_autarky_rate`, `no_output_risk` |
| (80)–(81), pp. 338–339 | Autarky prices; the current account from autarky and world prices | `SmallCountry.autarky_prices_log`, `current_account_autarky_prices` |
| pp. 339–340 | Gross flows | `SmallCountry.gross_flows_balanced` |
| Ex 1, p. 345 | Gross AD purchases | `SmallCountry.exercise1_gross_purchases` |
| Ex 3, p. 346 | Quadratic utility: certainty equivalence, the Kuhn–Tucker corner (corrected), complete markets | `SmallCountry.quad_euler_iff`, `quad_lifetime_eq`, `quad_binding`, `quad_nonbinding`, `quad_complete_markets` |
| Ex 3(a), p. 346 | Infinite horizon: consumption martingale and the permanent-income rule, and its converse | `InfiniteHorizonPricing.quadratic_infinite_horizon_consumption`, `quadratic_permanent_income_rule` |

## Appendix 5C An event tree with many dates

| Book | Claim | Lean |
| --- | --- | --- |
| p. 341 | History probabilities sum to one; chain rule | `EventTree.Tree.histProb_sum_eq_one`, `condProb_chain` |
| (82)–(84), pp. 341–342 | First-order conditions, budget and concavity give the optimal plan | `EventTree.arrowDebreu_plan_optimal` |
| (85), p. 342 | Bond Euler equation; ratio of first-order conditions | `EventTree.euler_bond`, `foc_ratio` |
| p. 342 | CRRA: `C = μY^W` at the closed-form prices, which sum to one; `μ` the present-value share | `EventTree.crra_foc`, `crraPrice_sum`, `budget_of_share` |
| p. 342 | Constant shares from the first-order conditions and market clearing | `EventTree.crra_constant_share` |
| p. 342 | `R_{1,t} = β^{t−1}E[(Y^W_t)^{−ρ}]/(Y^W_1)^{−ρ}` | `EventTree.crra_interest_factor` |
| (82)–(84), pp. 341–342 | **Infinite horizon**: first-order conditions, infinite budget and concavity give an optimum; necessity at every history | `EventTree.arrowDebreu_optimal_infinite`, `arrowDebreu_foc_necessary`, `euler_bond_plan` |
| p. 342 | The CRRA and log equilibria of the infinite economy; `μ` pinned by the infinite budget | `EventTree.crra_equilibrium_infinite`, `log_equilibrium_infinite`, `crra_constant_share_infinite`, `crra_share_of_budget`, `crraDatePrice_sum` |

## Appendix 5D Dynamic consistency

| Book | Claim | Lean |
| --- | --- | --- |
| fn 53, p. 344 | Bayes rule `π(h_s∣h_{t+1}) = π(h_s∣h_t)/π(h_{t+1}∣h_t)` | `EventTree.Tree.bayes_rule`, `histProb_div_date2` |
| (87)–(88), p. 344 | The date-1 plan satisfies the date-2 first-order conditions | `EventTree.foc_date2_ratio`, `foc_date2` |
| pp. 343–344 | The date-1 plan is optimal when markets reopen at date 2 | `EventTree.dynamic_consistency` |
| (86)–(88), p. 344 | Dynamic consistency over the infinite horizon | `EventTree.dynamic_consistency_infinite`, `dateTwo_restriction_admissible` |

## Supplement to Chapter 5

| Book | Claim | Lean |
| --- | --- | --- |
| p. 743 | Log utility: the Euler equation holds iff `μ = 1 − β` | `EventTree.log_share_iff` |
| p. 744 | CRRA: the Euler equation iff the `μ_t` recursion | `EventTree.crra_share_recursion`, `share_formula_iff` |
| p. 744 | iid returns: `μ = 1 − [βE(1+r°)^{1−ρ}]^{1/ρ}`, the unique fixed point in `(0, 1)`; `1 − β` at `ρ = 1` | `EventTree.crra_iid_share`, `crra_iid_share_log` |
| p. 742 | Wealth accumulation; the Bellman equation solved exactly by `V = μ^{−ρ}W^{1−ρ}/(1−ρ)`, maximum at `C = μW` | `ConsumptionPortfolio.wealth_accumulation_book`, `bellman_crra`, `bellman_guess_pins_share`, `bellman_log` |
| (1)–(2), pp. 742–743 | Consumption Euler equation; the portfolio condition, sufficient and necessary; an optimal portfolio exists under no arbitrage | `ConsumptionPortfolio.crraShare_euler`, `portfolio_condition_sufficient`, `portfolio_condition_necessary`, `exists_optimal_portfolio`, `exists_optimal_log_portfolio` |
| pp. 742–744 | **Verification**: `C = μW` with the optimal portfolio is optimal over the infinite horizon (transversality proved) | `ConsumptionPortfolio.verification_crra_of_noArbitrage`, `verification_log_of_noArbitrage` |
| pp. 743–744 | Log utility with any return process: `μ = 1 − β`, the myopic portfolio, `V_t = log W/(1−β) + K_t` | `ConsumptionPortfolio.myopicPort_spec`, `logConstT_recursion`, `bellman_log_node`, `verification_log_tree` |
| p. 744 | History-dependent returns: the `μ_t` recursion has a solution, and `C = μ_tW` is optimal | `ConsumptionPortfolio.exists_share_recursion_solution`, `verification_varying_returns` |
