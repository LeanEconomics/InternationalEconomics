# Source map

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Chapter 2, “Dynamics of Small Open Economies” (pp. 59–128), and the Supplements
to Chapter 2, A–C (pp. 715–741). Equation numbers are the book's (`SA`, `SC`
for the supplements); page numbers are book pages. Lean names are relative to
`ObstfeldRogoff.SmallOpenEconomyDynamics`. The book's date `t` is date 0 in
the Lean statements. Where a statement adds a hypothesis the book leaves
implicit or departs from the printed claim, see [corrections](corrections.md).

The whole chapter is covered: the deterministic core (phase 2a) and the
stochastic model, durables, firms and the appendices (phase 2b). Probability
uses Mathlib's conditional expectation `μ[X|ℱ t]` with respect to a filtration;
the book's Euler equations under uncertainty (2.28)–(2.29) enter as hypotheses
in conditional-expectation form.

## §2.1 A small economy with many periods (pp. 60–73)

| Book | Claim | Lean |
| --- | --- | --- |
| (2.2)–(2.3), p. 60 | Current account and period budget constraint | `Economy.ca`, `Economy.Flow`, `Economy.flow_iff`, `BudgetConstraint.flow_iff_recursion`, `BudgetConstraint.flow_shiftPaths` |
| (2.4), p. 61 | Finite-horizon budget constraint; equivalent, for all horizons, to the period constraints | `PresentValue.discounted_telescope`, `BudgetConstraint.finite_identity`, `BudgetConstraint.finite_ibc`, `BudgetConstraint.flow_iff_finite_ibc` |
| fn 1, p. 62 | Finite geometric sum | `PresentValue.sum_range_disc_pow` |
| (2.10), p. 62 | Constant consumption and the budget constraint give `C = rW/(1 + r)` | `FundamentalCurrentAccount.flat_consumption_level`, `FundamentalCurrentAccount.annuity_wealth` |
| (2.12), p. 64 | The naive limit: a constant plan explodes unless `C̄ = rB + Ȳ` | `BudgetConstraint.naive_path`, `naive_tendsto_atTop`, `naive_tendsto_atBot`, `naive_limit_zero_iff`, `naive_transversality_iff` |
| (2.13) ⇔ (2.14), p. 64 | **Period constraints + transversality ⇔ intertemporal budget constraint** | `PresentValue.tendsto_discounted`, `PresentValue.discounted_tendsto_zero_iff`, `BudgetConstraint.tendsto_terminal`, `BudgetConstraint.transversality_iff_ibc` |
| fn 4, p. 65 | No-Ponzi inequality ⇔ PV(C + I) ≤ wealth; strict iff an unrequited gift | `PresentValue.noPonzi_iff`, `BudgetConstraint.noPonzi_iff_ibc_le`, `BudgetConstraint.terminal_pos_iff_ibc_lt` |
| p. 65 | Debt limit from nonnegative consumption | `BudgetConstraint.debt_limit`, `BudgetConstraint.debt_limit_debtor` |
| p. 66 | Solvency as the PV of trade surpluses; growth below `r` gives summability | `BudgetConstraint.tradeBalance`, `pv_tradeBalance`, `ibc_iff_trade_surplus`, `transversality_iff_trade_surplus`, `PresentValue.summable_of_growth` |
| p. 68 | Steady debt–output ratio: `TB/Y = −(r − g)B/Y = −B/[Y/(r − g)]` | `BudgetConstraint.steady_ratio_trade_balance`, `output_claim_value`, `steady_ratio_burden`, `steady_ratio_transversality`, `PresentValue.pv_geometric` |
| (2.5), p. 61; (2.11), p. 63 | Lifetime utility; the Euler equation is necessary | `ConsumptionOptimality.lifetimeUtility`, `ConsumptionOptimality.euler_of_optimal` |
| pp. 62–65; SA.1 | Euler + binding budget ⇒ optimal (concave `u`); strictly and uniquely so for strictly concave `u` | `ConsumptionOptimality.isOptimal_of_euler`, `ConsumptionOptimality.lifetimeUtility_lt_of_euler`, `euler_iterate`, `discounted_marginal_utility` |
| pp. 64–65; SA(4) | The budget constraint binds at an optimum | `ConsumptionOptimality.pv_eq_of_optimal` |
| p. 62, p. 71 | Consumption is flat, rises or falls as `β(1 + r)` is `=, >, <` one | `ConsumptionOptimality.flat_of_beta_mul`, `ConsumptionOptimality.tilt_up`, `ConsumptionOptimality.tilt_down` |
| (2.16), p. 71 | Geometric consumption growth `γ < 1 + r` and the budget give `C₀ = (1 + r − γ)W/(1 + r)` | `FundamentalCurrentAccount.geometric_consumption_level` |
| §2.1.4, p. 72; SA(5) | Dynamic consistency | `ConsumptionOptimality.continuation_optimal` |
| p. 73 | Strotz: quasi-hyperbolic preferences are time-inconsistent | `ConsumptionOptimality.strotz_mrs_differ` |
| (2.9), p. 62 | Finite-horizon consumption with `β(1 + r) = 1`, and its limit (2.10) | `ConsumptionFunctions.finite_horizon_consumption`, `ConsumptionFunctions.finite_horizon_tendsto` |
| fn 2, p. 62 | `C = rW/(1 + r)` is exactly the rule that keeps wealth constant | `ConsumptionFunctions.wealth_unchanged_iff`, `ConsumptionFunctions.annuity_wealth_constant` |
| p. 70 | CRRA marginal utility and strict concavity | `ConsumptionFunctions.crra`, `crra_hasDerivAt`, `crra_strictConcaveOn` |
| (2.15), p. 70 | CRRA Euler equation ⇔ `C_{s+1} = (1 + r)^σ β^σ C_s` | `ConsumptionFunctions.crra_euler_iff`, `crra_euler_path_iff` |
| (2.16), p. 71 | `C₀ = [1 − (1 + r)^{σ−1}β^σ]W`, and the path is **optimal** when `(1 + r)^{σ−1}β^σ < 1` (and for log utility) | `ConsumptionFunctions.crra_consumption_function`, `crra_isOptimal`, `log_isOptimal`, `crraGrowth_eq` |
| p. 71; fn 8 | No optimum when `(1 + r)^{σ−1}β^σ ≥ 1`, which needs `σ > 1` | `ConsumptionFunctions.crra_no_optimum`, `ConsumptionFunctions.one_lt_sigma_of_one_le_tilt` |
| p. 71 | Consumption is decreasing in `β` at given `r` | `ConsumptionFunctions.crra_consumption_strictAnti_beta` |
| SA(6)–(10), pp. 718–721 | The CRRA value function satisfies the Bellman equation, uniquely maximised at the (2.16) policy | `ConsumptionFunctions.crra_bellman_fixed_point`, `crra_bellman_strict_max`, `crra_bellman_isGreatest`, `crra_policy_formula` |
| (2.72)–(2.73), p. 115 | Endogenous labour: intratemporal condition and consumption growth; rising wages tilt consumption up when `σ < 1` | `ConsumptionFunctions.labourUtility_hasDerivAt_C`, `labourUtility_hasDerivAt_leisure`, `labour_intratemporal_iff`, `labour_consumption_growth`, `labour_tilt_up_of_wage_growth` |

## §2.2 Dynamics of the current account (pp. 74–78)

| Book | Claim | Lean |
| --- | --- | --- |
| (2.17), p. 74 | Permanent value and its annuity property | `PresentValue.pv`, `PresentValue.permanent`, `PresentValue.pv_permanent`, `pv_const`, `permanent_const`, `permanent_add`, `permanent_sub` |
| (2.18), p. 74 | **`CA = (Y − Ỹ) − (I − Ĩ) − (G − G̃)`** | `FundamentalCurrentAccount.fundamental_current_account`, `FundamentalCurrentAccount.fundamental_current_account_of_flat` |
| pp. 74–75 | Permanent shocks leave the current account unchanged; a temporary one raises it by `d/(1 + r)` | `FundamentalCurrentAccount.permanent_shock_no_ca`, `FundamentalCurrentAccount.temporary_shock_ca` |
| (2.20), p. 75 | Tilted fundamental equation | `FundamentalCurrentAccount.tilted_current_account`, `tilted_current_account_of_growth`, `tilt_term_neg_iff` |
| (2.21)–(2.23), pp. 76–77 | Variable-rate discount factors and budget constraint | `PresentValue.varDisc`, `varDisc_telescope`, `varDisc_tendsto_zero_iff`, `varDisc_sub_succ` |
| fn 13, p. 78 | `Σ_{s>t} R_{t,s} r_s = 1` when the discount factors vanish | `PresentValue.hasSum_rate_mul_varDisc`, `PresentValue.rate_mul_varDisc_zero_rates` |
| (2.26), p. 78; fn 14 | Variable-rate fundamental equation | `FundamentalCurrentAccount.variable_rate_current_account`, `variable_rate_current_account_flat` |

## §2.5.2 Investment with adjustment costs: Tobin's q (pp. 105–114)

| Book | Claim | Lean |
| --- | --- | --- |
| (2.62)–(2.63), pp. 106–107 | Investment first-order condition `I = (q − 1)K/χ` | `TobinQ.hasDerivAt_lagrangian_investment`, `TobinQ.investment_foc_iff` |
| (2.64), p. 107 | Investment Euler equation | `TobinQ.hasDerivAt_lagrangian_capital`, `TobinQ.capital_foc_iff`, `TobinQ.marginalEarnings` |
| (2.65), p. 107 | Forward solution for `q` ⇔ no bubble (**corrected indices**); the printed formula sums to `q_{t+1}` | `TobinQ.forward_iterate`, `TobinQ.q_forward_solution`, `TobinQ.hasSum_of_tail`, `TobinQ.tail_of_hasSum`, `TobinQ.book_formula_sums_to_next_q`, `TobinQ.book_formula_eq_q_iff` |
| (2.66)–(2.67), p. 108 | Exact dynamics; unique steady state `q̄ = 1`, `AF_K = r`; `ΔK = 0 ⇔ q = 1` | `TobinQ.exact_dynamics`, `TobinQ.steady_state_iff`, `TobinQ.steady_state_unique`, `TobinQ.capital_stationary_iff` |
| (2.68)–(2.69), pp. 108–109 | Linearisation; the `Δq = 0` locus slopes down | `TobinQ.hasDerivAt_capital_dynamics_q`, `_K`, `hasDerivAt_q_dynamics_q`, `_K`, `_quadratic`, `TobinQ.dq_locus` |
| p. 109; SC pp. 736–737 | **Saddle path**: `det = 1 + r`, real roots `0 < ω₂ < 1 < ω₁`; the saddle path solves, converges monotonically, has `q > 1 ⇔ K₀ < K̄`, and is the unique bounded solution | `TobinQ.qMatrix_det_trace`, `qDisc_eq`, `omega_roots`, `omega_saddle`, `cobbDouglas_curvature`, `saddle_path_solves`, `saddle_path_tendsto`, `saddle_q_above_one_iff`, `saddle_monotone`, `saddle_path_unique` |
| (2.70), p. 112 | **Marginal q = average q** (Hayashi) | `TobinQ.euler_of_homogeneous`, `TobinQ.hayashi_step`, `TobinQ.marginal_q_eq_average_q` |
| p. 113 | Rate-of-return form of (2.64) | `TobinQ.rate_of_return_form` |
| App. 2B.2, p. 124 | Bubble identity: `q_t − PV = lim (1 + r)^{−T} q_{t+T}` | `TobinQ.bubble_identity`, `TobinQ.bubble_overvalues` |

## §2.3 A stochastic current account model (pp. 79–96)

| Book | Claim | Lean |
| --- | --- | --- |
| (2.30)–(2.31), p. 81; fn 18 | **Hall**: quadratic utility and `(1 + r)β = 1` make consumption a martingale; `E_t C_s = C_t` | `StochasticConsumption.quadU`, `hasDerivAt_quadU`, `hall_random_walk`, `hall_martingale`, `hall_condExp_future` |
| (2.32), p. 81 | Certainty-equivalent consumption, from the expected budget recursion and named limit hypotheses | `StochasticConsumption.condExp_budget_step`, `certainty_equivalence`, `certainty_equivalence_quadratic` |
| (2.33)–(2.34), p. 82 | AR(1) output forecasts `E_t(Y_{t+k} − Ȳ) = ρ^k(Y_t − Ȳ)` | `StochasticConsumption.ar1_condExp_step`, `ar1_forecast`, `output_forecast` |
| (2.36), p. 83 | Moving-average form (finite horizon) | `StochasticConsumption.ar1_moving_average` |
| (2.35), (2.37), p. 83 | Consumption and the current account under AR(1) output, for `|ρ| < 1 + r` | `StochasticConsumption.hasSum_disc_mul_pow`, `consumption_ar1`, `consumption_innovation_form`, `current_account_ar1`, `current_account_ar1_ae` |
| pp. 83–84 | Temporary shocks raise the current account, permanent ones do not; the predictable component | `StochasticConsumption.temporary_shock_effects`, `permanent_shock_effects`, `expected_current_account` |
| p. 85 | Deaton's numbers: a consumption response of 0.5 | `StochasticConsumption.deaton_consumption_response` |
| (2.38), p. 84 | Nonstationary output: forecasts, consumption, current-account deficit after a positive innovation | `StochasticConsumption.nonstationary_forecast`, `nonstationary_revision`, `consumption_nonstationary`, `current_account_nonstationary`, `consumption_more_volatile` |
| (2.40), p. 86; fn 23 | Risky capital: `E_t[AF'] = r − Cov_t(AF', u'(C_{t+1})/u'(C_t))` | `StochasticConsumption.condCov`, `condExp_mul_eq_add_condCov`, `condCov_const_add`, `risky_capital_return` |
| pp. 94–95; fn 32 | Precautionary saving: `u''' ≥ 0` makes `u'` convex; Jensen; a mean-preserving spread lowers current consumption; CRRA has `u''' > 0` | `StochasticConsumption.convexOn_of_third_deriv_nonneg`, `condExp_marginal_utility_ge`, `mps_raises_expected_marginal_utility`, `precautionary_saving_two_period`, `crra_third_derivative`, `crra_marginal_utility_convex` |
| SA.3, p. 722 | First-order and envelope conditions give the stochastic Euler equation | `StochasticConsumption.euler_of_bellman` |
### §2.3.5 The present-value test of the current account (pp. 90–93)

| Book | Claim | Lean |
| --- | --- | --- |
| (2.42), p. 90 | `CA_t = Z_t − E_t Z̃_t` with `Z = Y − I − G` | `PresentValueTest.Stochastic.forecastPermanent`, `PresentValueTest.one_sub_disc_eq` |
| (2.43), p. 90 | Summation by parts: deterministic finite, infinite and tail-only forms | `PresentValueTest.sum_disc_diff_eq`, `campbell_finite_horizon`, `tail_tendsto_zero`, `summable_disc_diff`, `campbell_deterministic`, `campbell_of_tail` |
| (2.43), p. 90 | **Campbell**: `CA_t = −Σ_{s>t} (1 + r)^{−(s−t)} E_t ΔZ_s`, with the expectation–sum interchange proved | `PresentValueTest.Stochastic.campbellPV`, `condExp_tsum_of_integral`, `ae_condExp_diff`, `campbell_eq_43` |
| fn 28, p. 91 | Matrix geometric series | `PresentValueTest.Stochastic.tsum_pow_succ_eq_mul_inv`, `summable_pow_of_rowSum_lt_one`, `summable_disc_smul_pow` |
| (2.45), p. 91 | VAR-predicted current account; the tested restriction | `PresentValueTest.Stochastic.condExp_var_pow`, `condExp_coord`, `var_forecast_sum`, `var_predicted_current_account`, `var_null_restriction` |
| fn 29, p. 92 | (2.43) holds on any coarser information set for which `CA_t` is known | `PresentValueTest.Stochastic.condExp_coarser_info`, `forecastSum_ae_eq_condExp`, `campbell_coarser_information` |

## §2.4 Consumer durables and the current account (pp. 96–99)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 97 | Euler equations for durables and bonds, from one-period perturbations | `Durables.durable_perturbation_feasible`, `hasDerivAt_durable_perturbation`, `durable_euler_of_isLocalMax`, `hasDerivAt_bond_perturbation`, `consumption_euler_of_isLocalMax` |
| (2.47), p. 97 | User cost `ι_s = p_s − (1 − δ)p_{s+1}/(1 + r_{s+1})` | `Durables.userCost`, `user_cost_of_euler`, `user_cost_of_euler_const` |
| (2.48), p. 97 | Durables intertemporal budget constraint ⇔ transversality | `Durables.durableAssets`, `durableAssets_succ`, `durables_ibc_iff`, `durableAssets_transversality` |
| (2.49)–(2.50), p. 98 | Consumption of nondurables and durables; `ι = p(r + δ)/(1 + r)` | `Durables.flat_nondurables`, `nondurables_consumption`, `durables_consumption`, `userCost_const`, `price_of_consumption_ratio` |
| p. 98 | With constant `p`, the durables stock is constant and later purchases are replacement only (zero if `δ = 0`) | `Durables.durables_stock_const`, `durables_purchases_after_t`, `durables_lump_sum` |
| (2.51), p. 99 | Modified fundamental equation; `ι → p` as `δ → 1` | `Durables.durables_current_account`, `userCost_full_depreciation`, `userCost_tendsto_price`, `durables_current_account_full_depreciation` |

## §2.5.1 Firms, the labour market and investment (pp. 99–105)

| Book | Claim | Lean |
| --- | --- | --- |
| (2.53)–(2.54), p. 101 | Share arbitrage `1 + r = (d + V')/V` | `FirmsAndWealth.share_arbitrage_iff`, `dividend_capital_gain_eq` |
| p. 101; (2.55) | Financial wealth accumulation; the budget constraint ⇔ transversality on `Q` | `FirmsAndWealth.wealth_accumulation`, `initial_financial_wealth`, `ibc_iff_transversality` |
| (2.56)–(2.57), p. 102 | Share price = PV of dividends ⇔ no bubble | `FirmsAndWealth.share_price_eq_pv_dividends_iff` |
| (2.58), p. 103 | Firm first-order conditions `AF_L = w`, `AF_K = r`; Euler's theorem | `FirmsAndWealth.labor_foc`, `capital_foc`, `euler_homogeneous`, `hasDerivAt_capital_partial`, `hasDerivAt_labor_partial` |
| (2.59), p. 104 | **Firm value equals the capital stock**; any gap grows at rate `r` | `FirmsAndWealth.firmDividend`, `dividend_eq_of_foc`, `tendsto_pv_capital_dividends`, `pv_capital_dividends`, `firm_value_sub_capital`, `firm_value_eq_capital_iff`, `firm_value_eq_capital` |
| (2.60)–(2.61), p. 104 | `Q = B + K`; consumption out of financial and human wealth | `FirmsAndWealth.financial_wealth_eq_bonds_add_capital`, `ibc_financial_human_wealth`, `ibc_financial_human_wealth_expost`, `consumption_financial_human` |
| pp. 104–105 | Saving and the current account in permanent-value form | `FirmsAndWealth.saving_eq_financial`, `saving_permanent`, `current_account_permanent` |
| fn 36, p. 102 | Modigliani–Miller | `FirmsAndWealth.modigliani_miller`, `modigliani_miller_consumer_wealth` |

## Appendix 2A Trend productivity growth (pp. 116–120)

| Book | Claim | Lean |
| --- | --- | --- |
| pp. 116–117 | `K/Y = α/r`; capital grows at `g`; `I = (αg/r)Y` | `TrendGrowth.capital_output`, `capital_growth`, `investment_share` |
| (2.74), p. 117 | The current account with trend growth | `TrendGrowth.current_account_trend` |
| (2.75)–(2.76), p. 117 | Debt–output recursion and its steady state `b̄ = −(1 − ς − αg/r)/(r − g)` | `TrendGrowth.debt_ratio_recursion`, `steady_debt_ratio`, `debt_ratio_deviation` |
| pp. 117–119, Fig. 2.12 | Convergence if `γ < 1 + g`, divergence if `γ > 1 + g`, constancy at the knife edge | `TrendGrowth.debt_ratio_tendsto`, `debt_ratio_diverges`, `debt_ratio_constant` |
| pp. 118–119 | `C/Y = (r + ϑ)(b − b̄)`: debt beyond `−b̄` needs negative consumption; `C/Y → 0`; `−b̄` is the PV of net output | `TrendGrowth.consumption_output_ratio`, `consumption_neg_below_steady`, `consumption_output_tendsto_zero`, `steady_ratio_eq_pv` |
| p. 119 | `b̄ = −15`, trade surplus 45% of GDP | `TrendGrowth.numerical_steady_ratio`, `numerical_trade_surplus`, `steady_trade_balance` |
| (2.77), pp. 119–120 | `1 + r = (1 + g*)^{1/σ}/β`; `g* = 3.68%`; 1.26% of the gap closed a year; half-life 55 years | `TrendGrowth.world_interest_rate`, `numerical_world_growth`, `fraction_closed`, `numerical_fraction_closed`, `numerical_half_life` |

## Appendix 2B Bubbles, Ponzi games and transversality (pp. 121–124)

| Book | Claim | Lean |
| --- | --- | --- |
| (2.78), p. 122 | Iterated asset Euler equation | `FirmsAndWealth.iterated_asset_euler`, `tendsto_iterated_asset_euler` |
| p. 123 | `β^T u'(C_T) = u'(C_0)(1 + r)^{−T}`; the limit condition ⇔ (2.57) | `FirmsAndWealth.discounted_marginal_utility`, `utility_bubble_iff` |
| p. 123; fn 54 | A positive limit ⇔ price above fundamentals; nonnegative prices rule out a negative one | `FirmsAndWealth.bubble_pos_iff_price_gt_pv`, `price_ge_pv_of_nonneg` |

## Supplement B Intertemporally nonadditive preferences (pp. 722–726)

| Book | Claim | Lean |
| --- | --- | --- |
| SB(3)–(4), p. 724 | A steady state requires `β(C̄)(1 + r) = 1` | `TrendGrowth.uzawa_steady_state` |

## Supplement C: linear difference equations (pp. 726–741)

| Book | Claim | Lean |
| --- | --- | --- |
| SC(1), SC(5), p. 727 | Scalar equation; general solution = one solution + `b₀aᵗ` | `LinearDifferenceEquations.ScalarSolves`, `scalar_general_solution`, `scalar_homogeneous_solution`, `scalar_add_homogeneous` |
| SC(4), p. 727 | Backward solution, the unique bounded solution on ℤ | `LinearDifferenceEquations.backwardSolution`, `scalar_backward_solution`, `scalar_backward_unique`, `scalar_stable_bounded` |
| SC(6)–(7), p. 728 | Particular solution; capital accumulation | `LinearDifferenceEquations.scalar_particular_solution`, `scalar_particular_solves`, `capital_accumulation_solution` |
| SC(9)–(10), pp. 729–730; fn 13 | Forward solution under a growth bound; general solution | `LinearDifferenceEquations.forwardSolution`, `forward_summable`, `scalar_forward_solution`, `scalar_forward_general_solution`, `forward_bounded` |
| p. 730 | Bubble-free uniqueness (`b₀ = 0`) under transversality, slower growth or boundedness; `b₀ ≠ 0` explodes; asset prices | `LinearDifferenceEquations.scalar_forward_unique_of_transversality`, `_of_growth`, `_of_bounded`, `forward_plus_bubble_unbounded`, `transversality_of_growth`, `asset_value_no_bubble` |
| SC(14), p. 733 | Trace and determinant are the sum and product of the roots | `LinearDifferenceEquations.charpoly_factor`, `trace_det_eq_roots`, `vieta_of_distinct_roots`, `exists_distinct_real_roots`, `charpoly_root` |
| SC(15)–(17), pp. 733–734 | Eigenvectors, `E⁻¹`, diagonalisation, decoupling | `LinearDifferenceEquations.eigvec_eq`, `eigvec_alt_form`, `root_ne_a11`, `eigvec_distinct`, `eigvec_matrix_inverse`, `eigvec_diagonalizes`, `decouple`, `decoupled_system`, `decoupled_reconstruct`, `recouple` |
| SC(18), p. 734 | Steady state, unique when `1 − tr A + det A ≠ 0` | `LinearDifferenceEquations.steady_state`, `steady_state_unique`, `one_sub_trace_add_det`, `charpoly_one_ne_zero_of_saddle` |
| p. 736 | Saddle roots from `det A > 0` and `p(1) < 0` | `LinearDifferenceEquations.saddle_roots_of_charpoly_one_neg`, `discriminant_pos_of_charpoly_one_neg` |
| SC(19)–(21), pp. 736–738 | Saddle-path solution: existence and uniqueness among bounded solutions | `LinearDifferenceEquations.saddle_path_constant_solves`, `saddle_path_constant_unique`, `saddle_path_exists`, `saddle_path_unique` |
| SC(22), p. 739 | Polynomial factorisation | `LinearDifferenceEquations.lag_polynomial_factor`, `polynomial_factorization_row1`, `polynomial_factorization_row2` |
| C.3, p. 741 | Second-order equations as companion systems | `LinearDifferenceEquations.companion_of_second_order`, `second_order_of_companion`, `companion_lag_polynomial` |

## Exercises (pp. 124–127)

| Book | Claim | Lean |
| --- | --- | --- |
| Ex 1(a) | `B_{s+1} = [1 + (1 − ξ)r]B_s` | `BudgetConstraint.ex1_recursion`, `BudgetConstraint.ex1_path` |
| Ex 1(b) | The budget constraint holds, **for `0 < ξ < 2 + 2/r` only** | `BudgetConstraint.ex1_discounted_tb`, `ex1_ibc`, `ex1_transversality`, `ex1_not_summable` |
| Ex 1(c) | The budget constraint holds yet consumption eventually turns negative | `BudgetConstraint.ex1_consumption`, `ex1_debt_unbounded`, `ex1_eventually_infeasible` |
| Ex 3 | Lognormal consumption: the drift is `v_t/(2σ)`, constant only with constant conditional variance | `StochasticConsumption.lognormal_consumption_drift`, `lognormal_random_walk_drift` |
| Ex 4 | Nonstationary output: revisions, `ΔC = (1 + r)ε/(1 + r − ρ)`, current-account response `−ρ/(1 + r − ρ)` | `StochasticConsumption.nonstationary_revision`, `revision_weight_closed_form`, `consumption_change_revisions`, `hasSum_revision_weights`, `consumption_innovation_from_revisions`, `consumption_innovation_nonstationary`, `consumption_innovation_nonstationary_ae`, `current_account_nonstationary` |
| Ex 5 | Campbell test: residual orthogonality **plus a no-bubble condition** ⇔ (2.43); orthogonality alone is not enough | `PresentValueTest.Stochastic.campbellResidual`, `condExp_residual_eq_zero`, `campbell_of_residual`, `campbell_iff_residual`, `residual_orthogonality_insufficient` |
| Ex 6 | Derive (2.43) from `CA_t = Z_t − E_t Z̃_t` | `PresentValueTest.Stochastic.campbell_eq_43`, `PresentValueTest.campbell_deterministic` |
| Ex 9(a)–(c) | Simplified q model: first-order conditions; steady state independent of `χ` | `TobinQ.ex9_hasDerivAt_investment`, `ex9_hasDerivAt_capital`, `ex9_system`, `ex9_steady_state_iff` |
| Ex 9(f) | Marginal q ≠ average q when the cost is not homogeneous of degree one | `TobinQ.text_cost_homogeneous`, `ex9_cost_not_homogeneous`, `ex9_step`, `ex9_average_q_gap`, `ex9_counterexample` |
| Ex 2 | Uncertain lifetimes: survival probability `φ` multiplies the discount factor | `ConsumptionFunctions.hasSum_survival_weights`, `uncertain_lifetime_sum`, `expected_utility_uncertain_lifetime` |
