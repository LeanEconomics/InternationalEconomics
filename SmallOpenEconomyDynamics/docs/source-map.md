# Source map

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Chapter 2, “Dynamics of Small Open Economies” (pp. 59–128), and the Supplements
to Chapter 2, A–C (pp. 715–741). Equation numbers are the book's (`SA`, `SC`
for the supplements); page numbers are book pages. Lean names are relative to
`ObstfeldRogoff.SmallOpenEconomyDynamics`. The book's date `t` is date 0 in
the Lean statements. Where a statement adds a hypothesis the book leaves
implicit or departs from the printed claim, see [corrections](corrections.md).

Phase 2a covers the deterministic core. The stochastic model (§2.3), the
present-value test, durables, firms and asset pricing (§2.4–2.5 except Tobin's
q), and Appendices 2A–2B are phase 2b.

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
| Ex 9(a)–(c) | Simplified q model: first-order conditions; steady state independent of `χ` | `TobinQ.ex9_hasDerivAt_investment`, `ex9_hasDerivAt_capital`, `ex9_system`, `ex9_steady_state_iff` |
| Ex 9(f) | Marginal q ≠ average q when the cost is not homogeneous of degree one | `TobinQ.text_cost_homogeneous`, `ex9_cost_not_homogeneous`, `ex9_step`, `ex9_average_q_gap`, `ex9_counterexample` |
| Ex 2 | Uncertain lifetimes: survival probability `φ` multiplies the discount factor | `ConsumptionFunctions.hasSum_survival_weights`, `uncertain_lifetime_sum`, `expected_utility_uncertain_lifetime` |
