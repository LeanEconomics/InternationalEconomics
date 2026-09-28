# Source map

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Chapter 7, “Global Linkages and Economic Growth” (pp. 429–512). Equation numbers
are the book's, cited as (n); page numbers are book pages. Lean names are
relative to `ObstfeldRogoff.GlobalGrowth`; the rows list the main declarations,
and each module's docstring maps its remaining results. Where a statement adds a
hypothesis the book leaves implicit, or departs from the printed claim, see
[corrections](corrections.md).

## §7.1 The neoclassical growth model (pp. 430–454)

| Book | Claim | Lean |
| --- | --- | --- |
| (1)–(9), Fig. 7.1 | The Solow map; unique steady state; **global monotone convergence** | `SolowModel.capital_per_efficiency_worker`, `solow_steady_existsUnique`, `solow_global_convergence` |
| Fig. 7.1, `δ > 1` | Unique steady state for any `δ`; local stability iff `G′(k̄) > −1`; global criteria | `SolowExtensions.solow_steady_existsUnique_any`, `solow_local_stability`, `lyapunov_convergence`, `cobbDouglas_delta_gt_one_convergence` |
| pp. 433–434 | Comparative statics; long-run growth; the golden rule; dynamic inefficiency | `SolowModel.steady_strictMono_saving`, `output_per_capita_growth_tendsto`, `golden_rule_strict_max`, `dynamic_inefficiency` |
| (10), pp. 435–437 | Cobb–Douglas closed forms; the MRW `α`; fourfold saving | `SolowModel.cobbDouglas_steady`, `mrw_implied_alpha`, `fourfold_saving` |
| (13)–(17), p. 439 | Human capital (MRW): steady state, estimating equation, global stability | `SolowExtensions.mrw_steady_unique`, `mrw_estimating_equation`, `mrw_global_convergence` |
| (18)–(26), Fig. 7.4 | **Ramsey–Cass–Koopmans**: the optimal path exists and is unique; Euler + transversality necessary and sufficient; monotone convergence (bounded and log utility) | `RamseyCassKoopmans.book_optimal_existsUnique`, `isOptimal_iff_euler_tvc`, `book_convergence`, `LogUtility.book_unbounded_existsUnique`, `LogUtility.uoptimal_iff_euler_tvc` |
| (23), p. 441 | The boundedness condition is exactly a detrended discount factor below 1 | `RamseyCassKoopmans.condition23_iff`, `detrend_welfare` |
| (25), (28), fn 7–8, p. 442 | Steady states; dynamic efficiency; `dk̄/dβ > 0` | `RamseyCassKoopmans.book_steady_spec`, `steady_lt_golden_rule`, `steady_strictMono_patience` |
| p. 441, `n = g = δ = 0` | Existence, uniqueness and convergence with an unbounded feasible set | `RamseyCassKoopmans.book_no_growth`, `unbounded_without_depreciation` |
| Figs. 7.5–7.6, p. 464 | Impatience and population experiments; small open and world economies | `RamseyCassKoopmans.impatience_experiment`, `population_experiment`, `small_open_capital`, `equal_mpk_iff` |
| (30)–(33), fn 10–13 | Weil OLG growth: aggregation, the newborn gap, the unique steady state, dynamic inefficiency | `OLGGrowth.aggregate_budget`, `eq33`, `steady_existsUnique`, `inefficient_iff` |
| Fig. 7.7, pp. 447–449 | **The global saddle path**: from every `k₀` exactly one equilibrium path, monotone and convergent | `OLGGrowth.weil_saddle_path`, `posOrbit_exists`, `posOrbit_unique`, `posOrbit_representation` |
| Ex 1, p. 512 | Government spending: crowding out; two steady states; the announced change (existence for small spending, uniqueness, monotone path, non-existence for large spending) | `OLGGrowth.crowding_out`, `two_steady_states_with_spending`, `announcement_equilibrium`, `announcement_unique_general`, `announcement_no_equilibrium` |
| (34)–(41), pp. 448–454 | Immigration: impact gain; natives gain along any price path; the saddle path; immigrants never borrow; the Harberger triangle | `Immigration.impact_gain`, `natives_gain`, `immig_saddle_path`, `cobbDouglas_immigrants_never_borrow`, `harberger_gain_second_order` |

## §7.2 International convergence (pp. 454–473)

| Book | Claim | Lean |
| --- | --- | --- |
| (42)–(45), pp. 460–464 | The tax steady state; the convergence rate `μ`; half-lives | `SolowModel.taxSteady_elasticity`, `cobbDouglas_mu`, `solow_ratio_tendsto`, `half_life_two_percent` |
| p. 462 | The increment claim (false for levels, true for growth rates) | `SolowExtensions.increment_not_larger_further_below`, `growth_rate_strictAnti` |
| (46)–(51), pp. 465–467 | Public capital: steady state, speed ordering, global convergence | `SolowExtensions.bms_steady_and_speed`, `bms_speed_order`, `bms_global_convergence` |
| (52)–(60), fn 29–31 | Borrowing-constrained OLG: the saver's problem, the equilibrium map, the constrained steady state, (60) exactly, global convergence, general `δ` | `BorrowingConstrainedOLG.optimal_binding`, `equilibrium_existsUnique`, `cond60_iff`, `equilibrium_converges`, `equilibriumD_converges` |
| Ex 2, p. 512 | A productivity rise | `BorrowingConstrainedOLG.exercise2` |

## §7.3 Endogenous growth (pp. 473–496)

| Book | Claim | Lean |
| --- | --- | --- |
| (61)–(65), fn 32 | AK: the planner optimum over the infinite horizon; unique; finite utility iff `ḡ < A`; market = planner | `AKModel.ak_planner_optimal`, `ak_planner_unique`, `ak_finite_utility_iff`, `ak_competitive_eq_planner` |
| (66)–(68), fn 33 | Learning by doing: equilibrium exists and is unique; market growth below social; the optimal subsidy | `AKModel.lbd_equilibrium`, `lbd_market_growth_lt_social`, `lbd_subsidy_implements_optimum` |
| (69)–(78), p. 481 | Portfolio diversification and growth: the Kelly share exists and is unique; infinite-horizon optimality; diversification raises the share and growth; variances | `PortfolioGrowth.existsUnique_kelly`, `kelly_plan_optimal`, `diversification_raises_growth`, `var_world_counterexample` |
| (79)–(92) | Romer: final-goods firms, monopoly pricing, the blueprint price as a present value, labour arbitrage | `RomerGrowth.finalGoods_optimal`, `monopoly_optimal`, `romer_log_blueprint_pv`, `labour_arbitrage_iff` |
| (93)–(96), p. 490 | The balanced path is unique for every `σ`; exists iff `θL > (1−β)/(αβ)`; the transition from any `K₀` (log); no finite arrival | `RomerGrowth.bgp_unique`, `bgp_exists_iff`, `romer_log_equilibrium`, `romer_log_convergence`, `romer_no_finite_arrival`, `romer_sigma_ne_one_no_jump` |
| (97), fn 42, Ex 3 | The planner: optimum, uniqueness, the corner case, planner growth above market | `RomerGrowth.planner_optimal`, `planner_unique`, `planner_corner_optimal`, `planner_minus_market` |
| p. 492, §7.3.3.6 | The subsidised equilibrium; merging economies raises growth | `RomerGrowth.SubsidyAllocation.household_optimal`, `subsidy_bgp_unique`, `merge_raises_growth` |
| (98)–(102) | Kremer's population model | `RomerGrowth.kremer_equation`, `kremer_path` |
| pp. 495–496 | Grossman–Helpman, corrected | `RomerGrowth.gh_linear_ppf`, `gh_specialisation`, `gh_growth_corrected`, `gh_trade_growth` |

## §7.4 Stochastic growth (pp. 496–508)

| Book | Claim | Lean |
| --- | --- | --- |
| (103)–(109), fn 46 | Brock–Mirman on a finite Markov chain: the log-savings policy is optimal (Bellman verification, transversality); the unique share `1 − αβ` | `BrockMirman.tsum_le_value`, `tsum_lp_eq_value`, `bellman_eq`, `euler_share_iff`, `transversality_lp` |
| (110)–(113), fn 48 | Log output is AR(1); steady state; transitory shocks; the law of log output converges (i.i.d.) | `BrockMirman.logOutput_ar1`, `steady_logOutput_iff`, `transitory_shock_response`, `law_logOutput_converges` |
| (114)–(116), (136) | Two-country model: the share `Ψ` exists and is unique; planner optimality; investment shifts | `TwoCountryRBC.existsUnique_psi`, `Planner.opt_is_optimal`, `Planner.euler_home_iff`, `Planner.investment_shift` |
| (117)–(135), p. 506 | Log-linear model: steady state; undetermined coefficients; roots of opposite sign; `a_ce` increasing in `ρ`; impulse responses | `LogLinearRBC.steady_state`, `undetermined_coefficients`, `roots_opposite_sign`, `ace_increasing_in_persistence`, `impulseK_closed` |
| Ex 4, p. 512 | Consumption from total wealth | `BrockMirman.exercise4_consumption` |

## Appendices

| Book | Claim | Lean |
| --- | --- | --- |
| 7A, (3′)–(9′), fn 23 | Period-`h` Solow and its `h → 0` limit; continuous Solow: closed form and convergence | `ContinuousTimeLimits.period_h_solow`, `continuous_solow_derivation`, `closed_form_solves`, `continuous_convergence` |
| 7A, pp. 509–510 | Period-`h` Ramsey steady state; period-`h` dynamics converge to the Ramsey ODE (log and CRRA); discounted sums converge to the integral; saddle choice (given the continuous saddle property) | `ContinuousTimeLimits.period_h_ramsey_steady`, `ramsey_period_h_converges`, `crra_period_h_converges`, `discounted_sum_tendsto_integral`, `ramsey_saddle_choice_converges` |
| 7B, (137)–(143) | Stochastic OLG: saving, the harmonic-mean riskless rate, capital dynamics | `BrockMirman.StochasticOLG.young_consumption_optimal`, `harmonic_of_zero_optimal`, `olg_log_dynamics` |
