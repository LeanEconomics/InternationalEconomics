# Corrections to the source

Places where a claim in Chapter 7 of Obstfeld and Rogoff (1996) is false,
imprecise, or relies on an unstated hypothesis. In each case the Lean statement
proves the corrected version and cites the original.

## Claims that are wrong or need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| p. 440 | Lifetime utility is bounded if `β(1+n) ≤ 1`. | Must be strict: at equality a constant path with `u(c) ≠ 0` has divergent utility (`RamseyCassKoopmans.not_summable_at_boundary`). |
| p. 439 | The MRW estimating equation. | The last term is mistypeset; it should be `−[(α+φ)/(1−α−φ)] log(n+g+δ)` (`SolowExtensions.mrw_estimating_equation`). |
| p. 462 | The further `k` is below `k̄`, the larger the increment. | False for `Δk`: with `α = 1/2`, `s = 1`, `z = 0`, `δ = 1`, `Δk(0.01) = 0.09 < Δk(0.25) = 0.25` (`SolowExtensions.increment_not_larger_further_below`); true for the growth rate `Δk/k` (`growth_rate_strictAnti`) and for `Δk` above `k̄`. |
| p. 466 | `H′ − H = s(Y − rK)`. | Omits `−δH`; eq. (48) itself is correct (`SolowExtensions.bms_human_capital_accumulation`). |
| p. 506 | Output rises by less than 0.04 percent. | About 0.1 percent: the book multiplies the change in capital by the marginal product instead of the capital share (`LogLinearRBC.p506_numbers`). |
| p. 506 | For reasonable parameter values the quadratic has one positive and one negative root. | For every `α ∈ (0, 1)`; the stable root lies in `(α, α/(1−β))` and is unique (`LogLinearRBC.roots_opposite_sign`, `saddle_path`). |
| (117), p. 502 | `K_{t−1} − K_t = Y_t − C_t`. | Typo for `K_{t+1}`. |
| Ex 2, p. 512 | `y = Ak`. | Should read `y = Ak^α`; the economy returns to `r^D = r` in one period iff `1 + η(1+β)/β ≥ A^{α/(1−α)}` (`BorrowingConstrainedOLG.exercise2`). |
| p. 476 | Growth under AK needs `β(1+A) > 1`. | That gives positive growth only; an optimum exists iff `(β(1+A))^σ < 1 + A`, and none exists otherwise (`AKModel.ak_finite_utility_iff`, `ak_no_optimum`). |
| p. 478 | Learning by doing. | The planner needs its own finiteness condition `β^σ(1+A)^{σ−1} < 1`, not implied for `σ > 1` (counterexample `σ = 2`, `β = 9/10`, `A = 1/2`, `α = 1/5`, `AKModel.lbd_planner_infinite_example`). |
| pp. 490–491 | The Romer balanced path. | Unique for every `σ`, exists iff `θL > (1−β)/(αβ)`; the omitted condition `g < r` fails for `σ > 1` (`σ = 2`, `β = 9/10`, `α = 1/3`, `θL = 36/25`: no equilibrium) (`RomerGrowth.bgp_unique`, `bgp_exists_iff`, `bgp_infinite_utility_example`). |
| p. 490 | The economy jumps immediately to the balanced path. | Only half right: capital before date 0 is a state. With log utility research labour and growth jump but capital and the interest rate converge gradually (`RomerGrowth.romer_log_equilibrium`, `romer_log_convergence`); for `σ ≠ 1` growth also moves (`romer_sigma_ne_one_no_jump`); no path arrives in finite time (`romer_no_finite_arrival`). |
| fn 42 | The planner's balanced path. | Balanced from date 0 only if `K₀ = K^PLAN`; otherwise capital converges to it (`RomerGrowth.plannerK_tendsto`); the corner `βθL ≤ 1−β` has no research (`planner_corner_optimal`). |
| pp. 495–496 | Grossman–Helpman example. | With the same technology in both sectors the frontier is linear, so trade means complete specialisation, and the printed law makes growth explode; the corrected law gives constant growth, and a world price above autarky weakly raises growth (`RomerGrowth.gh_linear_ppf`, `gh_growth_explodes`, `gh_growth_corrected`, `gh_trade_growth`). |
| p. 481 | The world fund has lower variance than every country. | Needs equal variances: variances `1/100` and `1` give `101/400` (`PortfolioGrowth.var_world_counterexample`). |
| (74)–(77) | The portfolio approximations. | Expansions around zero consumption growth; the exact share differs from (76) by `(βR)²`, and the ignored constraint `x ≤ 1` can bind (`PortfolioGrowth.kelly_exact`, `corner_counterexample`). |
| §7.4.2 | “Easy to check.” | Hides a fixed-point problem for `Ψ`; the interior solution exists and is unique, `0` and `1` are spurious (`TwoCountryRBC.existsUnique_psi`, `psiMap_zero_one`). |
| Ex 1(b) | The steady state with government spending. | Generally two steady states; crowding out holds at each (`OLGGrowth.two_steady_states_with_spending`, `crowding_out`). |
| Ex 1(c) | The announced spending change. | An equilibrium path exists for small spending and is then unique, with capital rising and consumption falling until the change (`OLGGrowth.announcement_equilibrium`); for large spending none exists (`announcement_no_equilibrium`). |
| §7.2.2.3 | The constrained saver's problem. | Needs `k ≥ 0`, without which it is unbounded when `r^D < r` (`BorrowingConstrainedOLG.unbounded_without_k_nonneg`); fn 31 holds exactly as (60) iff `D > 0` and `k̄^D < k̄^U` (`cond60_iff`, `fn31`). |
| p. 453 | Newborns lose from immigration. | Their human wealth is lower in general (`Immigration.newborn_human_wealth_lower`); lower utility is proved in the closed-form case (`bm_newborn_loses`). |
| Fig. 7.1 | Convergence of the Solow model. | Needs `δ ≤ 1` (monotonicity fails for `δ = 3/2`, `f = √k`); with `δ > 1` capital can turn negative, and convergence holds locally iff `G′(k̄) > −1` (`SolowModel.solow_overshoots_of_delta_gt_one`, `SolowExtensions.solow_local_stability`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| Fig. 7.1 | Solow convergence. | `δ ≤ 1`, `z + δ > 0`, `1 + z > 0` and Inada conditions. |
| fn 7 | `k̄` differentiable in `β`. | Needs `f″(k̄) ≠ 0`; the sign holds without it. |
| fn 13 | Dynamic inefficiency is possible. | Exactly when `β > (D + n(1+n))/((D+n)(1+n))`, which for Cobb–Douglas is `(1+αn)/(1+n)` (`OLGGrowth.betaThreshold_cobbDouglas`). |
| pp. 452 | Immigrants' and natives' paths. | Immigrants never borrow iff `h_t ≥ h₀∏βR_s`; proved for Cobb–Douglas with any `δ ∈ [0,1]`, and for general `f` under a monotonicity condition (`Immigration.immigrants_nonneg_iff`, `cobbDouglas_immigrants_never_borrow`, `saddle_growth_ge_gap`). |
| (127) | The lognormal Euler step. | The lognormal moment identity is a hypothesis (states are finite). |

## Not formalised

| Where | Claim | Status |
| --- | --- | --- |
| Ex 1(c) | Existence for spending between the small-spending bound and the non-existence bound. | Undecided. |
| 7A | The period-`h` optimal initial consumption converges to the continuous saddle value. | Proved given the continuous-time saddle property (needs ODE existence and a phase analysis) and boundedness of the period-`h` optimal paths, which are hypotheses. |
| p. 490 | The explicit Romer transition for `σ ≠ 1`. | Only its non-stationarity is proved. |
| p. 452 | Immigrants never borrow, general `f`. | Open without the monotonicity condition. |
