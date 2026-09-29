# Corrections to the source

Places where a claim in Chapter 5 of Obstfeld and Rogoff (1996) is false,
imprecise, or relies on an unstated hypothesis. In each case the Lean statement
proves the corrected version and cites the original.

## Claims that are wrong or need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| p. 304 | Pareto efficiency can be ensured only when `S ≤ N+1`. | `S ≤ N+1` is **neither sufficient for spanning** (two assets with identical riskless payoffs over two states give rank 1: `Spanning.card_le_not_sufficient`) **nor necessary for efficiency** (with `S > N+1` spanning fails, yet the §5.3.2 CRRA allocation meets every complete-markets condition: `Spanning.efficient_without_spanning`). Correct statement: spanning holds iff `rank R = S` (`spans_iff_rank`); it implies `S ≤ N+1` and is sufficient, not necessary, for efficiency. |
| Ex 3(b), p. 346 | In the binding case “`C_t = (1+r)B₁ + Y₁ + Y₂(1)/(1+r)`”. | Typo: `C₁`. The corrected corner solution is optimal, lies strictly below the certainty-equivalent `C₁*`, and the bond Euler equation holds as the strict inequality `u′(C₁) > E u′(C₂)` (`SmallCountry.quad_binding`). |
| (19), p. 281 | The parenthetical argument for revealed preference. | Garbled: the contradiction is not with “gains from trade” but with the endowment being optimal at autarky prices, combined with transitivity and local non-satiation (`ComparativeAdvantage.revealed_preference`). |
| fn 10, p. 280 | `Σ p Y₂ = E Y₂` holds only in the actuarially fair case. | Imprecise: if `Y₂(1) = Y₂(2)` it holds at any prices. Correct: it holds for every `Y₂` iff `p = π` (`SmallCountry.value_eq_expectation_iff`), and for a given two-state `Y₂` with `Y₂(1) ≠ Y₂(2)` iff `p = π` (`value_eq_expectation_two_iff`). |
| (7), p. 277 | No arbitrage requires `Σ p = 1`. | Only half of it: no arbitrage iff `Σ p = 1` and `p ≥ 0` (`SmallCountry.noArbitrage_iff`). |
| (75), p. 330 | `τ = {exp[½(1−ρ)ρV]}^{1/(1−ρ)} − 1 ≈ ρV/2`. | The expression simplifies **exactly** to `τ = exp(ρV/2) − 1` for every `ρ ≠ 1` (`AssetPricing.lucas_tau_simplifies`), so `ρV/2` is a lower bound (`lucas_tau_bounds`). |
| pp. 308–309 | With multiplicative productivity shocks every owner values investment identically. | Also needs `F(K₀) ≠ 0`, so that the payoff is a nonzero multiple of a traded payoff (`AssetPricing.investment_value_invariant`). |
| (59), p. 316 | The price is the present-value sum `Σ`. | The sum is a limit of partial sums; when dividends can be negative it need not converge absolutely, so the main theorem uses partial sums (`InfiniteHorizonPricing.price_eq_series`) and the absolutely summable form needs `u′Y ≥ 0` (`price_hasSum`). |
| p. 316 | No bubbles is assumed to select the fundamental price. | Given convergence of the series, no bubbles is **necessary and sufficient** (`InfiniteHorizonPricing.price_eq_fundamental_iff`); without it `V + (c/β^{t−1})/u′(C)` also solves (57) (`euler_nonunique_without_noBubble`). It holds automatically for bounded `u′V` when `β < 1` (`noBubble_of_bounded`). |
| Ex 6(b), p. 347 | Each country holds its endowment. | Needs a no-Ponzi restriction the book leaves out: with bounded holdings no trade is globally optimal and transversality follows (`InfiniteHorizonPricing.lucas_noTrade_optimal`); uniqueness holds at any prices at which both countries optimise, under strict concavity, and only at histories of positive probability (`lucas_allocation_unique`). |
| (86)–(88), p. 344 | Dynamic consistency. | Over an infinite horizon a conditionally convergent date-1 utility series need not converge on a subtree; absolute convergence is required, which coincides with convergence for constant-sign `u` such as CRRA (`EventTree.dynamic_consistency_infinite`). |
| Supplement, pp. 742–744 | The value function `A·W^{1−ρ}/(1−ρ)` and `μ = 1 − [βE(1+r°)^{1−ρ}]^{1/ρ}`. | The book never states the growth condition `βE(1+r°)^{1−ρ} < 1`, needed for `0 < μ < 1` and a finite value, nor proves transversality; both are handled (`ConsumptionPortfolio.transversality_crra`, `verification_crra_of_noArbitrage`). With history-dependent returns the analogue is a uniform bound `G < 1` (`exists_share_recursion_solution`). |
| p. 284 | (26) reduces to expected utility when `σ = 1/ρ` by a monotone transformation. | With the book's normalisation it is an exact identity (`TwoStageBudgeting.ez_eq_expectedUtility`), and the orderings coincide only when `σ = 1/ρ` (`ez_same_ordering_iff`). |

## Claims confirmed

| Where | Claim | Lean |
| --- | --- | --- |
| p. 338 | The sign of `CA₁` need not be that of `r − r^A`. | Counterexample `π = (1/2, 1/2)`, `Y₁ = 1`, `Y₂ = (1, 3)`, `β = 1`, `p = (1/10, 9/10)`, `r = 1`: `r^A = 1/2 < r` but `CA₁ = −1/5` (`SmallCountry.current_account_sign_not_autarky_rate`). |
| fn 16, fn 17, p. 294, Ex 4, Ex 5(c) | The share `μ`, the planner weight `κ`, the harmonic-mean `ρ̃`, the log-utility prices, the fund share `γ*/(γ+γ*)`. | As printed (`GlobalEquilibrium.GlobalEqm.share_closed_form`, `plannerWeight`, `Aggregation.geometric_aggregation`, `PortfolioDiversification.PortfolioEconomy.logV_eq_sharePrice`, `Exercise5.exercise5c_sharing`). |
| (73), p. 324 | The log-linearised equation. | Holds exactly as an identity between logarithmic derivatives along any differentiable path (`Nontradables.ces_loglinear_exact`). |
| p. 324 | (72) is additively separable when `θρ = 1`. | And only then (`Nontradables.cesCrra_additive_iff`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| (10), p. 277 | Full insurance iff fair prices. | Needs `u′` strictly decreasing, `π > 0`, `β > 0`, `u′(C₁) ≠ 0`. |
| p. 285 | `P < 1` when `p ≠ π`. | Needs `π > 0` and `p` a probability vector; `0 < ρ ≠ 1` throughout §5.1.8. |
| p. 287 | Fair prices iff no aggregate risk. | Needs `π > 0` and `ρ > 0`. |
| fn 17, p. 289 | The equilibrium maximises `κU + (1−κ)U*`. | Global optimality by concavity, proved for CRRA with `ρ > 0`, `ρ ≠ 1`. |
| fn 18, p. 290 | Consumption growth rates are perfectly correlated. | Needs `Var(g) > 0` and `π > 0`. |
| §5.2.4.1 | Log utility, linear production. | Nonnegativity of investment is ignored; the denominators are hypotheses. |
| Ex 5(c), p. 347 | Who borrows. | Not determined: the sign of the less risk-averse country's bond position depends on endowments; the theorem proves only that it holds more than half the fund. |
| p. 311 | The equity-premium relation. | The book's Taylor approximation is informal; the relation is proved exactly for the linearised discount factor `M = β(1 − ρ(C₂/C₁ − 1))`. |
| p. 313 | The lognormal riskless rate. | The lognormal moment-generating identity is a hypothesis (states are finite). |
| (87), p. 344 | The date-1 plan satisfies the date-2 conditions. | The no-arbitrage identity `p̃(h_t∣h_1)/p̃(h_2∣h_1) = p̃(h_t∣h_2)` is a hypothesis, as in the book's argument; needs `π(h_2∣h_1) > 0` and `u′ > 0`; date-2 optimality needs concave `u`. |
| p. 342 | Constant consumption shares. | Needs `π(h_t) > 0`, `ρ ≠ 0` and market clearing at every node. |
| §5.6, p. 334 | The cohort equilibrium. | The riskless-bond normalisation `Σ p = 1` pins down `1 + r`. |
| Ex 3(a), p. 346 | The infinite-horizon certainty-equivalence rule. | Needs `r > 0`, bounded income and Chapter 2's transversality condition (a hypothesis of the forward direction; the converse proves the rule satisfies it) (`InfiniteHorizonPricing.quadratic_infinite_horizon_consumption`, `quadratic_permanent_income_rule`). |
| (84), p. 342 | “You can easily check” the first-order conditions. | Necessity needs an interior optimum, differentiable `u` and the numeraire `P(h₁) = 1`; sufficiency needs concave `u` (`EventTree.arrowDebreu_foc_necessary`, `arrowDebreu_optimal_infinite`). |
| p. 342 | The log (`ρ = 1`) equilibrium. | Needs `β < 1` and convergence of `Σ β^{t−1}E log Y^W` (`EventTree.log_equilibrium_infinite`). |
| (2), p. 743 | An optimal portfolio. | Existence is proved under no arbitrage with non-redundant assets and positive state probabilities (`ConsumptionPortfolio.exists_optimal_portfolio`); with a zero-probability state the supremum need not be attained. |
| (61), p. 317 | `C = μY^W`. | Derived from the complete-markets first-order conditions of every country plus market clearing, at histories of positive probability (`InfiniteHorizonPricing.price_crra_world_output_derived`). |
| pp. 743–744 | Log utility gives `μ = 1 − β` for any return process. | True, with the myopic portfolio, but a finite value function needs a bound: a uniform bound on the optimal expected log return with `β < 1` suffices (`ConsumptionPortfolio.verification_log_tree`). |
