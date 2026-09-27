# Corrections to the source

Places where a claim in Chapter 2 of Obstfeld and Rogoff (1996), or in its
Supplements A–C, is false, imprecise, or relies on an unstated hypothesis. In
each case the Lean statement proves the corrected version and cites the
original.

## Claims that are wrong or need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| (2.65), p. 107; repeated p. 124 | `q_t = Σ_{s=t+1}^∞ (1 + r)^{−(s−t)} [A_{s+1}F_K(K_{s+1}, L_{s+1}) + (χ/2)(I_{s+1}/K_{s+1})²]`. | Index typo: iterating (2.64) gives the same sum and discount with subscripts `s`. Under the model's own hypotheses the printed series sums to `q_{t+1}`, not `q_t` (`TobinQ.book_formula_sums_to_next_q`), and equals `q_t` only if `q_{t+1} = q_t`. The corrected formula is `TobinQ.q_forward_solution`; (2.70) on p. 112 already uses the correct indexing. |
| Ex 1(b), p. 124 | The intertemporal budget constraint holds “for any `ξ > 0`”. | False for large `ξ`. The discounted trade balances form a geometric series with ratio `[1 + (1 − ξ)r]/(1 + r)`, which converges iff `0 < ξ < 2 + 2/r`. Proved for that range (`BudgetConstraint.ex1_ibc`); for `ξr ≥ 2(1 + r)` and `B₀ ≠ 0` the present value does not exist (`BudgetConstraint.ex1_not_summable`). The book's “small fraction” case is covered. |
| p. 65 | Foreign debt cannot exceed the present value of output net of `G` and `I`. | The sharp bound is `−(1 + r)B_t ≤ PV(Y − G − I)` (`BudgetConstraint.debt_limit`). The form `−B_t ≤ PV(Y − G − I)` holds for a debtor (`debt_limit_debtor`) but can fail for a creditor when the present value is negative. Needs `C ≥ 0` and summable present values; `K ≥ 0` is not needed. |
| p. 68 | `Y/(r − g)` is the market value of a claim to all future output. | It is `Σ_{v≥0} (1 + r)^{−(v+1)} Y_{s+v}`: output from date `s` on, valued at the start of date `s`, the same timing as `B_s`. Needs `−1 < g < r` (`BudgetConstraint.output_claim_value`). |
| fn 13, p. 78 | `Σ_{s>t} R_{t,s} r_s = 1`. | Needs `R_{t,s} → 0`. It fails when all rates are zero (`PresentValue.rate_mul_varDisc_zero_rates`). Proved with the hypothesis and nonnegative rates (`PresentValue.hasSum_rate_mul_varDisc`). |
| Supplement C, fn 13, p. 729 | The forward sum converges “when (and only when)” `|a| > 1`. | Convergence is a growth condition on the forcing term, not on `a` alone. Proved under `|m_t| ≤ M gᵗ` with `0 ≤ g < |a|` (`LinearDifferenceEquations.forward_summable`). |
| Supplement C, p. 730 | `b₀ > 0` explodes and `b₀ < 0` implodes, “irrespective of `m`”. | For `a < −1` the bubble term oscillates, and “irrespective of `m`” needs `m` to grow more slowly than `|a|ᵗ`. Proved: `b₀ ≠ 0` makes the solution unbounded for bounded `m`, or violates transversality in the growth case (`LinearDifferenceEquations.forward_plus_bubble_unbounded`, `scalar_forward_unique_of_growth`). |
| Supplement A, p. 716 | The Kuhn–Tucker conditions are necessary and sufficient for concave objectives and convex constraints. | Necessity needs a constraint qualification: maximise `z` subject to `z² ≤ 0` has optimum `z = 0` but no multiplier. Harmless for the book's linear budget constraint. Not formalised; the optimality results use the Euler equation directly (`ConsumptionOptimality`). |
| fn 8, p. 71 | If `(1 + r)^{σ−1}β^σ > 1`, no optimum exists, and this needs `σ > 1`. | Both hold with `≥`: at equality consumption grows at exactly `1 + r` and its present value still diverges. Proved for `≥` (`ConsumptionFunctions.crra_no_optimum`, `one_lt_sigma_of_one_le_tilt`), the latter needing `0 < β < 1`, `r > 0`, `σ > 0`. |
| Ex 2 | Survival probability `φ` turns the expected utility into `Σ (φβ)^s u(C_s)`. | Interchanging the two sums needs `Σ (φβ)^s |u(C_s)| < ∞`, `0 ≤ φ < 1` and `β ≥ 0`; stated explicitly (`ConsumptionFunctions.uncertain_lifetime_sum`). |
| SA.2, pp. 718–721 | The CRRA value function is `J(W) = ΘW^{1−1/σ}/(1 − 1/σ)`. | What is shown there, and proved here, is that this `J` satisfies the Bellman equation with the stated policy as unique maximiser (`ConsumptionFunctions.crra_bellman_isGreatest`). That `J` is the value function needs a verification argument not given in the book; optimality of the policy itself is proved directly from the Euler equation (`crra_isOptimal`). |
| Ex 5, p. 126 | The Campbell test: (2.43) holds if and only if `CA_{t+1} − ΔZ_{t+1} − (1 + r)CA_t` is uncorrelated with date-`t` information. | **The “if” direction is false.** With `Z ≡ 0` and `CA_t = (1 + r)^t` the residual is identically zero but (2.43) fails (`PresentValueTest.Stochastic.residual_orthogonality_insufficient`). The correct equivalence adds the no-bubble condition `lim (1 + r)^{−n} E_t CA_{t+n} = 0` (`campbell_iff_residual`). |
| Ex 6 and (2.43), p. 90 | Summation by parts turns (2.42) into (2.43). | Needs the tail condition `(1 + r)^{−T} Z_T → 0`, which the book leaves unstated, and an interchange of conditional expectation and infinite sum. The interchange is proved from the stochastic form of the growth condition, `Σ (1 + r)^{−s} E|Z_{t+s}| < ∞` (`PresentValueTest.Stochastic.condExp_tsum_of_integral`). |
| Ex 3, p. 125 | With lognormal consumption, `log C` is a random walk with constant drift. | The Euler equation gives drift `v_t/(2σ)` with `v_t` the conditional variance of `log C_{t+1}`; it is constant only if `v_t` is (`StochasticConsumption.lognormal_consumption_drift`, `lognormal_random_walk_drift`). |
| (2.32), p. 81 | Certainty-equivalent consumption follows from the almost-sure budget constraint. | The book swaps `E_t` with an infinite sum. Here the expected budget recursion is proved exactly at every finite horizon; the limit uses two named hypotheses, expected transversality and summable discounted forecasts (`StochasticConsumption.certainty_equivalence`). |
| (2.45), p. 91 | The VAR forecast of the current account. | Needs `Σ (Ψ/(1 + r))^k` to converge; the book is silent. Row sums of `|Ψ|` below `1 + r` suffice (`PresentValueTest.Stochastic.summable_disc_smul_pow`). |
| pp. 94–95 | More future risk makes current consumption fall when `u''' > 0`. | A heuristic in the book. The two-period statement needs `u'` strictly decreasing, convex and continuous, with interior optima at both risk levels given by their Euler equations (`StochasticConsumption.precautionary_saving_two_period`). |
| fn 36, p. 102 | Modigliani–Miller: the firm's financing does not matter. | Needs no-bubble conditions on both the unlevered and the equity value and a no-Ponzi condition on firm debt (`FirmsAndWealth.modigliani_miller`). |
| (2.59), p. 104 | Firm value equals the capital stock. | Needs `(1 + r)^{−n} K_{n+1} → 0`. Without any summability assumption, `V_s − K_{s+1} = (1 + r)^s (V_0 − K_1)`: any gap grows at exactly rate `r` (`FirmsAndWealth.firm_value_sub_capital`). |
| App. 2B.1, p. 123 | A positive limit of discounted prices cannot be an equilibrium. | Informal. Proved: a positive limit ⇔ the price exceeds the present value of dividends, and nonnegative prices rule out a negative limit (`FirmsAndWealth.bubble_pos_iff_price_gt_pv`, `price_ge_pv_of_nonneg`). |
| p. 98 | With constant durables prices and `δ = 0`, durables are bought in one lump. | Needs `pr ≠ 0`. For general `δ`, later spending is replacement `pδD_t`, not zero (`Durables.durables_purchases_after_t`, `durables_lump_sum`). |
| Supplement C.1.3 | Bubble solutions of the stochastic forward equation are `b₀aᵗ`. | They are all processes with `E_t b_{t+1} = a b_t`. Not formalised (the stochastic difference equations SC(11)–(12) are outside the library). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| p. 66, throughout | Every discounted quantity grows at a net rate below `r`. | Explicit `Summable` hypotheses on each present value; `PresentValue.summable_of_growth` derives them from a growth bound. |
| (2.4), p. 61 | A single horizon's budget identity does not imply the period constraints. | The equivalence is between (2.4) at every horizon and (2.2) at every date (`BudgetConstraint.flow_iff_finite_ibc`). |
| p. 63 | An optimum exists. | Not assumed. Sufficiency (`ConsumptionOptimality.isOptimal_of_euler`) and necessity (`pv_eq_of_optimal`, `euler_of_optimal`) are proved separately; admissible paths are positive with summable present value and lifetime utility. |
| pp. 62, 65 | The Euler equation with the budget constraint characterises the optimum. | Needs `u` concave (sufficiency) and strictly concave (uniqueness): `ConsumptionOptimality.lifetimeUtility_lt_of_euler`. |
| (2.64)–(2.69) | Capital and `χ` are nonzero; `F_K` is strictly decreasing for a unique steady state. | Explicit hypotheses of the `TobinQ` theorems. |
| SC p. 736 | The saddle configuration `0 < ω₂ < 1 < ω₁` is derived for Cobb–Douglas with `r > 0`. | Needs only `1 + r > 0` and `F_KK < 0` (`TobinQ.omega_saddle`); in general, `det A > 0` and `1 − tr A + det A < 0` (`LinearDifferenceEquations.saddle_roots_of_charpoly_one_neg`). |
| p. 109; SC(19)–(21) | The saddle path is “the” path from a given capital stock. | Proved for the linear system among bounded solutions. Uniqueness needs only `|ω₁| > 1`, existence `|ω₂| < 1` (`LinearDifferenceEquations.saddle_path_unique`, `saddle_path_exists`, `TobinQ.saddle_path_unique`). |
| SC(15), p. 733 | Eigenvector formulas. | Need `a₂₁ ≠ 0`; the second form also needs `ω_i ≠ a₁₁`, guaranteed when `a₁₂ ≠ 0` (`LinearDifferenceEquations.root_ne_a11`). |
| SC(18), p. 734 | Steady-state formula. | Needs `1 − tr A + det A = (1 − ω₁)(1 − ω₂) ≠ 0`, automatic in the saddle case. |
| (2.70), p. 112 | Marginal equals average `q`. | Needs `F` homogeneous of degree one (Euler's theorem is derived, `TobinQ.euler_of_homogeneous`), the labour first-order condition, and a no-bubble condition on `q_s K_{s+1}`. |

## Not formalised

* The global nonlinear phase diagrams for the `q` model (Figures 2.9–2.11). The linearised system is fully treated.
* The intertemporal budget constraint (2.71) of the `q` model.
* The variational derivation of the stochastic Euler equation (2.28)–(2.29), which is taken as a hypothesis in conditional-expectation form.
* The infinite moving-average forms (2.36) and (2.39); the finite-horizon (2.36) is proved.
* The stochastic forward solution SC(11)–(12), C.2.5 and SC(23).
* Exercises 7 and 8: Exercise 7 (an unstable debt ratio still satisfies transversality) is covered in substance by `TrendGrowth.debt_ratio_diverges` and `BudgetConstraint`; Exercise 8 is discussion.
* Empirical applications, Figure 2.3 and the Glick–Rogoff estimates.
