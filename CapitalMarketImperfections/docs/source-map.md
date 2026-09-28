# Source map

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Chapter 6, “Imperfections in International Capital Markets” (pp. 349–428).
Equation numbers are the book's, cited as (n); page numbers are book pages.
Lean names are relative to `ObstfeldRogoff.CapitalMarketImperfections`; the rows
list the main declarations, and each module's docstring maps its remaining
results. Where a statement adds a hypothesis the book leaves implicit, or departs
from the printed claim, see [corrections](corrections.md).

Uncertainty is a finite set of states (`Model.StateSpace`); infinite-horizon
games live on trees of finite histories with `tsum` over dates.

## §6.1.1 Sovereign risk with direct sanctions (pp. 349–363)

| Book | Claim | Lean |
| --- | --- | --- |
| fn 7–8, p. 355 | Full insurance is the unique optimum without default risk; the country defaults on it iff `ε > ηȲ/(1−η)` | `DirectSanctionsInsurance.full_insurance_optimal`, `full_insurance_unique`, `default_on_full_insurance_iff` |
| (1)–(9), pp. 356–358 | **The optimal incentive-compatible contract** `C = max(c̄, (1−η)Y)`, with `c̄` unique; optimal for every utility, uniquely | `DirectSanctionsInsurance.cbar_exists`, `cbar_unique`, `optimal_ic_contract` |
| (4)–(6), p. 356 | Kuhn–Tucker multipliers exist at the optimum; the conditions are sufficient | `DirectSanctionsInsurance.kuhn_tucker_at_optimum`, `kuhn_tucker_sufficient` |
| (7)–(9), fn 10–11 | Threshold, two-arm schedule; full insurance iff `(1−η)(Ȳ+ε̄) ≤ Ȳ`; put-option form | `DirectSanctionsInsurance.threshold_eqs`, `optPayment_arms`, `full_insurance_iff`, `put_option_form` |
| p. 360 | Welfare rises with `η`; `η = 0` gives autarky | `DirectSanctionsInsurance.value_mono_eta`, `value_strictMono_eta`, `no_sanctions_autarky` |
| (10), pp. 358–360 | Uniform example: quadratic, root, comparative statics | `DirectSanctionsInsurance.uniform_threshold_iff`, `uniformThreshold_strictMono`, `uniformThreshold_neg_iff` |
| fn 6, (7) | The clamp contract for a general continuous density | `DirectSanctionsInsurance.ContinuousDensity.density_cbar_exists`, `density_optimal` |
| (58)–(65), pp. 423–424 | Appendix 6B, with saving: `C₂ = max(C₁, (1−η)Y)`, unique `C₁`, schedule (65), Kuhn–Tucker | `SanctionsWithSaving.optimal_saving_contract`, `c1_unique`, `schedule_65`, `kuhn_tucker_6B` |
| pp. 362, 424–425 | Positive saving iff the constraint binds; insurance even at `η = 0`; the `η = 0` uniform root | `SanctionsWithSaving.positive_saving_iff`, `insurance_without_sanctions`, `threshold66_bounds` |
| Ex 1–2, pp. 425–426 | Two-sided contract; indexed debt is strictly worse than insurance | `SanctionsWithSaving.two_sided_efficient`, `indexed_optimal`, `indexed_strictly_worse`, `indexed_full_insurance_iff` |

## §6.1.2 Reputation (pp. 363–375)

| Book | Claim | Lean |
| --- | --- | --- |
| (14)–(16), pp. 364–365 | Default as a stopping time; honouring is optimal iff Gain ≤ Cost; Cost as a `tsum`; (16) holds for `β` near 1 | `ReputationTrigger.Trigger.payoff_decomposition`, `trigger_iff`, `FullInsurance.full_insurance_sustainable_iff`, `sustainable_for_beta_near_one` |
| fn 19, p. 365 | The second-order limit of Cost | `ReputationTrigger.FullInsurance.footnote_19` |
| p. 365 | The finite-horizon game unravels; the one-shot constraints derived from it | `ReputationTrigger.FiniteHorizon.finite_game_oneshot`, `finite_game_unravels` |
| pp. 366–369 | Lognormal model: `ρ > 1` sustainable iff `qX ≥ 1`; never for `ρ < 1` or log; `κ`, `τ = exp(ρV/2) − 1` | `ReputationTrigger.Lognormal.sustainable_iff_rho_gt_one`, `not_sustainable_rho_lt_one`, `not_sustainable_log`, `kappa_iff`, `tau_eq` |
| Table 6.1, p. 369 | Every entry as an interval; Venezuela corrected | `ReputationTrigger.table_argentina`, …, `table_venezuela`, `venezuela_flip`, `argentina_beta_085` |
| (17)–(21), pp. 370–373 | Partial insurance: the optimum exists for every utility and is unique; Kuhn–Tucker necessary and sufficient; `C = max(c̄, u⁻¹(u(Y) − Cost))` | `ReputationTrigger.PartialInsurance.optimum_exists_general`, `optimum_unique`, `kuhn_tucker_necessary`, `kuhn_tucker_sufficient`, `optimum_characterisation` |
| p. 370 | Partial insurance can be impossible | `ReputationTrigger.PartialInsurance.two_state_autarky` |
| pp. 366–369 | Trigger strategies are subgame perfect iff (16); multiplicity; not renegotiation-proof | `ReputationTrigger.SubgamePerfection.triggerSPE_iff`, `multiplicity`, `continuum_of_equilibria`, `exclusion_not_renegotiation_proof` |
| §6.1.3, pp. 375–377 | General equilibrium; (22) with finitely many countries is degenerate | `ReputationTrigger.GeneralEquilibrium.ge_trigger_iff`, `idiosyncratic_sum_zero_degenerate` |
| Ex 3, pp. 426–427 | Reputation and investment; self-financing weakens the punishment; no investment loans | `ReputationTrigger.ReputationInvestment.enforceable_iff`, `selffin_unenforceable`, `BulowRogoff.lending_abroad_no_investment_loans` |
| pp. 373–375 | **Bulow–Rogoff** on a general event tree, with growing payments (`g < r`) and in expected-utility form | `BulowRogoff.Theorem.bulow_rogoff`, `stationary_no_reputation`, `Growth.bulow_rogoff_growth`, `bulow_rogoff_expected_utility` |
| p. 373 | Collateral: the steady state; `B̄` necessary and sufficient | `BulowRogoff.Collateral.collateral_dominates_iff`, `steady_state_requires_collateral`, `steady_state_first_best` |
| p. 373 | **Worrall convergence** (seizure only): after the first top shock consumption is `Ȳ + rB̄` or more for ever; the probability of being below tends to 0 geometrically; existence when `B₀ ≥ B̄` | `BulowRogoff.Worrall.optimal_after_top_shock`, `prob_below_steady_state_tendsto`, `shortfall_tendsto`, `settle_optimal`, `steady_optimal` |
| §6.2.2, pp. 391–392 | No sovereign borrowing in a deterministic economy | `BulowRogoff.Deterministic.no_sovereign_borrowing`, `default_when_market_unneeded` |

## §6.2 Sovereign risk and investment (pp. 379–401)

| Book | Claim | Lean |
| --- | --- | --- |
| (23)–(24), pp. 380–381 | Repayment and the sovereign's objective as a maximum; ties repay | `DebtCeiling.repayment_eq_full_iff`, `sovereignObjective_eq_max`, `repay_optimal_of_value_ge` |
| (26)–(30), pp. 383–384 | Log-linear optima; the debt ceiling characterises repayment; comparative statics | `DebtCeiling.logLinear_repay_optimum`, `repay_iff_le_debtCeiling`, `debtCeiling_strictMono_eta`, `debtCeiling_strictAnti_r` |
| p. 385, fn 37 | At the repay optimum, repayment is strictly slack | `DebtCeiling.repayment_slack_strict`, `default_optimum_ne_repay_optimum` |
| p. 387 | The repayment set is an interval under the analogue of (25); fails in general | `DebtCeiling.repay_interval_of_ineq25`, `repaySet_not_interval` |
| (31)–(35), pp. 388–390 | Kuhn–Tucker necessary and sufficient with and without precommitment; dynamic inconsistency | `PrecommitmentInvestment.ceiling_kt_necessary`, `precommit_kt_necessary`, `precommit_ratio_gt_iff`, `dynamic_inconsistency` |
| (36)–(38), fn 43–44 | Market value; `∂V/∂K` by the Leibniz rule; the optimal `K(D)` exists and is differentiable, `K′ < 0` | `DebtOverhangLaffer.marketValue_eq`, `hasDerivAt_marketValue_K`, `optimalInvestment_hasDerivAt`, `optimalInvestment_deriv_neg` |
| p. 394 | Debt overhang without calculus | `DebtOverhangLaffer.investment_antitone` |
| (39), pp. 394–398 | The debt Laffer curve; marginal ≤ average price without concavity; the curve declines, so is not concave | `DebtOverhangLaffer.hasDerivAt_laffer`, `marginal_le_average`, `example_laffer_declines` |
| (40), fn 48, pp. 397–400 | Buybacks hurt the debtor; the Bolivia arithmetic | `DebtOverhangLaffer.buyback_hurts_debtor`, `creditors_gain_from_buyback`, `bolivia_arithmetic` |
| Ex 6, pp. 427–428 | Default investment; Pareto write-down; the creditors' optimal write-down is attained | `DebtOverhangLaffer.ex6a_default_investment`, `ex6b_writedown`, `ex6c_attained` |
| Appendix 6A, (54)–(57), pp. 419–422 | Rubinstein bargaining: the SPE exists and is unique; the share for period length `h` and its limit | `SovereignBargaining.rubinstein_exists_unique`, `spe_unique`, `spe_creditor_share`, `spe_share_limit`, `bargaining_debt_lt_pv` |

## §6.3 Risk sharing with hidden information (pp. 401–407)

| Book | Claim | Lean |
| --- | --- | --- |
| (41)–(42), p. 405 | The incentive constraints as linear inequalities; both bind iff the contract is null | `HiddenInformation.icH_iff_linear`, `icL_iff_linear`, `both_bind_iff_null` |
| pp. 403–404 | Bond equilibrium `r = 0`; autarky < bonds | `HiddenInformation.bond_market_clears_iff`, `eu_autarky_lt_bond` |
| (43), pp. 405–406 | Contract C: consumptions, binding pattern, welfare ranking | `HiddenInformation.contractC_consumption`, `eu_bond_lt_contractC`, `contractC_on_contract_curve` |
| p. 406 | **The optimal IC contract exists and is unique**; off the contract curve | `HiddenInformation.optimal_contract_exists_unique`, `opt_off_contract_curve` |
| fn 59 | The revelation principle | `HiddenInformation.revelation_principle` |
| p. 406 | With ex post bond trade the best allocation is B | `HiddenInformation.bond_trade_best_is_B` |

## §6.4 Moral hazard in international lending (pp. 407–419)

| Book | Claim | Lean |
| --- | --- | --- |
| (44), p. 408 | Efficient investment exists, is unique, maximises | `MoralHazardSmallCountry.efficient_investment_exists_unique` |
| (46)–(49), fn 66, Fig. 6.11 | Best response (interior or corner); IC and ZP curves; unique crossing | `MoralHazardSmallCountry.bestResponse_of_foc`, `zpCurve_strictMonoOn`, `equilibrium_exists_unique` |
| pp. 410–412, fn 65 | The optimal contract exists and is unique; Kuhn–Tucker with a constraint qualification | `MoralHazardSmallCountry.Setting.optimal_contract_exists_unique`, `licq_at_optimum`, `kt_multipliers_at_optimum` |
| p. 412 | Comparative statics; the inflow claim: exact condition and counterexample | `MoralHazardSmallCountry.eqm_strictMono_wealth`, `inflowFn_deriv_neg_iff`, `p412_counterexample` |
| p. 413 | Investment concave in wealth iff inflows concave; counterexample | `MoralHazardSmallCountry.eqmI_strictConcave_iff`, `inequality_lowers_average_investment`, `p413_counterexample` |
| §6.4.3, p. 416 | Risk aversion: an optimal contract exists and is below first best; risk iff investment; the optimum can be riskless | `MoralHazardSmallCountry.ra_optimal_contract_exists`, `ra_below_first_best`, `ra_risky_iff_invest`, `cara_no_investment` |
| Ex 4–5 | Collateral and overhang equivalences; constrained efficiency | `MoralHazardSmallCountry.ex4a_collateral_raises_investment`, `ex4b_overhang_lowers_investment`, `ex5_constrained_efficient` |
| (50)–(53), fn 67, Fig. 6.12 | Two countries: the rate function; **equilibrium exists and is unique**; efficient iff equal wealth; output loss | `MoralHazardTwoCountry.rho_hasDerivAt_I`, `eqm_exists_unique`, `eqm_efficient_iff`, `output_loss` |
| p. 415 | The richer country always lends | `MoralHazardTwoCountry.richer_country_lends` |
| p. 415 | Foreign government debt depresses Foreign investment; multiplicity | `MoralHazardTwoCountry.debt_depresses_foreign`, `small_debt_multiple_equilibria` |
| Ex 4(b) | Full tax equilibrium, trap multiplicity, regime switch | `MoralHazardTwoCountry.ex4b_existence`, `ex4b_two_equilibria`, `ex4b_regime_switch` |
