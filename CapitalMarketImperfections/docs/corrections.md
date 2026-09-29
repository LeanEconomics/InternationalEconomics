# Corrections to the source

Places where a claim in Chapter 6 of Obstfeld and Rogoff (1996) is false,
imprecise, or relies on an unstated hypothesis. In each case the Lean statement
proves the corrected version and cites the original.

## Claims that are wrong or need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| p. 405 | (41) and (42) cannot both bind, since that would force `Ȳ = Y`. | Both bind **iff the contract is null** (`P₁ = P₂ = 0`), for every `Y < Ȳ`; a nonzero contract has at most one binding (`HiddenInformation.both_bind_iff_null`). |
| p. 412 | Investment rises by less than `Y₁`, so capital inflows fall. | **False in general.** Exact local condition `(I − Y₁)π′/π² < −π″/π′²` (`MoralHazardSmallCountry.inflowFn_deriv_neg_iff`); counterexample `π(I) = I/(1+I)`, `Z = 5/2`, `r = 0`: raising `Y₁` from `7/300` to `1/16` raises `I` from `1/5` to `1/4` and inflows from `53/300` to `3/16` (`p412_counterexample`). |
| p. 415 | A seemingly perverse flow of savings from Foreign to Home can occur. | **Impossible in this model**: if Home is richer it is a strict net lender (`MoralHazardTwoCountry.richer_country_lends`). |
| p. 413 | Under plausible conditions investment is strictly concave in `Y₁`, so inequality lowers average investment. | Exactly when capital inflows are strictly concave (`MoralHazardSmallCountry.eqmI_strictConcave_iff`); true for `π = I/(1+I)`, false for a mixture technology, where equality lowers average investment (`p413_counterexample`). |
| p. 415 | Foreign government debt shifts ρρ up and lowers Foreign investment. | True in every equilibrium (`MoralHazardTwoCountry.debt_depresses_foreign`), but debt destroys uniqueness: small debts give at least two equilibria, large debts none (`small_debt_multiple_equilibria`, `debt_no_eqm_of_large`). |
| p. 416 | The optimal contract under risk aversion leaves consumption exposed to production risk. | Consumption is risky iff investment is positive (`MoralHazardSmallCountry.ra_risky_iff_invest`); with CARA utility, `π = 1 − e^{−I}` and `kR ≥ 1` the optimum has no investment and no risk (`cara_no_investment`). |
| Table 6.1, p. 369 | Venezuela: κ “Undefined”; Venezuela alone would never default. | From the printed inputs `qX < 1`, so κ ∈ (4.2, 4.3) is finite and the sustainability claim fails (`ReputationTrigger.venezuela_qX_lt_one`, `venezuela_not_sustainable`); the verdict flips at σ ≈ 0.1185 (`venezuela_flip`). Also Brazil κ ∈ (0.23, 0.235) (printed 0.24), Philippines rounds to 0.25 (printed 0.24), Lesotho 0.5376 (printed 0.53). |
| p. 370 | Can partial insurance be sustained? “Yes.” | Not always: with two states and small `β` only the null contract satisfies (13) and (18) (`ReputationTrigger.PartialInsurance.two_state_autarky`). |
| (22), p. 376 | Idiosyncratic i.i.d. shocks summing to zero across countries. | With finitely many countries this forces every shock to be zero (`ReputationTrigger.GeneralEquilibrium.idiosyncratic_sum_zero_degenerate`); the setup needs a continuum of countries or dependent shocks. |
| Ex 2(a), hint | `C(ε) = X(ε)` at the worst shock. | False when debt service exceeds the worst shock and sanctions are strong; correct statement: `P(ε) = 0` iff `X(ε) ≤ c̄` (`SanctionsWithSaving.indexed_hint_fails`, `indexed_zero_payment_iff`). |
| p. 361 | The bond interpretation gives results not very different from insurance. | Indexed debt is never better and strictly worse whenever the insurance constraint binds, with a strictly higher full-insurance threshold (`SanctionsWithSaving.indexed_strictly_worse`, `threshold_comparison`). |
| p. 387 | For any debt below `D̄` the sovereign repays. | False in general (concave `u`, `F` counterexample: default at `D = 1/2`, repay at `D = 5/2`, `DebtCeiling.repaySet_not_interval`); true under the analogue `η(1 + F′(K^N)) < 1 + r` of (25) at the repay optimum (`repay_interval_of_ineq25`). |
| p. 385, fn 37 | The debt ceiling is where the repay optimum hits the kink. | At an interior repay optimum repayment is strictly slack (`DebtCeiling.repayment_slack_strict`). |
| p. 390 | Verify the inequality using (25). | The ratio exceeds `1 + α` iff `α > r`; (25) only makes the denominator positive (`PrecommitmentInvestment.precommit_ratio_gt_iff`). |
| p. 395 | The debt Laffer curve is concave, as drawn. | Inconsistent with its downward-sloping part: a nonnegative concave function on `[0, ∞)` is nondecreasing (`DebtOverhangLaffer.laffer_not_concave_of_decreasing`), and an explicit model has a declining curve (`example_laffer_declines`). Marginal ≤ average price needs no concavity (`marginal_le_average`). |
| fn 44 | `U″ < 0` must hold at the optimum. | Only `U″ ≤ 0` is necessary (`DebtOverhangLaffer.soc_nonpos`). |
| Appendix 6B, p. 425 | The threshold lies in `(−ε̄, 0)`. | Sharper: `(−ε̄/3, 0)` (`SanctionsWithSaving.threshold66_bounds`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| p. 408 | Success probabilities. | `π ≤ 1` is added; the existence and uniqueness of efficient investment are then derived, as is continuity of `π′`. |
| (47), p. 410 | The first-order condition holds with equality. | Only at interior choices; the best response is `min(Y₁ + D, I*)`, and `P(0) = 0` is derived (`MoralHazardSmallCountry.bestResponse_of_foc`, `Setting.admissible_at_Ie_unique`). |
| fn 65 | Kuhn–Tucker necessity. | A constraint qualification is proved (`MoralHazardSmallCountry.licq_at_optimum`). |
| p. 414 | Both countries borrow; equilibrium exists. | Proved to exist and be unique for all positive wealths, allowing self-financing (`MoralHazardTwoCountry.eqm_exists_unique`). |
| pp. 405–406 | The low type can pose as high. | That deviation may need negative consumption; (42) then holds because it is unavailable (`HiddenInformation.contractC_lowType_deviation_infeasible_example`). |
| §6.1.2.4 | Bulow–Rogoff. | Needs `r > 0` and bounded (or slower-than-`r` growing) payments; the series diverges when `g ≥ r` (`BulowRogoff.Growth.not_summable_fast_growth`). |
| §6.2.2 | Default once the market is unneeded. | Strict only for `β > 0`. |

## Not formalised

| Where | Claim | Status |
| --- | --- | --- |
| §6.4.3, p. 416 | Investment is below first best at the risk-averse optimum. | Open: numerical evidence supports it, but a small-risk-aversion expansion suggests it can fail when `π(Ī) > ½` with low curvature; a certified global optimum of the non-concave problem is out of reach. |
| p. 373 | Worrall convergence for initial assets below `B̄`, and Worrall's combined exclusion-plus-seizure model. | Convergence is proved for any optimal plan, and existence for `B₀ ≥ B̄`; existence below `B̄` needs a principle-of-optimality theory not built here. |
