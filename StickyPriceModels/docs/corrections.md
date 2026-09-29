# Corrections to the source

Places where a claim in Chapter 10 of Obstfeld and Rogoff (1996) is false,
imprecise, or relies on an unstated hypothesis. In each case the Lean statement
proves the corrected version and cites the original.

## Claims that are wrong or need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| p. 688 | Country size does not affect the current account. | It does, by (67); the size-free quantity is `b̄/(1−n)` (`ReduxMoneyShocks.country_size_correction`). |
| p. 684, fn 19 | A Foreign expansion raises Home welfare as long as `χ` is not too large. | Exactly: for every `χ` iff `θ² − 2θ − 1 ≤ δ(1+θ)`, otherwise iff `χ` is below an explicit threshold; at `θ = 6`, `δ = 0.05`, `χ = 0.2` Home welfare falls (`ReduxWelfare.foreign_shock_welfare_pos_iff`, `welfare_threshold`, `counterexample_theta6`). |
| (65), p. 681 | `e < m − m*`. | Needs `m − m* > 0`; in general `|e| < |m − m*|` (`ReduxMoneyShocks.eq65_sign`). |
| p. 677 | `b_t = b̄` for all `t ≥ 2`. | Only to first order; exactly `B̄ = (1+r₂)B₂/(1+δ)` (`ReduxMoneyShocks.longrun_assets`). |
| pp. 674, 692 | Output is demand-determined for small shocks. | Exactly while the money ratio is at most `√(θ/(θ−1))` (`ReduxMoneyShocks.equiproportionate_demand_bound`, `NontradablesOvershooting.shock_equilibrium_iff`). |
| fn 16, p. 681 | A temporary money expansion. | Leaves the Home currency permanently appreciated, which the book does not say (`ReduxMoneyShocks.temporary_shock_appreciation`). |
| (91), p. 692 | Tradables consumption equals the endowment. | Needs a no-bubble condition on discounted real money (`NontradablesModel.cT_eq_endowment_iff`). |
| (81), p. 688 | A Foreign expansion lowers Home welfare for large enough `θ`. | Exactly iff `τᴸ(θ−1)² > δ(1+θ) + 2` (`ReduxWelfare.welfare81_neg_iff`). |
| Ex 1 | The timing of the money-growth change. | Ambiguous; if the new rate starts at date 2 the intercept is `ν/ī` rather than `ν(1+ī)/ī` (`ReduxMoneyShocks.ex1_growth_shock_late`). |
| Ex 2 | The real exchange rate. | Never defined; with `Q = ℰP*/P`, real interest parity holds exactly (`NontradablesOvershooting.real_interest_parity`). |
| Ex 4(d)–(e) | The one-shot inflation game. | The penalty is on gross inflation; the answer holds for that objective, but commitment then has no optimum, and "one-shot" drops a next-period term; with `(π−1)²` the equilibrium differs (`CashInAdvanceCredibility.commitment_gross_no_optimum`, `fullObj_sub`, `conventional_equilibrium`). |
| (142)–(143), p. 710 | The labour normalisation. | (143) requires total hours; the per-firm reading changes `κ` to `4κ` (`ReduxPresetWages.normalisation_flag`). |
| p. 712 | Pass-through with linear demand is incomplete. | Always below one half (`PassThrough.lin_passThrough_bounds`). |

## Claims confirmed or sharpened

| Where | Claim | Lean |
| --- | --- | --- |
| p. 668 | No simple closed form for the steady state. | The steady state exists and is unique for every net foreign asset position (`ReduxSteadyState.exists_unique_steady`). |
| (58)–(60) | No overshooting. | Holds exactly in the nonlinear model (`ReduxMoneyShocks.no_overshooting_exact`). |
| (99), p. 693 | Overshooting iff `ε > 1` to first order. | Exactly, and (99) is the derivative of the exact impact (`NontradablesOvershooting.overshoot_iff`, `hasDerivAt_impact`). |
| pp. 694, 700, 703–706 | Welfare gains stated in words. | Exact or closed-form (`NontradablesOvershooting.welfare_gain_eq`, `ReduxFiscalProductivity.productivity_welfare`, `gov_permanent_welfare`). |
| pp. 671–673 | The log-linear system. | Exactly the derivative of the nonlinear steady-state map (`ReduxLinearisationLink.linearisation_link_system`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| (16), p. 666 | The discount factor `R` and a no-Ponzi condition. | `R_T = Π(1+r_s)⁻¹`; no-Ponzi added; transversality proved necessary (`ReduxPrimitives.HouseholdEnv.isOptimal_iff`). |
| §10.4.2 | A continuum of labour types. | Finitely many types with weights summing to one; the CES argument is identical. |
