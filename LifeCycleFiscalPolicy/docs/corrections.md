# Corrections to the source

Places where a claim in Chapter 3 of Obstfeld and Rogoff (1996) is false,
imprecise, or relies on an unstated hypothesis. In each case the Lean statement
proves the corrected version and cites the original.

## Claims that are wrong or need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| Ex 2(b), p. 195 | With `n > r^A > r`, opening to trade makes everyone worse off. | **False as stated.** With Cobb–Douglas production and log utility, lifetime utility is `U(r) = C − (1 + β)α/(1 − α) · log r + β log(1 + r)`, which tends to `+∞` as `r → 0⁺` (`OLGGainsFromTrade.lifetimeUtility_CD_tendsto_atTop`). So for any parameters some `r < r^A` makes the young strictly better off (`exists_rate_below_autarky_young_gain`), e.g. `α = 1/20`, `β = 9/10`, `n = 1/2`, `r = e^{−7}` (`counterexample_everyone_worse_off`). Corrected: `U` falls on `(0, r*]` and rises on `[r*, ∞)` with `r* = r^A/(1 + n − r^A) < r^A`, so everyone is worse off for `r ∈ [r*, r^A)` (`everyone_worse_off_corrected`). |
| §3.6.3, p. 171, Fig. 3.6 | With public debt there is a stable steady state with less capital and a second, unstable one. | Positive steady states exist only below a debt threshold, since the law of motion tends to `−∞` as `k → 0`. Proved: two steady states when the map rises above the diagonal somewhere (`TwoCountryOLG.TwoCountry.exists_two_steady_states`), and none at all when `x d̄ (1 + n + β)/((1 + n)(1 + β)) ≥ k̄` (`no_steady_state_of_large_debt`). The book never states the threshold. |
| fn 52, p. 186 | Steady-state consumption rises with output. | Also needs `n > 0` (with `r > 0`): at `n = 0`, `c̄ = 0` for every `ȳ` (`PerpetualYouth.weilSteadyC_slope_pos_iff`, `weilSteadyC_zero_growth`). |
| fn 49, p. 184 | When `(1 + r)β > 1 + n` the “steady state” has negative consumption. | Also needs `n > 0`; at `n = 0`, `c̄ = 0` (`PerpetualYouth.weilSteadyC_neg_of_unstable`). |
| fn 25, p. 159 | Per-capita investment `(1 + n)nk̄/(2 + n)` rises with `n`. | Its derivative `(n² + 4n + 2)k̄/(2 + n)²` is positive iff `n > √2 − 2 ≈ −0.586`: true for all `n ≥ 0`, false for `−1 < n < √2 − 2` (`SmallOpenDiamond.investPerCapita_deriv_pos_iff`). |
| fn 24, p. 159 | Per-capita saving rises with `n`. | Its derivative `(s^Y − s^O)/(2 + n)²` is positive iff `s^Y > s^O`; in the model `s^O = −s^Y`, so iff the young save (`SmallOpenDiamond.savingPerCapita_deriv_pos`). |
| p. 188 | A rise in `g` always lowers the long-run debt–output ratio. | Stated without proof. Proved on the stable region `{(1 + r)β < (1 + n)(1 + g), g < r}` for `n ≥ 0` and `0 < β < 1`, via a partial-fraction decomposition (`PerpetualYouth.growthSteadyRatio_strictAntiOn`). |
| p. 177 | A small bond-financed transfer is neutral when bequests are strictly positive. | Needs a global condition to pass from “interior” to “optimum unchanged”. Proved: if the optimum of the unconstrained present-value problem implies nonnegative bequests and the transfer does not exceed the first bequest, it stays optimal (`RicardianEquivalence.interior_bequest_neutrality`). A transfer to the old is always absorbed; only a tax on the old needs “small”. |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| (3.66), p. 183 | Every vintage faces the same output and tax path. | Explicit; a general version with vintage-specific human wealth is also proved (`PerpetualYouth.weil_aggregate_consumption_general`). |
| (3.3)–(3.8), (3.59) | Transversality or no-Ponzi conditions and summable present values. | Explicit hypotheses; the telescoping lemma is copied from `SmallOpenEconomyDynamics` so the project builds on its own. |
| Fig. 3.5, p. 169 | Global convergence of the two-country OLG model is argued from the figure. | Proved: every orbit from `k₀ > 0` converges monotonically to `k̄` (`TwoCountryOLG.TwoCountry.psi_global_convergence`). |
| p. 171 | Debt crowds out capital when `r ≥ n`. | Holds for every `r > 0`, `n > −1`: the crowding-out bracket is `(1 + n + β + βr)/((1 + n)(1 + β)) > 0` (`TwoCountryOLG.TwoCountry.crowding_bracket_pos`). |
| §3.5, pp. 165–166 | The date-`t` young earn the world-rate wage, so capital jumps at `t`. | Stated as the timing assumption; with predetermined capital the date-`t` young gain instead (`OLGGainsFromTrade.dateT_young_predetermined_hasDerivAt`). |
| Ex 3, p. 196 | Timing of annuity holdings. | Parts (c)–(e) fit together only if `b^v_t` is the annuity carried out of date `t − 1`; with that reading (e) is verified as stated. |
| pp. 192–193 | “Reducing capital makes everyone better off” when `r̄ < z`. | Needs some lower capital level with `f' ≤ z`; one exists by continuity of `f'` (`DynamicInefficiency.exists_lower_capital`). |

## Not formalised

* The converse of dynamic inefficiency (Cass 1972): the book defers it to Chapter 7.
* The §3.6.4 claim that “in at least one country the initial young and all future generations must lose”: no hypotheses are stated.
* Bernheim–Bagwell, Drazen and Figure 3.8 (§3.7.2): informal.
* Empirical applications (pp. 141–147, Feldstein–Horioka) and the Ex 4 transition path.
