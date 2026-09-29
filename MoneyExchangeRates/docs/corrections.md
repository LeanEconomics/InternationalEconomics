# Corrections to the source

Places where a claim in Chapter 8 of Obstfeld and Rogoff (1996), or its
Supplement, is false, imprecise, or relies on an unstated hypothesis. In each
case the Lean statement proves the corrected version and cites the original.

## Claims that are wrong or need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| (77), p. 564 | `ē = log(B_H + B_F)`. | Should be `log(B_H + ℰ̄B_F)` (`SpeculativeAttack.printed_77_wrong`, `attackTime_corrected`). |
| p. 564 | The attack date with `μ = 0`. | The formula divides by zero: without bubbles a peg with positive reserves is never attacked; with bubbles every date is an attack date (`SpeculativeAttack.no_attack_without_growth`, `attack_without_growth_any_date`). |
| (86), p. 574 | The second moment of the regulated increment is `hv²`. | It is `E(dk)²/2`; the conclusion survives through the mean term (`TargetZone.regulated_second_moment`, `regulated_mean`). |
| App. 8A, p. 597 | The government budget constraint. | Sign error: it must read `T_t = −ΔM/P_t`; as printed total money is forced constant (`CashInAdvance.appendix8A_taxes`, `appendix8A_printed_sign`). |
| (100), p. 583 | `ε ≥ 0`. | Must be positive: a zero shock makes money vanish (`NominalAssetPricing.no_positive_money_of_eps_zero`). |
| p. 536 | Outside `σ = θ = 1` nominal rates affect consumption. | Equilibrium consumption is independent of the price-index path iff `σ = θ` (`MoneyInUtility.dichotomy_iff`). |
| p. 539 | Paths below the steady state diverge. | With log utility they reach negative real balances in finite time (`MonetaryBubbles.log_no_hyperinflation`). |
| §8.3.5.3 | Transversality rules out deflations. | Needs `μ ≥ 0`; with `β < 1+μ < 1` every `m₀ ≥ m̄` is an equilibrium (`MonetaryBubbles.log_equilibria_multiple`). |
| fn 32, p. 543 | Transversality generally rules out deflations. | Exactly when `Σ v′(m_t) = ∞` (`MonetaryBubbles.tvc_iff_not_summable`); verified deflationary equilibria for `v = am + log m` and `v = ∫ dt/log(t+e)` (`linlog_deflation_equilibrium`, `logInt_deflation_equilibrium`). |
| fn 34 | The condition for hyperinflations. | Necessary, not sufficient (`MonetaryBubbles.vSlow_counterexample`). |
| Fig. 8.3 | Collapse at period `T − 1`. | A collapse date needs some `m*` with `C̄v′(m*) = 1`; otherwise balances fall to 0 only asymptotically (`MonetaryBubbles.hyperinflation_asymptotic`). |
| (67), p. 553 | The dollarization threshold `a₀ > 1 − β`. | In general `a₀ > 1 − β/π*`; needs positive home nominal rates; (66) is a Kuhn–Tucker inequality at the corner (`MoneyInUtility.dollar_eventually_iff`, `dollar_foreign_kkt_of_optimal`). |
| p. 582 | Existence and uniqueness assuming no bubbles. | Uniqueness among bounded solutions; transversality rules out bubbles iff `(1+μ) min ε ≥ 1`, which forces `μ ≥ 0`; for `μ < 0` a bubble satisfies transversality; `1 + μ > β` is necessary for any positive solution (`NominalAssetPricing.Solutions.unique_bounded`, `depthBubble_TVC_of_neg`, `no_positive_solution`). |
| (97), p. 581 | The Fisher relation holds only if the covariance is zero. | If and only if (`NominalAssetPricing.fisher_iff_cov_zero`). |
| (23), p. 525 | The seignorage-maximising rate from the first-order condition. | `μ = 1/η` is the unique global maximum (`CaganModel.seignorage_lt_max`). |
| Supplement, p. 748 | The maximum-principle conditions with (15). | (15) is not sufficient without a no-Ponzi condition on rivals (`MaximumPrinciple.ponzi_counterexample`), not necessary in general (`halkin_candidate`), but necessary for the monetary problem (`monetary_optimal_iff`); `λ ≥ 0` is specific to this problem. |
| Supplement A.3.3 | “One can then show” the nominal-rate formula. | It is the unique solution of an unstable ODE with a no-bubble condition (`MaximumPrinciple.xStar_unique`). |
| p. 548 | The cash-in-advance constraint always binds. | Needs strictly increasing utility and `i > 0`; at date 0 an inequality (`CashInAdvance.cia_binds`). |
| Ex 4 | (60). | Holds with `r_{s+1}` (`CashInAdvance.euler_60_iff`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| fn 6, (8) | Convergence of the forward solution. | Summability of `q^s m_s`; the growth-rate condition is proved sufficient (`CaganModel.caganSummable_of_growth`). |
| (14) | The Gaussian AR(1) money process. | Replaced by a Markov eigen-relation, valid for any `ρ ≤ 1` (`CaganModel.markovFundamental_eigen`). |
| p. 536, Ex 3 | Existence of the CES optimum. | Needs summability of the discount-weight series (`MoneyInUtility.ces_isOptimal_of_closedForm`). |
| (106), (109), (119) | Lognormality. | Proved for genuine (jointly) Gaussian variables and as exact finite-state decompositions (`ForwardPremium.Gaussian.log_forward_gaussian`, `JointGaussian.eq109_gaussian`, `forward_exact_decomposition`). |
| p. 578 | Reserves run out. | Proved with probability 1 on the lattice, counting reserve losses at the ceiling (`TargetZone.reserves_exhausted_almost_surely`). |

## Not formalised

| Where | Claim | Status |
| --- | --- | --- |
| §8.5 | Continuous-time smooth pasting as a necessary condition (Itô calculus, local time). | Replaced by the explicit solution and the lattice model with its continuous limit. |
| Ex 8(c) | Hansen–Hodrick GMM. | Econometric, out of scope. |
