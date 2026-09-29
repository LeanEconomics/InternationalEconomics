# Corrections to the source

Places where a claim in Chapter 9 of Obstfeld and Rogoff (1996) is false,
imprecise, or relies on an unstated hypothesis. In each case the Lean statement
proves the corrected version and cites the original.

## Claims that are wrong or need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| p. 632 | Under a peg, a fall in `q̄` brings unemployment and falling prices. | **Sign error.** A fall in `q̄` (real appreciation) gives a boom with rising prices (`DornbuschExtensions.peg_real_appreciation_boom`); the book's story holds for a rise in `q̄` (`peg_real_depreciation_slump`). |
| p. 632, Ex 3(d) | The optimal feedback coefficient tends to `∞` as real shocks vanish, and lies between 0 and ∞. | **Sign error.** `Φ* < η` and `Φ* → −∞`; the peg is a limit, never attained by a finite rule (counterexample `Φ* ∈ (−19.5, −19)`, `PooleRegimeChoice.signExample_optimalPhi`, `optimalPhi_tendsto_atBot`, `feedback_peg_only_limit`); with no real shocks no optimal finite rule exists (`no_optimal_rule_of_eps_zero`). |
| Ex 3 | The feedback rule selects a unique equilibrium. | Bounded equilibrium output is unique iff `Φ < 1` or `Φ > 1 + 2η` (`PooleRegimeChoice.bounded_eqm_output_unique_iff`); on the closed region, boundary included, bounded sunspot equilibria exist (`boundary_sunspot_eqm`, `sunspot_at_phi_one`, `sunspot_at_phi_one_add_two_eta`), and the book's optimal rule can fall there (`indetExample_optimalPhi`). |
| p. 612 | Convergence needs `ψδ < 1`. | `0 < ψδ < 2` suffices; `ψδ < 1` gives monotone convergence; `ψδ > 2` diverges (`DornbuschModel.q_tendsto`, `q_oscillates`, `q_diverges`). |
| p. 616 | Output rises temporarily after a money shock. | At every date only if `ψδ < 1`; for `1 < ψδ < 2` it oscillates (`DornbuschShocks.perm_shock_output_oscillates`). |
| p. 613 | One cannot argue rigorously for the saddle path. | Within the model the saddle path is exactly the set of convergent, bounded and no-bubble paths (`DornbuschModel.converges_iff_on_saddle`, `bounded_iff_on_saddle`, `no_bubble_iff_on_saddle`). |
| p. 619 | The stochastic version is straightforward. | The Phillips curve must carry `E_t p̃`; uniqueness holds under no bubbles and bubble solutions exist (`DornbuschExtensions.Stochastic.stoch_exists_unique_no_bubble`, `stoch_bubble_solutions`). |
| Ex 2 | Use (6)–(7). | They assume constant `q̄`; with an anticipated change the model must be worked from (5) (`DornbuschExtensions.naive_seven_wrong`, `reducedTV_iff`). |
| Ex 1 | The date-0 money path. | Ambiguous; both readings are proved, with jumps `(1+η)μ` and `ημ` (`DornbuschShocks.disinflation_literal_impact`, `disinflation_alt_impact`). |
| p. 624 | The half-life is roughly 4.2 years. | It lies in `(4.264, 4.266)` (`ExchangeRateFacts.halfLife_bounds`). |
| p. 628 | The regression in logs of ratios. | Read as logs of ratios the intercept implies an elevenfold ratio at zero inflation; the equation fits logs of the 100-based indices (`ExchangeRateFacts.gd_ratio_reading_inconsistent`, `gd_index_reading_consistent`). |
| Fig. 9.12 | Three equilibria, the low one on the flat branch. | The drawn picture needs `c̄ > c̲` (`EscapeClausePeg.exactly_three_needs_cbar_gt`); three equilibria are possible with equal costs, on the convex branch (`three_eqm_symmetric_costs`). |
| fn 40 | The condition for `π^e = k/χ`. | It characterises the free-float regime (`EscapeClausePeg.float_eqm_iff`); `k/χ` can be an equilibrium without it (`fn40_not_necessary`); exactly three equilibria needs it strictly (`fn40_equality_two`). |
| p. 641 | Any rate between 0 and `k/χ`, even negative rates, can be sustained. | The sustainable set is exactly `[π̲(β), k/χ]`; negative rates need `β > χ/(1+2χ)` strictly (`ReputationEquilibria.trigger_eqm_iff_bounds`, `negative_sustainable_iff`). |
| fn 42 | Nash and planner levels. | Expected money growth is zero in both; the Nash equilibrium is unique iff `(a₁²+χ)² ≠ a₁²a₂²` (`PolicyCoordination.nash_expect_zero`, `nash_nonunique_of_det_zero`). |
| p. 655 | Both countries can stabilise output exactly. | Iff `a₁² ≠ a₂²` (`PolicyCoordination.two_instruments_iff`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| p. 642 | Rogoff's conservative central banker. | Needs `k > 0` and `σ² > 0`; the degenerate cases are separate (`CentralBankDelegation.no_bias_optimum`, `no_shock_limit`); no conservative banker reaches the commitment value (`socialLoss_gt_commit`). |
| Ex 4 | Independence of the shocks. | Only `E[λz] = 0` is used. |
| pp. 639–641 | Punishment lasts for ever. | Stated; one-period punishments are handled separately (`ReputationEquilibria.onePeriod_eqm_iff_bounds`). |

## Not formalised

| Where | Claim | Status |
| --- | --- | --- |
| pp. 633–634, 653–654 | Optimum currency areas; openness and inflation. | Verbal; no model to formalise. |
