# Corrections to the source

Places where a claim in Chapter 4 of Obstfeld and Rogoff (1996) is false,
imprecise, or relies on an unstated hypothesis. In each case the Lean statement
proves the corrected version and cites the original.

## Claims that are wrong or need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| p. 208 | If `μ_LN/μ_LT ≥ 1`, faster productivity growth in tradables than in nontradables raises the relative price of nontradables. | **False without `Â_T ≥ 0`.** Counterexample: `μ_LT = 1/4`, `μ_LN = 1/2`, `Â_T = −1`, `Â_N = −3/2` gives `p̂ = −1/2` (`BalassaSamuelson.bs_sign_counterexample`). With `Â_T ≥ 0`, `p̂ ≥ Â_T − Â_N > 0` (`bs_price_rises`). |
| p. 212 | The Harrod–Balassa–Samuelson differential `P̂ − P̂* = (1 − γ)[(μ_LN/μ_LT)(Â_T − Â_T*) − (Â_N − Â_N*)]`, with its sign reading. | Silently assumes both countries share the same `μ_LN/μ_LT`; with common technologies but different productivity levels the shares differ unless production is Cobb–Douglas. Proved in general with each country's shares (`BalassaSamuelson.hbs_path_hasDerivAt`), the book's formula under an explicit common-ratio hypothesis (`hbs_common_shares`), and the sign under `Â_T − Â_T* ≥ 0` (`hbs_sign`). |
| p. 209 | A rise in the world interest rate lowers `p` when `μ_LN ≥ μ_LT`. | Needs `μ_LN > μ_LT` strictly; at equality `p̂ = 0` (`BalassaSamuelson.price_falls_with_r`, `price_r_boundary`). |
| p. 251 | A rise in `z^F` raises Foreign's price level relative to Home's, because the prices include transport costs. | Right direction, wrong mechanism. Holding wages and `z^H` fixed, the derivative of `log(P/P*)` in `z^F` is zero at the equilibrium cutoff: the moving limit of integration cancels the explicit `z^F log(1 − κ)` term (`DFSPriceIndex.logRERInCutoff_deriv_zero_at_cutoff`). The book's direction holds for discrete moves, since `log(P/P*)` is maximised at the equilibrium cutoff (`logRERInCutoff_decreases`). |
| p. 254, Fig. 4.13 | Four classes of goods after a rise in `L*/L`, each with a weakly higher Home/Foreign price ratio. | The partition assumes a small shock. For a large shock (relative wage up by at least `1/(1 − κ)²`) a fifth class appears, Home exports that become Foreign exports, whose price ratio jumps from `1 − κ` to `1/(1 − κ)` (`DFSTransportCosts.fifth_class_priceRatio`, `fifth_class_requires_large_shock`). The conclusion holds for every good regardless (`priceRatio_mono`). |
| pp. 241–242 | After a rise in `L*/L` Foreign's real wage falls on every relocated good. | Unchanged at the old cutoff itself, where `wa(z̄) = w*a*(z̄)`; the fall is strict only on the open interval (`DFSStatic.labour_rise_foreign_realWage_relocated`). |
| fn 41, p. 252 | `B̃` is increasing for `κ` small enough. | Precisely: `B̃` is strictly increasing iff `1 + log(1 − κ)(1 + TB·a*(1)/L*) > 0` (`DFSTransportCosts.Btilde_strictMonoOn_iff`). |
| (4.65), p. 252 | `z^H = z^F − log(1 − κ)` for the exponential example. | Interior cutoffs need `z^F ≥ 0` and `z^H ≤ 1`, which forces `κ ≤ 1 − e^{−1}` (`DFSTransportCosts.interior_cutoffs_bound`). |
| Ex 6(d), p. 266 | Wages rise with `α` (assuming `α > r + π`). | The assumption is also necessary: `∂ log w/∂α = log(α/(r + π))` (`BSExtensions.ex6_dlogw_dalpha`, `ex6_w_increasing_in_alpha_iff`). |
| p. 235 | A rising price level raises current tradables consumption when `σ > θ`. | True under conditions the book does not state: positive tradables wealth, `P_s ≥ P_t` with strict inequality somewhere, and a summable weight (`ConsumptionDynamics.tradables_consumption_gt_constant_price`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| (4.2)–(4.5), p. 206 | Strict concavity and Inada conditions, so the first-order conditions have solutions, and both goods are produced. | Fields of `CRSProduction.IntensiveTech`; existence by the intermediate value theorem. |
| p. 216 | The immobile-capital system is solved “except in degenerate cases”. | Precisely `μ_K1 ≠ μ_K2`; without it the solution is not unique (`BSExtensions.immobileCapital_degenerate`). |
| (4.30), fn 30 | Transversality `(1 + r)^{−T}K_T → 0` for the capital identity. | An explicit hypothesis, together with summability (`ConsumptionDynamics.capital_eq_present_value`). |
| pp. 227–228 | Duality with zero consumption when `θ < 1`. | Both goods are essential when `θ < 1`; the duality theorem then requires positive consumption (`CESIndex.cesIndex_le_div_price`). |
| Ex 4(a), p. 265 | “Show that `p`, `C` and `C_T` are constant.” | The missing step, that `(p/P)^θP^σ` is strictly increasing in `p`, is proved (`ConsumptionDynamics.ex4_ratio_strictMonoOn`). |
| §4.5.4 | The shock analysis assumes `A′ < 0`. | The sign results need only `A′(½) < 4`. |

## Not formalised

* The Ex 4(b) chain from constant prices within each regime to constant tradables consumption (both ends are proved separately).
* The transfer's effect on `P/P*` (p. 255) and real wages after a labour shock with transport costs; the relative wage and terms-of-trade effects are proved.
* The comparative statics with transport costs are proved for the book's exponential example `A(z) = e^{1−2z}`; cutoff ordering holds for general `A`.
* Global nonlinear dynamics of Appendix 4B (Fig. 4.15); the linearised saddle is proved.
* Empirical material (Box 4.1, Box 4.2, the applications).
