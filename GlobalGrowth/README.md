# Global linkages and economic growth in Lean

This is the `GlobalGrowth/` proof project in
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Run the commands below from this directory: `cd GlobalGrowth` from the repository
root. [Return to the library index](../README.md).

A checked formalisation of Obstfeld and Rogoff (1996), *Foundations of
International Macroeconomics*, Chapter 7, “Global Linkages and Economic Growth”
(pp. 429–512), with Appendices 7A–7B and the exercises. The library contains
**927 theorems** and audits **1348 declarations**.

Headline results, in the namespace `ObstfeldRogoff.GlobalGrowth`:
* **Solow and its extensions** converge globally and monotonically
  (`SolowModel.solow_global_convergence`, `SolowExtensions.mrw_global_convergence`).
* **Ramsey–Cass–Koopmans**: the optimal path exists and is unique, Euler plus
  transversality is necessary and sufficient, and the path converges monotonically,
  for bounded and for log utility (`RamseyCassKoopmans.book_optimal_existsUnique`,
  `isOptimal_iff_euler_tvc`, `book_convergence`).
* **OLG growth**: from every initial capital stock there is exactly one equilibrium
  path, and it converges (`OLGGrowth.weil_saddle_path`).
* **Endogenous growth**: AK and learning-by-doing optima over the infinite horizon; the
  Romer balanced path is unique for every `σ`, and the economy does not jump to it
  (`AKModel.ak_planner_optimal`, `RomerGrowth.bgp_unique`, `romer_no_finite_arrival`).
* **Stochastic growth**: Brock–Mirman optimality on a Markov chain, the unique
  two-country share `Ψ`, and diversification raising growth
  (`BrockMirman.tsum_lp_eq_value`, `TwoCountryRBC.existsUnique_psi`,
  `PortfolioGrowth.diversification_raises_growth`).

See the [source map](docs/source-map.md) for the correspondence with the book and
[corrections](docs/corrections.md) for where the printed text is wrong or
imprecise.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Model](GlobalGrowth/Model.lean) | 2 | Cobb–Douglas production |
| [SolowModel](GlobalGrowth/SolowModel.lean) | 66 | §7.1.1: the Solow model, golden rule, convergence rates |
| [SolowExtensions](GlobalGrowth/SolowExtensions.lean) | 42 | Human capital, public capital, `δ > 1` |
| [RamseyCassKoopmans](GlobalGrowth/RamseyCassKoopmans.lean) | 177 | §7.1.2: optimal growth, open and world economies |
| [OLGGrowth](GlobalGrowth/OLGGrowth.lean) | 102 | §7.1.2.3: Weil OLG, the global saddle path; Ex 1 |
| [ContinuousTimeLimits](GlobalGrowth/ContinuousTimeLimits.lean) | 43 | Appendix 7A |
| [AKModel](GlobalGrowth/AKModel.lean) | 54 | §7.3.1: AK and learning by doing |
| [RomerGrowth](GlobalGrowth/RomerGrowth.lean) | 124 | §7.3.3: Romer, Kremer, Grossman–Helpman; Ex 3 |
| [BorrowingConstrainedOLG](GlobalGrowth/BorrowingConstrainedOLG.lean) | 68 | §7.2.2.3; Ex 2 |
| [Immigration](GlobalGrowth/Immigration.lean) | 54 | §7.1.2.3 immigration |
| [BrockMirman](GlobalGrowth/BrockMirman.lean) | 80 | §7.4.1, Appendix 7B; Ex 4 |
| [TwoCountryRBC](GlobalGrowth/TwoCountryRBC.lean) | 46 | §7.4.2 |
| [LogLinearRBC](GlobalGrowth/LogLinearRBC.lean) | 25 | §7.4.3 |
| [PortfolioGrowth](GlobalGrowth/PortfolioGrowth.lean) | 44 | §7.3.2: portfolio diversification and growth |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
