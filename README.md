# International Economics in Lean

Checked international macroeconomics, following Obstfeld and Rogoff (1996),
*Foundations of International Macroeconomics* (MIT Press). Each folder is an
independent Lean/Mathlib project for one chapter, with precise statements, a
source map to the book's equations and pages, and reproducible proof checks.

| Project | Chapter | Checked results | Start here |
| --- | --- | --- | --- |
| [IntertemporalTrade](IntertemporalTrade/README.md) | 1. Intertemporal Trade and the Current Account Balance | 272 theorems: gains from trade and the trade pattern by revealed preference, world equilibrium existence and efficiency, Fisher separation, the optimal tax on borrowing, labour mobility, Marshall–Lerner | [Chapter overview](IntertemporalTrade/README.md) |
| [SmallOpenEconomyDynamics](SmallOpenEconomyDynamics/README.md) | 2. Dynamics of Small Open Economies, with Supplements A–C | 379 theorems: transversality ⇔ intertemporal budget constraint, Euler sufficiency and necessity, the fundamental current-account equation, Hall's martingale, Campbell's present-value test, Tobin's q saddle path, firm value = capital, trend growth and the debt–output ratio | [Chapter overview](SmallOpenEconomyDynamics/README.md) |
| [LifeCycleFiscalPolicy](LifeCycleFiscalPolicy/README.md) | 3. The Life Cycle, Tax Policy, and the Current Account | 288 theorems: Ricardian equivalence and its failure, Barro altruism, the debt-financed transfer, the small open Diamond economy, global stability of the two-country OLG model, Weil's perpetual youth, dynamic inefficiency, tax smoothing | [Chapter overview](LifeCycleFiscalPolicy/README.md) |
| [RealExchangeRate](RealExchangeRate/README.md) | 4. The Real Exchange Rate and the Terms of Trade | 281 theorems: Balassa–Samuelson with exact log-derivatives and corrected signs, the CES price index and duality, consumption dynamics, the Dornbusch–Fischer–Samuelson model with transport costs, costly capital and a saddle-point theorem | [Chapter overview](RealExchangeRate/README.md) |
| [InternationalFinancialMarkets](InternationalFinancialMarkets/README.md) | 5. Uncertainty and International Financial Markets | 503 theorems: full insurance iff fair prices, first-order conditions necessary and sufficient, Epstein–Zin, comparative advantage for arbitrary preferences, global risk sharing and the planner, spanning iff full rank (correcting the book's `S ≤ N+1`), the consumption CAPM and Hansen–Jagannathan, Lucas's welfare cost in exact form, stochastic infinite-horizon pricing and bubbles, infinite event trees, the consumption–portfolio problem with a verification theorem | [Chapter overview](InternationalFinancialMarkets/README.md) |
| [CapitalMarketImperfections](CapitalMarketImperfections/README.md) | 6. Imperfections in International Capital Markets | 738 theorems: optimal contracts under sovereign risk for every utility, reputation and trigger strategies as an infinite-horizon game, Bulow–Rogoff on an event tree, Worrall convergence, the debt ceiling and debt overhang, a declining Laffer curve, Rubinstein bargaining, hidden information and moral hazard with equilibrium existence and uniqueness | [Chapter overview](CapitalMarketImperfections/README.md) |
| [GlobalGrowth](GlobalGrowth/README.md) | 7. Global Linkages and Economic Growth | 927 theorems: global convergence of Solow and its extensions, Ramsey–Cass–Koopmans existence, uniqueness and convergence with Euler plus transversality, the global OLG saddle path, AK and Romer growth with transition dynamics, borrowing-constrained OLG, immigration, Brock–Mirman on a Markov chain, the two-country RBC share, portfolio diversification and growth | [Chapter overview](GlobalGrowth/README.md) |
| [MoneyExchangeRates](MoneyExchangeRates/README.md) | 8. Money and Exchange Rates under Flexible Prices | 820 theorems: the Cagan model with bubbles and the unique no-bubble solution (deterministic, stochastic, continuous time), seignorage, speculative attacks, target zones with smooth pasting and a lattice limit, money in utility and the dichotomy, deflationary bubbles and hyperinflations, dollarization, cash in advance, nominal asset pricing with whole-plan optimality, Siegel and Fama, and the maximum principle | [Chapter overview](MoneyExchangeRates/README.md) |
| [NominalRigidities](NominalRigidities/README.md) | 9. Nominal Price Rigidities: Empirical Facts and Basic Open-Economy Models | in progress | [Chapter overview](NominalRigidities/README.md) |

## Scope

The projects formalise the book's chapters in order: the two-period
Fisher economy and world equilibrium, the infinite-horizon small open economy
(intertemporal budget constraint, permanent-income current account, Hall's
random walk, Tobin's q), overlapping-generations fiscal policy (Ricardian
equivalence and its failure, the Diamond model, Weil's perpetual youth, dynamic
inefficiency), the real exchange rate with traded and nontraded goods
(Balassa–Samuelson, the Dornbusch–Fischer–Samuelson continuum),
international financial markets under uncertainty (complete markets, risk
sharing, portfolio diversification, asset pricing), and imperfections in
international capital markets (sovereign risk, reputation, debt overhang,
bargaining, hidden information, moral hazard), growth (Solow,
Ramsey–Cass–Koopmans, OLG, endogenous and stochastic growth), and money and
exchange rates under flexible prices (Cagan, speculative attacks, target zones,
money in utility, nominal asset pricing), with uncertainty as a finite set
of states or a tree of histories. Provable end-of-chapter exercises are included. The
projects together check 4208 theorems.

Where the book argues from a diagram, the Lean statement is a theorem with
explicit hypotheses. Where the book leaves a hypothesis implicit (interiority,
strict concavity, summability, transversality, stability), it is stated. Where
the book's claim is false or imprecise as printed, the corrected statement is
proved and the change is recorded in that project's `docs/corrections.md`.

## Build and verify

Install [elan](https://github.com/leanprover/elan) and Python 3.12+. Each project
pins Lean and Mathlib `v4.34.0`, and its Lake manifest pins transitive
dependencies. From the repository root:

```sh
cd IntertemporalTrade
lake exe cache get
python scripts/verify.py
```

and the same in `SmallOpenEconomyDynamics/`, `LifeCycleFiscalPolicy/`,
`RealExchangeRate/` and `InternationalFinancialMarkets/`.

The verifier builds the complete project, freshly recompiles every contributed
proof without importing its compiled project module, and audits each named
declaration's transitive axioms. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. Warnings, failed proofs, or placeholder axioms fail
the check. Every file carries the Apache 2.0 header that Mathlib's header linter
checks. GitHub Actions runs all five projects independently on pushes and pull
requests. The generated `verification/verification.json` records source hashes
and axiom lists. Proof checking happens in Lean's kernel; the JSON is a record
of a run.

The layout follows
[LeanEconomics/EconomicGrowth](https://github.com/LeanEconomics/EconomicGrowth).
Each project is self-contained: a lemma needed by more than one chapter is
copied into each project that uses it, rather than shared through a
cross-project dependency.

## Development and provenance

These contributions are developed with **Claude Code** (Anthropic), under the
direction of Robert Kirkby. The book is cited by equation and page number and is
not reproduced; see each project's `THIRD_PARTY_NOTICES.md`.

## License

Apache License 2.0; see [LICENSE](LICENSE).
