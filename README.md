# International Economics in Lean

Checked international macroeconomics, following Obstfeld and Rogoff (1996),
*Foundations of International Macroeconomics* (MIT Press). Each folder is an
independent Lean/Mathlib project for one chapter, with precise statements, a
source map to the book's equations and pages, and reproducible proof checks.

| Project | Chapter | Checked results | Start here |
| --- | --- | --- | --- |
| [IntertemporalTrade](IntertemporalTrade/README.md) | 1. Intertemporal Trade and the Current Account Balance | 2 theorems: the two-period budget line and the current-account identity (scaffold) | [Source map](IntertemporalTrade/docs/source-map.md) |
| [SmallOpenEconomyDynamics](SmallOpenEconomyDynamics/README.md) | 2. Dynamics of Small Open Economies, with Supplements A–C | 1 theorem: the two forms of the period budget constraint (scaffold) | [Source map](SmallOpenEconomyDynamics/docs/source-map.md) |
| [LifeCycleFiscalPolicy](LifeCycleFiscalPolicy/README.md) | 3. The Life Cycle, Tax Policy, and the Current Account | 2 theorems: log-utility OLG demands exhaust wealth and satisfy the Euler equation (scaffold) | [Source map](LifeCycleFiscalPolicy/docs/source-map.md) |

## Scope

The three projects formalise the book's first three chapters. These are its
"real", one-good, discrete-time chapters: the two-period Fisher economy
and world equilibrium, the infinite-horizon small open economy (intertemporal
budget constraint, permanent-income current account, Hall's random walk, Tobin's
q), and overlapping-generations fiscal policy (Ricardian equivalence and its
failure, the Diamond model, Weil's perpetual youth, dynamic inefficiency).
Provable end-of-chapter exercises are included.

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

and the same in `SmallOpenEconomyDynamics/` and `LifeCycleFiscalPolicy/`.

The verifier builds the complete project, freshly recompiles every contributed
proof without importing its compiled project module, and audits each named
declaration's transitive axioms. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. Warnings, failed proofs, or placeholder axioms fail
the check. Every file carries the Apache 2.0 header that Mathlib's header linter
checks. GitHub Actions runs all three projects independently on pushes and pull
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
