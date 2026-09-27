# Intertemporal trade and the current account in Lean

This is the `IntertemporalTrade/` proof project in
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Run the commands below from this directory: `cd IntertemporalTrade` from the repository
root. [Return to the library index](../README.md).

A checked formalisation of Obstfeld and Rogoff (1996), *Foundations of
International Macroeconomics*, Chapter 1, “Intertemporal Trade and the Current Account Balance” (pp. 1–58).

The two-period Fisher economy: a small open endowment economy, investment
and Fisher separation, the two-region world equilibrium and the Metzler diagram,
the optimal tax on foreign borrowing, international labour mobility, and the
Marshall–Lerner stability condition.

**Status: phase 0 scaffold.** The library currently contains **2 theorems**,
the model primitives the chapter builds on. The planned modules are listed
below. See the [source map](docs/source-map.md) for the correspondence with the
book, and [corrections](docs/corrections.md) for the places where a printed
claim is false or imprecise and the Lean statement differs.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Model](IntertemporalTrade/Model.lean) | 2 | Two-period small open endowment economy, budget line, CA₁ + CA₂ = 0 |

## Planned modules

| Module | Contents |
| --- | --- |
| Consumer | Two-period problem, existence/uniqueness, Euler (1.3)/(1.4), flat path (1.5), tilt, Ex 1 |
| CurrentAccount | Identities (1.6), (1.12)–(1.14), GNP/GDP, government (1.8), temporary vs permanent shocks |
| AutarkyGains | Autarky rate (1.7), saving-sign lemma, gains from trade, welfare monotone away from r^A, Ex 2(f) |
| Investment | (1.15)–(1.18), Fisher separation, strictly concave PPF, no crowding out |
| Isoelastic | CRRA/log closed forms (1.24)–(1.26), σ→1 and σ→0 limits, CARA, Ex 3, Ex 4, Ex 7 |
| WorldEquilibrium | Existence and r^A < r < r^{A*}, log closed form (Ex 2), Metzler with investment, Blanchard–Summers |
| Duality | Expenditure function, Shephard (1.27), (1.28), Slutsky (1.29)–(1.31) |
| OptimalTax | Offer curve (1.32), r^{A*} < r^τ < r^L, welfare signs, Ex 8 |
| LabourMobility | CRS facts (1.34)–(1.36), factor-price frontier, pattern of labour trade |
| Stability | Walrasian stability (1.39)–(1.40), Marshall–Lerner (1.41) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
