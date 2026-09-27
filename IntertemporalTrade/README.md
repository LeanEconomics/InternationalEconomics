# Intertemporal trade and the current account in Lean

This is the `IntertemporalTrade/` proof project in
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Run the commands below from this directory: `cd IntertemporalTrade` from the
repository root. [Return to the library index](../README.md).

A checked formalisation of Obstfeld and Rogoff (1996), *Foundations of
International Macroeconomics*, Chapter 1, “Intertemporal Trade and the Current
Account Balance” (pp. 1–58), including the provable end-of-chapter exercises.
The library contains **272 theorems** and audits **381 declarations**,
including structure constructors and projections.

Several results the book argues only from a diagram are proved from primitives:
* **Gains from trade and the pattern of trade** (Figure 1.1, pp. 8–10): by revealed
  preference, using only that `u` is strictly increasing and strictly concave. A
  country lends when the world rate exceeds its autarky rate, and its welfare rises
  with the distance between the two.
* **The world rate lies strictly between the autarky rates** (Figure 1.5, p. 23),
  without the figure's assumption of upward-sloping saving curves. **An equilibrium
  exists**: optimal consumption is continuous in `r`, and the intermediate value
  theorem applies to world excess demand. The equilibrium is **Pareto optimal**.
* **The optimal tax on foreign borrowing** (Figure 1.11, pp. 42–45): the foreign offer
  curve is strictly concave, so the planner's optimum lies between autarky and
  laissez-faire. The tax lowers the world rate, `r^{A*} < r^τ < r^L`; Home gains,
  Foreign loses, and Foreign could bribe Home not to tax.
* **The pattern of labour trade** (p. 50), which the book calls straightforward: labour
  flows in when the autarky wage exceeds the world wage.

The main entry points are `Consumer.Household.isOptimal_iff_euler`,
`Consumer.Household.saving_nonneg_of_autarky_lt`,
`WorldEquilibrium.exists_equilibrium`, `WorldEquilibrium.rate_between_autarky`,
`WorldEquilibrium.first_welfare_theorem`, `Investment.fisher_separation`,
`OptimalTax.rate_ordering`, `LabourMobility.Technology.labour_imports_of_autarkyWage_gt`
and `Stability.marshall_lerner`, all in the namespace `ObstfeldRogoff.IntertemporalTrade`.

See the [source map](docs/source-map.md) for the correspondence with the book,
equation by equation. [Corrections](docs/corrections.md) records where a printed
claim is false or needs a changed statement: most notably, Exercise 8(b)'s
`ζ* > 1` does not follow without an extra hypothesis. It also lists the hypotheses
the book leaves implicit and what is not formalised.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Model](IntertemporalTrade/Model.lean) | 2 | Two-period endowment economy, budget line, `CA₁ + CA₂ = 0` |
| [Consumer](IntertemporalTrade/Consumer.lean) | 19 | Household, binding budget, uniqueness, Euler (1.3) necessary and sufficient, flat (1.5) and tilted consumption, existence under Inada, Ex 1 |
| [AutarkyGains](IntertemporalTrade/AutarkyGains.lean) | 19 | Autarky rate (1.7), gains from trade, saving-sign lemma and welfare monotonicity by revealed preference, comparative statics of `r^A` |
| [CurrentAccount](IntertemporalTrade/CurrentAccount.lean) | 12 | GNP/GDP, government (1.8), permanent vs temporary shocks, temporary government spending |
| [Investment](IntertemporalTrade/Investment.lean) | 34 | (1.11)–(1.18), Fisher separation, no crowding out, strictly concave PPF, autarky tangency, government spending under normality |
| [Isoelastic](IntertemporalTrade/Isoelastic.lean) | 29 | EIS (1.21), isoelastic class (1.22) and its converse, closed forms (1.25)–(1.26), (1.23)–(1.24), σ→1 and σ→0 limits, Ex 3, 4, 7 |
| [WorldEquilibrium](IntertemporalTrade/WorldEquilibrium.lean) | 24 | Walras's law, rate between autarky rates, existence, first welfare theorem, log closed forms (Ex 2, 5), Blanchard–Summers |
| [Duality](IntertemporalTrade/Duality.lean) | 36 | Expenditure function, Shephard (1.27), welfare effect (1.28), Slutsky (1.29)–(1.31), isoelastic closed forms |
| [OptimalTax](IntertemporalTrade/OptimalTax.lean) | 47 | Foreign offer curve (1.32), optimal tax ordering `r^{A*} < r^τ < r^L`, welfare effects, Pareto inefficiency, small country, fn 19, Ex 8 |
| [LabourMobility](IntertemporalTrade/LabourMobility.lean) | 44 | CRS (1.33)–(1.36), FOCs (1.37)–(1.38), factor-price frontier, GNP/GDP lines, pattern of labour trade |
| [Stability](IntertemporalTrade/Stability.lean) | 6 | Walrasian stability (1.39)–(1.40), Marshall–Lerner (1.41), stability of zero-CA equilibria |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
