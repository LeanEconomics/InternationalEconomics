# Corrections to the source

Places where a claim in Chapter 3 of Obstfeld and Rogoff (1996) is
false, imprecise, or relies on an unstated hypothesis. In each case the Lean
statement proves the corrected version and cites the original. Entries are
recorded when found, before the corresponding module is written, and are
revised if formalisation shows the finding itself to be wrong.

| Where | Book says | Finding |
| --- | --- | --- |
| Ex 2(b) (exercises pp. 195–197) | With n > r^A > r, opening to trade makes everyone worse off. | False as stated. With Cobb–Douglas and log utility, U(r) = −(1+β)α/(1−α)·log r + β log(1+r) → +∞ as r → 0⁺. Counterexample: α = 0.05, β = 0.9, n = 0.5 gives r^A = 1/6, and at r = 0.01, U(r) − U(r^A) ≈ +0.15. The claim holds only for r ∈ [r^A/(1+n−r^A), r^A). |
| §3.6.3 (§3.6 is pp. 167–174), Fig 3.6 | With public debt there is a stable steady state with lower capital. | A positive steady state exists only below a debt threshold, since Ψ(k, d̄) → −∞ as k → 0; the threshold is an explicit hypothesis. |
| (3.66), Weil model (§§3.7.3–3.7.6) | Aggregate consumption function in the Weil model. | Needs output and taxes identical across vintages; stated. |
| fn 52 | dc̄/dȳ > 0. | Also needs n > 0 and r > 0; at n = 0, c̄ = 0. |
| Weil model with growth, eq. (3.73) | A rise in g always lowers long-run b/y. | Stated without proof; proved here under n ≥ 0, β < 1 and stability. |
