# Corrections to the source

Places where a claim in Chapter 2 of Obstfeld and Rogoff (1996) is
false, imprecise, or relies on an unstated hypothesis. In each case the Lean
statement proves the corrected version and cites the original. Entries are
recorded when found, before the corresponding module is written, and are
revised if formalisation shows the finding itself to be wrong.

| Where | Book says | Finding |
| --- | --- | --- |
| (2.65), p. 107; repeated p. 124 | Forward solution for q with subscripts s + 1 inside Σ_{s=t+1} (1+r)^{−(s−t)}. | Index typo: iterating (2.64) gives subscripts s. Eq. (2.70) uses the correct indexing. |
| Supplement A, p. 716 | Kuhn–Tucker conditions are necessary and sufficient for concave f and convex constraints. | Necessity needs a constraint qualification (counterexample: maximise z subject to z² ≤ 0). Harmless for the book's linear constraint; only that case is formalised. |
| fn 13, p. 78 | Σ_{s>t} R_{t,s} r_s = 1. | Needs R_{t,s} → 0, stated as a hypothesis. |
| Ex 3 (exercises pp. 124–127) | log C is a random walk with constant drift. | Needs constant conditional variance of log C. |
| Ex 5 (exercises pp. 124–127) | The Campbell test holds “if and only if”. | The converse needs a no-bubble condition, lim (1+r)^{−T} E_t CA_{t+T} = 0. |
| Supplement C.1.3 | Bubble solutions have the form b₀aᵗ. | In a stochastic setting they are all processes with E_t b_{t+1} = a b_t. |
| Supplement C (C15), (C18) | Eigenvector and steady-state formulas. | Need a₂₁ ≠ 0 and 1 − tr A + det A ≠ 0 respectively; stated. |
