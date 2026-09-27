# Corrections to the source

Places where a claim in Chapter 1 of Obstfeld and Rogoff (1996) is
false, imprecise, or relies on an unstated hypothesis. In each case the Lean
statement proves the corrected version and cites the original. Entries are
recorded when found, before the corresponding module is written, and are
revised if formalisation shows the finding itself to be wrong.

| Where | Book says | Finding |
| --- | --- | --- |
| Ex 5 (exercises pp. 54–58) | For the general model, a rise in Y₁ lowers r and a rise in Y₂ raises it. | True only under log utility (closed form, Ex 2) or with an explicit Walrasian stability hypothesis; the Lean statement carries one of the two. |
| Ex 8 (exercises pp. 54–58) | Refers to “section 1.5's model”. | Should be §1.4. The tax is additive in §1.4, `1 + r^τ + τ`, but ad valorem in Ex 8, `(1 + τ)(1 + r^τ)`; each is formalised in its own form. |
| §1.3.2, p. 29 | For a lender, dC₁/dr < 0 “only if r is not too far from r^A”. | Not a theorem as stated. Proved instead: dC₁/dr < 0 whenever C₁ ≥ Y₁, and in a neighbourhood of r^A. |
| Throughout | Inada conditions appear only in footnotes 1, 9, 23; r > −1, positive endowments and interiority are implicit. | Stated as explicit hypotheses wherever used. |
