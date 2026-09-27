# Imperfections in international capital markets in Lean

This is the `CapitalMarketImperfections/` proof project in
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Run the commands below from this directory: `cd CapitalMarketImperfections` from the repository
root. [Return to the library index](../README.md).

A checked formalisation of Obstfeld and Rogoff (1996), *Foundations of
International Macroeconomics*, Chapter 6, “Imperfections in International Capital Markets” (pp. 349–428).

**Status: scaffold.** The library currently contains **2 theorems**. See the
[source map](docs/source-map.md) and [corrections](docs/corrections.md).

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```
