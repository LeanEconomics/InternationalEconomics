# Real exchange rate and the terms of trade in Lean

This is the `RealExchangeRate/` proof project in
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Run the commands below from this directory: `cd RealExchangeRate` from the repository
root. [Return to the library index](../README.md).

A checked formalisation of Obstfeld and Rogoff (1996), *Foundations of
International Macroeconomics*, Chapter 4, “The Real Exchange Rate and the Terms of Trade” (pp. 199–268).

**Status: scaffold.** The library currently contains **2 theorems**. See the
[source map](docs/source-map.md) and [corrections](docs/corrections.md).

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```
