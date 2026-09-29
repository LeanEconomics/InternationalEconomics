# Sticky-price models in Lean

This is the `StickyPriceModels/` proof project in
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Run the commands below from this directory: `cd StickyPriceModels` from the repository
root. [Return to the library index](../README.md).

A checked formalisation of Obstfeld and Rogoff (1996), *Foundations of
International Macroeconomics*, Chapter 10, “Sticky-Price Models of Output, the Exchange Rate, and the Current Account” (pp. 659–713).

**Status: scaffold.** The library currently contains **2 theorems**. See the
[source map](docs/source-map.md) and [corrections](docs/corrections.md).

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```
