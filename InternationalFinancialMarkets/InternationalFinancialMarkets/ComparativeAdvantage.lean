/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Algebra.Monoid

/-!
# A general result on comparative advantage

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.1.7,
pp. 280–282 (the theorem of Deardorff (1980) and Dixit and Norman (1980), their footnote 12).

A consumption bundle is `x = (C₁, C₂(·)) ∈ ℝ × (S → ℝ)`, valued at date-1 prices
`q(s)` of state-`s` claims: `x.1 + Σ q(s)x.2(s)`. World prices are `q(s) = p(s)/(1+r)`,
autarky prices `q^A(s) = p^A(s)/(1+r^A)`. The preference relation `pref x y` ("`x` is at least
as good as `y`") is arbitrary except for transitivity and local non-satiation; no expected
utility, concavity, completeness or continuity is assumed. We prove:
* Walras' law: an optimal free-trade bundle exhausts the budget, giving (18);
* the revealed-preference inequality (19): the free-trade bundle is worth at least the
  endowment at autarky prices;
* the comparative-advantage inequality `Σ [p^A(s)/(1+r^A) − p(s)/(1+r)]B₂(s) ≥ 0`;
* the one-state case `S = Unit`, which is Chapter 1's result (`r > r^A` ⇒ `CA₁ ≥ 0`).

The book's parenthetical argument for (19) ("if the preceding inequality failed, the country
would be able to buy its free-trade consumption bundle, and then some, at autarky prices,
contradicting the presence of gains from trade") is garbled: the contradiction is not with
gains from trade as such but with the optimality of the endowment at autarky prices. If (19)
failed, the free-trade bundle *plus a little more* (local non-satiation) would have been
affordable in autarky; the endowment, chosen in autarky, would then be revealed preferred to a
bundle strictly better than the free-trade bundle, which in turn is at least as good as the
endowment — contradicting transitivity. That is the proof formalised below.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.ComparativeAdvantage

open Finset

variable {S : Type} [Fintype S]

/-- The date-1 value of a bundle `x = (C₁, C₂)` at date-1 state-claim prices `q`,
`C₁ + Σ q(s)C₂(s)`, O&R (18)–(19), p. 281 (with `q(s) = p(s)/(1+r)` or `p^A(s)/(1+r^A)`). -/
def bundleValue (q : S → ℝ) (x : ℝ × (S → ℝ)) : ℝ := x.1 + ∑ s, q s * x.2 s

/-- Bundle values are continuous (in the sup metric on `ℝ × (S → ℝ)`), O&R §5.1.7. -/
theorem continuous_bundleValue (q : S → ℝ) : Continuous (bundleValue q) := by
  unfold bundleValue
  fun_prop

/-- Local non-satiation, O&R p. 282 ("more consumption is preferred to less", weakened): every
neighbourhood of every bundle `x` contains a bundle `y` with `¬ (x ⪰ y)`. (For complete
preferences `¬ (x ⪰ y)` means `y ≻ x`; for incomplete ones it is weaker than the usual
condition, so the results below are stronger.) -/
def LocallyNonsatiated (pref : ℝ × (S → ℝ) → ℝ × (S → ℝ) → Prop) : Prop :=
  ∀ x : ℝ × (S → ℝ), ∀ ε > 0, ∃ y, dist y x < ε ∧ ¬ pref x y

/-- Walras' law for the free-trade choice, O&R (18), p. 281: if `C` is affordable at world
prices `q` and at least as good as every affordable bundle, and preferences are locally
non-satiated, then `C` exhausts the budget: `value_q(C) = value_q(Y)`. -/
theorem walras_law {pref : ℝ × (S → ℝ) → ℝ × (S → ℝ) → Prop} (hlns : LocallyNonsatiated pref)
    (q : S → ℝ) (Y C : ℝ × (S → ℝ)) (hC : bundleValue q C ≤ bundleValue q Y)
    (hopt : ∀ z, bundleValue q z ≤ bundleValue q Y → pref C z) :
    bundleValue q C = bundleValue q Y := by
  by_contra hne
  have hlt : bundleValue q C < bundleValue q Y := lt_of_le_of_ne hC hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_lt (continuous_bundleValue q) continuous_const) C hlt
  obtain ⟨y, hy, hnot⟩ := hlns C ε hε
  have hyv : bundleValue q y < bundleValue q Y := hball (Metric.mem_ball.mpr hy)
  exact hnot (hopt y hyv.le)

/-- The revealed-preference inequality, O&R (19), p. 281: if the endowment `Y` was optimal at
autarky prices `q^A` (it is at least as good as every bundle worth no more than it at `q^A`),
the free-trade bundle `C` is at least as good as `Y` (gains from trade), and preferences are
transitive and locally non-satiated, then `value_{q^A}(C) ≥ value_{q^A}(Y)`, i.e.
`C₁ − Y₁ + Σ q^A(s)[C₂(s) − Y₂(s)] ≥ 0`. -/
theorem revealed_preference {pref : ℝ × (S → ℝ) → ℝ × (S → ℝ) → Prop}
    (htrans : ∀ x y z, pref x y → pref y z → pref x z) (hlns : LocallyNonsatiated pref)
    (qA : S → ℝ) (Y C : ℝ × (S → ℝ))
    (hautarky : ∀ z, bundleValue qA z ≤ bundleValue qA Y → pref Y z) (hCY : pref C Y) :
    bundleValue qA Y ≤ bundleValue qA C := by
  by_contra hlt
  push Not at hlt
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_lt (continuous_bundleValue qA) continuous_const) C hlt
  obtain ⟨y, hy, hnot⟩ := hlns C ε hε
  have hyv : bundleValue qA y < bundleValue qA Y := hball (Metric.mem_ball.mpr hy)
  exact hnot (htrans C Y y hCY (hautarky y hyv.le))

/-- The principle of comparative advantage, O&R §5.1.7, p. 281, for ANY transitive, locally
non-satiated preference relation and any number of states: suppose the endowment `Y` is
optimal at autarky prices `p^A(s)/(1+r^A)` and the free-trade bundle `C` is affordable and
optimal at world prices `p(s)/(1+r)`. Then, with net AD purchases `B₂(s) = C₂(s) − Y₂(s)`,
`Σ_s [p^A(s)/(1+r^A) − p(s)/(1+r)]B₂(s) ≥ 0`. -/
theorem comparative_advantage {pref : ℝ × (S → ℝ) → ℝ × (S → ℝ) → Prop}
    (htrans : ∀ x y z, pref x y → pref y z → pref x z) (hlns : LocallyNonsatiated pref)
    (p pA : S → ℝ) (r rA : ℝ) (Y C : ℝ × (S → ℝ))
    (hautarky : ∀ z, bundleValue (fun s => pA s / (1 + rA)) z ≤
      bundleValue (fun s => pA s / (1 + rA)) Y → pref Y z)
    (hC : bundleValue (fun s => p s / (1 + r)) C ≤ bundleValue (fun s => p s / (1 + r)) Y)
    (hopt : ∀ z, bundleValue (fun s => p s / (1 + r)) z ≤
      bundleValue (fun s => p s / (1 + r)) Y → pref C z) :
    0 ≤ ∑ s, (pA s / (1 + rA) - p s / (1 + r)) * (C.2 s - Y.2 s) := by
  have h18 := walras_law hlns _ Y C hC hopt
  have h19 := revealed_preference htrans hlns _ Y C hautarky (hopt Y le_rfl)
  simp only [bundleValue] at h18 h19
  have e : ∑ s, (pA s / (1 + rA) - p s / (1 + r)) * (C.2 s - Y.2 s) =
      (∑ s, pA s / (1 + rA) * C.2 s - ∑ s, pA s / (1 + rA) * Y.2 s) -
        (∑ s, p s / (1 + r) * C.2 s - ∑ s, p s / (1 + r) * Y.2 s) := by
    simp only [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e]
  linarith

/-- The one-state case is Chapter 1's comparative advantage, O&R p. 281: with a single (sure)
date-2 state, `1 + r > 0` and `1 + r^A > 0`, a country whose autarky interest rate is below
the world rate (`r^A < r`) runs a date-1 current-account surplus, `Y₁ − C₁ ≥ 0`, and one with
`r < r^A` runs a deficit, under the hypotheses of `comparative_advantage`. -/
theorem comparative_advantage_one_state {pref : ℝ × (Unit → ℝ) → ℝ × (Unit → ℝ) → Prop}
    (htrans : ∀ x y z, pref x y → pref y z → pref x z) (hlns : LocallyNonsatiated pref)
    {r rA : ℝ} (hr : 0 < 1 + r) (hrA : 0 < 1 + rA) (Y C : ℝ × (Unit → ℝ))
    (hautarky : ∀ z, bundleValue (fun _ => 1 / (1 + rA)) z ≤
      bundleValue (fun _ => 1 / (1 + rA)) Y → pref Y z)
    (hC : bundleValue (fun _ => 1 / (1 + r)) C ≤ bundleValue (fun _ => 1 / (1 + r)) Y)
    (hopt : ∀ z, bundleValue (fun _ => 1 / (1 + r)) z ≤
      bundleValue (fun _ => 1 / (1 + r)) Y → pref C z) :
    (rA < r → 0 ≤ Y.1 - C.1) ∧ (r < rA → Y.1 - C.1 ≤ 0) := by
  have hca := comparative_advantage htrans hlns (fun _ => 1) (fun _ => 1) r rA Y C hautarky hC
    hopt
  have h18 := walras_law hlns _ Y C hC hopt
  simp only [bundleValue, Finset.univ_unique, Finset.sum_singleton] at hca h18
  have hCA : Y.1 - C.1 = 1 / (1 + r) * (C.2 () - Y.2 ()) := by linarith
  rw [hCA]
  constructor
  · intro h
    have hq : 1 / (1 + r) < 1 / (1 + rA) := one_div_lt_one_div_of_lt hrA (by linarith)
    have hB : 0 ≤ C.2 () - Y.2 () := nonneg_of_mul_nonneg_right hca (by linarith)
    exact mul_nonneg (by positivity) hB
  · intro h
    have hq : 1 / (1 + rA) < 1 / (1 + r) := one_div_lt_one_div_of_lt hr (by linarith)
    have hB : C.2 () - Y.2 () ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hB

/-- Comparative advantage for utility-representable preferences, O&R p. 282 ("the result holds
for nonexpected- as well as expected-utility preferences"): for ANY utility function `U` on
bundles that is locally non-satiated (every neighbourhood of `x` contains `y` with
`U y > U x`), the inequality of `comparative_advantage` holds. -/
theorem comparative_advantage_utility (U : ℝ × (S → ℝ) → ℝ)
    (hlns : ∀ x : ℝ × (S → ℝ), ∀ ε > 0, ∃ y, dist y x < ε ∧ U x < U y)
    (p pA : S → ℝ) (r rA : ℝ) (Y C : ℝ × (S → ℝ))
    (hautarky : ∀ z, bundleValue (fun s => pA s / (1 + rA)) z ≤
      bundleValue (fun s => pA s / (1 + rA)) Y → U z ≤ U Y)
    (hC : bundleValue (fun s => p s / (1 + r)) C ≤ bundleValue (fun s => p s / (1 + r)) Y)
    (hopt : ∀ z, bundleValue (fun s => p s / (1 + r)) z ≤
      bundleValue (fun s => p s / (1 + r)) Y → U z ≤ U C) :
    0 ≤ ∑ s, (pA s / (1 + rA) - p s / (1 + r)) * (C.2 s - Y.2 s) :=
  comparative_advantage (pref := fun x y => U y ≤ U x) (fun _ _ _ h1 h2 => h2.trans h1)
    (fun x ε hε => (hlns x ε hε).imp fun _ h => ⟨h.1, not_le.mpr h.2⟩) p pA r rA Y C
    hautarky hC hopt

end ObstfeldRogoff.InternationalFinancialMarkets.ComparativeAdvantage
