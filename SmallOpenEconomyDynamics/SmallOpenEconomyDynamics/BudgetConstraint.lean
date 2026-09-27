/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SmallOpenEconomyDynamics.Model
import SmallOpenEconomyDynamics.PresentValue
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# The intertemporal budget constraint of a small open economy

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§2.1, pp. 60–68, and Chapter 2 Exercise 1, pp. 124–125.

The date `t` of the book is normalised to `0`; `shiftPaths` restarts any path at a
later date and preserves the period constraints, so every result applies at any `t`.

* The finite-horizon constraint O&R (2.4), p. 61, is equivalent to the period
  constraints (2.2) (`flow_iff_finite_ibc`).
* Given the period constraints and summable present values, the transversality
  condition (2.13) is equivalent to the intertemporal budget constraint (2.14), p. 64
  (`transversality_iff_ibc`); the no-Ponzi-game condition is equivalent to the weak
  inequality (footnote 4, p. 65; `noPonzi_iff_ibc_le`).
* Nonnegative consumption bounds foreign debt by the value of future net output, p. 65
  (`debt_limit`), and solvency is a statement about trade surpluses, p. 66
  (`ibc_iff_trade_surplus`).
* A steady debt–output ratio, p. 68 (`steady_ratio_burden`).
* The naive limit condition fails, (2.12), p. 64 (`naive_path`, `naive_limit_zero_iff`).
* Exercise 1 on current-account sustainability. Part (b) holds only for
  `ξ r < 2 (1 + r)`, not for every `ξ > 0` (`ex1_not_summable`).
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint

open Filter Topology Finset PresentValue

/-- The trade balance `TB_s ≡ Y_s − C_s − I_s − G_s`, O&R p. 66. -/
def tradeBalance (p : Paths) (s : ℕ) : ℝ := p.Y s - p.C s - p.I s - p.G s

/-- The paths restarted at date `t`: the book's general date `t`, O&R §2.1, p. 60. -/
def shiftPaths (p : Paths) (t : ℕ) : Paths :=
  ⟨fun s => p.B (t + s), fun s => p.Y (t + s), fun s => p.C (t + s),
    fun s => p.G (t + s), fun s => p.I (t + s)⟩

/-- The deviation from the period constraint O&R (2.2) at date `s`. -/
def residual (e : Economy) (p : Paths) (s : ℕ) : ℝ :=
  p.B (s + 1) - (1 + e.r) * p.B s - tradeBalance p s

/-- The period constraints O&R (2.2), p. 60, as the recursion
`B_{s+1} = (1 + r) B_s + TB_s`. -/
theorem flow_iff_recursion (e : Economy) (p : Paths) :
    e.Flow p ↔ ∀ s, p.B (s + 1) = (1 + e.r) * p.B s + tradeBalance p s := by
  unfold Economy.Flow Economy.ca tradeBalance
  constructor <;> intro h s <;> linarith [h s]

/-- The period constraints O&R (2.2) hold at every date after `t` when they hold
from date `0`: the book's date `t` may be normalised to `0`. -/
theorem flow_shiftPaths (e : Economy) (p : Paths) (h : e.Flow p) (t : ℕ) :
    e.Flow (shiftPaths p t) := by
  intro s
  have := h (t + s)
  unfold Economy.ca at this ⊢
  simpa only [shiftPaths, add_assoc] using this

/-- Accounting identity behind O&R (2.4), p. 61, with no hypotheses: the finite-horizon
constraint holds up to the discounted sum of the period residuals. -/
theorem finite_identity (e : Economy) (p : Paths) (T : ℕ) :
    ∑ s ∈ range (T + 1), disc e.r ^ s * (p.C s + p.I s) + disc e.r ^ T * p.B (T + 1)
      = (1 + e.r) * p.B 0 + ∑ s ∈ range (T + 1), disc e.r ^ s * (p.Y s - p.G s)
        + ∑ s ∈ range (T + 1), disc e.r ^ s * residual e p s := by
  have hd := one_add_mul_disc (show 0 < 1 + e.r by linarith [e.r_pos])
  induction T with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, pow_zero, one_mul, residual,
      tradeBalance]
    ring
  | succ T ih =>
    rw [sum_range_succ, sum_range_succ (fun s => disc e.r ^ s * (p.Y s - p.G s)),
      sum_range_succ (fun s => disc e.r ^ s * residual e p s)]
    simp only [residual, tradeBalance] at ih ⊢
    rw [pow_succ]
    linear_combination ih + disc e.r ^ T * p.B (T + 1) * hd

/-- **Finite-horizon budget constraint**, O&R (2.4), p. 61: the period constraints imply
`Σ_{s≤T} (1+r)^{-s}(C_s + I_s) + (1+r)^{-T} B_{T+1} = (1+r) B_0 + Σ_{s≤T} (1+r)^{-s}(Y_s − G_s)`. -/
theorem finite_ibc (e : Economy) (p : Paths) (h : e.Flow p) (T : ℕ) :
    ∑ s ∈ range (T + 1), disc e.r ^ s * (p.C s + p.I s) + disc e.r ^ T * p.B (T + 1)
      = (1 + e.r) * p.B 0 + ∑ s ∈ range (T + 1), disc e.r ^ s * (p.Y s - p.G s) := by
  have hr := (flow_iff_recursion e p).1 h
  have h0 : ∀ s, residual e p s = 0 := fun s => by unfold residual; linarith [hr s]
  simpa [h0] using finite_identity e p T

/-- **O&R (2.4) ⇔ (2.2)**, p. 61: the finite-horizon constraints for every horizon `T`
hold iff every period constraint holds. -/
theorem flow_iff_finite_ibc (e : Economy) (p : Paths) :
    e.Flow p ↔ ∀ T, ∑ s ∈ range (T + 1), disc e.r ^ s * (p.C s + p.I s)
      + disc e.r ^ T * p.B (T + 1)
      = (1 + e.r) * p.B 0 + ∑ s ∈ range (T + 1), disc e.r ^ s * (p.Y s - p.G s) := by
  refine ⟨finite_ibc e p, fun h => ?_⟩
  have hS : ∀ T, ∑ s ∈ range (T + 1), disc e.r ^ s * residual e p s = 0 := fun T => by
    linarith [finite_identity e p T, h T]
  have hd : disc e.r ≠ 0 := (disc_pos (show 0 < 1 + e.r by linarith [e.r_pos])).ne'
  have h0 : ∀ s, residual e p s = 0 := by
    intro s
    cases s with
    | zero => simpa using hS 0
    | succ n =>
      have := hS (n + 1)
      rw [sum_range_succ, hS n, zero_add] at this
      exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hd)
  refine (flow_iff_recursion e p).2 fun s => ?_
  have := h0 s
  unfold residual at this
  linarith

/-- The discounted terminal stock `(1+r)^{-T} B_{T+1}` of O&R (2.4) converges to
`(1+r) B_0 + PV(Y − G) − PV(C + I)`, given the period constraints and summability. -/
theorem tendsto_terminal (e : Economy) (p : Paths) (h : e.Flow p)
    (hCI : Summable fun s => disc e.r ^ s * (p.C s + p.I s))
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s)) :
    Tendsto (fun T => disc e.r ^ T * p.B (T + 1)) atTop
      (𝓝 ((1 + e.r) * p.B 0 + pv e.r (fun s => p.Y s - p.G s)
        - pv e.r (fun s => p.C s + p.I s))) := by
  unfold pv
  have h1 := hYG.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h2 := hCI.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h3 := ((tendsto_const_nhds (x := (1 + e.r) * p.B 0)).add h1).sub h2
  refine h3.congr fun T => ?_
  simp only [Function.comp]
  linarith [finite_ibc e p h T]

/-- **Transversality ⇔ intertemporal budget constraint**, O&R (2.13) ⇔ (2.14), p. 64:
under the period constraints and summable present values,
`lim (1+r)^{-T} B_{T+1} = 0` iff `PV(C + I) = (1+r) B_0 + PV(Y − G)`. -/
theorem transversality_iff_ibc (e : Economy) (p : Paths) (h : e.Flow p)
    (hCI : Summable fun s => disc e.r ^ s * (p.C s + p.I s))
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s)) :
    Tendsto (fun T => disc e.r ^ T * p.B (T + 1)) atTop (𝓝 0) ↔
      pv e.r (fun s => p.C s + p.I s)
        = (1 + e.r) * p.B 0 + pv e.r (fun s => p.Y s - p.G s) := by
  have ht := tendsto_terminal e p h hCI hYG
  constructor
  · intro h0
    have := tendsto_nhds_unique ht h0
    linarith
  · intro hi
    rwa [show (1 + e.r) * p.B 0 + pv e.r (fun s => p.Y s - p.G s)
      - pv e.r (fun s => p.C s + p.I s) = 0 by linarith] at ht

/-- **No-Ponzi-game condition**, O&R footnote 4, p. 65: `lim (1+r)^{-T} B_{T+1} ≥ 0` iff
`PV(C + I) ≤ (1+r) B_0 + PV(Y − G)`. -/
theorem noPonzi_iff_ibc_le (e : Economy) (p : Paths) (h : e.Flow p)
    (hCI : Summable fun s => disc e.r ^ s * (p.C s + p.I s))
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s)) :
    (∃ L, 0 ≤ L ∧ Tendsto (fun T => disc e.r ^ T * p.B (T + 1)) atTop (𝓝 L)) ↔
      pv e.r (fun s => p.C s + p.I s)
        ≤ (1 + e.r) * p.B 0 + pv e.r (fun s => p.Y s - p.G s) := by
  have ht := tendsto_terminal e p h hCI hYG
  constructor
  · rintro ⟨L, hL, hL'⟩
    have := tendsto_nhds_unique ht hL'
    linarith
  · intro hi
    exact ⟨_, by linarith, ht⟩

/-- **Unrequited gift**, O&R p. 65: `lim (1+r)^{-T} B_{T+1} > 0` iff the present value of
absorption falls strictly short of wealth, `PV(C + I) < (1+r) B_0 + PV(Y − G)`. -/
theorem terminal_pos_iff_ibc_lt (e : Economy) (p : Paths) (h : e.Flow p)
    (hCI : Summable fun s => disc e.r ^ s * (p.C s + p.I s))
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s)) :
    (∃ L, 0 < L ∧ Tendsto (fun T => disc e.r ^ T * p.B (T + 1)) atTop (𝓝 L)) ↔
      pv e.r (fun s => p.C s + p.I s)
        < (1 + e.r) * p.B 0 + pv e.r (fun s => p.Y s - p.G s) := by
  have ht := tendsto_terminal e p h hCI hYG
  constructor
  · rintro ⟨L, hL, hL'⟩
    have := tendsto_nhds_unique ht hL'
    linarith
  · intro hi
    exact ⟨_, by linarith, ht⟩

/-- **Debt limit**, O&R p. 65: if consumption is nonnegative and the (no-Ponzi) budget
constraint holds, then `−(1+r) B_0 ≤ Σ (1+r)^{-s}(Y_s − G_s − I_s)`. -/
theorem debt_limit (e : Economy) (p : Paths) (hC : ∀ s, 0 ≤ p.C s)
    (hCs : Summable fun s => disc e.r ^ s * p.C s)
    (hIs : Summable fun s => disc e.r ^ s * p.I s)
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s))
    (hibc : pv e.r (fun s => p.C s + p.I s)
      ≤ (1 + e.r) * p.B 0 + pv e.r (fun s => p.Y s - p.G s)) :
    -((1 + e.r) * p.B 0) ≤ pv e.r (fun s => p.Y s - p.G s - p.I s) := by
  rw [pv_sub hYG hIs]
  rw [pv_add hCs hIs] at hibc
  have hd := disc_pos (show 0 < 1 + e.r by linarith [e.r_pos])
  have : 0 ≤ pv e.r p.C := tsum_nonneg fun s => mul_nonneg (pow_nonneg hd.le _) (hC s)
  linarith

/-- **Debt limit, book form**, O&R p. 65: for a debtor (`B_0 ≤ 0`), foreign debt `−B_0` is
bounded by the market value of future net output `Σ (1+r)^{-s}(Y_s − G_s − I_s)`. -/
theorem debt_limit_debtor (e : Economy) (p : Paths) (hB : p.B 0 ≤ 0) (hC : ∀ s, 0 ≤ p.C s)
    (hCs : Summable fun s => disc e.r ^ s * p.C s)
    (hIs : Summable fun s => disc e.r ^ s * p.I s)
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s))
    (hibc : pv e.r (fun s => p.C s + p.I s)
      ≤ (1 + e.r) * p.B 0 + pv e.r (fun s => p.Y s - p.G s)) :
    -p.B 0 ≤ pv e.r (fun s => p.Y s - p.G s - p.I s) := by
  have := debt_limit e p hC hCs hIs hYG hibc
  nlinarith [e.r_pos]

/-- The present value of the trade balance is `PV(Y − G) − PV(C + I)`, O&R p. 66. -/
theorem pv_tradeBalance (e : Economy) (p : Paths)
    (hCI : Summable fun s => disc e.r ^ s * (p.C s + p.I s))
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s)) :
    pv e.r (tradeBalance p)
      = pv e.r (fun s => p.Y s - p.G s) - pv e.r (fun s => p.C s + p.I s) := by
  have : tradeBalance p = fun s => (p.Y s - p.G s) - (p.C s + p.I s) := by
    funext s
    unfold tradeBalance
    ring
  rw [this, pv_sub hYG hCI]

/-- **Solvency as trade surpluses**, O&R p. 66: the intertemporal budget constraint (2.14)
holds iff `−(1+r) B_0 = Σ (1+r)^{-s} TB_s`. -/
theorem ibc_iff_trade_surplus (e : Economy) (p : Paths)
    (hCI : Summable fun s => disc e.r ^ s * (p.C s + p.I s))
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s)) :
    pv e.r (fun s => p.C s + p.I s)
        = (1 + e.r) * p.B 0 + pv e.r (fun s => p.Y s - p.G s) ↔
      -((1 + e.r) * p.B 0) = pv e.r (tradeBalance p) := by
  rw [pv_tradeBalance e p hCI hYG]
  constructor <;> intro h <;> linarith

/-- O&R (2.13) ⇔ p. 66: under the period constraints, transversality holds iff the present
value of trade surpluses repays the initial debt with interest. -/
theorem transversality_iff_trade_surplus (e : Economy) (p : Paths) (h : e.Flow p)
    (hCI : Summable fun s => disc e.r ^ s * (p.C s + p.I s))
    (hYG : Summable fun s => disc e.r ^ s * (p.Y s - p.G s)) :
    Tendsto (fun T => disc e.r ^ T * p.B (T + 1)) atTop (𝓝 0) ↔
      -((1 + e.r) * p.B 0) = pv e.r (tradeBalance p) :=
  (transversality_iff_ibc e p h hCI hYG).trans (ibc_iff_trade_surplus e p hCI hYG)

/-- **Steady debt–output ratio**, O&R p. 68: if `B_{s+1} = (1+g) B_s`, the period constraints
force `TB_s = −(r − g) B_s`. -/
theorem steady_ratio_trade_balance (e : Economy) (p : Paths) {g : ℝ} (h : e.Flow p)
    (hB : ∀ s, p.B (s + 1) = (1 + g) * p.B s) (s : ℕ) :
    tradeBalance p s = -(e.r - g) * p.B s := by
  linarith [(flow_iff_recursion e p).1 h s, hB s]

/-- O&R p. 68: with `Y_{s+1} = (1+g) Y_s` and `−1 < g < r`, `Y_s/(r − g)` is the market
value of a claim to all output from date `s` on, `Σ_{v≥0} (1+r)^{-(v+1)} Y_{s+v}`. -/
theorem output_claim_value (e : Economy) (p : Paths) {g : ℝ} (hg : -1 < g) (hgr : g < e.r)
    (hY : ∀ s, p.Y (s + 1) = (1 + g) * p.Y s) (s : ℕ) :
    ∑' v, disc e.r ^ (v + 1) * p.Y (s + v) = p.Y s / (e.r - g) := by
  have hYv : ∀ v, p.Y (s + v) = (1 + g) ^ v * p.Y s := by
    intro v
    induction v with
    | zero => simp
    | succ v ih => rw [← add_assoc, hY, ih, pow_succ]; ring
  have hf : (fun v => disc e.r ^ (v + 1) * p.Y (s + v))
      = fun v => disc e.r * (disc e.r ^ v * ((1 + g) ^ v * p.Y s)) := by
    funext v
    rw [hYv, pow_succ]
    ring
  have hp := pv_geometric hg hgr (p.Y s)
  unfold pv at hp
  rw [hf, tsum_mul_left, hp]
  have h1 : (1 + e.r) ≠ 0 := by linarith [e.r_pos]
  have h2 : e.r - g ≠ 0 := by linarith
  unfold disc
  field_simp

/-- **Debt burden**, O&R p. 68: along a steady debt–output path, the trade surplus needed as a
share of output is the ratio of debt to the market value of future output,
`TB_s/Y_s = −B_s / [Y_s/(r − g)]`. -/
theorem steady_ratio_burden (e : Economy) (p : Paths) {g : ℝ} (hg : -1 < g) (hgr : g < e.r)
    (h : e.Flow p) (hB : ∀ s, p.B (s + 1) = (1 + g) * p.B s)
    (hY : ∀ s, p.Y (s + 1) = (1 + g) * p.Y s) (s : ℕ) (hYs : p.Y s ≠ 0) :
    tradeBalance p s / p.Y s = -(e.r - g) * p.B s / p.Y s ∧
      tradeBalance p s / p.Y s = -p.B s / ∑' v, disc e.r ^ (v + 1) * p.Y (s + v) := by
  rw [output_claim_value e p hg hgr hY s, steady_ratio_trade_balance e p h hB s]
  refine ⟨rfl, ?_⟩
  have h2 : e.r - g ≠ 0 := by linarith
  field_simp

/-- O&R p. 68: a constant debt–output ratio with growth `−1 < g < r` satisfies the
transversality condition (2.13). -/
theorem steady_ratio_transversality (e : Economy) (p : Paths) {g : ℝ} (hg : -1 < g)
    (hgr : g < e.r) (hB : ∀ s, p.B (s + 1) = (1 + g) * p.B s) :
    Tendsto (fun T => disc e.r ^ T * p.B (T + 1)) atTop (𝓝 0) := by
  have hBn : ∀ n, p.B n = (1 + g) ^ n * p.B 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hB, ih, pow_succ]; ring
  have h1 : 0 < 1 + e.r := by linarith [e.r_pos]
  have hq0 : 0 ≤ (1 + g) * disc e.r := mul_nonneg (by linarith) (disc_pos h1).le
  have hq1 : (1 + g) * disc e.r < 1 := by
    unfold disc
    rw [← div_eq_mul_inv, div_lt_one h1]
    linarith
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const ((1 + g) * p.B 0)
  rw [zero_mul] at this
  refine this.congr fun T => ?_
  rw [hBn (T + 1), mul_pow, pow_succ]
  ring

/-- **The naive path**, O&R (2.12), p. 64: with constant output `Ȳ`, constant consumption
`C̄` and `G = I = 0`, `B_n = B_0 + (r B_0 + Ȳ − C̄)((1+r)^n − 1)/r` (the book's
`B_{t+T+1}` is `n = T + 1`). -/
theorem naive_path (e : Economy) (p : Paths) {Ybar Cbar : ℝ} (h : e.Flow p)
    (hY : ∀ s, p.Y s = Ybar) (hC : ∀ s, p.C s = Cbar) (hG : ∀ s, p.G s = 0)
    (hI : ∀ s, p.I s = 0) (n : ℕ) :
    p.B n = p.B 0 + (e.r * p.B 0 + Ybar - Cbar) * ((1 + e.r) ^ n - 1) / e.r := by
  have hr := e.r_pos.ne'
  induction n with
  | zero => simp
  | succ n ih =>
    rw [(flow_iff_recursion e p).1 h n, ih]
    simp only [tradeBalance, hY, hC, hG, hI]
    field_simp
    ring

/-- O&R p. 64: if `C̄ < r B_0 + Ȳ`, net foreign assets diverge to `+∞`. -/
theorem naive_tendsto_atTop (e : Economy) (p : Paths) {Ybar Cbar : ℝ} (h : e.Flow p)
    (hY : ∀ s, p.Y s = Ybar) (hC : ∀ s, p.C s = Cbar) (hG : ∀ s, p.G s = 0)
    (hI : ∀ s, p.I s = 0) (hlt : Cbar < e.r * p.B 0 + Ybar) :
    Tendsto p.B atTop atTop := by
  have hk : 0 < (e.r * p.B 0 + Ybar - Cbar) / e.r := div_pos (by linarith) e.r_pos
  have hp := tendsto_pow_atTop_atTop_of_one_lt (show 1 < 1 + e.r by linarith [e.r_pos])
  have := tendsto_atTop_add_const_left _ (p.B 0 - (e.r * p.B 0 + Ybar - Cbar) / e.r)
    (hp.const_mul_atTop hk)
  refine this.congr fun n => ?_
  rw [naive_path e p h hY hC hG hI n]
  ring

/-- O&R p. 64: if `C̄ > r B_0 + Ȳ`, net foreign assets diverge to `−∞`. -/
theorem naive_tendsto_atBot (e : Economy) (p : Paths) {Ybar Cbar : ℝ} (h : e.Flow p)
    (hY : ∀ s, p.Y s = Ybar) (hC : ∀ s, p.C s = Cbar) (hG : ∀ s, p.G s = 0)
    (hI : ∀ s, p.I s = 0) (hgt : e.r * p.B 0 + Ybar < Cbar) :
    Tendsto p.B atTop atBot := by
  have hk : (e.r * p.B 0 + Ybar - Cbar) / e.r < 0 := div_neg_of_neg_of_pos (by linarith) e.r_pos
  have hp := tendsto_pow_atTop_atTop_of_one_lt (show 1 < 1 + e.r by linarith [e.r_pos])
  have := tendsto_atBot_add_const_left _ (p.B 0 - (e.r * p.B 0 + Ybar - Cbar) / e.r)
    (hp.const_mul_atTop_of_neg hk)
  refine this.congr fun n => ?_
  rw [naive_path e p h hY hC hG hI n]
  ring

/-- **Failure of the naive limit**, O&R p. 64: for a constant plan, `lim B_n = 0` holds only
in the accidental case `C̄ = Ȳ` and `B_0 = 0`. -/
theorem naive_limit_zero_iff (e : Economy) (p : Paths) {Ybar Cbar : ℝ} (h : e.Flow p)
    (hY : ∀ s, p.Y s = Ybar) (hC : ∀ s, p.C s = Cbar) (hG : ∀ s, p.G s = 0)
    (hI : ∀ s, p.I s = 0) :
    Tendsto p.B atTop (𝓝 0) ↔ Cbar = Ybar ∧ p.B 0 = 0 := by
  constructor
  · intro ht
    rcases lt_trichotomy Cbar (e.r * p.B 0 + Ybar) with hlt | heq | hgt
    · exact absurd ht (not_tendsto_nhds_of_tendsto_atTop
        (naive_tendsto_atTop e p h hY hC hG hI hlt) 0)
    · have hc : ∀ n, p.B n = p.B 0 := fun n => by
        rw [naive_path e p h hY hC hG hI n, heq]; ring
      have h0 : Tendsto p.B atTop (𝓝 (p.B 0)) :=
        tendsto_const_nhds.congr fun n => (hc n).symm
      have hB0 := tendsto_nhds_unique h0 ht
      refine ⟨?_, hB0⟩
      rw [heq, hB0]
      ring
    · exact absurd ht (not_tendsto_nhds_of_tendsto_atBot
        (naive_tendsto_atBot e p h hY hC hG hI hgt) 0)
  · rintro ⟨hCY, hB0⟩
    have hc : ∀ n, p.B n = 0 := fun n => by
      rw [naive_path e p h hY hC hG hI n, hCY, hB0]; ring
    exact tendsto_const_nhds.congr fun n => (hc n).symm

/-- **Transversality for the constant plan**, O&R (2.13), p. 64: with constant `Ȳ`, `C̄` and
`G = I = 0`, the transversality condition holds iff `C̄ = r B_0 + Ȳ`, the only constant plan
meeting the intertemporal budget constraint (2.14). -/
theorem naive_transversality_iff (e : Economy) (p : Paths) {Ybar Cbar : ℝ} (h : e.Flow p)
    (hY : ∀ s, p.Y s = Ybar) (hC : ∀ s, p.C s = Cbar) (hG : ∀ s, p.G s = 0)
    (hI : ∀ s, p.I s = 0) :
    Tendsto (fun T => disc e.r ^ T * p.B (T + 1)) atTop (𝓝 0) ↔
      Cbar = e.r * p.B 0 + Ybar := by
  have hCI : (fun s => p.C s + p.I s) = fun _ => Cbar := by
    funext s; simp [hC, hI]
  have hYG : (fun s => p.Y s - p.G s) = fun _ => Ybar := by
    funext s; simp [hY, hG]
  have hs := (hasSum_disc_pow e.r_pos).summable
  have hsC : Summable fun s => disc e.r ^ s * (p.C s + p.I s) := by
    simpa only [hC, hI, add_zero] using hs.mul_right Cbar
  have hsY : Summable fun s => disc e.r ^ s * (p.Y s - p.G s) := by
    simpa only [hY, hG, sub_zero] using hs.mul_right Ybar
  rw [transversality_iff_ibc e p h hsC hsY, hCI, hYG, pv_const e.r_pos, pv_const e.r_pos]
  have hr := e.r_pos.ne'
  have h1 : (1 + e.r) / e.r ≠ 0 := div_ne_zero (by linarith [e.r_pos]) hr
  have key : (1 + e.r) / e.r * Cbar - ((1 + e.r) * p.B 0 + (1 + e.r) / e.r * Ybar)
      = (1 + e.r) / e.r * (Cbar - (e.r * p.B 0 + Ybar)) := by
    field_simp
  constructor
  · intro hi
    rw [hi, sub_self] at key
    exact sub_eq_zero.1 ((mul_eq_zero.1 key.symm).resolve_left h1)
  · intro hi
    subst hi
    field_simp

/-- **Exercise 1(a)**, O&R p. 124: under the rule `TB_s = −ξ r B_s`, the period constraints
give `B_{s+1} = [1 + (1 − ξ) r] B_s`. -/
theorem ex1_recursion (e : Economy) (p : Paths) {ξ : ℝ} (h : e.Flow p)
    (hTB : ∀ s, tradeBalance p s = -ξ * e.r * p.B s) (s : ℕ) :
    p.B (s + 1) = (1 + (1 - ξ) * e.r) * p.B s := by
  linear_combination (flow_iff_recursion e p).1 h s + hTB s

/-- Exercise 1(a), O&R p. 124, solved: `B_s = [1 + (1 − ξ) r]^s B_0`. -/
theorem ex1_path (e : Economy) (p : Paths) {ξ : ℝ} (h : e.Flow p)
    (hTB : ∀ s, tradeBalance p s = -ξ * e.r * p.B s) (s : ℕ) :
    p.B s = (1 + (1 - ξ) * e.r) ^ s * p.B 0 := by
  induction s with
  | zero => simp
  | succ n ih => rw [ex1_recursion e p h hTB n, ih, pow_succ]; ring

/-- Exercise 1(b), O&R p. 124: the discounted trade balance is geometric,
`(1+r)^{-s} TB_s = q^s (−ξ r B_0)` with `q = [1 + (1 − ξ) r]/(1 + r)`. -/
theorem ex1_discounted_tb (e : Economy) (p : Paths) {ξ : ℝ} (h : e.Flow p)
    (hTB : ∀ s, tradeBalance p s = -ξ * e.r * p.B s) (s : ℕ) :
    disc e.r ^ s * tradeBalance p s
      = ((1 + (1 - ξ) * e.r) * disc e.r) ^ s * (-ξ * e.r * p.B 0) := by
  rw [hTB, ex1_path e p h hTB, mul_pow]
  ring

/-- **Exercise 1(b)**, O&R p. 124: for `0 < ξ` and `ξ r < 2(1 + r)` (i.e. `ξ < 2 + 2/r`) the
discounted trade balances are summable and `Σ (1+r)^{-s} TB_s = −(1+r) B_0`: the
intertemporal budget constraint holds. -/
theorem ex1_ibc (e : Economy) (p : Paths) {ξ : ℝ} (h : e.Flow p)
    (hTB : ∀ s, tradeBalance p s = -ξ * e.r * p.B s) (hξ : 0 < ξ)
    (hξ2 : ξ * e.r < 2 * (1 + e.r)) :
    Summable (fun s => disc e.r ^ s * tradeBalance p s) ∧
      pv e.r (tradeBalance p) = -((1 + e.r) * p.B 0) := by
  have h1 : 0 < 1 + e.r := by linarith [e.r_pos]
  have hq : |(1 + (1 - ξ) * e.r) * disc e.r| < 1 := by
    unfold disc
    rw [← div_eq_mul_inv, abs_lt, lt_div_iff₀ h1, div_lt_one h1]
    constructor <;> nlinarith [e.r_pos]
  have hf : (fun s => disc e.r ^ s * tradeBalance p s)
      = fun s => ((1 + (1 - ξ) * e.r) * disc e.r) ^ s * (-ξ * e.r * p.B 0) := by
    funext s
    exact ex1_discounted_tb e p h hTB s
  refine ⟨hf ▸ (summable_geometric_of_abs_lt_one hq).mul_right _, ?_⟩
  unfold pv
  rw [hf, tsum_mul_right, tsum_geometric_of_abs_lt_one hq]
  have hne : 1 - (1 + (1 - ξ) * e.r) * disc e.r = ξ * e.r * disc e.r := by
    have := one_add_mul_disc h1
    linear_combination -this
  rw [hne]
  have hd := (disc_pos h1).ne'
  have hr := e.r_pos.ne'
  have := one_add_mul_disc h1
  field_simp
  linear_combination p.B 0 * this

/-- Exercise 1(b), O&R p. 124: for `0 < ξ` and `ξ r < 2(1 + r)` the transversality condition
(2.13) holds along the rule's path. -/
theorem ex1_transversality (e : Economy) (p : Paths) {ξ : ℝ} (h : e.Flow p)
    (hTB : ∀ s, tradeBalance p s = -ξ * e.r * p.B s) (hξ : 0 < ξ)
    (hξ2 : ξ * e.r < 2 * (1 + e.r)) :
    Tendsto (fun T => disc e.r ^ T * p.B (T + 1)) atTop (𝓝 0) := by
  have h1 : 0 < 1 + e.r := by linarith [e.r_pos]
  have hq : |(1 + (1 - ξ) * e.r) * disc e.r| < 1 := by
    unfold disc
    rw [← div_eq_mul_inv, abs_lt, lt_div_iff₀ h1, div_lt_one h1]
    constructor <;> nlinarith [e.r_pos]
  have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq).mul_const
    ((1 + (1 - ξ) * e.r) * p.B 0)
  rw [zero_mul] at this
  refine this.congr fun T => ?_
  rw [ex1_path e p h hTB (T + 1), mul_pow, pow_succ]
  ring

/-- **Correction to Exercise 1(b)**, O&R p. 124: the claim "for any `ξ > 0`" fails for large
`ξ`. If `ξ r ≥ 2(1 + r)` and `B_0 ≠ 0`, the ratio `[1 + (1 − ξ) r]/(1 + r) ≤ −1` and the
discounted trade balances are not summable, so the present value in (2.14) does not exist. -/
theorem ex1_not_summable (e : Economy) (p : Paths) {ξ : ℝ} (h : e.Flow p)
    (hTB : ∀ s, tradeBalance p s = -ξ * e.r * p.B s) (hξ2 : 2 * (1 + e.r) ≤ ξ * e.r)
    (hB0 : p.B 0 ≠ 0) :
    ¬ Summable (fun s => disc e.r ^ s * tradeBalance p s) := by
  intro hs
  have h1 : 0 < 1 + e.r := by linarith [e.r_pos]
  have hq : 1 ≤ |(1 + (1 - ξ) * e.r) * disc e.r| := by
    have : (1 + (1 - ξ) * e.r) * disc e.r ≤ -1 := by
      unfold disc
      rw [← div_eq_mul_inv, div_le_iff₀ h1]
      linarith
    rw [abs_of_neg (by linarith)]
    linarith
  have hξ : 0 < ξ := by
    by_contra hn
    push Not at hn
    nlinarith [e.r_pos]
  have hc : 0 < |ξ * e.r * p.B 0| := abs_pos.2 (mul_ne_zero (mul_pos hξ e.r_pos).ne' hB0)
  have hbig : ∀ s, |ξ * e.r * p.B 0| ≤ |disc e.r ^ s * tradeBalance p s| := by
    intro s
    rw [ex1_discounted_tb e p h hTB, abs_mul (_ ^ s), abs_pow, neg_mul, neg_mul, abs_neg]
    exact le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hq)
  have ht := hs.tendsto_atTop_zero.abs
  rw [abs_zero] at ht
  obtain ⟨s, hs'⟩ := (ht.eventually (gt_mem_nhds hc)).exists
  exact absurd (hbig s) (not_le.2 hs')

/-- **Exercise 1(c)**, O&R p. 125: with `G = I = 0` and constant output `Ȳ`, the rule means
consumption `C_s = Ȳ + ξ r B_s`. -/
theorem ex1_consumption (p : Paths) {ξ r Ybar : ℝ} (hY : ∀ s, p.Y s = Ybar)
    (hG : ∀ s, p.G s = 0) (hI : ∀ s, p.I s = 0)
    (hTB : ∀ s, tradeBalance p s = -ξ * r * p.B s) (s : ℕ) :
    p.C s = Ybar + ξ * r * p.B s := by
  have := hTB s
  unfold tradeBalance at this
  rw [hY, hG, hI] at this
  linarith

/-- **Exercise 1(c)**, O&R p. 125: for a debtor (`B_0 < 0`) with `0 < ξ < 1`, debt grows
without bound, `B_s → −∞`, although the budget constraint holds (`ex1_ibc`). -/
theorem ex1_debt_unbounded (e : Economy) (p : Paths) {ξ : ℝ} (h : e.Flow p)
    (hTB : ∀ s, tradeBalance p s = -ξ * e.r * p.B s) (hξ1 : ξ < 1) (hB0 : p.B 0 < 0) :
    Tendsto p.B atTop atBot := by
  have hq : 1 < 1 + (1 - ξ) * e.r := by nlinarith [e.r_pos]
  have := (tendsto_pow_atTop_atTop_of_one_lt hq).atTop_mul_const_of_neg hB0
  exact this.congr fun s => (ex1_path e p h hTB s).symm

/-- **Exercise 1(c)**, O&R p. 125: for `B_0 < 0` and `0 < ξ < 1`, eventually the debt exceeds
the value of all future output, `−(1+r) B_s > Σ (1+r)^{-v} Ȳ`, and consumption
`C_s = Ȳ + ξ r B_s` turns negative. The budget constraint holds only because the rule
eventually demands infeasible (negative) consumption. -/
theorem ex1_eventually_infeasible (e : Economy) (p : Paths) {ξ Ybar : ℝ} (h : e.Flow p)
    (hY : ∀ s, p.Y s = Ybar) (hG : ∀ s, p.G s = 0) (hI : ∀ s, p.I s = 0)
    (hTB : ∀ s, tradeBalance p s = -ξ * e.r * p.B s) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hB0 : p.B 0 < 0) :
    ∃ S, ∀ s, S ≤ s →
      pv e.r (fun _ => Ybar) < -((1 + e.r) * p.B s) ∧ p.C s < 0 := by
  have hr := e.r_pos
  have ht := ex1_debt_unbounded e p h hTB hξ1 hB0
  have hev := ht.eventually (eventually_lt_atBot (min (-Ybar / e.r) (-Ybar / (ξ * e.r))))
  obtain ⟨S, hS⟩ := eventually_atTop.1 hev
  refine ⟨S, fun s hs => ?_⟩
  have hb := hS s hs
  have hb1 : p.B s < -Ybar / e.r := lt_of_lt_of_le hb (min_le_left _ _)
  have hb2 : p.B s < -Ybar / (ξ * e.r) := lt_of_lt_of_le hb (min_le_right _ _)
  rw [lt_div_iff₀ hr] at hb1
  rw [lt_div_iff₀ (mul_pos hξ hr)] at hb2
  rw [pv_const hr, ex1_consumption p hY hG hI hTB s]
  refine ⟨?_, by linarith⟩
  have h1 : 0 < 1 + e.r := by linarith
  rw [div_mul_eq_mul_div, div_lt_iff₀ hr]
  nlinarith

end ObstfeldRogoff.SmallOpenEconomyDynamics.BudgetConstraint
