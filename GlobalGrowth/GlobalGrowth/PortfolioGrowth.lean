/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GlobalGrowth.BrockMirman
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# International portfolio diversification and growth in the stochastic AK model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §7.3.2
(pp. 478–481), equations (69)–(78) and footnote 35.

Risky returns are i.i.d. on a finite state space; the event tree comes from `BrockMirman`.

* **The Kelly problem exactly**: supporting-line and strict concavity; with the physical-capital
  constraint `0 ≤ x ≤ 1` (the book ignores `x ≤ 1`), a KKT share exists (IVT), is unique under
  non-degenerate risk and maximises `E log(R + x(R̃ − R))`; `x* > 0 ⟺ E R̃ > R` and
  `x* < 1 ⟺ E[R/R̃] > 1`; an explicit example where `x ≤ 1` binds and the unconstrained Kelly
  share exceeds one. Unconstrained: with full support and risk on both sides the root of
  `D(x) = 0` exists and is unique. The exact share `x* = E e/E[e²/π*]` versus (76).
* **Infinite-horizon optimality** of `C = (1 − β)W` with the Kelly share (constrained and
  unconstrained), with finite utility, and of `C = (1 − β)W` for **any** portfolio rule (73).
  Consumption growth (75) and expected growth (77) exactly.
* **Diversification**: with symmetric countries and `E r̃ > r`, `D_W ≥ D_n` (Jensen + swap
  symmetry), hence `x*_W ≥ x*_n` and expected growth is weakly higher; strictly when returns are
  not perfectly correlated and the autarky share is below one.
* **The world-fund variance**: a portfolio's variance is at most the average of the country
  variances; the book's `Var r̃^W < Var r̃^n` for every `n` needs equal variances (explicit
  counterexample `101/400 > 1/100` otherwise).
* The approximations (74)–(78) as algebra given (74).
-/

namespace ObstfeldRogoff.GlobalGrowth.PortfolioGrowth

open Finset Filter Topology
open ObstfeldRogoff.GlobalGrowth.BrockMirman

variable {S : Type*} [Fintype S]

/-! ## The one-period log (Kelly) portfolio problem -/

/-- Gross portfolio return with risky share `x`: `(1 + r) + x(r̃ − r)`, O&R (70), with `R = 1 + r`
and `Rt(s) = 1 + r̃(s)`. -/
def portRet (R : ℝ) (Rt : S → ℝ) (x : ℝ) (s : S) : ℝ := R + x * (Rt s - R)

/-- Expected log gross return `g(x) = E log(R + x(R̃ − R))`. -/
noncomputable def expLog (p : S → ℝ) (R : ℝ) (Rt : S → ℝ) (x : ℝ) : ℝ :=
  ∑ s, p s * Real.log (portRet R Rt x s)

/-- The first-order-condition function `D(x) = E[(R̃ − R)/(R + x(R̃ − R))]`, the derivative of
`g` (the exact form of the Euler equations (71)–(72) for the portfolio share). -/
noncomputable def focD (p : S → ℝ) (R : ℝ) (Rt : S → ℝ) (x : ℝ) : ℝ :=
  ∑ s, p s * ((Rt s - R) / portRet R Rt x s)

/-- Returns on the finite state space: a pmf `p`, riskless gross return `R > 0`, risky gross
returns `Rt(s) > 0`. -/
structure Returns (p : S → ℝ) (R : ℝ) (Rt : S → ℝ) : Prop where
  p_nonneg : ∀ s, 0 ≤ p s
  p_sum : ∑ s, p s = 1
  R_pos : 0 < R
  Rt_pos : ∀ s, 0 < Rt s

/-- Portfolio returns are positive for shares in `[0, 1]` (no short sales of either capital). -/
theorem portRet_pos {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (s : S) : 0 < portRet R Rt x s := by
  unfold portRet
  have h := hr.Rt_pos s
  have h2 := hr.R_pos
  rcases eq_or_lt_of_le hx1 with h1 | h1
  · rw [h1]; linarith
  · nlinarith [mul_nonneg hx0 h.le, mul_pos (sub_pos.2 h1) h2]

/-- **Concavity (supporting line)**: `g(y) ≤ g(x) + (y − x) D(x)` whenever both portfolios have
positive returns in every state. -/
theorem expLog_le_tangent {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt) {x y : ℝ}
    (hx : ∀ s, 0 < portRet R Rt x s) (hy : ∀ s, 0 < portRet R Rt y s) :
    expLog p R Rt y ≤ expLog p R Rt x + (y - x) * focD p R Rt x := by
  unfold expLog focD
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  have l := Real.log_le_sub_one_of_pos (div_pos (hy s) (hx s))
  rw [Real.log_div (hy s).ne' (hx s).ne'] at l
  have e : portRet R Rt y s / portRet R Rt x s - 1 =
      (y - x) * ((Rt s - R) / portRet R Rt x s) := by
    rw [div_sub_one (hx s).ne', mul_div_assoc']
    congr 1
    unfold portRet
    ring
  rw [e] at l
  have := mul_le_mul_of_nonneg_left l (hr.p_nonneg s)
  nlinarith

/-- Non-degenerate risk: some state with positive probability has `R̃ ≠ R`. -/
def Nondegenerate (p : S → ℝ) (R : ℝ) (Rt : S → ℝ) : Prop := ∃ s, 0 < p s ∧ Rt s ≠ R

/-- **Strict concavity**: under non-degenerate risk the supporting line is strict for `y ≠ x`. -/
theorem expLog_lt_tangent {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt)
    (hnd : Nondegenerate p R Rt) {x y : ℝ} (hx : ∀ s, 0 < portRet R Rt x s)
    (hy : ∀ s, 0 < portRet R Rt y s) (hxy : y ≠ x) :
    expLog p R Rt y < expLog p R Rt x + (y - x) * focD p R Rt x := by
  obtain ⟨s₀, hp0, hs0⟩ := hnd
  unfold expLog focD
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have key : ∀ s, portRet R Rt y s / portRet R Rt x s - 1 =
      (y - x) * ((Rt s - R) / portRet R Rt x s) := by
    intro s
    rw [div_sub_one (hx s).ne', mul_div_assoc']
    congr 1
    unfold portRet
    ring
  refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s₀, Finset.mem_univ _, ?_⟩
  · have l := Real.log_le_sub_one_of_pos (div_pos (hy s) (hx s))
    rw [Real.log_div (hy s).ne' (hx s).ne', key] at l
    have := mul_le_mul_of_nonneg_left l (hr.p_nonneg s)
    nlinarith
  · have hne : portRet R Rt y s₀ / portRet R Rt x s₀ ≠ 1 := by
      intro h
      rw [div_eq_one_iff_eq (hx s₀).ne'] at h
      unfold portRet at h
      have : (y - x) * (Rt s₀ - R) = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · exact hxy (by linarith)
      · exact hs0 (by linarith)
    have l := Real.log_lt_sub_one_of_pos (div_pos (hy s₀) (hx s₀)) hne
    rw [Real.log_div (hy s₀).ne' (hx s₀).ne', key] at l
    have := mul_lt_mul_of_pos_left l hp0
    nlinarith

/-- `D` is non-increasing, and strictly decreasing under non-degenerate risk, on shares with
positive returns. -/
theorem focD_anti {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hp0 : ∀ s, 0 ≤ p s) {x y : ℝ}
    (hx : ∀ s, 0 < portRet R Rt x s) (hy : ∀ s, 0 < portRet R Rt y s) (hxy : x < y) :
    focD p R Rt y ≤ focD p R Rt x ∧
      (Nondegenerate p R Rt → focD p R Rt y < focD p R Rt x) := by
  have hterm : ∀ s, (Rt s - R) / portRet R Rt x s - (Rt s - R) / portRet R Rt y s =
      (y - x) * (Rt s - R) ^ 2 / (portRet R Rt x s * portRet R Rt y s) := by
    intro s
    rw [div_sub_div _ _ (hx s).ne' (hy s).ne']
    congr 1
    unfold portRet
    ring
  have hdiff : focD p R Rt x - focD p R Rt y = ∑ s, p s *
      ((y - x) * (Rt s - R) ^ 2 / (portRet R Rt x s * portRet R Rt y s)) := by
    unfold focD
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by rw [← mul_sub, hterm]
  have hnn : ∀ s, 0 ≤ p s * ((y - x) * (Rt s - R) ^ 2 /
      (portRet R Rt x s * portRet R Rt y s)) := fun s =>
    mul_nonneg (hp0 s) (div_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
      (mul_pos (hx s) (hy s)).le)
  refine ⟨by linarith [Finset.sum_nonneg fun s (_ : s ∈ Finset.univ) => hnn s], ?_⟩
  rintro ⟨s₀, hp0, hs0⟩
  have hpos : 0 < p s₀ * ((y - x) * (Rt s₀ - R) ^ 2 /
      (portRet R Rt x s₀ * portRet R Rt y s₀)) := by
    have : 0 < (Rt s₀ - R) ^ 2 := by
      have : Rt s₀ - R ≠ 0 := sub_ne_zero.2 hs0
      positivity
    exact mul_pos hp0 (div_pos (mul_pos (by linarith) this) (mul_pos (hx s₀) (hy s₀)))
  have := Finset.sum_lt_sum (s := Finset.univ) (fun s _ => hnn s)
    ⟨s₀, Finset.mem_univ _, hpos⟩
  simp only [Finset.sum_const_zero] at this
  linarith [show ∑ _s : S, (0 : ℝ) = 0 from Finset.sum_const_zero]

/-- The Karush–Kuhn–Tucker conditions for the risky share on `[0, 1]` (no short sales of the
physical riskless or risky capital; the book ignores `x ≤ 1`). -/
def IsKKT (p : S → ℝ) (R : ℝ) (Rt : S → ℝ) (x : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ 1 ∧ (0 < x → 0 ≤ focD p R Rt x) ∧ (x < 1 → focD p R Rt x ≤ 0)

/-- A KKT share maximises the expected log return over `[0, 1]`. -/
theorem IsKKT.isMax {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt) {x : ℝ}
    (hk : IsKKT p R Rt x) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    expLog p R Rt y ≤ expLog p R Rt x := by
  obtain ⟨hx0, hx1, hA, hB⟩ := hk
  have ht := expLog_le_tangent hr (portRet_pos hr hx0 hx1) (portRet_pos hr hy0 hy1)
  have : (y - x) * focD p R Rt x ≤ 0 := by
    rcases lt_trichotomy y x with h | h | h
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hA (by linarith))
    · rw [h, sub_self, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (hB (by linarith))
  linarith

/-- `D` is continuous on `[0, 1]`. -/
theorem continuousOn_focD {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt) :
    ContinuousOn (focD p R Rt) (Set.Icc 0 1) := by
  unfold focD
  refine continuousOn_finsetSum _ fun s _ => ?_
  refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const ?_ ?_)
  · unfold portRet; fun_prop
  · intro x hx; exact (portRet_pos hr hx.1 hx.2 s).ne'

/-- **Existence of the optimal risky share** on `[0, 1]` (the Kelly portfolio with the
physical-capital constraint): a KKT share exists. -/
theorem exists_kkt {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt) :
    ∃ x, IsKKT p R Rt x := by
  by_cases h0 : focD p R Rt 0 ≤ 0
  · exact ⟨0, le_rfl, zero_le_one, fun h => absurd h (lt_irrefl 0), fun _ => h0⟩
  by_cases h1 : 0 ≤ focD p R Rt 1
  · exact ⟨1, zero_le_one, le_rfl, fun _ => h1, fun h => absurd h (lt_irrefl 1)⟩
  push Not at h0 h1
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' zero_le_one (continuousOn_focD hr)
    ⟨h1.le, h0.le⟩
  exact ⟨x, hx.1, hx.2, fun _ => hx0.ge, fun _ => hx0.le⟩

/-- **Uniqueness of the optimal share** under non-degenerate risk: the KKT share is unique,
and it is the unique maximiser of the expected log return on `[0, 1]`. -/
theorem kkt_unique {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt)
    (hnd : Nondegenerate p R Rt) {x y : ℝ} (hx : IsKKT p R Rt x) (hy : IsKKT p R Rt y) :
    x = y := by
  by_contra hne
  have hlt := expLog_lt_tangent hr hnd (portRet_pos hr hx.1 hx.2.1)
    (portRet_pos hr hy.1 hy.2.1) (Ne.symm hne)
  have hle := IsKKT.isMax hr hy hx.1 hx.2.1
  have := IsKKT.isMax hr hx hy.1 hy.2.1
  have hmax : (y - x) * focD p R Rt x ≤ 0 := by
    obtain ⟨hx0, hx1, hA, hB⟩ := hx
    rcases lt_trichotomy y x with h | h | h
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hA (by linarith [hy.1]))
    · rw [h, sub_self, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (hB (by linarith [hy.2.1]))
  linarith

/-- **Positive risky share iff positive expected excess return** (O&R p. 479, `E r̃ > r`):
the optimal share is positive iff `E R̃ > R`. -/
theorem kkt_pos_iff {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt)
    (hnd : Nondegenerate p R Rt) {x : ℝ} (hx : IsKKT p R Rt x) :
    0 < x ↔ R < ∑ s, p s * Rt s := by
  have hR := hr.R_pos
  have hD0 : focD p R Rt 0 = (∑ s, p s * Rt s - R) / R := by
    rw [eq_div_iff hR.ne']
    have e1 : ∑ s, p s * Rt s - R = ∑ s, p s * (Rt s - R) := by
      rw [Finset.sum_congr rfl fun s _ => mul_sub (p s) (Rt s) R, Finset.sum_sub_distrib,
        ← Finset.sum_mul, hr.p_sum, one_mul]
    rw [e1]
    unfold focD portRet
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by
      rw [zero_mul, add_zero, mul_assoc, div_mul_cancel₀ _ hR.ne']
  constructor
  · intro hpos
    by_contra hle
    push Not at hle
    have hD : focD p R Rt 0 ≤ 0 := by
      rw [hD0]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hR.le
    have := (focD_anti hr.p_nonneg (portRet_pos hr le_rfl zero_le_one)
      (portRet_pos hr hx.1 hx.2.1) hpos).2 hnd
    have := hx.2.2.1 hpos
    linarith
  · intro hlt
    by_contra hle
    push Not at hle
    have hx0 : x = 0 := le_antisymm hle hx.1
    have := hx.2.2.2 (by rw [hx0]; exact zero_lt_one)
    rw [hx0, hD0] at this
    have : 0 < (∑ s, p s * Rt s - R) / R := div_pos (by linarith) hR
    linarith

/-- **The constraint `x ≤ 1` binds iff `E[R/R̃] ≤ 1`** (the book ignores it): the optimal
share is below one iff `E[R/R̃] > 1`. -/
theorem kkt_lt_one_iff {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt)
    (hnd : Nondegenerate p R Rt) {x : ℝ} (hx : IsKKT p R Rt x) :
    x < 1 ↔ 1 < ∑ s, p s * (R / Rt s) := by
  have hD1 : focD p R Rt 1 = 1 - ∑ s, p s * (R / Rt s) := by
    have hterm : ∀ s, p s * ((Rt s - R) / portRet R Rt 1 s) = p s - p s * (R / Rt s) := by
      intro s
      have := (hr.Rt_pos s).ne'
      rw [show portRet R Rt 1 s = Rt s by unfold portRet; ring]
      field_simp
    unfold focD
    rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_sub_distrib, hr.p_sum]
  constructor
  · intro hlt
    by_contra hle
    push Not at hle
    have hD : 0 ≤ focD p R Rt 1 := by rw [hD1]; linarith
    have := (focD_anti hr.p_nonneg (portRet_pos hr hx.1 hx.2.1)
      (portRet_pos hr zero_le_one le_rfl) hlt).2 hnd
    have := hx.2.2.2 hlt
    linarith
  · intro hgt
    by_contra hle
    push Not at hle
    have hx1 : x = 1 := le_antisymm hx.2.1 hle
    have := hx.2.2.1 (by rw [hx1]; exact zero_lt_one)
    rw [hx1, hD1] at this
    linarith

/-- **Exact Kelly formula** (the exact counterpart of (76)): at an interior optimum
`E(R̃ − R) = x* E[(R̃ − R)²/(R + x*(R̃ − R))]`, i.e.
`x* = E(R̃ − R) / E[(R̃ − R)²/π*]`. For small risk `π* ≈ R`, so `x* ≈ R E e/E e²`, which differs
from the book's (76) `x = E e/(β² R Var e)` by the factor `(βR)²`: the book's (74) is
expanded around zero consumption growth although the AK economy grows (`β(1 + A) > 1`). -/
theorem kelly_exact {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt) {x : ℝ}
    (hx : ∀ s, 0 < portRet R Rt x s) (hfoc : focD p R Rt x = 0) :
    ∑ s, p s * (Rt s - R) = x * ∑ s, p s * ((Rt s - R) ^ 2 / portRet R Rt x s) := by
  have hR := hr.R_pos
  have key : ∀ s, p s * (Rt s - R) = R * (p s * ((Rt s - R) / portRet R Rt x s)) +
      x * (p s * ((Rt s - R) ^ 2 / portRet R Rt x s)) := by
    intro s
    have e : R * (p s * ((Rt s - R) / portRet R Rt x s)) +
        x * (p s * ((Rt s - R) ^ 2 / portRet R Rt x s)) =
        p s * (Rt s - R) * ((R + x * (Rt s - R)) / portRet R Rt x s) := by ring
    rw [e, show R + x * (Rt s - R) = portRet R Rt x s from rfl, div_self (hx s).ne', mul_one]
  rw [Finset.sum_congr rfl fun s _ => key s, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  unfold focD at hfoc
  rw [hfoc, mul_zero, zero_add]

/-- **Counterexample: the book's implicit `x ≤ 1` can bind.** With `R = 1` and risky gross
returns `9/10` or `2` with probability `1/2` each, `D(1) > 0`, so the constrained optimum is the
corner `x* = 1`; the unconstrained problem does strictly better at `x = 11/10`
(borrowing at the riskless rate), so the unconstrained Kelly share exceeds one. -/
theorem corner_counterexample :
    let p : Fin 2 → ℝ := fun _ => 1 / 2
    let Rt : Fin 2 → ℝ := ![9 / 10, 2]
    0 < focD p 1 Rt 1 ∧ (∀ s, 0 < portRet 1 Rt (11 / 10) s) ∧
      expLog p 1 Rt 1 < expLog p 1 Rt (11 / 10) := by
  intro p Rt
  have hpos1 : ∀ s, 0 < portRet 1 Rt 1 s := by
    intro s; fin_cases s <;> norm_num [portRet, Rt]
  have hpos2 : ∀ s, 0 < portRet 1 Rt (11 / 10) s := by
    intro s; fin_cases s <;> simp [portRet, Rt] <;> norm_num
  have hD : 0 < focD p 1 Rt (11 / 10) := by
    simp [focD, portRet, Rt, p, Fin.sum_univ_two]; norm_num
  have hr : Returns p 1 Rt := ⟨fun _ => by norm_num [p], by simp [p],
    one_pos, fun s => by fin_cases s <;> norm_num [Rt]⟩
  have hnd : Nondegenerate p 1 Rt := ⟨0, by norm_num [p], by simp [Rt]; norm_num⟩
  refine ⟨by simp [focD, portRet, Rt, p, Fin.sum_univ_two]; norm_num, hpos2, ?_⟩
  have := expLog_lt_tangent hr hnd hpos2 hpos1 (by norm_num)
  nlinarith
/-- An interior constrained optimum (`0 < x* < 1`, riskless holdings positive, the book's
assumption, fn 35) solves the unconstrained first-order condition `D(x*) = 0`; so it is also the
unconstrained Kelly share (`existsUnique_kelly`, `kelly_plan_optimal_unconstrained`). -/
theorem kkt_interior_foc {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} {x : ℝ} (hk : IsKKT p R Rt x)
    (h0 : 0 < x) (h1 : x < 1) : focD p R Rt x = 0 :=
  le_antisymm (hk.2.2.2 h1) (hk.2.2.1 h0)

/-! ## The unconstrained Kelly share (short positions allowed) -/

/-- With full support, if some state has `R̃ < R`, there is a share `x ≥ 0` with positive returns
in every state and `D(x) < 0` (the log objective falls steeply near the bankruptcy boundary). -/
theorem exists_focD_neg {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hR : 0 < R) (hfull : ∀ s, 0 < p s)
    (hdown : ∃ s, Rt s < R) :
    ∃ x, 0 ≤ x ∧ (∀ s, 0 < portRet R Rt x s) ∧ focD p R Rt x < 0 := by
  classical
  set Sd := Finset.univ.filter fun s => Rt s < R
  have hSd : Sd.Nonempty := by
    obtain ⟨s, hs⟩ := hdown; exact ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩⟩
  obtain ⟨s₀, hs₀, hmin⟩ := Finset.exists_min_image Sd (fun s => R / (R - Rt s)) hSd
  have hs₀' : Rt s₀ < R := (Finset.mem_filter.1 hs₀).2
  set d := R - Rt s₀
  have hd : 0 < d := by simp only [d]; linarith
  set B := ∑ s, p s * |Rt s - R| / R
  have hB : 0 ≤ B := Finset.sum_nonneg fun s _ =>
    div_nonneg (mul_nonneg (hfull s).le (abs_nonneg _)) hR.le
  set π₀ := min R (p s₀ * d / (B + 1)) / 2
  have hq : 0 < p s₀ * d / (B + 1) := div_pos (mul_pos (hfull s₀) hd) (by linarith)
  have hπ₀ : 0 < π₀ := by simp only [π₀]; exact half_pos (lt_min hR hq)
  have hπR : π₀ < R := by
    have := min_le_left R (p s₀ * d / (B + 1)); simp only [π₀]; linarith
  have hπq : π₀ ≤ p s₀ * d / (B + 1) / 2 := by
    have := min_le_right R (p s₀ * d / (B + 1)); simp only [π₀]; linarith
  set x := (R - π₀) / d
  have hx : 0 ≤ x := div_nonneg (by linarith) hd.le
  have hxd : x * d = R - π₀ := by simp only [x]; field_simp
  -- lower bound on all portfolio returns
  have hlow : ∀ s, Rt s < R → π₀ ≤ portRet R Rt x s := by
    intro s hs
    have hm := hmin s (Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩)
    have h1 : 0 < R - Rt s := by linarith
    have hle : R - Rt s ≤ d := by
      rw [div_le_div_iff₀ hd h1] at hm
      nlinarith
    unfold portRet
    nlinarith
  have hpos : ∀ s, 0 < portRet R Rt x s := by
    intro s
    by_cases hs : Rt s < R
    · exact lt_of_lt_of_le hπ₀ (hlow s hs)
    · push Not at hs; unfold portRet; nlinarith
  have hs₀π : portRet R Rt x s₀ = π₀ := by
    unfold portRet
    have : x * (Rt s₀ - R) = -(x * d) := by simp only [d]; ring
    rw [this, hxd]; ring
  refine ⟨x, hx, hpos, ?_⟩
  -- each term is at most `p |R̃ − R|/R`, and the `s₀` term is `−p(s₀) d/π₀`
  have hterm : ∀ s, p s * ((Rt s - R) / portRet R Rt x s) ≤ p s * |Rt s - R| / R := by
    intro s
    by_cases hs : Rt s < R
    · have : (Rt s - R) / portRet R Rt x s ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) (hpos s).le
      have := mul_nonpos_of_nonneg_of_nonpos (hfull s).le this
      have : 0 ≤ p s * |Rt s - R| / R := div_nonneg (mul_nonneg (hfull s).le (abs_nonneg _)) hR.le
      linarith
    · push Not at hs
      have hge : R ≤ portRet R Rt x s := by unfold portRet; nlinarith
      rw [abs_of_nonneg (by linarith), mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by linarith) hR hge)
        (hfull s).le
  unfold focD
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s₀), hs₀π]
  have hrest : ∑ s ∈ Finset.univ.erase s₀, p s * ((Rt s - R) / portRet R Rt x s) ≤ B := by
    calc _ ≤ ∑ s ∈ Finset.univ.erase s₀, p s * |Rt s - R| / R :=
          Finset.sum_le_sum fun s _ => hterm s
      _ ≤ B := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun s _ _ => div_nonneg (mul_nonneg (hfull s).le (abs_nonneg _)) hR.le
  have hbig : p s₀ * ((Rt s₀ - R) / π₀) ≤ -(2 * (B + 1)) := by
    rw [show Rt s₀ - R = -d by simp only [d]; ring, mul_div_assoc', div_le_iff₀ hπ₀]
    · have : π₀ * (2 * (B + 1)) ≤ p s₀ * d := by
        have h2 := mul_le_mul_of_nonneg_right hπq (show (0 : ℝ) ≤ 2 * (B + 1) by linarith)
        have e : p s₀ * d / (B + 1) / 2 * (2 * (B + 1)) = p s₀ * d := by
          field_simp
        linarith
      nlinarith
  linarith

/-- **Existence and uniqueness of the unconstrained Kelly share** (O&R (76), exact): with full
support and risk on both sides (`R̃ < R` in some state and `R̃ > R` in another), there is exactly
one share `x*` with positive returns in every state and `D(x*) = 0`. It may exceed one (see
`corner_counterexample`), in which case it requires negative riskless holdings. -/
theorem existsUnique_kelly {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hR : 0 < R)
    (hfull : ∀ s, 0 < p s) (hdown : ∃ s, Rt s < R) (hup : ∃ s, R < Rt s) :
    ∃! x, (∀ s, 0 < portRet R Rt x s) ∧ focD p R Rt x = 0 := by
  obtain ⟨x₁, hx₁, hπ₁, hD₁⟩ := exists_focD_neg hR hfull hdown
  -- the reflected problem `R̃' = 2R − R̃` gives a share `x₀ ≤ 0` with `D(x₀) > 0`
  obtain ⟨y, hy, hπy, hDy⟩ := exists_focD_neg (Rt := fun s => 2 * R - Rt s) hR hfull
    (by obtain ⟨s, hs⟩ := hup; exact ⟨s, by linarith⟩)
  set x₀ := -y
  have hrefl : ∀ s, portRet R (fun s => 2 * R - Rt s) y s = portRet R Rt x₀ s := fun s => by
    simp only [portRet, x₀]; ring
  have hπ₀ : ∀ s, 0 < portRet R Rt x₀ s := fun s => hrefl s ▸ hπy s
  have hD₀ : 0 < focD p R Rt x₀ := by
    have : focD p R (fun s => 2 * R - Rt s) y = -focD p R Rt x₀ := by
      unfold focD
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun s _ => by rw [hrefl]; ring
    linarith
  have hx01 : x₀ ≤ x₁ := by simp only [x₀]; linarith
  -- positivity of returns on the whole interval (returns are affine in the share)
  have hint : ∀ x ∈ Set.Icc x₀ x₁, ∀ s, 0 < portRet R Rt x s := by
    intro x hx s
    have h0 := hπ₀ s
    have h1 := hπ₁ s
    unfold portRet at *
    rcases eq_or_lt_of_le hx01 with h | h
    · have : x = x₀ := by linarith [hx.1, hx.2]
      rw [this]; exact h0
    · have ht : x = x₀ + (x - x₀) / (x₁ - x₀) * (x₁ - x₀) := by field_simp; ring
      have hθ0 : 0 ≤ (x - x₀) / (x₁ - x₀) := div_nonneg (by linarith [hx.1]) (by linarith)
      have hθ1 : (x - x₀) / (x₁ - x₀) ≤ 1 := (div_le_one (by linarith)).2 (by linarith [hx.2])
      have : R + x * (Rt s - R) = (1 - (x - x₀) / (x₁ - x₀)) * (R + x₀ * (Rt s - R)) +
          (x - x₀) / (x₁ - x₀) * (R + x₁ * (Rt s - R)) := by
        rw [ht]; field_simp; ring
      rw [this]
      rcases eq_or_lt_of_le hθ1 with h2 | h2
      · rw [h2, sub_self, zero_mul, zero_add, one_mul]; exact h1
      · nlinarith [mul_pos (sub_pos.2 h2) h0, mul_nonneg hθ0 h1.le]
  have hcont : ContinuousOn (focD p R Rt) (Set.Icc x₀ x₁) := by
    unfold focD
    refine continuousOn_finsetSum _ fun s _ => ?_
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const ?_ ?_)
    · unfold portRet; fun_prop
    · intro x hx; exact (hint x hx s).ne'
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' hx01 hcont ⟨hD₁.le, hD₀.le⟩
  have hp0 : ∀ s, 0 ≤ p s := fun s => (hfull s).le
  exact ⟨x, ⟨hint x hx, hx0⟩, fun y ⟨hπy', hDy'⟩ => by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := (focD_anti hp0 hπy' (hint x hx) h).2 ⟨_, hfull _, ne_of_lt hdown.choose_spec⟩
      linarith
    · have := (focD_anti hp0 (hint x hx) hπy' h).2
        ⟨_, hfull _, ne_of_lt hdown.choose_spec⟩
      linarith⟩

/-! ## The infinite-horizon consumption–portfolio problem on the event tree -/

/-- The i.i.d. transition kernel of the risky return. -/
def iidKernel (p : S → ℝ) (_ s' : S) : ℝ := p s'

/-- The i.i.d. kernel is a Markov kernel. -/
theorem iidKernel_isMarkov {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt) :
    IsMarkov (iidKernel p) :=
  ⟨fun _ s' => hr.p_nonneg s', fun _ => hr.p_sum⟩

/-- Wealth at a node, O&R (70): `W₀` at the root; otherwise the gross return on the risky and
riskless capital `(kr, ks)` carried out of the parent node. -/
def wealth (R : ℝ) (Rt : S → ℝ) (W₀ : ℝ) (kr ks : List S → ℝ) : List S → ℝ
  | [] => 0
  | [_] => W₀
  | s' :: s :: h => Rt s' * kr (s :: h) + R * ks (s :: h)

/-- A feasible consumption–investment plan: positive consumption, the budget
`C + K^r + K^s = W`, and non-negative wealth in every successor state (so short positions are
allowed as long as wealth stays non-negative). -/
def Feasible (R : ℝ) (Rt : S → ℝ) (W₀ : ℝ) (c kr ks : List S → ℝ) : Prop :=
  ∀ s h, 0 < c (s :: h) ∧ c (s :: h) + kr (s :: h) + ks (s :: h) = wealth R Rt W₀ kr ks (s :: h)
    ∧ ∀ s', 0 ≤ Rt s' * kr (s :: h) + R * ks (s :: h)

/-- Expected discounted log utility (69) up to horizon `T`. -/
noncomputable def utility (p : S → ℝ) (β : ℝ) (c : List S → ℝ) (s₀ : S) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, β ^ t * ev (iidKernel p) (fun l => Real.log (c l)) t s₀ []

/-- Wealth under the reference plan: consume `(1 − β)W` (73), invest the share `x(node)` of
savings `βW` in risky capital. -/
noncomputable def refWealth (R : ℝ) (Rt : S → ℝ) (β W₀ : ℝ) (x : List S → ℝ) : List S → ℝ
  | [] => 0
  | [_] => W₀
  | s' :: s :: h => β * portRet R Rt (x (s :: h)) s' * refWealth R Rt β W₀ x (s :: h)

/-- Reference consumption `C = (1 − β) W` (73). -/
noncomputable def refCons (R : ℝ) (Rt : S → ℝ) (β W₀ : ℝ) (x : List S → ℝ) (l : List S) : ℝ :=
  (1 - β) * refWealth R Rt β W₀ x l

/-- Reference risky capital `x β W`. -/
noncomputable def refKr (R : ℝ) (Rt : S → ℝ) (β W₀ : ℝ) (x : List S → ℝ) (l : List S) : ℝ :=
  x l * (β * refWealth R Rt β W₀ x l)

/-- Reference riskless capital `(1 − x) β W`. -/
noncomputable def refKs (R : ℝ) (Rt : S → ℝ) (β W₀ : ℝ) (x : List S → ℝ) (l : List S) : ℝ :=
  (1 - x l) * (β * refWealth R Rt β W₀ x l)

omit [Fintype S] in
/-- The reference plan's wealth satisfies the budget (70). -/
theorem wealth_ref (R : ℝ) (Rt : S → ℝ) (β W₀ : ℝ) (x : List S → ℝ) (l : List S) :
    wealth R Rt W₀ (refKr R Rt β W₀ x) (refKs R Rt β W₀ x) l = refWealth R Rt β W₀ x l := by
  match l with
  | [] => rfl
  | [_] => rfl
  | s' :: s :: h => simp only [wealth, refWealth, refKr, refKs, portRet]; ring

omit [Fintype S] in
/-- Reference wealth is positive when every portfolio return is positive. -/
theorem refWealth_pos {R : ℝ} {Rt : S → ℝ} {β W₀ : ℝ} {x : List S → ℝ} (hβ : 0 < β)
    (hW : 0 < W₀) (hπ : ∀ l s, 0 < portRet R Rt (x l) s) :
    ∀ l : List S, l ≠ [] → 0 < refWealth R Rt β W₀ x l
  | [], h => absurd rfl h
  | [_], _ => hW
  | s' :: s :: h, _ => by
    simp only [refWealth]
    exact mul_pos (mul_pos hβ (hπ _ _)) (refWealth_pos hβ hW hπ (s :: h) (List.cons_ne_nil _ _))

omit [Fintype S] in
/-- The reference plan is feasible. -/
theorem ref_feasible {R : ℝ} {Rt : S → ℝ} {β W₀ : ℝ} {x : List S → ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hW : 0 < W₀) (hπ : ∀ l s, 0 < portRet R Rt (x l) s) :
    Feasible R Rt W₀ (refCons R Rt β W₀ x) (refKr R Rt β W₀ x) (refKs R Rt β W₀ x) := by
  intro s h
  have hw := refWealth_pos hβ0 hW hπ (s :: h) (List.cons_ne_nil _ _)
  refine ⟨mul_pos (by linarith) hw, ?_, fun s' => ?_⟩
  · rw [wealth_ref]; simp only [refCons, refKr, refKs]; ring
  · have := hπ (s :: h) s'
    have e : Rt s' * refKr R Rt β W₀ x (s :: h) + R * refKs R Rt β W₀ x (s :: h) =
        β * refWealth R Rt β W₀ x (s :: h) * portRet R Rt (x (s :: h)) s' := by
      simp only [refKr, refKs, portRet]; ring
    rw [e]; positivity

/-- The rival's wealth relative to reference consumption, `Z = W/C°`. -/
noncomputable def relWealth (R : ℝ) (Rt : S → ℝ) (β W₀ : ℝ) (x : List S → ℝ)
    (kr ks : List S → ℝ) (l : List S) : ℝ :=
  wealth R Rt W₀ kr ks l / refCons R Rt β W₀ x l

/-- The node condition behind the telescoping: the rival's positions `(K^r, K^s)` at a node,
priced with the reference plan's stochastic discount factor `1/π`, are worth at most
`K^r + K^s`: `E[(R̃ K^r + R K^s)/π] ≤ K^r + K^s`. -/
def NodeCond (p : S → ℝ) (R : ℝ) (Rt : S → ℝ) (xv kr ks : ℝ) : Prop :=
  ∑ s', p s' * ((Rt s' * kr + R * ks) / portRet R Rt xv s') ≤ kr + ks

/-- **(73) for any portfolio rule**: a rival that uses the same portfolio shares as the
reference plan satisfies the node condition with equality (the portfolio return cancels). -/
theorem nodeCond_same_portfolio {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt)
    {xv sv : ℝ} (hπ : ∀ s, 0 < portRet R Rt xv s) :
    NodeCond p R Rt xv (xv * sv) ((1 - xv) * sv) := by
  unfold NodeCond
  have : ∀ s', p s' * ((Rt s' * (xv * sv) + R * ((1 - xv) * sv)) / portRet R Rt xv s') =
      p s' * sv := fun s' => by
    rw [show Rt s' * (xv * sv) + R * ((1 - xv) * sv) = sv * portRet R Rt xv s' by
      unfold portRet; ring, mul_div_assoc, div_self (hπ s').ne', mul_one]
  rw [Finset.sum_congr rfl fun s' _ => this s', ← Finset.sum_mul, hr.p_sum]
  linarith

/-- **Kelly/KKT portfolio, no short sales**: if `x*` satisfies the KKT conditions on `[0, 1]`,
every non-negative position satisfies the node condition. -/
theorem nodeCond_kkt {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt) {x : ℝ}
    (hk : IsKKT p R Rt x) {kr ks : ℝ} (hkr : 0 ≤ kr) (hks : 0 ≤ ks) :
    NodeCond p R Rt x kr ks := by
  obtain ⟨hx0, hx1, hA, hB⟩ := hk
  have hπ := portRet_pos hr hx0 hx1
  set mr := ∑ s, p s * (Rt s / portRet R Rt x s)
  set ms := ∑ s, p s * (R / portRet R Rt x s)
  have hD : focD p R Rt x = mr - ms := by
    unfold focD
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by rw [← mul_sub, sub_div]
  have hone : x * mr + (1 - x) * ms = 1 := by
    have : ∀ s, x * (p s * (Rt s / portRet R Rt x s)) + (1 - x) * (p s * (R / portRet R Rt x s))
        = p s := fun s => by
      rw [show x * (p s * (Rt s / portRet R Rt x s)) + (1 - x) * (p s * (R / portRet R Rt x s)) =
        p s * ((R + x * (Rt s - R)) / portRet R Rt x s) by ring]
      rw [show R + x * (Rt s - R) = portRet R Rt x s from rfl, div_self (hπ s).ne', mul_one]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl fun s _ => this s, hr.p_sum]
  have hmr : mr ≤ 1 := by
    rcases eq_or_lt_of_le hx1 with h | h
    · rw [h] at hone; linarith
    · have := hB h; nlinarith
  have hms : ms ≤ 1 := by
    rcases eq_or_lt_of_le hx0 with h | h
    · rw [← h] at hone; linarith
    · have := hA h; nlinarith
  unfold NodeCond
  have : ∀ s', p s' * ((Rt s' * kr + R * ks) / portRet R Rt x s') =
      kr * (p s' * (Rt s' / portRet R Rt x s')) + ks * (p s' * (R / portRet R Rt x s')) :=
    fun s' => by ring
  rw [Finset.sum_congr rfl fun s' _ => this s', Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  nlinarith

/-- **Unconstrained Kelly portfolio** (the book's setting, short positions allowed): if `x*`
solves the first-order condition `D(x*) = 0` with positive returns, every position satisfies the
node condition (with equality). -/
theorem nodeCond_foc {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt) {x : ℝ}
    (hπ : ∀ s, 0 < portRet R Rt x s) (hfoc : focD p R Rt x = 0) (kr ks : ℝ) :
    NodeCond p R Rt x kr ks := by
  set mr := ∑ s, p s * (Rt s / portRet R Rt x s)
  set ms := ∑ s, p s * (R / portRet R Rt x s)
  have hD : focD p R Rt x = mr - ms := by
    unfold focD
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by rw [← mul_sub, sub_div]
  have hone : x * mr + (1 - x) * ms = 1 := by
    have : ∀ s, x * (p s * (Rt s / portRet R Rt x s)) + (1 - x) * (p s * (R / portRet R Rt x s))
        = p s := fun s => by
      rw [show x * (p s * (Rt s / portRet R Rt x s)) + (1 - x) * (p s * (R / portRet R Rt x s)) =
        p s * ((R + x * (Rt s - R)) / portRet R Rt x s) by ring]
      rw [show R + x * (Rt s - R) = portRet R Rt x s from rfl, div_self (hπ s).ne', mul_one]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl fun s _ => this s, hr.p_sum]
  rw [hfoc] at hD
  have hms' : ms = mr := by linarith
  have hmr : mr = 1 := by
    have : x * mr + (1 - x) * mr = mr := by ring
    rw [hms'] at hone; linarith
  have hms : ms = 1 := by linarith
  have e1 : (∑ i, p i * (Rt i / portRet R Rt x i)) = 1 := hmr
  have e2 : (∑ i, p i * (R / portRet R Rt x i)) = 1 := hms
  unfold NodeCond
  have : ∀ s', p s' * ((Rt s' * kr + R * ks) / portRet R Rt x s') =
      kr * (p s' * (Rt s' / portRet R Rt x s')) + ks * (p s' * (R / portRet R Rt x s')) :=
    fun s' => by ring
  rw [Finset.sum_congr rfl fun s' _ => this s', Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, e1, e2]
  linarith

/-- **Optimality of `C = (1 − β)W` with the reference portfolio rule** (O&R (73) and the Kelly
share (76), made exact, over the genuine infinite horizon). If at every node the rival's
positions satisfy the node condition for the reference share, then for every horizon `T`
`Σ_{t<T} βᵗ E₀ log C_t ≤ Σ_{t<T} βᵗ E₀ log C°_t + βᵀ/(1 − β)`. The rival's utility need not
converge. -/
theorem utility_le_ref_add {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt) {β W₀ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hW : 0 < W₀) {x : List S → ℝ}
    (hπ : ∀ l s, 0 < portRet R Rt (x l) s) {c kr ks : List S → ℝ}
    (hf : Feasible R Rt W₀ c kr ks)
    (hnode : ∀ s h, NodeCond p R Rt (x (s :: h)) (kr (s :: h)) (ks (s :: h))) (s₀ : S)
    (T : ℕ) :
    utility p β c s₀ T ≤ utility p β (refCons R Rt β W₀ x) s₀ T + 1 / (1 - β) * β ^ T := by
  set P := iidKernel p
  have hM : IsMarkov P := iidKernel_isMarkov hr
  have h1β : 0 < 1 - β := by linarith
  set Z := relWealth R Rt β W₀ x kr ks
  have hC : ∀ s h, 0 < refCons R Rt β W₀ x (s :: h) := fun s h =>
    mul_pos h1β (refWealth_pos hβ0 hW hπ (s :: h) (List.cons_ne_nil _ _))
  -- `Z ≥ 0` at every non-root node, and `Z = 1/(1 − β)` at the root
  have hZnn : ∀ s' s h, 0 ≤ Z (s' :: s :: h) := fun s' s h =>
    div_nonneg ((hf s h).2.2 s') (hC s' (s :: h)).le
  -- the node inequality
  have hnodeZ : ∀ s h, β * nextExp P Z (s :: h) ≤
      (kr (s :: h) + ks (s :: h)) / refCons R Rt β W₀ x (s :: h) := by
    intro s h
    have hw := refWealth_pos hβ0 hW hπ (s :: h) (List.cons_ne_nil _ _)
    have e : β * nextExp P Z (s :: h) = (∑ s', p s' * ((Rt s' * kr (s :: h) + R * ks (s :: h)) /
        portRet R Rt (x (s :: h)) s')) / refCons R Rt β W₀ x (s :: h) := by
      simp only [nextExp, P, iidKernel, Z, relWealth, wealth, refCons, refWealth]
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun s' _ => ?_
      have := (hπ (s :: h) s').ne'
      have := hw.ne'
      have := hβ0.ne'
      have := h1β.ne'
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (hnode s h) (hC s h).le
  set q : List S → ℝ := fun l => Z l - 1 / (1 - β)
  set r : List S → ℝ := fun l => nextExp P Z l - 1 / (1 - β)
  have key := telescope_bound (β := β) (c := 1 / (1 - β))
    (d := fun t => ev P (fun l => Real.log (c l) - Real.log (refCons R Rt β W₀ x l)) t s₀ [])
    (q := fun t => ev P q t s₀ []) (r := fun t => ev P r t s₀ []) hβ0.le (by positivity)
    (fun t => by
      rw [← ev_const_mul, ← ev_sub]
      refine ev_mono hM (fun s h => ?_) t s₀ []
      obtain ⟨hc, hbud, -⟩ := hf s h
      have hCs := hC s h
      have l1 := Real.log_le_sub_one_of_pos (div_pos hc hCs)
      rw [Real.log_div hc.ne' hCs.ne'] at l1
      have hZ : Z (s :: h) = wealth R Rt W₀ kr ks (s :: h) / refCons R Rt β W₀ x (s :: h) := rfl
      have e2 : c (s :: h) / refCons R Rt β W₀ x (s :: h) - 1 = Z (s :: h) - 1 -
          (kr (s :: h) + ks (s :: h)) / refCons R Rt β W₀ x (s :: h) := by
        rw [hZ, ← hbud]; field_simp; ring
      have := hnodeZ s h
      simp only [q, r]
      have e3 : (1 : ℝ) / (1 - β) - 1 - β * (1 / (1 - β)) = 0 := by field_simp; ring
      nlinarith)
    (fun t => by
      simp only [q, r]
      rw [ev_sub, ev_sub, ev_const hM, ev_const hM, ev_nextExp])
    (by
      simp only [q, ev, Z, relWealth, wealth, refCons, refWealth]
      field_simp
      ring_nf
      exact le_refl _)
    (fun t => by
      simp only [r]
      have := ev_mono hM (f := fun _ => -(1 / (1 - β)))
        (g := fun l => nextExp P Z l - 1 / (1 - β)) (fun s h => by
          have : 0 ≤ nextExp P Z (s :: h) := Finset.sum_nonneg fun s' _ =>
            mul_nonneg (hM.nonneg s s') (hZnn s' s h)
          linarith) t s₀ []
      rwa [ev_const hM] at this)
    T
  have hsum : ∑ t ∈ range T, β ^ t *
      ev P (fun l => Real.log (c l) - Real.log (refCons R Rt β W₀ x l)) t s₀ [] =
      utility p β c s₀ T - utility p β (refCons R Rt β W₀ x) s₀ T := by
    simp only [utility, ← Finset.sum_sub_distrib, ← mul_sub]
    exact Finset.sum_congr rfl fun t _ => by rw [ev_sub]
  linarith

omit [Fintype S] in
/-- Log reference wealth grows at most linearly along the tree (constant portfolio share):
`|log W°| ≤ |log W₀| + depth · L` with `L = |log β| + Σ_s |log π(s)|`. -/
theorem abs_log_refWealth_le [Fintype S] {R : ℝ} {Rt : S → ℝ} {β W₀ xv : ℝ} (hβ : 0 < β)
    (hW : 0 < W₀) (hπ : ∀ s, 0 < portRet R Rt xv s) (h : List S) (s : S) :
    |Real.log (refWealth R Rt β W₀ (fun _ => xv) (s :: h))| ≤
      |Real.log W₀| + h.length * (|Real.log β| + ∑ s, |Real.log (portRet R Rt xv s)|) := by
  induction h generalizing s with
  | nil => simp [refWealth]
  | cons s₁ h ih =>
    have hw := refWealth_pos (x := fun _ => xv) hβ hW (fun _ s => hπ s) (s₁ :: h)
      (List.cons_ne_nil _ _)
    simp only [refWealth, List.length_cons]
    rw [Real.log_mul (mul_pos hβ (hπ s)).ne' hw.ne', Real.log_mul hβ.ne' (hπ s).ne']
    have hs := Finset.single_le_sum (f := fun s => |Real.log (portRet R Rt xv s)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
    have := ih s₁
    calc _ ≤ |Real.log β| + |Real.log (portRet R Rt xv s)| +
          |Real.log (refWealth R Rt β W₀ (fun _ => xv) (s₁ :: h))| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by push_cast; nlinarith

/-- **The Kelly plan's expected utility is finite** (a genuine convergent series), for a constant
share with positive portfolio returns. -/
theorem summable_ref {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt) {β W₀ xv : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hW : 0 < W₀) (hπ : ∀ s, 0 < portRet R Rt xv s) (s₀ : S) :
    Summable (fun t => β ^ t *
      ev (iidKernel p) (fun l => Real.log (refCons R Rt β W₀ (fun _ => xv) l)) t s₀ []) := by
  have hM := iidKernel_isMarkov hr
  set L := |Real.log β| + ∑ s, |Real.log (portRet R Rt xv s)|
  set A := |Real.log (1 - β)| + |Real.log W₀|
  have hL : 0 ≤ L := add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hnode : ∀ s h, |Real.log (refCons R Rt β W₀ (fun _ => xv) (s :: h))| ≤
      A + ((s :: h).length : ℝ) * L := by
    intro s h
    have hw := refWealth_pos (x := fun _ => xv) hβ0 hW (fun _ s => hπ s) (s :: h)
      (List.cons_ne_nil _ _)
    simp only [refCons]
    rw [Real.log_mul (by linarith) hw.ne']
    have := abs_log_refWealth_le hβ0 hW hπ h s
    have : (h.length : ℝ) * L ≤ ((s :: h).length : ℝ) * L := by
      simp only [List.length_cons]; push_cast; nlinarith
    calc _ ≤ |Real.log (1 - β)| + |Real.log (refWealth R Rt β W₀ (fun _ => xv) (s :: h))| :=
          abs_add_le _ _
      _ ≤ _ := by simp only [A]; linarith
  have hbd : ∀ t, |ev (iidKernel p) (fun l => Real.log (refCons R Rt β W₀ (fun _ => xv) l))
      t s₀ []| ≤ A + ((t : ℝ) + 1) * L := by
    intro t
    have h1 := ev_mono hM (f := fun l => Real.log (refCons R Rt β W₀ (fun _ => xv) l))
      (g := fun l => A + (l.length : ℝ) * L) (fun s h => (abs_le.1 (hnode s h)).2) t s₀ []
    have h2 := ev_mono hM (g := fun l => Real.log (refCons R Rt β W₀ (fun _ => xv) l))
      (f := fun l => -(A + (l.length : ℝ) * L)) (fun s h => (abs_le.1 (hnode s h)).1) t s₀ []
    rw [ev_length hM (fun n => A + (n : ℝ) * L)] at h1
    rw [ev_length hM (fun n => -(A + (n : ℝ) * L))] at h2
    simp only [List.length_nil, add_zero, Nat.cast_add, Nat.cast_one] at h1 h2
    exact abs_le.2 ⟨by linarith, h1⟩
  have hg1 := (summable_geometric_of_lt_one hβ0.le hβ1).mul_left (A + L)
  have hg2 := (summable_pow_mul_geometric_of_norm_lt_one 1
    (show ‖β‖ < 1 by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1)).mul_left L
  refine Summable.of_norm_bounded (hg1.add hg2) fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 t)]
  calc β ^ t * |_| ≤ β ^ t * (A + ((t : ℝ) + 1) * L) :=
        mul_le_mul_of_nonneg_left (hbd t) (pow_pos hβ0 t).le
    _ = (A + L) * β ^ t + L * ((t : ℝ) ^ 1 * β ^ t) := by ring

/-- From the partial-sum bound and summability of the reference plan: eventual domination and
comparison of sums (used for every optimality statement below). -/
theorem optimal_of_bound {Uc Ur : ℕ → ℝ} {V β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hb : ∀ T, Uc T ≤ Ur T + 1 / (1 - β) * β ^ T) (hr : Tendsto Ur atTop (𝓝 V)) :
    ∀ ε > 0, ∀ᶠ T in atTop, Uc T ≤ V + ε := by
  intro ε hε
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul (1 / (1 - β))
  rw [mul_zero] at h2
  have h3 := hr.add h2
  rw [add_zero] at h3
  filter_upwards [h3.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))] with T hT
  linarith [hb T]

/-- **Infinite-horizon optimality of the constrained Kelly plan** (O&R (73), (76), exact; no short
sales of physical capital, so `x ≤ 1`, which the book ignores). Let `x*` satisfy the KKT
conditions on `[0, 1]`. For every feasible plan with non-negative risky and riskless capital and
every `ε > 0`, eventually `Σ_{t<T} βᵗ E₀ log C_t ≤ U* + ε`, where `U*` is the (finite) utility of
`C = (1 − β)W`, risky share `x*`; if the rival's utility converges, it is at most `U*`. -/
theorem kelly_plan_optimal {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt) {β W₀ x : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hW : 0 < W₀) (hk : IsKKT p R Rt x)
    {c kr ks : List S → ℝ} (hf : Feasible R Rt W₀ c kr ks)
    (hnn : ∀ s h, 0 ≤ kr (s :: h) ∧ 0 ≤ ks (s :: h)) (s₀ : S) :
    (∀ ε > 0, ∀ᶠ T in atTop, utility p β c s₀ T ≤
      ∑' t, β ^ t * ev (iidKernel p) (fun l => Real.log (refCons R Rt β W₀ (fun _ => x) l))
        t s₀ [] + ε) ∧
    (Summable (fun t => β ^ t * ev (iidKernel p) (fun l => Real.log (c l)) t s₀ []) →
      ∑' t, β ^ t * ev (iidKernel p) (fun l => Real.log (c l)) t s₀ [] ≤
        ∑' t, β ^ t * ev (iidKernel p) (fun l => Real.log (refCons R Rt β W₀ (fun _ => x) l))
          t s₀ []) := by
  have hπ := portRet_pos hr hk.1 hk.2.1
  have hb := utility_le_ref_add hr hβ0 hβ1 hW (x := fun _ => x) (fun _ s => hπ s) hf
    (fun s h => nodeCond_kkt hr hk (hnn s h).1 (hnn s h).2) s₀
  have hlim := (summable_ref hr hβ0 hβ1 hW hπ s₀).hasSum.tendsto_sum_nat
  have hev := optimal_of_bound hβ0 hβ1 hb hlim
  refine ⟨hev, fun hs => le_of_forall_pos_le_add fun ε hε => ?_⟩
  exact le_of_tendsto hs.hasSum.tendsto_sum_nat (hev ε hε)

/-- **Infinite-horizon optimality of the unconstrained Kelly plan** (the book's setting, where
riskless holdings may be negative): if `D(x*) = 0` with positive portfolio returns, the plan
`C = (1 − β)W`, share `x*`, beats every feasible plan (any signs, wealth non-negative). -/
theorem kelly_plan_optimal_unconstrained {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt)
    {β W₀ x : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hW : 0 < W₀) (hπ : ∀ s, 0 < portRet R Rt x s)
    (hfoc : focD p R Rt x = 0) {c kr ks : List S → ℝ} (hf : Feasible R Rt W₀ c kr ks)
    (s₀ : S) :
    (∀ ε > 0, ∀ᶠ T in atTop, utility p β c s₀ T ≤
      ∑' t, β ^ t * ev (iidKernel p) (fun l => Real.log (refCons R Rt β W₀ (fun _ => x) l))
        t s₀ [] + ε) ∧
    (Summable (fun t => β ^ t * ev (iidKernel p) (fun l => Real.log (c l)) t s₀ []) →
      ∑' t, β ^ t * ev (iidKernel p) (fun l => Real.log (c l)) t s₀ [] ≤
        ∑' t, β ^ t * ev (iidKernel p) (fun l => Real.log (refCons R Rt β W₀ (fun _ => x) l))
          t s₀ []) := by
  have hb := utility_le_ref_add hr hβ0 hβ1 hW (x := fun _ => x) (fun _ s => hπ s) hf
    (fun s h => nodeCond_foc hr hπ hfoc _ _) s₀
  have hlim := (summable_ref hr hβ0 hβ1 hW hπ s₀).hasSum.tendsto_sum_nat
  have hev := optimal_of_bound hβ0 hβ1 hb hlim
  refine ⟨hev, fun hs => le_of_forall_pos_le_add fun ε hε => ?_⟩
  exact le_of_tendsto hs.hasSum.tendsto_sum_nat (hev ε hε)

/-- **(73) holds for any portfolio rule** (O&R p. 479): for a fixed (possibly history-dependent)
portfolio rule `x`, consuming `(1 − β)W` beats every other consumption plan that follows the
same portfolio rule, on partial sums up to `βᵀ/(1 − β)`. -/
theorem consumption_rule_optimal {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt)
    {β W₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hW : 0 < W₀) {x : List S → ℝ}
    (hπ : ∀ l s, 0 < portRet R Rt (x l) s) {c kr ks : List S → ℝ}
    (hf : Feasible R Rt W₀ c kr ks)
    (hsame : ∀ s h, kr (s :: h) = x (s :: h) * (kr (s :: h) + ks (s :: h)) ∧
      ks (s :: h) = (1 - x (s :: h)) * (kr (s :: h) + ks (s :: h))) (s₀ : S) (T : ℕ) :
    utility p β c s₀ T ≤ utility p β (refCons R Rt β W₀ x) s₀ T + 1 / (1 - β) * β ^ T := by
  refine utility_le_ref_add hr hβ0 hβ1 hW hπ hf (fun s h => ?_) s₀ T
  have := nodeCond_same_portfolio hr (sv := kr (s :: h) + ks (s :: h)) (hπ (s :: h))
  rwa [← (hsame s h).1, ← (hsame s h).2] at this

omit [Fintype S] in
/-- **(75), exactly**: along the reference plan, realised consumption growth is
`C_{t+1}/C_t = β[1 + r + x(r̃_{t+1} − r)]`. -/
theorem consumption_growth_ref {R : ℝ} {Rt : S → ℝ} {β W₀ : ℝ} {x : List S → ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hW : 0 < W₀) (hπ : ∀ l s, 0 < portRet R Rt (x l) s) (s' s : S)
    (h : List S) :
    refCons R Rt β W₀ x (s' :: s :: h) / refCons R Rt β W₀ x (s :: h) =
      β * (R + x (s :: h) * (Rt s' - R)) := by
  have hw := refWealth_pos hβ0 hW hπ (s :: h) (List.cons_ne_nil _ _)
  simp only [refCons, refWealth, portRet]
  have := (sub_pos.2 hβ1).ne'
  field_simp

/-- **(77), exactly**: expected consumption growth is `E_t[C_{t+1}/C_t] = β[R + x E(R̃ − R)]`,
increasing in the risky share `x` when `E R̃ > R`. -/
theorem expected_growth_ref {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt) {β W₀ : ℝ}
    {x : List S → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hW : 0 < W₀)
    (hπ : ∀ l s, 0 < portRet R Rt (x l) s) (s : S) (h : List S) :
    ∑ s', p s' * (refCons R Rt β W₀ x (s' :: s :: h) / refCons R Rt β W₀ x (s :: h)) =
      β * (R + x (s :: h) * (∑ s', p s' * Rt s' - R)) := by
  simp only [consumption_growth_ref hβ0 hβ1 hW hπ]
  have : ∀ s', p s' * (β * (R + x (s :: h) * (Rt s' - R))) =
      β * R * p s' + β * x (s :: h) * (p s' * Rt s') - β * x (s :: h) * R * p s' :=
    fun s' => by ring
  rw [Finset.sum_congr rfl fun s' _ => this s', Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hr.p_sum]
  ring

/-! ## International diversification raises the risky share and growth (§7.3.2.3) -/

/-- A positive expected excess return rules out degenerate risk. -/
theorem nondegenerate_of_mean {p : S → ℝ} {R : ℝ} {Rt : S → ℝ} (hr : Returns p R Rt)
    (hmean : R < ∑ s, p s * Rt s) : Nondegenerate p R Rt := by
  by_contra h
  unfold Nondegenerate at h
  push Not at h
  have : ∑ s, p s * Rt s = ∑ s, p s * R := Finset.sum_congr rfl fun s _ => by
    rcases eq_or_lt_of_le (hr.p_nonneg s) with h0 | h0
    · rw [← h0, zero_mul, zero_mul]
    · rw [h s h0]
  rw [this, ← Finset.sum_mul, hr.p_sum, one_mul] at hmean
  exact lt_irrefl _ hmean

/-- Midpoint concavity of `φ(e) = e/(R + x e)` in the excess return, exactly:
`φ((a+b)/2) − (φ(a) + φ(b))/2 = R x (a − b)²/(2uv(u + v))` with `u = R + xa`, `v = R + xb`. -/
theorem midpoint_gap {R x a b : ℝ} (hu : 0 < R + x * a) (hv : 0 < R + x * b) :
    (a + b) / 2 / (R + x * ((a + b) / 2)) - (a / (R + x * a) + b / (R + x * b)) / 2 =
      R * x * (a - b) ^ 2 / (2 * (R + x * a) * (R + x * b) * ((R + x * a) + (R + x * b))) := by
  have h3 : 0 < R + x * ((a + b) / 2) := by nlinarith
  have hA : 2 * (R + x * ((a + b) / 2)) ≠ 0 := by positivity
  have hB : R + x * a ≠ 0 := hu.ne'
  have hC : R + x * b ≠ 0 := hv.ne'
  have hD : (R + x * a) * (R + x * b) * 2 ≠ 0 := by positivity
  have hE : 2 * (R + x * a) * (R + x * b) * ((R + x * a) + (R + x * b)) ≠ 0 := by positivity
  rw [div_div, div_add_div _ _ hB hC, div_div, div_sub_div _ _ hA hD, div_eq_div_iff
    (mul_ne_zero hA hD) hE]
  ring

/-- Symmetric two-country return structure: a pmf `q` on a finite state space with an
involution `σ` (swap the countries) preserving `q` and exchanging the two countries' risky gross
returns `r1`, `r2` (O&R p. 480: "the same preferences and technologies"). -/
structure Symmetric {T : Type*} [Fintype T] (q : T → ℝ) (r1 r2 : T → ℝ) (σ : T → T) : Prop where
  invol : Function.Involutive σ
  q_swap : ∀ t, q (σ t) = q t
  r_swap : ∀ t, r1 (σ t) = r2 t

/-- Under symmetry, expectations of any function of Home's return equal those of Foreign's. -/
theorem Symmetric.sum_swap {T : Type*} [Fintype T] {q r1 r2 : T → ℝ} {σ : T → T}
    (hs : Symmetric q r1 r2 σ) (f : ℝ → ℝ) :
    ∑ t, q t * f (r1 t) = ∑ t, q t * f (r2 t) := by
  rw [← Equiv.sum_comp hs.invol.toPerm]
  exact Finset.sum_congr rfl fun t _ => by
    simp only [Function.Involutive.coe_toPerm, hs.q_swap, hs.r_swap]

/-- The world mutual fund of risky capital, equally weighted: `r̃^W = (r̃¹ + r̃²)/2`. -/
noncomputable def worldFund {T : Type*} (r1 r2 : T → ℝ) (t : T) : ℝ := (r1 t + r2 t) / 2

/-- The world fund has the same mean return as each country (O&R p. 481). -/
theorem worldFund_mean {T : Type*} [Fintype T] {q r1 r2 : T → ℝ} {σ : T → T}
    (hs : Symmetric q r1 r2 σ) :
    ∑ t, q t * worldFund r1 r2 t = ∑ t, q t * r1 t := by
  have h := hs.sum_swap id
  simp only [id] at h
  have : ∀ t, q t * worldFund r1 r2 t = (q t * r1 t + q t * r2 t) / 2 := fun t => by
    unfold worldFund; ring
  rw [Finset.sum_congr rfl fun t _ => this t, ← Finset.sum_div, Finset.sum_add_distrib, ← h]
  ring

/-- **Diversification raises the marginal value of risk-taking**: for every share `x ∈ [0, 1]`,
`D_W(x) ≥ D_1(x)`, strictly when `x > 0` and the countries' returns differ in some state of
positive probability (Jensen + swap symmetry; exact version of the book's variance argument). -/
theorem focD_world_ge {T : Type*} [Fintype T] {q : T → ℝ} {R : ℝ} {r1 r2 : T → ℝ} {σ : T → T}
    (hr : Returns q R r1) (hr2 : ∀ t, 0 < r2 t) (hs : Symmetric q r1 r2 σ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    focD q R r1 x ≤ focD q R (worldFund r1 r2) x ∧
      (0 < x → (∃ t, 0 < q t ∧ r1 t ≠ r2 t) → focD q R r1 x < focD q R (worldFund r1 r2) x) := by
  have hr2' : Returns q R r2 := ⟨hr.p_nonneg, hr.p_sum, hr.R_pos, hr2⟩
  have hu := portRet_pos hr hx0 hx1
  have hv := portRet_pos hr2' hx0 hx1
  have hswap := hs.sum_swap (fun r => (r - R) / (R + x * (r - R)))
  have hgap : focD q R (worldFund r1 r2) x - focD q R r1 x = ∑ t, q t *
      (R * x * (r1 t - R - (r2 t - R)) ^ 2 / (2 * portRet R r1 x t * portRet R r2 x t *
        (portRet R r1 x t + portRet R r2 x t))) := by
    have e1 : focD q R r1 x = (focD q R r1 x + focD q R r2 x) / 2 := by
      have : focD q R r1 x = focD q R r2 x := hswap
      rw [← this]; ring
    rw [e1]
    unfold focD
    rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hg := midpoint_gap (R := R) (x := x) (a := r1 t - R) (b := r2 t - R) (hu t) (hv t)
    have hw : worldFund r1 r2 t - R = (r1 t - R + (r2 t - R)) / 2 := by unfold worldFund; ring
    simp only [portRet] at hg ⊢
    rw [hw, ← hg]
    ring
  have hnn : ∀ t, 0 ≤ q t * (R * x * (r1 t - R - (r2 t - R)) ^ 2 / (2 * portRet R r1 x t *
      portRet R r2 x t * (portRet R r1 x t + portRet R r2 x t))) := fun t =>
    mul_nonneg (hr.p_nonneg t) (div_nonneg (mul_nonneg (mul_nonneg hr.R_pos.le hx0)
      (sq_nonneg _)) (by have := hu t; have := hv t; positivity))
  refine ⟨by linarith [Finset.sum_nonneg fun t (_ : t ∈ Finset.univ) => hnn t], ?_⟩
  rintro hxpos ⟨t₀, hq0, hne⟩
  have hpos : 0 < q t₀ * (R * x * (r1 t₀ - R - (r2 t₀ - R)) ^ 2 / (2 * portRet R r1 x t₀ *
      portRet R r2 x t₀ * (portRet R r1 x t₀ + portRet R r2 x t₀))) := by
    have : 0 < (r1 t₀ - R - (r2 t₀ - R)) ^ 2 := by
      have : r1 t₀ - R - (r2 t₀ - R) ≠ 0 := by intro h; exact hne (by linarith)
      positivity
    have := hu t₀; have := hv t₀; have := hr.R_pos
    exact mul_pos hq0 (by positivity)
  have := Finset.sum_lt_sum (s := Finset.univ) (fun t _ => hnn t) ⟨t₀, Finset.mem_univ _, hpos⟩
  simp only [Finset.sum_const_zero] at this
  linarith

/-- The world fund's gross returns are positive. -/
theorem worldFund_returns {T : Type*} [Fintype T] {q : T → ℝ} {R : ℝ} {r1 r2 : T → ℝ}
    (hr : Returns q R r1) (hr2 : ∀ t, 0 < r2 t) : Returns q R (worldFund r1 r2) :=
  ⟨hr.p_nonneg, hr.p_sum, hr.R_pos, fun t => by
    unfold worldFund; have := hr.Rt_pos t; have := hr2 t; positivity⟩

/-- **Diversification raises the optimal risky share** (the exact version of (76) vs (78)):
with symmetric countries and `E r̃ > r`, the optimal share in the world fund is at least the
autarky share, `x*_W ≥ x*_n`; strictly if the autarky share is below the constraint `x ≤ 1`
and the countries' returns are not perfectly correlated (differ in some state). -/
theorem diversification_raises_share {T : Type*} [Fintype T] {q : T → ℝ} {R : ℝ}
    {r1 r2 : T → ℝ} {σ : T → T} (hr : Returns q R r1) (hr2 : ∀ t, 0 < r2 t)
    (hs : Symmetric q r1 r2 σ) (hmean : R < ∑ t, q t * r1 t) {x1 xW : ℝ}
    (h1 : IsKKT q R r1 x1) (hW : IsKKT q R (worldFund r1 r2) xW) :
    x1 ≤ xW ∧ (x1 < 1 → (∃ t, 0 < q t ∧ r1 t ≠ r2 t) → x1 < xW) := by
  have hrW := worldFund_returns hr hr2
  have hmeanW : R < ∑ t, q t * worldFund r1 r2 t := by rw [worldFund_mean hs]; exact hmean
  have hndW := nondegenerate_of_mean hrW hmeanW
  have hnd1 := nondegenerate_of_mean hr hmean
  have hx1pos : 0 < x1 := (kkt_pos_iff hr hnd1 h1).2 hmean
  constructor
  · by_contra hlt
    push Not at hlt
    have hA := h1.2.2.1 hx1pos
    have hB := (focD_world_ge hr hr2 hs h1.1 h1.2.1).1
    have hC := hW.2.2.2 (lt_of_lt_of_le hlt h1.2.1)
    have hD := (focD_anti hrW.p_nonneg (portRet_pos hrW hW.1 hW.2.1) (portRet_pos hrW h1.1 h1.2.1)
      hlt).2 hndW
    linarith
  · intro hlt1 hdiff
    have hA := h1.2.2.1 hx1pos
    have hA' := h1.2.2.2 hlt1
    have hB := (focD_world_ge hr hr2 hs h1.1 h1.2.1).2 hx1pos hdiff
    by_contra hle
    push Not at hle
    have hC := hW.2.2.2 (lt_of_le_of_lt hle hlt1)
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq] at hC; linarith
    · have hD := (focD_anti hrW.p_nonneg (portRet_pos hrW hW.1 hW.2.1) (portRet_pos hrW h1.1 h1.2.1)
        hlt).1
      linarith

/-- **Diversification raises expected growth** (O&R (77) vs (78), exact): with symmetric
countries and `E r̃ > r`, expected consumption growth `β[R + x* E(R̃ − R)]` under integration is at
least that under autarky, strictly under the conditions of `diversification_raises_share`. -/
theorem diversification_raises_growth {T : Type*} [Fintype T] {q : T → ℝ} {R β : ℝ}
    {r1 r2 : T → ℝ} {σ : T → T} (hβ : 0 < β) (hr : Returns q R r1) (hr2 : ∀ t, 0 < r2 t)
    (hs : Symmetric q r1 r2 σ) (hmean : R < ∑ t, q t * r1 t) {x1 xW : ℝ}
    (h1 : IsKKT q R r1 x1) (hW : IsKKT q R (worldFund r1 r2) xW) :
    β * (R + x1 * (∑ t, q t * r1 t - R)) ≤
        β * (R + xW * (∑ t, q t * worldFund r1 r2 t - R)) ∧
      (x1 < 1 → (∃ t, 0 < q t ∧ r1 t ≠ r2 t) →
        β * (R + x1 * (∑ t, q t * r1 t - R)) <
          β * (R + xW * (∑ t, q t * worldFund r1 r2 t - R))) := by
  obtain ⟨hle, hlt⟩ := diversification_raises_share hr hr2 hs hmean h1 hW
  rw [worldFund_mean hs]
  have he : 0 < ∑ t, q t * r1 t - R := by linarith
  refine ⟨?_, fun a b => ?_⟩
  · have := mul_le_mul_of_nonneg_right hle he.le
    nlinarith
  · have := mul_lt_mul_of_pos_right (hlt a b) he
    nlinarith

/-! ## The variance of the world mutual fund (corrected) -/

/-- Mean of a random variable on a finite probability space. -/
noncomputable def mean {T : Type*} [Fintype T] (q X : T → ℝ) : ℝ := ∑ t, q t * X t

/-- Variance of a random variable on a finite probability space. -/
noncomputable def var {T : Type*} [Fintype T] (q X : T → ℝ) : ℝ :=
  ∑ t, q t * (X t - mean q X) ^ 2

/-- **Diversification bound**: the variance of a portfolio of country funds with weights
`w_i ≥ 0`, `Σ w_i = 1`, is at most the weighted average of the country variances. -/
theorem var_portfolio_le {T ι : Type*} [Fintype T] [Fintype ι] {q : T → ℝ}
    (hq0 : ∀ t, 0 ≤ q t) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (X : ι → T → ℝ) :
    var q (fun t => ∑ i, w i * X i t) ≤ ∑ i, w i * var q (X i) := by
  have hmean : mean q (fun t => ∑ i, w i * X i t) = ∑ i, w i * mean q (X i) := by
    unfold mean
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => by ring
  have hjensen : ∀ t, (∑ i, w i * X i t - ∑ i, w i * mean q (X i)) ^ 2 ≤
      ∑ i, w i * (X i t - mean q (X i)) ^ 2 := by
    intro t
    set d : ι → ℝ := fun i => X i t - mean q (X i)
    have hd : ∑ i, w i * X i t - ∑ i, w i * mean q (X i) = ∑ i, w i * d i := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hd]
    set m := ∑ i, w i * d i
    have h0 : 0 ≤ ∑ i, w i * (d i - m) ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (sq_nonneg _)
    have e : ∑ i, w i * (d i - m) ^ 2 = ∑ i, w i * d i ^ 2 - 2 * m * m + m ^ 2 * ∑ i, w i := by
      have : ∀ i, w i * (d i - m) ^ 2 = w i * d i ^ 2 - 2 * m * (w i * d i) + m ^ 2 * w i :=
        fun i => by ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rfl
    rw [hw1] at e
    nlinarith
  unfold var
  rw [hmean]
  calc ∑ t, q t * (∑ i, w i * X i t - ∑ i, w i * mean q (X i)) ^ 2
      ≤ ∑ t, q t * ∑ i, w i * (X i t - mean q (X i)) ^ 2 :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hjensen t) (hq0 t)
    _ = ∑ i, w i * ∑ t, q t * (X i t - mean q (X i)) ^ 2 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => by ring

/-- **The corrected world-fund variance claim** (O&R p. 481): if all countries' returns have the
same variance `v` (the book's symmetry), the world fund's variance is at most `v`. -/
theorem var_world_le_of_equal {T ι : Type*} [Fintype T] [Fintype ι] {q : T → ℝ}
    (hq0 : ∀ t, 0 ≤ q t) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (X : ι → T → ℝ) {v : ℝ} (hv : ∀ i, var q (X i) = v) :
    var q (fun t => ∑ i, w i * X i t) ≤ v := by
  have := var_portfolio_le hq0 hw0 hw1 X
  simp only [hv, ← Finset.sum_mul, hw1, one_mul] at this
  exact this

/-- Two countries, exactly: `Var((X + Y)/2) = (Var X + Var Y)/2 − E[(X − EX) − (Y − EY)]²/4`, so
with equal variances `v`, `Var r̃^W = v − E[(dX − dY)²]/4`, which is **strictly** below `v`
unless the two returns move one-for-one in every state of positive probability. -/
theorem var_two_country {T : Type*} [Fintype T] (q : T → ℝ) (X Y : T → ℝ) :
    var q (fun t => (X t + Y t) / 2) = (var q X + var q Y) / 2 -
      (∑ t, q t * ((X t - mean q X) - (Y t - mean q Y)) ^ 2) / 4 := by
  have hm : mean q (fun t => (X t + Y t) / 2) = (mean q X + mean q Y) / 2 := by
    unfold mean
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun t _ => by beta_reduce; ring
  simp only [var, hm, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- **Counterexample to the book's "`Var(r̃^W) < Var(r̃^n)` for every `n`"** without equal
variances: two independent countries with return deviations `±1/10` and `±1` (variances `1/100`
and `1`, all four states equally likely) give `Var r̃^W = 101/400 > 1/100`. -/
theorem var_world_counterexample :
    let q : Fin 2 × Fin 2 → ℝ := fun _ => 1 / 4
    let X : Fin 2 × Fin 2 → ℝ := fun t => if t.1 = 0 then 1 / 10 else -(1 / 10)
    let Y : Fin 2 × Fin 2 → ℝ := fun t => if t.2 = 0 then 1 else -1
    var q X = 1 / 100 ∧ var q Y = 1 ∧ var q (fun t => (X t + Y t) / 2) = 101 / 400 ∧
      var q X < var q (fun t => (X t + Y t) / 2) := by
  intro q X Y
  have h1 : var q X = 1 / 100 := by
    norm_num [var, mean, q, X, Fintype.sum_prod_type, Fin.sum_univ_two]
  have h2 : var q Y = 1 := by
    norm_num [var, mean, q, Y, Fintype.sum_prod_type, Fin.sum_univ_two]
  have h3 : var q (fun t => (X t + Y t) / 2) = 101 / 400 := by
    norm_num [var, mean, q, X, Y, Fintype.sum_prod_type, Fin.sum_univ_two]
  refine ⟨h1, h2, h3, ?_⟩
  rw [h1, h3]; norm_num

/-! ## The book's approximations (74)–(78) as algebra -/

/-- Covariance on a finite probability space. -/
noncomputable def cov {T : Type*} [Fintype T] (q X Y : T → ℝ) : ℝ :=
  ∑ t, q t * (X t - mean q X) * (Y t - mean q Y)

/-- **(75)–(77) given (74)**: if the linearised Euler condition (74)
`E(r̃ − r) = (1 + r) β Cov(C′/C − 1, r̃ − r)` holds with consumption growth (75)
`C′/C − 1 = β[R + x e] − 1` (`e = r̃ − r`), then `x = E e/(β² R Var e)` (76) and
`E[C′/C] = (E e)²/(β R Var e) + βR` (77); (78) is the same statement for the world fund. These are
exact consequences of the *approximation* (74) (see `kelly_exact` for the exact share). -/
theorem approx_share_growth {T : Type*} [Fintype T] {q : T → ℝ} (hq1 : ∑ t, q t = 1)
    {R β x : ℝ} (hR : 0 < R) (hβ : 0 < β) (e : T → ℝ) (hvar : var q e ≠ 0)
    (h74 : mean q e = R * β * cov q (fun t => β * (R + x * e t) - 1) e) :
    x = mean q e / (β ^ 2 * R * var q e) ∧
      mean q (fun t => β * (R + x * e t)) = mean q e ^ 2 / (β * R * var q e) + β * R := by
  have hcov : cov q (fun t => β * (R + x * e t) - 1) e = β * x * var q e := by
    have hm : mean q (fun t => β * (R + x * e t) - 1) = β * (R + x * mean q e) - 1 := by
      unfold mean
      rw [show β * (R + x * ∑ t, q t * e t) - 1 =
        ∑ t, q t * (β * (R + x * e t) - 1) by
        have : ∀ t, q t * (β * (R + x * e t) - 1) = (β * R - 1) * q t + β * x * (q t * e t) :=
          fun t => by ring
        rw [Finset.sum_congr rfl fun t _ => this t, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, hq1]
        ring]
    unfold cov var
    rw [hm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hmean : mean q (fun t => β * (R + x * e t)) = β * (R + x * mean q e) := by
    unfold mean
    have : ∀ t, q t * (β * (R + x * e t)) = β * R * q t + β * x * (q t * e t) :=
      fun t => by ring
    rw [Finset.sum_congr rfl fun t _ => this t, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hq1]
    ring
  rw [hcov] at h74
  have hx : x = mean q e / (β ^ 2 * R * var q e) := by
    rw [eq_div_iff (by positivity)]; linarith
  refine ⟨hx, ?_⟩
  rw [hmean, hx]
  field_simp
  ring

end ObstfeldRogoff.GlobalGrowth.PortfolioGrowth
