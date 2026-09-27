import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.IntermediateValue
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The two-period overlapping generations endowment economy

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§3.2.1, pp. 133–135. Each generation lives for two periods, has utility
`log c^Y_t + β log c^O_{t+1}` (O&R (3.9)), and faces the world rate `r`.
With lifetime wealth `W = y^Y − τ^Y + (y^O − τ^O)/(1 + r)` (O&R (3.10)), the
consumption demands are `c^Y = W/(1 + β)` and `c^O = (1 + r) β W/(1 + β)`
(O&R (3.12)–(3.13)).
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy

/-- A small open two-period OLG economy with log utility and world rate `r > -1`. -/
structure LogOLG where
  β : ℝ
  r : ℝ
  β_pos : 0 < β
  one_add_r_pos : 0 < 1 + r

namespace LogOLG

/-- Consumption of the young out of lifetime wealth `W` (O&R (3.12)). -/
noncomputable def youngC (m : LogOLG) (W : ℝ) : ℝ := W / (1 + m.β)

/-- Consumption of the old out of lifetime wealth `W` (O&R (3.13)). -/
noncomputable def oldC (m : LogOLG) (W : ℝ) : ℝ := (1 + m.r) * m.β * W / (1 + m.β)

/-- The demands exhaust lifetime wealth: `c^Y + c^O/(1 + r) = W` (O&R (3.10)). -/
theorem budget (m : LogOLG) (W : ℝ) : m.youngC W + m.oldC W / (1 + m.r) = W := by
  have hr := m.one_add_r_pos.ne'
  have hb : 1 + m.β ≠ 0 := by linarith [m.β_pos]
  unfold youngC oldC
  field_simp

/-- The demands satisfy the Euler equation `c^O_{t+1} = (1 + r) β c^Y_t` (O&R (3.11)). -/
theorem euler (m : LogOLG) (W : ℝ) : m.oldC W = (1 + m.r) * m.β * m.youngC W := by
  unfold youngC oldC
  ring

end LogOLG

end ObstfeldRogoff.LifeCycleFiscalPolicy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Ricardian equivalence and intergenerational altruism

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§3.1, pp. 130–133, and §3.7.1, pp. 174–178.

**§3.1.** With lump-sum taxes, a constant interest rate and a single
representative taxpayer, only the present value of taxes enters the private
budget constraint once the government's constraint is imposed. In the two-period
model, substituting (3.2) into (3.1) removes taxes (`two_period_merged_constraint`),
so any two tax paths with equal present value give the same budget set and the
same optimum for any preferences (`two_period_budgetSet_eq_of_pv_eq`,
`two_period_optimum_invariant`). A retiming of taxes moves private saving by
exactly minus the change in government saving, at both dates, leaving national
saving unchanged (`retiming_saving_date_one`, `retiming_saving_date_two`).
In the infinite horizon the private and government intertemporal budget
constraints (3.4), (3.6) follow from the flow identities (3.3), (3.5) and a
transversality condition (`private_ibc_of_flow`, `government_ibc_of_flow`), and
with (3.7) they merge into (3.8) (`merged_ibc`). The private budget set in present
value form depends neither on the tax path nor on the split of national assets
between private sector and government (`privatePVSet_eq_of_government_ibc`).

**§3.7.1.** Barro's dynasty: `U_t = u(C_t) + β U_{t+1}` (3.56), budget
`(1 + r) H_t + Y_t − T_t = C_t + H_{t+1}` (3.57), bequests `H_{t+1} ≥ 0` (3.58).
We prove the dynasty budget constraint (3.59) under footnote 38's condition
(`dynasty_ibc`), the iterated form of (3.56) and its limit
(`utility_iterate`, `tendsto_utility_remainder`, `utility_eq_tsum_iff`), and
footnote 39's point (Gale 1983) that (3.56) does not pin down `U`: all
solutions differ by `K β^{-t}` (`gale_shift_solution`, `gale_solutions_differ`),
and the miser utility of footnote 39 solves (3.56) with
`β^{s-t} U_s → μ lim β^{s-t} H_{s+1}` (`miser_recursion`, `miser_limit`).
Finally, a bond-financed transfer `τ` to the current old leaves the dynasty's
present-value budget set unchanged (`dynastyPVSet_transfer`) and is offset
one-for-one by the bequest (`bequestPath_transfer_one`); with interior bequests
the optimum is unchanged (`interior_bequest_neutrality`), while if the bequest
constraint binds the transfer strictly enlarges the feasible set
(`binding_bequest_feasible_ssubset`).
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence

open Filter Topology Finset

/-! ### Optimality for an arbitrary preference relation -/

/-- `p` is optimal in the choice set `S` for the preference relation `R`, where `R q p` reads
"`p` is weakly preferred to `q`" (for a utility `U`, take `R q p := U q ≤ U p`). Used for the
"same optimal choices for any preferences" claims of O&R §3.1, p. 130. -/
def IsOptimal {α : Type*} (S : Set α) (R : α → α → Prop) (p : α) : Prop :=
  p ∈ S ∧ ∀ q ∈ S, R q p

/-! ### The two-period model, O&R (3.1)–(3.2), pp. 130–131 -/

/-- A two-period private plan `(C₁, I₁, C₂, I₂)`, O&R (3.1), p. 130. -/
structure TwoPeriodPlan where
  C1 : ℝ
  I1 : ℝ
  C2 : ℝ
  I2 : ℝ

/-- The private budget set of O&R (3.1), p. 130 (zero initial assets):
`C₁ + I₁ + (C₂ + I₂)/(1 + r) ≤ Y₁ − T₁ + (Y₂ − T₂)/(1 + r)`. -/
def twoPeriodBudgetSet (r Y1 Y2 T1 T2 : ℝ) : Set TwoPeriodPlan :=
  {p | p.C1 + p.I1 + (p.C2 + p.I2) / (1 + r) ≤ Y1 - T1 + (Y2 - T2) / (1 + r)}

/-- **Taxes drop out**, O&R p. 130: substituting the government constraint (3.2)
`G₁ + G₂/(1 + r) = T₁ + T₂/(1 + r)` into the private constraint (3.1) gives
`C₁ + I₁ + (C₂ + I₂)/(1 + r) = Y₁ − G₁ + (Y₂ − G₂)/(1 + r)`. -/
theorem two_period_merged_constraint {r Y1 Y2 T1 T2 G1 G2 C1 I1 C2 I2 : ℝ}
    (hP : C1 + I1 + (C2 + I2) / (1 + r) = Y1 - T1 + (Y2 - T2) / (1 + r))
    (hG : G1 + G2 / (1 + r) = T1 + T2 / (1 + r)) :
    C1 + I1 + (C2 + I2) / (1 + r) = Y1 - G1 + (Y2 - G2) / (1 + r) := by
  rw [hP, sub_div, sub_div]
  linarith

/-- **Timing neutrality of lump-sum taxes**, O&R p. 130: two tax paths with the same present
value give the same private budget set (3.1). -/
theorem two_period_budgetSet_eq_of_pv_eq {r Y1 Y2 T1 T2 T1' T2' : ℝ}
    (h : T1 + T2 / (1 + r) = T1' + T2' / (1 + r)) :
    twoPeriodBudgetSet r Y1 Y2 T1 T2 = twoPeriodBudgetSet r Y1 Y2 T1' T2' := by
  have key : Y1 - T1 + (Y2 - T2) / (1 + r) = Y1 - T1' + (Y2 - T2') / (1 + r) := by
    rw [sub_div, sub_div]
    linarith
  ext p
  simp only [twoPeriodBudgetSet, Set.mem_ofPred_eq, key]

/-- **The budget set depends only on government spending**, O&R p. 130: under (3.2) the private
budget set (3.1) equals the set `C₁ + I₁ + (C₂ + I₂)/(1 + r) ≤ Y₁ − G₁ + (Y₂ − G₂)/(1 + r)`,
the constraint (1.15) of Chapter 1. -/
theorem two_period_budgetSet_eq_government {r Y1 Y2 T1 T2 G1 G2 : ℝ}
    (hG : G1 + G2 / (1 + r) = T1 + T2 / (1 + r)) :
    twoPeriodBudgetSet r Y1 Y2 T1 T2 =
      {p | p.C1 + p.I1 + (p.C2 + p.I2) / (1 + r) ≤ Y1 - G1 + (Y2 - G2) / (1 + r)} := by
  have key : Y1 - T1 + (Y2 - T2) / (1 + r) = Y1 - G1 + (Y2 - G2) / (1 + r) := by
    rw [sub_div, sub_div]
    linarith
  ext p
  simp only [twoPeriodBudgetSet, Set.mem_ofPred_eq, key]

/-- **Same optimal choices for any preferences**, O&R p. 130: if two tax paths have the same
present value, a plan is optimal under one iff it is optimal under the other, for an arbitrary
preference relation `R`. -/
theorem two_period_optimum_invariant {r Y1 Y2 T1 T2 T1' T2' : ℝ}
    (R : TwoPeriodPlan → TwoPeriodPlan → Prop) (p : TwoPeriodPlan)
    (h : T1 + T2 / (1 + r) = T1' + T2' / (1 + r)) :
    IsOptimal (twoPeriodBudgetSet r Y1 Y2 T1 T2) R p ↔
      IsOptimal (twoPeriodBudgetSet r Y1 Y2 T1' T2') R p := by
  rw [two_period_budgetSet_eq_of_pv_eq h]

/-- **A retiming preserves present value**, O&R p. 131: cutting date-1 taxes by `dT` and raising
date-2 taxes by `(1 + r) dT` leaves `T₁ + T₂/(1 + r)` unchanged (for `1 + r ≠ 0`). -/
theorem retiming_pv_eq {r T1 T2 dT : ℝ} (hr : 1 + r ≠ 0) :
    (T1 - dT) + (T2 + (1 + r) * dT) / (1 + r) = T1 + T2 / (1 + r) := by
  field_simp
  ring

/-- Private saving `S^P = Y − T − C`, O&R p. 131. -/
def privateSaving (Y T C : ℝ) : ℝ := Y - T - C

/-- Government saving `S^G = T − G` (the budget surplus), O&R p. 131. -/
def governmentSaving (T G : ℝ) : ℝ := T - G

/-- **Private saving offsets government saving at date 1**, O&R p. 131: with consumption
unchanged (as it is, by `two_period_optimum_invariant`), a date-1 tax cut `dT` raises private
saving by `dT`, lowers government saving by `dT`, and leaves national saving
`S^P + S^G = Y − C − G` unchanged. -/
theorem retiming_saving_date_one (Y T C G dT : ℝ) :
    privateSaving Y (T - dT) C - privateSaving Y T C =
        -(governmentSaving (T - dT) G - governmentSaving T G) ∧
      privateSaving Y (T - dT) C + governmentSaving (T - dT) G = Y - C - G ∧
      privateSaving Y T C + governmentSaving T G = Y - C - G := by
  simp only [privateSaving, governmentSaving]
  refine ⟨by ring, by ring, by ring⟩

/-- **Private saving offsets government saving at date 2**, O&R p. 131: with zero initial
assets, date-2 saving includes interest on date-1 saving,
`S^P₂ = Y₂ + r S^P₁ − T₂ − C₂` and `S^G₂ = T₂ + r S^G₁ − G₂`. After the retiming
`(T₁, T₂) ↦ (T₁ − dT, T₂ + (1 + r) dT)` with consumption unchanged, private date-2 saving
falls by `dT` and government date-2 saving rises by `dT`. -/
theorem retiming_saving_date_two (r Y1 Y2 T1 T2 C1 C2 G1 G2 dT : ℝ) :
    (Y2 + r * privateSaving Y1 (T1 - dT) C1 - (T2 + (1 + r) * dT) - C2) -
        (Y2 + r * privateSaving Y1 T1 C1 - T2 - C2) = -dT ∧
      ((T2 + (1 + r) * dT) + r * governmentSaving (T1 - dT) G1 - G2) -
        (T2 + r * governmentSaving T1 G1 - G2) = dT := by
  simp only [privateSaving, governmentSaving]
  exact ⟨by ring, by ring⟩

/-! ### Infinite horizon, O&R (3.3)–(3.8), pp. 132–133 -/

/-- The one-period discount factor `1/(1 + r)`, O&R (3.4), p. 132. -/
noncomputable def ricDisc (r : ℝ) : ℝ := (1 + r)⁻¹

/-- `(1 + r) · 1/(1 + r) = 1`. -/
theorem one_add_mul_ricDisc {r : ℝ} (hr : 1 + r ≠ 0) : (1 + r) * ricDisc r = 1 :=
  mul_inv_cancel₀ hr

/-- **Discounted telescoping** (copied, with `1 + r ≠ 0` in place of `0 < 1 + r`, from
`ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue.discounted_telescope`; O&R (2.4), p. 61):
if `A_{s+1} = (1 + r) A_s + N_s` then `(1 + r)^{-n} A_n = A_0 + Σ_{s<n} (1 + r)^{-(s+1)} N_s`. -/
theorem ric_discounted_telescope {r : ℝ} (hr : 1 + r ≠ 0) {A N : ℕ → ℝ}
    (h : ∀ s, A (s + 1) = (1 + r) * A s + N s) (n : ℕ) :
    ricDisc r ^ n * A n = A 0 + ∑ s ∈ range n, ricDisc r ^ (s + 1) * N s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← add_assoc, ← ih, h n, pow_succ]
    have := one_add_mul_ricDisc hr
    linear_combination ricDisc r ^ n * A n * this

/-- **Transversality ⇔ intertemporal budget constraint**, the argument behind O&R (3.4) and
(3.6), p. 132 (Chapter 2's (2.13) ⇔ (2.14)): for `A_{s+1} = (1 + r) A_s + N_s` with summable
discounted `N`, `(1 + r)^{-n} A_n → 0` iff `(1 + r) A_0 + Σ_s (1 + r)^{-s} N_s = 0`. -/
theorem ric_transversality_iff_ibc {r : ℝ} (hr : 1 + r ≠ 0) {A N : ℕ → ℝ}
    (h : ∀ s, A (s + 1) = (1 + r) * A s + N s)
    (hs : Summable fun s => ricDisc r ^ s * N s) :
    Tendsto (fun n => ricDisc r ^ n * A n) atTop (𝓝 0) ↔
      (1 + r) * A 0 + ∑' s, ricDisc r ^ s * N s = 0 := by
  have hfun : (fun s => ricDisc r ^ (s + 1) * N s) = fun s => ricDisc r * (ricDisc r ^ s * N s) :=
    funext fun s => by ring
  have hsum : Summable fun s => ricDisc r ^ (s + 1) * N s := by
    rw [hfun]
    exact hs.mul_left _
  have ht : Tendsto (fun n => ricDisc r ^ n * A n) atTop
      (𝓝 (A 0 + ∑' s, ricDisc r ^ (s + 1) * N s)) := by
    simp_rw [ric_discounted_telescope hr h]
    exact tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat
  rw [hfun, tsum_mul_left] at ht
  have e : (1 + r) * (A 0 + ricDisc r * ∑' s, ricDisc r ^ s * N s) =
      (1 + r) * A 0 + ∑' s, ricDisc r ^ s * N s := by
    rw [mul_add, ← mul_assoc, one_add_mul_ricDisc hr, one_mul]
  rw [← e]
  constructor
  · intro h0
    rw [tendsto_nhds_unique ht h0, mul_zero]
  · intro h0
    have h1 : A 0 + ricDisc r * ∑' s, ricDisc r ^ s * N s = 0 :=
      (mul_eq_zero.mp h0).resolve_left hr
    rwa [h1] at ht

/-- **Private intertemporal budget constraint**, O&R (3.4), p. 132, derived from the flow
identity (3.3) `B^P_{s+1} − B^P_s = Y_s + r B^P_s − T_s − C_s − I_s` and the transversality
condition `(1 + r)^{-n} B^P_n → 0`:
`Σ (1 + r)^{-s} (C_s + I_s) = (1 + r) B^P_0 + Σ (1 + r)^{-s} (Y_s − T_s)`. -/
theorem private_ibc_of_flow {r : ℝ} (hr : 1 + r ≠ 0) {BP Y T C I : ℕ → ℝ}
    (hflow : ∀ s, BP (s + 1) - BP s = Y s + r * BP s - T s - C s - I s)
    (htv : Tendsto (fun n => ricDisc r ^ n * BP n) atTop (𝓝 0))
    (hCI : Summable fun s => ricDisc r ^ s * (C s + I s))
    (hYT : Summable fun s => ricDisc r ^ s * (Y s - T s)) :
    ∑' s, ricDisc r ^ s * (C s + I s) =
      (1 + r) * BP 0 + ∑' s, ricDisc r ^ s * (Y s - T s) := by
  have h' : ∀ s, BP (s + 1) = (1 + r) * BP s + (Y s - T s - (C s + I s)) := fun s => by
    linarith [hflow s]
  have hfun : (fun s => ricDisc r ^ s * (Y s - T s - (C s + I s))) =
      fun s => ricDisc r ^ s * (Y s - T s) - ricDisc r ^ s * (C s + I s) :=
    funext fun s => by ring
  have hs : Summable fun s => ricDisc r ^ s * (Y s - T s - (C s + I s)) := by
    rw [hfun]
    exact hYT.sub hCI
  have := (ric_transversality_iff_ibc hr h' hs).mp htv
  rw [hfun, hYT.tsum_sub hCI] at this
  linarith

/-- **Government intertemporal budget constraint**, O&R (3.6), p. 132, derived from the flow
identity (3.5) `B^G_{s+1} − B^G_s = T_s + r B^G_s − G_s` and `(1 + r)^{-n} B^G_n → 0`:
`Σ (1 + r)^{-s} G_s = (1 + r) B^G_0 + Σ (1 + r)^{-s} T_s`. -/
theorem government_ibc_of_flow {r : ℝ} (hr : 1 + r ≠ 0) {BG T G : ℕ → ℝ}
    (hflow : ∀ s, BG (s + 1) - BG s = T s + r * BG s - G s)
    (htv : Tendsto (fun n => ricDisc r ^ n * BG n) atTop (𝓝 0))
    (hG : Summable fun s => ricDisc r ^ s * G s)
    (hT : Summable fun s => ricDisc r ^ s * T s) :
    ∑' s, ricDisc r ^ s * G s = (1 + r) * BG 0 + ∑' s, ricDisc r ^ s * T s := by
  have h' : ∀ s, BG (s + 1) = (1 + r) * BG s + (T s - G s) := fun s => by
    linarith [hflow s]
  have hfun : (fun s => ricDisc r ^ s * (T s - G s)) =
      fun s => ricDisc r ^ s * T s - ricDisc r ^ s * G s :=
    funext fun s => by ring
  have hs : Summable fun s => ricDisc r ^ s * (T s - G s) := by
    rw [hfun]
    exact hT.sub hG
  have := (ric_transversality_iff_ibc hr h' hs).mp htv
  rw [hfun, hT.tsum_sub hG] at this
  linarith

/-- **The merged constraint**, O&R (3.8), p. 133: the private constraint (3.4), the government
constraint (3.6) and the aggregation (3.7) `B = B^P + B^G` give
`Σ (1 + r)^{-s} (C_s + I_s) = (1 + r) B_0 + Σ (1 + r)^{-s} (Y_s − G_s)`, in which neither the
tax path nor the private/public split of assets appears. -/
theorem merged_ibc {r B0 BP0 BG0 : ℝ} {Y T G C I : ℕ → ℝ}
    (hY : Summable fun s => ricDisc r ^ s * Y s)
    (hT : Summable fun s => ricDisc r ^ s * T s)
    (hG : Summable fun s => ricDisc r ^ s * G s)
    (hP : ∑' s, ricDisc r ^ s * (C s + I s) =
      (1 + r) * BP0 + ∑' s, ricDisc r ^ s * (Y s - T s))
    (hGov : ∑' s, ricDisc r ^ s * G s = (1 + r) * BG0 + ∑' s, ricDisc r ^ s * T s)
    (hB : B0 = BP0 + BG0) :
    ∑' s, ricDisc r ^ s * (C s + I s) =
      (1 + r) * B0 + ∑' s, ricDisc r ^ s * (Y s - G s) := by
  simp_rw [mul_sub] at hP ⊢
  rw [hY.tsum_sub hT] at hP
  rw [hY.tsum_sub hG, hP, hB]
  linarith

/-- The private budget set in present-value form, O&R (3.4), p. 132: plans `(C, I)` with
summable discounted spending and `Σ (1 + r)^{-s} (C_s + I_s) ≤ (1 + r) B^P_0 + Σ (1 + r)^{-s}
(Y_s − T_s)`. -/
def privatePVSet (r BP0 : ℝ) (Y T : ℕ → ℝ) : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {p | Summable (fun s => ricDisc r ^ s * (p.1 s + p.2 s)) ∧
    ∑' s, ricDisc r ^ s * (p.1 s + p.2 s) ≤
      (1 + r) * BP0 + ∑' s, ricDisc r ^ s * (Y s - T s)}

/-- **Ricardian equivalence in the infinite horizon**, O&R p. 133: if two tax paths `T`, `T'` and
two asset splits `(B^P_0, B^G_0)`, `(B^P_0', B^G_0')` with the same national total both satisfy the
government constraint (3.6) for the same spending path `G`, the private present-value budget sets
coincide. Hence neither the timing of taxes nor a transfer of assets between private sector and
government (with offsetting tax cuts) matters. -/
theorem privatePVSet_eq_of_government_ibc {r BP0 BG0 BP0' BG0' : ℝ} {Y T T' G : ℕ → ℝ}
    (hY : Summable fun s => ricDisc r ^ s * Y s)
    (hT : Summable fun s => ricDisc r ^ s * T s)
    (hT' : Summable fun s => ricDisc r ^ s * T' s)
    (hGov : ∑' s, ricDisc r ^ s * G s = (1 + r) * BG0 + ∑' s, ricDisc r ^ s * T s)
    (hGov' : ∑' s, ricDisc r ^ s * G s = (1 + r) * BG0' + ∑' s, ricDisc r ^ s * T' s)
    (hB : BP0 + BG0 = BP0' + BG0') :
    privatePVSet r BP0 Y T = privatePVSet r BP0' Y T' := by
  have key : (1 + r) * BP0 + ∑' s, ricDisc r ^ s * (Y s - T s) =
      (1 + r) * BP0' + ∑' s, ricDisc r ^ s * (Y s - T' s) := by
    simp_rw [mul_sub]
    rw [hY.tsum_sub hT, hY.tsum_sub hT']
    linear_combination (1 + r) * hB + hGov - hGov'
  ext p
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

/-- **Same optimal plans for any preferences**, O&R p. 133: under the hypotheses of
`privatePVSet_eq_of_government_ibc`, a plan is optimal under `(B^P_0, T)` iff it is optimal
under `(B^P_0', T')`. -/
theorem private_optimum_invariant {r BP0 BG0 BP0' BG0' : ℝ} {Y T T' G : ℕ → ℝ}
    (R : (ℕ → ℝ) × (ℕ → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) → Prop) (p : (ℕ → ℝ) × (ℕ → ℝ))
    (hY : Summable fun s => ricDisc r ^ s * Y s)
    (hT : Summable fun s => ricDisc r ^ s * T s)
    (hT' : Summable fun s => ricDisc r ^ s * T' s)
    (hGov : ∑' s, ricDisc r ^ s * G s = (1 + r) * BG0 + ∑' s, ricDisc r ^ s * T s)
    (hGov' : ∑' s, ricDisc r ^ s * G s = (1 + r) * BG0' + ∑' s, ricDisc r ^ s * T' s)
    (hB : BP0 + BG0 = BP0' + BG0') :
    IsOptimal (privatePVSet r BP0 Y T) R p ↔ IsOptimal (privatePVSet r BP0' Y T') R p := by
  rw [privatePVSet_eq_of_government_ibc hY hT hT' hGov hGov' hB]

/-! ### Barro's altruistic dynasty, O&R (3.56)–(3.60), pp. 175–177 -/

/-- **The dynasty's intertemporal budget constraint**, O&R (3.59), p. 176: iterating the budget
identity (3.57) `(1 + r) H_s + Y_s − T_s = C_s + H_{s+1}` under footnote 38's condition
`(1 + r)^{-s} H_{s+1} → 0` gives `Σ (1 + r)^{-s} C_s = (1 + r) H_0 + Σ (1 + r)^{-s} (Y_s − T_s)`. -/
theorem dynasty_ibc {r : ℝ} (hr : 1 + r ≠ 0) {H Y T C : ℕ → ℝ}
    (hflow : ∀ s, (1 + r) * H s + Y s - T s = C s + H (s + 1))
    (htv : Tendsto (fun s => ricDisc r ^ s * H (s + 1)) atTop (𝓝 0))
    (hC : Summable fun s => ricDisc r ^ s * C s)
    (hYT : Summable fun s => ricDisc r ^ s * (Y s - T s)) :
    ∑' s, ricDisc r ^ s * C s = (1 + r) * H 0 + ∑' s, ricDisc r ^ s * (Y s - T s) := by
  have h' : ∀ s, H (s + 1) = (1 + r) * H s + (Y s - T s - C s) := fun s => by
    linarith [hflow s]
  have h1 : Tendsto (fun n => ricDisc r ^ (n + 1) * H (n + 1)) atTop (𝓝 0) := by
    have := htv.const_mul (ricDisc r)
    rw [mul_zero] at this
    refine this.congr (fun n => ?_)
    ring
  have h2 : Tendsto (fun n => ricDisc r ^ n * H n) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat (f := fun n => ricDisc r ^ n * H n) 1).mp h1
  have hfun : (fun s => ricDisc r ^ s * (Y s - T s - C s)) =
      fun s => ricDisc r ^ s * (Y s - T s) - ricDisc r ^ s * C s :=
    funext fun s => by ring
  have hs : Summable fun s => ricDisc r ^ s * (Y s - T s - C s) := by
    rw [hfun]
    exact hYT.sub hC
  have := (ric_transversality_iff_ibc hr h' hs).mp h2
  rw [hfun, hYT.tsum_sub hC] at this
  linarith

/-- **Iterating the altruistic utility recursion**, O&R p. 176: if `U_s = u(C_s) + β U_{s+1}`
(O&R (3.56)) for all `s`, then `U_t = Σ_{k<n} β^k u(C_{t+k}) + β^n U_{t+n}`. -/
theorem utility_iterate {β : ℝ} {u : ℝ → ℝ} {C U : ℕ → ℝ}
    (hU : ∀ s, U s = u (C s) + β * U (s + 1)) (t n : ℕ) :
    U t = ∑ k ∈ range n, β ^ k * u (C (t + k)) + β ^ n * U (t + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, hU (t + n), show t + (n + 1) = t + n + 1 by omega]
    ring

/-- **The remainder of the iterated recursion**, O&R p. 176 (the display
`U_t = Σ_{s≥t} β^{s-t} u(C_s) + lim β^{s-t} U_s`): if the discounted utility stream is summable,
`β^n U_{t+n}` converges, to `U_t − Σ_k β^k u(C_{t+k})`. -/
theorem tendsto_utility_remainder {β : ℝ} {u : ℝ → ℝ} {C U : ℕ → ℝ}
    (hU : ∀ s, U s = u (C s) + β * U (s + 1)) (t : ℕ)
    (hsum : Summable fun k => β ^ k * u (C (t + k))) :
    Tendsto (fun n => β ^ n * U (t + n)) atTop
      (𝓝 (U t - ∑' k, β ^ k * u (C (t + k)))) := by
  refine (tendsto_const_nhds.sub hsum.hasSum.tendsto_sum_nat).congr (fun n => ?_)
  have := utility_iterate hU t n
  linarith

/-- **(3.56) gives (3.60) iff the limit term vanishes**, O&R p. 176: with a summable discounted
utility stream, `U_t = Σ_k β^k u(C_{t+k})` iff `β^n U_{t+n} → 0`. -/
theorem utility_eq_tsum_iff {β : ℝ} {u : ℝ → ℝ} {C U : ℕ → ℝ}
    (hU : ∀ s, U s = u (C s) + β * U (s + 1)) (t : ℕ)
    (hsum : Summable fun k => β ^ k * u (C (t + k))) :
    U t = ∑' k, β ^ k * u (C (t + k)) ↔ Tendsto (fun n => β ^ n * U (t + n)) atTop (𝓝 0) := by
  have ht := tendsto_utility_remainder hU t hsum
  constructor
  · intro h
    rwa [h, sub_self] at ht
  · intro h
    have := tendsto_nhds_unique ht h
    linarith

/-- **Gale's indeterminacy**, O&R footnote 39, p. 176: the recursion (3.56) does not pin down
`U`. If `U` solves `U_t = u(C_t) + β U_{t+1}` and `β ≠ 0`, so does `U_t + K β^{-t}` for any
constant `K`. -/
theorem gale_shift_solution {β : ℝ} (hβ : β ≠ 0) {u : ℝ → ℝ} {C U : ℕ → ℝ}
    (hU : ∀ s, U s = u (C s) + β * U (s + 1)) (K : ℝ) (t : ℕ) :
    U t + K * β⁻¹ ^ t = u (C t) + β * (U (t + 1) + K * β⁻¹ ^ (t + 1)) := by
  have h : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ
  rw [hU t]
  linear_combination (-(K * β⁻¹ ^ t)) * h

/-- **All solutions of (3.56)**, O&R footnote 39, p. 176: any two solutions of
`U_t = u(C_t) + β U_{t+1}` (with `β ≠ 0`) differ by `K β^{-t}`, with `K = V_0 − U_0`. So the
shifts of `gale_shift_solution` are the whole solution set. -/
theorem gale_solutions_differ {β : ℝ} (hβ : β ≠ 0) {u : ℝ → ℝ} {C U V : ℕ → ℝ}
    (hU : ∀ s, U s = u (C s) + β * U (s + 1)) (hV : ∀ s, V s = u (C s) + β * V (s + 1))
    (t : ℕ) : V t - U t = (V 0 - U 0) * β⁻¹ ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h : V (t + 1) - U (t + 1) = β⁻¹ * (V t - U t) := by
      rw [hV t, hU t]
      field_simp
      ring
    rw [h, ih, pow_succ]
    ring

/-- **The shifted solution violates the limit condition**, O&R footnote 39, p. 176: if
`β^n U_n → 0` then `β^n (U_n + K β^{-n}) → K`. -/
theorem gale_shift_limit {β : ℝ} (hβ : β ≠ 0) {U : ℕ → ℝ}
    (hU0 : Tendsto (fun n => β ^ n * U n) atTop (𝓝 0)) (K : ℝ) :
    Tendsto (fun n => β ^ n * (U n + K * β⁻¹ ^ n)) atTop (𝓝 K) := by
  have e : ∀ n : ℕ, β ^ n * (U n + K * β⁻¹ ^ n) = β ^ n * U n + K := by
    intro n
    rw [mul_add, show β ^ n * (K * β⁻¹ ^ n) = K * (β * β⁻¹) ^ n by ring,
      mul_inv_cancel₀ hβ, one_pow, mul_one]
  simp_rw [e]
  simpa using hU0.add_const K

/-- **(3.56) does not imply (3.60)**, O&R footnote 39, p. 176: if `U` solves (3.56) with
`β^n U_n → 0` and a summable utility stream, then `U_0 = Σ β^k u(C_k)`, but the equally valid
solution `U_t + K β^{-t}` with `K ≠ 0` does not equal the discounted sum at date 0. -/
theorem gale_shift_ne_tsum {β : ℝ} (hβ : β ≠ 0) {u : ℝ → ℝ} {C U : ℕ → ℝ}
    (hU : ∀ s, U s = u (C s) + β * U (s + 1))
    (hU0 : Tendsto (fun n => β ^ n * U n) atTop (𝓝 0))
    (hsum : Summable fun k => β ^ k * u (C k)) {K : ℝ} (hK : K ≠ 0) :
    U 0 = ∑' k, β ^ k * u (C k) ∧ U 0 + K * β⁻¹ ^ 0 ≠ ∑' k, β ^ k * u (C k) := by
  have hsum0 : Summable fun k => β ^ k * u (C (0 + k)) := by simpa using hsum
  have iffU := utility_eq_tsum_iff hU 0 hsum0
  have hV : ∀ s, U s + K * β⁻¹ ^ s = u (C s) + β * (U (s + 1) + K * β⁻¹ ^ (s + 1)) :=
    gale_shift_solution hβ hU K
  have iffV := utility_eq_tsum_iff (U := fun s => U s + K * β⁻¹ ^ s) hV 0 hsum0
  simp only [zero_add] at iffU iffV
  refine ⟨iffU.mpr hU0, fun h => hK ?_⟩
  exact tendsto_nhds_unique (gale_shift_limit hβ hU0 K) (iffV.mp h)

/-- **The miser's utility**, O&R footnote 39, p. 176:
`U_t = Σ_{s≥t} β^{s-t} u(C_s) + μ lim_{s→∞} β^{s-t} H_{s+1}`. For `β ≠ 0` the limit equals
`β^{-t} lim_s β^s H_{s+1}`, which is how it is written here (the limit is `limUnder`, and is the
genuine limit whenever it exists, see `miser_limit`). -/
noncomputable def miserUtility (β μ : ℝ) (u : ℝ → ℝ) (C H : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑' k, β ^ k * u (C (t + k)) + μ * (β⁻¹ ^ t * limUnder atTop (fun s => β ^ s * H (s + 1)))

/-- **The miser's utility solves (3.56)**, O&R footnote 39, pp. 176–177: for `β ≠ 0` and a
summable discounted utility stream, `U_t = u(C_t) + β U_{t+1}` for the miser utility, whatever
the bequest path `H` and weight `μ`. -/
theorem miser_recursion {β μ : ℝ} (hβ : β ≠ 0) {u : ℝ → ℝ} {C H : ℕ → ℝ}
    (hsum : Summable fun k => β ^ k * u (C k)) (t : ℕ) :
    miserUtility β μ u C H t = u (C t) + β * miserUtility β μ u C H (t + 1) := by
  have hs : ∀ t, Summable fun k => β ^ k * u (C (t + k)) := by
    intro t
    have h1 := ((summable_nat_add_iff (f := fun k => β ^ k * u (C k)) t).mpr hsum).mul_left
      (β⁻¹ ^ t)
    refine h1.congr (fun k => ?_)
    rw [add_comm k t, pow_add, show β⁻¹ ^ t * (β ^ t * β ^ k * u (C (t + k))) =
      (β⁻¹ * β) ^ t * (β ^ k * u (C (t + k))) by ring, inv_mul_cancel₀ hβ, one_pow, one_mul]
  have key : ∑' k, β ^ k * u (C (t + k)) =
      u (C t) + β * ∑' k, β ^ k * u (C (t + 1 + k)) := by
    rw [(hs t).tsum_eq_zero_add, ← tsum_mul_left]
    simp only [pow_zero, one_mul, add_zero]
    congr 1
    refine tsum_congr (fun k => ?_)
    rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
    ring
  have h : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ
  unfold miserUtility
  rw [key]
  linear_combination
    (-(μ * β⁻¹ ^ t * limUnder atTop (fun s => β ^ s * H (s + 1)))) * h

/-- **The miser's limit term**, O&R footnote 39, p. 177: if `β^s H_{s+1} → L` then
`β^n U_n → μ L` for the miser utility. So when `μ L ≠ 0` the limit condition behind (3.60)
fails although (3.56) holds (`miser_recursion`). -/
theorem miser_limit {β μ L : ℝ} (hβ : β ≠ 0) {u : ℝ → ℝ} {C H : ℕ → ℝ}
    (hL : Tendsto (fun s => β ^ s * H (s + 1)) atTop (𝓝 L)) :
    Tendsto (fun n => β ^ n * miserUtility β μ u C H n) atTop (𝓝 (μ * L)) := by
  have hlim := hL.limUnder_eq
  have e : ∀ n, β ^ n * miserUtility β μ u C H n =
      ∑' k, β ^ (k + n) * u (C (k + n)) + μ * L := by
    intro n
    unfold miserUtility
    rw [hlim, mul_add, ← tsum_mul_left]
    congr 1
    · refine tsum_congr (fun k => ?_)
      rw [add_comm k n, pow_add]
      ring
    · rw [show β ^ n * (μ * (β⁻¹ ^ n * L)) = μ * L * (β * β⁻¹) ^ n by ring,
        mul_inv_cancel₀ hβ, one_pow, mul_one]
  have h0 := (tendsto_sum_nat_add (fun m => β ^ m * u (C m))).add_const (μ * L)
  rw [zero_add] at h0
  exact h0.congr (fun n => (e n).symm)

/-- **The miser does not value the discounted consumption sum**, O&R footnote 39, p. 177: with a
summable utility stream, `β^s H_{s+1} → L` and `μ L ≠ 0`, the miser utility (which solves
(3.56)) is not `Σ β^k u(C_k)` at date 0. -/
theorem miser_ne_tsum {β μ L : ℝ} (hβ : β ≠ 0) {u : ℝ → ℝ} {C H : ℕ → ℝ}
    (hsum : Summable fun k => β ^ k * u (C k))
    (hL : Tendsto (fun s => β ^ s * H (s + 1)) atTop (𝓝 L)) (hμL : μ * L ≠ 0) :
    miserUtility β μ u C H 0 ≠ ∑' k, β ^ k * u (C k) := by
  have hsum0 : Summable fun k => β ^ k * u (C (0 + k)) := by simpa using hsum
  have iff := utility_eq_tsum_iff (fun s => miser_recursion (μ := μ) (H := H) hβ hsum s) 0 hsum0
  simp only [zero_add] at iff
  intro h
  exact hμL (tendsto_nhds_unique (miser_limit hβ hL) (iff.mp h))

/-! ### Bond-financed transfers and bequests, O&R pp. 176–178 -/

/-- The bequest path implied by the dynasty budget identity (3.57), p. 175, given the initial
bequest `H_0`, income, taxes and consumption: `H_{s+1} = (1 + r) H_s + Y_s − T_s − C_s`. -/
def bequestPath (r H0 : ℝ) (Y T C : ℕ → ℝ) : ℕ → ℝ
  | 0 => H0
  | s + 1 => (1 + r) * bequestPath r H0 Y T C s + Y s - T s - C s

/-- The bequest path satisfies the budget identity O&R (3.57), p. 175. -/
theorem bequestPath_flow (r H0 : ℝ) (Y T C : ℕ → ℝ) (s : ℕ) :
    (1 + r) * bequestPath r H0 Y T C s + Y s - T s =
      C s + bequestPath r H0 Y T C (s + 1) := by
  simp only [bequestPath]
  ring

/-- Given consumption, the bequest path is pinned down by (3.57), O&R p. 175: any `H` with
`H_0 = H0` satisfying (3.57) is `bequestPath`. -/
theorem eq_bequestPath {r H0 : ℝ} {Y T C H : ℕ → ℝ} (h0 : H 0 = H0)
    (hflow : ∀ s, (1 + r) * H s + Y s - T s = C s + H (s + 1)) (s : ℕ) :
    H s = bequestPath r H0 Y T C s := by
  induction s with
  | zero => exact h0
  | succ s ih =>
    simp only [bequestPath]
    rw [← ih]
    linarith [hflow s]

/-- A **bond-financed transfer** `τ` to the current (date-0) generation, repaid with interest by
taxes on the next generation, O&R p. 177: taxes become `T_0 − τ`, `T_1 + (1 + r) τ`, and are
unchanged afterwards. -/
def transferTax (r τ : ℝ) (T : ℕ → ℝ) : ℕ → ℝ
  | 0 => T 0 - τ
  | 1 => T 1 + (1 + r) * τ
  | s + 2 => T (s + 2)

/-- **Bequests offset the transfer one-for-one**, O&R p. 177: for an unchanged consumption plan,
the transfer raises the date-0 generation's bequest `H_1` by exactly `τ`. -/
theorem bequestPath_transfer_one (r τ H0 : ℝ) (Y T C : ℕ → ℝ) :
    bequestPath r H0 Y (transferTax r τ T) C 1 = bequestPath r H0 Y T C 1 + τ := by
  simp only [bequestPath, transferTax]
  ring

/-- **Later bequests are unchanged**, O&R p. 177: for an unchanged consumption plan, the
transfer leaves `H_{s+2}` unchanged for every `s` (the bigger bequest exactly pays the next
generation's extra tax). -/
theorem bequestPath_transfer_of_two_le (r τ H0 : ℝ) (Y T C : ℕ → ℝ) (s : ℕ) :
    bequestPath r H0 Y (transferTax r τ T) C (s + 1 + 1) = bequestPath r H0 Y T C (s + 1 + 1) := by
  induction s with
  | zero =>
    simp only [bequestPath, transferTax]
    ring
  | succ n ih =>
    change (1 + r) * bequestPath r H0 Y (transferTax r τ T) C (n + 1 + 1) + Y (n + 2) -
        transferTax r τ T (n + 2) - C (n + 2) =
      (1 + r) * bequestPath r H0 Y T C (n + 1 + 1) + Y (n + 2) - T (n + 2) - C (n + 2)
    rw [ih]
    rfl

/-- The dynasty budget set in present-value form, O&R (3.59), p. 176 (no bequest constraint):
consumption paths with summable discounted value and
`Σ (1 + r)^{-s} C_s ≤ (1 + r) H_0 + Σ (1 + r)^{-s} (Y_s − T_s)`. -/
def dynastyPVSet (r H0 : ℝ) (Y T : ℕ → ℝ) : Set (ℕ → ℝ) :=
  {C | Summable (fun s => ricDisc r ^ s * C s) ∧
    ∑' s, ricDisc r ^ s * C s ≤ (1 + r) * H0 + ∑' s, ricDisc r ^ s * (Y s - T s)}

/-- The dynasty's feasible set with the bequest constraint, O&R (3.57)–(3.58), p. 175, and
footnote 38's condition: consumption paths with summable discounted value whose implied bequests
satisfy `H_{s+1} ≥ 0` and `(1 + r)^{-s} H_{s+1} → 0`. -/
def dynastyFeasible (r H0 : ℝ) (Y T : ℕ → ℝ) : Set (ℕ → ℝ) :=
  {C | Summable (fun s => ricDisc r ^ s * C s) ∧ (∀ s, 0 ≤ bequestPath r H0 Y T C (s + 1)) ∧
    Tendsto (fun s => ricDisc r ^ s * bequestPath r H0 Y T C (s + 1)) atTop (𝓝 0)}

/-- **The transfer leaves the present value of disposable income unchanged**, O&R p. 177:
`Σ (1 + r)^{-s} (Y_s − T'_s) = Σ (1 + r)^{-s} (Y_s − T_s)` for the transfer taxes `T'`, and the
new series is summable. -/
theorem hasSum_transferTax {r τ : ℝ} (hr : 1 + r ≠ 0) {Y T : ℕ → ℝ}
    (hYT : Summable fun s => ricDisc r ^ s * (Y s - T s)) :
    HasSum (fun s => ricDisc r ^ s * (Y s - transferTax r τ T s))
      (∑' s, ricDisc r ^ s * (Y s - T s)) := by
  have hg : HasSum (fun s => ricDisc r ^ s * (Y s - transferTax r τ T s) -
      ricDisc r ^ s * (Y s - T s))
      (∑ b ∈ range 2, (ricDisc r ^ b * (Y b - transferTax r τ T b) -
        ricDisc r ^ b * (Y b - T b))) := by
    refine hasSum_sum_of_ne_finset_zero (fun b hb => ?_)
    rw [mem_range, not_lt] at hb
    obtain ⟨m, rfl⟩ : ∃ m, b = m + 2 := ⟨b - 2, by omega⟩
    change ricDisc r ^ (m + 2) * (Y (m + 2) - T (m + 2)) -
      ricDisc r ^ (m + 2) * (Y (m + 2) - T (m + 2)) = 0
    ring
  have h2 : ∑ b ∈ range 2, (ricDisc r ^ b * (Y b - transferTax r τ T b) -
      ricDisc r ^ b * (Y b - T b)) = 0 := by
    rw [sum_range_succ, sum_range_one]
    change ricDisc r ^ 0 * (Y 0 - (T 0 - τ)) - ricDisc r ^ 0 * (Y 0 - T 0) +
      (ricDisc r ^ 1 * (Y 1 - (T 1 + (1 + r) * τ)) - ricDisc r ^ 1 * (Y 1 - T 1)) = 0
    linear_combination (-τ) * one_add_mul_ricDisc hr
  rw [h2] at hg
  convert hYT.hasSum.add hg using 1
  · funext s
    ring
  · rw [add_zero]

/-- **Neutrality of a bond-financed transfer for the dynasty's budget**, O&R p. 177: the
present-value budget set (3.59) is the same before and after the transfer, so "the dynasty's
budget constraint (59) is not altered". -/
theorem dynastyPVSet_transfer {r τ H0 : ℝ} (hr : 1 + r ≠ 0) {Y T : ℕ → ℝ}
    (hYT : Summable fun s => ricDisc r ^ s * (Y s - T s)) :
    dynastyPVSet r H0 Y (transferTax r τ T) = dynastyPVSet r H0 Y T := by
  have h := (hasSum_transferTax (τ := τ) hr hYT).tsum_eq
  ext C
  simp only [dynastyPVSet, Set.mem_ofPred_eq, h]

/-- **Bequest-constrained plans are budget-feasible**, O&R (3.59), p. 176: every plan in the
feasible set with the bequest constraint satisfies the present-value budget constraint (with
equality, by `dynasty_ibc`). -/
theorem dynastyFeasible_subset_pv {r H0 : ℝ} (hr : 1 + r ≠ 0) {Y T : ℕ → ℝ}
    (hYT : Summable fun s => ricDisc r ^ s * (Y s - T s)) :
    dynastyFeasible r H0 Y T ⊆ dynastyPVSet r H0 Y T := by
  rintro C ⟨hC, -, htv⟩
  refine ⟨hC, le_of_eq ?_⟩
  have := dynasty_ibc hr (bequestPath_flow r H0 Y T C) htv hC hYT
  rwa [show bequestPath r H0 Y T C 0 = H0 from rfl] at this

/-- The transfer changes the implied bequests only at date 1, O&R p. 177: the transfer-case
tail condition holds iff the original one does. -/
theorem tendsto_bequest_transfer_iff (r τ H0 : ℝ) (Y T C : ℕ → ℝ) :
    Tendsto (fun s => ricDisc r ^ s * bequestPath r H0 Y (transferTax r τ T) C (s + 1))
        atTop (𝓝 0) ↔
      Tendsto (fun s => ricDisc r ^ s * bequestPath r H0 Y T C (s + 1)) atTop (𝓝 0) := by
  have hev : (fun s => ricDisc r ^ s * bequestPath r H0 Y (transferTax r τ T) C (s + 1)) =ᶠ[atTop]
      (fun s => ricDisc r ^ s * bequestPath r H0 Y T C (s + 1)) := by
    filter_upwards [eventually_ge_atTop 1] with s hs
    obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
    rw [bequestPath_transfer_of_two_le]
  exact tendsto_congr' hev

/-- **Small transfers keep plans feasible**, O&R p. 177: if a plan is feasible before the
transfer and `−H_1 ≤ τ` (automatic for a transfer `τ ≥ 0` to the old; for `τ < 0` it says the
transfer is small relative to the bequest), the same consumption plan stays feasible after it, the
bequest `H_1` absorbing the transfer. -/
theorem feasible_transfer_of_small {r τ H0 : ℝ} {Y T C : ℕ → ℝ}
    (hC : C ∈ dynastyFeasible r H0 Y T) (hτ : -bequestPath r H0 Y T C 1 ≤ τ) :
    C ∈ dynastyFeasible r H0 Y (transferTax r τ T) := by
  obtain ⟨hs, hnn, htv⟩ := hC
  refine ⟨hs, fun s => ?_, (tendsto_bequest_transfer_iff r τ H0 Y T C).mpr htv⟩
  cases s with
  | zero =>
    rw [bequestPath_transfer_one]
    linarith
  | succ m =>
    rw [bequestPath_transfer_of_two_le]
    exact hnn (m + 1)

/-- **A transfer to the old never shrinks the feasible set**, O&R p. 177: for `τ ≥ 0`, every plan
feasible under the old taxes is feasible under the transfer taxes. -/
theorem transfer_to_old_feasible_subset {r τ H0 : ℝ} (hτ : 0 ≤ τ) {Y T : ℕ → ℝ} :
    dynastyFeasible r H0 Y T ⊆ dynastyFeasible r H0 Y (transferTax r τ T) := by
  intro C hC
  exact feasible_transfer_of_small hC (by linarith [hC.2.1 0])

/-- **Undoing the transfer**, O&R p. 177: a plan feasible after the transfer whose date-1 bequest
covers the transfer, `τ ≤ H'_1`, was already feasible before it. -/
theorem feasible_of_transfer_feasible {r τ H0 : ℝ} {Y T C : ℕ → ℝ}
    (hC : C ∈ dynastyFeasible r H0 Y (transferTax r τ T))
    (hτ : τ ≤ bequestPath r H0 Y (transferTax r τ T) C 1) :
    C ∈ dynastyFeasible r H0 Y T := by
  obtain ⟨hs, hnn, htv⟩ := hC
  refine ⟨hs, fun s => ?_, (tendsto_bequest_transfer_iff r τ H0 Y T C).mp htv⟩
  cases s with
  | zero =>
    rw [bequestPath_transfer_one] at hτ
    linarith
  | succ m =>
    rw [← bequestPath_transfer_of_two_le r τ]
    exact hnn (m + 1)

/-- **Ricardian neutrality with interior bequests**, Barro (1974), O&R p. 177: suppose the plan
`p` is optimal (for any preference relation `R`) in the dynasty's present-value budget set, and
its implied bequests are nonnegative, so the bequest constraint (3.58) does not bind at the
optimum. Then after a bond-financed transfer `τ` with `−H_1 ≤ τ`, `p` is still optimal, both with
and without the bequest constraint, and the date-0 bequest rises by exactly `τ`. -/
theorem interior_bequest_neutrality {r τ H0 : ℝ} (hr : 1 + r ≠ 0) {Y T : ℕ → ℝ}
    (hYT : Summable fun s => ricDisc r ^ s * (Y s - T s)) (R : (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    {p : ℕ → ℝ} (hopt : IsOptimal (dynastyPVSet r H0 Y T) R p)
    (hp : p ∈ dynastyFeasible r H0 Y T) (hτ : -bequestPath r H0 Y T p 1 ≤ τ) :
    IsOptimal (dynastyFeasible r H0 Y T) R p ∧
      IsOptimal (dynastyFeasible r H0 Y (transferTax r τ T)) R p ∧
      IsOptimal (dynastyPVSet r H0 Y (transferTax r τ T)) R p ∧
      bequestPath r H0 Y (transferTax r τ T) p 1 = bequestPath r H0 Y T p 1 + τ := by
  have hYT' : Summable fun s => ricDisc r ^ s * (Y s - transferTax r τ T s) :=
    (hasSum_transferTax hr hYT).summable
  have hset := dynastyPVSet_transfer (τ := τ) (H0 := H0) hr hYT
  refine ⟨⟨hp, fun q hq => hopt.2 q (dynastyFeasible_subset_pv hr hYT hq)⟩,
    ⟨feasible_transfer_of_small hp hτ, fun q hq => hopt.2 q ?_⟩,
    by rw [hset]; exact hopt, bequestPath_transfer_one r τ H0 Y T p⟩
  rw [← hset]
  exact dynastyFeasible_subset_pv hr hYT' hq

/-- The consumption plan made possible by a transfer, O&R p. 177: the date-0 generation consumes
the transfer `τ`, the date-1 generation pays the extra tax `(1 + r) τ` out of consumption. -/
def transferConsumption (r τ : ℝ) (C : ℕ → ℝ) : ℕ → ℝ
  | 0 => C 0 + τ
  | 1 => C 1 - (1 + r) * τ
  | s + 2 => C (s + 2)

/-- Under the transfer taxes, `transferConsumption` has the same bequests as the original plan
under the original taxes, O&R p. 177. -/
theorem bequestPath_transferConsumption (r τ H0 : ℝ) (Y T C : ℕ → ℝ) (s : ℕ) :
    bequestPath r H0 Y (transferTax r τ T) (transferConsumption r τ C) s =
      bequestPath r H0 Y T C s := by
  induction s with
  | zero => rfl
  | succ n ih =>
    rcases n with _ | _ | m
    · simp only [bequestPath, transferTax, transferConsumption]
      ring
    · change (1 + r) * bequestPath r H0 Y (transferTax r τ T) (transferConsumption r τ C) 1 +
          Y 1 - (T 1 + (1 + r) * τ) - (C 1 - (1 + r) * τ) =
        (1 + r) * bequestPath r H0 Y T C 1 + Y 1 - T 1 - C 1
      rw [ih]
      ring
    · change (1 + r) * bequestPath r H0 Y (transferTax r τ T) (transferConsumption r τ C) (m + 2) +
          Y (m + 2) - T (m + 2) - C (m + 2) =
        (1 + r) * bequestPath r H0 Y T C (m + 2) + Y (m + 2) - T (m + 2) - C (m + 2)
      rw [ih]

/-- **Non-neutrality when the bequest constraint binds**, O&R pp. 177–178: if a feasible plan
has date-0 bequest `H_1 < τ` (in particular a binding constraint `H_1 = 0` and any transfer
`τ > 0`), then the plan in which the old consume the transfer and the young repay it is feasible
after the transfer but not before, although it has the same present value (it lies in the
unconstrained budget set (3.59) of both tax paths). The government "passes on debt to future
generations", as the dynasty wished but could not. -/
theorem transfer_relaxes_binding_bequest {r τ H0 : ℝ} (hr : 1 + r ≠ 0) {Y T C : ℕ → ℝ}
    (hYT : Summable fun s => ricDisc r ^ s * (Y s - T s))
    (hC : C ∈ dynastyFeasible r H0 Y T) (hτ : bequestPath r H0 Y T C 1 < τ) :
    transferConsumption r τ C ∈ dynastyFeasible r H0 Y (transferTax r τ T) ∧
      transferConsumption r τ C ∉ dynastyFeasible r H0 Y T ∧
      transferConsumption r τ C ∈ dynastyPVSet r H0 Y T := by
  obtain ⟨hs, hnn, htv⟩ := hC
  have hfin : Summable fun s => ricDisc r ^ s * transferConsumption r τ C s -
      ricDisc r ^ s * C s := by
    refine summable_of_ne_finset_zero (s := range 2) (fun b hb => ?_)
    rw [mem_range, not_lt] at hb
    obtain ⟨m, rfl⟩ : ∃ m, b = m + 2 := ⟨b - 2, by omega⟩
    change ricDisc r ^ (m + 2) * C (m + 2) - ricDisc r ^ (m + 2) * C (m + 2) = 0
    ring
  have hs' : Summable fun s => ricDisc r ^ s * transferConsumption r τ C s :=
    (hs.add hfin).congr (fun s => by ring)
  have hmem : transferConsumption r τ C ∈ dynastyFeasible r H0 Y (transferTax r τ T) := by
    refine ⟨hs', fun s => ?_, ?_⟩
    · rw [bequestPath_transferConsumption]
      exact hnn s
    · simp_rw [bequestPath_transferConsumption]
      exact htv
  refine ⟨hmem, fun hbad => ?_, ?_⟩
  · have h0 := hbad.2.1 0
    have e : bequestPath r H0 Y T (transferConsumption r τ C) (0 + 1) =
        bequestPath r H0 Y T C 1 - τ := by
      simp only [bequestPath, transferConsumption]
      ring
    rw [e] at h0
    linarith
  · have hYT' : Summable fun s => ricDisc r ^ s * (Y s - transferTax r τ T s) :=
      (hasSum_transferTax hr hYT).summable
    rw [← dynastyPVSet_transfer (τ := τ) hr hYT]
    exact dynastyFeasible_subset_pv hr hYT' hmem

/-- **A binding bequest constraint makes the transfer matter**, O&R pp. 177–178: if some feasible
plan leaves a zero bequest (`H_1 = 0`, the constraint (3.58) binds) and `τ > 0`, the transfer
strictly enlarges the dynasty's feasible set. -/
theorem binding_bequest_feasible_ssubset {r τ H0 : ℝ} (hr : 1 + r ≠ 0) (hτ : 0 < τ)
    {Y T C : ℕ → ℝ} (hYT : Summable fun s => ricDisc r ^ s * (Y s - T s))
    (hC : C ∈ dynastyFeasible r H0 Y T) (hbind : bequestPath r H0 Y T C 1 = 0) :
    dynastyFeasible r H0 Y T ⊂ dynastyFeasible r H0 Y (transferTax r τ T) := by
  obtain ⟨h1, h2, -⟩ := transfer_relaxes_binding_bequest (τ := τ) hr hYT hC (by linarith)
  exact (Set.ssubset_iff_of_subset (transfer_to_old_feasible_subset hτ.le)).mpr
    ⟨_, h1, h2⟩

end ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Government deficits in a two-period overlapping generations economy

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§3.2.1–§3.2.2, pp. 133–137, and Box 3.1 (generational accounting), pp. 142–144.
Each generation lives two periods with log utility (O&R (3.9)) and faces the
world rate `r`. It pays lump-sum taxes `τ^Y` when young and `τ^O` when old, so
its lifetime wealth is `W = y^Y − τ^Y + (y^O − τ^O)/(1 + r)` (O&R (3.10)). The
consumption demands (3.12)–(3.13) are `LogOLG.youngC` and `LogOLG.oldC`.

* **Ricardian equivalence fails** (p. 136). In a steady state, aggregate
  consumption is `C = [1 + (1 + r)β]/(1 + β) · W`. After substituting the
  government's steady-state budget `G = rB^G + τ^Y + τ^O`, `C` still depends on
  the tax on the young and on government assets, not only on `G`.
* **Saving accounting** (3.17)–(3.23): the current account is private plus
  government saving; the old dissave what they saved when young; with
  `β(1 + r) = 1` the young save `β/(1 + β)` times the fall in their disposable
  income.
* **Generational accounting** (Box 3.1): cutting a generation's youth tax by one
  unit and raising its old-age tax by `1 + r` raises the measured deficit but
  leaves every generation's lifetime wealth, and hence all consumption,
  unchanged.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.TwoPeriodOLG

open LogOLG

/-- Lifetime wealth `W = y^Y − τ^Y + (y^O − τ^O)/(1 + r)` of a generation, O&R (3.10), p. 134. -/
noncomputable def lifetimeWealth (r yY yO τY τO : ℝ) : ℝ := yY - τY + (yO - τO) / (1 + r)

/-- **Steady-state aggregate consumption**, O&R p. 135: with constant endowments and taxes, the
young and old alive at any date consume `C = [1 + (1 + r)β]/(1 + β) · W`. -/
theorem aggregate_consumption_steady (m : LogOLG) (W : ℝ) :
    m.youngC W + m.oldC W = (1 + (1 + m.r) * m.β) / (1 + m.β) * W := by
  unfold youngC oldC
  ring

/-- **Steady-state consumption after the government budget**, O&R p. 136: using
`G = rB^G + τ^Y + τ^O` to eliminate `τ^O`,
`C = [1 + (1 + r)β]/(1 + β) · (y^Y + (y^O − G − rτ^Y + rB^G)/(1 + r))`. -/
theorem aggregate_consumption_government (m : LogOLG) {yY yO τY τO G BG : ℝ}
    (hG : G = m.r * BG + τY + τO) :
    m.youngC (lifetimeWealth m.r yY yO τY τO) + m.oldC (lifetimeWealth m.r yY yO τY τO) =
      (1 + (1 + m.r) * m.β) / (1 + m.β) *
        (yY + (yO - G - m.r * τY + m.r * BG) / (1 + m.r)) := by
  have hr := m.one_add_r_pos.ne'
  have hb : 1 + m.β ≠ 0 := by linarith [m.β_pos]
  rw [aggregate_consumption_steady]
  unfold lifetimeWealth
  rw [hG]
  field_simp
  ring

/-- **Ricardian equivalence fails in the OLG model** (O&R p. 136): holding government spending
and government assets fixed, a different split of taxes between young and old changes aggregate
consumption whenever `r ≠ 0`. -/
theorem consumption_depends_on_youth_tax (m : LogOLG) (hr0 : m.r ≠ 0) {yY yO G BG τY τY' : ℝ}
    (hτ : τY ≠ τY') :
    (1 + (1 + m.r) * m.β) / (1 + m.β) * (yY + (yO - G - m.r * τY + m.r * BG) / (1 + m.r)) ≠
      (1 + (1 + m.r) * m.β) / (1 + m.β) *
        (yY + (yO - G - m.r * τY' + m.r * BG) / (1 + m.r)) := by
  have hr := m.one_add_r_pos
  have hb := m.β_pos
  have hk : 0 < (1 + (1 + m.r) * m.β) / (1 + m.β) := by positivity
  intro heq
  have h1 := mul_left_cancel₀ hk.ne' heq
  have h2 : (yO - G - m.r * τY + m.r * BG) / (1 + m.r) =
      (yO - G - m.r * τY' + m.r * BG) / (1 + m.r) := by linarith
  rw [div_left_inj' hr.ne'] at h2
  exact hτ (mul_left_cancel₀ hr0 (by linarith))

/-- **Government assets matter** (O&R p. 136): holding spending and the youth tax fixed, higher
government assets `B^G` raise steady-state consumption when `r > 0`. -/
theorem consumption_increasing_in_government_assets (m : LogOLG) (hr0 : 0 < m.r)
    {yY yO G τY BG BG' : ℝ} (hB : BG < BG') :
    (1 + (1 + m.r) * m.β) / (1 + m.β) * (yY + (yO - G - m.r * τY + m.r * BG) / (1 + m.r)) <
      (1 + (1 + m.r) * m.β) / (1 + m.β) *
        (yY + (yO - G - m.r * τY + m.r * BG') / (1 + m.r)) := by
  have hr := m.one_add_r_pos
  have hb := m.β_pos
  have hk : 0 < (1 + (1 + m.r) * m.β) / (1 + m.β) := by positivity
  apply mul_lt_mul_of_pos_left _ hk
  have : (yO - G - m.r * τY + m.r * BG) / (1 + m.r) <
      (yO - G - m.r * τY + m.r * BG') / (1 + m.r) :=
    div_lt_div_of_pos_right (by nlinarith) hr
  linarith

/-! ### Saving and the current account (O&R §3.2.2) -/

/-- **The current account is private plus government saving**, O&R (3.17), p. 136: with
`B = B^P + B^G`, `CA_t = B_{t+1} − B_t = (B^P_{t+1} − B^P_t) + (B^G_{t+1} − B^G_t)`. -/
theorem current_account_split (BP BP' BG BG' : ℝ) :
    (BP' + BG') - (BP + BG) = (BP' - BP) + (BG' - BG) := by ring

/-- **The old dissave their youthful saving**, O&R (3.19), p. 137 and footnote 6: the old's saving
is interest on last period's saving plus disposable income less consumption; their budget
`y^O − τ^O − c^O = −(1 + r) S^Y_{t−1}` makes it `S^O_t = −S^Y_{t−1}`. -/
theorem old_saving {r SY yO τO cO : ℝ} (hbudget : yO - τO - cO = -(1 + r) * SY) :
    r * SY + yO - τO - cO = -SY := by linarith

/-- **Total private saving**, O&R (3.20)–(3.21), p. 137:
`S^P_t = S^Y_t + S^O_t = S^Y_t − S^Y_{t−1}`, the change in private assets `B^P_{t+1} − B^P_t`,
since `S^Y_t = B^P_{t+1}` (3.18). -/
theorem private_saving {SYprev SY SO : ℝ} (hSO : SO = -SYprev) : SY + SO = SY - SYprev := by
  rw [hSO]; ring

/-- **Saving by the young with flat consumption**, O&R (3.22), p. 137: if `β(1 + r) = 1`,
`S^Y = y^Y − τ^Y − c^Y = β/(1 + β) · [(y^Y − τ^Y) − (y^O − τ^O)]`. -/
theorem young_saving_flat (m : LogOLG) (hβr : m.β * (1 + m.r) = 1) (yY yO τY τO : ℝ) :
    yY - τY - m.youngC (lifetimeWealth m.r yY yO τY τO) =
      m.β / (1 + m.β) * ((yY - τY) - (yO - τO)) := by
  have hr := m.one_add_r_pos.ne'
  have hb : 1 + m.β ≠ 0 := by linarith [m.β_pos]
  have hinv : 1 / (1 + m.r) = m.β := by field_simp; linarith
  unfold youngC lifetimeWealth
  rw [div_eq_mul_one_div (yO - τO), hinv]
  field_simp
  ring

/-- **Aggregate private saving with flat consumption**, O&R (3.23), p. 137:
`S^P_t = β/(1 + β) · [Δ(y^Y − τ^Y) − Δ(y^O_{t+1} − τ^O_{t+1})]`, the difference of (3.22) at two
dates. -/
theorem private_saving_flat (β a a' b b' : ℝ) :
    β / (1 + β) * (a' - b') - β / (1 + β) * (a - b) = β / (1 + β) * ((a' - a) - (b' - b)) := by
  ring

/-- **Generational accounting**, O&R Box 3.1, pp. 142–144: cutting a generation's youth tax by one
unit and raising its old-age tax by `1 + r` leaves its lifetime wealth unchanged. -/
theorem generational_account_invariant {r : ℝ} (hr : 0 < 1 + r) (yY yO τY τO : ℝ) :
    lifetimeWealth r yY yO (τY - 1) (τO + (1 + r)) = lifetimeWealth r yY yO τY τO := by
  unfold lifetimeWealth
  field_simp
  ring

/-- Hence the swap leaves both consumption levels of that generation unchanged (Box 3.1), even
though it raises the government deficit in the generation's youth by one unit. -/
theorem generational_account_consumption (m : LogOLG) (yY yO τY τO : ℝ) :
    m.youngC (lifetimeWealth m.r yY yO (τY - 1) (τO + (1 + m.r))) =
        m.youngC (lifetimeWealth m.r yY yO τY τO) ∧
      m.oldC (lifetimeWealth m.r yY yO (τY - 1) (τO + (1 + m.r))) =
        m.oldC (lifetimeWealth m.r yY yO τY τO) := by
  rw [generational_account_invariant m.one_add_r_pos]
  exact ⟨rfl, rfl⟩

/-- **The government's accounts regroup by generation**, O&R Box 3.1: the present value of taxes
over dates equals the tax of the current old plus the present value, over generations, of each
generation's lifetime tax `τ^Y_s + τ^O_{s+1}/(1 + r)`, over any finite horizon. -/
theorem taxes_by_generation (r : ℝ) (τY τO : ℕ → ℝ) (T : ℕ) :
    ∑ s ∈ Finset.range (T + 1), ((1 + r)⁻¹) ^ s * (τY s + τO s) =
      τO 0 + ∑ s ∈ Finset.range T, ((1 + r)⁻¹) ^ s * (τY s + τO (s + 1) / (1 + r)) +
        ((1 + r)⁻¹) ^ T * τY T := by
  induction T with
  | zero => simp; ring
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [div_eq_mul_inv, pow_succ]
    ring

end ObstfeldRogoff.LifeCycleFiscalPolicy.TwoPeriodOLG

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The timing of taxes: a debt-financed transfer

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§3.2.3, pp. 137–141, footnotes 9–10, and the transitory output shock of §3.3.1,
p. 148.

Preferences are homothetic: a generation with lifetime wealth `W` consumes
`(1 − s)W` when young and `(1 + r)sW` when old. With log utility,
`s = β/(1 + β)` (O&R (3.12)–(3.13)); O&R footnote 9 notes that the results hold
for any homothetic utility, and all statements below are for a general
`0 < s < 1`. Because demands are linear in wealth, consumption changes are the
share times the change in wealth.

At date 0 the government cuts the taxes of the young and old by `d/2` each,
sells bonds `d` to the young, and forever after levies the interest `rd/2` on
each generation's young and old; the principal is never repaid.
* The date-0 old consume their windfall: `Δc^O_0 = d/2` (3.24).
* The date-0 young gain `d/2` now and pay `rd/2` later: their wealth rises by
  `d/(2(1 + r))`, so `Δc^Y_0 = (1 − s)d/(2(1 + r))` (3.25).
* Date-0 consumption rises by `[1 + (1 − s)/(1 + r)]d/2 < d` (3.26).
* Every later generation loses `(2r + r²)/(1 + r) · d/2` of wealth, so its
  consumption falls in both periods (3.28)–(3.29).
* Date-1 consumption changes by `[s − (1 − s)(2r + r²)/(1 + r)]d/2`, whose sign is
  ambiguous (3.30) and footnote 9. From date 2 on it falls; in the flat case
  `β(1 + r) = 1` it falls by exactly `rd` (footnote 10).
* The current account worsens at date 0 by the consumption rise (3.31) and at
  date 1 by `s(1 + r)d/2` (3.32), then returns to its original path.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer

/-- The wealth change of the date-0 young: `d/2` now, `−rd/2` when old (O&R p. 138). -/
noncomputable def youngWealthChange (r d : ℝ) : ℝ := d / 2 - r * (d / 2) / (1 + r)

/-- The wealth change of every generation born at date 1 or later: `−rd/2` in each period of life
(O&R p. 139). -/
noncomputable def laterWealthChange (r d : ℝ) : ℝ := -(r * (d / 2)) - r * (d / 2) / (1 + r)

theorem youngWealthChange_eq {r : ℝ} (hr : 0 < 1 + r) (d : ℝ) :
    youngWealthChange r d = d / (2 * (1 + r)) := by
  unfold youngWealthChange
  field_simp
  ring

/-- **Later generations lose** `(2r + r²)/(1 + r) · d/2`, O&R p. 139. -/
theorem laterWealthChange_eq {r : ℝ} (hr : 0 < 1 + r) (d : ℝ) :
    laterWealthChange r d = -((2 * r + r ^ 2) / (1 + r) * (d / 2)) := by
  unfold laterWealthChange
  field_simp
  ring

/-- **Consumption of the date-0 young**, O&R (3.25), p. 138: `Δc^Y_0 = (1 − s)/(1 + r) · d/2`. -/
theorem young0_consumption_change {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    (1 - s) * youngWealthChange r d = (1 - s) / (1 + r) * (d / 2) := by
  rw [youngWealthChange_eq hr]
  field_simp

/-- **Date-0 aggregate consumption**, O&R (3.26), p. 139: the old's windfall `d/2` (3.24) plus the
young's response gives `ΔC₀ = [1 + (1 − s)/(1 + r)] d/2`. -/
theorem consumption0_change {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    d / 2 + (1 - s) * youngWealthChange r d = (1 + (1 - s) / (1 + r)) * (d / 2) := by
  rw [young0_consumption_change hr]
  ring

/-- **Date-0 consumption rises by less than the transfer**, O&R p. 139: `0 < ΔC₀ < d` for `d > 0`,
`0 < s < 1` and `r > 0`. -/
theorem consumption0_change_lt {r s d : ℝ} (hr : 0 < r) (hs0 : 0 < s) (hs1 : s < 1) (hd : 0 < d) :
    0 < (1 + (1 - s) / (1 + r)) * (d / 2) ∧ (1 + (1 - s) / (1 + r)) * (d / 2) < d := by
  have h1 : 0 < (1 - s) / (1 + r) := div_pos (by linarith) (by linarith)
  have h2 : (1 - s) / (1 + r) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  constructor <;> nlinarith

/-- **The date-1 old**, O&R (3.27), p. 139: `Δc^O_1 = (1 + r)s · Δw = s d/2`. -/
theorem old1_consumption_change {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    (1 + r) * s * youngWealthChange r d = s * (d / 2) := by
  rw [youngWealthChange_eq hr]
  field_simp

/-- **Later young**, O&R (3.28), p. 139: `Δc^Y_t = −(1 − s)(2r + r²)/(1 + r) · d/2` for `t ≥ 1`. -/
theorem later_young_consumption_change {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    (1 - s) * laterWealthChange r d = -((1 - s) * ((2 * r + r ^ 2) / (1 + r)) * (d / 2)) := by
  rw [laterWealthChange_eq hr]
  ring

/-- **Later old**, O&R (3.29), p. 139: `Δc^O_t = −s(2r + r²) · d/2` for `t ≥ 2`. -/
theorem later_old_consumption_change {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    (1 + r) * s * laterWealthChange r d = -(s * (2 * r + r ^ 2) * (d / 2)) := by
  rw [laterWealthChange_eq hr]
  field_simp

/-- **Date-1 aggregate consumption**, O&R (3.30), p. 139:
`ΔC₁ = [s − (1 − s)(2r + r²)/(1 + r)] d/2`. -/
theorem consumption1_change {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    (1 + r) * s * youngWealthChange r d + (1 - s) * laterWealthChange r d =
      (s - (1 - s) * (2 * r + r ^ 2) / (1 + r)) * (d / 2) := by
  rw [old1_consumption_change hr, later_young_consumption_change hr]
  ring

/-- **The sign of the date-1 change**, O&R footnote 9, p. 139: for `d > 0` and `0 < s < 1`, date-1
consumption rises iff `s/(1 − s) > (2r + r²)/(1 + r)`. -/
theorem consumption1_rises_iff {r s d : ℝ} (hr : 0 < 1 + r) (hs1 : s < 1) (hd : 0 < d) :
    0 < (s - (1 - s) * (2 * r + r ^ 2) / (1 + r)) * (d / 2) ↔
      (2 * r + r ^ 2) / (1 + r) < s / (1 - s) := by
  have h1s : 0 < 1 - s := by linarith
  rw [mul_pos_iff_of_pos_right (by linarith : (0 : ℝ) < d / 2), sub_pos, div_lt_div_iff₀ hr h1s,
    div_lt_iff₀ hr]
  constructor <;> intro h <;> nlinarith

/-- **The sign really is ambiguous** (O&R p. 139): with log utility and `β = 1`, date-1 consumption
rises at `r = 1/10` and falls at `r = 1`. -/
theorem consumption1_sign_ambiguous :
    0 < ((1 : ℝ) / 2 - (1 - 1 / 2) * (2 * (1 / 10) + (1 / 10) ^ 2) / (1 + 1 / 10)) ∧
      ((1 : ℝ) / 2 - (1 - 1 / 2) * (2 * 1 + 1 ^ 2) / (1 + 1)) < 0 := by
  norm_num

/-- **Consumption falls from date 2 on**, O&R p. 139: `ΔC_t = Δc^Y_t + Δc^O_t < 0` for `t ≥ 2` when
`r > 0`, `d > 0` and `0 < s < 1`. -/
theorem consumption_later_falls {r s d : ℝ} (hr : 0 < r) (hs0 : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) :
    (1 - s) * laterWealthChange r d + (1 + r) * s * laterWealthChange r d < 0 := by
  rw [later_young_consumption_change (by linarith), later_old_consumption_change (by linarith)]
  have h1 : 0 < (1 - s) * ((2 * r + r ^ 2) / (1 + r)) * (d / 2) := by
    have : 0 < (2 * r + r ^ 2) / (1 + r) := div_pos (by nlinarith) (by linarith)
    positivity
  have h2 : 0 < s * (2 * r + r ^ 2) * (d / 2) := by
    have : 0 < 2 * r + r ^ 2 := by nlinarith
    positivity
  linarith

/-- **The long-run consumption fall**, O&R footnote 10, p. 139–140: from date 2 on, aggregate
consumption falls by `(1 + sr)(2r + r²)/(1 + r) · d/2`. With log utility (`s = β/(1 + β)`) this is
the book's `(1 + βr/(1 + β))(2r + r²)/(1 + r) · d/2`. -/
theorem consumption_later_change {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    (1 - s) * laterWealthChange r d + (1 + r) * s * laterWealthChange r d =
      -((1 + s * r) * ((2 * r + r ^ 2) / (1 + r)) * (d / 2)) := by
  rw [later_young_consumption_change hr, later_old_consumption_change hr]
  field_simp
  ring

/-- **Flat consumption: the fall is exactly `rd`**, O&R footnote 10: with log utility and
`β(1 + r) = 1`, `s = β/(1 + β) = 1/(2 + r)` and the long-run fall is `rd`. -/
theorem consumption_later_change_flat {r : ℝ} (hr : 0 < 1 + r) (d : ℝ) :
    -((1 + 1 / (2 + r) * r) * ((2 * r + r ^ 2) / (1 + r)) * (d / 2)) = -(r * d) := by
  have h2 : (2 : ℝ) + r ≠ 0 := by linarith
  have h1 := hr.ne'
  field_simp
  ring

/-- With log utility and `β(1 + r) = 1`, the saving share `β/(1 + β)` equals `1/(2 + r)`. -/
theorem share_of_flat {β r : ℝ} (hr : 0 < 1 + r) (hβr : β * (1 + r) = 1) :
    β / (1 + β) = 1 / (2 + r) := by
  have hβ : β = 1 / (1 + r) := by field_simp; linarith
  rw [hβ]
  have h1 := hr.ne'
  have h2 : (2 : ℝ) + r ≠ 0 := by linarith
  field_simp
  ring

/-! ### The current account (O&R (3.31)–(3.32)) -/

/-- **Date-1 current account**, O&R (3.32), p. 140: the date-1 change is the interest on the date-0
change less the date-1 consumption change, `ΔCA₁ = rΔCA₀ − ΔC₁ = −s(1 + r)d/2`. -/
theorem current_account1_change {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    r * (-((1 + (1 - s) / (1 + r)) * (d / 2))) -
        (s - (1 - s) * (2 * r + r ^ 2) / (1 + r)) * (d / 2) =
      -(s * (1 + r) * (d / 2)) := by
  field_simp
  ring

/-- **The current account returns to its path from date 2**, O&R p. 140: interest on the
accumulated foreign debt exactly matches the permanent consumption fall, so `ΔCA_t = 0` for
`t ≥ 2`: `r(ΔCA₀ + ΔCA₁) = ΔC_t`. -/
theorem current_account_later_zero {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    r * (-((1 + (1 - s) / (1 + r)) * (d / 2)) + -(s * (1 + r) * (d / 2))) -
        (-((1 + s * r) * ((2 * r + r ^ 2) / (1 + r)) * (d / 2))) = 0 := by
  field_simp
  ring

/-! ### Transfers without deficits and transitory shocks -/

/-- **A tax-financed transfer from young to old**, O&R p. 141: a transfer `δ` raises the old's
consumption by `δ` and lowers the young's by `(1 − s)δ`, so aggregate consumption rises by
`sδ > 0` and the current account worsens with a balanced budget. -/
theorem balanced_transfer_consumption {s δ : ℝ} (hs0 : 0 < s) (hδ : 0 < δ) :
    δ + (1 - s) * (-δ) = s * δ ∧ 0 < s * δ :=
  ⟨by ring, mul_pos hs0 hδ⟩

/-- **A transitory output shock**, O&R §3.3.1, p. 148: output rises by `dy` for both generations
at date 0 only. The old consume theirs, the young consume `(1 − s)dy`, so `ΔCA₀ = s·dy`; at date
1 the old consume `(1 + r)s·dy` and `ΔCA₁ = r·s·dy − (1 + r)s·dy = −s·dy`. The two changes cancel,
so there is no long-run effect. -/
theorem transitory_shock_current_account (r s dy : ℝ) :
    2 * dy - (dy + (1 - s) * dy) = s * dy ∧
      r * (s * dy) - (1 + r) * s * dy = -(s * dy) ∧ s * dy + -(s * dy) = 0 := by
  refine ⟨by ring, by ring, by ring⟩

/-- With log utility the share is `s = β/(1 + β)`, so `1 − s = 1/(1 + β)`: the demands of O&R
(3.12)–(3.13) are the homothetic demands above. -/
theorem log_share (m : LogOLG) (W : ℝ) :
    m.youngC W = (1 - m.β / (1 + m.β)) * W ∧
      m.oldC W = (1 + m.r) * (m.β / (1 + m.β)) * W := by
  have hb : 1 + m.β ≠ 0 := by linarith [m.β_pos]
  unfold LogOLG.youngC LogOLG.oldC
  constructor
  · field_simp
    ring
  · field_simp

end ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Output growth, demographics and saving

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§3.3.2–§3.3.3, pp. 148–152, and Exercise 1, p. 195.

* **Growth and saving** (pp. 149–150). With `β(1 + r) = 1` and no taxes, lifetime
  earnings grow at rate `e` (`y^O_{t+1} = (1 + e)y^Y_t`) and each generation's youth
  endowment grows at rate `g`. Then the private saving rate is
  `S^P/Y = −β/(1 + β) · eg/(2 + e + g)`. It falls with `e` (when `g > 0`) and rises with
  `g` iff `e < 0`.
* **Population growth** (O&R (3.33), p. 151). With cohorts growing at rate `n` and
  constant individual saving `s^Y`, `S^P/Y = n s^Y/((1 + n)y^Y + y^O)`, increasing in
  `n` when the young save.
* **Exercise 1** (three-period lives, `r = 0`, log utility, no borrowing by the young).
  Earnings are `y^Y` when young, `(1 + e)y^Y` in middle age and zero in old age.
  Unconstrained, each period consumes a third of lifetime income, which is optimal
  by the AM–GM inequality. For `e > 1` the young are constrained and consume their
  income. With youth income growing at `g`, the aggregate saving rate falls with `e`
  if the young can borrow, but **rises** with `e` when the constraint binds.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving

/-- The private saving rate with growing earnings, O&R p. 150: with `y^Y_t = y`,
`y^O_t = (1 + e)y/(1 + g)` and saving given by (3.23),
`S^P/Y = −β/(1 + β) · eg/(2 + e + g)`. -/
theorem saving_rate_growth {β e g y : ℝ} (hβ : 0 < 1 + β) (hg : 0 < 1 + g) (hy : 0 < y)
    (heg : 0 < 2 + e + g) :
    β / (1 + β) * ((y - (1 + e) * y) - (y / (1 + g) - (1 + e) * (y / (1 + g)))) /
        (y + (1 + e) * (y / (1 + g))) =
      -(β / (1 + β) * (e * g / (2 + e + g))) := by
  have h1 := hβ.ne'
  have h2 := hg.ne'
  have h3 := hy.ne'
  have h4 := heg.ne'
  have hY : y + (1 + e) * (y / (1 + g)) = y * (2 + e + g) / (1 + g) := by field_simp; ring
  rw [hY]
  field_simp
  ring

/-- The saving rate as a function of lifetime earnings growth `e` and output growth `g`. -/
noncomputable def savingRate (β e g : ℝ) : ℝ := -(β / (1 + β) * (e * g / (2 + e + g)))

/-- **Faster lifetime earnings growth lowers saving**, O&R p. 150:
`d(S^P/Y)/de = −β/(1 + β) · g(2 + g)/(2 + e + g)² < 0` when `g > 0` and `β > 0`. -/
theorem hasDerivAt_savingRate_e {β e g : ℝ} (heg : 2 + e + g ≠ 0) :
    HasDerivAt (fun e => savingRate β e g)
      (-(β / (1 + β) * (g * (2 + g) / (2 + e + g) ^ 2))) e := by
  unfold savingRate
  have hd : HasDerivAt (fun e : ℝ => 2 + e + g) 1 e := by
    simpa using ((hasDerivAt_id e).const_add 2).add_const g
  have := (((hasDerivAt_id e).mul_const g).div hd heg).const_mul (β / (1 + β))
  convert this.neg using 1
  · funext y
    simp only [Pi.div_apply, id, Pi.neg_apply]
  · simp only [id]
    field_simp
    ring

theorem savingRate_e_deriv_neg {β e g : ℝ} (hβ : 0 < β) (hg : 0 < g) (heg : 0 < 2 + e + g) :
    -(β / (1 + β) * (g * (2 + g) / (2 + e + g) ^ 2)) < 0 := by
  have : 0 < β / (1 + β) * (g * (2 + g) / (2 + e + g) ^ 2) := by positivity
  linarith

/-- **Faster output growth raises saving iff earnings fall over the life cycle**, O&R p. 150:
`d(S^P/Y)/dg = −β/(1 + β) · e(2 + e)/(2 + e + g)²`, positive iff `e < 0` (given `e ≥ −1`). -/
theorem hasDerivAt_savingRate_g {β e g : ℝ} (heg : 2 + e + g ≠ 0) :
    HasDerivAt (fun g => savingRate β e g)
      (-(β / (1 + β) * (e * (2 + e) / (2 + e + g) ^ 2))) g := by
  unfold savingRate
  have hd : HasDerivAt (fun g : ℝ => 2 + e + g) 1 g := by
    simpa using (hasDerivAt_id g).const_add (2 + e)
  have := (((hasDerivAt_id g).const_mul e).div hd heg).const_mul (β / (1 + β))
  convert this.neg using 1
  · funext y
    simp only [Pi.div_apply, id, Pi.neg_apply]
  · simp only [id]
    field_simp
    ring

theorem savingRate_g_deriv_pos_iff {β e g : ℝ} (hβ : 0 < β) (he : -1 ≤ e) (heg : 0 < 2 + e + g) :
    0 < -(β / (1 + β) * (e * (2 + e) / (2 + e + g) ^ 2)) ↔ e < 0 := by
  have hk : 0 < β / (1 + β) := by positivity
  have hd : 0 < (2 + e + g) ^ 2 := by positivity
  rw [neg_pos, mul_neg_iff]
  simp only [hk, not_lt.2 hk.le, true_and, false_and, false_or, div_neg_iff, hd,
    not_lt.2 hd.le, and_true, and_false, or_false]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    nlinarith

/-- **Population growth and saving**, O&R (3.33), p. 151: with `N_t = (1 + n)N_{t−1}`,
`S^P/Y = (N_t − N_{t−1})s^Y/(N_t y^Y + N_{t−1}y^O) = n s^Y/((1 + n)y^Y + y^O)`. -/
theorem saving_rate_population {n N sY yY yO : ℝ} (hN : 0 < N)
    (hden : 0 < (1 + n) * yY + yO) :
    ((1 + n) * N - N) * sY / ((1 + n) * N * yY + N * yO) = n * sY / ((1 + n) * yY + yO) := by
  have h1 := hN.ne'
  have h2 := hden.ne'
  have : (1 + n) * N * yY + N * yO = N * ((1 + n) * yY + yO) := by ring
  rw [this]
  field_simp
  ring

/-- **Faster population growth raises saving when the young save**, O&R p. 151:
`d(S^P/Y)/dn = s^Y(y^Y + y^O)/((1 + n)y^Y + y^O)² > 0` for `s^Y > 0`. -/
theorem hasDerivAt_saving_rate_population {n sY yY yO : ℝ} (hden : (1 + n) * yY + yO ≠ 0) :
    HasDerivAt (fun n => n * sY / ((1 + n) * yY + yO))
      (sY * (yY + yO) / ((1 + n) * yY + yO) ^ 2) n := by
  have hd : HasDerivAt (fun n : ℝ => (1 + n) * yY + yO) yY n := by
    simpa using (((hasDerivAt_id n).const_add 1).mul_const yY).add_const yO
  have := ((hasDerivAt_id n).mul_const sY).div hd hden
  convert this using 1
  · funext y
    simp only [Pi.div_apply, id]
  · simp only [id]
    field_simp
    ring

/-! ### Exercise 1: three-period lives (O&R p. 195) -/

/-- **The unconstrained three-period plan is optimal** (Exercise 1): with `r = 0` and log utility,
spending a third of lifetime income `W` in each period maximises `log c^Y + log c^M + log c^O`
over positive plans with `c^Y + c^M + c^O = W` (AM–GM). -/
theorem three_period_optimal {W cY cM cO : ℝ} (hY : 0 < cY) (hM : 0 < cM) (hO : 0 < cO)
    (hW : cY + cM + cO = W) :
    Real.log cY + Real.log cM + Real.log cO ≤ 3 * Real.log (W / 3) := by
  have h := Real.geom_mean_le_arith_mean3_weighted (w₁ := 1 / 3) (w₂ := 1 / 3) (w₃ := 1 / 3)
    (p₁ := cY) (p₂ := cM) (p₃ := cO) (by norm_num) (by norm_num) (by norm_num) hY.le hM.le hO.le
    (by norm_num)
  have hW3 : 0 < W / 3 := by linarith
  have hlhs : 0 < cY ^ (1 / 3 : ℝ) * cM ^ (1 / 3 : ℝ) * cO ^ (1 / 3 : ℝ) := by positivity
  have hrhs : 1 / 3 * cY + 1 / 3 * cM + 1 / 3 * cO = W / 3 := by rw [← hW]; ring
  rw [hrhs] at h
  have hl := Real.log_le_log hlhs h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hY, Real.log_rpow hM, Real.log_rpow hO] at hl
  linarith

/-- **Exercise 1(a), unconstrained case** (`e ≤ 1`): with `y^M = (1 + e)y^Y` and `y^O = 0`, each
period consumes `(2 + e)y^Y/3`, so the young save `(1 − e)y^Y/3 ≥ 0`, the middle-aged save
`(1 + 2e)y^Y/3` and the old dissave `(2 + e)y^Y/3`. -/
theorem ex1_unconstrained_saving (e y : ℝ) :
    y - (2 + e) * y / 3 = (1 - e) * y / 3 ∧
      (1 + e) * y - (2 + e) * y / 3 = (1 + 2 * e) * y / 3 ∧
      0 - (2 + e) * y / 3 = -((2 + e) * y / 3) := by
  refine ⟨by ring, by ring, by ring⟩

/-- The young want to borrow exactly when `e > 1` (Exercise 1(a)): the unconstrained youth saving
`(1 − e)y^Y/3` is negative iff `e > 1`. -/
theorem ex1_constraint_binds_iff {e y : ℝ} (hy : 0 < y) : (1 - e) * y / 3 < 0 ↔ 1 < e := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    have : (1 - e) * y < 0 := mul_neg_of_neg_of_pos (by linarith) hy
    linarith

/-- **Exercise 1(a), constrained case** (`e > 1`): the young consume their income and save
nothing; the middle-aged and old split `(1 + e)y^Y` equally, so the middle-aged save
`(1 + e)y^Y/2` and the old dissave as much. -/
theorem ex1_constrained_saving (e y : ℝ) :
    y - y = 0 ∧ (1 + e) * y - (1 + e) * y / 2 = (1 + e) * y / 2 ∧
      0 - (1 + e) * y / 2 = -((1 + e) * y / 2) := by
  refine ⟨by ring, by ring, by ring⟩

/-- **Exercise 1(b), unconstrained**: with youth income growing at `g`, the aggregate saving rate
of the three generations alive at `t` out of output `y^Y_t + (1 + e)y^Y_{t−1}` is
`g[(1 − e)(1 + g) + 2 + e]/(3(1 + g)(2 + e + g))`. -/
theorem ex1_saving_rate_unconstrained {e g y : ℝ} (hg : 0 < 1 + g) (hy : 0 < y)
    (heg : 0 < 2 + e + g) :
    ((1 - e) * y / 3 + (1 + 2 * e) * (y / (1 + g)) / 3 - (2 + e) * (y / (1 + g) ^ 2) / 3) /
        (y + (1 + e) * (y / (1 + g))) =
      g * ((1 - e) * (1 + g) + 2 + e) / (3 * (1 + g) * (2 + e + g)) := by
  have h1 := hg.ne'
  have h2 := hy.ne'
  have h3 := heg.ne'
  have hY : y + (1 + e) * (y / (1 + g)) = y * (2 + e + g) / (1 + g) := by field_simp; ring
  rw [hY]
  field_simp
  ring

/-- **Exercise 1(b), constrained** (`e > 1`): the aggregate saving rate is
`(1 + e)g/(2(1 + g)(2 + e + g))`. -/
theorem ex1_saving_rate_constrained {e g y : ℝ} (hg : 0 < 1 + g) (hy : 0 < y)
    (heg : 0 < 2 + e + g) :
    (0 + (1 + e) * (y / (1 + g)) / 2 - (1 + e) * (y / (1 + g) ^ 2) / 2) /
        (y + (1 + e) * (y / (1 + g))) =
      (1 + e) * g / (2 * (1 + g) * (2 + e + g)) := by
  have h1 := hg.ne'
  have h2 := hy.ne'
  have h3 := heg.ne'
  have hY : y + (1 + e) * (y / (1 + g)) = y * (2 + e + g) / (1 + g) := by field_simp; ring
  rw [hY]
  field_simp
  ring

/-- **Exercise 1(c), young can borrow**: the unconstrained saving rate falls as `e` rises
(for `g > 0` and `0 ≤ e < e'`). -/
theorem ex1_unconstrained_rate_anti_e {g e e' : ℝ} (hg : 0 < g) (he : 0 ≤ e) (hee : e < e') :
    g * ((1 - e') * (1 + g) + 2 + e') / (3 * (1 + g) * (2 + e' + g)) <
      g * ((1 - e) * (1 + g) + 2 + e) / (3 * (1 + g) * (2 + e + g)) := by
  have hd1 : 0 < 3 * (1 + g) * (2 + e + g) := by positivity
  have hd2 : 0 < 3 * (1 + g) * (2 + e' + g) := by nlinarith
  rw [div_lt_div_iff₀ hd2 hd1]
  have key : (3 + g - e' * g) * (2 + e + g) < (3 + g - e * g) * (2 + e' + g) := by
    nlinarith [mul_pos (sub_pos.2 hee) (by positivity : (0 : ℝ) < 3 + g + g * (2 + g))]
  have hpos : 0 < 3 * g * (1 + g) := by positivity
  nlinarith [mul_lt_mul_of_pos_left key hpos]

/-- **Exercise 1(c), young constrained**: when the borrowing constraint binds, the saving rate
**rises** with `e` (for `g > 0`): the opposite of the unconstrained case. -/
theorem ex1_constrained_rate_mono_e {g e e' : ℝ} (hg : 0 < g) (he : 0 ≤ e) (hee : e < e') :
    (1 + e) * g / (2 * (1 + g) * (2 + e + g)) < (1 + e') * g / (2 * (1 + g) * (2 + e' + g)) := by
  have hd1 : 0 < 2 * (1 + g) * (2 + e + g) := by positivity
  have hd2 : 0 < 2 * (1 + g) * (2 + e' + g) := by nlinarith
  rw [div_lt_div_iff₀ hd1 hd2]
  nlinarith [mul_pos hg (by linarith : (0 : ℝ) < e' - e), mul_pos hg hg]

/-- **Exercise 1(d), first part**: if the young can borrow, youth endowments grow at `g`, and
middle-age endowment `m` and old-age endowment `0` are constant, aggregate saving at `t` is
`y^Y_t [1 − (1 + 1/(1 + g) + 1/(1 + g)²)/3]`, positive for `g > 0`: the middle-aged terms cancel. -/
theorem ex1d_saving {g y m : ℝ} (hg : 0 < g) (hy : 0 < y) :
    (y - (y + m) / 3) + (m - (y / (1 + g) + m) / 3) + (0 - (y / (1 + g) ^ 2 + m) / 3) =
        y * (1 - (1 + 1 / (1 + g) + 1 / (1 + g) ^ 2) / 3) ∧
      0 < y * (1 - (1 + 1 / (1 + g) + 1 / (1 + g) ^ 2) / 3) := by
  have h1 : (0 : ℝ) < 1 + g := by linarith
  refine ⟨by field_simp; ring, mul_pos hy ?_⟩
  have a : 1 / (1 + g) < 1 := (div_lt_one h1).2 (by linarith)
  have b : 1 / (1 + g) ^ 2 < 1 := (div_lt_one (by positivity)).2 (by nlinarith)
  linarith

end ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Investment and growth in the small open OLG economy

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§3.4, "Investment and Growth", pp. 156–161 (the Feldstein–Horioka application,
pp. 161–164, is empirical and is not formalised).

Output is Cobb–Douglas, `Y = A K^α L^{1−α}` (O&R (3.34)); capital does not depreciate
and there are no adjustment costs; the young supply one unit of labour, the old none;
cohorts grow at rate `n` (O&R (3.35)); there is no government and the world rate `r`
is fixed.

* **Factor prices** (O&R (3.36)–(3.39)). The marginal-product condition `r = αAk^{α−1}`
  has the unique positive solution `k(r, A) = (αA/r)^{1/(1−α)}`, the wage is
  `w = (1 − α)A(αA/r)^{α/(1−α)}`, and the factor-price frontier satisfies `dw/dr = −k`.
* **Saving and foreign assets** (O&R (3.40)–(3.42)): `s^Y = (1 + n)(b + k)` and
  `b̄ = s̄^Y/(1 + n) − k̄`; steady-state net foreign assets grow at rate `n`, so the
  current account has the sign of `b̄`.
* **Per-capita saving and investment** (p. 159, footnotes 24–25), with their
  derivatives in `n`. The footnote-25 derivative `(n² + 4n + 2)k̄/(2 + n)²` is positive
  only for `n > √2 − 2`; we prove positivity exactly there.
* **Productivity growth** (O&R (3.43)–(3.44), footnote 27): `K/Y = α/r` at every date,
  `Y_t = N_t A_t^{1/(1−α)}(α/r)^{α/(1−α)}`, `Y_{t+1} = (1 + n)(1 + g)Y_t` and
  `I/Y = (n + g + ng)α/r`.
* **Log utility** (O&R (3.45)–(3.46), p. 161): `s^Y = βw/(1 + β)`, the old dissave
  exactly `s^Y`, `S/Y = β(1−α)/(1+β)·[1 − 1/((1+n)(1+g))]`,
  `B/Y = β(1−α)/((1+β)(1+n)(1+g)) − α/r` and `CA/Y = S/Y − I/Y = (n + g + ng)B/Y`,
  together with the comparative statics stated in the text.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond

/-! ## Factor prices -/

/-- The capital–labour ratio `k(r, A) = (αA/r)^{1/(1−α)}`, O&R (3.38), p. 157. -/
noncomputable def capLabour (α A r : ℝ) : ℝ := (α * A / r) ^ (1 / (1 - α))

/-- The real wage `w = (1 − α)A(αA/r)^{α/(1−α)}`, O&R (3.39), p. 157. -/
noncomputable def wageOf (α A r : ℝ) : ℝ := (1 - α) * A * (α * A / r) ^ (α / (1 - α))

/-- O&R (3.36), p. 157: `k(r, A)` satisfies the marginal-product condition
`αA k^{α−1} = r` (for `A, r > 0`, `0 < α < 1`). -/
theorem mpk_capLabour {α A r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hr : 0 < r) :
    α * A * capLabour α A r ^ (α - 1) = r := by
  have hx : 0 ≤ α * A / r := by positivity
  have h1 : (1 - α) ≠ 0 := by linarith
  unfold capLabour
  rw [← Real.rpow_mul hx, show 1 / (1 - α) * (α - 1) = -1 by field_simp; ring,
    Real.rpow_neg_one]
  field_simp

/-- O&R (3.36)–(3.38), p. 157: `k(r, A)` is the only positive capital–labour ratio at
which the marginal product of capital equals the world rate. -/
theorem capLabour_unique {α A r k : ℝ} (hα1 : α < 1) (hk : 0 < k) (hr : 0 < r)
    (hmpk : α * A * k ^ (α - 1) = r) : k = capLabour α A r := by
  have hkp : 0 < k ^ (α - 1) := Real.rpow_pos_of_pos hk _
  have h1 : (1 - α) ≠ 0 := by linarith
  have hαA : α * A ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmpk
    linarith
  have hx : α * A / r = k ^ (1 - α) := by
    rw [show (1 - α) = -(α - 1) by ring, Real.rpow_neg hk.le, ← hmpk]
    field_simp
    exact div_self hαA
  unfold capLabour
  rw [hx, ← Real.rpow_mul hk.le, show (1 - α) * (1 / (1 - α)) = 1 by field_simp,
    Real.rpow_one]

/-- O&R (3.37)/(3.39), p. 157: the wage equals the marginal product of labour at
`k(r, A)`, `(1 − α)A k(r, A)^α = (1 − α)A(αA/r)^{α/(1−α)}`. -/
theorem mpl_capLabour {α A r : ℝ} (hα1 : α < 1) (hA : 0 < A) (hr : 0 < r) (hα0 : 0 < α) :
    (1 - α) * A * capLabour α A r ^ α = wageOf α A r := by
  have hx : 0 ≤ α * A / r := by positivity
  have h1 : (1 - α) ≠ 0 := by linarith
  unfold capLabour wageOf
  rw [← Real.rpow_mul hx, show 1 / (1 - α) * α = α / (1 - α) by field_simp]

/-- Factor-price frontier, O&R (3.39), p. 157: along `w(r)` the wage falls with the world
rate at the rate `dw/dr = −k(r, A)` (for `A, r > 0`, `0 < α < 1`). -/
theorem wage_hasDerivAt {α A r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hr : 0 < r) :
    HasDerivAt (fun ρ => wageOf α A ρ) (-capLabour α A r) r := by
  have h1 : (1 - α) ≠ 0 := by linarith
  have hx : 0 < α * A / r := by positivity
  have hinv : HasDerivAt (fun ρ : ℝ => α * A / ρ) (α * A * (-(r ^ 2)⁻¹)) r := by
    have := (hasDerivAt_inv hr.ne').const_mul (α * A)
    simpa [div_eq_mul_inv] using this
  have hp := (hinv.rpow_const (p := α / (1 - α)) (Or.inl hx.ne')).const_mul ((1 - α) * A)
  refine hp.congr_deriv ?_
  unfold capLabour
  rw [show 1 / (1 - α) = (α / (1 - α) - 1) + 2 by field_simp; ring,
    Real.rpow_add hx, Real.rpow_two]
  generalize (α * A / r) ^ (α / (1 - α) - 1) = y
  field_simp

/-! ## Saving, investment and foreign assets with constant productivity -/

/-- O&R (3.40)–(3.41), p. 158: if aggregate saving of the young is `S^Y_t = B_{t+1} +
K_{t+1}` and `N_{t+1} = (1 + n)N_t`, then per young person
`s^Y_t = (1 + n)(b_{t+1} + k_{t+1})` with `b = B/N`, `k = K/N`. -/
theorem young_saving_per_capita {SY B' K' N N' n : ℝ} (hN : 0 < N) (hn : 0 < 1 + n)
    (hN' : N' = (1 + n) * N) (hS : SY = B' + K') :
    SY / N = (1 + n) * (B' / N' + K' / N') := by
  subst hN' hS
  field_simp

/-- O&R (3.42), p. 158: steady-state net foreign assets per worker,
`b̄ = s̄^Y/(1 + n) − k̄`. -/
theorem steady_foreign_assets {sY b k n : ℝ} (hn : 0 < 1 + n)
    (h : sY = (1 + n) * (b + k)) : b = sY / (1 + n) - k := by
  subst h
  field_simp
  ring

/-- O&R p. 159: in a steady state with `B_t = N_t b̄` and `N_{t+1} = (1 + n)N_t`, the
current account `B_{t+1} − B_t` equals `n N_t b̄`; for `n > 0` it is in surplus iff
`b̄ > 0` (and in deficit iff `b̄ < 0`). -/
theorem steady_current_account_sign {N n b : ℝ} (hN : 0 < N) (hn : 0 < n) :
    (1 + n) * N * b - N * b = n * N * b ∧ (0 < n * N * b ↔ 0 < b) ∧
      (n * N * b < 0 ↔ b < 0) := by
  have hnN : 0 < n * N := mul_pos hn hN
  refine ⟨by ring, ⟨fun h => ?_, fun h => mul_pos hnN h⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact pos_of_mul_pos_right h hnN.le
  · by_contra hb
    push Not at hb
    linarith [mul_nonneg hnN.le hb]
  · nlinarith

/-- Steady-state saving per member of the population, O&R p. 159:
`(S^Y_t + S^O_t)/(N_t + N_{t−1})` with `S^Y_t = N_t s^Y`, `S^O_t = N_{t−1}s^O`. -/
noncomputable def savingPerCapita (n sY sO : ℝ) : ℝ := (1 + n) / (2 + n) * sY + 1 / (2 + n) * sO

/-- O&R p. 159: with `N_t = (1 + n)N_{t−1}`, aggregate saving per capita is
`(1 + n)/(2 + n)·s^Y + 1/(2 + n)·s^O`. -/
theorem saving_per_capita_eq {N0 n sY sO : ℝ} (hN : 0 < N0) (hn : 0 < 1 + n) :
    ((1 + n) * N0 * sY + N0 * sO) / ((1 + n) * N0 + N0) = savingPerCapita n sY sO := by
  have h2 : 2 + n ≠ 0 := by linarith
  unfold savingPerCapita
  field_simp
  ring

/-- O&R footnote 24, p. 159: `d/dn` of steady-state saving per capita is
`(s^Y − s^O)/(2 + n)²` (holding the individual saving levels fixed, as they are
independent of `n`). -/
theorem savingPerCapita_hasDerivAt {n sY sO : ℝ} (hn : 0 < 2 + n) :
    HasDerivAt (fun m => savingPerCapita m sY sO) ((sY - sO) / (2 + n) ^ 2) n := by
  have hd : HasDerivAt (fun m : ℝ => 2 + m) 1 n := by
    simpa using (hasDerivAt_id n).const_add (2 : ℝ)
  have hn' : HasDerivAt (fun m : ℝ => 1 + m) 1 n := by
    simpa using (hasDerivAt_id n).const_add (1 : ℝ)
  have hq1 := ((hn'.div hd hn.ne').mul_const sY)
  have hq2 := (((hasDerivAt_const n (1 : ℝ)).div hd hn.ne').mul_const sO)
  refine (HasDerivAt.add hq1 hq2).congr_deriv ?_
  field_simp
  ring

/-- O&R p. 159 and footnote 24: since the old dissave (`s^O = −s^Y`), the derivative
`(s^Y − s^O)/(2 + n)²` is positive whenever the young save (`s^Y > 0`). -/
theorem savingPerCapita_deriv_pos {n sY : ℝ} (hsY : 0 < sY) (hn : 0 < 2 + n) :
    0 < (sY - -sY) / (2 + n) ^ 2 := by
  have : 0 < sY - -sY := by linarith
  positivity

/-- Steady-state investment per capita, O&R p. 159: `(1 + n)n k̄/(2 + n)`. -/
noncomputable def investPerCapita (n k : ℝ) : ℝ := (1 + n) * n * k / (2 + n)

/-- O&R p. 159: with `K_t = N_t k̄` and `N_{t+1} = (1 + n)N_t`, investment per member of
the population `(K_{t+1} − K_t)/(N_t + N_{t−1})` equals `(1 + n)n k̄/(2 + n)`. -/
theorem invest_per_capita_eq {N0 n k : ℝ} (hN : 0 < N0) (hn : 0 < 1 + n) :
    ((1 + n) * ((1 + n) * N0) * k - (1 + n) * N0 * k) / ((1 + n) * N0 + N0) =
      investPerCapita n k := by
  have h2 : 2 + n ≠ 0 := by linarith
  unfold investPerCapita
  field_simp
  ring

/-- O&R footnote 25, p. 159: `d/dn` of investment per capita is
`(n² + 4n + 2)k̄/(2 + n)²`. -/
theorem investPerCapita_hasDerivAt {n k : ℝ} (hn : 0 < 2 + n) :
    HasDerivAt (fun m => investPerCapita m k) ((n ^ 2 + 4 * n + 2) * k / (2 + n) ^ 2) n := by
  have hd : HasDerivAt (fun m : ℝ => 2 + m) 1 n := by
    simpa using (hasDerivAt_id n).const_add (2 : ℝ)
  have hn' : HasDerivAt (fun m : ℝ => 1 + m) 1 n := by
    simpa using (hasDerivAt_id n).const_add (1 : ℝ)
  have hnum := ((hn'.mul (hasDerivAt_id n)).mul_const k)
  refine (hnum.div hd hn.ne').congr_deriv ?_
  simp only [Pi.mul_apply, id]
  field_simp
  ring

/-- O&R footnote 25, p. 159, corrected: the derivative `(n² + 4n + 2)k̄/(2 + n)²` is
positive for `k̄ > 0` exactly when `n > √2 − 2` (the book says "`> 0`" without a
qualifier; it is negative for `−1 < n < √2 − 2`). -/
theorem investPerCapita_deriv_pos_iff {n k : ℝ} (hk : 0 < k) (hn : -1 < n) :
    0 < (n ^ 2 + 4 * n + 2) * k / (2 + n) ^ 2 ↔ Real.sqrt 2 - 2 < n := by
  have h2 : 0 < (2 + n) ^ 2 := by nlinarith
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [div_pos_iff_of_pos_right h2, mul_pos_iff_of_pos_right hk]
  have hfac : n ^ 2 + 4 * n + 2 = (n + 2 - Real.sqrt 2) * (n + 2 + Real.sqrt 2) := by
    nlinarith
  rw [hfac]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    have : 0 < n + 2 + Real.sqrt 2 := by linarith
    have : 0 < n + 2 - Real.sqrt 2 := by linarith
    positivity

/-! ## Productivity growth -/

namespace Growth

/-- Capital stock at date `t` when firms equate the marginal product of capital to `r`:
`K_t = N_t k(r, A_t)`, O&R (3.38), p. 157. -/
noncomputable def capital (α r : ℝ) (A N : ℕ → ℝ) (t : ℕ) : ℝ := N t * capLabour α (A t) r

/-- Output `Y_t = A_t K_t^α N_t^{1−α}` (labour force `L_t = N_t`), O&R (3.34), p. 156. -/
noncomputable def output (α r : ℝ) (A N : ℕ → ℝ) (t : ℕ) : ℝ :=
  A t * capital α r A N t ^ α * N t ^ (1 - α)

/-- O&R p. 160: under Cobb–Douglas technology, whenever `αA(K/N)^{α−1} = r` the
capital–output ratio is `K/(AK^αN^{1−α}) = α/r`. -/
theorem capital_output_ratio_of_mpk {α A K N r : ℝ} (hK : 0 < K) (hN : 0 < N)
    (hr : 0 < r) (hα0 : 0 < α) (hmpk : α * A * (K / N) ^ (α - 1) = r) :
    K / (A * K ^ α * N ^ (1 - α)) = α / r := by
  have hY : A * K ^ α * N ^ (1 - α) = A * (K / N) ^ (α - 1) * K := by
    rw [Real.div_rpow hK.le hN.le, Real.rpow_sub_one hK.ne',
      show α - 1 = -(1 - α) by ring, Real.rpow_neg hN.le]
    have : 0 < N ^ (1 - α) := Real.rpow_pos_of_pos hN _
    field_simp
  rw [hY, ← hmpk]
  have : 0 < (K / N) ^ (α - 1) := Real.rpow_pos_of_pos (div_pos hK hN) _
  have hA : A ≠ 0 := by
    rintro rfl
    simp at hmpk
    linarith
  field_simp

/-- O&R (3.43)–(3.44) text and footnote 27, p. 160: `Y_t = N_t A_t k(r,A_t)^α`. -/
theorem output_eq_labour_mul {α r : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hr : 0 < r) (hα0 : 0 < α) :
    output α r A N t = N t * A t * capLabour α (A t) r ^ α := by
  have hk : 0 ≤ capLabour α (A t) r := by unfold capLabour; positivity
  unfold output capital
  rw [Real.mul_rpow hN.le hk]
  have hNN : N t ^ α * N t ^ (1 - α) = N t := by
    rw [← Real.rpow_add hN, show α + (1 - α) = 1 by ring, Real.rpow_one]
  calc A t * (N t ^ α * capLabour α (A t) r ^ α) * N t ^ (1 - α)
      = (N t ^ α * N t ^ (1 - α)) * A t * capLabour α (A t) r ^ α := by ring
    _ = N t * A t * capLabour α (A t) r ^ α := by rw [hNN]

/-- O&R p. 160: `K_t/Y_t = α/r` at every date (not only in steady state), whatever the
path of productivity `A_t > 0` and labour force `N_t > 0`. -/
theorem capital_output_ratio {α r : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) :
    capital α r A N t / output α r A N t = α / r := by
  have hk : 0 < capLabour α (A t) r := by unfold capLabour; positivity
  unfold output
  refine capital_output_ratio_of_mpk (mul_pos hN hk) hN hr hα0 ?_
  unfold capital
  rw [show N t * capLabour α (A t) r / N t = capLabour α (A t) r by field_simp]
  exact mpk_capLabour hα0 hα1 hA hr

/-- O&R footnote 27, p. 160: `Y_t = N_t A_t^{1/(1−α)}(α/r)^{α/(1−α)}`. -/
theorem output_closed_form {α r : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) :
    output α r A N t = N t * A t ^ (1 / (1 - α)) * (α / r) ^ (α / (1 - α)) := by
  have h1 : (1 - α) ≠ 0 := by linarith
  have hx : 0 ≤ α * A t / r := by positivity
  rw [output_eq_labour_mul t hA hN hr hα0]
  unfold capLabour
  rw [← Real.rpow_mul hx, show 1 / (1 - α) * α = α / (1 - α) by field_simp,
    show α * A t / r = A t * (α / r) by ring, Real.mul_rpow hA.le (by positivity),
    show 1 / (1 - α) = 1 + α / (1 - α) by field_simp; ring, Real.rpow_add hA,
    Real.rpow_one]
  ring

/-- O&R (3.43) and footnote 27, p. 160: with `A_{t+1} = (1 + g)^{1−α}A_t` and
`N_{t+1} = (1 + n)N_t`, output grows at the gross rate `(1 + n)(1 + g)`. -/
theorem output_growth {α r n g : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) (hg : 0 < 1 + g) (hn : 0 < 1 + n)
    (hAg : A (t + 1) = (1 + g) ^ (1 - α) * A t) (hNn : N (t + 1) = (1 + n) * N t) :
    output α r A N (t + 1) = (1 + n) * (1 + g) * output α r A N t := by
  have h1 : (1 - α) ≠ 0 := by linarith
  have hA1 : 0 < A (t + 1) := by rw [hAg]; positivity
  have hN1 : 0 < N (t + 1) := by rw [hNn]; positivity
  rw [output_closed_form t hA hN hr hα0 hα1, output_closed_form (t + 1) hA1 hN1 hr hα0 hα1,
    hAg, hNn, Real.mul_rpow (by positivity) hA.le, ← Real.rpow_mul hg.le,
    show (1 - α) * (1 / (1 - α)) = 1 by field_simp, Real.rpow_one]
  ring

/-- O&R (3.44), p. 160: the investment share `I_t/Y_t = (K_{t+1} − K_t)/Y_t` equals
`(n + g + ng)α/r` at every date. -/
theorem investment_share {α r n g : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) (hg : 0 < 1 + g) (hn : 0 < 1 + n)
    (hAg : A (t + 1) = (1 + g) ^ (1 - α) * A t) (hNn : N (t + 1) = (1 + n) * N t) :
    (capital α r A N (t + 1) - capital α r A N t) / output α r A N t =
      (n + g + n * g) * (α / r) := by
  have hA1 : 0 < A (t + 1) := by rw [hAg]; positivity
  have hN1 : 0 < N (t + 1) := by rw [hNn]; positivity
  have hY : 0 < output α r A N t := by
    rw [output_closed_form t hA hN hr hα0 hα1]; positivity
  have hK0 := capital_output_ratio t hA hN hr hα0 hα1
  have hK1 := capital_output_ratio (t + 1) hA1 hN1 hr hα0 hα1
  rw [output_growth t hA hN hr hα0 hα1 hg hn hAg hNn] at hK1
  rw [div_eq_iff hY.ne'] at hK0
  rw [div_eq_iff (by positivity)] at hK1
  rw [hK0, hK1]
  field_simp
  ring

/-- Labour's share, O&R p. 160: total wages `N_t w_t` are the fraction `1 − α` of output. -/
theorem wage_bill_share {α r : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) :
    N t * wageOf α (A t) r = (1 - α) * output α r A N t := by
  rw [output_eq_labour_mul t hA hN hr hα0, ← mpl_capLabour hα1 hA hr hα0]
  ring

/-! ### Log utility -/

/-- O&R (3.45), p. 160: with log utility and wage income `w` only when young, the plan
is `c^Y = w/(1 + β)`, `c^O = (1 + r)βw/(1 + β)`, so saving of the young is
`s^Y = w − c^Y = βw/(1 + β)`. -/
theorem log_young_saving (m : LogOLG) (w : ℝ) :
    m.youngC w = w / (1 + m.β) ∧ m.oldC w = (1 + m.r) * m.β * w / (1 + m.β) ∧
      w - m.youngC w = m.β * w / (1 + m.β) := by
  have hb : 1 + m.β ≠ 0 := by linarith [m.β_pos]
  refine ⟨rfl, rfl, ?_⟩
  unfold LogOLG.youngC
  field_simp
  ring

/-- O&R p. 160 ("`s^O_t = −s^Y_{t−1}`"): the old, with no labour income, earn `r s^Y`
on their saving and consume `c^O = (1 + r)s^Y`, so their saving is exactly `−s^Y`. -/
theorem log_old_saving (m : LogOLG) (w : ℝ) :
    m.oldC w = (1 + m.r) * (w - m.youngC w) ∧
      m.r * (w - m.youngC w) - m.oldC w = -(w - m.youngC w) := by
  have hb : 1 + m.β ≠ 0 := by linarith [m.β_pos]
  have h : m.oldC w = (1 + m.r) * (w - m.youngC w) := by
    unfold LogOLG.oldC LogOLG.youngC
    field_simp
    ring
  exact ⟨h, by rw [h]; ring⟩

/-- O&R p. 160, saving of a date-`t` young person with log utility:
`s^Y_t = βw_t/(1 + β) = β(1 − α)A_t^{1/(1−α)}(α/r)^{α/(1−α)}/(1 + β)`. Neither `n` nor
`g` enters (O&R p. 161: "`g` doesn't even enter"). -/
theorem young_saving_closed_form {α β r A : ℝ} (hA : 0 < A) (hr : 0 < r) (hα0 : 0 < α)
    (hα1 : α < 1) :
    β / (1 + β) * wageOf α A r =
      β * (1 - α) * A ^ (1 / (1 - α)) * (α / r) ^ (α / (1 - α)) / (1 + β) := by
  have h1 : (1 - α) ≠ 0 := by linarith
  unfold wageOf
  rw [show α * A / r = A * (α / r) by ring, Real.mul_rpow hA.le (by positivity),
    show 1 / (1 - α) = 1 + α / (1 - α) by field_simp; ring, Real.rpow_add hA,
    Real.rpow_one]
  ring

/-- Aggregate young saving `N_t s^Y_t` with `s^Y_t = βw_t/(1 + β)`, O&R p. 160. -/
noncomputable def youngSaving (α β r : ℝ) (A N : ℕ → ℝ) (t : ℕ) : ℝ :=
  N t * (β / (1 + β) * wageOf α (A t) r)

/-- National saving `S_{t+1} = N_{t+1}s^Y_{t+1} + N_t s^O_{t+1}` with
`s^O_{t+1} = −s^Y_t`, O&R (3.46), p. 160. -/
noncomputable def saving (α β r : ℝ) (A N : ℕ → ℝ) (t : ℕ) : ℝ :=
  youngSaving α β r A N (t + 1) - youngSaving α β r A N t

/-- Net foreign assets `B_{t+1} = N_t s^Y_t − K_{t+1}`, O&R (3.40), p. 158. -/
noncomputable def foreignAssets (α β r : ℝ) (A N : ℕ → ℝ) (t : ℕ) : ℝ :=
  youngSaving α β r A N t - capital α r A N (t + 1)

/-- The steady-state saving rate `β(1−α)/(1+β)·[1 − 1/((1+n)(1+g))]`, O&R (3.46). -/
noncomputable def savingRate (α β n g : ℝ) : ℝ :=
  β * (1 - α) / (1 + β) * (1 - 1 / ((1 + n) * (1 + g)))

/-- The steady-state asset ratio `β(1−α)/((1+β)(1+n)(1+g)) − α/r`, O&R p. 161. -/
noncomputable def assetRatio (α β r n g : ℝ) : ℝ :=
  β * (1 - α) / ((1 + β) * (1 + n) * (1 + g)) - α / r

/-- O&R p. 160: young saving is the constant share `β(1 − α)/(1 + β)` of output. -/
theorem youngSaving_share {α β r : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) :
    youngSaving α β r A N t = β * (1 - α) / (1 + β) * output α r A N t := by
  have h := wage_bill_share t hA hN hr hα0 hα1
  unfold youngSaving
  calc N t * (β / (1 + β) * wageOf α (A t) r)
      = β / (1 + β) * (N t * wageOf α (A t) r) := by ring
    _ = β * (1 - α) / (1 + β) * output α r A N t := by rw [h]; ring

/-- O&R (3.46), p. 160: the national saving rate is
`S/Y = β(1−α)/(1+β)·[1 − 1/((1+n)(1+g))]` at every date. -/
theorem saving_share {α β r n g : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hβ : 0 < β) (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) (hg : 0 < 1 + g) (hn : 0 < 1 + n)
    (hAg : A (t + 1) = (1 + g) ^ (1 - α) * A t) (hNn : N (t + 1) = (1 + n) * N t) :
    saving α β r A N t / output α r A N (t + 1) = savingRate α β n g := by
  have hA1 : 0 < A (t + 1) := by rw [hAg]; positivity
  have hN1 : 0 < N (t + 1) := by rw [hNn]; positivity
  have hY : 0 < output α r A N t := by
    rw [output_closed_form t hA hN hr hα0 hα1]; positivity
  unfold saving savingRate
  rw [youngSaving_share t hA hN hr hα0 hα1, youngSaving_share (t + 1) hA1 hN1 hr hα0 hα1,
    output_growth t hA hN hr hα0 hα1 hg hn hAg hNn]
  have hb : 1 + β ≠ 0 := by linarith
  field_simp

/-- O&R p. 161: net foreign assets relative to output are
`B_{t+1}/Y_{t+1} = β(1−α)/((1+β)(1+n)(1+g)) − α/r` at every date. -/
theorem asset_share {α β r n g : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hβ : 0 < β) (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) (hg : 0 < 1 + g) (hn : 0 < 1 + n)
    (hAg : A (t + 1) = (1 + g) ^ (1 - α) * A t) (hNn : N (t + 1) = (1 + n) * N t) :
    foreignAssets α β r A N t / output α r A N (t + 1) = assetRatio α β r n g := by
  have hA1 : 0 < A (t + 1) := by rw [hAg]; positivity
  have hN1 : 0 < N (t + 1) := by rw [hNn]; positivity
  have hY : 0 < output α r A N t := by
    rw [output_closed_form t hA hN hr hα0 hα1]; positivity
  have hK1 := capital_output_ratio (t + 1) hA1 hN1 hr hα0 hα1
  have hY1 : 0 < output α r A N (t + 1) := by
    rw [output_closed_form (t + 1) hA1 hN1 hr hα0 hα1]; positivity
  rw [div_eq_iff hY1.ne'] at hK1
  unfold foreignAssets assetRatio
  rw [youngSaving_share t hA hN hr hα0 hα1, hK1,
    output_growth t hA hN hr hα0 hα1 hg hn hAg hNn]
  have hb : 1 + β ≠ 0 := by linarith
  field_simp

/-- O&R p. 161: the current account `CA_{t+1} = B_{t+2} − B_{t+1}` satisfies
`CA/Y = S/Y − I/Y = (n + g + ng)·B/Y` at every date, where `S_{t+1}` is `saving … t`
and `I_{t+1} = K_{t+2} − K_{t+1}`. -/
theorem current_account_share {α β r n g : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t)
    (hN : 0 < N t) (hβ : 0 < β) (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) (hg : 0 < 1 + g)
    (hn : 0 < 1 + n) (hAg : ∀ s, A (s + 1) = (1 + g) ^ (1 - α) * A s)
    (hNn : ∀ s, N (s + 1) = (1 + n) * N s) :
    let Y := output α r A N (t + 1)
    (foreignAssets α β r A N (t + 1) - foreignAssets α β r A N t) / Y =
        saving α β r A N t / Y -
          (capital α r A N (t + 2) - capital α r A N (t + 1)) / Y ∧
      (foreignAssets α β r A N (t + 1) - foreignAssets α β r A N t) / Y =
        (n + g + n * g) * assetRatio α β r n g := by
  intro Y
  have hA1 : 0 < A (t + 1) := by rw [hAg]; positivity
  have hN1 : 0 < N (t + 1) := by rw [hNn]; positivity
  have hY1 : 0 < Y := by
    change 0 < output α r A N (t + 1)
    rw [output_closed_form (t + 1) hA1 hN1 hr hα0 hα1]; positivity
  refine ⟨?_, ?_⟩
  · unfold foreignAssets saving
    rw [show t + 1 + 1 = t + 2 from rfl]
    ring
  · have hB0 := asset_share t hA hN hβ hr hα0 hα1 hg hn (hAg t) (hNn t)
    have hB1 := asset_share (t + 1) hA1 hN1 hβ hr hα0 hα1 hg hn (hAg (t + 1))
      (hNn (t + 1))
    have hG := output_growth (t + 1) hA1 hN1 hr hα0 hα1 hg hn (hAg (t + 1)) (hNn (t + 1))
    rw [hG, div_eq_iff (by positivity)] at hB1
    rw [div_eq_iff hY1.ne'] at hB0
    rw [hB1, hB0]
    field_simp
    ring

/-! ### Comparative statics (O&R pp. 160–161) -/

/-- O&R p. 160: "net saving rises when `n` or `g` rises" — the steady-state saving
rate is strictly increasing in `n` (for `β > 0`, `α < 1`, `n, n' > −1`, `g > −1`). -/
theorem savingRate_strictMono_n {α β n n' g : ℝ} (hβ : 0 < β) (hα1 : α < 1)
    (hn : 0 < 1 + n) (hg : 0 < 1 + g) (hnn : n < n') :
    savingRate α β n g < savingRate α β n' g := by
  unfold savingRate
  have hc : 0 < β * (1 - α) / (1 + β) := by
    have : 0 < 1 - α := by linarith
    positivity
  have hlt : 1 / ((1 + n') * (1 + g)) < 1 / ((1 + n) * (1 + g)) :=
    one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  nlinarith

/-- O&R p. 160: the steady-state saving rate is strictly increasing in `g` as well
(`n` and `g` enter symmetrically). -/
theorem savingRate_strictMono_g {α β n g g' : ℝ} (hβ : 0 < β) (hα1 : α < 1)
    (hn : 0 < 1 + n) (hg : 0 < 1 + g) (hgg : g < g') :
    savingRate α β n g < savingRate α β n g' := by
  have h := savingRate_strictMono_n (α := α) (β := β) (g := n) hβ hα1 hg hn hgg
  unfold savingRate at h ⊢
  rwa [mul_comm (1 + g), mul_comm (1 + g')] at h

/-- O&R p. 160: "a rise in either obviously raises investment" — `(n + g + ng)α/r` is
strictly increasing in `n` (for `g > −1`) and in `g` (for `n > −1`), given `α, r > 0`. -/
theorem investShare_strictMono {α r n n' g g' : ℝ} (hα0 : 0 < α) (hr : 0 < r)
    (hn : 0 < 1 + n) (hg : 0 < 1 + g) :
    (n < n' → (n + g + n * g) * (α / r) < (n' + g + n' * g) * (α / r)) ∧
      (g < g' → (n + g + n * g) * (α / r) < (n + g' + n * g') * (α / r)) := by
  have hc : 0 < α / r := by positivity
  refine ⟨fun h => ?_, fun h => ?_⟩
  · apply mul_lt_mul_of_pos_right _ hc
    nlinarith
  · apply mul_lt_mul_of_pos_right _ hc
    nlinarith

/-- O&R p. 161: "more impatient countries (low `β`) tend to have bigger debt-output
ratios" — `B/Y` is strictly increasing in `β > 0`. -/
theorem assetRatio_strictMono_beta {α β β' r n g : ℝ} (hα1 : α < 1) (hβ : 0 < β)
    (hn : 0 < 1 + n) (hg : 0 < 1 + g) (hbb : β < β') :
    assetRatio α β r n g < assetRatio α β' r n g := by
  unfold assetRatio
  have hG : 0 < (1 + n) * (1 + g) := by positivity
  have h1 : 0 < 1 - α := by linarith
  have hβ' : 0 < β' := by linarith
  rw [show β * (1 - α) / ((1 + β) * (1 + n) * (1 + g)) =
      β / (1 + β) * ((1 - α) / ((1 + n) * (1 + g))) by field_simp,
    show β' * (1 - α) / ((1 + β') * (1 + n) * (1 + g)) =
      β' / (1 + β') * ((1 - α) / ((1 + n) * (1 + g))) by field_simp]
  have hq : β / (1 + β) < β' / (1 + β') := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have : 0 < (1 - α) / ((1 + n) * (1 + g)) := by positivity
  nlinarith

/-- O&R p. 161: "the debt-output ratio falls as the world interest rate `r` rises" —
`B/Y` is strictly increasing in `r > 0` (for `α > 0`). -/
theorem assetRatio_strictMono_r {α β r r' n g : ℝ} (hα0 : 0 < α) (hr : 0 < r)
    (hrr : r < r') : assetRatio α β r n g < assetRatio α β r' n g := by
  unfold assetRatio
  have : α / r' < α / r := div_lt_div_of_pos_left hα0 hr hrr
  linarith

/-- O&R p. 161: "the economy may be either debtor or creditor" — it is a debtor
(`B/Y < 0`) iff `β(1 − α)r < α(1 + β)(1 + n)(1 + g)`. -/
theorem assetRatio_neg_iff {α β r n g : ℝ} (hβ : 0 < β) (hr : 0 < r) (hn : 0 < 1 + n)
    (hg : 0 < 1 + g) :
    assetRatio α β r n g < 0 ↔ β * (1 - α) * r < α * ((1 + β) * (1 + n) * (1 + g)) := by
  unfold assetRatio
  have hD : 0 < (1 + β) * (1 + n) * (1 + g) := by
    have : 0 < 1 + β := by linarith
    positivity
  rw [sub_neg, div_lt_div_iff₀ hD hr]

end Growth

end ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Aggregate and intergenerational gains from trade in an OLG economy

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §3.5,
pp. 164–167, and Chapter 3 Exercise 2, p. 195.

A small Diamond economy with log utility `log c^Y + β log c^O`, no government, and a
production sector whose wage is a function `w(r)` of the interest rate (the factor-price
frontier, with `dw/dr = −k`, fn 32; for Cobb–Douglas `Y = A K^α L^(1−α)` the frontier is
`w(r) = (1−α) A (α A / r)^(α/(1−α))` and `k(r) = (α A / r)^(1/(1−α))`).
A generation facing `(w, r)` has lifetime utility `U(r) = (1+β) log w(r) + β log(1+r)`
up to a constant.

**Timing assumption.** Following the book, every generation born on or after the opening
date `t` is treated as a steady-state generation facing the post-opening factor prices
`(w(r), r)`, and the date-`t` old earn the world rate on their saving: the capital stock
jumps to its world-rate level at `t`. If instead date-`t` capital is predetermined at its
autarky level, the date-`t` young still earn the autarky wage and only gain from a rise in
`r` (`dateT_young_predetermined_hasDerivAt`).

Main results:
* (3.47): at the autarky rate `dU/dr = −βr/(1+r) < 0`; the first-period income equivalent
  is `−rk/(1+r)` per generation, with present value `−k` over all generations, exactly
  offsetting the old's gain `k`; a budget-balanced compensation scheme.
* The already-open economy: `dU/dr = −βk/(k+b) + β/(1+r)`; generations gain iff `b > rk`;
  economy-wide gain `(1+r) b / r`.
* Exercise 2(a): with growth `n`, `dU/dr = β(1/(1+r) − 1/(1+n))`, positive iff `r < n`.
* Exercise 2(b): the book's claim that for `n > r^A > r` opening makes *everyone* worse off
  is false as stated: in the Cobb–Douglas case `U(r) → +∞` as `r → 0⁺`, so the young gain
  from a sufficiently low world rate (explicit instance with `α = 1/20`, `β = 9/10`,
  `n = 1/2`). The correct statement holds for `r ∈ [r^A/(1+n−r^A), r^A)`.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade

open Real Filter Set Topology

/-! ## Lifetime utility as a function of the world rate -/

/-- Lifetime utility of a steady-state generation facing the world rate `r`, O&R §3.5,
p. 165: `U(r) = (1+β) log w(r) + β log(1+r)` (apart from an additive constant), where
`w` is the wage schedule (factor-price frontier). -/
noncomputable def lifetimeUtility (β : ℝ) (w : ℝ → ℝ) (r : ℝ) : ℝ :=
  (1 + β) * Real.log (w r) + β * Real.log (1 + r)

/-- O&R §3.5, p. 165: `dU/dr = ((1+β)/w)(dw/dr) + β/(1+r)`, for a positive wage
differentiable at `r` and `r > −1`. -/
theorem hasDerivAt_lifetimeUtility (β : ℝ) (w : ℝ → ℝ) {r w' : ℝ} (hw : 0 < w r)
    (hr : 0 < 1 + r) (hdw : HasDerivAt w w' r) :
    HasDerivAt (lifetimeUtility β w) ((1 + β) * (w' / w r) + β * (1 / (1 + r))) r := by
  have h1 : HasDerivAt (fun x => Real.log (w x)) (w' / w r) r := hdw.log hw.ne'
  have h2 : HasDerivAt (fun x => 1 + x) 1 r := (hasDerivAt_id r).const_add 1
  have h3 : HasDerivAt (fun x => Real.log (1 + x)) (1 / (1 + r)) r := h2.log hr.ne'
  exact HasDerivAt.add (h1.const_mul (1 + β)) (h3.const_mul β)

/-- O&R §3.5, p. 165 with fn 32: along the factor-price frontier `dw/dr = −k`,
`dU/dr = −(1+β) k / w + β/(1+r)`. -/
theorem hasDerivAt_lifetimeUtility_frontier (β : ℝ) (w : ℝ → ℝ) {r k : ℝ} (hw : 0 < w r)
    (hr : 0 < 1 + r) (hdw : HasDerivAt w (-k) r) :
    HasDerivAt (lifetimeUtility β w) (-(1 + β) * k / w r + β / (1 + r)) r := by
  refine (hasDerivAt_lifetimeUtility β w hw hr hdw).congr_deriv ?_
  field_simp

/-- O&R (3.47), p. 165: at the autarky steady state, where the capital-labour ratio
equals the saving of the young, `k = βw/(1+β)`, a marginal rise in the interest rate
changes the lifetime utility of every generation born on or after the opening date by
`dU/dr = −βr/(1+r)`. -/
theorem hasDerivAt_lifetimeUtility_autarky {β : ℝ} (w : ℝ → ℝ) {r k : ℝ} (hβ : 0 < β)
    (hw : 0 < w r) (hr : 0 < 1 + r) (hdw : HasDerivAt w (-k) r)
    (hk : k = β * w r / (1 + β)) :
    HasDerivAt (lifetimeUtility β w) (-(β * r) / (1 + r)) r := by
  refine (hasDerivAt_lifetimeUtility_frontier β w hw hr hdw).congr_deriv ?_
  subst hk
  have : (1 + β) ≠ 0 := by linarith
  field_simp
  ring

/-- O&R (3.47), p. 165: the utility change is strictly negative when `r > 0`, so a
marginal rise of the world rate above the autarky rate hurts the date-`t` young and all
later generations. -/
theorem autarky_utility_slope_neg {β r : ℝ} (hβ : 0 < β) (hr : 0 < r) :
    -(β * r) / (1 + r) < 0 := by
  have : 0 < β * r / (1 + r) := by positivity
  rw [neg_div]; linarith

/-- O&R §3.5, p. 165: the old at the opening date hold capital `k` per person, so their
second-period income `(1+r)k` rises at rate `k` with the interest rate (they gain `k dr`). -/
theorem old_income_hasDerivAt (k r : ℝ) : HasDerivAt (fun x => (1 + x) * k) k r := by
  have h := ((hasDerivAt_id r).const_add 1).mul_const k
  simpa using h

/-! ## Income equivalents, present values and compensation (n = 0) -/

/-- O&R §3.5, p. 165: dividing the utility change `−βr/(1+r)` by the marginal utility of
first-period income `(1+β)/w` gives the first-period income equivalent `−rk/(1+r)`
when `k = βw/(1+β)`; it equals the wage loss `−k` plus the capital-income gain
`k/(1+r)` discounted one period. -/
theorem income_equivalent_autarky {β w k r : ℝ} (hβ : 0 < β) (hw : 0 < w) (hr : 0 < 1 + r)
    (hk : k = β * w / (1 + β)) :
    (-(β * r) / (1 + r)) / ((1 + β) / w) = -(r * k) / (1 + r) ∧
      -k + β * w / ((1 + β) * (1 + r)) = -(r * k) / (1 + r) := by
  subst hk
  have : (1 + β) ≠ 0 := by linarith
  constructor
  · field_simp
  · field_simp
    ring

/-- O&R §3.5, p. 166: the present discounted value, at date `t`, of the per capita income
losses `−rk/(1+r)` of the date-`t` young and all later generations is `−k`, provided
`r > 0` (the geometric series converges). -/
theorem pv_generation_losses {k r : ℝ} (hr : 0 < r) :
    HasSum (fun j : ℕ => -(r * k) / (1 + r) * (1 / (1 + r)) ^ j) (-k) := by
  have hq0 : 0 ≤ 1 / (1 + r) := by positivity
  have hq1 : 1 / (1 + r) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (-(r * k) / (1 + r))
  convert h using 1
  have : (1 + r) ≠ 0 := by linarith
  have h2 : r ≠ 0 := hr.ne'
  rw [one_sub_div this, add_sub_cancel_left, inv_div]
  field_simp

/-- O&R §3.5, p. 166: the aggregate first-order effect of the marginal opening is zero:
the date-`t` old's gain `k` exactly offsets the present value `−k` of all other
generations' losses. -/
theorem aggregate_first_order_zero {k r : ℝ} (hr : 0 < r) :
    HasSum (fun j : ℕ => -(r * k) / (1 + r) * (1 / (1 + r)) ^ j) (-k) ∧ k + -k = 0 :=
  ⟨pv_generation_losses hr, by ring⟩

/-- O&R §3.5, p. 166, the compensation scheme stated precisely: tax each date-`t` old
person `k dr` and give each generation born on or after `t` a transfer `rk dr/(1+r)`
when young. For `r > 0` (i) the present value of the transfers equals the revenue
`k dr`, so the scheme is budget balanced in present value; (ii) every agent's net
first-order income change is zero (old: `k dr − k dr`; each later generation:
`−rk dr/(1+r) + rk dr/(1+r)`), so to first order nobody is worse off. -/
theorem compensation_scheme {k r dr : ℝ} (hr : 0 < r) :
    HasSum (fun j : ℕ => r * k * dr / (1 + r) * (1 / (1 + r)) ^ j) (k * dr) ∧
      k * dr - k * dr = 0 ∧ -(r * k * dr) / (1 + r) + r * k * dr / (1 + r) = 0 := by
  refine ⟨?_, by ring, by ring⟩
  have h := (pv_generation_losses (k := k) hr).mul_left (-dr)
  convert h using 1
  · funext j
    ring
  · ring

/-! ## An economy already open to trade (O&R p. 166) -/

/-- O&R §3.5, p. 166: in an economy already open, the saving of the young `βw/(1+β)`
equals `k + b` (capital plus net foreign assets per worker), and the utility change
becomes `dU/dr = −βk/(k+b) + β/(1+r)`. -/
theorem hasDerivAt_lifetimeUtility_open {β : ℝ} (w : ℝ → ℝ) {r k b : ℝ} (hβ : 0 < β)
    (hw : 0 < w r) (hr : 0 < 1 + r) (hdw : HasDerivAt w (-k) r)
    (hkb : k + b = β * w r / (1 + β)) :
    HasDerivAt (lifetimeUtility β w) (-(β * k) / (k + b) + β / (1 + r)) r := by
  refine (hasDerivAt_lifetimeUtility_frontier β w hw hr hdw).congr_deriv ?_
  rw [hkb]
  have : (1 + β) ≠ 0 := by linarith
  field_simp

/-- O&R §3.5, p. 166: the first-period income equivalent of the utility change in the
open economy is `−k + (k+b)/(1+r)` (per unit `dr`). -/
theorem income_equivalent_open {β w k b r : ℝ} (hβ : 0 < β) (hw : 0 < w)
    (hkb : k + b = β * w / (1 + β)) :
    (-(β * k) / (k + b) + β / (1 + r)) / ((1 + β) / w) = -k + (k + b) / (1 + r) := by
  have hkb0 : k + b ≠ 0 := by rw [hkb]; positivity
  have hw' : w = (1 + β) * (k + b) / β := by
    rw [hkb]; field_simp
  subst hw'
  have : (1 + β) ≠ 0 := by linarith
  field_simp

/-- O&R §3.5, p. 166, made precise: each generation gains from a rise in `r`
(positive income equivalent) if and only if `b > rk` ("b sufficiently positive"). -/
theorem open_generation_gains_iff {k b r : ℝ} (hr : 0 < 1 + r) :
    0 < -k + (k + b) / (1 + r) ↔ r * k < b := by
  rw [show -k + (k + b) / (1 + r) = (b - r * k) / (1 + r) by
    field_simp; ring]
  constructor
  · intro h
    have := (div_pos_iff_of_pos_right hr).mp h
    linarith
  · intro h
    exact div_pos (by linarith) hr

/-- O&R §3.5, pp. 166–167: the gain to the economy as a whole from a rise `dr` in the
world rate is `(1+r) b dr / r`: the date-`t` old gain `(k+b) dr` and the generations born
on or after `t` have present value `(−k + (k+b)/(1+r)) dr (1+r)/r` (for `r > 0`). It is
a loss iff `b < 0`. -/
theorem open_economywide_gain {k b r dr : ℝ} (hr : 0 < r) :
    HasSum (fun j : ℕ => (-k + (k + b) / (1 + r)) * dr * (1 / (1 + r)) ^ j)
        ((-k + (k + b) / (1 + r)) * dr * ((1 + r) / r)) ∧
      (k + b) * dr + (-k + (k + b) / (1 + r)) * dr * ((1 + r) / r) =
        (1 + r) * b * dr / r := by
  have hq0 : 0 ≤ 1 / (1 + r) := by positivity
  have hq1 : 1 / (1 + r) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((-k + (k + b) / (1 + r)) * dr)
  have h1 : (1 + r) ≠ 0 := by linarith
  have h2 : r ≠ 0 := hr.ne'
  refine ⟨?_, ?_⟩
  · convert h using 1
    congr 1
    rw [one_sub_div h1, add_sub_cancel_left, inv_div]
  · field_simp
    ring

/-! ## Timing caveat: predetermined capital at the opening date -/

/-- Timing caveat to O&R §3.5: if date-`t` capital is predetermined at its autarky level,
the date-`t` young earn the autarky wage `w^A` whatever the world rate, and their utility
`(1+β) log w^A + β log(1+r)` has slope `β/(1+r) > 0`: they gain from a rise in `r`,
unlike the steady-state generations of (3.47). -/
theorem dateT_young_predetermined_hasDerivAt (β wA r : ℝ) (hr : 0 < 1 + r) :
    HasDerivAt (fun x => (1 + β) * Real.log wA + β * Real.log (1 + x)) (β / (1 + r)) r ∧
      (0 < β → 0 < β / (1 + r)) := by
  refine ⟨?_, fun hβ => div_pos hβ hr⟩
  have h2 : HasDerivAt (fun x => 1 + x) 1 r := (hasDerivAt_id r).const_add 1
  have h3 := (h2.log hr.ne').const_mul β
  have h4 := h3.const_add ((1 + β) * Real.log wA)
  convert h4 using 1
  field_simp

/-! ## Exercise 2(a): population growth and dynamic inefficiency -/

/-- O&R Ch. 3 Exercise 2(a), p. 195: with labour-force growth `n > −1`, autarky capital
per worker is `k = βw/((1+β)(1+n))`, and at the autarky rate
`dU/dr = β (1/(1+r) − 1/(1+n))`. -/
theorem hasDerivAt_lifetimeUtility_growth {β n : ℝ} (w : ℝ → ℝ) {r k : ℝ} (hβ : 0 < β)
    (hn : 0 < 1 + n) (hw : 0 < w r) (hr : 0 < 1 + r) (hdw : HasDerivAt w (-k) r)
    (hk : k = β * w r / ((1 + β) * (1 + n))) :
    HasDerivAt (lifetimeUtility β w) (β * (1 / (1 + r) - 1 / (1 + n))) r := by
  refine (hasDerivAt_lifetimeUtility_frontier β w hw hr hdw).congr_deriv ?_
  subst hk
  have : (1 + β) ≠ 0 := by linarith
  field_simp
  ring

/-- O&R Ch. 3 Exercise 2(a), p. 195: the slope `β(1/(1+r) − 1/(1+n))` is positive iff
`r < n` (dynamic inefficiency), so when the world rate equals `r^A < n` a small permanent
rise benefits every generation born on or after `t`; the date-`t` old, whose income
`(1+r) s` rises at rate `s > 0`, gain as well (`old_income_hasDerivAt`). -/
theorem growth_slope_pos_iff {β n r : ℝ} (hβ : 0 < β) (hn : 0 < 1 + n) (hr : 0 < 1 + r) :
    0 < β * (1 / (1 + r) - 1 / (1 + n)) ↔ r < n := by
  rw [mul_pos_iff_of_pos_left hβ, sub_pos, one_div_lt_one_div hn hr]
  constructor <;> intro h <;> linarith

/-! ## Cobb–Douglas factor-price frontier -/

/-- Cobb–Douglas wage as a function of the interest rate, O&R §1.5.2 and §3.5 fn 32:
`w(r) = (1−α) A (αA/r)^(α/(1−α))`. -/
noncomputable def wageCD (α A r : ℝ) : ℝ :=
  (1 - α) * A * (α * A / r) ^ (α / (1 - α))

/-- Cobb–Douglas capital-labour ratio as a function of the interest rate, O&R §3.5:
`k(r) = (αA/r)^(1/(1−α))`, from `r = αA k^(α−1)`. -/
noncomputable def capitalCD (α A r : ℝ) : ℝ :=
  (α * A / r) ^ (1 / (1 - α))

/-- O&R §3.5 fn 32, checked directly for Cobb–Douglas: the factor-price frontier has slope
`dw/dr = −k(r)`, for `0 < α < 1`, `A > 0`, `r > 0`. -/
theorem hasDerivAt_wageCD {α A r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hr : 0 < r) : HasDerivAt (wageCD α A) (-capitalCD α A r) r := by
  have h1α : (1 - α) ≠ 0 := by linarith
  have hx : 0 < α * A / r := by positivity
  have hq : HasDerivAt (fun x => α * A / x) (-(α * A) / r ^ 2) r := by
    have := (hasDerivAt_inv hr.ne').const_mul (α * A)
    convert this using 1
    · funext x; simp [div_eq_mul_inv]
    · field_simp
  have hp := hq.rpow_const (p := α / (1 - α)) (Or.inl hx.ne')
  have hw := hp.const_mul ((1 - α) * A)
  unfold wageCD capitalCD
  convert hw using 1
  have he : α / (1 - α) - 1 = 1 / (1 - α) - 2 := by field_simp; ring
  rw [he, Real.rpow_sub hx, Real.rpow_two]
  have hxpos : 0 < (α * A / r) ^ (1 / (1 - α)) := Real.rpow_pos_of_pos hx _
  field_simp

/-- O&R §3.5 (Cobb–Douglas): the ratio of capital to the wage is `k/w = α/((1−α) r)`. -/
theorem capitalCD_div_wageCD {α A r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hr : 0 < r) : capitalCD α A r / wageCD α A r = α / ((1 - α) * r) := by
  have h1α : (1 - α) ≠ 0 := by linarith
  have hx : 0 < α * A / r := by positivity
  have he : 1 / (1 - α) = α / (1 - α) + 1 := by field_simp; ring
  unfold capitalCD wageCD
  rw [he, Real.rpow_add hx, Real.rpow_one]
  have hxpos : 0 < (α * A / r) ^ (α / (1 - α)) := Real.rpow_pos_of_pos hx _
  field_simp

/-- O&R §3.5 (Cobb–Douglas): the wage is positive for `0 < α < 1`, `A > 0`, `r > 0`. -/
theorem wageCD_pos {α A r : ℝ} (hα1 : α < 1) (hA : 0 < A) (hx : 0 < α * A / r) :
    0 < wageCD α A r := by
  unfold wageCD
  have : 0 < 1 - α := by linarith
  have := Real.rpow_pos_of_pos hx (α / (1 - α))
  positivity

/-- O&R Ch. 3 Exercise 2 (Cobb–Douglas): the autarky steady-state interest rate with
growth `n`, `r^A = α(1+β)(1+n)/((1−α)β)`. -/
noncomputable def autarkyRateCD (α β n : ℝ) : ℝ :=
  α * (1 + β) * (1 + n) / ((1 - α) * β)

/-- O&R Ch. 3 Exercise 2 hint (Cobb–Douglas): at `r = r^A` the capital-labour ratio
satisfies the autarky condition `k = βw/((1+β)(1+n))`. -/
theorem capitalCD_autarky {α β n A : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hn : 0 < 1 + n) (hA : 0 < A) :
    capitalCD α A (autarkyRateCD α β n) =
      β * wageCD α A (autarkyRateCD α β n) / ((1 + β) * (1 + n)) := by
  have h1α : 0 < 1 - α := by linarith
  have hrA : 0 < autarkyRateCD α β n := by unfold autarkyRateCD; positivity
  have hwpos := wageCD_pos (r := autarkyRateCD α β n) hα1 hA (by positivity)
  have hratio := capitalCD_div_wageCD hα0 hα1 hA hrA
  rw [div_eq_iff hwpos.ne'] at hratio
  rw [hratio]
  unfold autarkyRateCD
  field_simp

/-! ## Exercise 2(b): the Cobb–Douglas welfare function and the counterexample -/

/-- O&R Ch. 3 Exercise 2(b) (Cobb–Douglas): lifetime utility is, up to a constant `C`,
`U(r) = C − (1+β)(α/(1−α)) log r + β log(1+r)`. -/
theorem lifetimeUtility_wageCD {α β A r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hr : 0 < r) :
    lifetimeUtility β (wageCD α A) r =
      (1 + β) * (Real.log ((1 - α) * A) + α / (1 - α) * Real.log (α * A)) -
        (1 + β) * (α / (1 - α)) * Real.log r + β * Real.log (1 + r) := by
  have h1α : 0 < 1 - α := by linarith
  have hx : 0 < α * A / r := by positivity
  unfold lifetimeUtility wageCD
  rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hx _).ne', Real.log_rpow hx,
    Real.log_div (by positivity) hr.ne']
  ring

/-- O&R Ch. 3 Exercise 2(b) (Cobb–Douglas): the slope of lifetime utility at any `r > 0`
is `dU/dr = β (1/(1+r) − r^A/((1+n) r))`. -/
theorem hasDerivAt_lifetimeUtility_CD {α β n A r : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hn : 0 < 1 + n) (hA : 0 < A) (hr : 0 < r) :
    HasDerivAt (lifetimeUtility β (wageCD α A))
      (β * (1 / (1 + r) - autarkyRateCD α β n / ((1 + n) * r))) r := by
  have hwpos := wageCD_pos (r := r) hα1 hA (by positivity)
  have h := hasDerivAt_lifetimeUtility_frontier β (wageCD α A) hwpos (by linarith)
    (hasDerivAt_wageCD hα0 hα1 hA hr)
  refine h.congr_deriv ?_
  have hratio := capitalCD_div_wageCD hα0 hα1 hA hr
  have h1α : (1 - α) ≠ 0 := by linarith
  rw [show -(1 + β) * capitalCD α A r / wageCD α A r =
      -(1 + β) * (capitalCD α A r / wageCD α A r) by ring, hratio]
  unfold autarkyRateCD
  field_simp
  ring

/-- The threshold `r* = r^A/(1+n−r^A)` of O&R Ch. 3 Exercise 2(b) (Cobb–Douglas) at which
lifetime utility is minimised. -/
noncomputable def utilityMinRateCD (α β n : ℝ) : ℝ :=
  autarkyRateCD α β n / (1 + n - autarkyRateCD α β n)

/-- O&R Ch. 3 Exercise 2(b) (Cobb–Douglas): sign of the slope. For `r > 0` and
`r^A < 1+n`, `dU/dr > 0` iff `r > r^A/(1+n−r^A)`. -/
theorem slope_CD_pos_iff {α β n r : ℝ} (hβ : 0 < β) (hn : 0 < 1 + n) (hr : 0 < r)
    (hA1 : autarkyRateCD α β n < 1 + n) :
    0 < β * (1 / (1 + r) - autarkyRateCD α β n / ((1 + n) * r)) ↔
      utilityMinRateCD α β n < r := by
  set rA := autarkyRateCD α β n
  have hd : 0 < 1 + n - rA := by linarith
  unfold utilityMinRateCD
  rw [mul_pos_iff_of_pos_left hβ, sub_pos, div_lt_div_iff₀ (by positivity) (by linarith),
    div_lt_iff₀ hd]
  constructor <;> intro h <;> nlinarith

/-- O&R Ch. 3 Exercise 2(b) (Cobb–Douglas): lifetime utility is strictly increasing in the
world rate on `[r*, ∞)`, `r* = r^A/(1+n−r^A)`, when `0 < r^A < 1+n`. -/
theorem lifetimeUtility_CD_strictMonoOn {α β n A : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hn : 0 < 1 + n) (hA : 0 < A) (hA1 : autarkyRateCD α β n < 1 + n) :
    StrictMonoOn (lifetimeUtility β (wageCD α A)) (Ici (utilityMinRateCD α β n)) := by
  have hrA : 0 < autarkyRateCD α β n := by
    unfold autarkyRateCD; have : 0 < 1 - α := by linarith
    positivity
  have hstar : 0 < utilityMinRateCD α β n := by
    unfold utilityMinRateCD; exact div_pos hrA (by linarith)
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hstar hx
    exact (hasDerivAt_lifetimeUtility_CD (n := n) hα0 hα1 hβ hn hA hx0).continuousAt
      |>.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := lt_trans hstar hx
    rw [(hasDerivAt_lifetimeUtility_CD (n := n) hα0 hα1 hβ hn hA hx0).deriv]
    exact (slope_CD_pos_iff hβ hn hx0 hA1).mpr hx

/-- O&R Ch. 3 Exercise 2(b) (Cobb–Douglas): lifetime utility is strictly decreasing in the
world rate on `(0, r*]`, `r* = r^A/(1+n−r^A)`, when `0 < r^A < 1+n`. -/
theorem lifetimeUtility_CD_strictAntiOn {α β n A : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hn : 0 < 1 + n) (hA : 0 < A) (hA1 : autarkyRateCD α β n < 1 + n) :
    StrictAntiOn (lifetimeUtility β (wageCD α A)) (Ioc 0 (utilityMinRateCD α β n)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc _ _)
  · intro x hx
    exact (hasDerivAt_lifetimeUtility_CD (n := n) hα0 hα1 hβ hn hA hx.1).continuousAt
      |>.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    rw [(hasDerivAt_lifetimeUtility_CD (n := n) hα0 hα1 hβ hn hA hx.1).deriv]
    have h := (slope_CD_pos_iff (r := x) hβ hn hx.1 hA1).not
    push Not at h
    rcases (h.mpr hx.2.le).lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have hβ' : β ≠ 0 := hβ.ne'
      have hsub := (mul_eq_zero.mp h').resolve_left hβ'
      set rA := autarkyRateCD α β n
      have hd : 0 < 1 + n - rA := by linarith
      have hx1 := hx.1
      have hx2 := hx.2
      unfold utilityMinRateCD at hx2
      rw [lt_div_iff₀ hd] at hx2
      rw [sub_eq_zero, div_eq_div_iff (by linarith) (by positivity)] at hsub
      nlinarith

/-- O&R Ch. 3 Exercise 2(b), corrected (Cobb–Douglas): if `r^A < n` then
`r* = r^A/(1+n−r^A) < r^A`, and for every world rate `r ∈ [r*, r^A)` opening to trade makes
everyone worse off: every steady-state generation (`U(r) < U(r^A)`) and the date-`t` old,
whose income `(1+r)s` on autarky saving `s > 0` falls. -/
theorem everyone_worse_off_corrected {α β n A r s : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hn : 0 < 1 + n) (hA : 0 < A) (hs : 0 < s)
    (hAn : autarkyRateCD α β n < n) (hr1 : utilityMinRateCD α β n ≤ r)
    (hr2 : r < autarkyRateCD α β n) :
    utilityMinRateCD α β n < autarkyRateCD α β n ∧
      lifetimeUtility β (wageCD α A) r <
        lifetimeUtility β (wageCD α A) (autarkyRateCD α β n) ∧
      (1 + r) * s < (1 + autarkyRateCD α β n) * s := by
  have hA1 : autarkyRateCD α β n < 1 + n := by linarith
  have hrA : 0 < autarkyRateCD α β n := by
    unfold autarkyRateCD; have : 0 < 1 - α := by linarith
    positivity
  have hlt : utilityMinRateCD α β n < autarkyRateCD α β n := by
    unfold utilityMinRateCD
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  refine ⟨hlt, ?_, by nlinarith⟩
  exact lifetimeUtility_CD_strictMonoOn hα0 hα1 hβ hn hA hA1 hr1 (le_of_lt hlt) hr2

/-- O&R Ch. 3 Exercise 2(b) refuted (Cobb–Douglas): lifetime utility tends to `+∞` as the
world rate falls to zero, because the wage `w(r) ∝ r^(−α/(1−α))` explodes. -/
theorem lifetimeUtility_CD_tendsto_atTop {α β A : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hA : 0 < A) :
    Tendsto (lifetimeUtility β (wageCD α A)) (𝓝[>] 0) atTop := by
  have h1α : 0 < 1 - α := by linarith
  set C := (1 + β) * (Real.log ((1 - α) * A) + α / (1 - α) * Real.log (α * A))
  set c := (1 + β) * (α / (1 - α))
  have hc : 0 < c := by positivity
  have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      C + (-c * Real.log r + β * Real.log (1 + r)) = lifetimeUtility β (wageCD α A) r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [lifetimeUtility_wageCD hα0 hα1 hA hr]
    ring
  refine Tendsto.congr' heq ?_
  refine tendsto_atTop_add_const_left _ C ?_
  have hlog : Tendsto (fun r => -c * Real.log r) (𝓝[>] 0) atTop :=
    Real.tendsto_log_nhdsGT_zero.const_mul_atBot_of_neg (by linarith)
  have hcont :
      Tendsto (fun r : ℝ => β * Real.log (1 + r)) (𝓝[>] 0) (𝓝 (β * Real.log 1)) := by
    have : ContinuousAt (fun r : ℝ => β * Real.log (1 + r)) 0 := by
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.log (continuousAt_const.add continuousAt_id)
      norm_num
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  exact hlog.atTop_add hcont

/-- O&R Ch. 3 Exercise 2(b) refuted (Cobb–Douglas): for any parameters and any autarky
rate `r^A > 0` there is a world rate `r ∈ (0, r^A)` at which every steady-state generation
is strictly better off than in autarky. Hence "opening to trade makes everyone worse off
whenever `n > r^A > r`" is false. -/
theorem exists_rate_below_autarky_young_gain {α β A rA : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hA : 0 < A) (hrA : 0 < rA) :
    ∃ r ∈ Ioo 0 rA,
      lifetimeUtility β (wageCD α A) rA < lifetimeUtility β (wageCD α A) r := by
  have h1 := (lifetimeUtility_CD_tendsto_atTop hα0 hα1 hβ hA).eventually_gt_atTop
    (lifetimeUtility β (wageCD α A) rA)
  have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 rA := Ioo_mem_nhdsGT hrA
  obtain ⟨r, hr1, hr2⟩ := (h2.and h1).exists
  exact ⟨r, hr1, hr2⟩

/-- O&R Ch. 3 Exercise 2(b), explicit counterexample: with `α = 1/20`, `β = 9/10`,
`n = 1/2`, the autarky rate is `r^A = 1/6 < n`, yet at the world rate `r = e^(−7) < r^A`
every steady-state generation is strictly better off than in autarky. -/
theorem counterexample_everyone_worse_off {A : ℝ} (hA : 0 < A) :
    autarkyRateCD (1 / 20) (9 / 10) (1 / 2) = 1 / 6 ∧ (1 / 6 : ℝ) < 1 / 2 ∧
      Real.exp (-7) < 1 / 6 ∧
      lifetimeUtility (9 / 10) (wageCD (1 / 20) A) (1 / 6) <
        lifetimeUtility (9 / 10) (wageCD (1 / 20) A) (Real.exp (-7)) := by
  have he7 : Real.exp (-7) < 1 / 6 := by
    have h7 : (7 : ℝ) + 1 ≤ Real.exp 7 := Real.add_one_le_exp 7
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 7) (by norm_num)]
    linarith
  refine ⟨by unfold autarkyRateCD; norm_num, by norm_num, he7, ?_⟩
  rw [lifetimeUtility_wageCD (by norm_num) (by norm_num) hA (by norm_num),
    lifetimeUtility_wageCD (by norm_num) (by norm_num) hA (Real.exp_pos _), Real.log_exp]
  have hl6 : Real.log (1 / 6) = -Real.log 6 := by
    rw [one_div, Real.log_inv]
  have h6 : Real.log 6 ≤ 6 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h76 : Real.log (1 + 1 / 6) ≤ (1 + 1 / 6) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hpos : 0 < Real.log (1 + Real.exp (-7)) :=
    Real.log_pos (by linarith [Real.exp_pos (-7)])
  rw [hl6]
  norm_num at h76 ⊢
  nlinarith

end ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Public debt and the world interest rate in a two-country OLG model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §3.6,
pp. 167–174 (Figs 3.5–3.6), and Chapter 3 Exercise 4, p. 197.

Two countries share Cobb–Douglas technology `y = k^α` (`A = 1`), log preferences
and the population growth rate `n`; only the young are taxed.  With integrated
capital markets the capital-labour ratios equalise (O&R (3.50)) and the world
capital-labour ratio follows (O&R (3.52))
`k_{t+1} = Ψ(k_t) = β(1-α)/((1+n)(1+β)) · k_t^α`.
With Home government debt per worker `d̄` financed by taxes on the young
(`τ = (r - n)d̄`, O&R (3.54)) the law of motion becomes (p. 170)
`Ψ(k, d̄) = β[(1-α)k^α - x(αk^{α-1} - n)d̄]/((1+n)(1+β)) - x d̄`,
with `x` Home's share of world labour.

Main results:
* global monotone convergence of the debt-free map to `k̄` (Fig 3.5, proved here);
* `Ψ(·, d̄)` is strictly increasing and strictly concave; two positive steady states
  exist when `Ψ(k, d̄) > k` somewhere, the upper one attracts every orbit starting above
  the lower one; no positive steady state exists when the debt is large (a threshold the
  book omits);
* crowding out: debt lowers the upper steady state and raises the world interest rate.
  In fact `∂Ψ/∂d̄ < 0` at every `k > 0`, for any `r` (not only `r ≥ n`);
* §3.6.4: `r̄ ≤ n` exactly when `α` is below an explicit threshold, and `r̄ → 0` as `α → 0`;
* Exercise 4 (a precise piece): the steady-state lifetime utility of the untaxed Foreign
  young rises with `k` if and only if `β(1-α)r < α(1+β)(1+r)`; so when
  `α(1+β) ≥ β(1-α)` Home debt strictly lowers Foreign steady-state welfare, while for small
  `α` and high `r` it can raise it.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG

open Filter Topology Set

/-- The two-country OLG world of O&R §3.6.1, p. 167: capital share `α ∈ (0,1)`,
discount factor `β > 0`, common population growth `n > -1`, Home labour share
`x ∈ (0,1]` (p. 170). -/
structure TwoCountry where
  α : ℝ
  β : ℝ
  n : ℝ
  x : ℝ
  α_pos : 0 < α
  α_lt_one : α < 1
  β_pos : 0 < β
  n_gt : -1 < n
  x_pos : 0 < x
  x_le_one : x ≤ 1

/-! ## Generic monotone convergence of one-dimensional maps -/

/-- Monotone convergence from below (the staircase of O&R Fig 3.5, p. 169): if `f p = p`,
`k < f k < p` on `(a, p)` and `f` is continuous on `(a, p]`, then every orbit starting in
`(a, p]` is nondecreasing and converges to `p`. -/
theorem iterate_tendsto_of_below {f : ℝ → ℝ} {a p k0 : ℝ} (hfp : f p = p)
    (hbelow : ∀ k, a < k → k < p → k < f k ∧ f k < p)
    (hcont : ∀ k, a < k → k ≤ p → ContinuousAt f k) (ha : a < k0) (hp : k0 ≤ p) :
    Monotone (fun t : ℕ => f^[t] k0) ∧ Tendsto (fun t : ℕ => f^[t] k0) atTop (𝓝 p) := by
  have aux : ∀ y, k0 ≤ y → y ≤ p → y ≤ f y ∧ f y ≤ p := by
    intro y hy1 hy2
    rcases hy2.lt_or_eq with h | h
    · exact ⟨(hbelow y (ha.trans_le hy1) h).1.le, (hbelow y (ha.trans_le hy1) h).2.le⟩
    · rw [h, hfp]; exact ⟨le_rfl, le_rfl⟩
  have hmem : ∀ t : ℕ, k0 ≤ f^[t] k0 ∧ f^[t] k0 ≤ p := by
    intro t
    induction t with
    | zero => exact ⟨le_rfl, hp⟩
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨ih.1.trans (aux _ ih.1 ih.2).1, (aux _ ih.1 ih.2).2⟩
  have hmono : Monotone (fun t : ℕ => f^[t] k0) := by
    refine monotone_nat_of_le_succ fun t => ?_
    simp only [Function.iterate_succ_apply']
    exact (aux _ (hmem t).1 (hmem t).2).1
  refine ⟨hmono, ?_⟩
  have hbdd : BddAbove (range fun t : ℕ => f^[t] k0) := ⟨p, by
    rintro _ ⟨t, rfl⟩; exact (hmem t).2⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ t : ℕ, f^[t] k0 with hL
  have hLp : L ≤ p := ciSup_le fun t => (hmem t).2
  have hk0L : k0 ≤ L := le_ciSup_of_le hbdd 0 le_rfl
  have hshift : Tendsto (fun t : ℕ => f (f^[t] k0)) atTop (𝓝 L) := by
    have := hlim.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun t => ?_
    simp [Function.iterate_succ_apply']
  have hfL : f L = L :=
    tendsto_nhds_unique ((hcont L (ha.trans_le hk0L) hLp).tendsto.comp hlim) hshift
  rcases hLp.lt_or_eq with h | h
  · exact absurd hfL (hbelow L (ha.trans_le hk0L) h).1.ne'
  · rw [← h]; exact hlim

/-- Monotone convergence from above (O&R Fig 3.5, p. 169): if `f p = p`, `p < f k < k`
for `k > p` and `f` is continuous on `[p, ∞)`, every orbit starting at `k0 ≥ p` is
nonincreasing and converges to `p`. -/
theorem iterate_tendsto_of_above {f : ℝ → ℝ} {p k0 : ℝ} (hfp : f p = p)
    (habove : ∀ k, p < k → p < f k ∧ f k < k)
    (hcont : ∀ k, p ≤ k → ContinuousAt f k) (hp : p ≤ k0) :
    Antitone (fun t : ℕ => f^[t] k0) ∧ Tendsto (fun t : ℕ => f^[t] k0) atTop (𝓝 p) := by
  have aux : ∀ y, p ≤ y → f y ≤ y ∧ p ≤ f y := by
    intro y hy
    rcases hy.lt_or_eq with h | h
    · exact ⟨(habove y h).2.le, (habove y h).1.le⟩
    · rw [← h, hfp]; exact ⟨le_rfl, le_rfl⟩
  have hmem : ∀ t : ℕ, p ≤ f^[t] k0 := by
    intro t
    induction t with
    | zero => exact hp
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact (aux _ ih).2
  have hanti : Antitone (fun t : ℕ => f^[t] k0) := by
    refine antitone_nat_of_succ_le fun t => ?_
    simp only [Function.iterate_succ_apply']
    exact (aux _ (hmem t)).1
  refine ⟨hanti, ?_⟩
  have hbdd : BddBelow (range fun t : ℕ => f^[t] k0) := ⟨p, by
    rintro _ ⟨t, rfl⟩; exact hmem t⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ t : ℕ, f^[t] k0 with hL
  have hpL : p ≤ L := le_ciInf fun t => hmem t
  have hshift : Tendsto (fun t : ℕ => f (f^[t] k0)) atTop (𝓝 L) := by
    have := hlim.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun t => ?_
    simp [Function.iterate_succ_apply']
  have hfL : f L = L := tendsto_nhds_unique ((hcont L hpL).tendsto.comp hlim) hshift
  rcases hpL.lt_or_eq with h | h
  · exact absurd hfL (habove L h).2.ne
  · rw [h]; exact hlim

/-- Strict concavity on `(0, ∞)` in secant form: for `0 < a < z < b` the chord lies strictly
below the graph (used for the steady-state pattern of O&R Fig 3.6, p. 171). -/
theorem strictConcave_chord_lt {g : ℝ → ℝ} (hg : StrictConcaveOn ℝ (Ioi 0) g) {a z b : ℝ}
    (ha : 0 < a) (haz : a < z) (hzb : z < b) :
    (b - z) / (b - a) * g a + (z - a) / (b - a) * g b < g z := by
  have hba : 0 < b - a := by linarith
  have h := hg.2 (mem_Ioi.2 ha) (mem_Ioi.2 (ha.trans (haz.trans hzb))) (by linarith)
    (div_pos (by linarith : (0 : ℝ) < b - z) hba) (div_pos (by linarith : (0 : ℝ) < z - a) hba)
    (by field_simp; ring)
  have hz : (b - z) / (b - a) * a + (z - a) / (b - a) * b = z := by field_simp; ring
  simp only [smul_eq_mul] at h
  rwa [hz] at h

namespace TwoCountry

variable (e : TwoCountry)

/-! ## The debt-free world economy (O&R §3.6.2) -/

/-- The slope coefficient `β(1-α)/((1+n)(1+β))` of O&R (3.52), p. 169. -/
noncomputable def coef : ℝ := e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β))

/-- The debt-free law of motion `Ψ(k) = β(1-α)k^α/((1+n)(1+β))`, O&R (3.52), p. 169. -/
noncomputable def psi (k : ℝ) : ℝ := e.coef * k ^ e.α

/-- The positive steady state `k̄ = [β(1-α)/((1+n)(1+β))]^{1/(1-α)}`, O&R p. 169. -/
noncomputable def kbar : ℝ := e.coef ^ (1 / (1 - e.α))

/-- The world interest rate `r = αk^{α-1}`, O&R (3.50), p. 168. -/
noncomputable def rate (k : ℝ) : ℝ := e.α * k ^ (e.α - 1)

/-- The coefficient `β(1-α)/((1+n)(1+β))` is positive (O&R (3.52), p. 169). -/
theorem coef_pos : 0 < e.coef := by
  have := e.α_lt_one; have := e.β_pos; have := e.n_gt
  unfold coef
  apply div_pos (mul_pos e.β_pos (by linarith)) (mul_pos (by linarith) (by linarith))

/-- `k̄ > 0` (O&R p. 169). -/
theorem kbar_pos : 0 < e.kbar := Real.rpow_pos_of_pos e.coef_pos _

/-- The zero capital stock is a steady state, `Ψ(0) = 0` (O&R p. 169). -/
theorem psi_zero : e.psi 0 = 0 := by
  simp [psi, Real.zero_rpow e.α_pos.ne']

/-- `k̄` is a steady state of O&R (3.52), p. 169: `Ψ(k̄) = k̄`. -/
theorem psi_kbar : e.psi e.kbar = e.kbar := by
  have hc := e.coef_pos
  have h1 : 1 - e.α ≠ 0 := by have := e.α_lt_one; linarith
  unfold psi kbar
  rw [← Real.rpow_mul hc.le]
  conv_lhs => arg 1; rw [← Real.rpow_one e.coef]
  rw [← Real.rpow_add hc]
  congr 1
  field_simp
  ring

/-- `k̄` is the UNIQUE positive steady state of O&R (3.52), p. 169. -/
theorem psi_fixed_iff {k : ℝ} (hk : 0 < k) : e.psi k = k ↔ k = e.kbar := by
  refine ⟨fun h => ?_, fun h => h ▸ e.psi_kbar⟩
  have h1 : 1 - e.α ≠ 0 := by have := e.α_lt_one; linarith
  have hsplit : k = k ^ (1 - e.α) * k ^ e.α := by
    rw [← Real.rpow_add hk]; simp
  have hc : e.coef = k ^ (1 - e.α) := by
    have hpos : 0 < k ^ e.α := Real.rpow_pos_of_pos hk _
    unfold psi at h
    have : e.coef * k ^ e.α = k ^ (1 - e.α) * k ^ e.α := h.trans hsplit
    exact mul_right_cancel₀ hpos.ne' this
  unfold kbar
  rw [hc, ← Real.rpow_mul hk.le, mul_one_div_cancel h1, Real.rpow_one]

/-- `Ψ` is strictly increasing on `[0, ∞)` (O&R Fig 3.5, p. 169). -/
theorem psi_strictMonoOn : StrictMonoOn e.psi (Ici 0) := by
  intro a ha b _ hab
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow ha hab e.α_pos) e.coef_pos

/-- `coef · k̄^α / k̄ = 1`, a restatement of the fixed point (O&R p. 169). -/
theorem coef_kbar_div : e.coef * e.kbar ^ e.α / e.kbar = 1 := by
  have := e.psi_kbar
  unfold psi at this
  rw [this, div_self e.kbar_pos.ne']

/-- Below `k̄` capital rises but stays below `k̄`: `0 < k < k̄ ⇒ k < Ψ(k) < k̄`
(O&R Fig 3.5, p. 169). -/
theorem psi_between_below {k : ℝ} (hk : 0 < k) (hlt : k < e.kbar) :
    k < e.psi k ∧ e.psi k < e.kbar := by
  refine ⟨?_, e.psi_kbar ▸ e.psi_strictMonoOn (mem_Ici.2 hk.le) (mem_Ici.2 e.kbar_pos.le) hlt⟩
  have hdec : e.kbar ^ (e.α - 1) < k ^ (e.α - 1) :=
    Real.rpow_lt_rpow_of_neg hk hlt (by linarith [e.α_lt_one])
  rw [Real.rpow_sub_one hk.ne', Real.rpow_sub_one e.kbar_pos.ne'] at hdec
  have h1 : 1 < e.coef * k ^ e.α / k := by
    rw [← e.coef_kbar_div, mul_div_assoc, mul_div_assoc]
    exact mul_lt_mul_of_pos_left hdec e.coef_pos
  unfold psi
  rwa [lt_div_iff₀ hk, one_mul] at h1

/-- Above `k̄` capital falls but stays above `k̄`: `k̄ < k ⇒ k̄ < Ψ(k) < k`
(O&R Fig 3.5, p. 169). -/
theorem psi_between_above {k : ℝ} (hgt : e.kbar < k) :
    e.kbar < e.psi k ∧ e.psi k < k := by
  have hk : 0 < k := e.kbar_pos.trans hgt
  refine ⟨e.psi_kbar ▸ e.psi_strictMonoOn (mem_Ici.2 e.kbar_pos.le) (mem_Ici.2 hk.le) hgt, ?_⟩
  have hdec : k ^ (e.α - 1) < e.kbar ^ (e.α - 1) :=
    Real.rpow_lt_rpow_of_neg e.kbar_pos hgt (by linarith [e.α_lt_one])
  rw [Real.rpow_sub_one hk.ne', Real.rpow_sub_one e.kbar_pos.ne'] at hdec
  have h1 : e.coef * k ^ e.α / k < 1 := by
    rw [← e.coef_kbar_div, mul_div_assoc, mul_div_assoc]
    exact mul_lt_mul_of_pos_left hdec e.coef_pos
  unfold psi
  rwa [div_lt_iff₀ hk, one_mul] at h1

/-- `Ψ` is continuous (O&R (3.52), p. 169). -/
theorem psi_continuous : Continuous e.psi :=
  continuous_const.mul (Real.continuous_rpow_const e.α_pos.le)

/-- Global stability, O&R Fig 3.5, p. 169: from ANY `k_0 > 0` the world capital-labour ratio
converges to `k̄`, monotonically (increasing if `k_0 ≤ k̄`, decreasing if `k_0 ≥ k̄`). -/
theorem psi_global_convergence {k0 : ℝ} (hk0 : 0 < k0) :
    Tendsto (fun t : ℕ => e.psi^[t] k0) atTop (𝓝 e.kbar) ∧
      (k0 ≤ e.kbar → Monotone (fun t : ℕ => e.psi^[t] k0)) ∧
      (e.kbar ≤ k0 → Antitone (fun t : ℕ => e.psi^[t] k0)) := by
  have hbelow : ∀ k, 0 < k → k < e.kbar → k < e.psi k ∧ e.psi k < e.kbar :=
    fun k hk hlt => e.psi_between_below hk hlt
  have hcont : ∀ k : ℝ, ContinuousAt e.psi k := fun k => e.psi_continuous.continuousAt
  refine ⟨?_, fun h => (iterate_tendsto_of_below e.psi_kbar hbelow
      (fun k _ _ => hcont k) hk0 h).1,
    fun h => (iterate_tendsto_of_above e.psi_kbar (fun k hk => e.psi_between_above hk)
      (fun k _ => hcont k) h).1⟩
  rcases le_total k0 e.kbar with h | h
  · exact (iterate_tendsto_of_below e.psi_kbar hbelow (fun k _ _ => hcont k) hk0 h).2
  · exact (iterate_tendsto_of_above e.psi_kbar (fun k hk => e.psi_between_above hk)
      (fun k _ => hcont k) h).2

/-- The zero steady state is unstable (O&R p. 169): no orbit from `k_0 > 0` converges
to `0`. -/
theorem zero_unstable {k0 : ℝ} (hk0 : 0 < k0) :
    ¬ Tendsto (fun t : ℕ => e.psi^[t] k0) atTop (𝓝 0) := fun h =>
  e.kbar_pos.ne' (tendsto_nhds_unique (e.psi_global_convergence hk0).1 h)

/-- The steady-state interest rate as a function of the primitives, O&R (3.53), p. 169:
`r̄ = α(1+n)(1+β)/(β(1-α))`. -/
noncomputable def rbarOf (α β n : ℝ) : ℝ := α * (1 + n) * (1 + β) / (β * (1 - α))

/-- O&R (3.53), p. 169: the marginal product of capital at `k̄` is
`α(k̄)^{α-1} = α(1+n)(1+β)/(β(1-α))`. -/
theorem rate_kbar : e.rate e.kbar = rbarOf e.α e.β e.n := by
  have hc := e.coef_pos
  have h1 : 1 - e.α ≠ 0 := by have := e.α_lt_one; linarith
  have hpow : e.kbar ^ (e.α - 1) = e.coef⁻¹ := by
    unfold kbar
    rw [← Real.rpow_mul hc.le, ← Real.rpow_neg_one]
    congr 1
    field_simp
    ring
  have := e.β_pos; have := e.n_gt
  have h2 : (1 + e.n) ≠ 0 := by linarith
  have h3 : (1 + e.β) ≠ 0 := by linarith
  unfold rate rbarOf
  rw [hpow]
  unfold coef
  field_simp

/-! ## Public debt (O&R §3.6.3) -/

/-- O&R (3.54), p. 170: keeping government debt per worker constant at `d̄`
(`-B_t = d̄N_t`, `-B_{t+1} = d̄(1+n)N_t`) under the budget `B_{t+1} = (1+r)B_t + N_tτ`
requires the tax on each young worker `τ = (r - n)d̄`. -/
theorem tax_eq {B B' N τ r n d : ℝ} (hN : N ≠ 0) (hB : B = -(d * N))
    (hB' : B' = -(d * ((1 + n) * N))) (hbud : B' = (1 + r) * B + N * τ) :
    τ = (r - n) * d := by
  rw [hB, hB'] at hbud
  have h : N * (τ - (r - n) * d) = 0 := by linear_combination -hbud
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h hN
  · linarith

/-- The law of motion with Home debt, O&R p. 170:
`Ψ(k, d̄) = β[(1-α)k^α - x(αk^{α-1} - n)d̄]/((1+n)(1+β)) - x d̄`. -/
noncomputable def psiDebt (d k : ℝ) : ℝ :=
  e.β * ((1 - e.α) * k ^ e.α - e.x * (e.α * k ^ (e.α - 1) - e.n) * d) /
    ((1 + e.n) * (1 + e.β)) - e.x * d

/-- Derivation of the debt law of motion, O&R (3.55) and p. 170: with Home saving
`s = β[w - (r - n)d̄]/(1+β)`, Foreign saving `s* = βw/(1+β)`, `w = (1-α)k^α`,
`r = αk^{α-1}`, and world asset-market clearing `K' + K*' + d̄N_{t+1} = Ns + N*s*`, the
next-period world capital-labour ratio `(K'+K*')/((1+n)(N+N*))` equals `Ψ(k, d̄)` when
`x = N/(N+N*)`. -/
theorem law_of_motion_debt {d k N Ns Kw s sS : ℝ} (hN : 0 < N) (hNs : 0 < Ns)
    (hx : e.x = N / (N + Ns))
    (hs : s = e.β / (1 + e.β) *
      ((1 - e.α) * k ^ e.α - (e.α * k ^ (e.α - 1) - e.n) * d))
    (hsS : sS = e.β / (1 + e.β) * ((1 - e.α) * k ^ e.α))
    (hclear : Kw + d * ((1 + e.n) * N) = N * s + Ns * sS) :
    Kw / ((1 + e.n) * (N + Ns)) = e.psiDebt d k := by
  have := e.β_pos; have := e.n_gt
  have h1 : (1 + e.n) ≠ 0 := by linarith
  have h2 : (1 + e.β) ≠ 0 := by linarith
  have h3 : N + Ns ≠ 0 := by linarith
  have hK : Kw = N * s + Ns * sS - d * ((1 + e.n) * N) := by linarith
  unfold psiDebt
  rw [hK, hx, hs, hsS]
  field_simp
  ring

/-- With zero debt the law of motion reduces to O&R (3.52), p. 170: `Ψ(k, 0) = Ψ(k)`. -/
theorem psiDebt_zero (k : ℝ) : e.psiDebt 0 k = e.psi k := by
  unfold psiDebt psi coef
  ring

/-- Decomposition of the debt law of motion (O&R p. 170):
`Ψ(k, d̄) = Ψ(k) - x d̄ [1 + β(r - n)/((1+n)(1+β))]` with `r = αk^{α-1}`. -/
theorem psiDebt_eq (d k : ℝ) : e.psiDebt d k =
    e.psi k - e.x * d * (1 + e.β * (e.rate k - e.n) / ((1 + e.n) * (1 + e.β))) := by
  unfold psiDebt psi coef rate
  ring

/-- The crowding-out bracket is positive at every `k > 0` (O&R p. 171):
`1 + β(r - n)/((1+n)(1+β)) = (1 + n + β + βr)/((1+n)(1+β)) > 0`. This holds for any
`r > 0` and `n > -1`, not only when `r ≥ n`. -/
theorem crowding_bracket_pos {k : ℝ} (hk : 0 < k) :
    0 < 1 + e.β * (e.rate k - e.n) / ((1 + e.n) * (1 + e.β)) := by
  have := e.β_pos; have := e.n_gt
  have hr : 0 < e.rate k := mul_pos e.α_pos (Real.rpow_pos_of_pos hk _)
  have hD : 0 < (1 + e.n) * (1 + e.β) := mul_pos (by linarith) (by linarith)
  have h1 : (1 + e.n) ≠ 0 := by linarith
  have h2 : (1 + e.β) ≠ 0 := by linarith
  have heq : 1 + e.β * (e.rate k - e.n) / ((1 + e.n) * (1 + e.β)) =
      (1 + e.n + e.β + e.β * e.rate k) / ((1 + e.n) * (1 + e.β)) := by
    field_simp; ring
  rw [heq]
  exact div_pos (by nlinarith) hD

/-- O&R p. 171, as a derivative: `∂Ψ(k, d̄)/∂d̄ = -x[1 + β(r - n)/((1+n)(1+β))]`. -/
theorem psiDebt_hasDerivAt_debt (d k : ℝ) :
    HasDerivAt (fun d' => e.psiDebt d' k)
      (-(e.x * (1 + e.β * (e.rate k - e.n) / ((1 + e.n) * (1 + e.β))))) d := by
  have hfun : (fun d' => e.psiDebt d' k) = fun d' =>
      e.psi k - e.x * (d' * (1 + e.β * (e.rate k - e.n) / ((1 + e.n) * (1 + e.β)))) := by
    funext d'; rw [psiDebt_eq]; ring
  rw [hfun]
  have h := (((hasDerivAt_id d).mul_const
    (1 + e.β * (e.rate k - e.n) / ((1 + e.n) * (1 + e.β)))).const_mul e.x).const_sub (e.psi k)
  convert h using 1 <;> simp

/-- Debt shifts the law of motion down at every `k > 0` (O&R Fig 3.6, p. 171):
`d_1 < d_2 ⇒ Ψ(k, d_2) < Ψ(k, d_1)`. -/
theorem psiDebt_strictAnti_debt {k d1 d2 : ℝ} (hk : 0 < k) (hd : d1 < d2) :
    e.psiDebt d2 k < e.psiDebt d1 k := by
  rw [psiDebt_eq, psiDebt_eq]
  have hb := e.crowding_bracket_pos hk
  have : e.x * d1 * _ < e.x * d2 * _ :=
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hd e.x_pos) hb
  linarith

/-- Positive debt lies strictly below the debt-free map (O&R Fig 3.6, p. 171):
`d̄ > 0 ⇒ Ψ(k, d̄) < Ψ(k)`. -/
theorem psiDebt_lt_psi {k d : ℝ} (hk : 0 < k) (hd : 0 < d) : e.psiDebt d k < e.psi k := by
  rw [← e.psiDebt_zero k]; exact e.psiDebt_strictAnti_debt hk hd

/-- The derivative of the debt law of motion in `k` (O&R Fig 3.6, p. 171):
`∂Ψ/∂k = A α k^{α-1} + B (α-1) k^{α-2}` with `A = β(1-α)/((1+n)(1+β))` and
`B = -βxαd̄/((1+n)(1+β))`. -/
theorem psiDebt_hasDerivAt {d k : ℝ} (hk : 0 < k) :
    HasDerivAt (e.psiDebt d)
      (e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * (e.α * k ^ (e.α - 1)) +
        -(e.β * e.x * e.α * d) / ((1 + e.n) * (1 + e.β)) *
          ((e.α - 1) * k ^ (e.α - 1 - 1))) k := by
  have hfun : e.psiDebt d = fun y =>
      e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * y ^ e.α +
        -(e.β * e.x * e.α * d) / ((1 + e.n) * (1 + e.β)) * y ^ (e.α - 1) +
        (e.β * e.x * e.n * d / ((1 + e.n) * (1 + e.β)) - e.x * d) := by
    funext y; unfold psiDebt; ring
  rw [hfun]
  have h1 := Real.hasDerivAt_rpow_const (p := e.α) (Or.inl hk.ne')
  have h2 := Real.hasDerivAt_rpow_const (p := e.α - 1) (Or.inl hk.ne')
  exact ((h1.const_mul _).add (h2.const_mul _)).add_const _

/-- The derivative of `Ψ(·, d̄)` is strictly decreasing on `(0, ∞)` for `d̄ ≥ 0`
(the curvature of O&R Fig 3.6, p. 171). -/
theorem psiDebt_deriv_strictAnti {d a b : ℝ} (hd : 0 ≤ d) (ha : 0 < a) (hab : a < b) :
    e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * (e.α * b ^ (e.α - 1)) +
        -(e.β * e.x * e.α * d) / ((1 + e.n) * (1 + e.β)) * ((e.α - 1) * b ^ (e.α - 1 - 1)) <
      e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * (e.α * a ^ (e.α - 1)) +
        -(e.β * e.x * e.α * d) / ((1 + e.n) * (1 + e.β)) *
          ((e.α - 1) * a ^ (e.α - 1 - 1)) := by
  have := e.β_pos; have := e.n_gt; have := e.α_lt_one; have := e.α_pos; have := e.x_pos
  have hD : 0 < (1 + e.n) * (1 + e.β) := mul_pos (by linarith) (by linarith)
  have hA : 0 < e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * e.α :=
    mul_pos (div_pos (mul_pos e.β_pos (by linarith)) hD) e.α_pos
  have hB : 0 ≤ -(e.β * e.x * e.α * d) / ((1 + e.n) * (1 + e.β)) * (e.α - 1) := by
    rw [div_mul_eq_mul_div]
    apply div_nonneg _ hD.le
    have : 0 ≤ e.β * e.x * e.α * d := by positivity
    nlinarith
  have h1 : b ^ (e.α - 1) < a ^ (e.α - 1) := Real.rpow_lt_rpow_of_neg ha hab (by linarith)
  have h2 : b ^ (e.α - 1 - 1) < a ^ (e.α - 1 - 1) :=
    Real.rpow_lt_rpow_of_neg ha hab (by linarith)
  have e1 := mul_lt_mul_of_pos_left h1 hA
  have e2 := mul_le_mul_of_nonneg_left h2.le hB
  nlinarith

/-- `Ψ(·, d̄)` is strictly increasing on `(0, ∞)` for `d̄ ≥ 0` (O&R Fig 3.6, p. 171). -/
theorem psiDebt_strictMonoOn {d : ℝ} (hd : 0 ≤ d) : StrictMonoOn (e.psiDebt d) (Ioi 0) := by
  have := e.β_pos; have := e.n_gt; have := e.α_lt_one; have := e.α_pos; have := e.x_pos
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun k hk => (e.psiDebt_hasDerivAt hk).continuousAt.continuousWithinAt) fun k hk => ?_
  rw [interior_Ioi] at hk
  have hk : 0 < k := hk
  rw [(e.psiDebt_hasDerivAt hk).deriv]
  have hD : 0 < (1 + e.n) * (1 + e.β) := mul_pos (by linarith) (by linarith)
  have hA : 0 < e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * (e.α * k ^ (e.α - 1)) :=
    mul_pos (div_pos (mul_pos e.β_pos (by linarith)) hD)
      (mul_pos e.α_pos (Real.rpow_pos_of_pos hk _))
  have hB : 0 ≤ -(e.β * e.x * e.α * d) / ((1 + e.n) * (1 + e.β)) *
      ((e.α - 1) * k ^ (e.α - 1 - 1)) := by
    have hp : 0 < k ^ (e.α - 1 - 1) := Real.rpow_pos_of_pos hk _
    have : 0 ≤ e.β * e.x * e.α * d := by positivity
    rw [div_mul_eq_mul_div]
    apply div_nonneg _ hD.le
    have : 0 ≤ e.β * e.x * e.α * d * ((1 - e.α) * k ^ (e.α - 1 - 1)) :=
      mul_nonneg this (mul_nonneg (by linarith) hp.le)
    nlinarith
  linarith

/-- `Ψ(·, d̄)` is strictly concave on `(0, ∞)` for `d̄ ≥ 0` (the shape drawn in O&R
Fig 3.6, p. 171): `k^α` is concave and `-k^{α-1}` is concave. -/
theorem psiDebt_strictConcaveOn {d : ℝ} (hd : 0 ≤ d) :
    StrictConcaveOn ℝ (Ioi 0) (e.psiDebt d) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0)
    (fun k hk => (e.psiDebt_hasDerivAt hk).continuousAt.continuousWithinAt) ?_
  rw [interior_Ioi]
  intro a ha b hb hab
  rw [(e.psiDebt_hasDerivAt ha).deriv, (e.psiDebt_hasDerivAt hb).deriv]
  exact e.psiDebt_deriv_strictAnti hd ha hab

/-- The excess `Ψ(k, d̄) - k` is strictly concave on `(0, ∞)` for `d̄ ≥ 0`, so it has at most
two zeros (O&R Fig 3.6, p. 171). -/
theorem psiDebt_gap_strictConcaveOn {d : ℝ} (hd : 0 ≤ d) :
    StrictConcaveOn ℝ (Ioi 0) (fun k => e.psiDebt d k - k) := by
  have hder : ∀ k, 0 < k → HasDerivAt (fun k => e.psiDebt d k - k)
      (e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * (e.α * k ^ (e.α - 1)) +
        -(e.β * e.x * e.α * d) / ((1 + e.n) * (1 + e.β)) *
          ((e.α - 1) * k ^ (e.α - 1 - 1)) - 1) k :=
    fun k hk => (e.psiDebt_hasDerivAt hk).sub (hasDerivAt_id k)
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0)
    (fun k hk => (hder k hk).continuousAt.continuousWithinAt) ?_
  rw [interior_Ioi]
  intro a ha b hb hab
  rw [(hder a ha).deriv, (hder b hb).deriv]
  linarith [e.psiDebt_deriv_strictAnti hd ha hab]

/-- Steady-state pattern with debt (O&R Fig 3.6, p. 171): if `0 < l < u` are both steady
states of `Ψ(·, d̄)` with `d̄ ≥ 0`, then capital falls below `l`, rises between `l` and `u`,
and falls above `u`; in particular there are no other positive steady states. -/
theorem steady_state_pattern {d l u : ℝ} (hd : 0 ≤ d) (hl : 0 < l) (hlu : l < u)
    (hfl : e.psiDebt d l = l) (hfu : e.psiDebt d u = u) :
    (∀ k, 0 < k → k < l → e.psiDebt d k < k) ∧
      (∀ k, l < k → k < u → k < e.psiDebt d k) ∧
      (∀ k, u < k → e.psiDebt d k < k) := by
  have hg := e.psiDebt_gap_strictConcaveOn hd
  have hgl : e.psiDebt d l - l = 0 := by rw [hfl]; ring
  have hgu : e.psiDebt d u - u = 0 := by rw [hfu]; ring
  refine ⟨fun k hk hkl => ?_, fun k hlk hku => ?_, fun k huk => ?_⟩
  · have h := strictConcave_chord_lt hg hk hkl hlu
    simp only [hgl, hgu] at h
    have hpos : 0 < (l - k) / (u - k) := div_pos (by linarith) (by linarith)
    have : (u - l) / (u - k) * (e.psiDebt d k - k) < 0 := by linarith
    have hc : 0 < (u - l) / (u - k) := div_pos (by linarith) (by linarith)
    have := (mul_neg_iff.1 this).resolve_right (fun h' => (not_lt.2 hc.le) h'.1)
    linarith [this.2]
  · have h := strictConcave_chord_lt hg hl hlk hku
    simp only [hgl, hgu, mul_zero, add_zero] at h
    linarith
  · have h := strictConcave_chord_lt hg hl hlu huk
    simp only [hgl, hgu] at h
    have hc : 0 < (u - l) / (k - l) := div_pos (by linarith) (by linarith)
    have : (u - l) / (k - l) * (e.psiDebt d k - k) < 0 := by linarith
    have := (mul_neg_iff.1 this).resolve_right (fun h' => (not_lt.2 hc.le) h'.1)
    linarith [this.2]

/-- At most two positive steady states (O&R Fig 3.6, p. 171): with steady states `0 < l < u`
and `d̄ ≥ 0`, every positive steady state is `l` or `u`. -/
theorem steady_state_at_most_two {d l u k : ℝ} (hd : 0 ≤ d) (hl : 0 < l) (hlu : l < u)
    (hfl : e.psiDebt d l = l) (hfu : e.psiDebt d u = u) (hk : 0 < k)
    (hfk : e.psiDebt d k = k) : k = l ∨ k = u := by
  obtain ⟨h1, h2, h3⟩ := e.steady_state_pattern hd hl hlu hfl hfu
  rcases lt_trichotomy k l with h | h | h
  · exact absurd hfk (h1 k hk h).ne
  · exact Or.inl h
  rcases lt_trichotomy k u with h' | h' | h'
  · exact absurd hfk (h2 k h h').ne'
  · exact Or.inr h'
  · exact absurd hfk (h3 k h').ne

/-- Stability of the upper steady state (O&R Fig 3.6, p. 171): with steady states
`0 < l < u` and `d̄ ≥ 0`, every orbit starting above the unstable lower steady state `l`
converges monotonically to `u`. -/
theorem upper_steady_state_attracts {d l u k0 : ℝ} (hd : 0 ≤ d) (hl : 0 < l) (hlu : l < u)
    (hfl : e.psiDebt d l = l) (hfu : e.psiDebt d u = u) (hk0 : l < k0) :
    Tendsto (fun t : ℕ => (e.psiDebt d)^[t] k0) atTop (𝓝 u) := by
  obtain ⟨_, h2, h3⟩ := e.steady_state_pattern hd hl hlu hfl hfu
  have hmono := e.psiDebt_strictMonoOn hd
  have hcont : ∀ k, 0 < k → ContinuousAt (e.psiDebt d) k :=
    fun k hk => (e.psiDebt_hasDerivAt hk).continuousAt
  have hu : 0 < u := hl.trans hlu
  rcases le_total k0 u with h | h
  · refine (iterate_tendsto_of_below hfu (fun k hlk hku => ⟨h2 k hlk hku, ?_⟩)
      (fun k hk _ => hcont k (hl.trans hk)) hk0 h).2
    exact hfu ▸ hmono (mem_Ioi.2 (hl.trans hlk)) (mem_Ioi.2 hu) hku
  · refine (iterate_tendsto_of_above hfu (fun k huk => ⟨?_, h3 k huk⟩)
      (fun k hk => hcont k (hu.trans_le hk)) h).2
    exact hfu ▸ hmono (mem_Ioi.2 hu) (mem_Ioi.2 (hu.trans huk)) huk

/-- An upper (stable) steady state of `Ψ(·, d̄)` (O&R p. 171): a positive steady state above
which capital always falls. -/
def IsUpperSteadyState (d u : ℝ) : Prop :=
  0 < u ∧ e.psiDebt d u = u ∧ ∀ k, u < k → e.psiDebt d k < k

/-- Without debt `k̄` is the upper steady state (O&R p. 169). -/
theorem kbar_isUpper : e.IsUpperSteadyState 0 e.kbar := by
  refine ⟨e.kbar_pos, by rw [psiDebt_zero, psi_kbar], fun k hk => ?_⟩
  rw [psiDebt_zero]; exact (e.psi_between_above hk).2

/-- `Ψ(k) ≤ k + k̄` for every `k > 0` (bound used for the debt threshold, O&R p. 169). -/
theorem psi_le_add_kbar {k : ℝ} (hk : 0 < k) : e.psi k ≤ k + e.kbar := by
  rcases le_or_gt k e.kbar with h | h
  · rcases h.lt_or_eq with h' | h'
    · linarith [(e.psi_between_below hk h').2]
    · rw [h', psi_kbar]; linarith
  · linarith [(e.psi_between_above h).2, e.kbar_pos]

/-- Existence of steady states with debt (O&R Fig 3.6, p. 171, made precise): if
`d̄ > 0` and `Ψ(k*, d̄) > k*` for some `k* > 0`, there are exactly the two steady states
`0 < l < k* < u ≤ k̄` of the figure, and `u` is the upper (stable) one. The book assumes
this configuration silently; it fails for large debt
(see `no_steady_state_of_large_debt`). -/
theorem exists_two_steady_states {d ks : ℝ} (hd : 0 < d) (hks : 0 < ks)
    (hgap : ks < e.psiDebt d ks) :
    ∃ l u, 0 < l ∧ l < ks ∧ ks < u ∧ u ≤ e.kbar ∧ e.psiDebt d l = l ∧
      e.psiDebt d u = u ∧ e.IsUpperSteadyState d u := by
  have := e.β_pos; have := e.n_gt; have := e.α_lt_one; have := e.α_pos; have := e.x_pos
  have hcont : ContinuousOn (fun k => e.psiDebt d k - k) (Ioi 0) := fun k hk =>
    ((e.psiDebt_hasDerivAt hk).continuousAt.sub continuousAt_id).continuousWithinAt
  -- `ks < k̄`
  have hks_kbar : ks < e.kbar := by
    by_contra h
    push Not at h
    have hle : e.psi ks ≤ ks := by
      rcases h.lt_or_eq with h' | h'
      · exact (e.psi_between_above h').2.le
      · rw [← h', psi_kbar]
    linarith [e.psiDebt_lt_psi hks hd]
  -- upper steady state by the IVT on `[ks, k̄]`
  have hgk : e.psiDebt d e.kbar - e.kbar ≤ 0 := by
    linarith [e.psiDebt_lt_psi e.kbar_pos hd, e.psi_kbar]
  obtain ⟨u, ⟨hu1, hu2⟩, hu⟩ := intermediate_value_Icc' hks_kbar.le
    (hcont.mono fun k hk => hks.trans_le hk.1) ⟨hgk, by linarith⟩
  have hu' : e.psiDebt d u = u := by simp only at hu; linarith
  have hksu : ks < u := lt_of_le_of_ne hu1 (fun h => by rw [← h] at hu'; linarith)
  -- a point near zero with `Ψ(ε, d̄) < ε`
  have hD : 0 < (1 + e.n) * (1 + e.β) := mul_pos (by linarith) (by linarith)
  set Bc := e.β * e.x * e.α * d / ((1 + e.n) * (1 + e.β)) with hBc
  have hBpos : 0 < Bc := div_pos (by positivity) hD
  set M := (e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) +
    |e.β * e.x * e.n * d / ((1 + e.n) * (1 + e.β)) - e.x * d|) / Bc with hM
  have hev : ∀ᶠ k in 𝓝[>] (0 : ℝ), M < k ^ (e.α - 1) ∧ k ∈ Ioo 0 (min 1 ks) :=
    ((tendsto_rpow_neg_nhdsGT_zero (by linarith)).eventually_gt_atTop M).and
      (Ioo_mem_nhdsGT (lt_min one_pos hks))
  obtain ⟨ε, hεM, hε0, hε1⟩ := hev.exists
  have hε1' : ε < 1 := hε1.trans_le (min_le_left _ _)
  have hεks : ε < ks := hε1.trans_le (min_le_right _ _)
  have hgε : e.psiDebt d ε - ε ≤ 0 := by
    have hform : e.psiDebt d ε = e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * ε ^ e.α
        - Bc * ε ^ (e.α - 1) +
        (e.β * e.x * e.n * d / ((1 + e.n) * (1 + e.β)) - e.x * d) := by
      rw [hBc]; unfold psiDebt; ring
    have hpow : ε ^ e.α ≤ 1 := Real.rpow_le_one hε0.le hε1'.le e.α_pos.le
    have hA : 0 < e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) :=
      div_pos (mul_pos e.β_pos (by linarith)) hD
    have hMB : M * Bc = e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) +
        |e.β * e.x * e.n * d / ((1 + e.n) * (1 + e.β)) - e.x * d| := by
      rw [hM]; field_simp
    have h1 : M * Bc < ε ^ (e.α - 1) * Bc := mul_lt_mul_of_pos_right hεM hBpos
    have h2 := le_abs_self (e.β * e.x * e.n * d / ((1 + e.n) * (1 + e.β)) - e.x * d)
    have h3 : e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) * ε ^ e.α ≤
        e.β * (1 - e.α) / ((1 + e.n) * (1 + e.β)) := by
      nlinarith
    rw [hform]
    nlinarith
  obtain ⟨l, ⟨hl1, hl2⟩, hl⟩ := intermediate_value_Icc hεks.le
    (hcont.mono fun k hk => hε0.trans_le hk.1) ⟨hgε, by linarith⟩
  have hl' : e.psiDebt d l = l := by simp only at hl; linarith
  have hlks : l < ks := lt_of_le_of_ne hl2 (fun h => by rw [h] at hl'; linarith)
  have hl0 : 0 < l := hε0.trans_le hl1
  refine ⟨l, u, hl0, hlks, hksu, hu2, hl', hu', hl0.trans (hlks.trans hksu), hu', ?_⟩
  exact (e.steady_state_pattern hd.le hl0 (hlks.trans hksu) hl' hu').2.2

/-- Non-existence for large debt (a threshold O&R p. 171 omits): if
`x d̄ (1 + n + β)/((1+n)(1+β)) ≥ k̄` then `Ψ(k, d̄) < k` for every `k > 0`, so there is no
positive steady state and world capital cannot be sustained. -/
theorem no_steady_state_of_large_debt {d : ℝ} (hd : 0 < d)
    (hbig : e.kbar ≤ e.x * d * ((1 + e.n + e.β) / ((1 + e.n) * (1 + e.β)))) {k : ℝ}
    (hk : 0 < k) : e.psiDebt d k < k := by
  have := e.β_pos; have := e.n_gt; have := e.x_pos
  have hD : 0 < (1 + e.n) * (1 + e.β) := mul_pos (by linarith) (by linarith)
  have hr : 0 < e.rate k := mul_pos e.α_pos (Real.rpow_pos_of_pos hk _)
  have h1 : (1 + e.n) ≠ 0 := by linarith
  have h2 : (1 + e.β) ≠ 0 := by linarith
  have hsplit : 1 + e.β * (e.rate k - e.n) / ((1 + e.n) * (1 + e.β)) =
      (1 + e.n + e.β) / ((1 + e.n) * (1 + e.β)) +
        e.β * e.rate k / ((1 + e.n) * (1 + e.β)) := by
    field_simp; ring
  have hpos : 0 < e.x * d * (e.β * e.rate k / ((1 + e.n) * (1 + e.β))) :=
    mul_pos (mul_pos e.x_pos hd) (div_pos (mul_pos e.β_pos hr) hD)
  rw [psiDebt_eq, hsplit, mul_add]
  linarith [e.psi_le_add_kbar hk]

/-- Crowding out, O&R p. 171: raising Home debt from `d_1` to `d_2` pushes every positive
steady state `u_2` of `Ψ(·, d_2)` strictly below the upper steady state `u_1` of
`Ψ(·, d_1)`; world capital falls in BOTH countries since `k = k* = k^W` (O&R (3.50)). -/
theorem crowding_out {d1 d2 u1 u2 : ℝ} (hd : d1 < d2) (hu1 : e.IsUpperSteadyState d1 u1)
    (hu2 : 0 < u2) (hfu2 : e.psiDebt d2 u2 = u2) : u2 < u1 := by
  have hlt := e.psiDebt_strictAnti_debt hu2 hd
  rw [hfu2] at hlt
  by_contra h
  push Not at h
  rcases h.lt_or_eq with h' | h'
  · linarith [hu1.2.2 u2 h']
  · rw [← h', hu1.2.1] at hlt; exact lt_irrefl _ hlt

/-- Debt lowers capital below the debt-free level (O&R p. 171): with `d̄ > 0` every positive
steady state lies strictly below `k̄`. -/
theorem steady_state_lt_kbar {d u : ℝ} (hd : 0 < d) (hu : 0 < u)
    (hfu : e.psiDebt d u = u) : u < e.kbar :=
  e.crowding_out hd e.kbar_isUpper hu hfu

/-- The world interest rate rises with debt, O&R p. 171: under the hypotheses of
`crowding_out`, `α u_1^{α-1} < α u_2^{α-1}`. -/
theorem rate_rises {d1 d2 u1 u2 : ℝ} (hd : d1 < d2) (hu1 : e.IsUpperSteadyState d1 u1)
    (hu2 : 0 < u2) (hfu2 : e.psiDebt d2 u2 = u2) : e.rate u1 < e.rate u2 :=
  mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg hu2 (e.crowding_out hd hu1 hu2 hfu2)
    (by linarith [e.α_lt_one])) e.α_pos

/-! ## Dynamic inefficiency (O&R §3.6.4) -/

/-- O&R §3.6.4, p. 171: for `n ≥ 0`, `β > 0`, `0 < α < 1`, the steady-state rate of (3.53)
satisfies `r̄ ≤ n` exactly when `α ≤ nβ/((1+n)(1+β) + nβ)`. -/
theorem rbar_le_n_iff {α β n : ℝ} (hα1 : α < 1) (hβ : 0 < β) (hn : 0 ≤ n) :
    rbarOf α β n ≤ n ↔ α ≤ n * β / ((1 + n) * (1 + β) + n * β) := by
  have hden : 0 < β * (1 - α) := mul_pos hβ (by linarith)
  have hden2 : 0 < (1 + n) * (1 + β) + n * β := by positivity
  unfold rbarOf
  rw [div_le_iff₀ hden, le_div_iff₀ hden2]
  constructor <;> intro h <;> nlinarith

/-- O&R §3.6.4, p. 171: `r̄ ≤ n` is possible — for every `n > 0` and `β > 0` some capital
share `α ∈ (0,1)` gives `r̄ ≤ n`. -/
theorem exists_alpha_rbar_le_n {β n : ℝ} (hβ : 0 < β) (hn : 0 < n) :
    ∃ α, 0 < α ∧ α < 1 ∧ rbarOf α β n ≤ n := by
  have hden2 : 0 < (1 + n) * (1 + β) + n * β := by positivity
  refine ⟨n * β / ((1 + n) * (1 + β) + n * β), by positivity, ?_, ?_⟩
  · rw [div_lt_one hden2]; nlinarith
  · have h1 : n * β / ((1 + n) * (1 + β) + n * β) < 1 := by
      rw [div_lt_one hden2]; nlinarith
    exact (rbar_le_n_iff h1 hβ hn.le).2 le_rfl

/-- O&R §3.6.4, p. 171: `r̄ → 0` as `α → 0⁺` ("making `α` sufficiently small"). -/
theorem rbar_tendsto_zero {β n : ℝ} (hβ : 0 < β) :
    Tendsto (fun α => rbarOf α β n) (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt (fun α => rbarOf α β n) 0 := by
    unfold rbarOf
    exact ((continuousAt_id.mul continuousAt_const).mul continuousAt_const).div
      (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)) (by simp [hβ.ne'])
  have h0 : rbarOf 0 β n = 0 := by simp [rbarOf]
  have ht := hc.tendsto
  rw [h0] at ht
  exact tendsto_nhdsWithin_of_tendsto_nhds ht

/-- O&R §3.6.4, p. 171 with (3.54): if `r ≤ n` then the tax needed to hold debt per worker at
`d̄ ≥ 0` is non-positive, `τ = (r - n)d̄ ≤ 0`. -/
theorem tax_nonpos_of_rate_le {r n d : ℝ} (hr : r ≤ n) (hd : 0 ≤ d) : (r - n) * d ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (by linarith) hd

/-! ## Exercise 4: the untaxed Foreign young (O&R p. 197) -/

/-- Steady-state lifetime utility of a Foreign young agent (untaxed) at world capital `k`,
O&R Exercise 4, p. 197, with log preferences (3.9): `log c^Y + β log c^O`,
`c^Y = w/(1+β)`, `c^O = (1+r)βw/(1+β)`, `w = (1-α)k^α`, `r = αk^{α-1}`. -/
noncomputable def foreignUtility (k : ℝ) : ℝ :=
  Real.log ((1 - e.α) * k ^ e.α / (1 + e.β)) +
    e.β * Real.log ((1 + e.α * k ^ (e.α - 1)) * e.β * ((1 - e.α) * k ^ e.α) / (1 + e.β))

/-- O&R Exercise 4, p. 197: the marginal effect of world capital on Foreign steady-state
welfare, `dV/dk = [α(1+β) - β(1-α) r/(1+r)]/k` with `r = αk^{α-1}` — wage gain versus the
loss of interest income. -/
theorem foreignUtility_hasDerivAt {k : ℝ} (hk : 0 < k) :
    HasDerivAt e.foreignUtility
      ((e.α * (1 + e.β) - e.β * (1 - e.α) * (e.rate k / (1 + e.rate k))) / k) k := by
  have := e.β_pos; have := e.α_lt_one; have := e.α_pos
  have h1 := Real.hasDerivAt_rpow_const (p := e.α) (Or.inl hk.ne')
  have h2 := Real.hasDerivAt_rpow_const (p := e.α - 1) (Or.inl hk.ne')
  have hP : 0 < k ^ e.α := Real.rpow_pos_of_pos hk _
  have hQ : 0 < k ^ (e.α - 1) := Real.rpow_pos_of_pos hk _
  have hw := (h1.const_mul (1 - e.α)).div_const (1 + e.β)
  have hR := ((((h2.const_mul e.α).const_add 1).mul_const e.β).mul
    (h1.const_mul (1 - e.α))).div_const (1 + e.β)
  have hne1 : (1 - e.α) * k ^ e.α / (1 + e.β) ≠ 0 := by
    have : 0 < (1 - e.α) * k ^ e.α / (1 + e.β) := div_pos (mul_pos (by linarith) hP)
      (by linarith)
    exact this.ne'
  have hne2 : (1 + e.α * k ^ (e.α - 1)) * e.β * ((1 - e.α) * k ^ e.α) / (1 + e.β) ≠ 0 := by
    have : 0 < (1 + e.α * k ^ (e.α - 1)) * e.β * ((1 - e.α) * k ^ e.α) / (1 + e.β) := by
      apply div_pos _ (by linarith)
      exact mul_pos (mul_pos (by nlinarith) e.β_pos) (mul_pos (by linarith) hP)
    exact this.ne'
  have h := (hw.log hne1).add ((hR.log hne2).const_mul e.β)
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  unfold rate
  rw [Real.rpow_sub_one hk.ne' (e.α - 1), Real.rpow_sub_one hk.ne' e.α]
  have hk' : k ≠ 0 := hk.ne'
  have hP' : k ^ e.α ≠ 0 := hP.ne'
  have h1a : 1 - e.α ≠ 0 := by linarith
  have h1b : 1 + e.β ≠ 0 := by linarith
  have h1c : k + e.α * k ^ e.α ≠ 0 := by nlinarith
  have h1d : 1 + e.α * (k ^ e.α / k) ≠ 0 := by
    rw [show 1 + e.α * (k ^ e.α / k) = (k + e.α * k ^ e.α) / k by field_simp]
    exact div_ne_zero h1c hk'
  field_simp
  ring

/-- O&R Exercise 4, p. 197: Foreign steady-state welfare rises with world capital at `k`
exactly when `β(1-α) r < α(1+β)(1+r)`, `r = αk^{α-1}`. -/
theorem foreignUtility_deriv_pos_iff {k : ℝ} (hk : 0 < k) :
    0 < deriv e.foreignUtility k ↔
      e.β * (1 - e.α) * e.rate k < e.α * (1 + e.β) * (1 + e.rate k) := by
  have hr : 0 < e.rate k := mul_pos e.α_pos (Real.rpow_pos_of_pos hk _)
  rw [(e.foreignUtility_hasDerivAt hk).deriv, div_pos_iff_of_pos_right hk, sub_pos,
    mul_div_assoc', div_lt_iff₀ (by linarith)]

/-- O&R Exercise 4, p. 197 (the answer can be yes): Foreign steady-state welfare FALLS with
world capital at `k`, so a debt-induced fall in `k` benefits Foreign generations, exactly when
`α(1+β)(1+r) < β(1-α) r` — possible when `α` is small and `r = αk^{α-1}` is high. -/
theorem foreignUtility_deriv_neg_iff {k : ℝ} (hk : 0 < k) :
    deriv e.foreignUtility k < 0 ↔
      e.α * (1 + e.β) * (1 + e.rate k) < e.β * (1 - e.α) * e.rate k := by
  have hr : 0 < e.rate k := mul_pos e.α_pos (Real.rpow_pos_of_pos hk _)
  rw [(e.foreignUtility_hasDerivAt hk).deriv, div_neg_iff, sub_neg, mul_div_assoc',
    lt_div_iff₀ (by linarith)]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact absurd h (not_lt.2 hk.le)
    · exact h
  · intro h; exact Or.inr ⟨h, hk⟩

/-- O&R Exercise 4, p. 197: if `α(1+β) ≥ β(1-α)` then Foreign steady-state welfare is strictly
increasing in world capital on `(0, ∞)`. -/
theorem foreignUtility_strictMonoOn (hαβ : e.β * (1 - e.α) ≤ e.α * (1 + e.β)) :
    StrictMonoOn e.foreignUtility (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun k hk => (e.foreignUtility_hasDerivAt hk).continuousAt.continuousWithinAt)
    fun k hk => ?_
  rw [interior_Ioi] at hk
  have hk : 0 < k := hk
  have hr : 0 < e.rate k := mul_pos e.α_pos (Real.rpow_pos_of_pos hk _)
  have hb : 0 < e.β * (1 - e.α) := mul_pos e.β_pos (by linarith [e.α_lt_one])
  rw [e.foreignUtility_deriv_pos_iff hk]
  nlinarith

/-- O&R Exercise 4, p. 197 (a precise answer for Foreign): when `α(1+β) ≥ β(1-α)`, raising
Home debt from `d_1` to `d_2` strictly lowers the steady-state lifetime utility of every
Foreign generation (compare an upper steady state `u_1` with any positive steady state
`u_2` under the higher debt). -/
theorem foreign_welfare_falls_with_debt (hαβ : e.β * (1 - e.α) ≤ e.α * (1 + e.β))
    {d1 d2 u1 u2 : ℝ} (hd : d1 < d2) (hu1 : e.IsUpperSteadyState d1 u1) (hu2 : 0 < u2)
    (hfu2 : e.psiDebt d2 u2 = u2) : e.foreignUtility u2 < e.foreignUtility u1 :=
  e.foreignUtility_strictMonoOn hαβ (mem_Ioi.2 hu2) (mem_Ioi.2 hu1.1)
    (e.crowding_out hd hu1 hu2 hfu2)

end TwoCountry

end ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Infinitely lived overlapping generations (Weil 1989) and perpetual youth (Blanchard 1985)

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §3.7.3–§3.7.6,
pp. 181–191, and Chapter 3 Exercises 3 and 5, pp. 195–197.

Weil's small open economy: each vintage `v` lives forever with utility `Σ β^{s-t} log c^v_s`
(O&R (3.61)); population grows as `N_t = (1 + n) N_{t-1}`, `N_0 = 1`; newborns hold no financial
wealth (O&R (3.63)). We formalise

* the vintage budget constraint (3.62) from the flow constraint and no-Ponzi, and the log-utility
  consumption function (3.64) from (3.62) and the Euler equation;
* the vintage weights (3.65), aggregate consumption (3.66) and the generational-turnover law
  (3.67) — making explicit the book's implicit assumption that all vintages share the same
  after-tax income path, hence the same human wealth;
* the combined law of motion (3.68)–(3.69), its stability condition `(1 + r) β < 1 + n`, the
  steady state (3.70)–(3.71) and footnotes 49 and 52 (both need `n > 0`; at `n = 0` steady-state
  consumption is identically zero);
* the transitory shock (3.72), trend growth (3.73) and the claim that faster growth lowers the
  long-run asset/output ratio (proved via a partial-fraction decomposition);
* §3.7.6: the unit-tilt case `(1 + r) β = 1`, and debt as net wealth (3.74)–(3.75);
* Exercise 3 (Blanchard perpetual youth, parts (a)–(f)) and Exercise 5 (arbitrary debt paths).

Paths from date `t` are indexed by the offset `k = s - t`, and present values carry explicit
`HasSum` hypotheses.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth

open Filter Topology Finset

/-! ## Budget constraint and consumption function, (3.62) and (3.64) -/

/-- Discounted telescoping behind the vintage budget constraint O&R (3.62), p. 182: if assets
obey the flow constraint `b_{k+1} = R b_k + x_k - c_k` with gross return `R > 0` and discount
factor `ρ = R⁻¹`, then for every horizon `T`,
`Σ_{k<T} ρ^k (c_k - x_k) = R b_0 - R ρ^T b_T`. -/
theorem perpetual_finite_budget {R ρ : ℝ} (hRρ : R * ρ = 1) {b x c : ℕ → ℝ}
    (hflow : ∀ k, b (k + 1) = R * b k + x k - c k) (T : ℕ) :
    ∑ k ∈ range T, ρ ^ k * (c k - x k) = R * b 0 - R * ρ ^ T * b T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, ih]
    linear_combination ρ ^ T * hflow T + ρ ^ T * b (T + 1) * hRρ

/-- The vintage intertemporal budget constraint O&R (3.62), p. 182, derived from the flow
constraint and the no-Ponzi condition `ρ^T b_T → 0`: the present value of consumption equals
`R b_0` plus the present value of after-tax income `x`. (With `R = 1 + r` this is (3.62); with
`R = (1 + r)/φ` it is the Blanchard budget constraint of Exercise 3(c), p. 196.) -/
theorem perpetual_ibc_of_flow {R ρ : ℝ} (hRρ : R * ρ = 1) {b x c : ℕ → ℝ}
    (hflow : ∀ k, b (k + 1) = R * b k + x k - c k) {X C : ℝ}
    (hX : HasSum (fun k => ρ ^ k * x k) X) (hC : HasSum (fun k => ρ ^ k * c k) C)
    (hNP : Tendsto (fun T => ρ ^ T * b T) atTop (𝓝 0)) :
    C = R * b 0 + X := by
  have h1 : Tendsto (fun T => ∑ k ∈ range T, ρ ^ k * (c k - x k)) atTop (𝓝 (C - X)) := by
    have := (hC.sub hX).tendsto_sum_nat
    simpa [mul_sub] using this
  have h2 : Tendsto (fun T => ∑ k ∈ range T, ρ ^ k * (c k - x k)) atTop
      (𝓝 (R * b 0 - R * 0)) := by
    have : Tendsto (fun T => R * b 0 - R * (ρ ^ T * b T)) atTop (𝓝 (R * b 0 - R * 0)) :=
      tendsto_const_nhds.sub (hNP.const_mul R)
    refine this.congr fun T => ?_
    rw [perpetual_finite_budget hRρ hflow T]
    ring
  have := tendsto_nhds_unique h1 h2
  linarith

/-- Consumption out of wealth under geometric Euler dynamics, O&R (3.64), p. 182: if the
discounted consumption path satisfies `ρ c_{k+1} = δ c_k` with `0 ≤ δ < 1`, and the present
value of consumption is `W`, then `c_0 = (1 - δ) W`. -/
theorem perpetual_consumption_of_euler {ρ δ W : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {c : ℕ → ℝ}
    (heuler : ∀ k, ρ * c (k + 1) = δ * c k) (hW : HasSum (fun k => ρ ^ k * c k) W) :
    c 0 = (1 - δ) * W := by
  have hpow : ∀ k, ρ ^ k * c k = c 0 * δ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      linear_combination ρ ^ k * heuler k + δ * ih
  have hG : HasSum (fun k => ρ ^ k * c k) (c 0 * (1 - δ)⁻¹) := by
    simp_rw [hpow]
    exact (hasSum_geometric_of_lt_one hδ0 hδ1).mul_left (c 0)
  have hne : (1 - δ) ≠ 0 := by linarith
  rw [hW.unique hG]
  field_simp

/-- The Weil consumption function O&R (3.64), p. 182, derived: under the flow constraint
`b_{k+1} = (1 + r) b_k + (y_k - τ_k) - c_k`, no-Ponzi, and the log-utility Euler equation
`c_{k+1} = (1 + r) β c_k`, consumption is
`c_0 = (1 - β) [(1 + r) b_0 + Σ (1 + r)^{-k} (y_k - τ_k)]`. -/
theorem weil_consumption_function {r β : ℝ} (hr : 0 < 1 + r) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {b x c : ℕ → ℝ} (hflow : ∀ k, b (k + 1) = (1 + r) * b k + x k - c k)
    (heuler : ∀ k, c (k + 1) = (1 + r) * β * c k) {X C : ℝ}
    (hX : HasSum (fun k => ((1 + r)⁻¹) ^ k * x k) X)
    (hC : HasSum (fun k => ((1 + r)⁻¹) ^ k * c k) C)
    (hNP : Tendsto (fun T => ((1 + r)⁻¹) ^ T * b T) atTop (𝓝 0)) :
    c 0 = (1 - β) * ((1 + r) * b 0 + X) := by
  have hRρ : (1 + r) * (1 + r)⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  rw [← perpetual_ibc_of_flow hRρ hflow hX hC hNP]
  refine perpetual_consumption_of_euler hβ0 hβ1 (fun k => ?_) hC
  rw [heuler k]
  field_simp

/-! ## Aggregation over vintages, (3.65)–(3.67) -/

/-- Size of vintage `v` in Weil's economy, O&R p. 183: vintage `0` has `N_0 = 1` member and
vintage `v ≥ 1` has `N_v - N_{v-1} = n (1 + n)^{v-1}` members. -/
def vintageSize (n : ℝ) : ℕ → ℝ
  | 0 => 1
  | v + 1 => n * (1 + n) ^ v

/-- Aggregate per capita value of a vintage-indexed variable on date `t`, O&R (3.65), p. 183:
`(x^0 + n x^1 + ... + n (1 + n)^{t-1} x^t) / (1 + n)^t`. -/
noncomputable def vintageAgg (n : ℝ) (t : ℕ) (x : ℕ → ℝ) : ℝ :=
  (∑ v ∈ range (t + 1), vintageSize n v * x v) / (1 + n) ^ t

/-- Population accounting behind O&R (3.65), p. 183: the vintages alive on date `t` sum to the
total population `N_t = (1 + n)^t`. -/
theorem sum_vintageSize (n : ℝ) (t : ℕ) :
    ∑ v ∈ range (t + 1), vintageSize n v = (1 + n) ^ t := by
  induction t with
  | zero => simp [vintageSize]
  | succ t ih =>
    rw [sum_range_succ, ih]
    simp only [vintageSize]
    ring

/-- The vintage weights of O&R (3.65), p. 183, sum to one, so the aggregate of a variable that
is the same for every vintage is that common value. -/
theorem vintageAgg_const {n : ℝ} (hn : 0 < 1 + n) (t : ℕ) (a : ℝ) :
    vintageAgg n t (fun _ => a) = a := by
  have : (1 + n) ^ t ≠ 0 := pow_ne_zero _ hn.ne'
  unfold vintageAgg
  rw [← sum_mul, sum_vintageSize]
  field_simp

/-- Linearity of the aggregation (3.65), O&R p. 183 ("the preceding linear aggregation
procedure can be applied to any other variable"). -/
theorem vintageAgg_affine {n : ℝ} (hn : 0 < 1 + n) (t : ℕ) (p q : ℝ) (x y : ℕ → ℝ) :
    vintageAgg n t (fun v => p * x v + q * y v) = p * vintageAgg n t x + q * vintageAgg n t y := by
  unfold vintageAgg
  have : (1 + n) ^ t ≠ 0 := pow_ne_zero _ hn.ne'
  field_simp
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun v _ => ?_
  ring

/-- The aggregate depends only on the vintages alive on date `t` (O&R (3.65), p. 183). -/
theorem vintageAgg_congr {n : ℝ} {t : ℕ} {x y : ℕ → ℝ} (h : ∀ v ≤ t, x v = y v) :
    vintageAgg n t x = vintageAgg n t y := by
  unfold vintageAgg
  congr 1
  refine sum_congr rfl fun v hv => ?_
  rw [h v (Nat.lt_succ_iff.mp (mem_range.mp hv))]

/-- Aggregation of the consumption functions (3.64) with vintage-specific human wealth `H^v`,
O&R p. 183: `c_t = (1 - β) [(1 + r) b^P_t + H_t]` where `H_t` is aggregate human wealth. -/
theorem weil_aggregate_consumption_general {n r β : ℝ} (hn : 0 < 1 + n) {t : ℕ}
    {c b H : ℕ → ℝ} (hc : ∀ v ≤ t, c v = (1 - β) * ((1 + r) * b v + H v)) :
    vintageAgg n t c = (1 - β) * ((1 + r) * vintageAgg n t b + vintageAgg n t H) := by
  rw [vintageAgg_congr hc]
  have := vintageAgg_affine hn t ((1 - β) * (1 + r)) (1 - β) b H
  rw [show (fun v => (1 - β) * ((1 + r) * b v + H v))
      = fun v => (1 - β) * (1 + r) * b v + (1 - β) * H v from funext fun v => by ring, this]
  ring

/-- Aggregate consumption O&R (3.66), p. 183. The book leaves implicit that every vintage has
the same output and tax path, hence the same human wealth `H = Σ (1 + r)^{-(s-t)} (y_s - τ_s)`;
under that assumption `c_t = (1 - β) [(1 + r) b^P_t + H]`. -/
theorem weil_aggregate_consumption {n r β H : ℝ} (hn : 0 < 1 + n) {t : ℕ} {c b : ℕ → ℝ}
    (hc : ∀ v ≤ t, c v = (1 - β) * ((1 + r) * b v + H)) :
    vintageAgg n t c = (1 - β) * ((1 + r) * vintageAgg n t b + H) := by
  rw [weil_aggregate_consumption_general (H := fun _ => H) hn hc, vintageAgg_const hn]

/-- Aggregate private asset accumulation O&R (3.67), p. 184. If each vintage alive on date `t`
accumulates `b^v_{t+1} = (1 + r) b^v_t + y_t - τ_t - c^v_t` and the newborn vintage `t + 1`
holds no financial wealth (O&R (3.63)), then per capita assets obey
`b^P_{t+1} = [(1 + r) b^P_t + y_t - τ_t - c_t] / (1 + n)`. -/
theorem weil_aggregate_accumulation {n r y τ : ℝ} (hn : 0 < 1 + n) {t : ℕ}
    {b b' c : ℕ → ℝ} (hacc : ∀ v ≤ t, b' v = (1 + r) * b v + y - τ - c v)
    (hnew : b' (t + 1) = 0) :
    vintageAgg n (t + 1) b' =
      ((1 + r) * vintageAgg n t b + y - τ - vintageAgg n t c) / (1 + n) := by
  have hsplit : vintageAgg n (t + 1) b' = vintageAgg n t b' / (1 + n) := by
    have : (1 + n) ^ t ≠ 0 := pow_ne_zero _ hn.ne'
    unfold vintageAgg
    rw [sum_range_succ (fun v => vintageSize n v * b' v) (t + 1), hnew, mul_zero, add_zero,
      pow_succ]
    field_simp
  have hmid : vintageAgg n t b' =
      vintageAgg n t (fun v => (1 + r) * b v + (-1) * c v) + (y - τ) := by
    rw [vintageAgg_congr (y := fun v => (1 + r) * b v + (-1) * c v + (y - τ) * 1)
      (fun v hv => by rw [hacc v hv]; ring)]
    have h1 := vintageAgg_affine hn t 1 (y - τ) (fun v => (1 + r) * b v + (-1) * c v)
      (fun _ => 1)
    simp only [one_mul, vintageAgg_const hn] at h1
    rw [h1, mul_one]
  rw [hsplit, hmid, vintageAgg_affine hn]
  ring

/-- The combined law of motion O&R (3.68), p. 184: substituting (3.66) into (3.67),
`b^P_{t+1} = [(1 + r) β / (1 + n)] b^P_t + [y_t - τ_t - (1 - β) H_t] / (1 + n)`. -/
theorem weil_law_of_motion {n r β y τ H bP bP' c : ℝ} (hn : 0 < 1 + n)
    (hc : c = (1 - β) * ((1 + r) * bP + H)) (hb : bP' = ((1 + r) * bP + y - τ - c) / (1 + n)) :
    bP' = (1 + r) * β / (1 + n) * bP + (y - τ - (1 - β) * H) / (1 + n) := by
  rw [hb, hc]
  field_simp
  ring

/-! ## Constant output: dynamics and steady state, (3.69)–(3.71) -/

/-- Present value of a constant stream, used in O&R (3.69), p. 184: for `r > 0`,
`Σ_{k ≥ 0} (1 + r)^{-k} ȳ = (1 + r) ȳ / r`. -/
theorem weil_hasSum_const {r : ℝ} (hr : 0 < r) (ybar : ℝ) :
    HasSum (fun k : ℕ => ((1 + r)⁻¹) ^ k * ybar) ((1 + r) / r * ybar) := by
  have h0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have h1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h := (hasSum_geometric_of_lt_one h0 h1).mul_right ybar
  have e : 1 - (1 + r)⁻¹ = r / (1 + r) := by
    have : (1 + r) ≠ 0 := by linarith
    field_simp
    ring
  rwa [e, inv_div] at h

/-- Slope of the Weil law of motion (3.69), O&R p. 184: `(1 + r) β / (1 + n)`. -/
noncomputable def weilSlope (r β n : ℝ) : ℝ := (1 + r) * β / (1 + n)

/-- Intercept of the Weil law of motion (3.69), O&R p. 184: `[(1 + r) β - 1] ȳ / (r (1 + n))`. -/
noncomputable def weilIntercept (r β n ybar : ℝ) : ℝ := ((1 + r) * β - 1) * ybar / (r * (1 + n))

/-- Steady-state net foreign assets O&R (3.70), p. 185:
`b̄ = [(1 + r) β - 1] ȳ / ([(1 + n) - (1 + r) β] r)`. -/
noncomputable def weilSteadyB (r β n ybar : ℝ) : ℝ :=
  ((1 + r) * β - 1) * ybar / (((1 + n) - (1 + r) * β) * r)

/-- Steady-state consumption O&R (3.71), p. 186: `c̄ = (r - n) b̄ + ȳ`. -/
noncomputable def weilSteadyC (r β n ybar : ℝ) : ℝ := (r - n) * weilSteadyB r β n ybar + ybar

/-- The law of motion O&R (3.69), p. 184: with `τ = 0`, `b^P = b` and constant output `ȳ`,
(3.68) becomes `b_{t+1} = [(1 + r) β / (1 + n)] b_t + [(1 + r) β - 1] ȳ / (r (1 + n))`. -/
theorem weil_law_of_motion_const {n r β ybar b b' c : ℝ} (hn : 0 < 1 + n) (hr : 0 < r)
    (hc : c = (1 - β) * ((1 + r) * b + (1 + r) / r * ybar))
    (hb : b' = ((1 + r) * b + ybar - 0 - c) / (1 + n)) :
    b' = weilSlope r β n * b + weilIntercept r β n ybar := by
  rw [weil_law_of_motion hn hc hb, weilSlope, weilIntercept]
  field_simp
  ring

/-- Solution of a linear difference equation (used for Figure 3.9, O&R p. 185): if
`b_{k+1} = a b_k + q` and `x̄ = a x̄ + q`, then `b_k - x̄ = a^k (b_0 - x̄)`. -/
theorem weil_affine_iterate {a q xbar : ℝ} {b : ℕ → ℝ} (hb : ∀ k, b (k + 1) = a * b k + q)
    (hfix : xbar = a * xbar + q) (k : ℕ) : b k - xbar = a ^ k * (b 0 - xbar) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hb k, pow_succ]
    linear_combination a * ih - hfix

/-- `b̄` of (3.70) is the fixed point of (3.69), O&R p. 185 (given `r ≠ 0` and
`(1 + n) ≠ (1 + r) β`). -/
theorem weilSteadyB_fixed {r β n ybar : ℝ} (hn : 0 < 1 + n) (hr : r ≠ 0)
    (hstab : (1 + r) * β ≠ 1 + n) :
    weilSteadyB r β n ybar =
      weilSlope r β n * weilSteadyB r β n ybar + weilIntercept r β n ybar := by
  have h1 : (1 + n) - (1 + r) * β ≠ 0 := sub_ne_zero.mpr (Ne.symm hstab)
  unfold weilSteadyB weilSlope weilIntercept
  field_simp
  ring

/-- Uniqueness of the steady state (3.70), O&R p. 185: any fixed point of (3.69) equals `b̄`. -/
theorem weilSteadyB_unique {r β n ybar x : ℝ} (hn : 0 < 1 + n) (hr : r ≠ 0)
    (hstab : (1 + r) * β ≠ 1 + n) (hx : x = weilSlope r β n * x + weilIntercept r β n ybar) :
    x = weilSteadyB r β n ybar := by
  have h1 : (1 + n) - (1 + r) * β ≠ 0 := sub_ne_zero.mpr (Ne.symm hstab)
  unfold weilSlope weilIntercept at hx
  unfold weilSteadyB
  field_simp at hx
  rw [eq_div_iff (mul_ne_zero h1 hr)]
  linear_combination hx

/-- Stability of the Weil dynamics, O&R p. 184 ("existence and stability of the steady state
follow from the assumption ... `(1 + r) β / (1 + n) < 1`"): if `(1 + r) β < 1 + n` then every
path of (3.69) converges to `b̄`. -/
theorem weil_converges {r β n ybar : ℝ} (hn : 0 < 1 + n) (hr0 : 0 < 1 + r) (hr : r ≠ 0)
    (hβ : 0 ≤ β) (hstab : (1 + r) * β < 1 + n) {b : ℕ → ℝ}
    (hb : ∀ k, b (k + 1) = weilSlope r β n * b k + weilIntercept r β n ybar) :
    Tendsto b atTop (𝓝 (weilSteadyB r β n ybar)) := by
  have hfix := weilSteadyB_fixed (ybar := ybar) hn hr hstab.ne
  have ha0 : 0 ≤ weilSlope r β n := by unfold weilSlope; positivity
  have ha1 : weilSlope r β n < 1 := by unfold weilSlope; rw [div_lt_one hn]; exact hstab
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).mul_const
    (b 0 - weilSteadyB r β n ybar)
  have := hlim.add_const (weilSteadyB r β n ybar)
  rw [zero_mul, zero_add] at this
  refine this.congr fun k => ?_
  rw [← weil_affine_iterate hb hfix k]
  ring

/-- Instability when the stability condition fails, O&R p. 184 and footnote 49: if
`(1 + r) β > 1 + n` (so the slope exceeds one) and `b_0 ≠ b̄`, the path of (3.69) does not
converge to `b̄`. -/
theorem weil_not_converges {r β n ybar : ℝ} (hn : 0 < 1 + n) (hr : r ≠ 0)
    (hunst : 1 + n < (1 + r) * β) {b : ℕ → ℝ}
    (hb : ∀ k, b (k + 1) = weilSlope r β n * b k + weilIntercept r β n ybar)
    (h0 : b 0 ≠ weilSteadyB r β n ybar) :
    ¬ Tendsto b atTop (𝓝 (weilSteadyB r β n ybar)) := by
  intro hT
  have hfix := weilSteadyB_fixed (ybar := ybar) hn hr hunst.ne'
  have ha1 : 1 ≤ weilSlope r β n := by
    unfold weilSlope; rw [le_div_iff₀ hn]; linarith
  set e := |b 0 - weilSteadyB r β n ybar| with he
  have hepos : 0 < e := abs_pos.mpr (sub_ne_zero.mpr h0)
  have hev : ∀ᶠ k in atTop, |b k - weilSteadyB r β n ybar| < e := by
    have := (Metric.tendsto_atTop.mp hT) e hepos
    obtain ⟨N, hN⟩ := this
    exact eventually_atTop.mpr ⟨N, fun k hk => by simpa [Real.dist_eq] using hN k hk⟩
  obtain ⟨k, hk⟩ := hev.exists
  rw [weil_affine_iterate hb hfix k, abs_mul, abs_of_nonneg (by positivity)] at hk
  have : 1 ≤ weilSlope r β n ^ k := one_le_pow₀ ha1
  nlinarith

/-- Stability is automatic for a debtor, O&R p. 185: if `(1 + r) β < 1` and `n ≥ 0` then
`(1 + r) β < 1 + n`. -/
theorem weil_stable_of_impatient {r β n : ℝ} (himp : (1 + r) * β < 1) (hn : 0 ≤ n) :
    (1 + r) * β < 1 + n := by linarith

/-- Sign of the steady state, O&R p. 185: under the stability condition and `r > 0`, `ȳ > 0`,
`b̄ > 0` iff `(1 + r) β > 1`. -/
theorem weilSteadyB_pos_iff {r β n ybar : ℝ} (hr : 0 < r) (hy : 0 < ybar)
    (hstab : (1 + r) * β < 1 + n) :
    0 < weilSteadyB r β n ybar ↔ 1 < (1 + r) * β := by
  have hd : 0 < ((1 + n) - (1 + r) * β) * r := mul_pos (by linarith) hr
  unfold weilSteadyB
  rw [div_pos_iff_of_pos_right hd]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    exact mul_pos (by linarith) hy

/-- Steady-state consumption O&R (3.71), p. 186: at a steady state of the current-account
constraint `b = [(1 + r) b + ȳ - c] / (1 + n)`, consumption is `c = (r - n) b + ȳ`. -/
theorem weil_steady_consumption {r n ybar b c : ℝ} (hn : 0 < 1 + n)
    (hss : b = ((1 + r) * b + ybar - c) / (1 + n)) : c = (r - n) * b + ybar := by
  field_simp at hss
  linarith

/-- Consistency of (3.71) with the consumption function (3.66), O&R p. 186: at `b̄`,
`(1 - β) [(1 + r) b̄ + (1 + r) ȳ / r] = (r - n) b̄ + ȳ`. -/
theorem weilSteadyC_eq_consumption_function {r β n ybar : ℝ} (hr : r ≠ 0)
    (hstab : (1 + r) * β ≠ 1 + n) :
    (1 - β) * ((1 + r) * weilSteadyB r β n ybar + (1 + r) / r * ybar) =
      weilSteadyC r β n ybar := by
  have h1 : (1 + n) - (1 + r) * β ≠ 0 := sub_ne_zero.mpr (Ne.symm hstab)
  have hB : weilSteadyB r β n ybar * ((1 + n) - (1 + r) * β) * r = ((1 + r) * β - 1) * ybar := by
    unfold weilSteadyB
    field_simp
  unfold weilSteadyC
  generalize weilSteadyB r β n ybar = B at hB ⊢
  field_simp
  linear_combination hB

/-- Footnote 52, O&R p. 186: substituting (3.70) into (3.71),
`c̄ = n (1 + r) (1 - β) ȳ / ([(1 + n) - (1 + r) β] r)`. -/
theorem weilSteadyC_closed {r β n ybar : ℝ} (hr : r ≠ 0) (hstab : (1 + r) * β ≠ 1 + n) :
    weilSteadyC r β n ybar = n * (1 + r) * (1 - β) * ybar / (((1 + n) - (1 + r) * β) * r) := by
  have h1 : (1 + n) - (1 + r) * β ≠ 0 := sub_ne_zero.mpr (Ne.symm hstab)
  unfold weilSteadyC weilSteadyB
  field_simp
  ring

/-- Footnote 52 corrected, O&R p. 186: `dc̄/dȳ = n (1 + r) (1 - β) / ([(1 + n) - (1 + r) β] r)`. -/
theorem weilSteadyC_hasDerivAt {r β n : ℝ} (hr : r ≠ 0) (hstab : (1 + r) * β ≠ 1 + n)
    (ybar : ℝ) :
    HasDerivAt (fun y => weilSteadyC r β n y)
      (n * (1 + r) * (1 - β) / (((1 + n) - (1 + r) * β) * r)) ybar := by
  have hfun : (fun y => weilSteadyC r β n y) =
      fun y => (n * (1 + r) * (1 - β) / (((1 + n) - (1 + r) * β) * r)) * y := by
    funext y
    rw [weilSteadyC_closed hr hstab]
    ring
  rw [hfun]
  simpa using (hasDerivAt_id ybar).const_mul
    (n * (1 + r) * (1 - β) / (((1 + n) - (1 + r) * β) * r))

/-- Footnote 52 corrected, O&R p. 186: under stability, `r > 0` and `β < 1`, the slope
`dc̄/dȳ` is positive iff `n > 0`. (The book's "`dc̄/dȳ > 0`" also needs `n > 0`.) -/
theorem weilSteadyC_slope_pos_iff {r β n : ℝ} (hr : 0 < r) (hβ : β < 1)
    (hstab : (1 + r) * β < 1 + n) :
    0 < n * (1 + r) * (1 - β) / (((1 + n) - (1 + r) * β) * r) ↔ 0 < n := by
  have hd : 0 < ((1 + n) - (1 + r) * β) * r := mul_pos (by linarith) hr
  have hk : 0 < (1 + r) * (1 - β) := mul_pos (by linarith) (by linarith)
  rw [div_pos_iff_of_pos_right hd, mul_assoc]
  exact ⟨fun h => pos_of_mul_pos_left h hk.le, fun h => mul_pos h hk⟩

/-- Without population growth steady-state consumption vanishes, O&R footnote 52 (p. 186)
corrected: at `n = 0`, `c̄ = 0` for every `ȳ` (the whole of human wealth is mortgaged). -/
theorem weilSteadyC_zero_growth {r β ybar : ℝ} (hr : r ≠ 0) (hstab : (1 + r) * β ≠ 1 + 0) :
    weilSteadyC r β 0 ybar = 0 := by
  rw [weilSteadyC_closed hr hstab]
  ring

/-- Footnote 49, O&R p. 184, made precise: if `(1 + r) β > 1 + n` the formal "steady state" has
negative consumption, provided `n > 0`, `r > 0`, `β < 1` and `ȳ > 0` (at `n = 0` it is zero). -/
theorem weilSteadyC_neg_of_unstable {r β n ybar : ℝ} (hr : 0 < r) (hβ : β < 1) (hn : 0 < n)
    (hy : 0 < ybar) (hunst : 1 + n < (1 + r) * β) : weilSteadyC r β n ybar < 0 := by
  rw [weilSteadyC_closed hr.ne' hunst.ne']
  apply div_neg_of_pos_of_neg
  · have : 0 < 1 - β := by linarith
    have : 0 < 1 + r := by linarith
    positivity
  · exact mul_neg_of_neg_of_pos (by linarith) hr

/-- A permanent rise in output, O&R §3.7.5, p. 186: if `(1 + r) β < 1` (and `r > 0`, `n ≥ 0`),
raising `ȳ` to `ȳ' > ȳ` lowers `b̄`. -/
theorem weilSteadyB_falls {r β n ybar ybar' : ℝ} (hr : 0 < r) (hn : 0 ≤ n)
    (himp : (1 + r) * β < 1) (hy : ybar < ybar') :
    weilSteadyB r β n ybar' < weilSteadyB r β n ybar := by
  have hd : 0 < ((1 + n) - (1 + r) * β) * r := mul_pos (by linarith) hr
  unfold weilSteadyB
  rw [div_lt_div_iff_of_pos_right hd]
  nlinarith

/-- A permanent rise in output raises steady-state consumption, O&R p. 186 and footnote 52:
under stability with `r > 0`, `β < 1` and `n > 0`, `ȳ < ȳ'` implies `c̄(ȳ) < c̄(ȳ')`. -/
theorem weilSteadyC_rises {r β n ybar ybar' : ℝ} (hr : 0 < r) (hβ : β < 1) (hn : 0 < n)
    (hstab : (1 + r) * β < 1 + n) (hy : ybar < ybar') :
    weilSteadyC r β n ybar < weilSteadyC r β n ybar' := by
  have hd : 0 < ((1 + n) - (1 + r) * β) * r := mul_pos (by linarith) hr
  have hk : 0 < n * (1 + r) * (1 - β) := by
    have : 0 < 1 - β := by linarith
    have : 0 < 1 + r := by linarith
    positivity
  rw [weilSteadyC_closed hr.ne' hstab.ne, weilSteadyC_closed hr.ne' hstab.ne,
    div_lt_div_iff_of_pos_right hd]
  nlinarith

/-! ## Transitory output shock, (3.72) -/

/-- Human wealth under the transitory shock path (3.72), O&R p. 187: if output is `ȳ'` on
date `t` and `ȳ` afterwards, its present value is `(1 + r) ȳ / r + (ȳ' - ȳ)`. -/
theorem weil_hasSum_transitory {r : ℝ} (hr : 0 < r) (ybar ybar' : ℝ) :
    HasSum (fun k : ℕ => ((1 + r)⁻¹) ^ k * (if k = 0 then ybar' else ybar))
      ((1 + r) / r * ybar + (ybar' - ybar)) := by
  have h := (weil_hasSum_const hr ybar).add (hasSum_ite_eq 0 (ybar' - ybar))
  convert h using 1
  funext k
  split_ifs with hk
  · subst hk; ring
  · simp

/-- The transitory shock O&R (3.72), p. 187: starting from `b_t = b̄` with the output path
(3.72), `b_{t+1} = b̄ + β (ȳ' - ȳ) / (1 + n)`. -/
theorem weil_transitory_jump {n r β ybar ybar' H c b' : ℝ} (hn : 0 < 1 + n) (hr : 0 < r)
    (hstab : (1 + r) * β ≠ 1 + n)
    (hH : HasSum (fun k : ℕ => ((1 + r)⁻¹) ^ k * (if k = 0 then ybar' else ybar)) H)
    (hc : c = (1 - β) * ((1 + r) * weilSteadyB r β n ybar + H))
    (hb : b' = ((1 + r) * weilSteadyB r β n ybar + ybar' - c) / (1 + n)) :
    b' = weilSteadyB r β n ybar + β * (ybar' - ybar) / (1 + n) := by
  have hfix := weilSteadyB_fixed (ybar := ybar) hn hr.ne' hstab
  rw [hH.unique (weil_hasSum_transitory hr ybar ybar')] at hc
  unfold weilSlope weilIntercept at hfix
  rw [hb, hc]
  generalize weilSteadyB r β n ybar = B at hfix ⊢
  field_simp at hfix ⊢
  linear_combination (-1) * hfix

/-- Monotone return after a transitory shock, O&R p. 187: under stability with `β > 0`, a path
of (3.69) that starts above `b̄` stays above it and falls strictly every period. -/
theorem weil_transitory_return {r β n ybar : ℝ} (hn : 0 < 1 + n) (hr0 : 0 < 1 + r)
    (hr : r ≠ 0) (hβ : 0 < β) (hstab : (1 + r) * β < 1 + n) {b : ℕ → ℝ}
    (hb : ∀ k, b (k + 1) = weilSlope r β n * b k + weilIntercept r β n ybar)
    (h0 : weilSteadyB r β n ybar < b 0) (k : ℕ) :
    weilSteadyB r β n ybar < b (k + 1) ∧ b (k + 1) < b k := by
  have hfix := weilSteadyB_fixed (ybar := ybar) hn hr hstab.ne
  have ha0 : 0 < weilSlope r β n := by unfold weilSlope; positivity
  have ha1 : weilSlope r β n < 1 := by unfold weilSlope; rw [div_lt_one hn]; exact hstab
  have e1 := weil_affine_iterate hb hfix (k + 1)
  have e0 := weil_affine_iterate hb hfix k
  have hp : 0 < weilSlope r β n ^ k := pow_pos ha0 k
  have hd : 0 < b 0 - weilSteadyB r β n ybar := by linarith
  rw [pow_succ] at e1
  constructor
  · nlinarith [mul_pos (mul_pos hp ha0) hd]
  · nlinarith [mul_pos (mul_pos hp (sub_pos.mpr ha1)) hd]

/-! ## Trend output growth, (3.73) -/

/-- Human wealth with growing output, O&R p. 188: if `y_{t+k} = (1 + g)^k y_t` with
`0 ≤ 1 + g` and `g < r`, then `Σ (1 + r)^{-k} y_{t+k} = (1 + r) y_t / (r - g)`. -/
theorem weil_hasSum_growth {r g : ℝ} (hg : 0 ≤ 1 + g) (hgr : g < r) (y : ℝ) :
    HasSum (fun k : ℕ => ((1 + r)⁻¹) ^ k * ((1 + g) ^ k * y)) ((1 + r) / (r - g) * y) := by
  have hr : 0 < 1 + r := by linarith
  have hq0 : 0 ≤ (1 + g) / (1 + r) := div_nonneg hg hr.le
  have hq1 : (1 + g) / (1 + r) < 1 := by rw [div_lt_one hr]; linarith
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_right y
  have e : 1 - (1 + g) / (1 + r) = (r - g) / (1 + r) := by
    field_simp
    ring
  rw [e, inv_div] at h
  convert h using 1
  funext k
  rw [div_pow, div_eq_mul_inv, inv_pow]
  ring

/-- The growth law of motion, O&R p. 188: with `c_t = (1 - β)[(1 + r) b_t + (1 + r) y_t/(r - g)]`
and `b_{t+1} = [(1 + r) b_t + y_t - c_t]/(1 + n)`,
`b_{t+1} = [(1 + r) β/(1 + n)] b_t + [((1 + r) β - (1 + g))/((1 + n)(r - g))] y_t`. -/
theorem weil_growth_law {n r β g y b b' c : ℝ} (hn : 0 < 1 + n) (hgr : g < r)
    (hc : c = (1 - β) * ((1 + r) * b + (1 + r) / (r - g) * y))
    (hb : b' = ((1 + r) * b + y - c) / (1 + n)) :
    b' = (1 + r) * β / (1 + n) * b + ((1 + r) * β - (1 + g)) / ((1 + n) * (r - g)) * y := by
  have : r - g ≠ 0 := by linarith
  rw [hb, hc]
  field_simp
  ring

/-- The asset/output law of motion O&R (3.73), p. 188: dividing by `y_{t+1} = (1 + g) y_t`,
`b_{t+1}/y_{t+1} = [(1 + r) β/((1 + n)(1 + g))] b_t/y_t
  + ((1 + r) β - (1 + g))/((1 + n)(1 + g)(r - g))`. -/
theorem weil_growth_ratio_law {n r β g y b b' c : ℝ} (hn : 0 < 1 + n) (hgr : g < r)
    (hg : 0 < 1 + g) (hy : y ≠ 0)
    (hc : c = (1 - β) * ((1 + r) * b + (1 + r) / (r - g) * y))
    (hb : b' = ((1 + r) * b + y - c) / (1 + n)) :
    b' / ((1 + g) * y) = (1 + r) * β / ((1 + n) * (1 + g)) * (b / y)
      + ((1 + r) * β - (1 + g)) / ((1 + n) * (1 + g) * (r - g)) := by
  have : r - g ≠ 0 := by linarith
  rw [weil_growth_law hn hgr hc hb]
  field_simp

/-- Steady-state net-foreign-asset/output ratio of (3.73), O&R p. 188:
`((1 + r) β - (1 + g)) / ([(1 + n)(1 + g) - (1 + r) β] (r - g))`. -/
noncomputable def growthSteadyRatio (r β n g : ℝ) : ℝ :=
  ((1 + r) * β - (1 + g)) / (((1 + n) * (1 + g) - (1 + r) * β) * (r - g))

/-- The ratio `growthSteadyRatio` is the fixed point of (3.73), O&R p. 188. -/
theorem growthSteadyRatio_fixed {r β n g : ℝ} (hn : 0 < 1 + n) (hg : 0 < 1 + g) (hgr : g < r)
    (hstab : (1 + r) * β ≠ (1 + n) * (1 + g)) :
    growthSteadyRatio r β n g = (1 + r) * β / ((1 + n) * (1 + g)) * growthSteadyRatio r β n g
      + ((1 + r) * β - (1 + g)) / ((1 + n) * (1 + g) * (r - g)) := by
  have h1 : (1 + n) * (1 + g) - (1 + r) * β ≠ 0 := sub_ne_zero.mpr (Ne.symm hstab)
  have h2 : r - g ≠ 0 := by linarith
  have hNG : (1 + n) * (1 + g) ≠ 0 := mul_ne_zero hn.ne' hg.ne'
  unfold growthSteadyRatio
  rw [div_mul_div_comm, div_add_div _ _ (mul_ne_zero hNG (mul_ne_zero h1 h2))
    (mul_ne_zero hNG h2), div_eq_div_iff (mul_ne_zero h1 h2)
    (mul_ne_zero (mul_ne_zero hNG (mul_ne_zero h1 h2)) (mul_ne_zero hNG h2))]
  ring

/-- Sign of the long-run asset/output ratio, O&R p. 188: under the stability condition
`(1 + r) β < (1 + n)(1 + g)` and `g < r`, net foreign assets are positive iff
`β (1 + r) > 1 + g`. -/
theorem growthSteadyRatio_pos_iff {r β n g : ℝ} (hgr : g < r)
    (hstab : (1 + r) * β < (1 + n) * (1 + g)) :
    0 < growthSteadyRatio r β n g ↔ 1 + g < (1 + r) * β := by
  have hd : 0 < ((1 + n) * (1 + g) - (1 + r) * β) * (r - g) :=
    mul_pos (by linarith) (by linarith)
  unfold growthSteadyRatio
  rw [div_pos_iff_of_pos_right hd, sub_pos]

/-- Partial-fraction form of the long-run asset/output ratio (O&R p. 188), with
`A = (1 + r) β`: `[n A/((1 + n)(1 + g) - A) - ((1 + r) - A)/(r - g)] / ((1 + n)(1 + r) - A)`. -/
theorem growthSteadyRatio_partial_fractions {r β n g : ℝ}
    (h1 : (1 + n) * (1 + g) - (1 + r) * β ≠ 0) (h2 : r - g ≠ 0)
    (h3 : (1 + n) * (1 + r) - (1 + r) * β ≠ 0) :
    growthSteadyRatio r β n g =
      (n * ((1 + r) * β) / ((1 + n) * (1 + g) - (1 + r) * β)
        - ((1 + r) - (1 + r) * β) / (r - g)) / ((1 + n) * (1 + r) - (1 + r) * β) := by
  unfold growthSteadyRatio
  rw [div_sub_div _ _ h1 h2, div_div, div_eq_div_iff (mul_ne_zero h1 h2)
    (mul_ne_zero (mul_ne_zero h1 h2) h3)]
  ring

/-- "A rise in the growth rate `g` always lowers the economy's long-run net-foreign-asset-to-output
ratio", O&R p. 188 (no proof in the book). Proved for `n ≥ 0`, `0 < β < 1`, `r > -1`, on the
region where (3.73) is stable (`(1 + r) β < (1 + n)(1 + g)`) and `g < r`: the ratio is strictly
decreasing in `g`. No case split on the sign of `β (1 + r) - (1 + g)` is needed. -/
theorem growthSteadyRatio_strictAntiOn {r β n : ℝ} (hn : 0 ≤ n) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hr : 0 < 1 + r) :
    StrictAntiOn (growthSteadyRatio r β n)
      {g | (1 + r) * β < (1 + n) * (1 + g) ∧ g < r} := by
  intro g1 hg1 g2 hg2 hlt
  obtain ⟨hs1, hr1⟩ := hg1
  obtain ⟨hs2, hr2⟩ := hg2
  have hA : 0 < (1 + r) * β := mul_pos hr hβ0
  have hRA : 0 < (1 + r) - (1 + r) * β := by nlinarith
  have hD : 0 < (1 + n) * (1 + r) - (1 + r) * β := by nlinarith
  have hu1 : 0 < (1 + n) * (1 + g1) - (1 + r) * β := by linarith
  have hu12 : (1 + n) * (1 + g1) - (1 + r) * β ≤ (1 + n) * (1 + g2) - (1 + r) * β := by
    nlinarith
  rw [growthSteadyRatio_partial_fractions hu1.ne' (by linarith) hD.ne',
    growthSteadyRatio_partial_fractions (by linarith) (by linarith) hD.ne',
    div_lt_div_iff_of_pos_right hD]
  have t1 : n * ((1 + r) * β) / ((1 + n) * (1 + g2) - (1 + r) * β) ≤
      n * ((1 + r) * β) / ((1 + n) * (1 + g1) - (1 + r) * β) :=
    div_le_div_of_nonneg_left (by positivity) hu1 hu12
  have t2 : ((1 + r) - (1 + r) * β) / (r - g1) < ((1 + r) - (1 + r) * β) / (r - g2) :=
    div_lt_div_of_pos_left hRA (by linarith) (by linarith)
  linarith

/-! ## §3.7.6.1 Temporary shocks with `(1 + r) β = 1` -/

/-- O&R p. 189: when `(1 + r) β = 1`, the law of motion (3.69) is `b_{t+1} = b_t / (1 + n)`. -/
theorem weil_unit_tilt_law {r β n ybar : ℝ} (htilt : (1 + r) * β = 1) (b : ℝ) :
    weilSlope r β n * b + weilIntercept r β n ybar = b / (1 + n) := by
  unfold weilSlope weilIntercept
  rw [htilt]
  ring

/-- O&R p. 189: with `(1 + r) β = 1` the steady state is `b̄ = 0` and `c̄ = ȳ`. -/
theorem weil_unit_tilt_steady {r β n ybar : ℝ} (htilt : (1 + r) * β = 1) :
    weilSteadyB r β n ybar = 0 ∧ weilSteadyC r β n ybar = ybar := by
  have h0 : weilSteadyB r β n ybar = 0 := by unfold weilSteadyB; rw [htilt]; ring
  exact ⟨h0, by unfold weilSteadyC; rw [h0]; ring⟩

/-- O&R p. 189: with `(1 + r) β = 1` and zero population growth, `b_{t+1} = b_t`, so a
transitory shock has permanent effects on foreign assets. -/
theorem weil_unit_tilt_zero_growth {r β ybar : ℝ} (htilt : (1 + r) * β = 1) {b : ℕ → ℝ}
    (hb : ∀ k, b (k + 1) = weilSlope r β 0 * b k + weilIntercept r β 0 ybar) (k : ℕ) :
    b k = b 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [hb k, weil_unit_tilt_law htilt, ih]; ring

/-- The impact effect of a transitory shock, O&R p. 190: consumption on the shock date rises by
`(1 - β)(ȳ' - ȳ)` relative to the no-shock path, whatever the population growth rate (`n` does
not enter). Holds for any `b_t`, not only under `(1 + r) β = 1`. -/
theorem weil_transitory_consumption_jump {r β ybar ybar' b H H' : ℝ} (hr : 0 < r)
    (hH : HasSum (fun k : ℕ => ((1 + r)⁻¹) ^ k * ybar) H)
    (hH' : HasSum (fun k : ℕ => ((1 + r)⁻¹) ^ k * (if k = 0 then ybar' else ybar)) H') :
    (1 - β) * ((1 + r) * b + H') - (1 - β) * ((1 + r) * b + H) = (1 - β) * (ybar' - ybar) := by
  rw [hH.unique (weil_hasSum_const hr ybar), hH'.unique (weil_hasSum_transitory hr ybar ybar')]
  ring

/-! ## §3.7.6.2 Government debt, (3.74)–(3.75) -/

/-- The uniform tax that holds per capita debt at `d̄`, O&R (3.75), p. 190: in the per capita
government constraint (3.74) `b^G_{t+1} = [(1 + r) b^G_t + τ_t - g_t]/(1 + n)`, the level
`b^G = -d̄` is maintained iff `τ = (r - n) d̄ + g`. -/
theorem weil_debt_tax {n r d τ g : ℝ} (hn : 0 < 1 + n) :
    -d = ((1 + r) * -d + τ - g) / (1 + n) ↔ τ = (r - n) * d + g := by
  rw [eq_div_iff hn.ne']
  constructor <;> intro h <;> linarith

/-- Consumption with a constant government debt, O&R p. 191: with `b^P = b + d̄` and taxes
(3.75), `c_t = (1 - β)[(1 + r)(b_t + n d̄/r) + Σ (1 + r)^{-(s-t)} (y_s - g_s)]`. -/
theorem weil_debt_consumption {n r β d b c Hyτ Hyg : ℝ} {y τ g : ℕ → ℝ} (hr : 0 < r)
    (hτ : ∀ k, τ k = (r - n) * d + g k)
    (hyτ : HasSum (fun k => ((1 + r)⁻¹) ^ k * (y k - τ k)) Hyτ)
    (hyg : HasSum (fun k => ((1 + r)⁻¹) ^ k * (y k - g k)) Hyg)
    (hc : c = (1 - β) * ((1 + r) * (b + d) + Hyτ)) :
    c = (1 - β) * ((1 + r) * (b + n * d / r) + Hyg) := by
  have h := hyg.sub (weil_hasSum_const hr ((r - n) * d))
  have e : Hyτ = Hyg - (1 + r) / r * ((r - n) * d) := by
    refine hyτ.unique ?_
    convert h using 1
    funext k
    rw [hτ k]
    ring
  rw [hc, e]
  field_simp
  ring

/-- Debt is net wealth iff `n > 0`, O&R p. 191: raising per capita debt from `d̄` to `d̄'` raises
consumption by `(1 - β)(1 + r) n (d̄' - d̄)/r`. -/
theorem weil_debt_consumption_change (n r β b d d' H : ℝ) (hr : r ≠ 0) :
    (1 - β) * ((1 + r) * (b + n * d' / r) + H) - (1 - β) * ((1 + r) * (b + n * d / r) + H)
      = (1 - β) * (1 + r) * n * (d' - d) / r := by
  field_simp
  ring

/-- Ricardian equivalence exactly at `n = 0`, O&R p. 191: with `β < 1`, `r > 0`, consumption
`(1 - β)[(1 + r)(b + n d̄/r) + H]` is independent of the debt level `d̄` iff `n = 0`. -/
theorem weil_ricardian_iff {n r β b H : ℝ} (hr : 0 < r) (hβ : β < 1) :
    (∀ d : ℝ, (1 - β) * ((1 + r) * (b + n * d / r) + H) =
        (1 - β) * ((1 + r) * (b + n * 0 / r) + H)) ↔ n = 0 := by
  constructor
  · intro h
    have h1 := h 1
    have e := weil_debt_consumption_change n r β b 0 1 H hr.ne'
    rw [h1, sub_self] at e
    have hk : (1 - β) * (1 + r) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
    have h2 : (1 - β) * (1 + r) * n * (1 - 0) / r = 0 := e.symm
    rw [div_eq_zero_iff, sub_zero, mul_one] at h2
    rcases h2 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 hk
      · exact h3
    · exact absurd h2 hr.ne'
  · rintro rfl d
    simp

/-! ## Exercise 5: arbitrary debt paths -/

/-- Exercise 5, O&R p. 197 (Weil model with an arbitrary non-Ponzi debt path `d`). With
`b^P = b + d_t`, taxes from (3.74) with `b^G = -d`, namely
`τ_s = g_s + (1 + r) d_s - (1 + n) d_{s+1}`, and a summable discounted debt path,
`c_t = (1 - β)[(1 + r) b_t + Σ (1 + r)^{-(s-t)}(y_s - g_s) + n Σ (1 + r)^{-(s-t)} d_{s+1}]`. -/
theorem weil_debt_path_consumption {n r β b c Hyτ Hyg S0 : ℝ} {y τ g d : ℕ → ℝ}
    (hr : 0 < 1 + r) (hτ : ∀ k, τ k = g k + (1 + r) * d k - (1 + n) * d (k + 1))
    (hd : HasSum (fun k => ((1 + r)⁻¹) ^ k * d k) S0)
    (hyτ : HasSum (fun k => ((1 + r)⁻¹) ^ k * (y k - τ k)) Hyτ)
    (hyg : HasSum (fun k => ((1 + r)⁻¹) ^ k * (y k - g k)) Hyg)
    (hc : c = (1 - β) * ((1 + r) * (b + d 0) + Hyτ)) :
    HasSum (fun k => ((1 + r)⁻¹) ^ k * d (k + 1)) ((1 + r) * (S0 - d 0)) ∧
      c = (1 - β) * ((1 + r) * b + Hyg + n * ∑' k, ((1 + r)⁻¹) ^ k * d (k + 1)) := by
  have hr0 : (1 + r) ≠ 0 := hr.ne'
  have hS1 : HasSum (fun k => ((1 + r)⁻¹) ^ k * d (k + 1)) ((1 + r) * (S0 - d 0)) := by
    have h := (hasSum_nat_add_iff' 1).mpr hd
    simp only [range_one, sum_singleton, pow_zero, one_mul] at h
    convert h.mul_left (1 + r) using 1
    funext k
    rw [pow_succ]
    field_simp
  refine ⟨hS1, ?_⟩
  have e : Hyτ = Hyg - (1 + r) * S0 + (1 + n) * ((1 + r) * (S0 - d 0)) := by
    refine hyτ.unique ?_
    convert (hyg.sub (hd.mul_left (1 + r))).add (hS1.mul_left (1 + n)) using 1
    funext k
    rw [hτ k]
    ring
  rw [hS1.tsum_eq, hc, e]
  ring

/-- Exercise 5, O&R p. 197, in the book's form:
`c_t = (1 - β){(1 + r)(n/r) d_t + Σ (1 + r)^{-(s-t)} ((1 + r)/r) n (d_{s+1} - d_s)
  + (1 + r) b_t + Σ (1 + r)^{-(s-t)} (y_s - g_s)}` (verified; needs `r ≠ 0`). -/
theorem weil_debt_path_consumption_book {n r β b c Hyτ Hyg S0 : ℝ} {y τ g d : ℕ → ℝ}
    (hr : 0 < r) (hτ : ∀ k, τ k = g k + (1 + r) * d k - (1 + n) * d (k + 1))
    (hd : HasSum (fun k => ((1 + r)⁻¹) ^ k * d k) S0)
    (hyτ : HasSum (fun k => ((1 + r)⁻¹) ^ k * (y k - τ k)) Hyτ)
    (hyg : HasSum (fun k => ((1 + r)⁻¹) ^ k * (y k - g k)) Hyg)
    (hc : c = (1 - β) * ((1 + r) * (b + d 0) + Hyτ)) :
    c = (1 - β) * ((1 + r) * (n / r) * d 0
      + ∑' k, ((1 + r)⁻¹) ^ k * ((1 + r) / r * n * (d (k + 1) - d k))
      + (1 + r) * b + Hyg) := by
  obtain ⟨hS1, hcons⟩ := weil_debt_path_consumption (by linarith) hτ hd hyτ hyg hc
  have hdiff : HasSum (fun k => ((1 + r)⁻¹) ^ k * ((1 + r) / r * n * (d (k + 1) - d k)))
      ((1 + r) / r * n * ((1 + r) * (S0 - d 0) - S0)) := by
    convert (hS1.sub hd).mul_left ((1 + r) / r * n) using 1
    funext k
    ring
  rw [hcons, hS1.tsum_eq, hdiff.tsum_eq]
  field_simp
  ring

/-! ## Exercise 3: Blanchard (1985) perpetual youth

Timing (consistent with parts (c)–(e) of the exercise): `b^v_t` is what an individual of age
`a = t - v` carried out of date `t - 1` as an annuity; survivors are paid `(1 + r)/φ` per unit.
With cohort masses `φ^a`, aggregate private net foreign assets at the start of `t` (the savings
of everyone alive at `t - 1`, including those who then died) are `B_t = (Σ_a φ^a b_t(a))/φ`,
while `C_t = Σ_a φ^a c_t(a)` and `Y_t - T_t = Σ_a φ^a (y - τ) = (y - τ)/(1 - φ)`. -/

/-- Exercise 3(a), O&R p. 196: with a unit cohort born each period and survival probability
`φ`, the cohort of age `a` has mass `φ^a` and total population is `1/(1 - φ)`. -/
theorem blanchard_population {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ < 1) :
    HasSum (fun a : ℕ => φ ^ a) (1 / (1 - φ)) := by
  rw [one_div]
  exact hasSum_geometric_of_lt_one h0 h1

/-- Exercise 3(b), O&R p. 196: an insurer that holds a saver's `b ≠ 0` at the world rate and
pays gross `R` to the fraction `φ > 0` who survive makes zero profit iff `R = (1 + r)/φ`. -/
theorem blanchard_annuity_zero_profit {φ r R b : ℝ} (hφ : 0 < φ) (hb : b ≠ 0) :
    (1 + r) * b - φ * (R * b) = 0 ↔ R = (1 + r) / φ := by
  rw [eq_div_iff hφ.ne']
  constructor
  · intro h
    have : ((1 + r) - R * φ) * b = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact absurd h' hb
  · intro h
    linear_combination (-b) * h

/-- Exercise 3(c), O&R p. 196: with the annuity return `(1 + r)/φ`, the flow constraint
`b_{k+1} = ((1 + r)/φ) b_k + (y_k - τ_k) - c_k` and no-Ponzi give the budget constraint
`Σ (φ/(1 + r))^k c_k = ((1 + r)/φ) b_0 + Σ (φ/(1 + r))^k (y_k - τ_k)`. -/
theorem blanchard_budget {φ r : ℝ} (hφ : 0 < φ) (hr : 0 < 1 + r) {b x c : ℕ → ℝ}
    (hflow : ∀ k, b (k + 1) = (1 + r) / φ * b k + x k - c k) {X C : ℝ}
    (hX : HasSum (fun k => (φ / (1 + r)) ^ k * x k) X)
    (hC : HasSum (fun k => (φ / (1 + r)) ^ k * c k) C)
    (hNP : Tendsto (fun T => (φ / (1 + r)) ^ T * b T) atTop (𝓝 0)) :
    C = (1 + r) / φ * b 0 + X := by
  have hRρ : (1 + r) / φ * (φ / (1 + r)) = 1 := by field_simp
  exact perpetual_ibc_of_flow hRρ hflow hX hC hNP

/-- Exercise 3(c)–(d), O&R p. 196: with log utility the Euler equation is
`c_{k+1} = (1 + r) β c_k` (effective discount `φ β`, return `(1 + r)/φ`), and the individual
consumption function is `c_0 = (1 - φ β) [((1 + r)/φ) b_0 + Σ (φ/(1 + r))^k (y_k - τ_k)]`. -/
theorem blanchard_consumption_function {φ r β : ℝ} (hφ : 0 < φ) (hr : 0 < 1 + r)
    (hδ0 : 0 ≤ φ * β) (hδ1 : φ * β < 1) {b x c : ℕ → ℝ}
    (hflow : ∀ k, b (k + 1) = (1 + r) / φ * b k + x k - c k)
    (heuler : ∀ k, c (k + 1) = (1 + r) * β * c k) {X C : ℝ}
    (hX : HasSum (fun k => (φ / (1 + r)) ^ k * x k) X)
    (hC : HasSum (fun k => (φ / (1 + r)) ^ k * c k) C)
    (hNP : Tendsto (fun T => (φ / (1 + r)) ^ T * b T) atTop (𝓝 0)) :
    c 0 = (1 - φ * β) * ((1 + r) / φ * b 0 + X) := by
  rw [← blanchard_budget hφ hr hflow hX hC hNP]
  refine perpetual_consumption_of_euler hδ0 hδ1 (fun k => ?_) hC
  rw [heuler k]
  field_simp

/-- Blanchard human wealth for constant after-tax income, Exercise 3(e), O&R p. 196: for
`0 ≤ φ < 1 + r`, `Σ (φ/(1 + r))^k x = (1 + r) x / (1 + r - φ)`. -/
theorem blanchard_hasSum_const {φ r : ℝ} (hφ : 0 ≤ φ) (hφr : φ < 1 + r) (x : ℝ) :
    HasSum (fun k : ℕ => (φ / (1 + r)) ^ k * x) ((1 + r) / (1 + r - φ) * x) := by
  have hr : 0 < 1 + r := by linarith
  have h0 : 0 ≤ φ / (1 + r) := div_nonneg hφ hr.le
  have h1 : φ / (1 + r) < 1 := by rw [div_lt_one hr]; exact hφr
  have h := (hasSum_geometric_of_lt_one h0 h1).mul_right x
  have e : 1 - φ / (1 + r) = (1 + r - φ) / (1 + r) := by field_simp
  rwa [e, inv_div] at h

/-- Exercise 3(d), O&R p. 196: aggregate private assets obey
`B_{t+1} = (1 + r) B_t + Y_t - T_t - C_t`. Here each age-`a` individual carries
`b'(a + 1) = ((1 + r)/φ) b(a) + x - c(a)` into `t + 1`, newborns carry nothing (`b'(0) = 0`),
`Σ φ^a b(a) = φ B_t`, `Σ φ^a c(a) = C_t` and `Y_t - T_t = x/(1 - φ)`; the conclusion is
`Σ φ^a b'(a) = φ [(1 + r) B_t + x/(1 - φ) - C_t]`, i.e. `B_{t+1} = (1 + r) B_t + Y - T - C`. -/
theorem blanchard_aggregate_accumulation {φ r x Bs Cs : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1)
    {b b' c : ℕ → ℝ} (hB : HasSum (fun a => φ ^ a * b a) Bs)
    (hC : HasSum (fun a => φ ^ a * c a) Cs)
    (hflow : ∀ a, b' (a + 1) = (1 + r) / φ * b a + x - c a) (hnew : b' 0 = 0) :
    HasSum (fun a => φ ^ a * b' a) (φ * ((1 + r) * (Bs / φ) + x * (1 - φ)⁻¹ - Cs)) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [range_one, sum_singleton, pow_zero, hnew, mul_zero, sub_zero]
  have h := ((hB.mul_left (1 + r)).add
    ((hasSum_geometric_of_lt_one hφ0.le hφ1).mul_left (φ * x))).sub (hC.mul_left φ)
  convert h using 1
  · funext a
    rw [hflow a, pow_succ]
    field_simp
  · field_simp

/-- Exercise 3(e), aggregate consumption, O&R p. 196: aggregating the consumption functions
`c(a) = (1 - φ β)[((1 + r)/φ) b(a) + (1 + r) x/(1 + r - φ)]` gives
`C = (1 - φ β)[(1 + r) B + (1 + r)(Y - T)/(1 + r - φ)]` with `B = Bs/φ`, `Y - T = x/(1 - φ)`. -/
theorem blanchard_aggregate_consumption {φ r β x Bs : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1)
    {b c : ℕ → ℝ} (hB : HasSum (fun a => φ ^ a * b a) Bs)
    (hc : ∀ a, c a = (1 - φ * β) * ((1 + r) / φ * b a + (1 + r) / (1 + r - φ) * x)) :
    HasSum (fun a => φ ^ a * c a)
      ((1 - φ * β) * ((1 + r) * (Bs / φ) + (1 + r) / (1 + r - φ) * (x * (1 - φ)⁻¹))) := by
  have h := (hB.mul_left ((1 - φ * β) * ((1 + r) / φ))).add
    ((hasSum_geometric_of_lt_one hφ0.le hφ1).mul_left ((1 - φ * β) * ((1 + r) / (1 + r - φ) * x)))
  convert h using 1
  · funext a
    rw [hc a]
    ring
  · ring

/-- Exercise 3(e), O&R p. 196 (verified): with constant `Y` and `T`,
`B_{t+1} = φ β (1 + r) B_t + φ [((1 + r) β - 1)/(1 + r - φ)] (Y - T)`. Stated with
`φ B_{t+1} = Σ φ^a b'(a)`, `B_t = Bs/φ` and `Y - T = x/(1 - φ)`. -/
theorem blanchard_law_of_motion {φ r β x Bs : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) (hφr : φ < 1 + r)
    {b b' c : ℕ → ℝ} (hB : HasSum (fun a => φ ^ a * b a) Bs)
    (hc : ∀ a, c a = (1 - φ * β) * ((1 + r) / φ * b a + (1 + r) / (1 + r - φ) * x))
    (hflow : ∀ a, b' (a + 1) = (1 + r) / φ * b a + x - c a) (hnew : b' 0 = 0) :
    HasSum (fun a => φ ^ a * b' a)
      (φ * (φ * β * (1 + r) * (Bs / φ)
        + φ * (((1 + r) * β - 1) / (1 + r - φ)) * (x * (1 - φ)⁻¹))) := by
  have hC := blanchard_aggregate_consumption hφ0 hφ1 hB hc (β := β)
  convert blanchard_aggregate_accumulation hφ0 hφ1 hB hC hflow hnew using 1
  have : 1 + r - φ ≠ 0 := by linarith
  have : 1 - φ ≠ 0 := by linarith
  field_simp
  ring

/-- Steady-state national net foreign assets with public debt `D`, Exercise 3(f), O&R p. 197:
the household assets `B^P` solve the steady state of 3(e) with `Y - T = Y - r D`, and national
assets are `B = B^P - D`. -/
noncomputable def blanchardSteadyB (r β φ Y D : ℝ) : ℝ :=
  φ * ((1 + r) * β - 1) / (1 + r - φ) * (Y - r * D) / (1 - φ * β * (1 + r)) - D

/-- Exercise 3(f), O&R p. 197: a uniform tax `τ = r D (1 - φ)` on a population of `1/(1 - φ)`
raises total taxes `T = r D`, which is exactly what keeps `B^G = -D` constant with `G = 0` in
`B^G_{t+1} = (1 + r) B^G_t + T - G`. -/
theorem blanchard_debt_tax {φ r D : ℝ} (hφ : φ < 1) :
    r * D * (1 - φ) * (1 - φ)⁻¹ = r * D ∧
      (-D = (1 + r) * -D + r * D * (1 - φ) * (1 - φ)⁻¹ - 0) := by
  have : 1 - φ ≠ 0 := by linarith
  have e : r * D * (1 - φ) * (1 - φ)⁻¹ = r * D := by field_simp
  exact ⟨e, by rw [e]; ring⟩

/-- Exercise 3(f), O&R p. 197: `B^P = blanchardSteadyB + D` is the steady state of the private
law of motion 3(e) with `Y - T = Y - r D`. -/
theorem blanchardSteadyB_private_fixed {r β φ Y D : ℝ} (hφr : φ < 1 + r)
    (hstab : φ * β * (1 + r) < 1) :
    blanchardSteadyB r β φ Y D + D = φ * β * (1 + r) * (blanchardSteadyB r β φ Y D + D)
      + φ * (((1 + r) * β - 1) / (1 + r - φ)) * (Y - r * D) := by
  have h1 : 1 + r - φ ≠ 0 := by linarith
  have h2 : 1 - φ * β * (1 + r) ≠ 0 := by linarith
  unfold blanchardSteadyB
  have e1 : φ * ((1 + r) * β - 1) = φ * β * (1 + r) - φ := by ring
  have e3 : φ * (((1 + r) * β - 1) / (1 + r - φ)) = (φ * β * (1 + r) - φ) / (1 + r - φ) := by
    rw [← e1]; ring
  rw [e1, e3]
  generalize φ * β * (1 + r) = a at h2 ⊢
  field_simp
  ring

/-- Exercise 3(f), O&R p. 197: effect of debt on steady-state national net foreign assets,
`B̄(D) = B̄(0) - [(1 + r)(1 - φ)(1 - φ β) / ((1 + r - φ)(1 - φ β (1 + r)))] D`. -/
theorem blanchardSteadyB_debt {r β φ Y D : ℝ} (hφr : φ < 1 + r) (hstab : φ * β * (1 + r) < 1) :
    blanchardSteadyB r β φ Y D = blanchardSteadyB r β φ Y 0
      - (1 + r) * (1 - φ) * (1 - φ * β) / ((1 + r - φ) * (1 - φ * β * (1 + r))) * D := by
  have h1 : 1 + r - φ ≠ 0 := by linarith
  have h2 : 1 - φ * β * (1 + r) ≠ 0 := by linarith
  unfold blanchardSteadyB
  have e1 : φ * ((1 + r) * β - 1) = φ * β * (1 + r) - φ := by ring
  have e2 : (1 + r) * (1 - φ) * (1 - φ * β) = (1 - φ) * ((1 + r) - φ * β * (1 + r)) := by ring
  rw [e1, e2]
  generalize φ * β * (1 + r) = a at h2 ⊢
  field_simp
  ring

/-- Exercise 3(f), O&R p. 197: with `0 < φ < 1`, `r > 0` and stability
`φ β (1 + r) < 1`, public debt `D > 0` lowers steady-state national net foreign assets, and
hence steady-state consumption `C̄ = r B̄ + Y` (from `B = (1 + r) B + Y - C` with `G = 0`). -/
theorem blanchard_debt_lowers {r β φ Y D : ℝ} (hr : 0 < r) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hstab : φ * β * (1 + r) < 1) (hD : 0 < D) :
    blanchardSteadyB r β φ Y D < blanchardSteadyB r β φ Y 0 ∧
      r * blanchardSteadyB r β φ Y D + Y < r * blanchardSteadyB r β φ Y 0 + Y := by
  have hφr : φ < 1 + r := by linarith
  have hk : 0 < (1 + r) * (1 - φ) * (1 - φ * β) / ((1 + r - φ) * (1 - φ * β * (1 + r))) := by
    have : 0 < 1 - φ * β := by nlinarith
    have : 0 < 1 + r - φ := by linarith
    have : 0 < 1 - φ * β * (1 + r) := by linarith
    have : 0 < 1 - φ := by linarith
    have : 0 < 1 + r := by linarith
    positivity
  have h1 : blanchardSteadyB r β φ Y D < blanchardSteadyB r β φ Y 0 := by
    rw [blanchardSteadyB_debt hφr hstab]
    nlinarith
  exact ⟨h1, by nlinarith⟩

/-- Exercise 3(f), O&R p. 197: steady-state national consumption, `C̄ = r B̄ + Y`, from the
national constraint `B = (1 + r) B + Y - C` (private plus government, `G = 0`). -/
theorem blanchard_steady_consumption {r B Y C : ℝ} (h : B = (1 + r) * B + Y - C) :
    C = r * B + Y := by linarith

/-- Exercise 3(f), O&R p. 197: in the representative-agent limit `φ = 1`, debt leaves steady
state national assets unchanged (Ricardian equivalence). -/
theorem blanchardSteadyB_ricardian {r β Y D : ℝ} (hr : 0 < r) (hstab : 1 * β * (1 + r) < 1) :
    blanchardSteadyB r β 1 Y D = blanchardSteadyB r β 1 Y 0 := by
  rw [blanchardSteadyB_debt (by linarith) hstab]
  ring

end ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Dynamic inefficiency

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Appendix 3A, pp. 191–195. Output per efficiency unit of labour is `f(k)`, and
efficiency labour grows at `1 + z = (1 + n)(1 + g)`. Capital per efficiency unit
obeys `k_{t+1} = (k_t + f(k_t) − c_t)/(1 + z)`.

* **Steady-state consumption and the golden rule** (O&R (3.77)–(3.78)): steady-state
  consumption is `c̄ = f(k̄) − zk̄`. For concave `f` it is maximised where
  `f'(k̄) = r̄ = z`.
* **Pareto inefficiency when `r̄ < z`** (pp. 192–193). If `f'(k̄) < z`, cut capital once
  to some `k < k̄` with `f'(k) ≤ z` (one always exists nearby) and hold it there. Total
  consumption is strictly higher on the first date and at least as high on every
  later date, so everyone can be made better off. If instead `f'(k̄) > z`, raising
  capital requires lower consumption on the first date.
* **Ponzi games** (§3A.2.1): debt rolled over at rate `r` shrinks relative to output
  growing at `z` iff `r < z`.
* **Bubbles** (§3A.2.2): a paper asset whose price rises at `r` stays affordable to
  the young forever when `r ≤ z` (given an affordable start), but not when `r > z`.
* **The empirical criterion** (§3A.3): `r > z` iff the profit share `rK/Y` exceeds the
  investment share `zK/Y`.

The converse — that `r̄ > z` rules out every Pareto improvement (Cass 1972) — is
deferred by the book to Chapter 7 and is not formalised here.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency

open Set Filter Topology

/-- Steady-state consumption per efficiency unit `c̄ = f(k̄) − zk̄`, O&R (3.77). -/
def steadyConsumption (f : ℝ → ℝ) (z k : ℝ) : ℝ := f k - z * k

/-- The law of motion `k_{t+1} = (k_t + f(k_t) − c_t)/(1 + z)` holds with constant `k` iff
consumption is `c̄ = f(k) − zk` (O&R p. 192). -/
theorem steady_state_iff {f : ℝ → ℝ} {z k c : ℝ} (hz : 0 < 1 + z) :
    k = (k + f k - c) / (1 + z) ↔ c = steadyConsumption f z k := by
  unfold steadyConsumption
  rw [eq_div_iff hz.ne']
  constructor <;> intro h <;> linarith

/-- Consumption on the transition date: moving capital from `k` today to `k'` next period leaves
`c = k + f(k) − (1 + z)k'` for consumption (O&R p. 192). -/
def transitionConsumption (f : ℝ → ℝ) (z k k' : ℝ) : ℝ := k + f k - (1 + z) * k'

/-- **The golden rule**, O&R (3.78), p. 192: for concave differentiable `f`, capital with
`f'(k_G) = z` maximises steady-state consumption. -/
theorem golden_rule_max {f f' : ℝ → ℝ} {z kG : ℝ} (hconc : ConcaveOn ℝ (Ioi 0) f)
    (hd : ∀ k, 0 < k → HasDerivAt f (f' k) k) (hkG : 0 < kG) (hG : f' kG = z) {k : ℝ}
    (hk : 0 < k) : steadyConsumption f z k ≤ steadyConsumption f z kG := by
  unfold steadyConsumption
  rcases lt_trichotomy k kG with hlt | rfl | hgt
  · have h := hconc.le_slope_of_hasDerivAt hk hkG hlt (hd kG hkG)
    rw [slope_def_field, le_div_iff₀ (by linarith), hG] at h
    linarith
  · exact le_rfl
  · have h := hconc.slope_le_of_hasDerivAt hkG hk hgt (hd kG hkG)
    rw [slope_def_field, div_le_iff₀ (by linarith), hG] at h
    linarith

/-- **The golden rule is a stationary point**, O&R (3.78): `dc̄/dk = f'(k) − z`, zero iff
`f'(k) = z`. -/
theorem hasDerivAt_steadyConsumption {f : ℝ → ℝ} {z k d : ℝ} (hd : HasDerivAt f d k) :
    HasDerivAt (steadyConsumption f z) (d - z) k := by
  unfold steadyConsumption
  have h2 : HasDerivAt (fun y => z * y) z k := by simpa using (hasDerivAt_id k).const_mul z
  exact HasDerivAt.sub hd h2

/-- **Lower capital raises steady-state consumption when `f' ≤ z` there**: for concave `f`, if
`k < k̄` and `f'(k) ≤ z`, then `c̄(k) ≥ c̄(k̄)`. -/
theorem steadyConsumption_ge_of_lower {f f' : ℝ → ℝ} {z k kbar : ℝ}
    (hconc : ConcaveOn ℝ (Ioi 0) f) (hd : ∀ k, 0 < k → HasDerivAt f (f' k) k) (hk : 0 < k)
    (hlt : k < kbar) (hfk : f' k ≤ z) :
    steadyConsumption f z kbar ≤ steadyConsumption f z k := by
  unfold steadyConsumption
  have h := hconc.slope_le_of_hasDerivAt hk (hk.trans hlt) hlt (hd k hk)
  rw [slope_def_field, div_le_iff₀ (by linarith)] at h
  nlinarith

/-- **The transition date gains**, O&R pp. 192–193: cutting capital from `k̄` to `k < k̄` raises
consumption on the transition date above its steady-state level by `(1 + z)(k̄ − k) > 0`. -/
theorem transition_gain {f : ℝ → ℝ} {z k kbar : ℝ} (hz : 0 < 1 + z) (hlt : k < kbar) :
    transitionConsumption f z kbar k - steadyConsumption f z kbar = (1 + z) * (kbar - k) ∧
      steadyConsumption f z kbar < transitionConsumption f z kbar k := by
  unfold transitionConsumption steadyConsumption
  constructor
  · ring
  · nlinarith

/-- **Near an inefficient steady state there is a better capital level**: if `f'` is continuous at
`k̄ > 0` and `f'(k̄) < z`, some `0 < k < k̄` has `f'(k) < z`. -/
theorem exists_lower_capital {f' : ℝ → ℝ} {z kbar : ℝ} (hkbar : 0 < kbar)
    (hcont : ContinuousAt f' kbar) (hineff : f' kbar < z) :
    ∃ k, 0 < k ∧ k < kbar ∧ f' k < z := by
  have hev : ∀ᶠ k in 𝓝 kbar, f' k < z := hcont.eventually (gt_mem_nhds hineff)
  have hev' : ∀ᶠ k in 𝓝[<] kbar, f' k < z ∧ 0 < k :=
    (hev.filter_mono nhdsWithin_le_nhds).and
      ((lt_mem_nhds hkbar : ∀ᶠ k in 𝓝 kbar, 0 < k).filter_mono nhdsWithin_le_nhds)
  obtain ⟨k, ⟨hfk, hk0⟩, hklt⟩ := (hev'.and self_mem_nhdsWithin).exists
  exact ⟨k, hk0, hklt, hfk⟩

/-- **Dynamic inefficiency implies Pareto inefficiency**, O&R pp. 192–193: if `f` is concave and
differentiable with `f'` continuous at the steady state and `f'(k̄) = r̄ < z`, there is a feasible
capital path — cut to some `k < k̄` once and hold it there — along which total consumption is
strictly higher on the transition date and at least as high on every later date. -/
theorem pareto_improvement_of_dynamically_inefficient {f f' : ℝ → ℝ} {z kbar : ℝ}
    (hz : 0 < 1 + z) (hconc : ConcaveOn ℝ (Ioi 0) f) (hd : ∀ k, 0 < k → HasDerivAt f (f' k) k)
    (hkbar : 0 < kbar) (hcont : ContinuousAt f' kbar) (hineff : f' kbar < z) :
    ∃ k, 0 < k ∧ k < kbar ∧
      steadyConsumption f z kbar < transitionConsumption f z kbar k ∧
      steadyConsumption f z kbar ≤ steadyConsumption f z k := by
  obtain ⟨k, hk0, hklt, hfk⟩ := exists_lower_capital hkbar hcont hineff
  exact ⟨k, hk0, hklt, (transition_gain hz hklt).2,
    steadyConsumption_ge_of_lower hconc hd hk0 hklt hfk.le⟩

/-- **With `r̄ > z` more capital costs the transition date**, O&R p. 193: moving capital up to
`k' > k̄` lowers first-date consumption below its steady-state level. -/
theorem transition_loss_of_more_capital {f : ℝ → ℝ} {z kbar k' : ℝ} (hz : 0 < 1 + z)
    (hgt : kbar < k') : transitionConsumption f z kbar k' < steadyConsumption f z kbar := by
  unfold transitionConsumption steadyConsumption
  nlinarith

/-- **With `r̄ > z` less capital costs later generations**: if `f'(k̄) = r̄ > z` and `f` is concave,
steady-state consumption at any lower capital level `k < k̄` is strictly below that at `k̄`. -/
theorem steadyConsumption_lt_of_lower_efficient {f f' : ℝ → ℝ} {z k kbar : ℝ}
    (hconc : ConcaveOn ℝ (Ioi 0) f) (hd : ∀ k, 0 < k → HasDerivAt f (f' k) k) (hk : 0 < k)
    (hlt : k < kbar) (hfk : z < f' kbar) :
    steadyConsumption f z k < steadyConsumption f z kbar := by
  unfold steadyConsumption
  have h := hconc.le_slope_of_hasDerivAt hk (hk.trans hlt) hlt (hd kbar (hk.trans hlt))
  rw [slope_def_field, le_div_iff₀ (by linarith)] at h
  nlinarith

/-! ### Ponzi games and bubbles (O&R §3A.2) -/

/-- **Ponzi debt shrinks relative to output iff `r < z`**, O&R p. 194: debt `D(1 + r)^t` rolled
over at rate `r`, relative to output `Y₀(1 + z)^t`, tends to zero when `r < z`. -/
theorem ponzi_ratio_tendsto_zero {r z D Y0 : ℝ} (hr : 0 < 1 + r) (hrz : r < z) :
    Tendsto (fun t : ℕ => D * (1 + r) ^ t / (Y0 * (1 + z) ^ t)) atTop (𝓝 0) := by
  have hz : 0 < 1 + z := by linarith
  have hq0 : 0 ≤ (1 + r) / (1 + z) := div_nonneg hr.le hz.le
  have hq1 : (1 + r) / (1 + z) < 1 := (div_lt_one hz).2 (by linarith)
  have e : (fun t : ℕ => D * (1 + r) ^ t / (Y0 * (1 + z) ^ t)) =
      fun t => D / Y0 * ((1 + r) / (1 + z)) ^ t := by
    funext t
    rw [div_pow, mul_div_mul_comm]
  rw [e]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (D / Y0)

/-- **Ponzi debt does not shrink when `r ≥ z`**: for `D, Y₀ > 0` the debt–output ratio stays at
least `D/Y₀`. -/
theorem ponzi_ratio_ge {r z D Y0 : ℝ} (hz : 0 < 1 + z) (hrz : z ≤ r) (hD : 0 < D) (hY : 0 < Y0)
    (t : ℕ) : D / Y0 ≤ D * (1 + r) ^ t / (Y0 * (1 + z) ^ t) := by
  have h1 : 1 ≤ ((1 + r) / (1 + z)) ^ t := one_le_pow₀ ((one_le_div hz).2 (by linarith))
  have e : D * (1 + r) ^ t / (Y0 * (1 + z) ^ t) = D / Y0 * ((1 + r) / (1 + z)) ^ t := by
    rw [div_pow, mul_div_mul_comm]
  rw [e]
  exact le_mul_of_one_le_right (div_pos hD hY).le h1

/-- **Bubbles are sustainable when `r ≤ z`**, O&R p. 194: if the price of a paper asset rises at `r`
(`p_t = (1 + r)^t p₀`) and the young's saving grows at `z` (`S_t = (1 + z)^t S₀`), an affordable
start `p₀D ≤ S₀` keeps the asset affordable forever. -/
theorem bubble_affordable {r z p0 D S0 : ℝ} (hr : 0 < 1 + r) (hrz : r ≤ z) (hp : 0 ≤ p0 * D)
    (h0 : p0 * D ≤ S0) (t : ℕ) : (1 + r) ^ t * p0 * D ≤ (1 + z) ^ t * S0 := by
  have hpow : (1 + r) ^ t ≤ (1 + z) ^ t := pow_le_pow_left₀ hr.le (by linarith) t
  have hS0 : 0 ≤ S0 := hp.trans h0
  calc (1 + r) ^ t * p0 * D = (1 + r) ^ t * (p0 * D) := by ring
    _ ≤ (1 + z) ^ t * (p0 * D) := mul_le_mul_of_nonneg_right hpow hp
    _ ≤ (1 + z) ^ t * S0 := mul_le_mul_of_nonneg_left h0 (pow_nonneg (by linarith) t)

/-- **Bubbles burst when `r > z`**, O&R p. 194: for any positive initial value `p₀D > 0`, there is a
date at which the asset's value exceeds the young's saving. -/
theorem bubble_unaffordable {r z p0 D S0 : ℝ} (hz : 0 < 1 + z) (hrz : z < r)
    (hp : 0 < p0 * D) : ∃ t : ℕ, (1 + z) ^ t * S0 < (1 + r) ^ t * p0 * D := by
  have hq : 1 < (1 + r) / (1 + z) := (one_lt_div hz).2 (by linarith)
  obtain ⟨t, ht⟩ := (tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop (S0 / (p0 * D))
    |>.exists
  refine ⟨t, ?_⟩
  have hzt : 0 < (1 + z) ^ t := pow_pos hz t
  rw [div_pow, div_lt_div_iff₀ hp hzt] at ht
  nlinarith

/-- **The profit-share criterion**, O&R §3A.3, p. 194: with positive capital and output,
`r > z` iff the profit share `rK/Y` exceeds the investment share `zK/Y`. So a steady state is
dynamically inefficient iff profits are a smaller share of output than investment. -/
theorem efficiency_iff_profit_share {r z K Y : ℝ} (hK : 0 < K) (hY : 0 < Y) :
    z < r ↔ z * K / Y < r * K / Y := by
  rw [div_lt_div_iff_of_pos_right hY]
  exact (mul_lt_mul_iff_of_pos_right hK).symm

end ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Tax smoothing à la Barro

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Exercise 6 of Chapter 3, p. 197. A small open representative-consumer economy has
`β = 1/(1 + r)`. Taxes `T_t` distort output, which is `Y_t − aT_t²/2` with
`a > 0`. The government must finance spending `G_t` and satisfy its intertemporal
budget constraint `Σ(1 + r)^{-s} T_s = Σ(1 + r)^{-s} G_s − (1 + r)B^G_0`.

* **Welfare depends on the tax path.** Consolidating the private and government
  budget constraints, the consumer's wealth is
  `(1 + r)(B^P_0 + B^G_0) + PV(Y − G) − PV(aT²/2)`: taxes matter only through the
  present value of their distortions. The government is therefore not indifferent
  to the timing of taxes.
* **Taxes should be smoothed.** Among all tax paths raising a given present value,
  the constant path `T̄ = r/(1 + r) · PV(T)` minimises the present value of the
  distortion, and uniquely so. This is Jensen's inequality for the convex cost `T²`.
* **Deficits track temporary spending.** With constant taxes equal to the permanent
  value of spending net of initial assets, the government runs a deficit exactly
  when spending is above its permanent level. With constant spending it never runs
  a deficit or a surplus.

The discount factor and the discounted-telescoping idea are copied from
`SmallOpenEconomyDynamics.PresentValue` so that this project builds on its own.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.TaxSmoothing

open Filter Topology

/-- The one-period discount factor `1/(1 + r)` (copied from `SmallOpenEconomyDynamics`). -/
noncomputable def taxDisc (r : ℝ) : ℝ := (1 + r)⁻¹

/-- `Σ_{s≥0} (1 + r)^{-s} = (1 + r)/r` for `r > 0`. -/
theorem hasSum_taxDisc_pow {r : ℝ} (hr : 0 < r) :
    HasSum (fun s => taxDisc r ^ s) ((1 + r) / r) := by
  have h0 : 0 ≤ taxDisc r := (inv_pos.2 (by linarith : (0 : ℝ) < 1 + r)).le
  have h1 : taxDisc r < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  convert hasSum_geometric_of_lt_one h0 h1 using 1
  have h2 : (1 : ℝ) + r ≠ 0 := by linarith
  have h3 : r ≠ 0 := hr.ne'
  have e : 1 - (1 + r)⁻¹ = r / (1 + r) := by field_simp; ring
  unfold taxDisc
  rw [e, inv_div]

/-- **Consolidated wealth**, Exercise 6: if the consumer's budget is
`PV(C) = (1 + r)B^P_0 + PV(Y − aT²/2 − T)` and the government's is
`PV(T) = PV(G) − (1 + r)B^G_0`, then
`PV(C) = (1 + r)(B^P_0 + B^G_0) + PV(Y − G) − PV(aT²/2)`. -/
theorem consolidated_wealth {r BP BG pvC pvY pvG pvT pvDist : ℝ}
    (hcons : pvC = (1 + r) * BP + (pvY - pvDist - pvT))
    (hgov : pvT = pvG - (1 + r) * BG) :
    pvC = (1 + r) * (BP + BG) + (pvY - pvG) - pvDist := by
  rw [hcons, hgov]
  ring

/-- **Taxes matter through their distortions**, Exercise 6: with flat consumption
`C = r/(1 + r) · PV(C)` (since `β(1 + r) = 1`), a tax path with a larger present value of
distortions gives strictly lower consumption in every period. -/
theorem consumption_lower_of_distortion {r BP BG pvY pvG d d' : ℝ} (hr : 0 < r) (hd : d < d') :
    r / (1 + r) * ((1 + r) * (BP + BG) + (pvY - pvG) - d') <
      r / (1 + r) * ((1 + r) * (BP + BG) + (pvY - pvG) - d) := by
  have : 0 < r / (1 + r) := div_pos hr (by linarith)
  exact mul_lt_mul_of_pos_left (by linarith) this

/-- **Tax smoothing**, Exercise 6: if `T` raises the same present value as the constant tax `T̄`,
the present value of the squared tax is at least that of the constant path. -/
theorem pv_sq_ge_of_pv_eq {r Tbar : ℝ} (hr : 0 < r) {T : ℕ → ℝ}
    (hT : Summable fun s => taxDisc r ^ s * T s)
    (hT2 : Summable fun s => taxDisc r ^ s * T s ^ 2)
    (hpv : ∑' s, taxDisc r ^ s * T s = ∑' s, taxDisc r ^ s * Tbar) :
    ∑' s, taxDisc r ^ s * Tbar ^ 2 ≤ ∑' s, taxDisc r ^ s * T s ^ 2 := by
  have hg := (hasSum_taxDisc_pow hr).summable
  have hc : Summable fun s => taxDisc r ^ s * Tbar := hg.mul_right Tbar
  have hc2 : Summable fun s => taxDisc r ^ s * Tbar ^ 2 := hg.mul_right (Tbar ^ 2)
  have hpos : ∀ s, 0 ≤ taxDisc r ^ s :=
    fun s => pow_nonneg (inv_pos.2 (by linarith : (0 : ℝ) < 1 + r)).le s
  -- the tangent-line bound T² ≥ T̄² + 2T̄(T − T̄), weighted by the discount factor
  have hterm : ∀ s, taxDisc r ^ s * Tbar ^ 2 + 2 * Tbar * (taxDisc r ^ s * T s -
      taxDisc r ^ s * Tbar) ≤ taxDisc r ^ s * T s ^ 2 := by
    intro s
    have := mul_nonneg (hpos s) (sq_nonneg (T s - Tbar))
    nlinarith
  have hsum : Summable fun s => taxDisc r ^ s * Tbar ^ 2 + 2 * Tbar * (taxDisc r ^ s * T s -
      taxDisc r ^ s * Tbar) := hc2.add ((hT.sub hc).mul_left _)
  have hle := hsum.tsum_le_tsum hterm hT2
  rw [hc2.tsum_add ((hT.sub hc).mul_left _), tsum_mul_left, hT.tsum_sub hc, hpv, sub_self,
    mul_zero, add_zero] at hle
  exact hle

/-- **Strict tax smoothing**: any tax path that raises the same present value as the constant path
but is not constant has a strictly larger present value of squared taxes. -/
theorem pv_sq_gt_of_pv_eq {r Tbar : ℝ} (hr : 0 < r) {T : ℕ → ℝ}
    (hT : Summable fun s => taxDisc r ^ s * T s)
    (hT2 : Summable fun s => taxDisc r ^ s * T s ^ 2)
    (hpv : ∑' s, taxDisc r ^ s * T s = ∑' s, taxDisc r ^ s * Tbar) {k : ℕ} (hk : T k ≠ Tbar) :
    ∑' s, taxDisc r ^ s * Tbar ^ 2 < ∑' s, taxDisc r ^ s * T s ^ 2 := by
  have hg := (hasSum_taxDisc_pow hr).summable
  have hc : Summable fun s => taxDisc r ^ s * Tbar := hg.mul_right Tbar
  have hc2 : Summable fun s => taxDisc r ^ s * Tbar ^ 2 := hg.mul_right (Tbar ^ 2)
  have hdpos : ∀ s, 0 < taxDisc r ^ s :=
    fun s => pow_pos (inv_pos.2 (by linarith : (0 : ℝ) < 1 + r)) s
  have hterm : ∀ s, taxDisc r ^ s * Tbar ^ 2 + 2 * Tbar * (taxDisc r ^ s * T s -
      taxDisc r ^ s * Tbar) ≤ taxDisc r ^ s * T s ^ 2 := by
    intro s
    have := mul_nonneg (hdpos s).le (sq_nonneg (T s - Tbar))
    nlinarith
  have hstrict : taxDisc r ^ k * Tbar ^ 2 + 2 * Tbar * (taxDisc r ^ k * T k -
      taxDisc r ^ k * Tbar) < taxDisc r ^ k * T k ^ 2 := by
    have := mul_pos (hdpos k) (pow_pos (abs_pos.2 (sub_ne_zero.2 hk)) 2)
    rw [sq_abs] at this
    nlinarith
  have hsum : Summable fun s => taxDisc r ^ s * Tbar ^ 2 + 2 * Tbar * (taxDisc r ^ s * T s -
      taxDisc r ^ s * Tbar) := hc2.add ((hT.sub hc).mul_left _)
  have hlt := hsum.tsum_lt_tsum hterm hstrict hT2
  rw [hc2.tsum_add ((hT.sub hc).mul_left _), tsum_mul_left, hT.tsum_sub hc, hpv, sub_self,
    mul_zero, add_zero] at hlt
  exact hlt

/-- **The optimal tax rule**, Exercise 6: with `a > 0`, the constant tax raising the required
present value minimises the present value of the distortion `aT²/2`, and every other tax path
raising the same present value is strictly worse. The government is not indifferent. -/
theorem constant_tax_optimal {r a Tbar : ℝ} (hr : 0 < r) (ha : 0 < a) {T : ℕ → ℝ}
    (hT : Summable fun s => taxDisc r ^ s * T s)
    (hT2 : Summable fun s => taxDisc r ^ s * T s ^ 2)
    (hpv : ∑' s, taxDisc r ^ s * T s = ∑' s, taxDisc r ^ s * Tbar) :
    a / 2 * ∑' s, taxDisc r ^ s * Tbar ^ 2 ≤ a / 2 * ∑' s, taxDisc r ^ s * T s ^ 2 ∧
      ((∃ k, T k ≠ Tbar) →
        a / 2 * ∑' s, taxDisc r ^ s * Tbar ^ 2 < a / 2 * ∑' s, taxDisc r ^ s * T s ^ 2) := by
  have ha2 : 0 < a / 2 := by linarith
  refine ⟨mul_le_mul_of_nonneg_left (pv_sq_ge_of_pv_eq hr hT hT2 hpv) ha2.le, ?_⟩
  rintro ⟨k, hk⟩
  exact mul_lt_mul_of_pos_left (pv_sq_gt_of_pv_eq hr hT hT2 hpv hk) ha2

/-- The constant tax raising present value `R` is `T̄ = r/(1 + r) · R`: the permanent value of the
required revenue. -/
theorem constant_tax_level {r R : ℝ} (hr : 0 < r) :
    ∑' s, taxDisc r ^ s * (r / (1 + r) * R) = R := by
  rw [tsum_mul_right, (hasSum_taxDisc_pow hr).tsum_eq]
  have h1 : (1 : ℝ) + r ≠ 0 := by linarith
  have h2 : r ≠ 0 := hr.ne'
  field_simp

/-- **Deficits track temporary spending**, Exercise 6: if the constant tax equals the permanent
value of spending net of interest on initial assets, `T̄ = G̃ − rB^G_0`, then the date-0 deficit
`G_0 − T̄ − rB^G_0` equals `G_0 − G̃`: the government borrows exactly when spending is above its
permanent level. -/
theorem deficit_eq_spending_gap {r Tbar G0 Gtilde BG0 : ℝ}
    (hT : Tbar = Gtilde - r * BG0) : G0 - Tbar - r * BG0 = G0 - Gtilde := by
  rw [hT]; ring

/-- **No deficits with constant spending**, Exercise 6: with constant spending `Ḡ` and the smooth
tax `T̄ = Ḡ − rB^G_0`, government assets obey `B_{t+1} = (1 + r)B_t + T̄ − Ḡ` and stay constant
at `B^G_0`. -/
theorem government_assets_constant {r Gbar BG0 : ℝ} {B : ℕ → ℝ} (h0 : B 0 = BG0)
    (hflow : ∀ t, B (t + 1) = (1 + r) * B t + (Gbar - r * BG0) - Gbar) (t : ℕ) :
    B t = BG0 := by
  induction t with
  | zero => exact h0
  | succ t ih => rw [hflow t, ih]; ring

end ObstfeldRogoff.LifeCycleFiscalPolicy.TaxSmoothing

set_option linter.style.longLine false
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.mk
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.β
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.r
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.β_pos
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.one_add_r_pos
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.youngC
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.oldC
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.budget
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.euler
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.IsOptimal
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.TwoPeriodPlan
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.TwoPeriodPlan.mk
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.TwoPeriodPlan.C1
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.TwoPeriodPlan.I1
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.TwoPeriodPlan.C2
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.TwoPeriodPlan.I2
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.twoPeriodBudgetSet
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.two_period_merged_constraint
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.two_period_budgetSet_eq_of_pv_eq
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.two_period_budgetSet_eq_government
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.two_period_optimum_invariant
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.retiming_pv_eq
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.privateSaving
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.governmentSaving
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.retiming_saving_date_one
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.retiming_saving_date_two
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.ricDisc
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.one_add_mul_ricDisc
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.ric_discounted_telescope
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.ric_transversality_iff_ibc
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.private_ibc_of_flow
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.government_ibc_of_flow
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.merged_ibc
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.privatePVSet
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.privatePVSet_eq_of_government_ibc
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.private_optimum_invariant
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.dynasty_ibc
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.utility_iterate
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.tendsto_utility_remainder
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.utility_eq_tsum_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.gale_shift_solution
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.gale_solutions_differ
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.gale_shift_limit
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.gale_shift_ne_tsum
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.miserUtility
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.miser_recursion
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.miser_limit
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.miser_ne_tsum
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.bequestPath
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.bequestPath_flow
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.eq_bequestPath
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.transferTax
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.bequestPath_transfer_one
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.bequestPath_transfer_of_two_le
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.dynastyPVSet
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.dynastyFeasible
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.hasSum_transferTax
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.dynastyPVSet_transfer
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.dynastyFeasible_subset_pv
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.tendsto_bequest_transfer_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.feasible_transfer_of_small
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.transfer_to_old_feasible_subset
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.feasible_of_transfer_feasible
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.interior_bequest_neutrality
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.transferConsumption
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.bequestPath_transferConsumption
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.transfer_relaxes_binding_bequest
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.binding_bequest_feasible_ssubset
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoPeriodOLG.lifetimeWealth
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoPeriodOLG.aggregate_consumption_steady
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoPeriodOLG.aggregate_consumption_government
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoPeriodOLG.consumption_depends_on_youth_tax
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoPeriodOLG.consumption_increasing_in_government_assets
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoPeriodOLG.current_account_split
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoPeriodOLG.old_saving
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoPeriodOLG.private_saving
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoPeriodOLG.young_saving_flat
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoPeriodOLG.private_saving_flat
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoPeriodOLG.generational_account_invariant
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoPeriodOLG.generational_account_consumption
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoPeriodOLG.taxes_by_generation
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.youngWealthChange
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.laterWealthChange
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.youngWealthChange_eq
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.laterWealthChange_eq
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.young0_consumption_change
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.consumption0_change
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.consumption0_change_lt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.old1_consumption_change
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.later_young_consumption_change
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.later_old_consumption_change
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.consumption1_change
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.consumption1_rises_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.consumption1_sign_ambiguous
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.consumption_later_falls
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.consumption_later_change
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.consumption_later_change_flat
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.share_of_flat
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.current_account1_change
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.current_account_later_zero
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.balanced_transfer_consumption
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.transitory_shock_current_account
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer.log_share
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving.saving_rate_growth
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving.savingRate
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving.hasDerivAt_savingRate_e
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving.savingRate_e_deriv_neg
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving.hasDerivAt_savingRate_g
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving.savingRate_g_deriv_pos_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving.saving_rate_population
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving.hasDerivAt_saving_rate_population
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving.three_period_optimal
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving.ex1_unconstrained_saving
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving.ex1_constraint_binds_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving.ex1_constrained_saving
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving.ex1_saving_rate_unconstrained
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving.ex1_saving_rate_constrained
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving.ex1_unconstrained_rate_anti_e
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving.ex1_constrained_rate_mono_e
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving.ex1d_saving
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.capLabour
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.wageOf
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.mpk_capLabour
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.capLabour_unique
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.mpl_capLabour
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.wage_hasDerivAt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.young_saving_per_capita
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.steady_foreign_assets
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.steady_current_account_sign
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.savingPerCapita
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.saving_per_capita_eq
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.savingPerCapita_hasDerivAt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.savingPerCapita_deriv_pos
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.investPerCapita
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.invest_per_capita_eq
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.investPerCapita_hasDerivAt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.investPerCapita_deriv_pos_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.capital
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.output
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.capital_output_ratio_of_mpk
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.output_eq_labour_mul
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.capital_output_ratio
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.output_closed_form
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.output_growth
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.investment_share
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.wage_bill_share
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.log_young_saving
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.log_old_saving
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.young_saving_closed_form
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.youngSaving
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.saving
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.foreignAssets
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.savingRate
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.assetRatio
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.youngSaving_share
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.saving_share
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.asset_share
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.current_account_share
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.savingRate_strictMono_n
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.savingRate_strictMono_g
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.investShare_strictMono
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.assetRatio_strictMono_beta
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.assetRatio_strictMono_r
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond.Growth.assetRatio_neg_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.lifetimeUtility
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.hasDerivAt_lifetimeUtility
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.hasDerivAt_lifetimeUtility_frontier
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.hasDerivAt_lifetimeUtility_autarky
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.autarky_utility_slope_neg
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.old_income_hasDerivAt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.income_equivalent_autarky
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.pv_generation_losses
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.aggregate_first_order_zero
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.compensation_scheme
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.hasDerivAt_lifetimeUtility_open
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.income_equivalent_open
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.open_generation_gains_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.open_economywide_gain
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.dateT_young_predetermined_hasDerivAt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.hasDerivAt_lifetimeUtility_growth
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.growth_slope_pos_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.wageCD
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.capitalCD
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.hasDerivAt_wageCD
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.capitalCD_div_wageCD
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.wageCD_pos
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.autarkyRateCD
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.capitalCD_autarky
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.lifetimeUtility_wageCD
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.hasDerivAt_lifetimeUtility_CD
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.utilityMinRateCD
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.slope_CD_pos_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.lifetimeUtility_CD_strictMonoOn
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.lifetimeUtility_CD_strictAntiOn
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.everyone_worse_off_corrected
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.lifetimeUtility_CD_tendsto_atTop
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.exists_rate_below_autarky_young_gain
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.OLGGainsFromTrade.counterexample_everyone_worse_off
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.mk
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.α
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.β
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.n
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.x
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.α_pos
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.α_lt_one
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.β_pos
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.n_gt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.x_pos
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.x_le_one
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.iterate_tendsto_of_below
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.iterate_tendsto_of_above
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.strictConcave_chord_lt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.coef
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psi
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.kbar
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.rate
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.coef_pos
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.kbar_pos
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psi_zero
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psi_kbar
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psi_fixed_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psi_strictMonoOn
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.coef_kbar_div
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psi_between_below
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psi_between_above
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psi_continuous
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psi_global_convergence
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.zero_unstable
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.rbarOf
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.rate_kbar
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.tax_eq
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psiDebt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.law_of_motion_debt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psiDebt_zero
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psiDebt_eq
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.crowding_bracket_pos
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psiDebt_hasDerivAt_debt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psiDebt_strictAnti_debt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psiDebt_lt_psi
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psiDebt_hasDerivAt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psiDebt_deriv_strictAnti
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psiDebt_strictMonoOn
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psiDebt_strictConcaveOn
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psiDebt_gap_strictConcaveOn
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.steady_state_pattern
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.steady_state_at_most_two
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.upper_steady_state_attracts
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.IsUpperSteadyState
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.kbar_isUpper
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.psi_le_add_kbar
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.exists_two_steady_states
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.no_steady_state_of_large_debt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.crowding_out
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.steady_state_lt_kbar
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.rate_rises
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.rbar_le_n_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.exists_alpha_rbar_le_n
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.rbar_tendsto_zero
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.tax_nonpos_of_rate_le
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.foreignUtility
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.foreignUtility_hasDerivAt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.foreignUtility_deriv_pos_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.foreignUtility_deriv_neg_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.foreignUtility_strictMonoOn
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TwoCountryOLG.TwoCountry.foreign_welfare_falls_with_debt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.perpetual_finite_budget
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.perpetual_ibc_of_flow
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.perpetual_consumption_of_euler
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_consumption_function
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.vintageSize
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.vintageAgg
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.sum_vintageSize
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.vintageAgg_const
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.vintageAgg_affine
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.vintageAgg_congr
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_aggregate_consumption_general
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_aggregate_consumption
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_aggregate_accumulation
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_law_of_motion
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_hasSum_const
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weilSlope
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weilIntercept
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weilSteadyB
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weilSteadyC
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_law_of_motion_const
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_affine_iterate
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weilSteadyB_fixed
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weilSteadyB_unique
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_converges
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_not_converges
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_stable_of_impatient
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weilSteadyB_pos_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_steady_consumption
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weilSteadyC_eq_consumption_function
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weilSteadyC_closed
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weilSteadyC_hasDerivAt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weilSteadyC_slope_pos_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weilSteadyC_zero_growth
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weilSteadyC_neg_of_unstable
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weilSteadyB_falls
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weilSteadyC_rises
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_hasSum_transitory
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_transitory_jump
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_transitory_return
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_hasSum_growth
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_growth_law
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_growth_ratio_law
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.growthSteadyRatio
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.growthSteadyRatio_fixed
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.growthSteadyRatio_pos_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.growthSteadyRatio_partial_fractions
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.growthSteadyRatio_strictAntiOn
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_unit_tilt_law
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_unit_tilt_steady
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_unit_tilt_zero_growth
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_transitory_consumption_jump
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_debt_tax
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_debt_consumption
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_debt_consumption_change
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_ricardian_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_debt_path_consumption
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.weil_debt_path_consumption_book
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.blanchard_population
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.blanchard_annuity_zero_profit
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.blanchard_budget
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.blanchard_consumption_function
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.blanchard_hasSum_const
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.blanchard_aggregate_accumulation
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.blanchard_aggregate_consumption
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.blanchard_law_of_motion
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.blanchardSteadyB
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.blanchard_debt_tax
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.blanchardSteadyB_private_fixed
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.blanchardSteadyB_debt
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.blanchard_debt_lowers
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.blanchard_steady_consumption
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth.blanchardSteadyB_ricardian
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency.steadyConsumption
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency.steady_state_iff
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency.transitionConsumption
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency.golden_rule_max
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency.hasDerivAt_steadyConsumption
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency.steadyConsumption_ge_of_lower
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency.transition_gain
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency.exists_lower_capital
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency.pareto_improvement_of_dynamically_inefficient
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency.transition_loss_of_more_capital
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency.steadyConsumption_lt_of_lower_efficient
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency.ponzi_ratio_tendsto_zero
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency.ponzi_ratio_ge
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency.bubble_affordable
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency.bubble_unaffordable
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency.efficiency_iff_profit_share
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TaxSmoothing.taxDisc
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TaxSmoothing.hasSum_taxDisc_pow
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TaxSmoothing.consolidated_wealth
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TaxSmoothing.consumption_lower_of_distortion
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TaxSmoothing.pv_sq_ge_of_pv_eq
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TaxSmoothing.pv_sq_gt_of_pv_eq
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TaxSmoothing.constant_tax_optimal
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TaxSmoothing.constant_tax_level
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TaxSmoothing.deficit_eq_spending_gap
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.TaxSmoothing.government_assets_constant
