/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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
