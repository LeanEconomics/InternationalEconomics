/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Risk sharing with hidden information

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §6.3
(pp. 401–407).

A continuum of countries; on date 1 half receive `Y_` (type `L`) and half `Ȳ` (type `H`),
`0 < Y_ < Ȳ`; on date 2 every country receives the mean `Y = (Y_ + Ȳ)/2`. Ex ante utility
is `E[log C₁ + log C₂]`. A contract `(P₁, P₂)` has a country reporting high output pay
`P₁` on date 1 and `P₂` on date 2, and a country reporting low output receive them.

* **Incentive constraints (41)–(42).** We prove they are equivalent to the *linear*
  constraints `Y P₁ + Ȳ P₂ ≤ 0` and `Y P₁ + Y_ P₂ ≥ 0`. The low type's deviation can
  require negative consumption (the book overlooks this); we treat such a deviation as
  unavailable, and show the linear form is still exact.
* **Correction of p. 405.** The book asserts that (41) and (42) cannot both bind since that
  would imply `Ȳ = Y_`. In fact both bind *iff* the contract is null, `P₁ = P₂ = 0`, for any
  `Y_ < Ȳ`; for a nonzero contract at most one binds.
* **Bond equilibrium (B).** With a riskless bond the unique market-clearing gross rate is
  `1` (`r = 0`), each type smooths perfectly, and `B` beats autarky `A` ex post and ex ante.
  The Arrow–Debreu point `E` is the unconstrained optimum and violates (41).
* **Contract (43), point C.** Consumptions `2ȲY/(Ȳ+Y)` and `2Y²/(Ȳ+Y)`; (41) binds, (42) is
  slack; the net-present-value transfer to `L` is `(Ȳ−Y)²/(Ȳ+Y)`; `C` is on the contract
  curve and has strictly higher expected utility than `B`.
* **The optimal incentive-compatible contract** (left as an exercise in the book): it exists,
  is unique, is given in closed form, (41) binds and (42) is slack at it, it lies strictly
  north-west of `C` and off the contract curve. By the revelation principle (fn 59), proved
  here for arbitrary message spaces, no mechanism does better.
* **Ex post bond trade (p. 406).** If countries can borrow and lend freely after reporting,
  incentive compatibility forces a zero net-present-value contract and the best implementable
  allocation is `B`; at contract (43) the high type gains by lying and saving (point `C″`).
-/

namespace ObstfeldRogoff.CapitalMarketImperfections.HiddenInformation

open Real

/-- The endowment structure of §6.3, p. 402: date-1 output `lo = Y_` (type `L`) or
`hi = Ȳ` (type `H`), with `0 < Y_ < Ȳ`. -/
structure Endowments where
  lo : ℝ
  hi : ℝ
  lo_pos : 0 < lo
  lo_lt_hi : lo < hi

namespace Endowments

variable (e : Endowments)

/-- Mean output `Y = (Y_ + Ȳ)/2`, O&R p. 402; it is every country's date-2 output. -/
noncomputable def avg : ℝ := (e.lo + e.hi) / 2

/-- `Ȳ > 0`, O&R p. 402. -/
theorem hi_pos : 0 < e.hi := e.lo_pos.trans e.lo_lt_hi

/-- `Y_ < Y < Ȳ`, O&R p. 402. -/
theorem lo_lt_avg : e.lo < e.avg := by unfold avg; linarith [e.lo_lt_hi]

/-- `Y < Ȳ`, O&R p. 402. -/
theorem avg_lt_hi : e.avg < e.hi := by unfold avg; linarith [e.lo_lt_hi]

/-- `Y > 0`, O&R p. 402. -/
theorem avg_pos : 0 < e.avg := e.lo_pos.trans e.lo_lt_avg

/-- `Ȳ − Y = Y − Y_`, O&R p. 404. -/
theorem hi_sub_avg : e.hi - e.avg = e.avg - e.lo := by unfold avg; ring

end Endowments

/-- Lifetime utility `log C₁ + log C₂` (β = 1), O&R p. 402. -/
noncomputable def lifetimeU (c₁ c₂ : ℝ) : ℝ := Real.log c₁ + Real.log c₂

/-- A contract `(P₁, P₂)` is feasible if all truthful consumptions are positive: type `H`
consumes `(Ȳ − P₁, Y − P₂)`, type `L` consumes `(Y_ + P₁, Y + P₂)`, O&R p. 405. -/
def Feasible (e : Endowments) (P₁ P₂ : ℝ) : Prop :=
  0 < e.hi - P₁ ∧ 0 < e.avg - P₂ ∧ 0 < e.lo + P₁ ∧ 0 < e.avg + P₂

/-- Incentive constraint (41), O&R p. 405: type `H` does not gain by posing as `L`
(it would then consume `(Ȳ + P₁, Y + P₂)`, both positive under feasibility). -/
def ICH (e : Endowments) (P₁ P₂ : ℝ) : Prop :=
  lifetimeU (e.hi + P₁) (e.avg + P₂) ≤ lifetimeU (e.hi - P₁) (e.avg - P₂)

/-- Incentive constraint (42), O&R p. 405: type `L` does not gain by posing as `H`. Posing
as `H` gives consumption `(Y_ − P₁, Y − P₂)`; when `Y_ − P₁ ≤ 0` the deviation is not
available (its utility is `−∞`), a case the book overlooks. -/
def ICL (e : Endowments) (P₁ P₂ : ℝ) : Prop :=
  0 < e.lo - P₁ → lifetimeU (e.lo - P₁) (e.avg - P₂) ≤ lifetimeU (e.lo + P₁) (e.avg + P₂)

/-- Ex ante expected utility, the average of the two types' utilities, O&R p. 405. -/
noncomputable def EU (e : Endowments) (P₁ P₂ : ℝ) : ℝ :=
  (lifetimeU (e.hi - P₁) (e.avg - P₂) + lifetimeU (e.lo + P₁) (e.avg + P₂)) / 2

/-- For positive arguments, `log a + log b ≤ log c + log d ↔ ab ≤ cd` (used for (41)–(42)). -/
theorem lifetimeU_le_iff {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    lifetimeU a b ≤ lifetimeU c d ↔ a * b ≤ c * d := by
  unfold lifetimeU
  rw [← Real.log_mul ha.ne' hb.ne', ← Real.log_mul hc.ne' hd.ne']
  exact Real.log_le_log_iff (mul_pos ha hb) (mul_pos hc hd)

/-- For positive arguments, `log a + log b = log c + log d ↔ ab = cd`. -/
theorem lifetimeU_eq_iff {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    lifetimeU a b = lifetimeU c d ↔ a * b = c * d := by
  unfold lifetimeU
  rw [← Real.log_mul ha.ne' hb.ne', ← Real.log_mul hc.ne' hd.ne']
  constructor
  · intro h
    exact Real.log_injOn_pos (Set.mem_Ioi.2 (mul_pos ha hb)) (Set.mem_Ioi.2 (mul_pos hc hd)) h
  · intro h
    rw [h]

/-- For positive arguments, `log a + log b < log c + log d ↔ ab < cd`. -/
theorem lifetimeU_lt_iff {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    lifetimeU a b < lifetimeU c d ↔ a * b < c * d := by
  unfold lifetimeU
  rw [← Real.log_mul ha.ne' hb.ne', ← Real.log_mul hc.ne' hd.ne']
  exact Real.log_lt_log_iff (mul_pos ha hb) (mul_pos hc hd)

/-- AM–GM in logs: `log a + log b ≤ 2 log((a+b)/2)` for `a, b > 0` (the concavity step of
O&R p. 404). -/
theorem log_add_log_le_two_log_mean {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log a + Real.log b ≤ 2 * Real.log ((a + b) / 2) := by
  rw [← Real.log_mul ha.ne' hb.ne',
    show (2 : ℝ) * Real.log ((a + b) / 2) = Real.log (((a + b) / 2) ^ 2) by
      rw [Real.log_pow]; norm_num]
  exact Real.log_le_log (mul_pos ha hb) (by nlinarith [sq_nonneg (a - b)])

/-- Strict AM–GM in logs: `log a + log b < 2 log((a+b)/2)` for `a ≠ b` positive,
O&R p. 404. -/
theorem log_add_log_lt_two_log_mean {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    Real.log a + Real.log b < 2 * Real.log ((a + b) / 2) := by
  rw [← Real.log_mul ha.ne' hb.ne',
    show (2 : ℝ) * Real.log ((a + b) / 2) = Real.log (((a + b) / 2) ^ 2) by
      rw [Real.log_pow]; norm_num]
  have : 0 < (a - b) ^ 2 := by
    have : a - b ≠ 0 := sub_ne_zero.2 hab
    positivity
  exact Real.log_lt_log (mul_pos ha hb) (by nlinarith)

/-! ## The incentive constraints are linear -/

/-- Under feasibility, type `H`'s deviation consumptions `(Ȳ + P₁, Y + P₂)` are positive,
so (41) is a genuine comparison of finite utilities, O&R p. 405. -/
theorem feasible_deviationH_pos {e : Endowments} {P₁ P₂ : ℝ} (h : Feasible e P₁ P₂) :
    0 < e.hi + P₁ ∧ 0 < e.avg + P₂ := by
  obtain ⟨_, _, h3, h4⟩ := h
  exact ⟨by linarith [e.lo_lt_hi], h4⟩

/-- (41) is equivalent to the linear constraint `Y P₁ + Ȳ P₂ ≤ 0`, O&R (41), p. 405
(the `P₁P₂` terms cancel). -/
theorem icH_iff_linear {e : Endowments} {P₁ P₂ : ℝ} (h : Feasible e P₁ P₂) :
    ICH e P₁ P₂ ↔ e.avg * P₁ + e.hi * P₂ ≤ 0 := by
  obtain ⟨d1, d2⟩ := feasible_deviationH_pos h
  obtain ⟨h1, h2, _, _⟩ := h
  unfold ICH
  rw [lifetimeU_le_iff d1 d2 h1 h2]
  constructor <;> intro hh <;> nlinarith

/-- (42) is equivalent to the linear constraint `Y P₁ + Y_ P₂ ≥ 0`, O&R (42), p. 405; this
remains exact when `Y_ − P₁ ≤ 0` (deviation unavailable), since then the linear form holds
automatically. -/
theorem icL_iff_linear {e : Endowments} {P₁ P₂ : ℝ} (h : Feasible e P₁ P₂) :
    ICL e P₁ P₂ ↔ 0 ≤ e.avg * P₁ + e.lo * P₂ := by
  obtain ⟨_, h2, h3, h4⟩ := h
  have hlo := e.lo_pos
  unfold ICL
  constructor
  · intro hh
    by_cases hp : 0 < e.lo - P₁
    · have := (lifetimeU_le_iff hp h2 h3 h4).1 (hh hp)
      nlinarith
    · push Not at hp
      nlinarith
  · intro hh hp
    rw [lifetimeU_le_iff hp h2 h3 h4]
    nlinarith

/-- (41) holds with equality iff `Y P₁ + Ȳ P₂ = 0`, O&R p. 405. -/
theorem icH_binds_iff {e : Endowments} {P₁ P₂ : ℝ} (h : Feasible e P₁ P₂) :
    lifetimeU (e.hi + P₁) (e.avg + P₂) = lifetimeU (e.hi - P₁) (e.avg - P₂) ↔
      e.avg * P₁ + e.hi * P₂ = 0 := by
  obtain ⟨d1, d2⟩ := feasible_deviationH_pos h
  obtain ⟨h1, h2, _, _⟩ := h
  rw [lifetimeU_eq_iff d1 d2 h1 h2]
  constructor <;> intro hh <;> nlinarith

/-- (42) holds with equality (the deviation being available) iff `Y P₁ + Y_ P₂ = 0`,
O&R p. 405. -/
theorem icL_binds_iff {e : Endowments} {P₁ P₂ : ℝ} (h : Feasible e P₁ P₂) :
    (0 < e.lo - P₁ ∧
        lifetimeU (e.lo - P₁) (e.avg - P₂) = lifetimeU (e.lo + P₁) (e.avg + P₂)) ↔
      e.avg * P₁ + e.lo * P₂ = 0 := by
  obtain ⟨_, h2, h3, h4⟩ := h
  have hlo := e.lo_pos
  have hav := e.avg_pos
  have hla := e.lo_lt_avg
  constructor
  · rintro ⟨hp, hh⟩
    have := (lifetimeU_eq_iff hp h2 h3 h4).1 hh
    nlinarith
  · intro hh
    have hp : 0 < e.lo - P₁ := by
      by_contra hc
      push Not at hc
      -- then `P₂ = −Y P₁ / Y_ ≤ −Y`, contradicting `Y + P₂ > 0`
      nlinarith
    exact ⟨hp, (lifetimeU_eq_iff hp h2 h3 h4).2 (by nlinarith)⟩

/-- **Correction of O&R p. 405.** Both incentive constraints bind iff the contract is null,
`P₁ = P₂ = 0` — for every `Y_ < Ȳ`. (The book claims both binding would force `Ȳ = Y_`.) -/
theorem both_bind_iff_null {e : Endowments} {P₁ P₂ : ℝ} (h : Feasible e P₁ P₂) :
    (lifetimeU (e.hi + P₁) (e.avg + P₂) = lifetimeU (e.hi - P₁) (e.avg - P₂) ∧
      (0 < e.lo - P₁ ∧
        lifetimeU (e.lo - P₁) (e.avg - P₂) = lifetimeU (e.lo + P₁) (e.avg + P₂))) ↔
      P₁ = 0 ∧ P₂ = 0 := by
  rw [icH_binds_iff h, icL_binds_iff h]
  have hlt := e.lo_lt_hi
  have hav := e.avg_pos
  constructor
  · rintro ⟨hH, hL⟩
    have hP₂ : P₂ = 0 := by
      have : (e.hi - e.lo) * P₂ = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h0
      · linarith
      · exact h0
    refine ⟨?_, hP₂⟩
    rw [hP₂] at hH
    have : e.avg * P₁ = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · linarith
    · exact h0
  · rintro ⟨rfl, rfl⟩
    constructor <;> ring

/-- The null contract is feasible, and both (41) and (42) bind at it although `Y_ < Ȳ`: the
statement of O&R p. 405 is false as written. -/
theorem null_contract_both_bind (e : Endowments) :
    Feasible e 0 0 ∧
      lifetimeU (e.hi + 0) (e.avg + 0) = lifetimeU (e.hi - 0) (e.avg - 0) ∧
      0 < e.lo - 0 ∧ lifetimeU (e.lo - 0) (e.avg - 0) = lifetimeU (e.lo + 0) (e.avg + 0) := by
  have hf : Feasible e 0 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [e.hi_pos, e.avg_pos, e.lo_pos]
  exact ⟨hf, by simp, by simp [e.lo_pos], by simp⟩

/-- For a nonzero feasible contract at most one incentive constraint binds (the correct
version of the claim on O&R p. 405). -/
theorem nonzero_contract_not_both_bind {e : Endowments} {P₁ P₂ : ℝ} (h : Feasible e P₁ P₂)
    (hne : P₁ ≠ 0 ∨ P₂ ≠ 0) :
    ¬ (e.avg * P₁ + e.hi * P₂ = 0 ∧ e.avg * P₁ + e.lo * P₂ = 0) := by
  rintro ⟨hH, hL⟩
  have := (both_bind_iff_null h).1
    ⟨(icH_binds_iff h).2 hH, (icL_binds_iff h).2 hL⟩
  rcases hne with h1 | h2
  · exact h1 this.1
  · exact h2 this.2


/-! ## Expected utility as a product -/

/-- `Y_ = 2Y − Ȳ`, O&R p. 402. -/
theorem lo_eq (e : Endowments) : e.lo = 2 * e.avg - e.hi := by unfold Endowments.avg; ring

/-- The product of the four truthful consumptions of a contract, O&R p. 405. -/
noncomputable def consProd (e : Endowments) (P₁ P₂ : ℝ) : ℝ :=
  (e.hi - P₁) * (e.avg - P₂) * ((e.lo + P₁) * (e.avg + P₂))

/-- For a feasible contract, `EU = log(∏ consumptions)/2`, O&R p. 405. -/
theorem EU_eq_log_consProd {e : Endowments} {P₁ P₂ : ℝ} (h : Feasible e P₁ P₂) :
    EU e P₁ P₂ = Real.log (consProd e P₁ P₂) / 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold EU lifetimeU consProd
  rw [Real.log_mul (mul_pos h1 h2).ne' (mul_pos h3 h4).ne', Real.log_mul h1.ne' h2.ne',
    Real.log_mul h3.ne' h4.ne']

/-- Expected utilities of feasible contracts are ranked by the consumption products. -/
theorem EU_lt_iff {e : Endowments} {P₁ P₂ Q₁ Q₂ : ℝ} (hP : Feasible e P₁ P₂)
    (hQ : Feasible e Q₁ Q₂) : EU e P₁ P₂ < EU e Q₁ Q₂ ↔ consProd e P₁ P₂ < consProd e Q₁ Q₂ := by
  have pos : ∀ {a b : ℝ}, Feasible e a b → 0 < consProd e a b := by
    rintro a b ⟨h1, h2, h3, h4⟩
    unfold consProd
    positivity
  rw [EU_eq_log_consProd hP, EU_eq_log_consProd hQ, div_lt_div_iff_of_pos_right two_pos]
  exact Real.log_lt_log_iff (pos hP) (pos hQ)

/-- Tangent-line bound for `log`: `log x ≤ log x₀ + (x − x₀)/x₀` for `x, x₀ > 0`. -/
theorem log_le_tangent {x x₀ : ℝ} (hx : 0 < x) (hx₀ : 0 < x₀) :
    Real.log x ≤ Real.log x₀ + (x - x₀) / x₀ := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hx₀)
  rw [Real.log_div hx.ne' hx₀.ne'] at h
  have : (x - x₀) / x₀ = x / x₀ - 1 := by field_simp
  linarith

/-- Strict tangent-line bound for `log` when `x ≠ x₀`. -/
theorem log_lt_tangent {x x₀ : ℝ} (hx : 0 < x) (hx₀ : 0 < x₀) (hne : x ≠ x₀) :
    Real.log x < Real.log x₀ + (x - x₀) / x₀ := by
  have hne' : x / x₀ ≠ 1 := by
    intro h
    exact hne ((div_eq_one_iff_eq hx₀.ne').1 h)
  have h := Real.log_lt_sub_one_of_pos (div_pos hx hx₀) hne'
  rw [Real.log_div hx.ne' hx₀.ne'] at h
  have : (x - x₀) / x₀ = x / x₀ - 1 := by field_simp
  linarith

/-! ## Autarky `A`, bonds `B`, Arrow–Debreu `E` -/

/-- A country with date-1 endowment `y₁` and date-2 endowment `Y` facing a riskless gross rate
`R > 0` has present-value wealth `W = y₁ + Y/R` and date-2 consumption `R(W − c₁)`; its unique
optimal date-1 consumption is `W/2`, O&R p. 404. -/
theorem bond_demand_optimal {W R c₁ : ℝ} (hR : 0 < R) (hc : 0 < c₁) (hcW : c₁ < W) :
    lifetimeU c₁ (R * (W - c₁)) ≤ lifetimeU (W / 2) (R * (W - W / 2)) ∧
      (lifetimeU c₁ (R * (W - c₁)) = lifetimeU (W / 2) (R * (W - W / 2)) → c₁ = W / 2) := by
  have hW : 0 < W - c₁ := by linarith
  have hW2 : 0 < W / 2 := by linarith
  have hW3 : 0 < W - W / 2 := by linarith
  have expand : ∀ a b : ℝ, 0 < a → 0 < b →
      lifetimeU a (R * b) = Real.log a + Real.log b + Real.log R := by
    intro a b ha hb
    unfold lifetimeU
    rw [Real.log_mul hR.ne' hb.ne']
    ring
  rw [expand _ _ hc hW, expand _ _ hW2 hW3]
  have hmean : (c₁ + (W - c₁)) / 2 = W / 2 := by ring
  have hval : Real.log (W / 2) + Real.log (W - W / 2) = 2 * Real.log (W / 2) := by
    rw [show W - W / 2 = W / 2 by ring]
    ring
  refine ⟨?_, ?_⟩
  · have := log_add_log_le_two_log_mean hc hW
    rw [hmean] at this
    linarith
  · intro heq
    by_contra hne
    have hne' : c₁ ≠ W - c₁ := by
      intro h
      exact hne (by linarith)
    have := log_add_log_lt_two_log_mean hc hW hne'
    rw [hmean] at this
    linarith

/-- The bond market clears iff the gross interest rate is `1`, i.e. `r = 0` is the unique
equilibrium rate, O&R p. 403–404: aggregate date-1 demand `(Ȳ + Y/R)/2 + (Y_ + Y/R)/2` equals
aggregate date-1 output `Ȳ + Y_` iff `R = 1`. -/
theorem bond_market_clears_iff (e : Endowments) {R : ℝ} (hR : 0 < R) :
    (e.hi + e.avg / R) / 2 + (e.lo + e.avg / R) / 2 = e.hi + e.lo ↔ R = 1 := by
  have hav := e.avg_pos
  have hlo : e.lo = 2 * e.avg - e.hi := lo_eq e
  rw [hlo]
  constructor
  · intro h
    have h2 : e.avg / R = e.avg := by linarith
    rw [div_eq_iff hR.ne'] at h2
    nlinarith
  · rintro rfl
    ring

/-- The bond allocation `B` written as a contract: `P₁ = (Ȳ − Y)/2` (type `H` lends) and
`P₂ = −(Ȳ − Y)/2` (it is repaid), O&R p. 404. -/
noncomputable def bondP₁ (e : Endowments) : ℝ := (e.hi - e.avg) / 2

/-- Date-2 payment of the bond allocation `B`, O&R p. 404. -/
noncomputable def bondP₂ (e : Endowments) : ℝ := -((e.hi - e.avg) / 2)

/-- At `B` type `H` consumes `(Ȳ + Y)/2` on both dates and type `L` consumes `(Y_ + Y)/2` on
both dates, O&R p. 404; these are the bond demands at `R = 1`. -/
theorem bond_B_consumption (e : Endowments) :
    e.hi - bondP₁ e = (e.hi + e.avg) / 2 ∧ e.avg - bondP₂ e = (e.hi + e.avg) / 2 ∧
      e.lo + bondP₁ e = (e.lo + e.avg) / 2 ∧ e.avg + bondP₂ e = (e.lo + e.avg) / 2 := by
  have hlo : e.lo = 2 * e.avg - e.hi := lo_eq e
  unfold bondP₁ bondP₂
  refine ⟨by ring, by ring, by rw [hlo]; ring, by rw [hlo]; ring⟩

/-- `B` is feasible, and strictly incentive compatible for both types, O&R p. 404
(noncontingent bonds need no revelation of information). -/
theorem bond_B_feasible_ic (e : Endowments) :
    Feasible e (bondP₁ e) (bondP₂ e) ∧ e.avg * bondP₁ e + e.hi * bondP₂ e < 0 ∧
      0 < e.avg * bondP₁ e + e.lo * bondP₂ e := by
  obtain ⟨b1, b2, b3, b4⟩ := bond_B_consumption e
  have := e.lo_pos; have := e.avg_lt_hi; have := e.lo_lt_avg; have := e.avg_pos
  refine ⟨⟨by rw [b1]; linarith, by rw [b2]; linarith, by rw [b3]; linarith,
    by rw [b4]; linarith⟩, ?_, ?_⟩ <;> unfold bondP₁ bondP₂ <;> nlinarith

/-- Autarky `A` (the null contract) is worse than `B` ex post for each type, O&R p. 404. -/
theorem bond_B_expost_better (e : Endowments) :
    lifetimeU e.hi e.avg < lifetimeU (e.hi - bondP₁ e) (e.avg - bondP₂ e) ∧
      lifetimeU e.lo e.avg < lifetimeU (e.lo + bondP₁ e) (e.avg + bondP₂ e) := by
  obtain ⟨b1, b2, b3, b4⟩ := bond_B_consumption e
  rw [b1, b2, b3, b4]
  have := e.lo_pos; have := e.avg_lt_hi; have := e.lo_lt_avg; have := e.avg_pos
  unfold lifetimeU
  constructor
  · have := log_add_log_lt_two_log_mean e.hi_pos e.avg_pos (by linarith)
    linarith
  · have := log_add_log_lt_two_log_mean e.lo_pos e.avg_pos (by linarith)
    linarith

/-- `B` gives strictly higher expected utility than autarky `A`, O&R p. 404 ("using the
concavity of utility"). -/
theorem eu_autarky_lt_bond (e : Endowments) : EU e 0 0 < EU e (bondP₁ e) (bondP₂ e) := by
  obtain ⟨h1, h2⟩ := bond_B_expost_better e
  unfold EU
  simp only [sub_zero, add_zero]
  linarith

/-- The Arrow–Debreu allocation `E`: full insurance, `P₁ = Ȳ − Y`, `P₂ = 0`, so both types
consume `Y` on both dates, O&R p. 402–403. -/
theorem arrowDebreu_consumption (e : Endowments) :
    e.hi - (e.hi - e.avg) = e.avg ∧ e.lo + (e.hi - e.avg) = e.avg := by
  have hlo : e.lo = 2 * e.avg - e.hi := lo_eq e
  constructor <;> [ring; (rw [hlo]; ring)]

/-- `E` is the unique maximiser of expected utility over all feasible contracts when incentive
constraints are ignored, O&R p. 403. -/
theorem arrowDebreu_unconstrained_optimum {e : Endowments} {P₁ P₂ : ℝ} (h : Feasible e P₁ P₂)
    (hne : P₁ ≠ e.hi - e.avg ∨ P₂ ≠ 0) : EU e P₁ P₂ < EU e (e.hi - e.avg) 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨a1, a2⟩ := arrowDebreu_consumption e
  have hlo : e.lo = 2 * e.avg - e.hi := lo_eq e
  unfold EU lifetimeU
  rw [a1, a2]
  simp only [sub_zero, add_zero]
  have m1 : ((e.hi - P₁) + (e.lo + P₁)) / 2 = e.avg := by rw [hlo]; ring
  have m2 : ((e.avg - P₂) + (e.avg + P₂)) / 2 = e.avg := by ring
  rcases hne with hne | hne
  · have s1 := log_add_log_lt_two_log_mean h1 h3 (by intro hh; apply hne; linarith)
    have s2 := log_add_log_le_two_log_mean h2 h4
    rw [m1] at s1; rw [m2] at s2
    linarith
  · have s1 := log_add_log_le_two_log_mean h1 h3
    have s2 := log_add_log_lt_two_log_mean h2 h4 (by intro hh; apply hne; linarith)
    rw [m1] at s1; rw [m2] at s2
    linarith

/-- `E` violates (41): type `H` would claim low output and move to point `D`, O&R p. 404. -/
theorem arrowDebreu_violates_icH (e : Endowments) : ¬ ICH e (e.hi - e.avg) 0 := by
  have hf : Feasible e (e.hi - e.avg) 0 := by
    obtain ⟨a1, a2⟩ := arrowDebreu_consumption e
    refine ⟨by rw [a1]; exact e.avg_pos, by simp [e.avg_pos], by rw [a2]; exact e.avg_pos,
      by simp [e.avg_pos]⟩
  rw [icH_iff_linear hf]
  have := e.avg_lt_hi; have := e.avg_pos
  nlinarith

/-! ## Contract (43): point `C` -/

/-- Date-1 payment of contract (43), `P₁ = Ȳ(Ȳ − Y)/(Ȳ + Y)`, O&R p. 405. -/
noncomputable def contractCP₁ (e : Endowments) : ℝ := e.hi / (e.hi + e.avg) * (e.hi - e.avg)

/-- Date-2 payment of contract (43), `P₂ = −Y(Ȳ − Y)/(Ȳ + Y)`, O&R p. 405. -/
noncomputable def contractCP₂ (e : Endowments) : ℝ := -(e.avg / (e.hi + e.avg) * (e.hi - e.avg))

/-- Under contract (43) type `H` consumes `2ȲY/(Ȳ+Y)` and type `L` consumes `2Y²/(Ȳ+Y)` on both
dates, O&R p. 405–406. -/
theorem contractC_consumption (e : Endowments) :
    e.hi - contractCP₁ e = 2 * e.hi * e.avg / (e.hi + e.avg) ∧
      e.avg - contractCP₂ e = 2 * e.hi * e.avg / (e.hi + e.avg) ∧
      e.lo + contractCP₁ e = 2 * e.avg ^ 2 / (e.hi + e.avg) ∧
      e.avg + contractCP₂ e = 2 * e.avg ^ 2 / (e.hi + e.avg) := by
  have hlo : e.lo = 2 * e.avg - e.hi := lo_eq e
  have hs : e.hi + e.avg ≠ 0 := (add_pos e.hi_pos e.avg_pos).ne'
  unfold contractCP₁ contractCP₂
  refine ⟨?_, ?_, ?_, ?_⟩ <;> [skip; skip; rw [hlo]; skip] <;> field_simp <;> ring

/-- Contract (43) is feasible, O&R p. 405. -/
theorem contractC_feasible (e : Endowments) : Feasible e (contractCP₁ e) (contractCP₂ e) := by
  obtain ⟨c1, c2, c3, c4⟩ := contractC_consumption e
  have := e.hi_pos; have := e.avg_pos
  refine ⟨?_, ?_, ?_, ?_⟩ <;> [rw [c1]; rw [c2]; rw [c3]; rw [c4]] <;> positivity

/-- At `C`, (41) binds and (42) holds strictly: the operative constraint stops the rich
country posing as poor, O&R p. 406. -/
theorem contractC_icH_binds_icL_slack (e : Endowments) :
    e.avg * contractCP₁ e + e.hi * contractCP₂ e = 0 ∧
      0 < e.avg * contractCP₁ e + e.lo * contractCP₂ e := by
  have hs : 0 < e.hi + e.avg := add_pos e.hi_pos e.avg_pos
  have := e.avg_lt_hi; have := e.lo_lt_avg; have := e.avg_pos
  unfold contractCP₁ contractCP₂
  constructor
  · field_simp
    ring
  · have key : e.avg * (e.hi / (e.hi + e.avg) * (e.hi - e.avg)) +
        e.lo * -(e.avg / (e.hi + e.avg) * (e.hi - e.avg)) =
        e.avg * (e.hi - e.avg) * (e.hi - e.lo) / (e.hi + e.avg) := by
      field_simp
      ring
    rw [key]
    have : 0 < e.hi - e.lo := by linarith
    have : 0 < e.hi - e.avg := by linarith
    positivity

/-- `C` is incentive compatible: it satisfies (41) and (42), O&R p. 406. -/
theorem contractC_ic (e : Endowments) :
    ICH e (contractCP₁ e) (contractCP₂ e) ∧ ICL e (contractCP₁ e) (contractCP₂ e) := by
  obtain ⟨hH, hL⟩ := contractC_icH_binds_icL_slack e
  exact ⟨(icH_iff_linear (contractC_feasible e)).2 hH.le,
    (icL_iff_linear (contractC_feasible e)).2 hL.le⟩

/-- `P₁ > (Ȳ − Y)/2` and `−P₂ < (Ȳ − Y)/2` at `C`, O&R p. 406. -/
theorem contractC_vs_bond (e : Endowments) :
    (e.hi - e.avg) / 2 < contractCP₁ e ∧ -contractCP₂ e < (e.hi - e.avg) / 2 := by
  have hs : 0 < e.hi + e.avg := add_pos e.hi_pos e.avg_pos
  have hd : 0 < e.hi - e.avg := by linarith [e.avg_lt_hi]
  unfold contractCP₁ contractCP₂
  constructor
  · have : e.hi / (e.hi + e.avg) * (e.hi - e.avg) - (e.hi - e.avg) / 2 =
        (e.hi - e.avg) ^ 2 / (2 * (e.hi + e.avg)) := by field_simp; ring
    have : 0 < (e.hi - e.avg) ^ 2 / (2 * (e.hi + e.avg)) := by positivity
    linarith
  · have : (e.hi - e.avg) / 2 - -(-(e.avg / (e.hi + e.avg) * (e.hi - e.avg))) =
        (e.hi - e.avg) ^ 2 / (2 * (e.hi + e.avg)) := by field_simp; ring
    have : 0 < (e.hi - e.avg) ^ 2 / (2 * (e.hi + e.avg)) := by positivity
    linarith

/-- The net-present-value transfer to type `L` at `C` (at `r = 0`) is `(Ȳ − Y)²/(Ȳ + Y) > 0`,
versus zero at `B`, O&R p. 406. -/
theorem contractC_npv_transfer (e : Endowments) :
    contractCP₁ e + contractCP₂ e = (e.hi - e.avg) ^ 2 / (e.hi + e.avg) ∧
      0 < contractCP₁ e + contractCP₂ e ∧ bondP₁ e + bondP₂ e = 0 := by
  have hs : 0 < e.hi + e.avg := add_pos e.hi_pos e.avg_pos
  have hd : 0 < e.hi - e.avg := by linarith [e.avg_lt_hi]
  have h1 : contractCP₁ e + contractCP₂ e = (e.hi - e.avg) ^ 2 / (e.hi + e.avg) := by
    unfold contractCP₁ contractCP₂; field_simp; ring
  refine ⟨h1, by rw [h1]; positivity, by unfold bondP₁ bondP₂; ring⟩

/-- `C` lies on the contract curve: each type consumes the same amount on both dates, so the
marginal rates of substitution `C₂/C₁` of both types equal `1`, O&R p. 406 (fn 58). -/
theorem contractC_on_contract_curve (e : Endowments) :
    e.hi - contractCP₁ e = e.avg - contractCP₂ e ∧
      e.lo + contractCP₁ e = e.avg + contractCP₂ e := by
  obtain ⟨c1, c2, c3, c4⟩ := contractC_consumption e
  exact ⟨by rw [c1, c2], by rw [c3, c4]⟩

/-- At `C` the ex post consumption gap between the types is smaller than at `B`, O&R fn 58. -/
theorem contractC_gap_lt_bond (e : Endowments) :
    (e.hi - contractCP₁ e) - (e.lo + contractCP₁ e) < (e.hi - bondP₁ e) - (e.lo + bondP₁ e) := by
  obtain ⟨c1, _, c3, _⟩ := contractC_consumption e
  obtain ⟨b1, _, b3, _⟩ := bond_B_consumption e
  rw [c1, c3, b1, b3]
  have hs : 0 < e.hi + e.avg := add_pos e.hi_pos e.avg_pos
  have hd : 0 < e.hi - e.avg := by linarith [e.avg_lt_hi]
  have hlo : e.lo = 2 * e.avg - e.hi := lo_eq e
  rw [hlo]
  have : (e.hi + e.avg) / 2 - (2 * e.avg - e.hi + e.avg) / 2 -
      (2 * e.hi * e.avg / (e.hi + e.avg) - 2 * e.avg ^ 2 / (e.hi + e.avg)) =
      (e.hi - e.avg) ^ 2 / (e.hi + e.avg) := by field_simp; ring
  have : 0 < (e.hi - e.avg) ^ 2 / (e.hi + e.avg) := by positivity
  linarith

/-- `C` yields strictly higher expected utility than `B`, O&R p. 406: the key identity is
`16ȲY³ − (Ȳ+Y)³(3Y−Ȳ) = (Ȳ−Y)³(Ȳ+3Y) > 0`. -/
theorem eu_bond_lt_contractC (e : Endowments) :
    EU e (bondP₁ e) (bondP₂ e) < EU e (contractCP₁ e) (contractCP₂ e) := by
  rw [EU_lt_iff (bond_B_feasible_ic e).1 (contractC_feasible e)]
  obtain ⟨c1, c2, c3, c4⟩ := contractC_consumption e
  obtain ⟨b1, b2, b3, b4⟩ := bond_B_consumption e
  unfold consProd
  rw [c1, c2, c3, c4, b1, b2, b3, b4]
  have hs : 0 < e.hi + e.avg := add_pos e.hi_pos e.avg_pos
  have hd : 0 < e.hi - e.avg := by linarith [e.avg_lt_hi]
  have hav := e.avg_pos
  have hlo : e.lo = 2 * e.avg - e.hi := lo_eq e
  have hlo' : 0 < e.lo := e.lo_pos
  rw [hlo] at hlo' ⊢
  set a := e.avg
  set h := e.hi
  -- compare the square roots of the two products
  have baseB : 0 < (h + a) / 2 * ((2 * a - h + a) / 2) := by
    have : 0 < 2 * a - h + a := by linarith
    positivity
  have key : (h + a) / 2 * ((2 * a - h + a) / 2) <
      2 * h * a / (h + a) * (2 * a ^ 2 / (h + a)) := by
    rw [show 2 * h * a / (h + a) * (2 * a ^ 2 / (h + a)) = 4 * h * a ^ 3 / (h + a) ^ 2 by
      field_simp; ring]
    rw [lt_div_iff₀ (by positivity)]
    have id : 16 * h * a ^ 3 - (h + a) ^ 3 * (3 * a - h) = (h - a) ^ 3 * (h + 3 * a) := by ring
    have : 0 < (h - a) ^ 3 * (h + 3 * a) := mul_pos (pow_pos hd 3) (by linarith)
    nlinarith
  have e1 : (h + a) / 2 * ((h + a) / 2) * ((2 * a - h + a) / 2 * ((2 * a - h + a) / 2)) =
      ((h + a) / 2 * ((2 * a - h + a) / 2)) ^ 2 := by ring
  have e2 : 2 * h * a / (h + a) * (2 * h * a / (h + a)) *
      (2 * a ^ 2 / (h + a) * (2 * a ^ 2 / (h + a))) =
      (2 * h * a / (h + a) * (2 * a ^ 2 / (h + a))) ^ 2 := by ring
  rw [e1, e2]
  exact pow_lt_pow_left₀ key baseB.le two_ne_zero

/-- The book's claim that type `L` never gains from posing as `H` needs care: at contract (43)
with `Y_ = 1/5`, `Ȳ = 9/5` the deviation requires negative date-1 consumption `Y_ − P₁ < 0`
(O&R p. 405–406 overlook this; (42) then holds because the deviation is unavailable). -/
theorem contractC_lowType_deviation_infeasible_example :
    ∃ e : Endowments, e.lo = 1 / 5 ∧ e.hi = 9 / 5 ∧ e.lo - contractCP₁ e < 0 := by
  refine ⟨⟨1 / 5, 9 / 5, by norm_num, by norm_num⟩, rfl, rfl, ?_⟩
  unfold contractCP₁ Endowments.avg
  norm_num


/-! ## The optimal incentive-compatible contract

The book leaves its derivation as an exercise (p. 406). With (41) binding, `P₂ = −Y P₁/Ȳ` and
the first-order condition reduces to the quadratic `4P₁² + (Ȳ + 3Y_)P₁ − Ȳ(Ȳ − Y_) = 0`, whose
positive root is the optimum. We prove global optimality and uniqueness over the whole
incentive-compatible set with the tangent-line inequality for `log` and a Kuhn–Tucker
multiplier `μ > 0` on (41). -/

/-- The discriminant `(Ȳ + 3Y_)² + 16Ȳ(Ȳ − Y_)` of the optimality quadratic. -/
noncomputable def optDisc (e : Endowments) : ℝ :=
  (e.hi + 3 * e.lo) ^ 2 + 16 * e.hi * (e.hi - e.lo)

/-- Date-1 payment of the optimal incentive-compatible contract, the positive root of
`4P₁² + (Ȳ + 3Y_)P₁ − Ȳ(Ȳ − Y_) = 0` (the exercise of O&R p. 406). -/
noncomputable def optP₁ (e : Endowments) : ℝ :=
  (Real.sqrt (optDisc e) - (e.hi + 3 * e.lo)) / 8

/-- Date-2 payment of the optimal contract, on the binding (41) line: `P₂ = −Y P₁/Ȳ`. -/
noncomputable def optP₂ (e : Endowments) : ℝ := -(e.avg * optP₁ e / e.hi)

/-- `optP₁` solves the optimality quadratic. -/
theorem optP₁_quadratic (e : Endowments) :
    4 * optP₁ e ^ 2 + (e.hi + 3 * e.lo) * optP₁ e - e.hi * (e.hi - e.lo) = 0 := by
  have hD : 0 ≤ optDisc e := by
    unfold optDisc; have := e.lo_lt_hi; have := e.lo_pos; nlinarith
  have hs := Real.sq_sqrt hD
  unfold optP₁
  unfold optDisc at hs ⊢
  nlinarith [hs]

/-- `0 < optP₁ < Ȳ`. -/
theorem optP₁_pos_lt (e : Endowments) : 0 < optP₁ e ∧ optP₁ e < e.hi := by
  have hlt := e.lo_lt_hi; have hlo := e.lo_pos; have hhi := e.hi_pos
  unfold optP₁
  constructor
  · have : e.hi + 3 * e.lo < Real.sqrt (optDisc e) := by
      rw [Real.lt_sqrt (by linarith)]
      unfold optDisc; nlinarith
    linarith
  · have : Real.sqrt (optDisc e) < 9 * e.hi + 3 * e.lo := by
      rw [Real.sqrt_lt' (by linarith)]
      unfold optDisc; nlinarith
    linarith

/-- The consumptions at the optimal contract: `H` consumes `(Ȳ − p, Y(Ȳ + p)/Ȳ)` and `L`
consumes `(Y_ + p, Y(Ȳ − p)/Ȳ)`, with `p = optP₁`. -/
theorem opt_consumption (e : Endowments) :
    e.avg - optP₂ e = e.avg * (e.hi + optP₁ e) / e.hi ∧
      e.avg + optP₂ e = e.avg * (e.hi - optP₁ e) / e.hi := by
  have := e.hi_pos.ne'
  unfold optP₂
  constructor <;> field_simp <;> ring

/-- The optimal contract is feasible. -/
theorem opt_feasible (e : Endowments) : Feasible e (optP₁ e) (optP₂ e) := by
  obtain ⟨hp, hph⟩ := optP₁_pos_lt e
  obtain ⟨c2, c4⟩ := opt_consumption e
  have := e.avg_pos; have := e.hi_pos; have := e.lo_pos
  refine ⟨by linarith, ?_, by linarith, ?_⟩
  · rw [c2]; have : 0 < e.hi + optP₁ e := by linarith
    positivity
  · rw [c4]; have : 0 < e.hi - optP₁ e := by linarith
    positivity

/-- At the optimal contract (41) binds and (42) is slack (the exercise of O&R p. 406). -/
theorem opt_icH_binds_icL_slack (e : Endowments) :
    e.avg * optP₁ e + e.hi * optP₂ e = 0 ∧ 0 < e.avg * optP₁ e + e.lo * optP₂ e := by
  obtain ⟨hp, _⟩ := optP₁_pos_lt e
  have hhi := e.hi_pos; have hav := e.avg_pos; have hlt := e.lo_lt_hi
  unfold optP₂
  constructor
  · field_simp; ring
  · have : e.avg * optP₁ e + e.lo * -(e.avg * optP₁ e / e.hi) =
        e.avg * optP₁ e * (e.hi - e.lo) / e.hi := by field_simp; ring
    rw [this]
    have : 0 < e.hi - e.lo := by linarith
    positivity

/-- The optimal contract is incentive compatible. -/
theorem opt_ic (e : Endowments) : ICH e (optP₁ e) (optP₂ e) ∧ ICL e (optP₁ e) (optP₂ e) := by
  obtain ⟨hH, hL⟩ := opt_icH_binds_icL_slack e
  exact ⟨(icH_iff_linear (opt_feasible e)).2 hH.le, (icL_iff_linear (opt_feasible e)).2 hL.le⟩

/-- The Kuhn–Tucker multiplier on (41) at the optimum, `μ = 2p/(Y(Ȳ² − p²)) > 0`. -/
noncomputable def optMultiplier (e : Endowments) : ℝ :=
  2 * optP₁ e / (e.avg * (e.hi ^ 2 - optP₁ e ^ 2))

/-- Kuhn–Tucker conditions at the optimal contract: the gradient of expected utility is
`μ ∇(−(Y P₁ + Ȳ P₂))` with `μ > 0`, i.e. `1/c^L₁ − 1/c^H₁ = μ Y` and `1/c^L₂ − 1/c^H₂ = μ Ȳ`. -/
theorem opt_kuhn_tucker (e : Endowments) :
    0 < optMultiplier e ∧
      1 / (e.lo + optP₁ e) - 1 / (e.hi - optP₁ e) = optMultiplier e * e.avg ∧
      1 / (e.avg + optP₂ e) - 1 / (e.avg - optP₂ e) = optMultiplier e * e.hi := by
  obtain ⟨hp, hph⟩ := optP₁_pos_lt e
  obtain ⟨c2, c4⟩ := opt_consumption e
  have hq := optP₁_quadratic e
  have hhi := e.hi_pos; have hav := e.avg_pos; have hlo := e.lo_pos
  have h1 : 0 < e.hi - optP₁ e := by linarith
  have h2 : 0 < e.hi + optP₁ e := by linarith
  have h3 : 0 < e.lo + optP₁ e := by linarith
  have hsq : 0 < e.hi ^ 2 - optP₁ e ^ 2 := by nlinarith
  unfold optMultiplier
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_sub_div _ _ h3.ne' h1.ne']
    have r : 2 * optP₁ e / (e.avg * (e.hi ^ 2 - optP₁ e ^ 2)) * e.avg =
        2 * optP₁ e / ((e.hi - optP₁ e) * (e.hi + optP₁ e)) := by
      field_simp; ring
    rw [r, div_eq_div_iff (mul_pos h3 h1).ne' (mul_pos h1 h2).ne']
    linear_combination (-(e.hi - optP₁ e)) * hq
  · rw [c2, c4]
    field_simp
    ring

/-- **Optimal incentive-compatible contract: global optimality with uniqueness.** Every other
feasible incentive-compatible contract gives strictly lower expected utility (the exercise of
O&R p. 406). -/
theorem opt_strictly_best {e : Endowments} {P₁ P₂ : ℝ} (h : Feasible e P₁ P₂)
    (hH : ICH e P₁ P₂) (hne : P₁ ≠ optP₁ e ∨ P₂ ≠ optP₂ e) :
    EU e P₁ P₂ < EU e (optP₁ e) (optP₂ e) := by
  have hlin := (icH_iff_linear h).1 hH
  obtain ⟨hμ, k1, k2⟩ := opt_kuhn_tucker e
  obtain ⟨hb, _⟩ := opt_icH_binds_icL_slack e
  obtain ⟨o1, o2, o3, o4⟩ := opt_feasible e
  obtain ⟨f1, f2, f3, f4⟩ := h
  set p := optP₁ e
  set q := optP₂ e
  set μ := optMultiplier e
  -- the four tangent bounds
  have t1 := log_le_tangent f1 o1
  have t2 := log_le_tangent f2 o2
  have t3 := log_le_tangent f3 o3
  have t4 := log_le_tangent f4 o4
  -- the first-order terms sum to `μ (Y P₁ + Ȳ P₂) ≤ 0`
  have lin : (e.hi - P₁ - (e.hi - p)) / (e.hi - p) + (e.avg - P₂ - (e.avg - q)) / (e.avg - q) +
      (e.lo + P₁ - (e.lo + p)) / (e.lo + p) + (e.avg + P₂ - (e.avg + q)) / (e.avg + q) =
      μ * (e.avg * P₁ + e.hi * P₂) := by
    have r : (e.hi - P₁ - (e.hi - p)) / (e.hi - p) + (e.avg - P₂ - (e.avg - q)) / (e.avg - q) +
        (e.lo + P₁ - (e.lo + p)) / (e.lo + p) + (e.avg + P₂ - (e.avg + q)) / (e.avg + q) =
        (P₁ - p) * (1 / (e.lo + p) - 1 / (e.hi - p)) +
          (P₂ - q) * (1 / (e.avg + q) - 1 / (e.avg - q)) := by
      field_simp; ring
    rw [r, k1, k2]
    linear_combination (-μ) * hb
  have hneg : μ * (e.avg * P₁ + e.hi * P₂) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hμ.le hlin
  unfold EU lifetimeU
  rcases hne with hne | hne
  · have s1 := log_lt_tangent f1 o1 (by intro hh; apply hne; linarith)
    linarith
  · have s2 := log_lt_tangent f2 o2 (by intro hh; apply hne; linarith)
    linarith

/-- The optimal contract weakly beats every feasible contract satisfying (41). -/
theorem opt_is_max {e : Endowments} {P₁ P₂ : ℝ} (h : Feasible e P₁ P₂) (hH : ICH e P₁ P₂) :
    EU e P₁ P₂ ≤ EU e (optP₁ e) (optP₂ e) := by
  by_cases hc : P₁ = optP₁ e ∧ P₂ = optP₂ e
  · rw [hc.1, hc.2]
  · have : P₁ ≠ optP₁ e ∨ P₂ ≠ optP₂ e := by tauto
    exact (opt_strictly_best h hH this).le

/-- **Existence and uniqueness of the optimal incentive-compatible contract** (O&R p. 406):
there is exactly one feasible contract satisfying (41) and (42) that maximises expected
utility over all such contracts, namely `(optP₁, optP₂)`. -/
theorem optimal_contract_exists_unique (e : Endowments) :
    ∃! c : ℝ × ℝ, (Feasible e c.1 c.2 ∧ ICH e c.1 c.2 ∧ ICL e c.1 c.2) ∧
      ∀ P₁ P₂, Feasible e P₁ P₂ → ICH e P₁ P₂ → ICL e P₁ P₂ → EU e P₁ P₂ ≤ EU e c.1 c.2 := by
  refine ⟨(optP₁ e, optP₂ e), ⟨⟨opt_feasible e, opt_ic e⟩, ?_⟩, ?_⟩
  · intro P₁ P₂ h hH _
    exact opt_is_max h hH
  · rintro ⟨c₁, c₂⟩ ⟨⟨hf, hH, _⟩, hmax⟩
    by_contra hc
    have hne : c₁ ≠ optP₁ e ∨ c₂ ≠ optP₂ e := by
      by_contra hh
      push Not at hh
      exact hc (Prod.ext hh.1 hh.2)
    have := opt_strictly_best hf hH hne
    have := hmax (optP₁ e) (optP₂ e) (opt_feasible e) (opt_ic e).1 (opt_ic e).2
    simp only at this
    linarith

/-- Which constraints bind: at *any* optimal incentive-compatible contract (41) binds and (42)
is slack (O&R p. 406: "the operative constraint is to prevent the high-income country from
posing as poor"). -/
theorem optimal_contract_binding {e : Endowments} {P₁ P₂ : ℝ} (h : Feasible e P₁ P₂)
    (hH : ICH e P₁ P₂) (hmax : ∀ Q₁ Q₂, Feasible e Q₁ Q₂ → ICH e Q₁ Q₂ → ICL e Q₁ Q₂ →
      EU e Q₁ Q₂ ≤ EU e P₁ P₂) :
    e.avg * P₁ + e.hi * P₂ = 0 ∧ 0 < e.avg * P₁ + e.lo * P₂ := by
  have heq : P₁ = optP₁ e ∧ P₂ = optP₂ e := by
    by_contra hc
    have hne : P₁ ≠ optP₁ e ∨ P₂ ≠ optP₂ e := by tauto
    have := opt_strictly_best h hH hne
    have := hmax _ _ (opt_feasible e) (opt_ic e).1 (opt_ic e).2
    linarith
  rw [heq.1, heq.2]
  exact opt_icH_binds_icL_slack e

/-- `C` lies on the binding (41) line: `P₂^C = −Y P₁^C/Ȳ`, and `P₁^C = Ȳ(Ȳ − Y_)/(3Ȳ + Y_)`. -/
theorem contractC_on_icH_line (e : Endowments) :
    contractCP₂ e = -(e.avg * contractCP₁ e / e.hi) ∧
      contractCP₁ e = e.hi * (e.hi - e.lo) / (3 * e.hi + e.lo) := by
  have hhi := e.hi_pos.ne'
  have hs : e.hi + e.avg ≠ 0 := (add_pos e.hi_pos e.avg_pos).ne'
  have hs' : 3 * e.hi + e.lo ≠ 0 := by have := e.hi_pos; have := e.lo_pos; positivity
  unfold contractCP₁ contractCP₂
  constructor
  · field_simp
  · unfold Endowments.avg
    field_simp
    ring

/-- **The optimal contract lies strictly north-west of `C`** (O&R p. 406): type `H` pays more on
date 1 and receives more on date 2, `P₁^* > P₁^C` and `P₂^* < P₂^C`. -/
theorem opt_northwest_of_C (e : Endowments) :
    contractCP₁ e < optP₁ e ∧ optP₂ e < contractCP₂ e := by
  obtain ⟨hl, hc⟩ := contractC_on_icH_line e
  obtain ⟨hp, _⟩ := optP₁_pos_lt e
  have hq := optP₁_quadratic e
  have hhi := e.hi_pos; have hlo := e.lo_pos; have hlt := e.lo_lt_hi; have hav := e.avg_pos
  have hC : 0 < contractCP₁ e := by
    rw [hc]; have : 0 < e.hi - e.lo := by linarith
    positivity
  -- the quadratic is negative at `P₁^C`
  have qC : 4 * contractCP₁ e ^ 2 + (e.hi + 3 * e.lo) * contractCP₁ e -
      e.hi * (e.hi - e.lo) < 0 := by
    rw [hc]
    have h3 : 0 < 3 * e.hi + e.lo := by positivity
    have key : 4 * (e.hi * (e.hi - e.lo) / (3 * e.hi + e.lo)) ^ 2 +
        (e.hi + 3 * e.lo) * (e.hi * (e.hi - e.lo) / (3 * e.hi + e.lo)) -
        e.hi * (e.hi - e.lo) =
        -(2 * e.hi * (e.hi - e.lo) * (e.hi ^ 2 - e.lo ^ 2)) / (3 * e.hi + e.lo) ^ 2 := by
      field_simp; ring
    rw [key]
    have : 0 < 2 * e.hi * (e.hi - e.lo) * (e.hi ^ 2 - e.lo ^ 2) := by
      have : 0 < e.hi - e.lo := by linarith
      have : 0 < e.hi ^ 2 - e.lo ^ 2 := by nlinarith
      positivity
    have : 0 < (3 * e.hi + e.lo) ^ 2 := by positivity
    exact div_neg_of_neg_of_pos (by linarith) this
  have h1 : contractCP₁ e < optP₁ e := by
    by_contra hle
    push Not at hle
    nlinarith
  refine ⟨h1, ?_⟩
  rw [hl]
  unfold optP₂
  have : e.avg * contractCP₁ e / e.hi < e.avg * optP₁ e / e.hi := by
    apply div_lt_div_of_pos_right _ hhi
    exact mul_lt_mul_of_pos_left h1 hav
  linarith

/-- On the binding (41) line `P₂ = −Y P₁/Ȳ` (with `0 < P₁ < Ȳ`), the two types' marginal rates of
substitution `C₂/C₁` are equal iff `P₁ = P₁^C`: the contract curve meets the line only at `C`. -/
theorem contract_curve_on_icH_line_iff (e : Endowments) (P₁ : ℝ) :
    (e.avg + e.avg * P₁ / e.hi) * (e.lo + P₁) = (e.avg - e.avg * P₁ / e.hi) * (e.hi - P₁) ↔
      P₁ = contractCP₁ e := by
  obtain ⟨_, hc⟩ := contractC_on_icH_line e
  have hhi := e.hi_pos; have hlo := e.lo_pos; have hav := e.avg_pos
  have h3 : 0 < 3 * e.hi + e.lo := by positivity
  rw [hc, eq_div_iff h3.ne']
  have key : (e.avg + e.avg * P₁ / e.hi) * (e.lo + P₁) - (e.avg - e.avg * P₁ / e.hi) * (e.hi - P₁)
      = e.avg / e.hi * (P₁ * (3 * e.hi + e.lo) - e.hi * (e.hi - e.lo)) := by
    field_simp; ring
  constructor
  · intro heq
    have : e.avg / e.hi * (P₁ * (3 * e.hi + e.lo) - e.hi * (e.hi - e.lo)) = 0 := by
      rw [← key]; linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (by positivity)
    · linarith
  · intro heq
    have : e.avg / e.hi * (P₁ * (3 * e.hi + e.lo) - e.hi * (e.hi - e.lo)) = 0 := by
      rw [heq]; ring
    linarith

/-- **The optimal incentive-compatible contract is not on the contract curve** (O&R p. 406):
the types' marginal rates of substitution differ at the optimum. -/
theorem opt_off_contract_curve (e : Endowments) :
    (e.avg - optP₂ e) * (e.lo + optP₁ e) ≠ (e.avg + optP₂ e) * (e.hi - optP₁ e) := by
  obtain ⟨h1, _⟩ := opt_northwest_of_C e
  intro heq
  have heq' : (e.avg + e.avg * optP₁ e / e.hi) * (e.lo + optP₁ e) =
      (e.avg - e.avg * optP₁ e / e.hi) * (e.hi - optP₁ e) := by
    unfold optP₂ at heq
    have a : e.avg - -(e.avg * optP₁ e / e.hi) = e.avg + e.avg * optP₁ e / e.hi := by ring
    have b : e.avg + -(e.avg * optP₁ e / e.hi) = e.avg - e.avg * optP₁ e / e.hi := by ring
    rw [a, b] at heq
    exact heq
  have := (contract_curve_on_icH_line_iff e (optP₁ e)).1 heq'
  linarith

/-- The optimal contract strictly beats `C`, `B` and autarky `A` in expected utility
(O&R p. 406: `C` is not the best that can be done). -/
theorem opt_beats_C_B_A (e : Endowments) :
    EU e (contractCP₁ e) (contractCP₂ e) < EU e (optP₁ e) (optP₂ e) ∧
      EU e (bondP₁ e) (bondP₂ e) < EU e (optP₁ e) (optP₂ e) ∧
      EU e 0 0 < EU e (optP₁ e) (optP₂ e) := by
  have hC : EU e (contractCP₁ e) (contractCP₂ e) < EU e (optP₁ e) (optP₂ e) :=
    opt_strictly_best (contractC_feasible e) (contractC_ic e).1
      (Or.inl (opt_northwest_of_C e).1.ne)
  have hB := eu_bond_lt_contractC e
  have hA := eu_autarky_lt_bond e
  exact ⟨hC, hB.trans hC, hA.trans (hB.trans hC)⟩

/-! ## The revelation principle (fn 59)

A general mechanism lets each country send any message `m` from an arbitrary set `M` and pays
it the net transfers `(t₁ m, t₂ m)`. A message giving nonpositive consumption is unavailable to
that type. In an equilibrium each type picks a best available message and transfers balance
across the two (equal-mass) types. -/

/-- A general (not necessarily direct) mechanism with message space `M`, O&R fn 59. -/
structure Mechanism (M : Type) where
  t₁ : M → ℝ
  t₂ : M → ℝ

/-- Message `m` is available to a type with date-1 output `y₁`: consumption stays positive. -/
def Mechanism.Available {M : Type} (mech : Mechanism M) (e : Endowments) (y₁ : ℝ) (m : M) :
    Prop :=
  0 < y₁ + mech.t₁ m ∧ 0 < e.avg + mech.t₂ m

/-- Utility of a type with date-1 output `y₁` sending message `m`. -/
noncomputable def Mechanism.payoff {M : Type} (mech : Mechanism M) (e : Endowments) (y₁ : ℝ)
    (m : M) : ℝ :=
  lifetimeU (y₁ + mech.t₁ m) (e.avg + mech.t₂ m)

/-- An equilibrium of a mechanism: type `H` sends `mH`, type `L` sends `mL`, each optimally
among available messages, and transfers balance (half the countries are of each type). -/
def Mechanism.IsEquilibrium {M : Type} (mech : Mechanism M) (e : Endowments) (mH mL : M) :
    Prop :=
  mech.Available e e.hi mH ∧ mech.Available e e.lo mL ∧
    (∀ m, mech.Available e e.hi m → mech.payoff e e.hi m ≤ mech.payoff e e.hi mH) ∧
    (∀ m, mech.Available e e.lo m → mech.payoff e e.lo m ≤ mech.payoff e e.lo mL) ∧
    mech.t₁ mH + mech.t₁ mL = 0 ∧ mech.t₂ mH + mech.t₂ mL = 0

/-- **Revelation principle** (O&R fn 59, Myerson 1979): the outcome of any equilibrium of any
mechanism is the outcome of a feasible direct contract satisfying (41) and (42), with the same
expected utility. -/
theorem revelation_principle {M : Type} (mech : Mechanism M) (e : Endowments) {mH mL : M}
    (heq : mech.IsEquilibrium e mH mL) :
    Feasible e (-mech.t₁ mH) (-mech.t₂ mH) ∧ ICH e (-mech.t₁ mH) (-mech.t₂ mH) ∧
      ICL e (-mech.t₁ mH) (-mech.t₂ mH) ∧
      (mech.payoff e e.hi mH + mech.payoff e e.lo mL) / 2 =
        EU e (-mech.t₁ mH) (-mech.t₂ mH) := by
  obtain ⟨⟨aH1, aH2⟩, ⟨aL1, aL2⟩, bH, bL, s1, s2⟩ := heq
  have tL1 : mech.t₁ mL = -mech.t₁ mH := by linarith
  have tL2 : mech.t₂ mL = -mech.t₂ mH := by linarith
  have hf : Feasible e (-mech.t₁ mH) (-mech.t₂ mH) := by
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · rw [tL1] at aL1; linarith
    · rw [tL2] at aL2; linarith
  refine ⟨hf, ?_, ?_, ?_⟩
  · -- `H` could send `mL`
    have avail : mech.Available e e.hi mL := by
      refine ⟨?_, aL2⟩
      have := e.lo_lt_hi; linarith
    have := bH mL avail
    unfold Mechanism.payoff at this
    unfold ICH
    rw [tL1, tL2] at this
    simpa [sub_eq_add_neg] using this
  · -- `L` could send `mH` whenever that is available to it
    intro hp
    have avail : mech.Available e e.lo mH := ⟨by linarith, aH2⟩
    have := bL mH avail
    unfold Mechanism.payoff at this
    rw [tL1, tL2] at this
    simpa [sub_eq_add_neg] using this
  · unfold Mechanism.payoff EU
    rw [tL1, tL2]
    simp [sub_eq_add_neg]

/-- No mechanism does better than the optimal incentive-compatible contract (O&R fn 59): so
restricting attention to truthful direct contracts is without loss. -/
theorem no_mechanism_beats_optimal_contract {M : Type} (mech : Mechanism M) (e : Endowments)
    {mH mL : M} (heq : mech.IsEquilibrium e mH mL) :
    (mech.payoff e e.hi mH + mech.payoff e e.lo mL) / 2 ≤ EU e (optP₁ e) (optP₂ e) := by
  obtain ⟨hf, hH, _, hval⟩ := revelation_principle mech e heq
  rw [hval]
  exact opt_is_max hf hH

/-! ## Ex post bond trade undoes incentive contracts (p. 406) -/

/-- The best lifetime utility attainable with present-value wealth `W` when borrowing and
lending are free at `r = 0`: `2 log(W/2)` (consume `W/2` on each date), O&R p. 406. -/
noncomputable def bondValue (W : ℝ) : ℝ := 2 * Real.log (W / 2)

/-- With free borrowing and lending at `r = 0`, any plan `(c₁, W − c₁)` gives at most
`bondValue W`, with equality iff `c₁ = W/2`, O&R p. 406. -/
theorem bond_smoothing {W c₁ : ℝ} (hc : 0 < c₁) (hcW : c₁ < W) :
    lifetimeU c₁ (W - c₁) ≤ bondValue W ∧ (lifetimeU c₁ (W - c₁) = bondValue W → c₁ = W / 2) := by
  have hW : 0 < W - c₁ := by linarith
  have hmean : (c₁ + (W - c₁)) / 2 = W / 2 := by ring
  unfold lifetimeU bondValue
  refine ⟨?_, ?_⟩
  · have := log_add_log_le_two_log_mean hc hW
    rwa [hmean] at this
  · intro heq
    by_contra hne
    have := log_add_log_lt_two_log_mean hc hW (by intro h; apply hne; linarith)
    rw [hmean] at this
    linarith

/-- `bondValue` is attained at `c₁ = W/2`. -/
theorem bondValue_attained (W : ℝ) : lifetimeU (W / 2) (W - W / 2) = bondValue W := by
  unfold lifetimeU bondValue
  rw [show W - W / 2 = W / 2 by ring]
  ring

/-- Incentive compatibility for type `H` when it can borrow and lend freely after reporting,
O&R p. 406: every consumption plan financed by lying (present value `Ȳ + Y + P₁ + P₂`) is no
better than the best truthful plan (present value `Ȳ + Y − P₁ − P₂`). -/
def ICHbonds (e : Endowments) (P₁ P₂ : ℝ) : Prop :=
  ∀ c₁, 0 < c₁ → c₁ < e.hi + e.avg + P₁ + P₂ →
    lifetimeU c₁ (e.hi + e.avg + P₁ + P₂ - c₁) ≤ bondValue (e.hi + e.avg - P₁ - P₂)

/-- Incentive compatibility for type `L` with free ex post borrowing and lending, O&R p. 406. -/
def ICLbonds (e : Endowments) (P₁ P₂ : ℝ) : Prop :=
  ∀ c₁, 0 < c₁ → c₁ < e.lo + e.avg - P₁ - P₂ →
    lifetimeU c₁ (e.lo + e.avg - P₁ - P₂ - c₁) ≤ bondValue (e.lo + e.avg + P₁ + P₂)

/-- A type's incentive constraint with ex post bond trade holds iff lying does not raise the
present value of its receipts (utility depends only on present value), O&R p. 406. -/
theorem ic_bonds_iff_pv {Wtruth Wlie : ℝ} (hT : 0 < Wtruth) :
    (∀ c₁, 0 < c₁ → c₁ < Wlie → lifetimeU c₁ (Wlie - c₁) ≤ bondValue Wtruth) ↔ Wlie ≤ Wtruth := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hWl : 0 < Wlie := hT.trans hlt
    have := h (Wlie / 2) (by linarith) (by linarith)
    rw [bondValue_attained] at this
    unfold bondValue at this
    have : Real.log (Wtruth / 2) < Real.log (Wlie / 2) :=
      Real.log_lt_log (by linarith) (by linarith)
    linarith
  · intro h c₁ hc hcW
    have := (bond_smoothing hc hcW).1
    refine this.trans ?_
    unfold bondValue
    have hWl : 0 < Wlie := hc.trans hcW
    have : Real.log (Wlie / 2) ≤ Real.log (Wtruth / 2) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith

/-- With ex post bond trade, (41) holds iff `P₁ + P₂ ≤ 0`, O&R p. 406. -/
theorem icHbonds_iff {e : Endowments} {P₁ P₂ : ℝ} (hT : 0 < e.hi + e.avg - P₁ - P₂) :
    ICHbonds e P₁ P₂ ↔ P₁ + P₂ ≤ 0 := by
  unfold ICHbonds
  rw [ic_bonds_iff_pv hT]
  constructor <;> intro h <;> linarith

/-- With ex post bond trade, (42) holds iff `P₁ + P₂ ≥ 0`, O&R p. 406. -/
theorem icLbonds_iff {e : Endowments} {P₁ P₂ : ℝ} (hT : 0 < e.lo + e.avg + P₁ + P₂) :
    ICLbonds e P₁ P₂ ↔ 0 ≤ P₁ + P₂ := by
  unfold ICLbonds
  rw [ic_bonds_iff_pv hT]
  constructor <;> intro h <;> linarith

/-- **Ex post bond trade forces zero net present value** (O&R p. 406): both incentive
constraints hold iff `P₁ + P₂ = 0`, so every type's wealth is its autarky wealth. -/
theorem bond_trade_ic_iff_zero_npv {e : Endowments} {P₁ P₂ : ℝ}
    (hH : 0 < e.hi + e.avg - P₁ - P₂) (hL : 0 < e.lo + e.avg + P₁ + P₂) :
    (ICHbonds e P₁ P₂ ∧ ICLbonds e P₁ P₂) ↔ P₁ + P₂ = 0 := by
  rw [icHbonds_iff hH, icLbonds_iff hL]
  constructor
  · rintro ⟨a, b⟩; linarith
  · intro h; exact ⟨h.le, h.ge⟩

/-- **With ex post bond trade the best the market can do is `B`** (O&R p. 406): under any
incentive-compatible contract each type's best attainable utility equals its utility at `B`,
so ex ante welfare equals that of `B`. -/
theorem bond_trade_best_is_B {e : Endowments} {P₁ P₂ : ℝ}
    (hH : 0 < e.hi + e.avg - P₁ - P₂) (hL : 0 < e.lo + e.avg + P₁ + P₂)
    (hic : ICHbonds e P₁ P₂ ∧ ICLbonds e P₁ P₂) :
    bondValue (e.hi + e.avg - P₁ - P₂) = lifetimeU (e.hi - bondP₁ e) (e.avg - bondP₂ e) ∧
      bondValue (e.lo + e.avg + P₁ + P₂) = lifetimeU (e.lo + bondP₁ e) (e.avg + bondP₂ e) ∧
      (bondValue (e.hi + e.avg - P₁ - P₂) + bondValue (e.lo + e.avg + P₁ + P₂)) / 2 =
        EU e (bondP₁ e) (bondP₂ e) := by
  have h0 := (bond_trade_ic_iff_zero_npv hH hL).1 hic
  obtain ⟨b1, b2, b3, b4⟩ := bond_B_consumption e
  have e1 : e.hi + e.avg - P₁ - P₂ = e.hi + e.avg := by linarith
  have e2 : e.lo + e.avg + P₁ + P₂ = e.lo + e.avg := by linarith
  have v1 : bondValue (e.hi + e.avg - P₁ - P₂) =
      lifetimeU (e.hi - bondP₁ e) (e.avg - bondP₂ e) := by
    rw [e1, b1, b2]; unfold bondValue lifetimeU; ring
  have v2 : bondValue (e.lo + e.avg + P₁ + P₂) =
      lifetimeU (e.lo + bondP₁ e) (e.avg + bondP₂ e) := by
    rw [e2, b3, b4]; unfold bondValue lifetimeU; ring
  refine ⟨v1, v2, ?_⟩
  rw [v1, v2]
  rfl

/-- **Point `C″`** (O&R p. 406): under contract (43) a type-`H` country that claims to be poor
and then smooths by lending consumes `(Ȳ² + Y²)/(Ȳ + Y)` on each date, strictly more than its
truthful `2ȲY/(Ȳ + Y)`; so (41) fails once ex post bond trade is possible. -/
theorem contractC_bond_deviation (e : Endowments) :
    (e.hi + e.avg + contractCP₁ e + contractCP₂ e) / 2 =
        (e.hi ^ 2 + e.avg ^ 2) / (e.hi + e.avg) ∧
      2 * e.hi * e.avg / (e.hi + e.avg) < (e.hi ^ 2 + e.avg ^ 2) / (e.hi + e.avg) ∧
      ¬ ICHbonds e (contractCP₁ e) (contractCP₂ e) := by
  obtain ⟨hnpv, hpos, _⟩ := contractC_npv_transfer e
  have hs : 0 < e.hi + e.avg := add_pos e.hi_pos e.avg_pos
  have hd : 0 < e.hi - e.avg := by linarith [e.avg_lt_hi]
  refine ⟨?_, ?_, ?_⟩
  · rw [add_assoc, hnpv]; field_simp; ring
  · apply div_lt_div_of_pos_right _ hs
    nlinarith
  · have hT : 0 < e.hi + e.avg - contractCP₁ e - contractCP₂ e := by
      have : e.hi + e.avg - contractCP₁ e - contractCP₂ e =
          4 * e.hi * e.avg / (e.hi + e.avg) := by
        rw [sub_sub, hnpv]; field_simp; ring
      rw [this]; have := e.hi_pos; have := e.avg_pos; positivity
    rw [icHbonds_iff hT]
    linarith

end ObstfeldRogoff.CapitalMarketImperfections.HiddenInformation
