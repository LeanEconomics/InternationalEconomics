/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceModels.ReduxMoneyShocks
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The redux model: welfare

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.1.7.1 (p. 674),
§10.1.8.2 (pp. 684–686), §10.1.9 (pp. 686–688), §10.1.10 (pp. 688–689) and Exercise 3
(p. 713). The equiproportionate shock of §10.1.8.1 (T19) is in `ReduxMoneyShocks`.

* **(75) as a genuine derivative (T17).** Lifetime utility is an infinite discounted sum
  (`lifetimeWelfare`, a `tsum`); along the post-shock path, which is at its new steady state from
  date 2 on, it equals date-1 utility plus `β/(1−β) = 1/δ` times the long-run period utility
  (`lifetimeWelfare_twoRegime`). Its derivative in the direction of any log-deviations is
  `c + χ(m − p) − κȳ₀² y + (1/δ)[c̄ + χ(m̄ − p̄) − κȳ₀² ȳ]` (`welfare_hasDerivAt`), and with
  `κȳ₀² = (θ−1)/θ` the real part is exactly (75) (`welfare_eq75`).
* **(76) (T17).** The quasi-reduced forms of p. 685 hold for every money-shock equilibrium
  (`quasi_reduced_forms`); every term in `e` cancels IDENTICALLY (`welfare_e_cancels`), so
  `dUᴿ = cᵂ/θ = mᵂ/θ` for Home AND for Foreign (`welfare_eq76`), and this is the derivative of
  `Uᴿ` along the equilibrium response (`welfare_eq76_hasDerivAt`).
* **"As long as χ is not too large" made exact (T18, p. 684, fn 19).** For a Foreign expansion
  the total first-order change in Home utility, real balances included, is
  `(1−n)m*[(δ(1+θ)+2) + χ(δ(1+θ)+2θ+1−θ²)]/D` (`foreign_shock_total`). It is positive for EVERY
  `χ ≥ 0` iff `θ² − 2θ − 1 ≤ δ(1+θ)` (e.g. whenever `θ ≤ 1 + √2`); otherwise it is positive iff
  `χ < (δ(1+θ)+2)/(θ² − 2θ − 1 − δ(1+θ))`. Counterexample to the unconditional reading:
  `θ = 6`, `δ = 0.05`, `χ = 0.2` (threshold `≈ 0.104`): a Foreign expansion LOWERS Home welfare
  (`counterexample_theta6`). fn 19's real-balance claims are proved (`home_shock_real_balances`,
  `foreign_shock_real_balances`).
* **Menu costs and demand-determined output (T20, p. 674).** The producer's payoff is strictly
  concave in output; the gain from re-optimising at a preset price is at most
  `(marginal payoff)²/(2κ)`, hence SECOND order in the shock, so any menu cost `Z > 0` deters
  adjustment for all small enough shocks (`menu_cost_second_order`, `menu_cost_rationale`).
  Meeting demand at a preset price is optimal IFF price covers marginal cost
  (`meet_demand_iff`); at the initial steady state it does so strictly (markup `θ/(θ−1)`).
* **Income taxes (77)–(81) (T21).** Rebated taxes leave the budget (8) and the log-linear
  labour condition unchanged; (80); the welfare effect (81) of a Foreign expansion, with the exact
  sign condition `dUᴿ < 0 ⟺ τ(θ−1)² > δ(1+θ)+2` and "for large enough θ" made precise.
* **Small country (T22, p. 688).** As `n → 0` a Home expansion has no world effects and no welfare
  effect, while `y → θe`.
* **Exercise 3.** The small open economy directly: the nonlinear steady state exists and is unique
  for every `B̄`; the linear model has exactly one solution, which is (65)–(67) with `n = 0`,
  `m* = 0`, and its welfare effect is exactly zero.
-/

namespace ObstfeldRogoff.StickyPriceModels.ReduxWelfare

open Real Filter Topology ReduxPrimitives ReduxLogLinear ReduxSteadyState ReduxMoneyShocks

/-- The linear-model parameters `(θ, δ, n)` of a nonlinear parameter set (O&R §10.1.5, p. 669):
the log-linearisation is taken at the symmetric steady state of `M`. -/
noncomputable def linearOf (M : ReduxParams) : ReduxLinear :=
  ⟨M.θ, M.δ, M.n, M.hθ, M.δ_pos, M.hn0, M.hn1⟩

/-! ## Lifetime utility along a path that reaches its steady state at date 2 -/

/-- A two-regime path (O&R p. 675: "the economy reaches its long-run equilibrium in just one
period"): value `a` at the shock date (index 0 = the book's date 1), value `b` from then on. -/
def twoRegime (a b : ℝ) (s : ℕ) : ℝ := if s = 0 then a else b

/-- **Discounted sum of a two-regime path** (O&R p. 684, "the new steady state is reached after
just one period"): for `0 ≤ β < 1`, `Σ_{s≥0} β^s x_s = a + (β/(1−β)) b`. -/
theorem hasSum_twoRegime {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (a b : ℝ) :
    HasSum (fun s => β ^ s * twoRegime a b s) (a + β / (1 - β) * b) := by
  have h1 := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right b
  have h2 : HasSum (fun s : ℕ => if s = 0 then a - b else 0) (a - b) := hasSum_ite_eq 0 (a - b)
  have h := h1.add h2
  have hne : 1 - β ≠ 0 := by linarith
  convert h using 1
  · funext s
    unfold twoRegime
    split_ifs with hs
    · subst hs; ring
    · ring
  · field_simp; ring

/-- `β/(1−β) = 1/δ` with `δ = (1−β)/β` (O&R (19) and p. 684: `Σ_{s≥t+1} β^{s−t} = 1/δ`). -/
theorem beta_div_one_sub (M : ReduxParams) : M.β / (1 - M.β) = 1 / M.δ := by
  have h0 := M.hβ0
  have h1 : 1 - M.β ≠ 0 := by linarith [M.hβ1]
  unfold ReduxParams.δ timePreferenceRate
  field_simp

/-- The period utility (1), O&R p. 661, with a possibly shocked effort weight `κ`:
`log C + χ log(M/P) − (κ/2) y²`. -/
noncomputable def periodWelfare (χ κ C k y : ℝ) : ℝ := Real.log C + χ * Real.log k - κ / 2 * y ^ 2

/-- Lifetime utility (1), O&R p. 661, as a genuine infinite sum from the shock date:
`Σ_{s≥0} β^s [log C_s + χ log(M_s/P_s) − (κ/2) y_s²]`. -/
noncomputable def lifetimeWelfare (β χ κ : ℝ) (C k y : ℕ → ℝ) : ℝ :=
  ∑' s, β ^ s * periodWelfare χ κ (C s) (k s) (y s)

/-- The "real" component of utility, O&R p. 684: `Uᴿ = Σ_{s≥0} β^s [log C_s − (κ/2) y_s²]`. -/
noncomputable def realWelfare (β κ : ℝ) (C y : ℕ → ℝ) : ℝ :=
  ∑' s, β ^ s * (Real.log (C s) - κ / 2 * y s ^ 2)

/-- `Uᴿ` is lifetime utility with `χ = 0` (O&R p. 684). -/
theorem realWelfare_eq (β κ : ℝ) (C y : ℕ → ℝ) :
    realWelfare β κ C y = lifetimeWelfare β 0 κ C (fun _ => 1) y := by
  unfold realWelfare lifetimeWelfare periodWelfare
  simp

/-- **Lifetime utility along a two-regime path** (O&R p. 684): it is date-1 utility plus
`β/(1−β)` times long-run period utility (the sum is genuinely infinite and summable). -/
theorem lifetimeWelfare_twoRegime {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (χ κ C1 Cb k1 kb y1 yb : ℝ) :
    lifetimeWelfare β χ κ (twoRegime C1 Cb) (twoRegime k1 kb) (twoRegime y1 yb) =
      periodWelfare χ κ C1 k1 y1 + β / (1 - β) * periodWelfare χ κ Cb kb yb := by
  have h := hasSum_twoRegime hβ0 hβ1 (periodWelfare χ κ C1 k1 y1) (periodWelfare χ κ Cb kb yb)
  rw [← h.tsum_eq]
  unfold lifetimeWelfare
  congr 1
  funext s
  unfold twoRegime
  split_ifs <;> rfl

/-- The derivative of `τ ↦ log(A e^{τx})` is `x` (log-deviations, O&R §10.1.5). -/
theorem hasDerivAt_log_exp_path {A x : ℝ} (hA : 0 < A) :
    HasDerivAt (fun τ => Real.log (A * Real.exp (τ * x))) x 0 := by
  have e : (fun τ => Real.log (A * Real.exp (τ * x))) = fun τ => Real.log A + τ * x := by
    funext τ
    rw [Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [e]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const x).const_add (Real.log A)

/-- **Differentiating period utility** (O&R p. 684, and p. 696 for the productivity term): along
`C = C₀e^{τc}`, `M/P = k₀e^{τm}`, `y = Y₀e^{τŷ}` and effort weight `κ = κ₀(1 − τa)`
(`a = −dκ/κ₀`, O&R p. 696), the derivative of period utility at `τ = 0` is
`c + χm − κ₀Y₀²ŷ + κ₀Y₀²a/2`. -/
theorem hasDerivAt_periodWelfare (χ κ0 a : ℝ) {C0 k0 : ℝ} (Y0 c m y : ℝ) (hC0 : 0 < C0)
    (hk0 : 0 < k0) :
    HasDerivAt (fun τ => periodWelfare χ (κ0 * (1 - τ * a)) (C0 * Real.exp (τ * c))
      (k0 * Real.exp (τ * m)) (Y0 * Real.exp (τ * y)))
      (c + χ * m - κ0 * Y0 ^ 2 * y + κ0 * Y0 ^ 2 * a / 2) 0 := by
  have h1 := hasDerivAt_log_exp_path (x := c) hC0
  have h2 := (hasDerivAt_log_exp_path (x := m) hk0).const_mul χ
  have h3 : HasDerivAt (fun τ => κ0 * (1 - τ * a) / 2) (κ0 * (-a) / 2) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const a).const_sub 1).const_mul κ0
    simpa using this.div_const 2
  have h4 : HasDerivAt (fun τ => (Y0 * Real.exp (τ * y)) ^ 2) (2 * (Y0 * (Y0 * y))) 0 := by
    have hY : HasDerivAt (fun τ => Y0 * Real.exp (τ * y)) (Y0 * y) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const y).exp.const_mul Y0
    convert hY.mul hY using 1
    · funext τ; simp only [Pi.mul_apply]; ring
    · simp only [zero_mul, Real.exp_zero]; ring
  have h := (h1.add h2).sub (h3.mul h4)
  convert h using 1
  · funext τ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, periodWelfare]
  · simp only [zero_mul, Real.exp_zero, mul_one, sub_zero]
    ring

/-- **The derivative of lifetime utility** (T17; O&R p. 684): for a path at its new steady state
from date 2 (a two-regime path) with log-deviations `c, c̄` (consumption), `m, m̄` (real
balances), `ŷ, ȳ` (output) and a permanent effort-weight shock `κ = κ₀(1 − τa)`, the derivative
of the infinite sum `Σ β^s u_s` at `τ = 0` is `[c + χm − κ₀Y₀²ŷ + κ₀Y₀²a/2] +
(β/(1−β))[c̄ + χm̄ − κ₀Y₀²ȳ + κ₀Y₀²a/2]`. -/
theorem welfare_hasDerivAt {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (χ κ0 a : ℝ) {C0 k0 kb0 : ℝ}
    (Y0 c cb m mb y yb : ℝ) (hC0 : 0 < C0) (hk0 : 0 < k0) (hkb0 : 0 < kb0) :
    HasDerivAt (fun τ => lifetimeWelfare β χ (κ0 * (1 - τ * a))
      (twoRegime (C0 * Real.exp (τ * c)) (C0 * Real.exp (τ * cb)))
      (twoRegime (k0 * Real.exp (τ * m)) (kb0 * Real.exp (τ * mb)))
      (twoRegime (Y0 * Real.exp (τ * y)) (Y0 * Real.exp (τ * yb))))
      ((c + χ * m - κ0 * Y0 ^ 2 * y + κ0 * Y0 ^ 2 * a / 2) +
        β / (1 - β) * (cb + χ * mb - κ0 * Y0 ^ 2 * yb + κ0 * Y0 ^ 2 * a / 2)) 0 := by
  have e : (fun τ => lifetimeWelfare β χ (κ0 * (1 - τ * a))
      (twoRegime (C0 * Real.exp (τ * c)) (C0 * Real.exp (τ * cb)))
      (twoRegime (k0 * Real.exp (τ * m)) (kb0 * Real.exp (τ * mb)))
      (twoRegime (Y0 * Real.exp (τ * y)) (Y0 * Real.exp (τ * yb)))) =
      fun τ => periodWelfare χ (κ0 * (1 - τ * a)) (C0 * Real.exp (τ * c))
        (k0 * Real.exp (τ * m)) (Y0 * Real.exp (τ * y)) + β / (1 - β) *
        periodWelfare χ (κ0 * (1 - τ * a)) (C0 * Real.exp (τ * cb))
          (kb0 * Real.exp (τ * mb)) (Y0 * Real.exp (τ * yb)) := by
    funext τ
    exact lifetimeWelfare_twoRegime hβ0 hβ1 _ _ _ _ _ _ _ _
  rw [e]
  exact (hasDerivAt_periodWelfare χ κ0 a Y0 c m y hC0 hk0).add
    ((hasDerivAt_periodWelfare χ κ0 a Y0 cb mb yb hC0 hkb0).const_mul _)

/-- The first-order change in real utility, the right side of (75), O&R p. 684:
`dUᴿ = c − ((θ−1)/θ) y + (1/δ)[c̄ − ((θ−1)/θ) ȳ]`. -/
noncomputable def dUR (L : ReduxLinear) (c y cb yb : ℝ) : ℝ :=
  c - (L.θ - 1) / L.θ * y + 1 / L.δ * (cb - (L.θ - 1) / L.θ * yb)

/-- **(75) is the derivative of `Uᴿ`** (T17; O&R p. 684): around the symmetric steady state
`C̄₀ = ȳ₀`, along log-deviations `c, ŷ` on impact and `c̄, ȳ` from date 2, the derivative of
`Uᴿ = Σ β^s [log C_s − (κ/2)y_s²]` is `c − ((θ−1)/θ)ŷ + (1/δ)[c̄ − ((θ−1)/θ)ȳ]`, using
`Σ_{s≥1} β^s = 1/δ` and `κȳ₀² = (θ−1)/θ` (24). -/
theorem welfare_eq75 (M : ReduxParams) (c y cb yb : ℝ) :
    HasDerivAt (fun τ => realWelfare M.β M.κ
      (twoRegime (M.ybar0 * Real.exp (τ * c)) (M.ybar0 * Real.exp (τ * cb)))
      (twoRegime (M.ybar0 * Real.exp (τ * y)) (M.ybar0 * Real.exp (τ * yb))))
      (dUR (linearOf M) c y cb yb) 0 := by
  have h := welfare_hasDerivAt M.hβ0.le M.hβ1 0 M.κ 0 M.ybar0 c cb 0 0 y yb M.ybar0_pos one_pos
    one_pos
  have e : (fun τ => realWelfare M.β M.κ
      (twoRegime (M.ybar0 * Real.exp (τ * c)) (M.ybar0 * Real.exp (τ * cb)))
      (twoRegime (M.ybar0 * Real.exp (τ * y)) (M.ybar0 * Real.exp (τ * yb)))) =
      fun τ => lifetimeWelfare M.β 0 (M.κ * (1 - τ * 0))
      (twoRegime (M.ybar0 * Real.exp (τ * c)) (M.ybar0 * Real.exp (τ * cb)))
      (twoRegime (1 * Real.exp (τ * 0)) (1 * Real.exp (τ * 0)))
      (twoRegime (M.ybar0 * Real.exp (τ * y)) (M.ybar0 * Real.exp (τ * yb))) := by
    funext τ
    rw [realWelfare_eq]
    unfold lifetimeWelfare periodWelfare
    simp
  rw [e]
  convert h using 1
  unfold dUR linearOf
  simp only
  rw [beta_div_one_sub M, M.κ_mul_ybar0_sq]
  ring

/-- The real-balance component of the first-order utility change (O&R p. 684 and fn 19):
`χ[x + x̄/δ]`, where `x = m − p` is the impact log-deviation of real balances and `x̄ = m̄ − p̄`
the long-run one. -/
noncomputable def realBalanceTerm (L : ReduxLinear) (χ x xb : ℝ) : ℝ := χ * (x + 1 / L.δ * xb)

/-- **The total first-order utility change** (T17–T18; O&R p. 684): around the symmetric steady
state, the derivative of TOTAL lifetime utility (1), real balances included, along impact
log-deviations `c, x, ŷ` and long-run `c̄, x̄, ȳ` is `dUᴿ + χ[x + x̄/δ]`. -/
theorem total_welfare_hasDerivAt (M : ReduxParams) {k0 kb0 : ℝ} (c cb x xb y yb : ℝ)
    (hk0 : 0 < k0) (hkb0 : 0 < kb0) :
    HasDerivAt (fun τ => lifetimeWelfare M.β M.χ M.κ
      (twoRegime (M.ybar0 * Real.exp (τ * c)) (M.ybar0 * Real.exp (τ * cb)))
      (twoRegime (k0 * Real.exp (τ * x)) (kb0 * Real.exp (τ * xb)))
      (twoRegime (M.ybar0 * Real.exp (τ * y)) (M.ybar0 * Real.exp (τ * yb))))
      (dUR (linearOf M) c y cb yb + realBalanceTerm (linearOf M) M.χ x xb) 0 := by
  have h := welfare_hasDerivAt M.hβ0.le M.hβ1 M.χ M.κ 0 M.ybar0 c cb x xb y yb M.ybar0_pos hk0
    hkb0
  have e : (fun τ => lifetimeWelfare M.β M.χ M.κ
      (twoRegime (M.ybar0 * Real.exp (τ * c)) (M.ybar0 * Real.exp (τ * cb)))
      (twoRegime (k0 * Real.exp (τ * x)) (kb0 * Real.exp (τ * xb)))
      (twoRegime (M.ybar0 * Real.exp (τ * y)) (M.ybar0 * Real.exp (τ * yb)))) =
      fun τ => lifetimeWelfare M.β M.χ (M.κ * (1 - τ * 0))
      (twoRegime (M.ybar0 * Real.exp (τ * c)) (M.ybar0 * Real.exp (τ * cb)))
      (twoRegime (k0 * Real.exp (τ * x)) (kb0 * Real.exp (τ * xb)))
      (twoRegime (M.ybar0 * Real.exp (τ * y)) (M.ybar0 * Real.exp (τ * yb))) := by
    funext τ; simp
  rw [e]
  convert h using 1
  unfold dUR realBalanceTerm linearOf
  simp only
  rw [beta_div_one_sub M, M.κ_mul_ybar0_sq]
  ring

/-! ## (76): the welfare effect of money shocks is `mᵂ/θ` (T17) -/

/-- **The quasi-reduced forms**, O&R p. 685: in every money-shock equilibrium
`y = mᵂ + (1−n)θe`, `c = δ(1−n)(θ²−1)e/(δ(1+θ)+2θ) + mᵂ`,
`c̄ = δ(1−n)(θ²−1)e/(δ(1+θ)+2θ)` and `ȳ = −δθ(1−n)(θ−1)e/(δ(1+θ)+2θ)`. -/
theorem quasi_reduced_forms {L : ReduxLinear} {m ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L m ms u v) :
    u.y = L.n * m + (1 - L.n) * ms + (1 - L.n) * L.θ * u.e ∧
    u.c = L.δ * (1 - L.n) * (L.θ ^ 2 - 1) / (L.δ * (1 + L.θ) + 2 * L.θ) * u.e +
      (L.n * m + (1 - L.n) * ms) ∧
    v.c = L.δ * (1 - L.n) * (L.θ ^ 2 - 1) / (L.δ * (1 + L.θ) + 2 * L.θ) * u.e ∧
    v.y = -(L.δ * L.θ * (1 - L.n) * (L.θ - 1) / (L.δ * (1 + L.θ) + 2 * L.θ)) * u.e := by
  obtain ⟨rfl, rfl⟩ := (moneyShock_iff L m ms u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hG : L.δ * (1 + L.θ) + 2 * L.θ ≠ 0 := by nlinarith
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [shortRunSolution, steadySolution, ReduxLinear.D, ReduxLinear.E] <;>
    field_simp <;> ring

/-- **Every exchange-rate term cancels, identically** (O&R p. 685): substituting the quasi-reduced
forms into (75) gives `mᵂ/θ` for EVERY value of `e`. -/
theorem welfare_e_cancels (L : ReduxLinear) (e mW : ℝ) :
    dUR L (L.δ * (1 - L.n) * (L.θ ^ 2 - 1) / (L.δ * (1 + L.θ) + 2 * L.θ) * e + mW)
      (mW + (1 - L.n) * L.θ * e)
      (L.δ * (1 - L.n) * (L.θ ^ 2 - 1) / (L.δ * (1 + L.θ) + 2 * L.θ) * e)
      (-(L.δ * L.θ * (1 - L.n) * (L.θ - 1) / (L.δ * (1 + L.θ) + 2 * L.θ)) * e) = mW / L.θ := by
  have hθ := L.hθ
  have hδ := L.hδ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hδ0 : L.δ ≠ 0 := hδ.ne'
  have hG : L.δ * (1 + L.θ) + 2 * L.θ ≠ 0 := by nlinarith
  unfold dUR
  field_simp
  ring

/-- **(76)**, O&R p. 685 (T17): in every money-shock equilibrium the first-order change in Home
real utility is `dUᴿ = cᵂ/θ = mᵂ/θ`, and so is Foreign's ("regardless of its origin"). -/
theorem welfare_eq76 {L : ReduxLinear} {m ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L m ms u v) :
    dUR L u.c u.y v.c v.y = (L.n * m + (1 - L.n) * ms) / L.θ ∧
    dUR L u.cs u.ys v.cs v.ys = (L.n * m + (1 - L.n) * ms) / L.θ ∧
    dUR L u.c u.y v.c v.y = u.cW / L.θ := by
  have hcW := (moneyShock_world h).2.1
  obtain ⟨rfl, rfl⟩ := (moneyShock_iff L m ms u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hδ0 : L.δ ≠ 0 := hδ.ne'
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  refine ⟨?_, ?_, ?_⟩
  · simp only [dUR, shortRunSolution, steadySolution, ReduxLinear.D, ReduxLinear.E]
    field_simp; ring
  · simp only [dUR, shortRunSolution, steadySolution, ReduxLinear.D, ReduxLinear.E]
    field_simp; ring
  · rw [hcW]
    simp only [dUR, shortRunSolution, steadySolution, ReduxLinear.D, ReduxLinear.E]
    field_simp; ring

/-- **(76) as a derivative** (T17): in the nonlinear model, real utility `Uᴿ` along the
equilibrium response to a money shock (impact `c, ŷ`, long run `c̄, ȳ` from the unique solution
of the linear system) has derivative `mᵂ/θ` at the initial steady state, for Home and Foreign. -/
theorem welfare_eq76_hasDerivAt (M : ReduxParams) {m ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm (linearOf M) m ms u v) :
    HasDerivAt (fun τ => realWelfare M.β M.κ
      (twoRegime (M.ybar0 * Real.exp (τ * u.c)) (M.ybar0 * Real.exp (τ * v.c)))
      (twoRegime (M.ybar0 * Real.exp (τ * u.y)) (M.ybar0 * Real.exp (τ * v.y))))
      ((M.n * m + (1 - M.n) * ms) / M.θ) 0 ∧
    HasDerivAt (fun τ => realWelfare M.β M.κ
      (twoRegime (M.ybar0 * Real.exp (τ * u.cs)) (M.ybar0 * Real.exp (τ * v.cs)))
      (twoRegime (M.ybar0 * Real.exp (τ * u.ys)) (M.ybar0 * Real.exp (τ * v.ys))))
      ((M.n * m + (1 - M.n) * ms) / M.θ) 0 := by
  obtain ⟨h1, h2, -⟩ := welfare_eq76 h
  refine ⟨?_, ?_⟩
  · have := welfare_eq75 M u.c u.y v.c v.y
    rwa [h1] at this
  · have := welfare_eq75 M u.cs u.ys v.cs v.ys
    rwa [h2] at this

/-! ## Real balances: the exact meaning of "χ not too large" (T18, p. 684, fn 19) -/

/-- **Total first-order welfare of a Foreign monetary expansion** (T18; O&R p. 684, fn 19): with
`m = 0`, Home's total utility change, real balances included (`x = m − p`, `x̄ = m̄ − p̄`), is
`(1−n)m*[(δ(1+θ)+2) + χ(δ(1+θ)+2θ+1−θ²)]/D`. -/
theorem foreign_shock_total {L : ReduxLinear} {ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L 0 ms u v) (χ : ℝ) :
    dUR L u.c u.y v.c v.y + realBalanceTerm L χ (0 - u.p) (0 - v.p) =
      (1 - L.n) * ms * (L.E + χ * (L.δ * (1 + L.θ) + 2 * L.θ + 1 - L.θ ^ 2)) / L.D := by
  obtain ⟨rfl, rfl⟩ := (moneyShock_iff L 0 ms u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hδ0 : L.δ ≠ 0 := hδ.ne'
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  simp only [dUR, realBalanceTerm, shortRunSolution, steadySolution, ReduxLinear.D,
    ReduxLinear.E]
  field_simp
  ring

/-- The exact threshold function of T18: `A = θ² − 2θ − 1 − δ(1+θ)`; the real-balance
coefficient in `foreign_shock_total` is `−A` (O&R fn 19). -/
theorem realBalance_coef (L : ReduxLinear) :
    L.δ * (1 + L.θ) + 2 * L.θ + 1 - L.θ ^ 2 = -(L.θ ^ 2 - 2 * L.θ - 1 - L.δ * (1 + L.θ)) := by
  ring

/-- **The sign of the Foreign-expansion welfare effect** (T18): for `m* > 0`, total Home welfare
rises IFF `χ(θ² − 2θ − 1 − δ(1+θ)) < δ(1+θ) + 2`. -/
theorem foreign_shock_welfare_pos_iff {L : ReduxLinear} {ms : ℝ} {u : ShortVars}
    {v : SteadyVars} (h : MoneyShockEqm L 0 ms u v) (hms : 0 < ms) (χ : ℝ) :
    0 < dUR L u.c u.y v.c v.y + realBalanceTerm L χ (0 - u.p) (0 - v.p) ↔
      χ * (L.θ ^ 2 - 2 * L.θ - 1 - L.δ * (1 + L.θ)) < L.E := by
  rw [foreign_shock_total h χ, realBalance_coef]
  have hD := L.D_pos
  have hn : 0 < 1 - L.n := by linarith [L.hn1]
  have hk : 0 < (1 - L.n) * ms := mul_pos hn hms
  rw [lt_div_iff₀ hD, zero_mul]
  constructor
  · intro h1
    by_contra h2
    push Not at h2
    have : L.E + χ * -(L.θ ^ 2 - 2 * L.θ - 1 - L.δ * (1 + L.θ)) ≤ 0 := by linarith
    nlinarith
  · intro h1
    have : 0 < L.E + χ * -(L.θ ^ 2 - 2 * L.θ - 1 - L.δ * (1 + L.θ)) := by linarith
    positivity

/-- **When is "χ not too large" vacuous?** (T18; O&R p. 684): for `m* > 0`, a Foreign expansion
raises total Home welfare for EVERY `χ ≥ 0` IFF `θ² − 2θ − 1 ≤ δ(1+θ)`. -/
theorem welfare_pos_forall_chi_iff {L : ReduxLinear} {ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L 0 ms u v) (hms : 0 < ms) :
    (∀ χ, 0 ≤ χ → 0 < dUR L u.c u.y v.c v.y + realBalanceTerm L χ (0 - u.p) (0 - v.p)) ↔
      L.θ ^ 2 - 2 * L.θ - 1 ≤ L.δ * (1 + L.θ) := by
  have hE := L.E_pos
  constructor
  · intro hall
    by_contra hA
    push Not at hA
    have hA' : 0 < L.θ ^ 2 - 2 * L.θ - 1 - L.δ * (1 + L.θ) := by linarith
    have h1 := (foreign_shock_welfare_pos_iff h hms _).1
      (hall (L.E / (L.θ ^ 2 - 2 * L.θ - 1 - L.δ * (1 + L.θ))) (div_pos hE hA').le)
    rw [div_mul_cancel₀ _ hA'.ne'] at h1
    exact lt_irrefl _ h1
  · intro hA χ hχ
    rw [foreign_shock_welfare_pos_iff h hms]
    have : χ * (L.θ ^ 2 - 2 * L.θ - 1 - L.δ * (1 + L.θ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hχ (by linarith)
    linarith

/-- **The exact threshold** (T18; O&R p. 684, "as long as χ is not too large"): if
`θ² − 2θ − 1 > δ(1+θ)`, a Foreign expansion (`m* > 0`) raises total Home welfare IFF
`χ < (δ(1+θ)+2)/(θ² − 2θ − 1 − δ(1+θ))`. -/
theorem welfare_threshold {L : ReduxLinear} {ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L 0 ms u v) (hms : 0 < ms)
    (hA : L.δ * (1 + L.θ) < L.θ ^ 2 - 2 * L.θ - 1) (χ : ℝ) :
    0 < dUR L u.c u.y v.c v.y + realBalanceTerm L χ (0 - u.p) (0 - v.p) ↔
      χ < L.E / (L.θ ^ 2 - 2 * L.θ - 1 - L.δ * (1 + L.θ)) := by
  rw [foreign_shock_welfare_pos_iff h hms, lt_div_iff₀ (by linarith)]

/-- **No threshold for moderate substitutability** (T18): if `1 < θ ≤ 1 + √2` then
`θ² − 2θ − 1 ≤ 0 < δ(1+θ)`, so the Foreign-expansion welfare gain is positive for every `χ`. -/
theorem no_threshold_of_le {θ δ : ℝ} (hθ : 1 < θ) (hδ : 0 < δ) (hθ2 : θ ≤ 1 + Real.sqrt 2) :
    θ ^ 2 - 2 * θ - 1 < δ * (1 + θ) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h1 : θ - 1 ≤ Real.sqrt 2 := by linarith
  have h2 : (θ - 1) ^ 2 ≤ 2 := by
    have : 0 ≤ θ - 1 := by linarith
    nlinarith
  nlinarith

/-- The linear model at `θ = 6`, `δ = 0.05`, `n = 1/2` (O&R p. 684; the survey's counterexample to
an unconditional reading of "χ not too large"). -/
noncomputable def counterexampleModel : ReduxLinear :=
  ⟨6, 0.05, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Counterexample: a Foreign expansion can LOWER Home welfare** (T18; O&R p. 684, fn 19): at
`θ = 6`, `δ = 0.05`, the threshold `(δ(1+θ)+2)/(θ²−2θ−1−δ(1+θ)) = 2.35/22.65` lies in
`(0.10, 0.11)`; with `χ = 0.2` every equilibrium of a Foreign expansion `m* > 0` has
`dUᴿ + χ[x + x̄/δ] = −(109/1410)m* < 0`, and such an equilibrium exists. -/
theorem counterexample_theta6 :
    (0.10 : ℝ) < (0.05 * (1 + 6) + 2) / (6 ^ 2 - 2 * 6 - 1 - 0.05 * (1 + 6)) ∧
    (0.05 * (1 + 6) + 2) / (6 ^ 2 - 2 * 6 - 1 - 0.05 * (1 + 6)) < (0.11 : ℝ) ∧
    (∀ ms : ℝ, 0 < ms → ∀ u v, MoneyShockEqm counterexampleModel 0 ms u v →
      dUR counterexampleModel u.c u.y v.c v.y +
        realBalanceTerm counterexampleModel 0.2 (0 - u.p) (0 - v.p) = -(109 / 1410) * ms ∧
      dUR counterexampleModel u.c u.y v.c v.y +
        realBalanceTerm counterexampleModel 0.2 (0 - u.p) (0 - v.p) < 0) ∧
    ∃ u v, MoneyShockEqm counterexampleModel 0 1 u v := by
  refine ⟨by norm_num, by norm_num, fun ms hms u v h => ?_, ?_⟩
  · have e := foreign_shock_total h 0.2
    have e2 : dUR counterexampleModel u.c u.y v.c v.y +
        realBalanceTerm counterexampleModel 0.2 (0 - u.p) (0 - v.p) = -(109 / 1410) * ms := by
      rw [e]
      simp only [counterexampleModel, ReduxLinear.D, ReduxLinear.E]
      norm_num
      ring
    exact ⟨e2, by rw [e2]; linarith⟩
  · obtain ⟨w, hw, -⟩ := moneyShock_existsUnique counterexampleModel 0 1
    exact ⟨w.1, w.2, hw⟩

/-- **fn 19: a Home expansion raises Home real balances in every period** (O&R p. 685, fn 19):
with `m > 0 = m*`, `m − p > 0` on impact and `m̄ − p̄ = c̄ > 0` in the long run; hence every
component of Home welfare rises, and total welfare rises for every `χ ≥ 0`. -/
theorem home_shock_real_balances {L : ReduxLinear} {m : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L m 0 u v) (hm : 0 < m) (χ : ℝ) (hχ : 0 ≤ χ) :
    0 < m - u.p ∧ 0 < m - v.p ∧
      0 < dUR L u.c u.y v.c v.y + realBalanceTerm L χ (m - u.p) (m - v.p) := by
  have h76 := (welfare_eq76 h).1
  obtain ⟨rfl, rfl⟩ := (moneyShock_iff L m 0 u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hn0 := L.hn0
  have hn : 0 < 1 - L.n := by linarith [L.hn1]
  have hD := L.D_pos
  have hE := L.E_pos
  have hsq : 0 < L.θ ^ 2 - 1 := by nlinarith
  have hθ1 : 0 < L.θ - 1 := by linarith
  have h1 : 0 < m - (shortRunSolution L m 0).p := by
    simp only [shortRunSolution]
    have e : m - (1 - L.n) * ((L.δ * (1 + L.θ) + 2 * L.θ) * (m - 0) / L.D) =
        L.n * m + (1 - L.n) * (L.δ * (L.θ ^ 2 - 1) * m / L.D) := by
      unfold ReduxLinear.D; field_simp; ring
    rw [e]; positivity
  have h2 : 0 < m - (steadySolution L (shortRunSolution L m 0).b m 0).p := by
    simp only [steadySolution, shortRunSolution]
    have : 0 < (1 + L.θ) * L.δ * (2 * (1 - L.n) * (L.θ - 1) * (m - 0) / L.E) / (2 * L.θ) := by
      have : 0 < m - 0 := by linarith
      positivity
    linarith
  refine ⟨h1, h2, ?_⟩
  rw [h76]
  unfold realBalanceTerm
  have : 0 ≤ χ * (m - (shortRunSolution L m 0).p +
      1 / L.δ * (m - (steadySolution L (shortRunSolution L m 0).b m 0).p)) := by positivity
  have : 0 < (L.n * m + (1 - L.n) * 0) / L.θ := by
    have : 0 < L.θ := by linarith
    simp only [mul_zero, add_zero]
    positivity
  linarith

/-- **fn 19: a Foreign expansion raises Home real balances in the short run and lowers them in
the long run** (O&R p. 685, fn 19): with `m = 0 < m*`, `0 − p > 0` (Home's currency appreciates)
but `0 − p̄ < 0` (the long-run Home price level rises). -/
theorem foreign_shock_real_balances {L : ReduxLinear} {ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L 0 ms u v) (hms : 0 < ms) : 0 < 0 - u.p ∧ 0 - v.p < 0 := by
  obtain ⟨rfl, rfl⟩ := (moneyShock_iff L 0 ms u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hn : 0 < 1 - L.n := by linarith [L.hn1]
  have hD := L.D_pos
  have hE := L.E_pos
  have hθ1 : 0 < L.θ - 1 := by linarith
  have hG : 0 < L.δ * (1 + L.θ) + 2 * L.θ := by positivity
  constructor
  · simp only [shortRunSolution]
    have : 0 < (1 - L.n) * ((L.δ * (1 + L.θ) + 2 * L.θ) * ms / L.D) := by positivity
    have e : (1 - L.n) * ((L.δ * (1 + L.θ) + 2 * L.θ) * (0 - ms) / L.D) =
        -((1 - L.n) * ((L.δ * (1 + L.θ) + 2 * L.θ) * ms / L.D)) := by ring
    rw [e]; linarith
  · simp only [steadySolution, shortRunSolution]
    have : 0 < (1 + L.θ) * L.δ * (2 * (1 - L.n) * (L.θ - 1) * ms / L.E) / (2 * L.θ) := by
      positivity
    have e : (1 + L.θ) * L.δ * (2 * (1 - L.n) * (L.θ - 1) * (0 - ms) / L.E) / (2 * L.θ) =
        -((1 + L.θ) * L.δ * (2 * (1 - L.n) * (L.θ - 1) * ms / L.E) / (2 * L.θ)) := by ring
    rw [e]; linarith

/-! ## Menu costs and demand-determined output (T20, p. 674) -/

/-- The producer's one-period payoff in utility units as a function of output, O&R p. 665 and
p. 674: real revenue `y^{(θ−1)/θ} (Cᵂ)^{1/θ}` (on the demand curve (10)) valued at the marginal
utility `1/C`, minus the disutility of effort `(κ/2) y²`. -/
noncomputable def producerPayoff (θ κ X C y : ℝ) : ℝ :=
  y ^ ((θ - 1) / θ) * X ^ (1 / θ) / C - κ / 2 * y ^ 2

/-- The marginal payoff `ρ y^{ρ−1} X^{1/θ}/C − κ y`, `ρ = (θ−1)/θ` (O&R (15)). -/
noncomputable def marginalPayoff (θ κ X C y : ℝ) : ℝ :=
  (θ - 1) / θ * y ^ ((θ - 1) / θ - 1) * X ^ (1 / θ) / C - κ * y

/-- **At a price `π`, the payoff is revenue minus effort** (O&R p. 665): if `y = π^{−θ} Cᵂ`
then `producerPayoff = π y/C − (κ/2) y²`. -/
theorem producerPayoff_at_price {θ κ X C q : ℝ} (hθ : θ ≠ 0) (hX : 0 < X) (hq : 0 < q) :
    producerPayoff θ κ X C (cesDemand θ q 1 X) =
      q * cesDemand θ q 1 X / C - κ / 2 * cesDemand θ q 1 X ^ 2 := by
  have hy : 0 < cesDemand θ q 1 X := cesDemand_pos θ hq one_pos hX
  have h := revenue_on_demand hθ hq hy hX rfl
  unfold producerPayoff
  rw [← h]

/-- **The payoff lies below its tangent parabola** (T20; strict concavity of `y ↦ y^ρ`): for
`y₁ > 0`, `y ≥ 0`, `W(y) ≤ W(y₁) + W′(y₁)(y − y₁) − (κ/2)(y − y₁)²`. -/
theorem producerPayoff_le {θ κ X C y1 y : ℝ} (hθ : 1 < θ) (hX : 0 < X) (hC : 0 < C)
    (hy1 : 0 < y1) (hy : 0 ≤ y) :
    producerPayoff θ κ X C y ≤ producerPayoff θ κ X C y1 + marginalPayoff θ κ X C y1 * (y - y1) -
      κ / 2 * (y - y1) ^ 2 := by
  have hρ0 : 0 < (θ - 1) / θ := div_pos (by linarith) (by linarith)
  have hρ1 : (θ - 1) / θ < 1 := by rw [div_lt_one (by linarith)]; linarith
  have ht := rpow_le_tangent hρ0 hρ1 hy1 hy
  have hA : 0 ≤ X ^ (1 / θ) / C := div_nonneg (rpow_nonneg hX.le _) hC.le
  have key := mul_le_mul_of_nonneg_right ht hA
  have e : producerPayoff θ κ X C y1 + marginalPayoff θ κ X C y1 * (y - y1) -
      κ / 2 * (y - y1) ^ 2 - producerPayoff θ κ X C y =
      ((y1 ^ ((θ - 1) / θ) + (θ - 1) / θ * y1 ^ ((θ - 1) / θ - 1) * (y - y1)) *
        (X ^ (1 / θ) / C) - y ^ ((θ - 1) / θ) * (X ^ (1 / θ) / C)) := by
    unfold producerPayoff marginalPayoff; ring
  linarith

/-- **The gain from re-optimising is at most `W′(y₁)²/(2κ)`** (T20(a)): for `κ > 0`, a producer
at output `y₁ > 0` gains at most `(marginal payoff)²/(2κ)` by moving to any other output. -/
theorem gain_le_sq {θ κ X C y1 y : ℝ} (hθ : 1 < θ) (hκ : 0 < κ) (hX : 0 < X) (hC : 0 < C)
    (hy1 : 0 < y1) (hy : 0 ≤ y) :
    producerPayoff θ κ X C y - producerPayoff θ κ X C y1 ≤
      marginalPayoff θ κ X C y1 ^ 2 / (2 * κ) := by
  have h := producerPayoff_le (κ := κ) hθ hX hC hy1 hy
  set g := marginalPayoff θ κ X C y1
  have e : g * (y - y1) - κ / 2 * (y - y1) ^ 2 =
      g ^ 2 / (2 * κ) - (g - κ * (y - y1)) ^ 2 / (2 * κ) := by field_simp; ring
  have : 0 ≤ (g - κ * (y - y1)) ^ 2 / (2 * κ) := by positivity
  linarith

/-- **The optimum is the labour–leisure condition (15)** (O&R p. 665; T20): output `y₁ > 0` is a
global maximiser of the producer's payoff IFF `W′(y₁) = 0`. -/
theorem producerPayoff_isMax_iff {θ κ X C y1 : ℝ} (hθ : 1 < θ) (hκ : 0 < κ) (hX : 0 < X)
    (hC : 0 < C) (hy1 : 0 < y1) :
    (∀ y, 0 ≤ y → producerPayoff θ κ X C y ≤ producerPayoff θ κ X C y1) ↔
      marginalPayoff θ κ X C y1 = 0 := by
  constructor
  · intro hmax
    have hd : HasDerivAt (producerPayoff θ κ X C) (marginalPayoff θ κ X C y1) y1 := by
      have h1 := ((Real.hasDerivAt_rpow_const (p := (θ - 1) / θ) (Or.inl hy1.ne')).mul_const
        (X ^ (1 / θ))).div_const C
      have h2 := (hasDerivAt_pow 2 y1).const_mul (κ / 2)
      have h := h1.sub h2
      convert h using 1
      · funext y; simp [producerPayoff]
      · unfold marginalPayoff; simp; ring
    have hloc : IsLocalMax (producerPayoff θ κ X C) y1 := by
      filter_upwards [lt_mem_nhds hy1] with y hy
      exact hmax y hy.le
    exact hloc.hasDerivAt_eq_zero hd
  · intro h0 y hy
    have := producerPayoff_le (κ := κ) hθ hX hC hy1 hy
    rw [h0, zero_mul, add_zero] at this
    have : 0 ≤ κ / 2 * (y - y1) ^ 2 := by positivity
    linarith

/-- **The marginal payoff at a preset price** (T20): at the demand `y = π₀^{−θ}X` for a preset
relative price `π₀`, the marginal payoff is `ρ π₀/C − κ π₀^{−θ} X` (marginal revenue in real
terms is the constant `ρ π₀`). -/
theorem marginalPayoff_at_demand {θ κ X C π0 : ℝ} (hθ : θ ≠ 0) (hX : 0 < X) (hπ0 : 0 < π0) :
    marginalPayoff θ κ X C (π0 ^ (-θ) * X) = (θ - 1) / θ * π0 / C - κ * (π0 ^ (-θ) * X) := by
  unfold marginalPayoff
  have e1 : (θ - 1) / θ - 1 = -(1 / θ) := by field_simp; ring
  have e2 : (π0 ^ (-θ) * X) ^ (-(1 / θ)) * X ^ (1 / θ) = π0 := by
    rw [mul_rpow (rpow_nonneg hπ0.le _) hX.le, ← rpow_mul hπ0.le, rpow_neg hX.le]
    have : -θ * -(1 / θ) = 1 := by field_simp
    rw [this, rpow_one]
    have := (rpow_pos_of_pos hX (1 / θ)).ne'
    field_simp
  rw [e1]
  have e3 : (θ - 1) / θ * (π0 ^ (-θ) * X) ^ (-(1 / θ)) * X ^ (1 / θ) / C =
      (θ - 1) / θ * ((π0 ^ (-θ) * X) ^ (-(1 / θ)) * X ^ (1 / θ)) / C := by ring
  rw [e3, e2]

/-- **The menu-cost rationale, precisely: the private gain from adjusting a preset price is
SECOND order** (T20(a); O&R p. 674, "small changes in an individual's price will have only a
second-order impact"). Let the relative price `π₀` be optimal at the base aggregates
`(X₀, C₀)` (`ρπ₀/C₀ = κπ₀^{−θ}X₀`, i.e. (15)), and let the aggregates move along
`X = X₀e^{τa}`, `C = C₀e^{τb}`. Keeping the price, the producer sells `π₀^{−θ}X`; there is a
constant `K` such that for all small `τ` NO output (equivalently no price) does better by more than
`Kτ²`. -/
theorem menu_cost_second_order {θ κ π0 X0 C0 : ℝ} (hθ : 1 < θ) (hκ : 0 < κ) (hπ0 : 0 < π0)
    (hX0 : 0 < X0) (hC0 : 0 < C0) (hopt : (θ - 1) / θ * π0 / C0 = κ * (π0 ^ (-θ) * X0))
    (a b : ℝ) :
    ∃ K, ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ y, 0 ≤ y →
      producerPayoff θ κ (X0 * Real.exp (τ * a)) (C0 * Real.exp (τ * b)) y -
        producerPayoff θ κ (X0 * Real.exp (τ * a)) (C0 * Real.exp (τ * b))
          (π0 ^ (-θ) * (X0 * Real.exp (τ * a))) ≤ K * τ ^ 2 := by
  have hθ0 : θ ≠ 0 := by linarith
  set g : ℝ → ℝ := fun τ => (θ - 1) / θ * π0 / C0 * Real.exp (τ * (-b)) -
    κ * (π0 ^ (-θ) * X0) * Real.exp (τ * a) with hg
  have hgeq : ∀ τ, marginalPayoff θ κ (X0 * Real.exp (τ * a)) (C0 * Real.exp (τ * b))
      (π0 ^ (-θ) * (X0 * Real.exp (τ * a))) = g τ := by
    intro τ
    rw [marginalPayoff_at_demand hθ0 (mul_pos hX0 (Real.exp_pos _)) hπ0]
    simp only [hg]
    rw [show τ * -b = -(τ * b) by ring, Real.exp_neg]
    field_simp
  have hg0 : g 0 = 0 := by simp only [hg]; simp [hopt]
  have hgd : HasDerivAt g ((θ - 1) / θ * π0 / C0 * (-b) - κ * (π0 ^ (-θ) * X0) * a) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (-b)).exp.const_mul ((θ - 1) / θ * π0 / C0)
    have h2 := ((hasDerivAt_id (0 : ℝ)).mul_const a).exp.const_mul (κ * (π0 ^ (-θ) * X0))
    convert h1.sub h2 using 1
    · funext τ; simp only [hg, Pi.sub_apply, id_eq]
    · simp
  set g' := (θ - 1) / θ * π0 / C0 * (-b) - κ * (π0 ^ (-θ) * X0) * a
  have hlo := (hasDerivAt_iff_isLittleO.1 hgd).def (show (0 : ℝ) < 1 by norm_num)
  refine ⟨(|g'| + 1) ^ 2 / (2 * κ), ?_⟩
  filter_upwards [hlo] with τ hτ y hy
  have hb : |g τ| ≤ (|g'| + 1) * |τ| := by
    rw [hg0, sub_zero, sub_zero, smul_eq_mul, one_mul, Real.norm_eq_abs, Real.norm_eq_abs] at hτ
    have := abs_sub_abs_le_abs_sub (g τ) (τ * g')
    rw [abs_mul] at this
    nlinarith [abs_nonneg τ, abs_nonneg g']
  have hX : 0 < X0 * Real.exp (τ * a) := mul_pos hX0 (Real.exp_pos _)
  have hC : 0 < C0 * Real.exp (τ * b) := mul_pos hC0 (Real.exp_pos _)
  have hy1 : 0 < π0 ^ (-θ) * (X0 * Real.exp (τ * a)) := mul_pos (rpow_pos_of_pos hπ0 _) hX
  have hgain := gain_le_sq (κ := κ) hθ hκ hX hC hy1 hy
  rw [hgeq τ] at hgain
  have hsq : g τ ^ 2 ≤ ((|g'| + 1) * |τ|) ^ 2 := by
    rw [← sq_abs (g τ)]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have : g τ ^ 2 / (2 * κ) ≤ (|g'| + 1) ^ 2 / (2 * κ) * τ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
    calc g τ ^ 2 ≤ ((|g'| + 1) * |τ|) ^ 2 := hsq
      _ = (|g'| + 1) ^ 2 * τ ^ 2 := by rw [mul_pow, sq_abs]
  linarith

/-- **Any menu cost deters adjustment for small enough shocks** (T20(a); O&R p. 674, "producers
will not necessarily find it profitable to change prices in the face of sufficiently small demand
shocks"): for every menu cost `Z > 0`, for all small enough `τ` the gain from changing the preset
price is below `Z`. -/
theorem menu_cost_rationale {θ κ π0 X0 C0 : ℝ} (hθ : 1 < θ) (hκ : 0 < κ) (hπ0 : 0 < π0)
    (hX0 : 0 < X0) (hC0 : 0 < C0) (hopt : (θ - 1) / θ * π0 / C0 = κ * (π0 ^ (-θ) * X0))
    (a b Z : ℝ) (hZ : 0 < Z) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ y, 0 ≤ y →
      producerPayoff θ κ (X0 * Real.exp (τ * a)) (C0 * Real.exp (τ * b)) y -
        producerPayoff θ κ (X0 * Real.exp (τ * a)) (C0 * Real.exp (τ * b))
          (π0 ^ (-θ) * (X0 * Real.exp (τ * a))) < Z := by
  obtain ⟨K, hK⟩ := menu_cost_second_order hθ hκ hπ0 hX0 hC0 hopt a b
  have hc : Tendsto (fun τ : ℝ => K * τ ^ 2) (𝓝 0) (𝓝 (K * 0 ^ 2)) :=
    ((continuous_const.mul (continuous_pow 2)).tendsto 0)
  rw [show K * (0 : ℝ) ^ 2 = 0 by ring] at hc
  filter_upwards [hK, hc.eventually (gt_mem_nhds hZ)] with τ h1 h2 y hy
  exact lt_of_le_of_lt (h1 y hy) h2

/-- **Meeting demand at a preset price is optimal IFF price covers marginal cost** (T20(b);
O&R p. 674): a producer with a fixed real price `q > 0` facing demand `y_d` can sell any
`y ∈ [0, y_d]`; producing `y_d` is optimal IFF `κ y_d ≤ q/C` (marginal disutility at `y_d` does
not exceed the marginal revenue `q` valued at `1/C`). -/
theorem meet_demand_iff {q C κ yd : ℝ} (hq : 0 < q) (hC : 0 < C) (hκ : 0 < κ) :
    (∀ y, 0 ≤ y → y ≤ yd → q * y / C - κ / 2 * y ^ 2 ≤ q * yd / C - κ / 2 * yd ^ 2) ↔
      κ * yd ≤ q / C := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    set y := q / C / κ with hy
    have hyle : y < yd := by rw [hy, div_lt_iff₀ hκ]; linarith
    have hy0 : 0 ≤ y := by positivity
    have := h y hy0 hyle.le
    have e : q * yd / C - κ / 2 * yd ^ 2 - (q * y / C - κ / 2 * y ^ 2) =
        -(κ / 2) * (yd - y) ^ 2 := by
      rw [hy]; field_simp; ring
    have : 0 < (κ / 2) * (yd - y) ^ 2 := by
      have : 0 < yd - y := by linarith
      positivity
    linarith
  · intro h y hy0 hyle
    have e : q * yd / C - κ / 2 * yd ^ 2 - (q * y / C - κ / 2 * y ^ 2) =
        (yd - y) * (q / C - κ / 2 * (yd + y)) := by field_simp; ring
    have h1 : 0 ≤ yd - y := by linarith
    have h2 : 0 ≤ q / C - κ / 2 * (yd + y) := by nlinarith
    nlinarith [mul_nonneg h1 h2]

/-- **At the initial steady state price strictly exceeds marginal cost** (O&R p. 674: "under
monopoly, prices are set above marginal cost"): with `q = 1`, `C = y = ȳ₀`, `κȳ₀ < 1/ȳ₀`, and
the markup of price over marginal cost is exactly `θ/(θ−1)`. -/
theorem steady_price_exceeds_mc (M : ReduxParams) :
    M.κ * M.ybar0 < 1 / M.ybar0 ∧ (1 / M.ybar0) / (M.κ * M.ybar0) = M.θ / (M.θ - 1) := by
  have hy := M.ybar0_pos
  have hk := M.κ_mul_ybar0_sq
  have hθ := M.hθ
  have hθ1 : M.θ - 1 ≠ 0 := by linarith
  have hθ0 : M.θ ≠ 0 := by linarith
  constructor
  · rw [lt_div_iff₀ hy]
    have : M.κ * M.ybar0 * M.ybar0 = (M.θ - 1) / M.θ := by rw [← hk]; ring
    rw [this, div_lt_one (by linarith)]
    linarith
  · have e : (1 / M.ybar0) / (M.κ * M.ybar0) = 1 / (M.κ * M.ybar0 ^ 2) := by
      have := M.hκ.ne'
      field_simp
    rw [e, hk]
    field_simp

/-! ## Distorting income taxes (77)–(81) (T21) -/

/-- **Rebated income taxes leave the budget unchanged** (O&R (77)–(78), p. 686–687): the
household budget (77) with income tax `τᴸ` and the government budget (78) with lump-sum rebate
`τ` combine to `P B′ = P(1+r)B + p y − P C`, the same as (8) with (9). -/
theorem tax_budget_rebate {P B B1 M Mprev r τL py C τ : ℝ} (hP : P ≠ 0)
    (h77 : P * B1 + M = P * (1 + r) * B + Mprev + (1 - τL) * py - P * C - P * τ)
    (h78 : 0 = τ + τL * py / P + (M - Mprev) / P) :
    P * B1 = P * (1 + r) * B + py - P * C := by
  have h : P * τ = -(τL * py) - (M - Mprev) := by
    have := congrArg (fun z => P * z) h78
    simp only [mul_zero] at this
    field_simp at this
    linarith
  linear_combination h77 - h

/-- **(80): steady-state output with an income tax**, O&R p. 687 (T21): in a symmetric steady
state (`y = C = Cᵂ`), the taxed labour condition (79)
`y^{(θ+1)/θ} = (1−τᴸ)((θ−1)/(θκ))(Cᵂ)^{1/θ}/C` holds IFF `y = [(θ−1)(1−τᴸ)/(θκ)]^{1/2}`. -/
theorem taxed_symmetric_output {θ κ τL y : ℝ} (hθ : 1 < θ) (hy : 0 < y) :
    y ^ ((θ + 1) / θ) = (1 - τL) * ((θ - 1) / (θ * κ)) * y ^ (1 / θ) / y ↔
      y = Real.sqrt ((θ - 1) * (1 - τL) / (θ * κ)) := by
  have hθ0 : θ ≠ 0 := by linarith
  rw [rpow_succ_div hθ0 hy]
  have hr := (rpow_pos_of_pos hy (1 / θ)).ne'
  have hK : (θ - 1) * (1 - τL) / (θ * κ) = (1 - τL) * ((θ - 1) / (θ * κ)) := by ring
  have e : (y * y ^ (1 / θ) = (1 - τL) * ((θ - 1) / (θ * κ)) * y ^ (1 / θ) / y) ↔
      y ^ 2 = (θ - 1) * (1 - τL) / (θ * κ) := by
    rw [hK, eq_div_iff hy.ne']
    constructor
    · intro h
      have h2 : (y ^ 2 - (1 - τL) * ((θ - 1) / (θ * κ))) * y ^ (1 / θ) = 0 := by
        linear_combination h
      have := (mul_eq_zero.1 h2).resolve_right hr
      linarith
    · intro h
      rw [← h]; ring
  rw [e]
  constructor
  · intro h; rw [← h, Real.sqrt_sq hy.le]
  · intro h
    have h0 : 0 ≤ (θ - 1) * (1 - τL) / (θ * κ) := by
      by_contra hneg
      push Not at hneg
      rw [Real.sqrt_eq_zero'.2 hneg.le] at h
      linarith
    rw [h, Real.sq_sqrt h0]

/-- **An income tax lowers steady-state output** (O&R p. 687): `τᴸ ↦ [(θ−1)(1−τᴸ)/(θκ)]^{1/2}` is
strictly decreasing on `τᴸ ≤ 1`. -/
theorem taxed_output_strictAntiOn {θ κ : ℝ} (hθ : 1 < θ) (hκ : 0 < κ) :
    StrictAntiOn (fun τL : ℝ => Real.sqrt ((θ - 1) * (1 - τL) / (θ * κ))) (Set.Iic 1) := by
  intro a ha b hb hab
  have ha' : a ≤ 1 := ha
  have hb' : b ≤ 1 := hb
  have hk : 0 < θ * κ := mul_pos (by linarith) hκ
  apply Real.sqrt_lt_sqrt
  · exact div_nonneg (mul_nonneg (by linarith) (by linarith)) hk.le
  · apply div_lt_div_of_pos_right _ hk
    have : 0 < θ - 1 := by linarith
    nlinarith

/-- **The log-linear labour condition is unchanged by the tax** (O&R p. 687, "the
log-linearization of the model goes through exactly as before"; T21): (79) is (15) with
`K` replaced by `(1−τᴸ)K`, and a constant factor drops out of log changes, so
`(θ+1)Δlog y = −θΔlog C + Δlog Cᵂ` exactly, which is (33). -/
theorem taxed_labour_log_exact {θ κ τL y0 y1 C0 C1 X0 X1 : ℝ} (hθ : 1 < θ) (hκ : 0 < κ)
    (hτ : τL < 1) (hy0 : 0 < y0) (hy1 : 0 < y1) (hC0 : 0 < C0) (hC1 : 0 < C1) (hX0 : 0 < X0)
    (hX1 : 0 < X1)
    (h0 : y0 ^ ((θ + 1) / θ) = (1 - τL) * ((θ - 1) / (θ * κ)) * X0 ^ (1 / θ) / C0)
    (h1 : y1 ^ ((θ + 1) / θ) = (1 - τL) * ((θ - 1) / (θ * κ)) * X1 ^ (1 / θ) / C1) :
    (θ + 1) * (Real.log y1 - Real.log y0) =
      -θ * (Real.log C1 - Real.log C0) + (Real.log X1 - Real.log X0) := by
  have hK : 0 < (1 - τL) * ((θ - 1) / (θ * κ)) :=
    mul_pos (by linarith) (div_pos (by linarith) (mul_pos (by linarith) hκ))
  exact labour_log_exact (by linarith) hK hy0 hy1 hC0 hC1 hX0 hX1 h0 h1

/-- The steady-state output with tax `τᴸ`, (80), O&R p. 687. -/
noncomputable def taxedOutput (M : ReduxParams) (τL : ℝ) : ℝ :=
  Real.sqrt ((M.θ - 1) * (1 - τL) / (M.θ * M.κ))

/-- `κ ȳ₀(τᴸ)² = (1−τᴸ)(θ−1)/θ` (O&R (80), used for (81)). -/
theorem κ_mul_taxedOutput_sq (M : ReduxParams) {τL : ℝ} (hτ : τL ≤ 1) :
    M.κ * taxedOutput M τL ^ 2 = (1 - τL) * ((M.θ - 1) / M.θ) := by
  have hθ := M.hθ
  have hκ := M.hκ
  unfold taxedOutput
  rw [Real.sq_sqrt (div_nonneg (mul_nonneg (by linarith) (by linarith))
    (mul_pos (by linarith) hκ).le)]
  have : M.θ ≠ 0 := by linarith
  field_simp

/-- The first-order change in real utility with an income tax, O&R p. 687–688:
`c − (1−τᴸ)((θ−1)/θ) y + (1/δ)[c̄ − (1−τᴸ)((θ−1)/θ) ȳ]`. -/
noncomputable def dURtax (L : ReduxLinear) (τL c y cb yb : ℝ) : ℝ :=
  c - (1 - τL) * ((L.θ - 1) / L.θ) * y + 1 / L.δ * (cb - (1 - τL) * ((L.θ - 1) / L.θ) * yb)

/-- **(75) with an income tax, as a derivative** (T21; O&R p. 687): around the taxed symmetric
steady state (80), the derivative of `Uᴿ` is `dURtax`. -/
theorem welfare_tax_hasDerivAt (M : ReduxParams) {τL : ℝ} (hτ : τL < 1) (c y cb yb : ℝ) :
    HasDerivAt (fun τ => realWelfare M.β M.κ
      (twoRegime (taxedOutput M τL * Real.exp (τ * c)) (taxedOutput M τL * Real.exp (τ * cb)))
      (twoRegime (taxedOutput M τL * Real.exp (τ * y)) (taxedOutput M τL * Real.exp (τ * yb))))
      (dURtax (linearOf M) τL c y cb yb) 0 := by
  have hθ := M.hθ
  have hY : 0 < taxedOutput M τL := by
    unfold taxedOutput
    exact Real.sqrt_pos.2 (div_pos (mul_pos (by linarith) (by linarith))
      (mul_pos (by linarith) M.hκ))
  have h := welfare_hasDerivAt M.hβ0.le M.hβ1 0 M.κ 0 (taxedOutput M τL) c cb 0 0 y yb hY
    one_pos one_pos
  have e : (fun τ => realWelfare M.β M.κ
      (twoRegime (taxedOutput M τL * Real.exp (τ * c)) (taxedOutput M τL * Real.exp (τ * cb)))
      (twoRegime (taxedOutput M τL * Real.exp (τ * y)) (taxedOutput M τL * Real.exp (τ * yb)))) =
      fun τ => lifetimeWelfare M.β 0 (M.κ * (1 - τ * 0))
      (twoRegime (taxedOutput M τL * Real.exp (τ * c)) (taxedOutput M τL * Real.exp (τ * cb)))
      (twoRegime (1 * Real.exp (τ * 0)) (1 * Real.exp (τ * 0)))
      (twoRegime (taxedOutput M τL * Real.exp (τ * y)) (taxedOutput M τL * Real.exp (τ * yb))) := by
    funext τ
    rw [realWelfare_eq]
    unfold lifetimeWelfare periodWelfare
    simp
  rw [e]
  convert h using 1
  unfold dURtax linearOf
  simp only
  rw [beta_div_one_sub M, κ_mul_taxedOutput_sq M hτ.le]
  ring

/-- **The tax wedge in welfare** (T21): `dURtax = dUᴿ + ((θ−1)/θ)τᴸ(y + ȳ/δ)` (O&R p. 687: the
marginal revenue from taxation is rebated to domestic residents only). -/
theorem dURtax_eq (L : ReduxLinear) (τL c y cb yb : ℝ) :
    dURtax L τL c y cb yb = dUR L c y cb yb + (L.θ - 1) / L.θ * τL * (y + yb / L.δ) := by
  unfold dURtax dUR; ring

/-- **(81)**, O&R p. 688 (T21): with an income tax, the welfare effect of a Foreign monetary
expansion (`m = 0`) on Home is `dUᴿ = ((1−n)m*/θ)[1 − τᴸ(θ−1)²/(δ(1+θ)+2)]`. The log-linear
equilibrium is the untaxed one (`taxed_labour_log_exact`, `tax_budget_rebate`). -/
theorem welfare_eq81 {L : ReduxLinear} {ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L 0 ms u v) (τL : ℝ) :
    dURtax L τL u.c u.y v.c v.y =
      (1 - L.n) * ms / L.θ * (1 - τL * (L.θ - 1) ^ 2 / (L.δ * (1 + L.θ) + 2)) := by
  obtain ⟨rfl, rfl⟩ := (moneyShock_iff L 0 ms u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hδ0 : L.δ ≠ 0 := hδ.ne'
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  simp only [dURtax, shortRunSolution, steadySolution, ReduxLinear.D, ReduxLinear.E]
  field_simp
  ring

/-- **The exact sign of (81)** (T21; O&R p. 688): for `m* > 0`, a Foreign expansion LOWERS Home
welfare IFF `τᴸ(θ−1)² > δ(1+θ) + 2`. -/
theorem welfare81_neg_iff {L : ReduxLinear} {ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L 0 ms u v) (hms : 0 < ms) (τL : ℝ) :
    dURtax L τL u.c u.y v.c v.y < 0 ↔ L.δ * (1 + L.θ) + 2 < τL * (L.θ - 1) ^ 2 := by
  rw [welfare_eq81 h]
  have hθ := L.hθ
  have hE : 0 < L.δ * (1 + L.θ) + 2 := L.E_pos
  have hk : 0 < (1 - L.n) * ms / L.θ := by
    have : 0 < 1 - L.n := by linarith [L.hn1]
    have : 0 < L.θ := by linarith
    positivity
  rw [mul_neg_iff]
  constructor
  · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
    · rw [sub_neg, one_lt_div hE] at h2; exact h2
    · linarith
  · intro h2
    left
    exact ⟨hk, by rw [sub_neg, one_lt_div hE]; exact h2⟩

/-- **"For large enough θ, Foreign monetary expansion lowers Home welfare"** (T21; O&R p. 688,
made precise): for every `δ > 0` and tax rate `τᴸ > 0` there is `θ̄` with
`τᴸ(θ−1)² > δ(1+θ) + 2` for all `θ > θ̄`. -/
theorem welfare81_large_theta {δ τL : ℝ} (hδ : 0 < δ) (hτ : 0 < τL) :
    ∃ θbar, ∀ θ, θbar < θ → δ * (1 + θ) + 2 < τL * (θ - 1) ^ 2 := by
  refine ⟨2 + (3 * δ + 2) / τL, fun θ hθ => ?_⟩
  set x := θ - 1 with hx
  have hq : 0 < (3 * δ + 2) / τL := by positivity
  have hx1 : 1 < x := by linarith
  have hx2 : (3 * δ + 2) / τL < x := by linarith
  have h3 : 3 * δ + 2 < τL * x := by rw [div_lt_iff₀ hτ] at hx2; linarith
  have e : δ * (1 + θ) + 2 = δ * x + 2 * δ + 2 := by rw [hx]; ring
  rw [e]
  nlinarith

/-- **For θ near one the monopoly distortion dominates** (T21; O&R p. 688): for `τᴸ ≤ 1` and
`1 < θ ≤ 2`, the bracket in (81) is positive, so a Foreign expansion raises Home welfare. -/
theorem welfare81_small_theta {δ τL θ : ℝ} (hδ : 0 < δ) (hτ1 : τL ≤ 1)
    (hθ1 : 1 < θ) (hθ2 : θ ≤ 2) : 0 < 1 - τL * (θ - 1) ^ 2 / (δ * (1 + θ) + 2) := by
  have hE : 0 < δ * (1 + θ) + 2 := by positivity
  rw [sub_pos, div_lt_one hE]
  have h1 : (θ - 1) ^ 2 ≤ 1 := by nlinarith
  have h2 : τL * (θ - 1) ^ 2 ≤ 1 := by
    calc τL * (θ - 1) ^ 2 ≤ 1 * 1 :=
          mul_le_mul hτ1 h1 (sq_nonneg _) zero_le_one
      _ = 1 := by ring
  nlinarith

/-! ## Country size and welfare (T22, §10.1.10, p. 688) -/

/-- **A Home monetary expansion in a country of size `n`** (T22; O&R p. 688): `dUᴿ = nm/θ`,
`cᵂ = nm`, `r = −((1+δ)/δ)nm`, and Home output `y = nm + (1−n)θe` with the size-free
`e = [δ(1+θ)+2θ]m/(θ(δ(1+θ)+2))` (`exchangeRateCoef`). -/
theorem home_shock_size {L : ReduxLinear} {m : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L m 0 u v) :
    dUR L u.c u.y v.c v.y = L.n * m / L.θ ∧ u.cW = L.n * m ∧
    u.r = -((1 + L.δ) / L.δ) * (L.n * m) ∧ u.e = exchangeRateCoef L.θ L.δ * m ∧
    u.y = L.n * m + (1 - L.n) * L.θ * (exchangeRateCoef L.θ L.δ * m) := by
  obtain ⟨h1, -, -⟩ := welfare_eq76 h
  obtain ⟨-, hcW, -, hr, hy, -⟩ := moneyShock_world h
  have he := (moneyShock_closed_forms h).1
  have hE : exchangeRateCoef L.θ L.δ * m = (L.δ * (1 + L.θ) + 2 * L.θ) * (m - 0) / L.D := by
    unfold exchangeRateCoef ReduxLinear.D; ring
  refine ⟨by rw [h1]; ring, by rw [hcW]; ring, by rw [hr]; ring, by rw [he, hE], ?_⟩
  rw [hy, he, hE]; ring

/-- **The small-country limit** (T22; O&R p. 688): as `n → 0`, a Home monetary expansion has no
effect on world consumption, on the world real interest rate, or on Home welfare
(`nm/θ → 0`), while Home output tends to `θe`. -/
theorem small_country_limit (θ δ m : ℝ) :
    Tendsto (fun n : ℝ => n * m / θ) (𝓝 0) (𝓝 0) ∧
    Tendsto (fun n : ℝ => n * m) (𝓝 0) (𝓝 0) ∧
    Tendsto (fun n : ℝ => -((1 + δ) / δ) * (n * m)) (𝓝 0) (𝓝 0) ∧
    Tendsto (fun n : ℝ => n * m + (1 - n) * θ * (exchangeRateCoef θ δ * m)) (𝓝 0)
      (𝓝 (θ * (exchangeRateCoef θ δ * m))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : Continuous (fun n : ℝ => n * m / θ) := by fun_prop
    simpa using h.tendsto 0
  · have h : Continuous (fun n : ℝ => n * m) := by fun_prop
    simpa using h.tendsto 0
  · have h : Continuous (fun n : ℝ => -((1 + δ) / δ) * (n * m)) := by fun_prop
    simpa using h.tendsto 0
  · have h : Continuous (fun n : ℝ => n * m + (1 - n) * θ * (exchangeRateCoef θ δ * m)) := by
      fun_prop
    simpa using h.tendsto 0

/-! ## Exercise 3: the small country directly -/

/-- **Ex. 3, the nonlinear steady state of the small country exists and is unique for every
`B̄`** (O&R p. 713): with exogenous world demand `Cᵂ = X > 0` and interest rate `r = δ`, the
steady-state conditions — demand `y = p^{−θ}X`, the labour–leisure condition (15)
`y^{(θ+1)/θ} = K X^{1/θ}/C` and income = expenditure `C = δB̄ + p y` — have exactly one positive
solution `(y, p, C)`: `y = g⁻¹(δB̄/X^{1/θ})` with the gap function `g` of T7. -/
theorem ex3_steady_existsUnique {θ κ δ X : ℝ} (hθ : 1 < θ) (hκ : 0 < κ) (hX : 0 < X) (B : ℝ) :
    ∃! t : ℝ × ℝ × ℝ, 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧ t.1 = cesDemand θ t.2.1 1 X ∧
      t.1 ^ ((θ + 1) / θ) = (θ - 1) / (θ * κ) * X ^ (1 / θ) / t.2.2 ∧
      t.2.2 = δ * B + t.2.1 * t.1 := by
  have hθ0 : θ ≠ 0 := by linarith
  set K := (θ - 1) / (θ * κ) with hKdef
  have hK : 0 < K := div_pos (by linarith) (mul_pos (by linarith) hκ)
  have hXr := rpow_pos_of_pos hX (1 / θ)
  -- the reduction: any solution has `X^{1/θ} g(y) = δB̄`, `p = X^{1/θ}/y^{1/θ}`, `C = K p / y`
  have reduce : ∀ y p C : ℝ, 0 < y → 0 < p → 0 < C → y = cesDemand θ p 1 X →
      y ^ ((θ + 1) / θ) = K * X ^ (1 / θ) / C → C = δ * B + p * y →
      p = X ^ (1 / θ) / y ^ (1 / θ) ∧ C = K * p / y ∧
        X ^ (1 / θ) * gapFn θ K y = δ * B := by
    intro y p C hy hp hC hd hl hb
    have hyr := rpow_pos_of_pos hy (1 / θ)
    have hXeq : X ^ (1 / θ) = p * y ^ (1 / θ) := by
      have hX' : X = p ^ θ * y := by
        rw [hd]; unfold cesDemand
        rw [div_one, rpow_neg hp.le]
        have := (rpow_pos_of_pos hp θ).ne'
        field_simp
      rw [hX', mul_rpow (rpow_nonneg hp.le _) hy.le, ← rpow_mul hp.le, mul_one_div_cancel hθ0,
        rpow_one]
    have hp' : p = X ^ (1 / θ) / y ^ (1 / θ) := by rw [hXeq]; field_simp
    have hC' : C = K * p / y := by
      rw [rpow_succ_div hθ0 hy, hXeq] at hl
      field_simp at hl ⊢
      nlinarith [hl]
    refine ⟨hp', hC', ?_⟩
    rw [gapFn_eq hθ0 hy, hXeq]
    have : C - p * y = δ * B := by linarith
    rw [← this, hC']
    field_simp
  -- existence
  set y0 := gapInv θ K (δ * B / X ^ (1 / θ)) with hy0
  obtain ⟨hy0pos, hgy0⟩ := gapInv_spec hθ hK (δ * B / X ^ (1 / θ))
  rw [← hy0] at hy0pos hgy0
  have hy0r := rpow_pos_of_pos hy0pos (1 / θ)
  set p0 := X ^ (1 / θ) / y0 ^ (1 / θ) with hp0
  have hp0pos : 0 < p0 := div_pos hXr hy0r
  set C0 := K * p0 / y0 with hC0
  have hC0pos : 0 < C0 := div_pos (mul_pos hK hp0pos) hy0pos
  refine ⟨(y0, p0, C0), ⟨hy0pos, hp0pos, hC0pos, ?_, ?_, ?_⟩, ?_⟩
  · change y0 = cesDemand θ p0 1 X
    unfold cesDemand
    rw [div_one, hp0, div_rpow hXr.le hy0r.le, ← rpow_mul hX.le, ← rpow_mul hy0pos.le]
    have e : 1 / θ * -θ = -1 := by field_simp
    rw [e, rpow_neg_one, rpow_neg_one]
    field_simp
  · change y0 ^ ((θ + 1) / θ) = K * X ^ (1 / θ) / C0
    rw [rpow_succ_div hθ0 hy0pos, hC0, hp0]
    field_simp
  · change C0 = δ * B + p0 * y0
    have hg : X ^ (1 / θ) * gapFn θ K y0 = δ * B := by
      rw [hgy0]; field_simp
    rw [gapFn_eq hθ0 hy0pos] at hg
    rw [hC0, hp0, ← hg]
    field_simp
    ring
  · -- uniqueness
    rintro ⟨y, p, C⟩ ⟨hy, hp, hC, hd, hl, hb⟩
    simp only at hy hp hC hd hl hb
    obtain ⟨hp', hC', hg⟩ := reduce y p C hy hp hC hd hl hb
    have hyeq : y = y0 := by
      have : gapFn θ K y = δ * B / X ^ (1 / θ) := by
        rw [eq_div_iff hXr.ne']; linarith
      rw [hy0, ← this, gapInv_gapFn hθ hK hy]
    subst hyeq
    have hpeq : p = p0 := by rw [hp', hp0]
    subst hpeq
    rw [hC']

/-- **Ex. 3: consumption is flat, exactly** (O&R p. 713): with the exogenous world rate satisfying
`β(1+r) = 1`, the Euler equation (13) gives `C_{t+1} = C_t`; in logs `c̄ = c`. -/
theorem ex3_consumption_flat {β r C1 C2 : ℝ} (hβr : β * (1 + r) = 1)
    (heuler : C2 = β * (1 + r) * C1) : C2 = C1 := by
  rw [heuler, hβr, one_mul]

/-- The unknowns of the linearised small-country model of Ex. 3 (O&R p. 713): impact
consumption `c`, output `y`, the relative world price of the Home good `p`, the exchange rate `e`,
the current account `b̄`, and the long-run `c̄, ȳ, p̄, ē`. -/
structure Ex3Vars where
  c : ℝ
  y : ℝ
  p : ℝ
  e : ℝ
  b : ℝ
  cb : ℝ
  yb : ℝ
  pb : ℝ
  eb : ℝ

/-- **The linearised small-country model** (Ex. 3, O&R p. 713, following §10.1.5–§10.1.7 with
`Cᵂ`, `P*` and `r` exogenous): the Home-currency price of the Home good is preset, so its world
relative price moves by `p = −e`; demand `y = −θp`; the current account `b̄ = p + y − c` ((55));
the Euler equation with an exogenous rate `c̄ = c`; money demand at date 1 (the consumer price
level moves with `e`, `r̂ = 0`) and in the long run; and the long-run demand, labour–leisure
condition and budget (the analogues of (30), (33), (40)). -/
structure Ex3Eqm (L : ReduxLinear) (m : ℝ) (w : Ex3Vars) : Prop where
  price : w.p = -w.e
  demand : w.y = -L.θ * w.p
  ca : w.b = w.p + w.y - w.c
  euler : w.cb = w.c
  money : m - w.e = w.c - (w.eb - w.e) / L.δ
  money_lr : m - w.eb = w.cb
  demand_lr : w.yb = -L.θ * w.pb
  labour_lr : (L.θ + 1) * w.yb = -L.θ * w.cb
  budget_lr : w.cb = L.δ * w.b + w.pb + w.yb

/-- The closed-form solution of Ex. 3 (O&R p. 713): (65)–(67) with `n = 0`, `m* = 0`. -/
noncomputable def ex3Solution (L : ReduxLinear) (m : ℝ) : Ex3Vars where
  c := L.δ * (L.θ ^ 2 - 1) * m / L.D
  y := L.θ * ((L.δ * (1 + L.θ) + 2 * L.θ) * m / L.D)
  p := -((L.δ * (1 + L.θ) + 2 * L.θ) * m / L.D)
  e := (L.δ * (1 + L.θ) + 2 * L.θ) * m / L.D
  b := 2 * (L.θ - 1) * m / L.E
  cb := L.δ * (L.θ ^ 2 - 1) * m / L.D
  yb := -(L.θ * (L.δ * (L.θ ^ 2 - 1) * m / L.D)) / (L.θ + 1)
  pb := L.δ * (L.θ ^ 2 - 1) * m / L.D / (L.θ + 1)
  eb := (L.δ * (1 + L.θ) + 2 * L.θ) * m / L.D

/-- **Ex. 3 has exactly one solution** (O&R p. 713): `Ex3Eqm` holds IFF the unknowns are
`ex3Solution`, i.e. `c = c̄ = δ(θ²−1)m/D`, `e = ē = [δ(1+θ)+2θ]m/D`, `b̄ = 2(θ−1)m/(δ(1+θ)+2)`,
`y = θe`. -/
theorem ex3_iff (L : ReduxLinear) (m : ℝ) (w : Ex3Vars) : Ex3Eqm L m w ↔ w = ex3Solution L m := by
  have hθ := L.hθ
  have hδ := L.hδ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hθ1 : L.θ + 1 ≠ 0 := by linarith
  have hD := L.D_pos.ne'
  have hE := L.E_pos.ne'
  constructor
  · rintro ⟨hp, hy, hb, heu, hm, hmlr, hylr, hllr, hblr⟩
    rcases w with ⟨c, y, p, e, b, cb, yb, pb, eb⟩
    simp only at hp hy hb heu hm hmlr hylr hllr hblr
    have hee : e = eb ∧ e = m - cb := mm_no_overshooting hδ (by rw [heu]; exact hm) (by linarith)
    have hpb : (L.θ + 1) * pb = cb := by
      have h2 : L.θ * ((L.θ + 1) * pb - cb) = 0 := by
        linear_combination (-1 : ℝ) * hllr + (L.θ + 1) * hylr
      have := (mul_eq_zero.1 h2).resolve_left hθ0
      linarith
    have h2c : 2 * L.θ * cb = (L.θ + 1) * L.δ * b := by
      linear_combination (L.θ + 1) * hblr + hpb + hllr
    have hb' : b = (L.θ - 1) * m - L.θ * cb := by
      rw [hb, hy, hp, hee.2, heu]; ring
    have key : cb * L.D = L.δ * (L.θ ^ 2 - 1) * m := by
      unfold ReduxLinear.D
      rw [hb'] at h2c
      linear_combination h2c
    have hcb : cb = L.δ * (L.θ ^ 2 - 1) * m / L.D := by field_simp; linarith
    have he : e = (L.δ * (1 + L.θ) + 2 * L.θ) * m / L.D := by
      rw [hee.2, hcb]; unfold ReduxLinear.D; field_simp; ring
    simp only [ex3Solution, Ex3Vars.mk.injEq]
    refine ⟨by rw [← heu, hcb], by rw [hy, hp, he]; ring, by rw [hp, he], he, ?_, hcb, ?_, ?_,
      by rw [← hee.1, he]⟩
    · rw [hb', hcb]; unfold ReduxLinear.D ReduxLinear.E; field_simp; ring
    · have : yb = -(L.θ * cb) / (L.θ + 1) := by field_simp; linarith
      rw [this, hcb]
    · have : pb = cb / (L.θ + 1) := by field_simp; linarith
      rw [this, hcb]
  · rintro rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [ex3Solution, ReduxLinear.D, ReduxLinear.E] <;> field_simp <;> ring

/-- **Ex. 3 reproduces the two-country differentials** (O&R p. 713): the small-country
solution coincides with (65), (66) and the per-capita current-account differential of (67),
all of which are independent of `n` (`country_size_correction`), at `m* = 0`. -/
theorem ex3_matches_two_country (L : ReduxLinear) (m : ℝ) :
    (ex3Solution L m).e = (shortRunSolution L m 0).e ∧
    (ex3Solution L m).c = (shortRunSolution L m 0).c - (shortRunSolution L m 0).cs ∧
    (ex3Solution L m).b = (shortRunSolution L m 0).b / (1 - L.n) := by
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hE := L.E_pos.ne'
  simp only [ex3Solution, shortRunSolution]
  refine ⟨by ring, by ring, ?_⟩
  field_simp
  ring

/-- **Ex. 3: no welfare effect for the small country** (O&R p. 688 and p. 713): the first-order
change in real utility (75) at the solution is exactly `0` (the GG cancellation). -/
theorem ex3_welfare_zero (L : ReduxLinear) (m : ℝ) :
    dUR L (ex3Solution L m).c (ex3Solution L m).y (ex3Solution L m).cb
      (ex3Solution L m).yb = 0 := by
  have hθ := L.hθ
  have hδ := L.hδ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hθ1 : L.θ + 1 ≠ 0 := by linarith
  have hδ0 : L.δ ≠ 0 := hδ.ne'
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  simp only [dUR, ex3Solution, ReduxLinear.D]
  field_simp
  ring

end ObstfeldRogoff.StickyPriceModels.ReduxWelfare
