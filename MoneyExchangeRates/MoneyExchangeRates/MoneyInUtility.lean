/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Money in the utility function

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §8.3.1–§8.3.4
(pp. 530–538), §8.3.8 (pp. 551–553), §8.4.1.2 (p. 557) and Exercise 3 (pp. 600–601).

A small open economy's representative agent maximises `Σ β^s u(C_s, M_s/P_s)` (33) subject to
the period constraint (34). Writing `A_s = (1+r)B_s + M_{s−1}/P_s` for financial wealth, (34)
becomes `A_{s+1} = (1+r)(A_s + y_s − C_s − ι_s m_s)` with the user cost of money
`ι_s = 1 − (P_s/P_{s+1})/(1+r) = i_{s+1}/(1+i_{s+1})` (37) (`wealth_of_budget`). We prove:

* **the household optimum, exactly** (`isOptimal_iff`): for jointly concave, differentiable
  `u` with `u_C > 0`, an admissible (no-Ponzi) plan is optimal IFF it satisfies the Euler
  equation (35), the money-demand condition (37) and the transversality condition
  `liminf (1+r)^{−T}A_T = 0`. Sufficiency is the supporting-hyperplane argument against every
  no-Ponzi rival; necessity of (35) and (37) is by one-period perturbations, and necessity of
  the TVC by consuming more at date 0. (36) is (37) given (35) (`money_euler_iff`);
* **the intertemporal budget constraint (38)** and the limiting TVC for every optimal plan
  (`intertemporal_budget`), the book's form of the TVC (`book_tvc_identity`), the government's
  present-value constraint of fn 26 with the no-hyperdeflation condition (`government_pv`),
  (42), (43), and Exercise 3(a)–(b) (`aggregate_budget`, `national_pv`);
* the leisure derivation of MIU preferences (p. 531, fn 23);
* for `u = log C + v(M/P)`: the exact optimality conditions and constant consumption under
  `(1+r)β = 1` whatever the path of nominal rates; steady-state consumption (44); the
  steady-state nominal rate of fn 27;
* **CES-isoelastic preferences (§8.3.3)**: the index, the consumption-based price index and its
  minimum-cost characterisation (copied from Chapter 4); the gradient of `u`; money demand
  `M/P = ((1−γ)/γ)(1 + 1/i)^θ C`; `u_C = γ^{1/σ}C^{−1/σ}(P^C)^{(θ−σ)/σ}` on the demand curve; the
  Euler equation `C_{s+1} = (β(1+r))^σ (P^C_{s+1}/P^C_s)^{θ−σ} C_s` DERIVED from optimality; the
  book's individual consumption function; equilibrium consumption; and
  **the real–monetary dichotomy holds for every path of nominal rates iff `σ = θ`**
  (`dichotomy_iff`), with the separable form of `u` at `σ = θ`. This corrects the book's
  "outside this special case [`σ = θ = 1`]" (p. 536): the right condition is `σ = θ`;
* `σ = θ = 1`: existence of the optimum in closed form, `C_0 = γ(1−β)W`, and its necessity;
  in equilibrium `C_0 = (1−β)W` (Exercise 3(c));
* (39) ⇒ (40), and Exercise 3(c) for `θ = 1` with the book's product of real-rate factors;
* dollarization (§8.3.8): the currency-substitution condition, (67) with its corner, the
  inflation threshold, and the precise role of `a₀ > 1 − β` (`dollar_eventually_iff`);
* fixing the exchange rate with government spending (69) (§8.4.1.2).
-/

namespace ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility

open Real Filter Topology Set

/-! ## The household's budget -/

/-- The user (rental) cost of real balances, O&R (37), p. 533:
`ι_s = 1 − (P_s/P_{s+1})/(1 + r)`, which equals `i_{s+1}/(1 + i_{s+1})` under Fisher parity. -/
noncomputable def userCost (r : ℝ) (P : ℕ → ℝ) (s : ℕ) : ℝ := 1 - P s / P (s + 1) / (1 + r)

/-- Financial wealth at the start of date `s`, O&R (34), p. 532, written in real terms:
`A_s = (1 + r)B_s + M_{s−1}/P_s`. Given the plan `(C, m)` (consumption and real balances
`m_s = M_s/P_s`), exogenous disposable income `y_s = Y_s − T_s` and user costs `ι`, it evolves as
`A_{s+1} = (1 + r)(A_s + y_s − C_s − ι_s m_s)` (see `wealth_of_budget`). -/
noncomputable def wealth (r A0 : ℝ) (y ι C m : ℕ → ℝ) : ℕ → ℝ
  | 0 => A0
  | s + 1 => (1 + r) * (wealth r A0 y ι C m s + y s - C s - ι s * m s)

/-- The law of motion of wealth (O&R (34), p. 532). -/
theorem wealth_succ (r A0 : ℝ) (y ι C m : ℕ → ℝ) (s : ℕ) :
    wealth r A0 y ι C m (s + 1) = (1 + r) * (wealth r A0 y ι C m s + y s - C s - ι s * m s) :=
  rfl

/-- **The period budget constraint (34) in wealth form**, O&R p. 532. Money is indexed so that
`N s` is the nominal balance brought INTO date `s` (the book's `M_{s−1}`), so (34) reads
`B_{s+1} + N_{s+1}/P_s = (1 + r)B_s + N_s/P_s + Y_s − C_s − T_s`. With real balances
`m_s = N_{s+1}/P_s` and the user cost (37), the quantity `(1 + r)B_s + N_s/P_s` is `wealth`. -/
theorem wealth_of_budget {r : ℝ} (hr : 0 < 1 + r) {P B N Y T C : ℕ → ℝ} (hP : ∀ s, 0 < P s)
    (hbud : ∀ s, B (s + 1) + N (s + 1) / P s = (1 + r) * B s + N s / P s + Y s - C s - T s)
    (s : ℕ) :
    (1 + r) * B s + N s / P s = wealth r ((1 + r) * B 0 + N 0 / P 0) (fun s => Y s - T s)
      (userCost r P) C (fun s => N (s + 1) / P s) s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [wealth_succ, ← ih]
    have h := hbud s
    have hPs := (hP s).ne'
    have hPs1 := (hP (s + 1)).ne'
    unfold userCost
    field_simp
    field_simp at h
    linear_combination (1 + r) * P (s + 1) * h

/-- **Finite-horizon intertemporal budget identity**, O&R p. 534: for every horizon `T`,
`Σ_{s<T} (1+r)^{−s}(C_s + ι_s m_s) + (1+r)^{−T} A_T = A_0 + Σ_{s<T} (1+r)^{−s} y_s`. -/
theorem wealth_pv_identity {r : ℝ} (hr : 0 < 1 + r) (A0 : ℝ) (y ι C m : ℕ → ℝ) (T : ℕ) :
    ∑ s ∈ Finset.range T, (1 + r)⁻¹ ^ s * (C s + ι s * m s) + (1 + r)⁻¹ ^ T * wealth r A0 y ι C m T
      = A0 + ∑ s ∈ Finset.range T, (1 + r)⁻¹ ^ s * y s := by
  induction T with
  | zero => simp [wealth]
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, wealth_succ, pow_succ]
    have h1 : (1 + r)⁻¹ * (1 + r) = 1 := inv_mul_cancel₀ hr.ne'
    linear_combination ih + (1 + r)⁻¹ ^ T *
      (wealth r A0 y ι C m T + y T - C T - ι T * m T) * h1

/-- Wealth depends on the plan only through its past: two plans that agree from date `k` on
and have the same wealth at `k` have the same wealth at every later date (O&R (34)). -/
theorem wealth_congr_after {r A0 A0' : ℝ} {y ι C m C' m' : ℕ → ℝ} {k : ℕ}
    (hk : wealth r A0 y ι C m k = wealth r A0' y ι C' m' k)
    (hC : ∀ s, k ≤ s → C s = C' s) (hm : ∀ s, k ≤ s → m s = m' s) (n : ℕ) :
    wealth r A0 y ι C m (k + n) = wealth r A0' y ι C' m' (k + n) := by
  induction n with
  | zero => exact hk
  | succ n ih =>
    rw [← add_assoc, wealth_succ, wealth_succ, ih, hC _ (by omega), hm _ (by omega)]

/-- Raising date-0 consumption by `ε` lowers wealth at every date `T ≥ 1` by `(1 + r)^T ε`
(O&R (34)). -/
theorem wealth_shift_date0 {r A0 ε : ℝ} {y ι C m : ℕ → ℝ} (T : ℕ) :
    wealth r A0 y ι (fun s => if s = 0 then C 0 + ε else C s) m (T + 1)
      = wealth r A0 y ι C m (T + 1) - (1 + r) ^ (T + 1) * ε := by
  induction T with
  | zero => simp [wealth]; ring
  | succ T ih =>
    rw [wealth_succ, wealth_succ (C := C), ih]
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    ring

/-! ## Optimality -/

/-- Lifetime utility (33), O&R p. 530: `Σ_{s≥0} β^s u(C_s, M_s/P_s)`. -/
noncomputable def lifetimeUtility (u : ℝ → ℝ → ℝ) (β : ℝ) (C m : ℕ → ℝ) : ℝ :=
  ∑' s, β ^ s * u (C s) (m s)

/-- The no-Ponzi condition on a plan's wealth: `liminf (1+r)^{−T} A_T ≥ 0`, stated as
"for every `ε > 0`, eventually `(1+r)^{−T} A_T > −ε`" (O&R Supplement to Ch. 8, fn 2, p. 748,
and fn 31, p. 542). -/
def NoPonzi (r : ℝ) (A : ℕ → ℝ) : Prop := ∀ ε > 0, ∀ᶠ T in atTop, -ε < (1 + r)⁻¹ ^ T * A T

/-- The transversality condition on a plan's wealth, in its weakest (and, as we prove, exact)
form: `liminf (1+r)^{−T} A_T ≤ 0`, i.e. "for every `ε > 0`, frequently
`(1+r)^{−T} A_T < ε`" (O&R p. 534). Together with `NoPonzi` it says `liminf = 0`. -/
def Transversality (r : ℝ) (A : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ᶠ T in atTop, (1 + r)⁻¹ ^ T * A T < ε

/-- An admissible plan (O&R §8.3.2, pp. 532–534): strictly positive consumption and real
balances, summable lifetime utility, and no Ponzi scheme. -/
def Admissible (u : ℝ → ℝ → ℝ) (β r A0 : ℝ) (y ι C m : ℕ → ℝ) : Prop :=
  (∀ s, 0 < C s) ∧ (∀ s, 0 < m s) ∧ Summable (fun s => β ^ s * u (C s) (m s)) ∧
    NoPonzi r (wealth r A0 y ι C m)

/-- An optimal plan: admissible and at least as good as every admissible plan (O&R p. 532). -/
def IsOptimal (u : ℝ → ℝ → ℝ) (β r A0 : ℝ) (y ι C m : ℕ → ℝ) : Prop :=
  Admissible u β r A0 y ι C m ∧
    ∀ C' m', Admissible u β r A0 y ι C' m' → lifetimeUtility u β C' m' ≤ lifetimeUtility u β C m

/-- The gradient `(u_C, u_{M/P})` of the period utility as a continuous linear map on
`ℝ × ℝ` (O&R p. 531). -/
noncomputable def grad (a b : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- Evaluating the gradient map.
Context: O&R §8.3, pp. 530–538. -/
theorem grad_apply (a b : ℝ) (p : ℝ × ℝ) : grad a b p = a * p.1 + b * p.2 := by
  simp [grad]

/-- **Supporting hyperplane of a concave function** (the tool behind the sufficiency proofs,
O&R p. 533): if `U` is concave on a convex set `S` and differentiable at `x ∈ S` with derivative
`L`, then `U y ≤ U x + L (y − x)` for every `y ∈ S`. -/
theorem concave_le_tangent {U : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)} (hU : ConcaveOn ℝ S U)
    {x y : ℝ × ℝ} (hx : x ∈ S) (hy : y ∈ S) {L : ℝ × ℝ →L[ℝ] ℝ} (hL : HasFDerivAt U L x) :
    U y ≤ U x + L (y - x) := by
  set g : ℝ → ℝ := fun τ => U (x + τ • (y - x)) with hg
  have hline : HasDerivAt (fun τ : ℝ => x + τ • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hL' : HasFDerivAt U L (x + (0 : ℝ) • (y - x)) := by simpa using hL
  have hgd : HasDerivAt g (L (y - x)) 0 := hL'.comp_hasDerivAt (0 : ℝ) hline
  have hslope := hasDerivAt_iff_tendsto_slope.mp hgd
  have hslope' : Tendsto (slope g 0) (𝓝[>] 0) (𝓝 (L (y - x))) :=
    hslope.mono_left (nhdsWithin_mono _ (fun τ (hτ : 0 < τ) => ne_of_gt hτ))
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), U y - U x ≤ slope g 0 τ := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with τ hτ
    obtain ⟨h0, h1⟩ := hτ
    have hc := hU.2 hx hy (show (0 : ℝ) ≤ 1 - τ by linarith) h0.le (by ring)
    have heq : (1 - τ) • x + τ • y = x + τ • (y - x) := by
      rw [sub_smul, one_smul, smul_sub]; abel
    rw [heq, smul_eq_mul, smul_eq_mul] at hc
    rw [slope_def_field, hg]
    simp only [zero_smul, add_zero, sub_zero]
    rw [le_div_iff₀ h0]
    linarith
  have := ge_of_tendsto hslope' hev
  linarith

/-- The derivative of the period utility along a straight line through `(c, k)` in the
direction `(a, b)` (used for the one-period perturbations, O&R p. 533). -/
theorem hasDerivAt_line {u : ℝ → ℝ → ℝ} {c k uc um : ℝ}
    (hd : HasFDerivAt (fun p : ℝ × ℝ => u p.1 p.2) (grad uc um) (c, k)) (a b : ℝ) :
    HasDerivAt (fun ε => u (c + ε * a) (k + ε * b)) (uc * a + um * b) 0 := by
  have hline : HasDerivAt (fun ε : ℝ => ((c, k) : ℝ × ℝ) + ε • ((a, b) : ℝ × ℝ)) (a, b) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ((a, b) : ℝ × ℝ)).const_add (c, k)
  have hd' : HasFDerivAt (fun p : ℝ × ℝ => u p.1 p.2) (grad uc um)
      (((c, k) : ℝ × ℝ) + (0 : ℝ) • ((a, b) : ℝ × ℝ)) := by simpa using hd
  have h := hd'.comp_hasDerivAt (0 : ℝ) hline
  rw [grad_apply] at h
  convert h using 1
  funext ε
  simp [smul_eq_mul, mul_comm]

/-- The partial derivative of the period utility with respect to consumption, read off the
joint derivative (O&R p. 531). -/
theorem hasDerivAt_fst {u : ℝ → ℝ → ℝ} {c k uc um : ℝ}
    (hd : HasFDerivAt (fun p : ℝ × ℝ => u p.1 p.2) (grad uc um) (c, k)) :
    HasDerivAt (fun c' => u c' k) uc c := by
  have h := hd.comp_hasDerivAt c ((hasDerivAt_id c).prodMk (hasDerivAt_const c k))
  simpa [grad_apply, Function.comp_def] using h

/-- The partial derivative of the period utility with respect to real balances.
Context: O&R §8.3, pp. 530–538. -/
theorem hasDerivAt_snd {u : ℝ → ℝ → ℝ} {c k uc um : ℝ}
    (hd : HasFDerivAt (fun p : ℝ × ℝ => u p.1 p.2) (grad uc um) (c, k)) :
    HasDerivAt (fun k' => u c k') um k := by
  have h := hd.comp_hasDerivAt k ((hasDerivAt_const k c).prodMk (hasDerivAt_id k))
  simpa [grad_apply, Function.comp_def] using h

/-- `u_C > 0` (O&R p. 531) makes utility strictly increasing in consumption. -/
theorem strictMonoOn_of_uC_pos {u uC um : ℝ → ℝ → ℝ}
    (hdiff : ∀ c k, 0 < c → 0 < k →
      HasFDerivAt (fun p : ℝ × ℝ => u p.1 p.2) (grad (uC c k) (um c k)) (c, k))
    (huC : ∀ c k, 0 < c → 0 < k → 0 < uC c k) {k : ℝ} (hk : 0 < k) :
    StrictMonoOn (fun c => u c k) (Ioi 0) := by
  have hder : ∀ c, 0 < c → HasDerivAt (fun c' => u c' k) (uC c k) c :=
    fun c hc => hasDerivAt_fst (hdiff c k hc hk)
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun x hx => (hder x hx).continuousAt.continuousWithinAt) (fun x hx => ?_)
  rw [interior_Ioi] at hx
  rw [(hder x hx).deriv]
  exact huC x k hx hk

/-- Plans that agree before date `k` have the same wealth at `k` (O&R (34)). -/
theorem wealth_congr_before {r A0 : ℝ} {y ι C m C' m' : ℕ → ℝ} {k : ℕ}
    (hC : ∀ t, t < k → C t = C' t) (hm : ∀ t, t < k → m t = m' t) :
    wealth r A0 y ι C m k = wealth r A0 y ι C' m' k := by
  have key : ∀ n, n ≤ k → wealth r A0 y ι C m n = wealth r A0 y ι C' m' n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [wealth_succ, wealth_succ, ih (by omega), hC n (by omega), hm n (by omega)]
  exact key k le_rfl

/-- Plans with the same period expenditure `C_s + ι_s m_s` have the same wealth path
(O&R (34)). -/
theorem wealth_congr_expenditure {r A0 : ℝ} {y ι C m C' m' : ℕ → ℝ}
    (h : ∀ t, C' t + ι t * m' t = C t + ι t * m t) (T : ℕ) :
    wealth r A0 y ι C' m' T = wealth r A0 y ι C m T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [wealth_succ, wealth_succ, ih]
    linear_combination (-(1 + r)) * h T

/-- The no-Ponzi condition depends only on the tail of the wealth path.
Context: O&R §8.3, pp. 530–538. -/
theorem noPonzi_congr {r : ℝ} {A A' : ℕ → ℝ} (h : NoPonzi r A) (heq : ∀ᶠ T in atTop, A' T = A T) :
    NoPonzi r A' := by
  intro ε hε
  filter_upwards [h ε hε, heq] with T h1 h2
  rw [h2]
  exact h1

/-- A finite modification of a summable sequence (copied from the `SmallOpenEconomyDynamics`
project's `ConsumptionOptimality`, so that this project builds on its own): if `g` agrees with
`f` off a finite set `S`, then `g` is summable and `Σ g = Σ f + Σ_{t∈S} (g t − f t)`.
Context: O&R §8.3, pp. 530–538. -/
theorem tsum_eq_add_of_eqOn_compl {f g : ℕ → ℝ} (hf : Summable f) (S : Finset ℕ)
    (hfg : ∀ t, t ∉ S → g t = f t) :
    Summable g ∧ ∑' t, g t = ∑' t, f t + ∑ t ∈ S, (g t - f t) := by
  have hd : Summable fun t => g t - f t :=
    summable_of_ne_finset_zero (s := S) fun t ht => by rw [hfg t ht, sub_self]
  have hg : g = fun t => f t + (g t - f t) := by funext t; ring
  refine ⟨hg ▸ hf.add hd, ?_⟩
  have h1 : ∑' t, (g t - f t) = ∑ t ∈ S, (g t - f t) :=
    tsum_eq_sum (f := fun t => g t - f t) (s := S) fun t ht => by rw [hfg t ht, sub_self]
  calc ∑' t, g t = ∑' t, (f t + (g t - f t)) := tsum_congr fun t => by ring
    _ = _ := by rw [hf.tsum_add hd, h1]

/-- **Iterated consumption Euler equation** (35), O&R p. 533: if
`λ_s = (1 + r) β λ_{s+1}` for all `s`, then `β^s λ_s = λ_0 (1 + r)^{−s}`. -/
theorem discounted_marginal_utility {β r : ℝ} (hr : 0 < 1 + r) {lam : ℕ → ℝ}
    (he : ∀ s, lam s = (1 + r) * β * lam (s + 1)) (s : ℕ) :
    β ^ s * lam s = lam 0 * (1 + r)⁻¹ ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 : (1 + r)⁻¹ * (1 + r) = 1 := inv_mul_cancel₀ hr.ne'
    rw [pow_succ, pow_succ]
    linear_combination (1 + r)⁻¹ * ih - β ^ s * (1 + r)⁻¹ * he s - β ^ s * β * lam (s + 1) * h1

/-- **Sufficiency of the first-order conditions and the transversality condition**
(O&R (35)–(37) and the TVC of p. 534, made precise). Let `u` be jointly concave on the positive
quadrant and differentiable with gradient `(u_C, u_{M/P})`. An admissible plan satisfying the
consumption Euler equation (35), the money-demand condition (37) `u_{M/P} = ι u_C` and the
transversality condition is optimal among ALL admissible (no-Ponzi) plans. Proof: the
supporting-hyperplane inequality, the iterated Euler equation and the finite-horizon budget
identity bound the utility gain of any rival by `u_C(0)((1+r)^{−T}A_T − (1+r)^{−T}A'_T)`. -/
theorem isOptimal_of_foc {u uC um : ℝ → ℝ → ℝ} {β r A0 : ℝ} {y ι C m : ℕ → ℝ}
    (hβ : 0 < β) (hr : 0 < 1 + r)
    (hconc : ConcaveOn ℝ (Ioi 0 ×ˢ Ioi 0) (fun p : ℝ × ℝ => u p.1 p.2))
    (hdiff : ∀ c k, 0 < c → 0 < k →
      HasFDerivAt (fun p : ℝ × ℝ => u p.1 p.2) (grad (uC c k) (um c k)) (c, k))
    (hadm : Admissible u β r A0 y ι C m) (hpos : 0 ≤ uC (C 0) (m 0))
    (heuler : ∀ s, uC (C s) (m s) = (1 + r) * β * uC (C (s + 1)) (m (s + 1)))
    (hmoney : ∀ s, um (C s) (m s) = ι s * uC (C s) (m s))
    (htvc : Transversality r (wealth r A0 y ι C m)) :
    IsOptimal u β r A0 y ι C m := by
  refine ⟨hadm, fun C' m' hadm' => ?_⟩
  obtain ⟨hC, hm, hsum, -⟩ := hadm
  obtain ⟨hC', hm', hsum', hnp'⟩ := hadm'
  set lam0 := uC (C 0) (m 0) with hlam0
  set d := (1 + r)⁻¹ with hd
  have hdisc : ∀ s, β ^ s * uC (C s) (m s) = lam0 * d ^ s :=
    discounted_marginal_utility hr (lam := fun s => uC (C s) (m s)) heuler
  have hterm : ∀ s, β ^ s * u (C' s) (m' s) - β ^ s * u (C s) (m s) ≤
      lam0 * (d ^ s * (C' s + ι s * m' s) - d ^ s * (C s + ι s * m s)) := by
    intro s
    have t := concave_le_tangent hconc (x := (C s, m s)) (y := (C' s, m' s))
      ⟨hC s, hm s⟩ ⟨hC' s, hm' s⟩ (hdiff _ _ (hC s) (hm s))
    simp only [grad_apply, Prod.fst_sub, Prod.snd_sub] at t
    rw [hmoney s] at t
    have hb := pow_pos hβ s
    have h2 := mul_le_mul_of_nonneg_left t hb.le
    have key : β ^ s * (uC (C s) (m s) * (C' s - C s) + ι s * uC (C s) (m s) * (m' s - m s))
        = lam0 * (d ^ s * (C' s + ι s * m' s) - d ^ s * (C s + ι s * m s)) := by
      linear_combination ((C' s - C s) + ι s * (m' s - m s)) * hdisc s
    linarith
  have hpartial : ∀ T, ∑ s ∈ Finset.range T, (β ^ s * u (C' s) (m' s) - β ^ s * u (C s) (m s)) ≤
      lam0 * (d ^ T * wealth r A0 y ι C m T - d ^ T * wealth r A0 y ι C' m' T) := by
    intro T
    have h1 := wealth_pv_identity hr A0 y ι C m T
    have h2 := wealth_pv_identity hr A0 y ι C' m' T
    have hle := Finset.sum_le_sum fun s (_ : s ∈ Finset.range T) => hterm s
    have heq : ∑ i ∈ Finset.range T, d ^ i * (C' i + ι i * m' i) -
        ∑ i ∈ Finset.range T, d ^ i * (C i + ι i * m i) =
        d ^ T * wealth r A0 y ι C m T - d ^ T * wealth r A0 y ι C' m' T := by linarith
    have hR : ∑ i ∈ Finset.range T, lam0 * (d ^ i * (C' i + ι i * m' i) -
        d ^ i * (C i + ι i * m i)) =
        lam0 * (d ^ T * wealth r A0 y ι C m T - d ^ T * wealth r A0 y ι C' m' T) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, heq]
    exact hle.trans hR.le
  have hlim : Tendsto (fun T => ∑ s ∈ Finset.range T, (β ^ s * u (C' s) (m' s) -
      β ^ s * u (C s) (m s))) atTop
      (𝓝 (lifetimeUtility u β C' m' - lifetimeUtility u β C m)) :=
    (hsum'.hasSum.sub hsum.hasSum).tendsto_sum_nat
  by_contra hlt
  push Not at hlt
  set δ := lifetimeUtility u β C' m' - lifetimeUtility u β C m with hδdef
  have hδ : 0 < δ := by linarith
  have hl1 : 0 < lam0 + 1 := by linarith
  set ε := δ / (4 * (lam0 + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hsmall : 2 * lam0 * ε < δ := by
    have h4 : ε * (4 * (lam0 + 1)) = δ := by rw [hεdef]; field_simp
    nlinarith
  obtain ⟨T, hT3, hT1, hT2⟩ :=
    ((htvc ε hε).and_eventually ((hlim.eventually (lt_mem_nhds hsmall)).and (hnp' ε hε))).exists
  have hP := hpartial T
  have hab : d ^ T * wealth r A0 y ι C m T - d ^ T * wealth r A0 y ι C' m' T ≤ 2 * ε := by
    linarith
  have := mul_le_mul_of_nonneg_left hab hpos
  linarith

/-- **Necessity of the consumption Euler equation** (35), O&R p. 533: at an optimal plan,
`u_C(C_s, m_s) = (1 + r) β u_C(C_{s+1}, m_{s+1})` for every `s`. Proof: shift `ε` of
consumption from `s` to `s + 1` (repaid with interest); wealth changes only at date `s + 1`. -/
theorem euler_of_optimal {u uC um : ℝ → ℝ → ℝ} {β r A0 : ℝ} {y ι C m : ℕ → ℝ}
    (hβ : 0 < β)
    (hdiff : ∀ c k, 0 < c → 0 < k →
      HasFDerivAt (fun p : ℝ × ℝ => u p.1 p.2) (grad (uC c k) (um c k)) (c, k))
    (hopt : IsOptimal u β r A0 y ι C m) (s : ℕ) :
    uC (C s) (m s) = (1 + r) * β * uC (C (s + 1)) (m (s + 1)) := by
  obtain ⟨⟨hC, hm, hsum, hnp⟩, hmax⟩ := hopt
  let D : ℝ → ℕ → ℝ := fun ε t =>
    if t = s then C s + ε * (-1) else if t = s + 1 then C (s + 1) + ε * (1 + r) else C t
  have hne : s + 1 ≠ s := Nat.succ_ne_self s
  have hDs : ∀ ε, D ε s = C s + ε * (-1) := fun ε => by simp [D]
  have hDs1 : ∀ ε, D ε (s + 1) = C (s + 1) + ε * (1 + r) := fun ε => by simp [D]
  have hoff : ∀ ε t, t ∉ ({s, s + 1} : Finset ℕ) → D ε t = C t := fun ε t ht => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    simp [D, ht.1, ht.2]
  -- wealth is unchanged from date `s + 2` on
  have hw : ∀ ε n, wealth r A0 y ι (D ε) m (s + 2 + n) = wealth r A0 y ι C m (s + 2 + n) := by
    intro ε n
    refine wealth_congr_after ?_ (fun t ht => hoff ε t (by simp; omega)) (fun _ _ => rfl) n
    have hbef : wealth r A0 y ι (D ε) m s = wealth r A0 y ι C m s :=
      wealth_congr_before (fun t ht => hoff ε t (by simp; omega)) (fun _ _ => rfl)
    rw [show s + 2 = s + 1 + 1 by ring, wealth_succ, wealth_succ (C := C), wealth_succ,
      wealth_succ (C := C), hbef, hDs, hDs1]
    ring
  have hnpD : ∀ ε, NoPonzi r (wealth r A0 y ι (D ε) m) := fun ε => by
    refine noPonzi_congr hnp ?_
    filter_upwards [eventually_ge_atTop (s + 2)] with T hT
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
    exact hw ε n
  have huD : ∀ ε, Summable (fun t => β ^ t * u (D ε t) (m t)) ∧ lifetimeUtility u β (D ε) m =
      lifetimeUtility u β C m + (β ^ s * u (C s + ε * (-1)) (m s) - β ^ s * u (C s) (m s)) +
        (β ^ (s + 1) * u (C (s + 1) + ε * (1 + r)) (m (s + 1)) -
          β ^ (s + 1) * u (C (s + 1)) (m (s + 1))) := by
    intro ε
    obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hsum {s, s + 1}
      (g := fun t => β ^ t * u (D ε t) (m t)) fun t ht => by simp only [hoff ε t ht]
    refine ⟨h1, ?_⟩
    unfold lifetimeUtility
    rw [h2, Finset.sum_pair hne.symm, hDs, hDs1]
    ring
  have hev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C s + ε * (-1) :=
    ((by fun_prop : Continuous fun ε : ℝ => C s + ε * (-1)).tendsto 0).eventually
      (lt_mem_nhds (by simpa using hC s))
  have hev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C (s + 1) + ε * (1 + r) :=
    ((by fun_prop : Continuous fun ε : ℝ => C (s + 1) + ε * (1 + r)).tendsto 0).eventually
      (lt_mem_nhds (by simpa using hC (s + 1)))
  set φ : ℝ → ℝ := fun ε => β ^ s * u (C s + ε * (-1)) (m s + ε * 0) +
    β ^ (s + 1) * u (C (s + 1) + ε * (1 + r)) (m (s + 1) + ε * 0) with hφ
  have hloc : IsLocalMax φ 0 := by
    filter_upwards [hev1, hev2] with ε h1 h2
    have hpos : ∀ t, 0 < D ε t := fun t => by
      by_cases ht : t = s
      · rw [ht, hDs]; exact h1
      by_cases ht1 : t = s + 1
      · rw [ht1, hDs1]; exact h2
      rw [hoff ε t (by simp [ht, ht1])]
      exact hC t
    have := hmax _ _ ⟨hpos, hm, (huD ε).1, hnpD ε⟩
    rw [(huD ε).2] at this
    simp only [φ, mul_zero, add_zero, zero_mul]
    linarith
  have hA := (hasDerivAt_line (hdiff _ _ (hC s) (hm s)) (-1) 0).const_mul (β ^ s)
  have hB := (hasDerivAt_line (hdiff _ _ (hC (s + 1)) (hm (s + 1))) (1 + r) 0).const_mul
    (β ^ (s + 1))
  have h0 := hloc.hasDerivAt_eq_zero (hA.add hB)
  rw [pow_succ] at h0
  have hβs : 0 < β ^ s := pow_pos hβ s
  have h3 : β ^ s * (uC (C s) (m s) - (1 + r) * β * uC (C (s + 1)) (m (s + 1))) = 0 := by
    linarith
  have := (mul_eq_zero.1 h3).resolve_left hβs.ne'
  linarith

/-- **Necessity of the money-demand condition** (37), O&R p. 533: at an optimal plan,
`u_{M/P}(C_s, m_s) = ι_s u_C(C_s, m_s)`. Proof: hold `ε` more real balances and consume `ι_s ε`
less; period expenditure, hence the whole wealth path, is unchanged. -/
theorem money_foc_of_optimal {u uC um : ℝ → ℝ → ℝ} {β r A0 : ℝ} {y ι C m : ℕ → ℝ}
    (hβ : 0 < β)
    (hdiff : ∀ c k, 0 < c → 0 < k →
      HasFDerivAt (fun p : ℝ × ℝ => u p.1 p.2) (grad (uC c k) (um c k)) (c, k))
    (hopt : IsOptimal u β r A0 y ι C m) (s : ℕ) :
    um (C s) (m s) = ι s * uC (C s) (m s) := by
  obtain ⟨⟨hC, hm, hsum, hnp⟩, hmax⟩ := hopt
  let DC : ℝ → ℕ → ℝ := fun ε t => if t = s then C s + ε * (-ι s) else C t
  let Dm : ℝ → ℕ → ℝ := fun ε t => if t = s then m s + ε * 1 else m t
  have hexp : ∀ ε t, DC ε t + ι t * Dm ε t = C t + ι t * m t := fun ε t => by
    by_cases ht : t = s
    · subst ht; simp [DC, Dm]; ring
    · simp [DC, Dm, ht]
  have hoffC : ∀ ε t, t ∉ ({s} : Finset ℕ) → DC ε t = C t := fun ε t ht => by
    simp only [Finset.mem_singleton] at ht; simp [DC, ht]
  have hoffm : ∀ ε t, t ∉ ({s} : Finset ℕ) → Dm ε t = m t := fun ε t ht => by
    simp only [Finset.mem_singleton] at ht; simp [Dm, ht]
  have huD : ∀ ε, Summable (fun t => β ^ t * u (DC ε t) (Dm ε t)) ∧
      lifetimeUtility u β (DC ε) (Dm ε) = lifetimeUtility u β C m +
        (β ^ s * u (C s + ε * (-ι s)) (m s + ε * 1) - β ^ s * u (C s) (m s)) := by
    intro ε
    obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hsum {s}
      (g := fun t => β ^ t * u (DC ε t) (Dm ε t)) fun t ht => by
        simp only [hoffC ε t ht, hoffm ε t ht]
    refine ⟨h1, ?_⟩
    unfold lifetimeUtility
    rw [h2, Finset.sum_singleton]
    simp [DC, Dm]
  have hev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C s + ε * (-ι s) :=
    ((by fun_prop : Continuous fun ε : ℝ => C s + ε * (-ι s)).tendsto 0).eventually
      (lt_mem_nhds (by simpa using hC s))
  have hev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < m s + ε * 1 :=
    ((by fun_prop : Continuous fun ε : ℝ => m s + ε * 1).tendsto 0).eventually
      (lt_mem_nhds (by simpa using hm s))
  have hloc : IsLocalMax (fun ε => β ^ s * u (C s + ε * (-ι s)) (m s + ε * 1)) 0 := by
    filter_upwards [hev1, hev2] with ε h1 h2
    have hposC : ∀ t, 0 < DC ε t := fun t => by
      by_cases ht : t = s
      · subst ht; simpa [DC] using h1
      · simpa [DC, ht] using hC t
    have hposm : ∀ t, 0 < Dm ε t := fun t => by
      by_cases ht : t = s
      · subst ht; simpa [Dm] using h2
      · simpa [Dm, ht] using hm t
    have hnpD : NoPonzi r (wealth r A0 y ι (DC ε) (Dm ε)) := by
      intro e he
      filter_upwards [hnp e he] with T hT
      rw [wealth_congr_expenditure (hexp ε) T]
      exact hT
    have := hmax _ _ ⟨hposC, hposm, (huD ε).1, hnpD⟩
    rw [(huD ε).2] at this
    simp only [add_zero, zero_mul]
    linarith
  have hA := (hasDerivAt_line (hdiff _ _ (hC s) (hm s)) (-ι s) 1).const_mul (β ^ s)
  have h0 := hloc.hasDerivAt_eq_zero hA
  have hβs : 0 < β ^ s := pow_pos hβ s
  have h3 : β ^ s * (um (C s) (m s) - ι s * uC (C s) (m s)) = 0 := by linarith
  have := (mul_eq_zero.1 h3).resolve_left hβs.ne'
  linarith

/-- **Necessity of the transversality condition** (O&R p. 534 and fn 31, p. 542): at an
optimal plan, `liminf (1+r)^{−T} A_T ≤ 0`, provided utility is strictly increasing in
consumption (`u_C > 0`). Otherwise wealth would eventually exceed some `ε > 0` in present
value, and consuming `ε` more at date 0 would keep the no-Ponzi condition and raise utility. -/
theorem transversality_of_optimal {u : ℝ → ℝ → ℝ} {β r A0 : ℝ} {y ι C m : ℕ → ℝ}
    (hr : 0 < 1 + r) (hmono : ∀ k, 0 < k → StrictMonoOn (fun c => u c k) (Ioi 0))
    (hopt : IsOptimal u β r A0 y ι C m) : Transversality r (wealth r A0 y ι C m) := by
  obtain ⟨⟨hC, hm, hsum, _⟩, hmax⟩ := hopt
  intro ε hε
  by_contra h
  rw [not_frequently] at h
  set C' : ℕ → ℝ := fun s => if s = 0 then C 0 + ε else C s with hC'
  have hoff : ∀ t, t ∉ ({0} : Finset ℕ) → C' t = C t := fun t ht => by
    simp only [Finset.mem_singleton] at ht; simp [hC', ht]
  obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hsum {0}
    (g := fun t => β ^ t * u (C' t) (m t)) fun t ht => by simp only [hoff t ht]
  have hpos : ∀ t, 0 < C' t := fun t => by
    by_cases ht : t = 0
    · subst ht; simp [hC']; linarith [hC 0]
    · simpa [hC', ht] using hC t
  have hnp' : NoPonzi r (wealth r A0 y ι C' m) := by
    intro e he
    filter_upwards [h, eventually_ge_atTop 1] with T hT hT1
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hT1
    push Not at hT
    rw [wealth_shift_date0]
    have hk : (1 + r)⁻¹ ^ (n + 1) * (1 + r) ^ (n + 1) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
    have : (1 + r)⁻¹ ^ (n + 1) * (wealth r A0 y ι C m (n + 1) - (1 + r) ^ (n + 1) * ε)
        = (1 + r)⁻¹ ^ (n + 1) * wealth r A0 y ι C m (n + 1) - ε := by
      linear_combination (-ε) * hk
    rw [this]
    linarith
  have hgain := hmax C' m ⟨hpos, hm, h1, hnp'⟩
  unfold lifetimeUtility at hgain
  rw [h2, Finset.sum_singleton] at hgain
  have hu : u (C 0) (m 0) < u (C 0 + ε) (m 0) :=
    hmono (m 0) (hm 0) (mem_Ioi.2 (hC 0)) (mem_Ioi.2 (by linarith [hC 0])) (by linarith)
  simp [hC'] at hgain
  linarith

/-- **Exact characterisation of the household optimum** (O&R §8.3.2, pp. 532–534, made precise):
with `u` jointly concave, differentiable and strictly increasing in consumption (`u_C > 0`),
an admissible plan is optimal IF AND ONLY IF it satisfies the Euler equation (35), the
money-demand condition (37) and the transversality condition. -/
theorem isOptimal_iff {u uC um : ℝ → ℝ → ℝ} {β r A0 : ℝ} {y ι C m : ℕ → ℝ}
    (hβ : 0 < β) (hr : 0 < 1 + r)
    (hconc : ConcaveOn ℝ (Ioi 0 ×ˢ Ioi 0) (fun p : ℝ × ℝ => u p.1 p.2))
    (hdiff : ∀ c k, 0 < c → 0 < k →
      HasFDerivAt (fun p : ℝ × ℝ => u p.1 p.2) (grad (uC c k) (um c k)) (c, k))
    (huC : ∀ c k, 0 < c → 0 < k → 0 < uC c k) :
    IsOptimal u β r A0 y ι C m ↔ Admissible u β r A0 y ι C m ∧
      (∀ s, uC (C s) (m s) = (1 + r) * β * uC (C (s + 1)) (m (s + 1))) ∧
      (∀ s, um (C s) (m s) = ι s * uC (C s) (m s)) ∧ Transversality r (wealth r A0 y ι C m) := by
  constructor
  · intro hopt
    exact ⟨hopt.1, euler_of_optimal hβ hdiff hopt, money_foc_of_optimal hβ hdiff hopt,
      transversality_of_optimal hr (fun k hk => strictMonoOn_of_uC_pos hdiff huC hk) hopt⟩
  · rintro ⟨hadm, he, hmo, htvc⟩
    exact isOptimal_of_foc hβ hr hconc hdiff hadm (huC _ _ (hadm.1 0) (hadm.2.1 0)).le he hmo htvc

/-! ## The money-demand condition, the intertemporal budget and the TVC -/

/-- **Fisher parity and the user cost**, O&R (37), p. 533: if `1 + i_{s+1} = (1+r)P_{s+1}/P_s`
then `1 − (P_s/P_{s+1})/(1+r) = i_{s+1}/(1 + i_{s+1})`. -/
theorem userCost_eq_fisher {r i : ℝ} {P : ℕ → ℝ} (s : ℕ) (hr : 0 < 1 + r) (hP : ∀ s, 0 < P s)
    (hfisher : 1 + i = (1 + r) * P (s + 1) / P s) : userCost r P s = i / (1 + i) := by
  have hPs := (hP s).ne'
  have hPs1 := (hP (s + 1)).ne'
  have hi : i = (1 + r) * P (s + 1) / P s - 1 := by linarith
  subst hi
  unfold userCost
  field_simp
  ring

/-- **The money Euler equation (36) is (37) given (35)**, O&R pp. 533: with
`u_C(s) = (1+r)β u_C(s+1)`, the condition `u_C(s)/P_s = u_{M/P}(s)/P_s + β u_C(s+1)/P_{s+1}`
holds iff `u_{M/P}(s) = ι_s u_C(s)`. -/
theorem money_euler_iff {r β uCs uCs1 ums : ℝ} {P : ℕ → ℝ} {s : ℕ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (heuler : uCs = (1 + r) * β * uCs1) :
    uCs / P s = ums / P s + β * uCs1 / P (s + 1) ↔ ums = userCost r P s * uCs := by
  have hPs := (hP s).ne'
  have hPs1 := (hP (s + 1)).ne'
  have hr' := hr.ne'
  have hb : β * uCs1 / P (s + 1) = uCs / ((1 + r) * P (s + 1)) := by
    rw [heuler]; field_simp
  unfold userCost
  rw [hb]
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- A path whose present value tends to zero satisfies the transversality condition.
Context: O&R §8.3, pp. 530–538. -/
theorem transversality_of_tendsto {r : ℝ} {A : ℕ → ℝ}
    (h : Tendsto (fun T => (1 + r)⁻¹ ^ T * A T) atTop (𝓝 0)) : Transversality r A :=
  fun _ hε => (h.eventually (gt_mem_nhds hε)).frequently

/-- A path whose present value tends to zero satisfies the no-Ponzi condition.
Context: O&R §8.3, pp. 530–538. -/
theorem noPonzi_of_tendsto {r : ℝ} {A : ℕ → ℝ}
    (h : Tendsto (fun T => (1 + r)⁻¹ ^ T * A T) atTop (𝓝 0)) : NoPonzi r A :=
  fun _ hε => h.eventually (lt_mem_nhds (by linarith))

/-- **The intertemporal budget constraint (38) and the limiting TVC**, O&R p. 534. With
nonnegative user costs (nonnegative nominal rates) and summable discounted income, every
no-Ponzi plan satisfying the transversality condition has `(1+r)^{−T}A_T → 0`, and its
expenditure on consumption and on renting real balances has present value exactly equal to
initial wealth plus the present value of income: (38). -/
theorem intertemporal_budget {r A0 : ℝ} {y ι C m : ℕ → ℝ} (hr : 0 < 1 + r) (hC : ∀ s, 0 < C s)
    (hm : ∀ s, 0 < m s) (hι : ∀ s, 0 ≤ ι s) (hy : Summable (fun s => (1 + r)⁻¹ ^ s * y s))
    (hnp : NoPonzi r (wealth r A0 y ι C m)) (htvc : Transversality r (wealth r A0 y ι C m)) :
    Tendsto (fun T => (1 + r)⁻¹ ^ T * wealth r A0 y ι C m T) atTop (𝓝 0) ∧
      HasSum (fun s => (1 + r)⁻¹ ^ s * (C s + ι s * m s))
        (A0 + ∑' s, (1 + r)⁻¹ ^ s * y s) := by
  set d := (1 + r)⁻¹ with hd
  have hd0 : 0 < d := inv_pos.2 hr
  set e : ℕ → ℝ := fun s => d ^ s * (C s + ι s * m s) with he
  have he0 : ∀ s, 0 ≤ e s := fun s =>
    mul_nonneg (pow_pos hd0 s).le (add_nonneg (hC s).le (mul_nonneg (hι s) (hm s).le))
  have hY := hy.hasSum.tendsto_sum_nat
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hY)
  have hident := wealth_pv_identity hr A0 y ι C m
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hnp 1 one_pos)
  have hbound : ∀ n, ∑ s ∈ Finset.range n, e s ≤ A0 + B + 1 := by
    intro n
    have hmono : ∑ s ∈ Finset.range n, e s ≤ ∑ s ∈ Finset.range (max n N), e s :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left n N))
        (fun s _ _ => he0 s)
    have h1 := hident (max n N)
    have h2 := hN (max n N) (le_max_right n N)
    have h3 := hB _ (Set.mem_range_self (max n N))
    rw [Real.norm_eq_abs] at h3
    have h4 := (abs_le.1 h3).2
    linarith
  have hes : Summable e := summable_of_sum_range_le he0 hbound
  have hE := hes.hasSum.tendsto_sum_nat
  have hlim : Tendsto (fun T => d ^ T * wealth r A0 y ι C m T) atTop
      (𝓝 (A0 + ∑' s, d ^ s * y s - ∑' s, e s)) := by
    have := (tendsto_const_nhds (x := A0)).add hY |>.sub hE
    refine this.congr fun T => ?_
    have := hident T
    simp only [he] at this ⊢
    linarith
  set L := A0 + ∑' s, d ^ s * y s - ∑' s, e s with hL
  have hL0 : 0 ≤ L := by
    by_contra hneg
    push Not at hneg
    obtain ⟨T, hT1, hT2⟩ := ((hlim.eventually (gt_mem_nhds (show L < L / 2 by linarith))).and
      (hnp (-(L / 2)) (by linarith))).exists
    linarith
  have hL1 : L ≤ 0 := by
    by_contra hpos
    push Not at hpos
    obtain ⟨T, hT1, hT2⟩ := ((htvc (L / 2) (by linarith)).and_eventually
      (hlim.eventually (lt_mem_nhds (show L / 2 < L by linarith)))).exists
    linarith
  have hL00 : L = 0 := le_antisymm hL1 hL0
  refine ⟨hL00 ▸ hlim, ?_⟩
  have : ∑' s, e s = A0 + ∑' s, d ^ s * y s := by linarith
  rw [← this]
  exact hes.hasSum

/-- **Converse**: if the present value (38) of expenditure equals initial wealth plus the present
value of income, then `(1+r)^{−T}A_T → 0`, so the plan satisfies the TVC (O&R p. 534). -/
theorem tendsto_wealth_of_budget {r A0 : ℝ} {y ι C m : ℕ → ℝ} (hr : 0 < 1 + r)
    (hy : Summable (fun s => (1 + r)⁻¹ ^ s * y s))
    (hpv : HasSum (fun s => (1 + r)⁻¹ ^ s * (C s + ι s * m s))
      (A0 + ∑' s, (1 + r)⁻¹ ^ s * y s)) :
    Tendsto (fun T => (1 + r)⁻¹ ^ T * wealth r A0 y ι C m T) atTop (𝓝 0) := by
  have h := ((tendsto_const_nhds (x := A0)).add hy.hasSum.tendsto_sum_nat).sub
    hpv.tendsto_sum_nat
  rw [sub_self] at h
  refine h.congr fun T => ?_
  have := wealth_pv_identity hr A0 y ι C m T
  linarith

/-- **The book's form of the TVC**, O&R p. 534: `(1+r)^{−T}(B_{T+1} + M_T/P_T)` equals
`(1+r)^{−(T+1)} A_{T+1} + (1+r)^{−T} ι_T m_T`, so when the present value of rental payments
`(1+r)^{−T} ι_T m_T` tends to zero, the book's condition and `(1+r)^{−T}A_T → 0` coincide. -/
theorem book_tvc_identity {r : ℝ} (hr : 0 < 1 + r) {P B N Y T C : ℕ → ℝ} (hP : ∀ s, 0 < P s)
    (hbud : ∀ s, B (s + 1) + N (s + 1) / P s = (1 + r) * B s + N s / P s + Y s - C s - T s)
    (t : ℕ) :
    (1 + r)⁻¹ ^ t * (B (t + 1) + N (t + 1) / P t) =
      (1 + r)⁻¹ ^ (t + 1) * wealth r ((1 + r) * B 0 + N 0 / P 0) (fun s => Y s - T s)
        (userCost r P) C (fun s => N (s + 1) / P s) (t + 1) +
      (1 + r)⁻¹ ^ t * (userCost r P t * (N (t + 1) / P t)) := by
  rw [← wealth_of_budget hr hP hbud (t + 1)]
  have hPs := (hP t).ne'
  have hPs1 := (hP (t + 1)).ne'
  unfold userCost
  rw [pow_succ]
  field_simp
  ring

/-! ## Government budget and the economy-wide constraint (§8.3.4, fn 26, Exercise 3) -/

/-- **Seignorage in present value, finite horizon** (O&R fn 26, p. 537): with
`G_s − T_s = (N_{s+1} − N_s)/P_s` (41), `Σ_{s≤T}(1+r)^{−s}(G_s − T_s)` equals
`−N_0/P_0 + Σ_{s<T}(1+r)^{−s} ι_s m_s + (1+r)^{−T} m_T`. -/
theorem seignorage_partial {r : ℝ} (hr : 0 < 1 + r) {P N : ℕ → ℝ} (hP : ∀ s, 0 < P s)
    (T : ℕ) :
    ∑ s ∈ Finset.range (T + 1), (1 + r)⁻¹ ^ s * ((N (s + 1) - N s) / P s) =
      -(N 0 / P 0) + ∑ s ∈ Finset.range T, (1 + r)⁻¹ ^ s * (userCost r P s * (N (s + 1) / P s))
        + (1 + r)⁻¹ ^ T * (N (T + 1) / P T) := by
  induction T with
  | zero => simp; ring
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have hPs := (hP T).ne'
    have hPs1 := (hP (T + 1)).ne'
    have hr' := hr.ne'
    unfold userCost
    rw [pow_succ]
    field_simp
    ring

/-- **The government's present-value constraint**, O&R fn 26, p. 537: with the period constraint
(41) `G_s = T_s + (N_{s+1} − N_s)/P_s`, summable rental revenue and the no-hyperdeflation
condition `(1+r)^{−T} m_T → 0`, the partial sums of `(1+r)^{−s}(G_s − T_s)` converge to
`−N_0/P_0 + Σ (1+r)^{−s} ι_s m_s`. -/
theorem government_pv {r : ℝ} (hr : 0 < 1 + r) {P N G T : ℕ → ℝ} (hP : ∀ s, 0 < P s)
    (hgov : ∀ s, G s = T s + (N (s + 1) - N s) / P s)
    (hsum : Summable (fun s => (1 + r)⁻¹ ^ s * (userCost r P s * (N (s + 1) / P s))))
    (hnhd : Tendsto (fun t => (1 + r)⁻¹ ^ t * (N (t + 1) / P t)) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ s ∈ Finset.range n, (1 + r)⁻¹ ^ s * (G s - T s)) atTop
      (𝓝 (-(N 0 / P 0) + ∑' s, (1 + r)⁻¹ ^ s * (userCost r P s * (N (s + 1) / P s)))) := by
  have hG : ∀ s, G s - T s = (N (s + 1) - N s) / P s := fun s => by rw [hgov s]; ring
  simp only [hG]
  have h1 := ((tendsto_const_nhds (x := -(N 0 / P 0))).add hsum.hasSum.tendsto_sum_nat).add
    hnhd
  rw [add_zero] at h1
  have h2 : Tendsto (fun n => ∑ s ∈ Finset.range (n + 1),
      (1 + r)⁻¹ ^ s * ((N (s + 1) - N s) / P s)) atTop
      (𝓝 (-(N 0 / P 0) + ∑' s, (1 + r)⁻¹ ^ s * (userCost r P s * (N (s + 1) / P s)))) :=
    h1.congr fun n => (seignorage_partial hr hP n).symm
  exact (tendsto_add_atTop_iff_nat 1).1 h2

/-- **The economy's budget constraint (42)**, O&R p. 537: the private constraint (34) and the
government constraint (41) give `B_{s+1} = (1+r)B_s + Y_s − G_s − C_s`; money is nontraded and
drops out. -/
theorem national_budget {r : ℝ} {P B N Y T C G : ℕ → ℝ} (s : ℕ)
    (hbud : B (s + 1) + N (s + 1) / P s = (1 + r) * B s + N s / P s + Y s - C s - T s)
    (hgov : G s = T s + (N (s + 1) - N s) / P s) :
    B (s + 1) = (1 + r) * B s + Y s - G s - C s := by
  rw [hgov]
  have : (N (s + 1) - N s) / P s = N (s + 1) / P s - N s / P s := sub_div _ _ _
  linarith

/-- (43), O&R p. 537: with zero government spending, transfers are financed by printing money,
`−T_s = (N_{s+1} − N_s)/P_s`. -/
theorem transfers_of_zero_spending {T P N : ℕ → ℝ} {s : ℕ}
    (hgov : (0 : ℝ) = T s + (N (s + 1) - N s) / P s) : -T s = (N (s + 1) - N s) / P s := by
  linarith

/-- **Exercise 3(a)**, O&R p. 600: combining the private intertemporal constraint (38) with the
government's (fn 26) gives the economy's constraint
`Σ(1+r)^{−s}(C_s + G_s) = (1+r)B_0 + Σ(1+r)^{−s}Y_s`: money cancels because it is nontraded
and its rental revenue returns to the public through the government. -/
theorem aggregate_budget {r B0 : ℝ} (hr : 0 < 1 + r) {P N Y T C G : ℕ → ℝ} (hP : ∀ s, 0 < P s)
    (hpriv : HasSum (fun s => (1 + r)⁻¹ ^ s * (C s + userCost r P s * (N (s + 1) / P s)))
      ((1 + r) * B0 + N 0 / P 0 + ∑' s, (1 + r)⁻¹ ^ s * (Y s - T s)))
    (hgov : ∀ s, G s = T s + (N (s + 1) - N s) / P s)
    (hY : Summable (fun s => (1 + r)⁻¹ ^ s * Y s)) (hT : Summable (fun s => (1 + r)⁻¹ ^ s * T s))
    (hG : Summable (fun s => (1 + r)⁻¹ ^ s * G s))
    (hsum : Summable (fun s => (1 + r)⁻¹ ^ s * (userCost r P s * (N (s + 1) / P s))))
    (hnhd : Tendsto (fun t => (1 + r)⁻¹ ^ t * (N (t + 1) / P t)) atTop (𝓝 0)) :
    HasSum (fun s => (1 + r)⁻¹ ^ s * (C s + G s)) ((1 + r) * B0 + ∑' s, (1 + r)⁻¹ ^ s * Y s) := by
  set d := (1 + r)⁻¹
  have hGT : HasSum (fun s => d ^ s * (G s - T s)) (∑' s, d ^ s * G s - ∑' s, d ^ s * T s) := by
    have := hG.hasSum.sub hT.hasSum
    simpa [mul_sub] using this
  have hlim := government_pv hr hP hgov hsum hnhd
  have huniq := tendsto_nhds_unique hGT.tendsto_sum_nat hlim
  have hYT : ∑' s, d ^ s * (Y s - T s) = ∑' s, d ^ s * Y s - ∑' s, d ^ s * T s := by
    rw [← hY.tsum_sub hT]; congr 1; funext s; ring
  have hC : HasSum (fun s => d ^ s * C s) ((1 + r) * B0 + N 0 / P 0 +
      (∑' s, d ^ s * Y s - ∑' s, d ^ s * T s) -
        ∑' s, d ^ s * (userCost r P s * (N (s + 1) / P s))) := by
    rw [← hYT]
    have := hpriv.sub hsum.hasSum
    simpa [mul_add] using this
  have := hC.add hG.hasSum
  convert this using 1
  · funext s; ring
  · linarith

/-- **Exercise 3(b)**, O&R p. 600: with government bond holdings `B^G`, the government's period
constraint `B^G_{s+1} + G_s = (1+r)B^G_s + T_s + (N_{s+1} − N_s)/P_s` and the private constraint
(34) for private bonds `B^p` give (42) for national bonds `B = B^p + B^G`. -/
theorem national_budget_with_public_assets {r : ℝ} {P Bp BG N Y T C G : ℕ → ℝ} (s : ℕ)
    (hbud : Bp (s + 1) + N (s + 1) / P s = (1 + r) * Bp s + N s / P s + Y s - C s - T s)
    (hgov : BG (s + 1) + G s = (1 + r) * BG s + T s + (N (s + 1) - N s) / P s) :
    Bp (s + 1) + BG (s + 1) = (1 + r) * (Bp s + BG s) + Y s - G s - C s := by
  have : (N (s + 1) - N s) / P s = N (s + 1) / P s - N s / P s := sub_div _ _ _
  linarith

/-- **The national intertemporal constraint** (O&R (42) iterated, Exercise 3(a)–(b)): if national
bonds follow (42) and `(1+r)^{−T}B_T → 0`, and consumption, government spending and output have
summable present values, then `Σ(1+r)^{−s}(C_s + G_s) = (1+r)B_0 + Σ(1+r)^{−s}Y_s`. -/
theorem national_pv {r : ℝ} (hr : 0 < 1 + r) {B Y C G : ℕ → ℝ}
    (hnat : ∀ s, B (s + 1) = (1 + r) * B s + Y s - G s - C s)
    (hCG : Summable (fun s => (1 + r)⁻¹ ^ s * (C s + G s)))
    (hY : Summable (fun s => (1 + r)⁻¹ ^ s * Y s))
    (hB : Tendsto (fun t => (1 + r)⁻¹ ^ t * B t) atTop (𝓝 0)) :
    HasSum (fun s => (1 + r)⁻¹ ^ s * (C s + G s)) ((1 + r) * B 0 + ∑' s, (1 + r)⁻¹ ^ s * Y s) := by
  set d := (1 + r)⁻¹ with hd
  have hid : ∀ T, ∑ s ∈ Finset.range T, d ^ s * (C s + G s) + (1 + r) * (d ^ T * B T) =
      (1 + r) * B 0 + ∑ s ∈ Finset.range T, d ^ s * Y s := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hnat T, pow_succ]
      have h1 : d * (1 + r) = 1 := inv_mul_cancel₀ hr.ne'
      linear_combination ih + (d ^ T * ((1 + r) * B T + Y T - G T - C T)) * h1
  have hlim := ((tendsto_const_nhds (x := (1 + r) * B 0)).add hY.hasSum.tendsto_sum_nat).sub
    (hB.const_mul (1 + r))
  rw [mul_zero, sub_zero] at hlim
  have h2 : Tendsto (fun T => ∑ s ∈ Finset.range T, d ^ s * (C s + G s)) atTop
      (𝓝 ((1 + r) * B 0 + ∑' s, d ^ s * Y s)) :=
    hlim.congr fun T => by have := hid T; linarith
  have := tendsto_nhds_unique hCG.hasSum.tendsto_sum_nat h2
  rw [← this]
  exact hCG.hasSum

/-! ## The leisure derivation of MIU preferences (p. 531) -/

/-- **Money in the utility function as a reduced form**, O&R p. 531: with
`L̄ − L = L̄((M/P)/C)^ε`, the utility `α log C + (1−α) log(L̄ − L)` equals
`[α − ε(1−α)] log C + ε(1−α) log(M/P) + (1−α) log L̄`. -/
theorem leisure_reduced_form {α ε C m Lbar : ℝ} (hC : 0 < C) (hm : 0 < m) (hL : 0 < Lbar) :
    α * Real.log C + (1 - α) * Real.log (Lbar * (m / C) ^ ε) =
      (α - ε * (1 - α)) * Real.log C + ε * (1 - α) * Real.log m + (1 - α) * Real.log Lbar := by
  rw [Real.log_mul hL.ne' (rpow_pos_of_pos (div_pos hm hC) ε).ne', Real.log_rpow (div_pos hm hC),
    Real.log_div hm.ne' hC.ne']
  ring

/-- Footnote 23, O&R p. 531: both coefficients of the reduced form are positive iff
`0 < ε < α/(1−α)` (for `α < 1`). -/
theorem leisure_coefficients_pos_iff {α ε : ℝ} (hα1 : α < 1) :
    (0 < α - ε * (1 - α) ∧ 0 < ε * (1 - α)) ↔ (0 < ε ∧ ε < α / (1 - α)) := by
  have h1 : 0 < 1 - α := by linarith
  rw [lt_div_iff₀ h1]
  constructor
  · rintro ⟨h2, h3⟩
    exact ⟨(pos_iff_pos_of_mul_pos h3).2 h1, by linarith⟩
  · rintro ⟨h2, h3⟩
    exact ⟨by linarith, mul_pos h2 h1⟩

/-! ## Additively separable utility, the steady state and (44) -/

/-- An additively separable utility `f(C) + v(M/P)` with `f, v` concave is jointly concave on the
positive quadrant (O&R (45), p. 538). -/
theorem separable_concaveOn {f v : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ioi 0) f)
    (hv : ConcaveOn ℝ (Set.Ioi 0) v) :
    ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) (fun p : ℝ × ℝ => f p.1 + v p.2) := by
  refine ⟨(convex_Ioi 0).prod (convex_Ioi 0), fun x hx y hy a b ha hb hab => ?_⟩
  have h1 := hf.2 hx.1 hy.1 ha hb hab
  have h2 := hv.2 hx.2 hy.2 ha hb hab
  simp only [smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd] at h1 h2 ⊢
  linarith

/-- The derivative of an additively separable utility is the pair of marginal utilities
(O&R (45), p. 538). -/
theorem separable_hasFDerivAt {f v : ℝ → ℝ} {c k f' v' : ℝ} (hf : HasDerivAt f f' c)
    (hv : HasDerivAt v v' k) :
    HasFDerivAt (fun p : ℝ × ℝ => f p.1 + v p.2) (grad f' v') (c, k) := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => f p.1)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) f').comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) (c, k) :=
    hf.hasFDerivAt.comp (c, k) hasFDerivAt_fst
  have h2 : HasFDerivAt (fun p : ℝ × ℝ => v p.2)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v').comp
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) (c, k) :=
    hv.hasFDerivAt.comp (c, k) hasFDerivAt_snd
  refine (h1.add h2).congr_fderiv ?_
  ext <;> simp [grad_apply, mul_comm]

/-- **Characterisation of the optimum for `u = log C + v(M/P)`** (O&R (45), p. 538): with `v`
concave and differentiable on `(0, ∞)`, an admissible plan is optimal iff
`1/C_s = (1+r)β/C_{s+1}`, `v'(m_s) = ι_s/C_s` and the transversality condition holds. -/
theorem logSeparable_isOptimal_iff {v v' : ℝ → ℝ} {β r A0 : ℝ} {y ι C m : ℕ → ℝ}
    (hβ : 0 < β) (hr : 0 < 1 + r) (hv : ConcaveOn ℝ (Set.Ioi 0) v)
    (hv' : ∀ k, 0 < k → HasDerivAt v (v' k) k) :
    IsOptimal (fun c k => Real.log c + v k) β r A0 y ι C m ↔
      Admissible (fun c k => Real.log c + v k) β r A0 y ι C m ∧
      (∀ s, (C s)⁻¹ = (1 + r) * β * (C (s + 1))⁻¹) ∧ (∀ s, v' (m s) = ι s * (C s)⁻¹) ∧
      Transversality r (wealth r A0 y ι C m) :=
  isOptimal_iff (uC := fun c _ => c⁻¹) (um := fun _ k => v' k) hβ hr
    (separable_concaveOn strictConcaveOn_log_Ioi.concaveOn hv)
    (fun _ k hc hk => separable_hasFDerivAt (Real.hasDerivAt_log hc.ne') (hv' k hk))
    (fun _ _ hc _ => inv_pos.2 hc)

/-- **Steady-state consumption (44)**, O&R p. 538: with `r > 0` and the present value `W` of
`Y − G`, a constant consumption level `C̄` satisfies the economy's intertemporal constraint
`Σ(1+r)^{−s} C̄ = (1+r)B_0 + W` iff `C̄ = rB_0 + (r/(1+r))W`. -/
theorem steady_consumption_iff {r B0 W Cbar : ℝ} (hr : 0 < r) :
    HasSum (fun s : ℕ => (1 + r)⁻¹ ^ s * Cbar) ((1 + r) * B0 + W) ↔
      Cbar = r * B0 + r / (1 + r) * W := by
  have hd0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have hd1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hg := (hasSum_geometric_of_lt_one hd0 hd1).mul_right Cbar
  have hr0 : r ≠ 0 := hr.ne'
  have hval : (1 - (1 + r)⁻¹)⁻¹ = (1 + r) / r := by
    have h1 : 1 - (1 + r)⁻¹ = r / (1 + r) := by field_simp; ring
    rw [h1, inv_div]
  rw [hval] at hg
  constructor
  · intro h
    have := h.unique hg
    field_simp at this ⊢
    linarith
  · intro h
    convert hg using 1
    rw [h]
    field_simp

/-- **Constant consumption under `(1+r)β = 1`** (O&R p. 538 and (44)): for `u = log C + v(M/P)`,
a constant consumption path with `v'(m_s) = ι_s/C̄` (money demand (37)) that is admissible and
satisfies the TVC is optimal, whatever the path of nominal interest rates. -/
theorem constant_consumption_isOptimal {v v' : ℝ → ℝ} {β r A0 Cbar : ℝ} {y ι m : ℕ → ℝ}
    (hβ : 0 < β) (hr : 0 < 1 + r) (hβr : (1 + r) * β = 1) (hv : ConcaveOn ℝ (Set.Ioi 0) v)
    (hv' : ∀ k, 0 < k → HasDerivAt v (v' k) k)
    (hadm : Admissible (fun c k => Real.log c + v k) β r A0 y ι (fun _ => Cbar) m)
    (hmoney : ∀ s, v' (m s) = ι s * Cbar⁻¹)
    (htvc : Transversality r (wealth r A0 y ι (fun _ => Cbar) m)) :
    IsOptimal (fun c k => Real.log c + v k) β r A0 y ι (fun _ => Cbar) m :=
  (logSeparable_isOptimal_iff hβ hr hv hv').2
    ⟨hadm, fun _ => by rw [hβr, one_mul], hmoney, htvc⟩

/-! ## The CES index and the consumption-based price index (§8.3.3) -/

/-- The CES index `Ω(C, M/P)`, O&R p. 535, identical to the Chapter 4 index (13), O&R p. 222:
`[γ^{1/θ} C^{(θ−1)/θ} + (1−γ)^{1/θ} m^{(θ−1)/θ}]^{θ/(θ−1)}`. This definition and the lemmas
down to `cesPrice_tendsto_cobbDouglas` are copied from the `RealExchangeRate` project's
`CESIndex` module (so that this project builds on its own); here real balances play the role of
nontradables and the user cost `i/(1+i)` that of their relative price `p` (O&R p. 535). -/
noncomputable def cesIndex (γ θ CT CN : ℝ) : ℝ :=
  (γ ^ (1 / θ) * CT ^ ((θ - 1) / θ) + (1 - γ) ^ (1 / θ) * CN ^ ((θ - 1) / θ)) ^ (θ / (θ - 1))

/-- The common denominator `γ + (1−γ) p^{1−θ}` of the demand functions (16), O&R p. 223. -/
noncomputable def cesDenom (γ θ p : ℝ) : ℝ := γ + (1 - γ) * p ^ (1 - θ)

/-- The consumption-based price index (20), O&R p. 227:
`P = [γ + (1−γ) p^{1−θ}]^{1/(1−θ)}`. -/
noncomputable def cesPrice (γ θ p : ℝ) : ℝ := (γ + (1 - γ) * p ^ (1 - θ)) ^ (1 / (1 - θ))

/-- Demand for tradables (16), O&R p. 223: `C_T = γZ/(γ + (1−γ)p^{1−θ})`. -/
noncomputable def cesDemandT (γ θ p Z : ℝ) : ℝ := γ * Z / cesDenom γ θ p

/-- Demand for nontradables (16), O&R p. 223: `C_N = p^{−θ}(1−γ)Z/(γ + (1−γ)p^{1−θ})`. -/
noncomputable def cesDemandN (γ θ p Z : ℝ) : ℝ := p ^ (-θ) * (1 - γ) * Z / cesDenom γ θ p

/-- The denominator of (16) is positive, O&R p. 223. -/
theorem cesDenom_pos {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p) :
    0 < cesDenom γ θ p := by
  unfold cesDenom
  have := rpow_pos_of_pos hp (1 - θ)
  nlinarith

/-- The price index is the `1/(1−θ)` power of the denominator of (16), O&R (20), p. 227. -/
theorem cesPrice_eq_denom_rpow (γ θ p : ℝ) :
    cesPrice γ θ p = cesDenom γ θ p ^ (1 / (1 - θ)) := rfl

/-- The price index is positive, O&R (20), p. 227. -/
theorem cesPrice_pos {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p) :
    0 < cesPrice γ θ p :=
  rpow_pos_of_pos (cesDenom_pos hγ0 hγ1 hp) _

/-- `P^{1−θ} = γ + (1−γ)p^{1−θ}`, O&R (20), p. 227. -/
theorem cesPrice_rpow_one_sub {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p)
    (hθ1 : θ ≠ 1) : cesPrice γ θ p ^ (1 - θ) = γ + (1 - γ) * p ^ (1 - θ) := by
  have h1 : (1 - θ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ1)
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  unfold cesDenom at hD
  rw [cesPrice, ← rpow_mul hD.le, one_div_mul_cancel h1, rpow_one]

/-- The demands (16) exhaust spending, `C_T + p C_N = Z` (14), O&R p. 223. -/
theorem cesDemand_budget {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p) (Z : ℝ) :
    cesDemandT γ θ p Z + p * cesDemandN γ θ p Z = Z := by
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  have hpp : p * p ^ (-θ) = p ^ (1 - θ) := by
    rw [sub_eq_add_neg, rpow_add hp, rpow_one]
  unfold cesDemandT cesDemandN
  field_simp
  unfold cesDenom
  linear_combination (1 - γ) * Z * hpp

/-- Relative demand (15), O&R p. 222: `γ C_N / ((1−γ) C_T) = p^{−θ}` at the demands (16). -/
theorem cesDemand_ratio {γ θ p Z : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p) (hZ : Z ≠ 0) :
    γ * cesDemandN γ θ p Z / ((1 - γ) * cesDemandT γ θ p Z) = p ^ (-θ) := by
  have hD := (cesDenom_pos (θ := θ) hγ0 hγ1 hp).ne'
  have h1 : (1 - γ) ≠ 0 := by linarith
  unfold cesDemandT cesDemandN
  field_simp

/-- The demand (16) for tradables as `γ · (Z/D)`, O&R p. 223. -/
theorem cesDemandT_eq (γ θ p Z : ℝ) :
    cesDemandT γ θ p Z = γ * (Z / cesDenom γ θ p) := by
  unfold cesDemandT; ring

/-- The demand (16) for nontradables as `(1−γ) p^{−θ} · (Z/D)`, O&R p. 223. -/
theorem cesDemandN_eq (γ θ p Z : ℝ) :
    cesDemandN γ θ p Z = (1 - γ) * p ^ (-θ) * (Z / cesDenom γ θ p) := by
  unfold cesDemandN; ring

/-- (21), O&R p. 228: the CES index evaluated at the optimal demands (16) equals `Z/P`, with `P`
the price index (20). -/
theorem cesIndex_demand {γ θ p Z : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ) (hθ1 : θ ≠ 1)
    (hp : 0 < p) (hZ : 0 < Z) :
    cesIndex γ θ (cesDemandT γ θ p Z) (cesDemandN γ θ p Z) = Z / cesPrice γ θ p := by
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hθm : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have hθm' : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ1)
  have h1γ : 0 < 1 - γ := by linarith
  set D := cesDenom γ θ p with hDdef
  have hm : 0 < Z / D := div_pos hZ hD
  set m := Z / D with hmdef
  set ρ := (θ - 1) / θ with hρ
  have hT : γ ^ (1 / θ) * (γ * m) ^ ρ = γ * m ^ ρ := by
    rw [mul_rpow hγ0.le hm.le, ← mul_assoc, ← rpow_add hγ0]
    have : 1 / θ + ρ = 1 := by rw [hρ]; field_simp; ring
    rw [this, rpow_one]
  have hN : (1 - γ) ^ (1 / θ) * ((1 - γ) * p ^ (-θ) * m) ^ ρ
      = (1 - γ) * p ^ (1 - θ) * m ^ ρ := by
    rw [mul_rpow (by positivity) hm.le, mul_rpow h1γ.le (by positivity), ← rpow_mul hp.le,
      ← mul_assoc, ← mul_assoc, ← rpow_add h1γ]
    have e1 : 1 / θ + ρ = 1 := by rw [hρ]; field_simp; ring
    have e2 : -θ * ρ = 1 - θ := by rw [hρ]; field_simp; ring
    rw [e1, e2, rpow_one]
  unfold cesIndex
  rw [cesDemandT_eq, cesDemandN_eq, ← hmdef, hT, hN]
  have hsum : γ * m ^ ρ + (1 - γ) * p ^ (1 - θ) * m ^ ρ = D * m ^ ρ := by
    rw [hDdef, cesDenom]; ring
  rw [hsum, mul_rpow hD.le (by positivity), ← rpow_mul hm.le]
  have e3 : ρ * (θ / (θ - 1)) = 1 := by rw [hρ]; field_simp
  rw [e3, rpow_one, cesPrice_eq_denom_rpow, ← hDdef, div_eq_mul_inv Z, ← rpow_neg hD.le]
  have e4 : D ^ (-(1 / (1 - θ))) = D ^ (θ / (θ - 1)) / D := by
    rw [← rpow_sub_one hD.ne']
    congr 1
    field_simp
    ring
  rw [e4, hmdef]
  field_simp

/-- (22), O&R p. 228: the demands (16) written as `C_T = γ P^θ C` and
`C_N = (1−γ)(p/P)^{−θ} C` with real consumption `C = Z/P`. -/
theorem cesDemand_eq_price_form {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1)
    (hp : 0 < p) (Z : ℝ) :
    cesDemandT γ θ p Z = γ * cesPrice γ θ p ^ θ * (Z / cesPrice γ θ p) ∧
    cesDemandN γ θ p Z = (1 - γ) * (p / cesPrice γ θ p) ^ (-θ) * (Z / cesPrice γ θ p) := by
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  have hP := cesPrice_pos (θ := θ) hγ0 hγ1 hp
  have hθm' : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ1)
  have key : cesPrice γ θ p ^ θ / cesPrice γ θ p = (cesDenom γ θ p)⁻¹ := by
    rw [← rpow_sub_one hP.ne', cesPrice_eq_denom_rpow, ← rpow_mul hD.le, ← rpow_neg_one]
    congr 1
    field_simp
    ring
  constructor
  · rw [cesDemandT_eq]
    calc γ * (Z / cesDenom γ θ p) = γ * (cesPrice γ θ p ^ θ / cesPrice γ θ p) * Z := by
          rw [key]; ring
      _ = _ := by ring
  · rw [cesDemandN_eq, div_rpow hp.le hP.le, rpow_neg hP.le, div_inv_eq_mul]
    calc (1 - γ) * p ^ (-θ) * (Z / cesDenom γ θ p)
        = (1 - γ) * p ^ (-θ) * (cesPrice γ θ p ^ θ / cesPrice γ θ p) * Z := by
          rw [key]; ring
      _ = _ := by ring

/-- Tangent-line (Bernoulli) bound for a concave power, used for the duality in §4.4.1.1
(O&R p. 227): for `0 ≤ ρ ≤ 1`, `x ≥ 0`, `a > 0`, `x^ρ ≤ a^ρ + ρ a^{ρ−1}(x − a)`. -/
theorem ces_rpow_le_tangent {ρ x a : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hx : 0 ≤ x) (ha : 0 < a) :
    x ^ ρ ≤ a ^ ρ + ρ * a ^ (ρ - 1) * (x - a) := by
  have hs : -1 ≤ x / a - 1 := by have := div_nonneg hx ha.le; linarith
  have hb := rpow_one_add_le_one_add_mul_self hs hρ0 hρ1
  rw [add_sub_cancel, div_rpow hx ha.le] at hb
  have haρ := rpow_pos_of_pos ha ρ
  rw [div_le_iff₀ haρ] at hb
  rw [rpow_sub_one ha.ne']
  calc x ^ ρ ≤ (1 + ρ * (x / a - 1)) * a ^ ρ := hb
    _ = a ^ ρ + ρ * (a ^ ρ / a) * (x - a) := by field_simp

/-- Tangent-line (Bernoulli) bound for a convex negative power, used for the duality in §4.4.1.1
(O&R p. 227): for `ρ ≤ 0`, `x, a > 0`, `a^ρ + ρ a^{ρ−1}(x − a) ≤ x^ρ`. -/
theorem ces_tangent_le_rpow {ρ x a : ℝ} (hρ : ρ ≤ 0) (hx : 0 < x) (ha : 0 < a) :
    a ^ ρ + ρ * a ^ (ρ - 1) * (x - a) ≤ x ^ ρ := by
  set y := x / a with hy
  have hy0 : 0 < y := div_pos hx ha
  have hs : -1 ≤ 1 / y - 1 := by have := one_div_pos.mpr hy0; linarith
  have hb := one_add_mul_self_le_rpow_one_add hs (p := 1 - ρ) (by linarith)
  rw [add_sub_cancel, one_div, inv_rpow hy0.le, ← rpow_neg hy0.le, neg_sub] at hb
  -- hb : 1 + (1 - ρ) * (1 / y - 1) ≤ y ^ (ρ - 1)
  have hyρ : y ^ ρ = y * y ^ (ρ - 1) := by
    rw [rpow_sub_one hy0.ne']; field_simp
  have h1 : 1 + ρ * (y - 1) ≤ y ^ ρ := by
    rw [hyρ]
    have := mul_le_mul_of_nonneg_left hb hy0.le
    calc 1 + ρ * (y - 1) = y * (1 + (1 - ρ) * (y⁻¹ - 1)) := by field_simp; ring
      _ ≤ _ := this
  have haρ := rpow_pos_of_pos ha ρ
  have hxy : x ^ ρ = y ^ ρ * a ^ ρ := by
    rw [hy, div_rpow hx.le ha.le]; field_simp
  rw [hxy, rpow_sub_one ha.ne']
  calc a ^ ρ + ρ * (a ^ ρ / a) * (x - a) = (1 + ρ * (y - 1)) * a ^ ρ := by
        rw [hy]; field_simp
    _ ≤ y ^ ρ * a ^ ρ := mul_le_mul_of_nonneg_right h1 haρ.le

/-- First-order conditions behind (15)–(16), O&R p. 222: at the demands (16) the marginal
contributions `γ^{1/θ} C_T^{−1/θ}` and `(1−γ)^{1/θ} C_N^{−1/θ}` to the inner CES sum are in the
price ratio `1 : p` (both equal to `(Z/D)^{−1/θ}` times `1`, resp. `p`). -/
theorem cesDemand_foc {γ θ p Z : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hp : 0 < p) (hZ : 0 < Z) :
    γ ^ (1 / θ) * cesDemandT γ θ p Z ^ ((θ - 1) / θ - 1)
      = (Z / cesDenom γ θ p) ^ ((θ - 1) / θ - 1) ∧
    (1 - γ) ^ (1 / θ) * cesDemandN γ θ p Z ^ ((θ - 1) / θ - 1)
      = p * (Z / cesDenom γ θ p) ^ ((θ - 1) / θ - 1) := by
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  have hm : 0 < Z / cesDenom γ θ p := div_pos hZ hD
  have h1γ : 0 < 1 - γ := by linarith
  have e1 : 1 / θ + ((θ - 1) / θ - 1) = 0 := by field_simp; ring
  have e2 : -θ * ((θ - 1) / θ - 1) = 1 := by field_simp; ring
  constructor
  · rw [cesDemandT_eq, mul_rpow hγ0.le hm.le, ← mul_assoc, ← rpow_add hγ0, e1, rpow_zero,
      one_mul]
  · rw [cesDemandN_eq, mul_rpow (by positivity) hm.le, mul_rpow h1γ.le (by positivity),
      ← rpow_mul hp.le, ← mul_assoc, ← mul_assoc, ← rpow_add h1γ, e1, e2, rpow_zero, rpow_one,
      one_mul]

/-- **Duality (T13)**, O&R §4.4.1.1, pp. 227–228: every bundle `C_T, C_N ≥ 0` costing
`Z = C_T + p C_N > 0` yields at most `Z/P` units of the CES index (13), `P` the price index
(20); equality holds at the demands (16) (`cesIndex_demand`). For `θ < 1` both goods must be
consumed in strictly positive amounts (otherwise Lean's `0 ^ y = 0` is a junk value, see the
module docstring). Proof: tangent-line bounds for `x ↦ x^{(θ−1)/θ}` at the optimum, whose
gradient is proportional to prices (`cesDemand_foc`). -/
theorem cesIndex_le_div_price {γ θ p CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hp : 0 < p) (hCT : 0 ≤ CT) (hCN : 0 ≤ CN)
    (hint : θ < 1 → 0 < CT ∧ 0 < CN) (hZ : 0 < CT + p * CN) :
    cesIndex γ θ CT CN ≤ (CT + p * CN) / cesPrice γ θ p := by
  set Z := CT + p * CN with hZdef
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  have hm : 0 < Z / cesDenom γ θ p := div_pos hZ hD
  have h1γ : 0 < 1 - γ := by linarith
  set xT := cesDemandT γ θ p Z with hxT
  set xN := cesDemandN γ θ p Z with hxN
  have hxT0 : 0 < xT := by rw [hxT, cesDemandT_eq]; positivity
  have hxN0 : 0 < xN := by rw [hxN, cesDemandN_eq]; exact mul_pos (by positivity) hm
  have hbud : xT + p * xN = Z := cesDemand_budget hγ0 hγ1 hp Z
  obtain ⟨hgT, hgN⟩ := cesDemand_foc (θ := θ) hγ0 hγ1 hθ hp hZ
  rw [← hxT] at hgT
  rw [← hxN] at hgN
  set ρ := (θ - 1) / θ with hρ
  set g := (Z / cesDenom γ θ p) ^ (ρ - 1) with hg
  have hval := cesIndex_demand hγ0 hγ1 hθ hθ1 hp hZ
  rw [← hxT, ← hxN] at hval
  unfold cesIndex at hval ⊢
  rw [← hρ] at hval ⊢
  rw [← hval]
  have ha := rpow_pos_of_pos hγ0 (1 / θ)
  have hb := rpow_pos_of_pos h1γ (1 / θ)
  set Astar := γ ^ (1 / θ) * xT ^ ρ + (1 - γ) ^ (1 / θ) * xN ^ ρ with hAstar
  set A := γ ^ (1 / θ) * CT ^ ρ + (1 - γ) ^ (1 / θ) * CN ^ ρ with hA
  have hlin : γ ^ (1 / θ) * (xT ^ ρ + ρ * xT ^ (ρ - 1) * (CT - xT))
      + (1 - γ) ^ (1 / θ) * (xN ^ ρ + ρ * xN ^ (ρ - 1) * (CN - xN)) = Astar := by
    have : γ ^ (1 / θ) * (xT ^ ρ + ρ * xT ^ (ρ - 1) * (CT - xT))
        + (1 - γ) ^ (1 / θ) * (xN ^ ρ + ρ * xN ^ (ρ - 1) * (CN - xN))
        = Astar + ρ * g * ((CT + p * CN) - (xT + p * xN)) := by
      rw [hAstar]
      linear_combination (ρ * (CT - xT)) * hgT + (ρ * (CN - xN)) * hgN
    rw [this, hbud, hZdef, sub_self, mul_zero, add_zero]
  rcases lt_or_gt_of_ne hθ1 with hlt | hgt
  · -- θ < 1: the power `ρ` is negative and the outer exponent is negative
    obtain ⟨hCT', hCN'⟩ := hint hlt
    have hρneg : ρ ≤ 0 := by rw [hρ]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hθ.le
    have t1 := ces_tangent_le_rpow hρneg hCT' hxT0
    have t2 := ces_tangent_le_rpow hρneg hCN' hxN0
    have key : Astar ≤ A := by
      rw [← hlin, hA]
      exact add_le_add (mul_le_mul_of_nonneg_left t1 ha.le) (mul_le_mul_of_nonneg_left t2 hb.le)
    have hApos : 0 < Astar := by rw [hAstar]; positivity
    exact rpow_le_rpow_of_nonpos hApos key
      (div_nonpos_of_nonneg_of_nonpos hθ.le (by linarith))
  · -- θ > 1: the power `ρ` lies in `(0, 1)` and the outer exponent is positive
    have hρ0 : 0 ≤ ρ := by rw [hρ]; exact div_nonneg (by linarith) hθ.le
    have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one hθ]; linarith
    have t1 := ces_rpow_le_tangent hρ0 hρ1 hCT hxT0
    have t2 := ces_rpow_le_tangent hρ0 hρ1 hCN hxN0
    have key : A ≤ Astar := by
      rw [← hlin, hA]
      exact add_le_add (mul_le_mul_of_nonneg_left t1 ha.le) (mul_le_mul_of_nonneg_left t2 hb.le)
    have hA0 : 0 ≤ A := by rw [hA]; positivity
    exact rpow_le_rpow hA0 key (div_nonneg hθ.le (by linarith))

/-- The price index is the minimum cost of one unit of real consumption, the definition of
O&R p. 227: any interior bundle with `Ω(C_T, C_N) = 1` costs at least `P`, and the demands (16)
at spending `Z = P` deliver `Ω = 1` at cost exactly `P`. -/
theorem cesPrice_isLeast_cost {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hp : 0 < p) :
    (∀ CT CN : ℝ, 0 < CT → 0 < CN → cesIndex γ θ CT CN = 1 → cesPrice γ θ p ≤ CT + p * CN) ∧
    cesIndex γ θ (cesDemandT γ θ p (cesPrice γ θ p)) (cesDemandN γ θ p (cesPrice γ θ p)) = 1 ∧
    cesDemandT γ θ p (cesPrice γ θ p) + p * cesDemandN γ θ p (cesPrice γ θ p)
      = cesPrice γ θ p := by
  have hP := cesPrice_pos (θ := θ) hγ0 hγ1 hp
  refine ⟨fun CT CN hCT hCN h1 => ?_, ?_, cesDemand_budget hγ0 hγ1 hp _⟩
  · have hZ : 0 < CT + p * CN := by positivity
    have := cesIndex_le_div_price hγ0 hγ1 hθ hθ1 hp hCT.le hCN.le (fun _ => ⟨hCT, hCN⟩) hZ
    rw [h1, le_div_iff₀ hP, one_mul] at this
    exact this
  · rw [cesIndex_demand hγ0 hγ1 hθ hθ1 hp hP, div_self hP.ne']

/-- "Of course, `P` is an increasing function of `p`", O&R p. 227: the CES price index (20) is
strictly increasing in the relative price of nontradables on `p > 0`, for every `θ ≠ 1`. -/
theorem cesPrice_strictMonoOn {γ θ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1) :
    StrictMonoOn (cesPrice γ θ) (Ioi 0) := by
  intro a ha b hb hab
  simp only [mem_Ioi] at ha hb
  have h1γ : 0 < 1 - γ := by linarith
  rw [cesPrice_eq_denom_rpow, cesPrice_eq_denom_rpow]
  have hDa := cesDenom_pos (θ := θ) hγ0 hγ1 ha
  have hDb := cesDenom_pos (θ := θ) hγ0 hγ1 hb
  rcases lt_or_gt_of_ne hθ1 with hlt | hgt
  · have hpow : a ^ (1 - θ) < b ^ (1 - θ) := rpow_lt_rpow ha.le hab (by linarith)
    have hD : cesDenom γ θ a < cesDenom γ θ b := by
      unfold cesDenom; nlinarith
    exact rpow_lt_rpow hDa.le hD (by apply one_div_pos.mpr; linarith)
  · have hpow : b ^ (1 - θ) < a ^ (1 - θ) := rpow_lt_rpow_of_neg ha hab (by linarith)
    have hD : cesDenom γ θ b < cesDenom γ θ a := by
      unfold cesDenom; nlinarith
    exact rpow_lt_rpow_of_neg hDb hD (by apply one_div_neg.mpr; linarith)

/-- Footnote 26, O&R p. 228: starting from `p = 1`, (20) implies `P̂ = (1−γ) p̂` for every
`θ ≠ 1`, stated exactly as `d log P / dp = 1 − γ` at `p = 1` (where `p̂ = dp/p = dp`). -/
theorem cesPrice_logDeriv_at_one {γ θ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1) :
    HasDerivAt (fun p => Real.log (cesPrice γ θ p)) (1 - γ) 1 := by
  have hθm' : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ1)
  have hin : HasDerivAt (fun p : ℝ => γ + (1 - γ) * p ^ (1 - θ))
      ((1 - γ) * ((1 - θ) * (1 : ℝ) ^ (1 - θ - 1))) 1 :=
    ((hasDerivAt_rpow_const (Or.inl one_ne_zero)).const_mul (1 - γ)).const_add γ
  have hlog := (hin.log (by simp)).const_mul (1 / (1 - θ))
  have hev : (fun p => Real.log (cesPrice γ θ p))
      =ᶠ[𝓝 1] fun p => 1 / (1 - θ) * Real.log (γ + (1 - γ) * p ^ (1 - θ)) := by
    filter_upwards [Ioi_mem_nhds one_pos] with p hp
    have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
    unfold cesDenom at hD
    rw [cesPrice, Real.log_rpow hD]
  refine (hlog.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [one_rpow, mul_one]
  field_simp
  ring

/-- Power-mean limit behind footnotes 22 and 26, O&R pp. 222–228: for weights `w, 1 − w > 0` and
`a, b > 0`, `(w a^ρ + (1−w) b^ρ)^{1/ρ} → a^w b^{1−w}` as `ρ → 0`. -/
theorem ces_powerMean_tendsto {w a b : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (ha : 0 < a)
    (hb : 0 < b) :
    Tendsto (fun ρ : ℝ => (w * a ^ ρ + (1 - w) * b ^ ρ) ^ (1 / ρ)) (𝓝[≠] 0)
      (𝓝 (a ^ w * b ^ (1 - w))) := by
  have h1w : 0 < 1 - w := by linarith
  set f : ℝ → ℝ := fun ρ => Real.log (w * a ^ ρ + (1 - w) * b ^ ρ) with hf
  have hin : HasDerivAt (fun ρ : ℝ => w * a ^ ρ + (1 - w) * b ^ ρ)
      (w * (a ^ (0 : ℝ) * Real.log a) + (1 - w) * (b ^ (0 : ℝ) * Real.log b)) 0 :=
    ((hasStrictDerivAt_const_rpow ha 0).hasDerivAt.const_mul w).add
      ((hasStrictDerivAt_const_rpow hb 0).hasDerivAt.const_mul (1 - w))
  have hder := hin.log (by simp)
  simp only [rpow_zero, one_mul, mul_one, add_sub_cancel, div_one] at hder
  have hslope := (Real.continuous_exp.tendsto _).comp (hasDerivAt_iff_tendsto_slope.mp hder)
  have hlim : Real.exp (w * Real.log a + (1 - w) * Real.log b) = a ^ w * b ^ (1 - w) := by
    rw [rpow_def_of_pos ha, rpow_def_of_pos hb, ← Real.exp_add]; ring_nf
  rw [hlim] at hslope
  refine hslope.congr' ?_
  filter_upwards with ρ
  have hpos : 0 < w * a ^ ρ + (1 - w) * b ^ ρ := by positivity
  rw [Function.comp_apply, slope_def_field, rpow_def_of_pos hpos]
  simp only [rpow_zero, mul_one, add_sub_cancel, Real.log_one, sub_zero]
  ring_nf

/-- `θ ↦ 1 − θ` maps a punctured neighbourhood of `1` into one of `0` (for the `θ → 1` limit of
the price index (20), O&R p. 228). -/
theorem ces_tendsto_one_sub_punctured :
    Tendsto (fun θ : ℝ => 1 - θ) (𝓝[≠] 1) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have : Tendsto (fun θ : ℝ => 1 - θ) (𝓝 1) (𝓝 (1 - 1)) :=
      tendsto_const_nhds.sub tendsto_id
    rw [sub_self] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact sub_ne_zero.mpr (Ne.symm hθ)

/-- Cobb–Douglas limit of the price index, O&R p. 228 (and fn 26): as `θ → 1`,
`P = [γ + (1−γ)p^{1−θ}]^{1/(1−θ)} → p^{1−γ}`. -/
theorem cesPrice_tendsto_cobbDouglas {γ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p) :
    Tendsto (fun θ => cesPrice γ θ p) (𝓝[≠] 1) (𝓝 (p ^ (1 - γ))) := by
  have h := (ces_powerMean_tendsto hγ0 hγ1 one_pos hp).comp ces_tendsto_one_sub_punctured
  rw [one_rpow, one_mul] at h
  refine h.congr' ?_
  filter_upwards with θ
  simp [cesPrice]

/-! ## CES-isoelastic money-in-the-utility preferences (§8.3.3) -/

/-- Two positive numbers are equal iff their `t`-th powers are (`t ≠ 0`); used to solve the
first-order conditions of §8.3.3.
Context: O&R §8.3, pp. 530–538. -/
theorem eq_iff_rpow_eq {x y t : ℝ} (hx : 0 < x) (hy : 0 < y) (ht : t ≠ 0) :
    x = y ↔ x ^ t = y ^ t := by
  constructor
  · intro h; rw [h]
  · intro h
    have h2 := congrArg (· ^ (1 / t)) h
    rwa [← rpow_mul hx.le, ← rpow_mul hy.le, mul_one_div_cancel ht, rpow_one, rpow_one] at h2

/-- The inner CES sum `γ^{1/θ} C^{(θ−1)/θ} + (1−γ)^{1/θ} m^{(θ−1)/θ}` (O&R p. 535). -/
noncomputable def cesInner (γ θ C m : ℝ) : ℝ :=
  γ ^ (1 / θ) * C ^ ((θ - 1) / θ) + (1 - γ) ^ (1 / θ) * m ^ ((θ - 1) / θ)

/-- The inner CES sum is positive on the positive quadrant.
Context: O&R §8.3, pp. 530–538. -/
theorem cesInner_pos {γ θ C m : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hC : 0 < C) (hm : 0 < m) :
    0 < cesInner γ θ C m := by
  have : 0 < 1 - γ := by linarith
  unfold cesInner
  positivity

/-- The CES index is positive on the positive quadrant (O&R p. 535). -/
theorem cesIndex_pos {γ θ C m : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hC : 0 < C) (hm : 0 < m) :
    0 < cesIndex γ θ C m :=
  rpow_pos_of_pos (cesInner_pos hγ0 hγ1 hC hm) _

/-- The CES-isoelastic period utility of §8.3.3, O&R p. 535:
`u(C, M/P) = Ω(C, M/P)^{1−1/σ}/(1 − 1/σ)`. -/
noncomputable def cesUtility (γ θ σ C m : ℝ) : ℝ := cesIndex γ θ C m ^ (1 - 1 / σ) / (1 - 1 / σ)

/-- Marginal utility of consumption for CES-isoelastic preferences:
`u_C = γ^{1/θ} C^{−1/θ} Ω^{1/θ − 1/σ}` (O&R p. 535; Supplement p. 752). -/
noncomputable def cesMargC (γ θ σ C m : ℝ) : ℝ :=
  γ ^ (1 / θ) * C ^ (-(1 / θ)) * cesIndex γ θ C m ^ (1 / θ - 1 / σ)

/-- Marginal utility of real balances for CES-isoelastic preferences:
`u_{M/P} = (1−γ)^{1/θ} m^{−1/θ} Ω^{1/θ − 1/σ}` (O&R p. 535). -/
noncomputable def cesMargM (γ θ σ C m : ℝ) : ℝ :=
  (1 - γ) ^ (1 / θ) * m ^ (-(1 / θ)) * cesIndex γ θ C m ^ (1 / θ - 1 / σ)

/-- **The gradient of CES-isoelastic utility** (O&R p. 535): on the positive quadrant `u` is
differentiable with partial derivatives `cesMargC` and `cesMargM`. -/
theorem cesUtility_hasFDerivAt {γ θ σ c k : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hc : 0 < c) (hk : 0 < k) :
    HasFDerivAt (fun p : ℝ × ℝ => cesUtility γ θ σ p.1 p.2)
      (grad (cesMargC γ θ σ c k) (cesMargM γ θ σ c k)) (c, k) := by
  set ρ := (θ - 1) / θ with hρ
  set e := θ / (θ - 1) with he
  set a := γ ^ (1 / θ) with ha
  set b := (1 - γ) ^ (1 / θ) with hb
  have hθm : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have hσ' : 1 - 1 / σ ≠ 0 := by
    intro h
    apply hσ1
    field_simp at h
    linarith
  have hX := cesInner_pos (θ := θ) hγ0 hγ1 hc hk
  have hΩ := cesIndex_pos (θ := θ) hγ0 hγ1 hc hk
  set X := cesInner γ θ c k with hXdef
  set Ω := cesIndex γ θ c k with hΩdef
  have hΩX : Ω = X ^ e := rfl
  have hf1 : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) (c, k) :=
    hasFDerivAt_fst
  have hf2 : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) (c, k) :=
    hasFDerivAt_snd
  have h1 :=
    (Real.hasDerivAt_rpow_const (x := c) (p := ρ) (Or.inl hc.ne')).comp_hasFDerivAt (c, k) hf1
  have h2 :=
    (Real.hasDerivAt_rpow_const (x := k) (p := ρ) (Or.inl hk.ne')).comp_hasFDerivAt (c, k) hf2
  have hin := (h1.const_mul a).add (h2.const_mul b)
  have hpow := hin.rpow_const (p := e) (Or.inl hX.ne')
  have hU := (hpow.rpow_const (p := 1 - 1 / σ) (Or.inl hΩ.ne')).mul_const ((1 - 1 / σ)⁻¹)
  have hfun : (fun p : ℝ × ℝ => cesUtility γ θ σ p.1 p.2) =
      fun p => ((a * p.1 ^ ρ + b * p.2 ^ ρ) ^ e) ^ (1 - 1 / σ) * (1 - 1 / σ)⁻¹ := by
    funext p
    rw [cesUtility, div_eq_mul_inv]
    rfl
  rw [hfun]
  have hXe : X ^ (e - 1) = Ω ^ (1 / θ) := by
    rw [hΩX, ← rpow_mul hX.le]
    congr 1
    rw [he]
    field_simp
    ring
  have heρ : e * ρ = 1 := by rw [he, hρ]; field_simp
  have hρ1 : ρ - 1 = -(1 / θ) := by rw [hρ]; field_simp; ring
  have hsplit : Ω ^ (1 / θ - 1 / σ) = Ω ^ (1 / θ) * Ω ^ (-(1 / σ)) := by
    rw [sub_eq_add_neg, rpow_add hΩ]
  have hσe : (1 : ℝ) - 1 / σ - 1 = -(1 / σ) := by ring
  refine hU.congr_fderiv ?_
  have hXval : a * c ^ ρ + b * k ^ ρ = X := rfl
  have hs : (1 - σ⁻¹)⁻¹ * (1 - σ⁻¹) = 1 := inv_mul_cancel₀ (by rwa [one_div] at hσ')
  ext
  · simp only [one_div, Function.comp_apply, Pi.add_apply, sub_sub_cancel_left, smul_add,
      ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.fst_comp_inl, ContinuousLinearMap.snd_comp_inl, smul_zero, add_zero,
      smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one, grad]
    rw [hXval, hXe, hρ1, ← hΩX, cesMargC, ← hΩdef, hsplit, one_div σ]
    linear_combination (e * ρ * (a * c ^ (-(1 / θ)) * (Ω ^ (1 / θ) * Ω ^ (-σ⁻¹)))) * hs +
      (a * c ^ (-(1 / θ)) * (Ω ^ (1 / θ) * Ω ^ (-σ⁻¹))) * heρ
  · simp only [one_div, Function.comp_apply, Pi.add_apply, sub_sub_cancel_left, smul_add,
      ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.fst_comp_inr, smul_zero, ContinuousLinearMap.snd_comp_inr, zero_add,
      smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one, grad]
    rw [hXval, hXe, hρ1, ← hΩX, cesMargM, ← hΩdef, hsplit, one_div σ]
    linear_combination (e * ρ * (b * k ^ (-(1 / θ)) * (Ω ^ (1 / θ) * Ω ^ (-σ⁻¹)))) * hs +
      (b * k ^ (-(1 / θ)) * (Ω ^ (1 / θ) * Ω ^ (-σ⁻¹))) * heρ

/-- **CES money demand**, O&R p. 535: the first-order condition (37),
`u_{M/P} = ι u_C` with user cost `ι = i/(1+i)`, holds iff
`M/P = ((1−γ)/γ) ι^{−θ} C`, i.e. `M/P = ((1−γ)/γ)(1 + 1/i)^θ C`. -/
theorem ces_money_demand_iff {γ θ σ c k ι : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hc : 0 < c) (hk : 0 < k) (hι : 0 < ι) :
    cesMargM γ θ σ c k = ι * cesMargC γ θ σ c k ↔ k = (1 - γ) / γ * ι ^ (-θ) * c := by
  have h1γ : 0 < 1 - γ := by linarith
  have hZ := rpow_pos_of_pos (cesIndex_pos (θ := θ) hγ0 hγ1 hc hk) (1 / θ - 1 / σ)
  unfold cesMargM cesMargC
  rw [show ι * (γ ^ (1 / θ) * c ^ (-(1 / θ)) * cesIndex γ θ c k ^ (1 / θ - 1 / σ)) =
    ι * γ ^ (1 / θ) * c ^ (-(1 / θ)) * cesIndex γ θ c k ^ (1 / θ - 1 / σ) by ring,
    mul_left_inj' hZ.ne', eq_iff_rpow_eq (by positivity) (by positivity)
    (neg_ne_zero.2 hθ.ne')]
  have e1 : 1 / θ * -θ = -1 := by field_simp
  have e2 : -(1 / θ) * -θ = 1 := by field_simp
  have hL : ((1 - γ) ^ (1 / θ) * k ^ (-(1 / θ))) ^ (-θ) = k / (1 - γ) := by
    rw [mul_rpow (by positivity) (by positivity), ← rpow_mul h1γ.le, ← rpow_mul hk.le, e1, e2,
      rpow_neg_one, rpow_one, div_eq_inv_mul]
  have hR : (ι * γ ^ (1 / θ) * c ^ (-(1 / θ))) ^ (-θ) = ι ^ (-θ) * c / γ := by
    rw [mul_rpow (by positivity) (by positivity), mul_rpow hι.le (by positivity),
      ← rpow_mul hγ0.le, ← rpow_mul hc.le, e1, e2, rpow_neg_one, rpow_one]
    field_simp
  rw [hL, hR, div_eq_iff h1γ.ne', show (1 - γ) / γ * ι ^ (-θ) * c = ι ^ (-θ) * c / γ * (1 - γ) by
    ring]

/-- On the money-demand locus, the CES index equals `C D/(γ P^C)` with `D = γ + (1−γ)ι^{1−θ}`
(O&R p. 535, via the Chapter 4 demand system). -/
theorem cesIndex_on_demand {γ θ c k ι : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hc : 0 < c) (hι : 0 < ι) (hk : k = (1 - γ) / γ * ι ^ (-θ) * c) :
    cesIndex γ θ c k = c * cesDenom γ θ ι / γ / cesPrice γ θ ι := by
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hι
  have hZ : 0 < c * cesDenom γ θ ι / γ := by positivity
  have h1 : cesDemandT γ θ ι (c * cesDenom γ θ ι / γ) = c := by
    unfold cesDemandT; field_simp
  have h2 : cesDemandN γ θ ι (c * cesDenom γ θ ι / γ) = k := by
    rw [hk]; unfold cesDemandN; field_simp
  have := cesIndex_demand hγ0 hγ1 hθ hθ1 hι hZ
  rw [h1, h2] at this
  exact this

/-- **Real consumption on the money-demand locus**, O&R p. 536: `Ω = C (P^C)^{−θ}/γ`, i.e. the
book's `C = γ (P^C)^θ Ω`. -/
theorem cesIndex_on_demand' {γ θ c k ι : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hc : 0 < c) (hι : 0 < ι) (hk : k = (1 - γ) / γ * ι ^ (-θ) * c) :
    cesIndex γ θ c k = c * cesPrice γ θ ι ^ (-θ) / γ := by
  have hP := cesPrice_pos (θ := θ) hγ0 hγ1 hι
  have hD : cesDenom γ θ ι = cesPrice γ θ ι ^ (1 - θ) :=
    (cesPrice_rpow_one_sub hγ0 hγ1 hι hθ1).symm
  rw [cesIndex_on_demand hγ0 hγ1 hθ hθ1 hc hι hk, hD, show -θ = 1 - θ - 1 by ring,
    rpow_sub_one hP.ne']
  field_simp

/-- **Total expenditure on the money-demand locus**, O&R p. 535: `Z = C + ι M/P = C D/γ`,
with `D = γ + (1−γ)ι^{1−θ} = (P^C)^{1−θ}`. -/
theorem expenditure_on_demand {γ θ c k ι : ℝ} (hγ0 : 0 < γ) (hι : 0 < ι)
    (hk : k = (1 - γ) / γ * ι ^ (-θ) * c) : c + ι * k = c * cesDenom γ θ ι / γ := by
  have h : ι ^ (1 - θ) = ι * ι ^ (-θ) := by
    rw [sub_eq_add_neg, rpow_add hι, rpow_one]
  rw [hk, cesDenom, h]
  field_simp

/-- **Marginal utility of consumption on the money-demand locus**, O&R Supplement p. 752 (and
§8.3.3): `u_C = γ^{1/σ} C^{−1/σ} (P^C)^{(θ−σ)/σ}`. -/
theorem cesMargC_on_demand {γ θ σ c k ι : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hσ : 0 < σ) (hc : 0 < c) (hι : 0 < ι)
    (hk : k = (1 - γ) / γ * ι ^ (-θ) * c) :
    cesMargC γ θ σ c k = γ ^ (1 / σ) * c ^ (-(1 / σ)) * cesPrice γ θ ι ^ ((θ - σ) / σ) := by
  have hP := cesPrice_pos (θ := θ) hγ0 hγ1 hι
  set q := 1 / θ - 1 / σ with hq
  set P := cesPrice γ θ ι with hPdef
  rw [cesMargC, cesIndex_on_demand' hγ0 hγ1 hθ hθ1 hc hι hk, ← hPdef,
    div_rpow (by positivity) hγ0.le, mul_rpow hc.le (by positivity), ← rpow_mul hP.le]
  have e1 : γ ^ (1 / θ) / γ ^ q = γ ^ (1 / σ) := by
    rw [← rpow_sub hγ0]; congr 1; rw [hq]; ring
  have e2 : c ^ (-(1 / θ)) * c ^ q = c ^ (-(1 / σ)) := by
    rw [← rpow_add hc]; congr 1; rw [hq]; ring
  have e3 : -θ * q = (θ - σ) / σ := by rw [hq]; field_simp; ring
  rw [← e1, ← e2, ← e3]
  ring

/-- **Consumption Euler equation with a time-varying consumption price index** (O&R §8.3.3
and Exercise 3, p. 601): if `u_C = K C^{−1/σ} P^{a/σ}` along the path and
`u_C(s) = (1+r)β u_C(s+1)`, then `C_{s+1} = (β(1+r))^σ (P_{s+1}/P_s)^a C_s`. -/
theorem euler_growth {K σ a β r c0 c1 P0 P1 : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hβ : 0 < β)
    (hr : 0 < 1 + r) (hc0 : 0 < c0) (hc1 : 0 < c1) (hP0 : 0 < P0) (hP1 : 0 < P1)
    (h : K * c0 ^ (-(1 / σ)) * P0 ^ (a / σ) = (1 + r) * β * (K * c1 ^ (-(1 / σ)) * P1 ^ (a / σ))) :
    c1 = (β * (1 + r)) ^ σ * (P1 / P0) ^ a * c0 := by
  have hs : -(1 / σ) ≠ 0 := neg_ne_zero.2 (one_div_pos.2 hσ).ne'
  rw [eq_iff_rpow_eq hc1 (by positivity) hs]
  have hq : ((P1 / P0) ^ a) ^ (-(1 / σ)) = P0 ^ (a / σ) / P1 ^ (a / σ) := by
    rw [← rpow_mul (div_pos hP1 hP0).le, show a * -(1 / σ) = -(a / σ) by ring,
      rpow_neg (div_pos hP1 hP0).le, div_rpow hP1.le hP0.le, inv_div]
  have hb : ((β * (1 + r)) ^ σ) ^ (-(1 / σ)) = (β * (1 + r))⁻¹ := by
    rw [← rpow_mul (by positivity), show σ * -(1 / σ) = -1 by field_simp, rpow_neg_one]
  rw [mul_rpow (by positivity) hc0.le, mul_rpow (by positivity) (by positivity), hb, hq]
  have hc0' := rpow_pos_of_pos hc0 (-(1 / σ))
  have hc1' := rpow_pos_of_pos hc1 (-(1 / σ))
  have hP0' := rpow_pos_of_pos hP0 (a / σ)
  have hP1' := rpow_pos_of_pos hP1 (a / σ)
  field_simp
  field_simp at h
  linarith

/-- Iterating the Euler growth equation: `C_s = ((β(1+r))^σ)^s (P_s/P_0)^a C_0`
(O&R §8.3.3). -/
theorem consumption_path {σ a β r : ℝ} {C PC : ℕ → ℝ} (hPC : ∀ s, 0 < PC s)
    (hg : ∀ s, C (s + 1) = (β * (1 + r)) ^ σ * (PC (s + 1) / PC s) ^ a * C s) (s : ℕ) :
    C s = ((β * (1 + r)) ^ σ) ^ s * (PC s / PC 0) ^ a * C 0 := by
  induction s with
  | zero => rw [div_self (hPC 0).ne', one_rpow]; ring
  | succ s ih =>
    rw [hg s, ih, pow_succ]
    have h : (PC (s + 1) / PC s) ^ a * (PC s / PC 0) ^ a = (PC (s + 1) / PC 0) ^ a := by
      rw [← mul_rpow (div_pos (hPC _) (hPC _)).le (div_pos (hPC _) (hPC _)).le]
      congr 1
      field_simp [(hPC s).ne']
    rw [← h]
    ring

/-- The weights of a positive consumption path: if `C_s = g_s C_0` with `C_0 > 0`, `g ≥ 0`,
`g_0 = 1`, and `Σ(1+r)^{−s} C_s = W`, then `C_0 = W / Σ(1+r)^{−s} g_s` (O&R §8.3.3). -/
theorem consumption_of_pv {r W : ℝ} {C g : ℕ → ℝ} (hr : 0 < 1 + r) (hC0 : 0 < C 0)
    (hg0 : g 0 = 1) (hg : ∀ s, 0 ≤ g s) (hpath : ∀ s, C s = g s * C 0)
    (hW : HasSum (fun s => (1 + r)⁻¹ ^ s * C s) W) :
    C 0 = W / ∑' s, (1 + r)⁻¹ ^ s * g s := by
  have hW' : HasSum (fun s => (1 + r)⁻¹ ^ s * g s) (W / C 0) := by
    have := hW.div_const (C 0)
    convert this using 1
    funext s
    rw [hpath s]
    field_simp
  have hpos : 0 < ∑' s, (1 + r)⁻¹ ^ s * g s := by
    have hle := hW'.summable.sum_le_tsum (Finset.range 1)
      (fun s _ => mul_nonneg (pow_pos (inv_pos.2 hr) s).le (hg s))
    simp only [Finset.sum_range_one, pow_zero, hg0, mul_one] at hle
    linarith
  rw [hW'.tsum_eq] at hpos ⊢
  have hW0 : W ≠ 0 := by
    intro h; rw [h, zero_div] at hpos; exact lt_irrefl _ hpos
  field_simp

/-- The discounted weights of §8.3.3: `(1+r)^{−s} ((β(1+r))^σ)^s (P_s/P_0)^a`, whose sum is the
denominator of the consumption function (O&R p. 536 and Exercise 3). -/
noncomputable def pvWeight (σ a β r : ℝ) (PC : ℕ → ℝ) (s : ℕ) : ℝ :=
  (1 + r)⁻¹ ^ s * (((β * (1 + r)) ^ σ) ^ s * (PC s / PC 0) ^ a)

/-- The product of consumption-based real interest factors
`1 + r^C_{v+1} = (1+r) P^C_v/P^C_{v+1}` telescopes to `(1+r)^s P^C_0/P^C_s` (O&R p. 535). -/
theorem prod_real_rate {r : ℝ} {PC : ℕ → ℝ} (hPC : ∀ s, 0 < PC s) (s : ℕ) :
    ∏ v ∈ Finset.range s, ((1 + r) * PC v / PC (v + 1)) = (1 + r) ^ s * PC 0 / PC s := by
  induction s with
  | zero => simp [div_self (hPC 0).ne']
  | succ s ih =>
    rw [Finset.prod_range_succ, ih, pow_succ]
    field_simp [(hPC s).ne', (hPC (s + 1)).ne']

/-- The weights in the book's notation (O&R p. 536):
`(1+r)^{−s}((β(1+r))^σ)^s (P_s/P_0)^{1−σ} = [Π_{v≤s}(1 + r^C_v)]^{σ−1} β^{σs}`. -/
theorem pvWeight_eq_book {σ β r : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r) {PC : ℕ → ℝ}
    (hPC : ∀ s, 0 < PC s) (s : ℕ) :
    pvWeight σ (1 - σ) β r PC s =
      (∏ v ∈ Finset.range s, ((1 + r) * PC v / PC (v + 1))) ^ (σ - 1) * (β ^ σ) ^ s := by
  rw [prod_real_rate hPC, pvWeight]
  have hP0 := hPC 0
  have hPs := hPC s
  have k1 : (1 + r)⁻¹ * (1 + r) ^ σ = (1 + r) ^ (σ - 1) := by
    rw [rpow_sub_one hr.ne']; field_simp
  have k2 : ((1 + r) ^ s) ^ (σ - 1) = ((1 + r) ^ (σ - 1)) ^ s := by
    rw [← rpow_natCast_mul hr.le, mul_comm, rpow_mul_natCast hr.le]
  have k3 : (PC s / PC 0) ^ (1 - σ) = (PC 0 / PC s) ^ (σ - 1) := by
    rw [show 1 - σ = -(σ - 1) by ring, rpow_neg (by positivity), ← inv_rpow (by positivity),
      inv_div]
  rw [mul_div_assoc, mul_rpow (pow_pos hr s).le (div_pos hP0 hPs).le, k2,
    mul_rpow hβ.le hr.le, k3, ← k1]
  ring

/-- **The real–monetary dichotomy holds iff `σ = θ`** (O&R p. 536, Exercise 3(c)–(d) and
Supplement p. 753, made precise). Equilibrium consumption is
`C_0 = W / Σ(1+r)^{−s}((β(1+r))^σ)^s (P^C_s/P^C_0)^{θ−σ}` (`ces_equilibrium_consumption`).
It is the same for EVERY path of the consumption-based price index (i.e. of nominal interest
rates) iff `σ = θ`: for `σ ≠ θ` a price index that steps up after date 0 changes `C_0`.
(Assumes `W ≠ 0` and `(1+r)^{−1}(β(1+r))^σ < 1`, so that constant paths have finite value.) -/
theorem dichotomy_iff {σ θ β r W : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r) (hW : W ≠ 0)
    (hq : (1 + r)⁻¹ * (β * (1 + r)) ^ σ < 1) :
    (∀ PC PC' : ℕ → ℝ, (∀ s, 0 < PC s) → (∀ s, 0 < PC' s) →
      Summable (pvWeight σ (θ - σ) β r PC) → Summable (pvWeight σ (θ - σ) β r PC') →
      W / ∑' s, pvWeight σ (θ - σ) β r PC s = W / ∑' s, pvWeight σ (θ - σ) β r PC' s) ↔
      σ = θ := by
  set q := (1 + r)⁻¹ * (β * (1 + r)) ^ σ with hqdef
  have hq0 : 0 < q := by positivity
  have hw : ∀ (PC : ℕ → ℝ) s, pvWeight σ (θ - σ) β r PC s = q ^ s * (PC s / PC 0) ^ (θ - σ) := by
    intro PC s; rw [pvWeight, hqdef, mul_pow]; ring
  constructor
  · intro h
    by_contra hne
    have ha : θ - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    set PC : ℕ → ℝ := fun _ => 1
    set PC' : ℕ → ℝ := fun s => if s = 0 then 1 else 2
    have hPC : ∀ s, 0 < PC s := fun _ => one_pos
    have hPC' : ∀ s, 0 < PC' s := fun s => by
      by_cases hs : s = 0 <;> simp [PC', hs]
    have hgeo := hasSum_geometric_of_lt_one hq0.le hq
    have hS : HasSum (pvWeight σ (θ - σ) β r PC) (1 - q)⁻¹ := by
      convert hgeo using 1; funext s; rw [hw]; simp [PC]
    set κ : ℝ := (2 : ℝ) ^ (θ - σ) with hκ
    have hS' : HasSum (pvWeight σ (θ - σ) β r PC') (κ * (1 - q)⁻¹ + (1 - κ)) := by
      have h1 := (hgeo.mul_left κ).add (hasSum_ite_eq 0 (1 - κ))
      convert h1 using 1
      funext s
      rw [hw]
      by_cases hs : s = 0
      · subst hs; simp [PC']
      · simp [PC', hs, hκ]; ring
    have hκ1 : κ ≠ 1 := by
      intro h1
      have := congrArg Real.log h1
      rw [hκ, Real.log_rpow two_pos, Real.log_one] at this
      exact ha ((mul_eq_zero.1 this).resolve_right (Real.log_pos one_lt_two).ne')
    have hq1 : 1 < (1 - q)⁻¹ := one_lt_inv_iff₀.2 ⟨by linarith, by linarith⟩
    have hκ0 : 0 < κ := by positivity
    have hSpos : 0 < (1 - q)⁻¹ := by linarith
    have hS'pos : 0 < κ * (1 - q)⁻¹ + (1 - κ) := by nlinarith
    have heq := h PC PC' hPC hPC' hS.summable hS'.summable
    rw [hS.tsum_eq, hS'.tsum_eq, div_eq_div_iff hSpos.ne' hS'pos.ne'] at heq
    have h2 : κ * (1 - q)⁻¹ + (1 - κ) = (1 - q)⁻¹ := by
      have := mul_left_cancel₀ hW heq
      linarith
    have h3 : (κ - 1) * ((1 - q)⁻¹ - 1) = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact hκ1 (by linarith)
    · linarith
  · intro h PC PC' _ _ _ _
    subst h
    simp only [pvWeight, sub_self, rpow_zero, mul_one]

/-- **With `σ = θ` CES-isoelastic utility is additively separable** (O&R p. 536 and Supplement
p. 753; this is why the dichotomy holds):
`u = [γ^{1/θ} C^{1−1/θ} + (1−γ)^{1/θ} m^{1−1/θ}]/(1−1/θ)`. -/
theorem cesUtility_separable {γ θ C m : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hC : 0 < C) (hm : 0 < m) :
    cesUtility γ θ θ C m =
      (γ ^ (1 / θ) * C ^ (1 - 1 / θ) + (1 - γ) ^ (1 / θ) * m ^ (1 - 1 / θ)) / (1 - 1 / θ) := by
  have hθm : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have hX := cesInner_pos (θ := θ) hγ0 hγ1 hC hm
  have e1 : (θ - 1) / θ = 1 - 1 / θ := by field_simp
  have e2 : θ / (θ - 1) * (1 - 1 / θ) = 1 := by field_simp
  rw [cesUtility, show cesIndex γ θ C m = cesInner γ θ C m ^ (θ / (θ - 1)) from rfl,
    ← rpow_mul hX.le, e2, rpow_one, cesInner, e1]

/-- Positivity of the CES marginal utilities (O&R p. 531: `u_C, u_{M/P} > 0`). -/
theorem cesMarg_pos {γ θ σ c k : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hc : 0 < c) (hk : 0 < k) :
    0 < cesMargC γ θ σ c k ∧ 0 < cesMargM γ θ σ c k := by
  have h1γ : 0 < 1 - γ := by linarith
  have hΩ := cesIndex_pos (θ := θ) hγ0 hγ1 hc hk
  exact ⟨by unfold cesMargC; positivity, by unfold cesMargM; positivity⟩

/-- **First-order conditions of the CES household, derived from optimality** (O&R §8.3.3):
at an optimal plan every user cost is positive, real balances are on the money-demand curve
`m_s = ((1−γ)/γ) ι_s^{−θ} C_s`, and consumption grows as
`C_{s+1} = (β(1+r))^σ (P^C_{s+1}/P^C_s)^{θ−σ} C_s`. -/
theorem ces_optimal_foc {γ θ σ β r A0 : ℝ} {y ι C m : ℕ → ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hr : 0 < 1 + r)
    (hopt : IsOptimal (cesUtility γ θ σ) β r A0 y ι C m) (s : ℕ) :
    0 < ι s ∧ m s = (1 - γ) / γ * ι s ^ (-θ) * C s ∧
      C (s + 1) = (β * (1 + r)) ^ σ *
        (cesPrice γ θ (ι (s + 1)) / cesPrice γ θ (ι s)) ^ (θ - σ) * C s := by
  have hdiff : ∀ c k, 0 < c → 0 < k → HasFDerivAt (fun p : ℝ × ℝ => cesUtility γ θ σ p.1 p.2)
      (grad (cesMargC γ θ σ c k) (cesMargM γ θ σ c k)) (c, k) :=
    fun c k hc hk => cesUtility_hasFDerivAt hγ0 hγ1 hθ hθ1 hσ hσ1 hc hk
  have hC := hopt.1.1
  have hm := hopt.1.2.1
  have hmo : ∀ t, cesMargM γ θ σ (C t) (m t) = ι t * cesMargC γ θ σ (C t) (m t) :=
    money_foc_of_optimal hβ hdiff hopt
  have hι : ∀ t, 0 < ι t := fun t => by
    obtain ⟨h1, h2⟩ := cesMarg_pos (θ := θ) (σ := σ) hγ0 hγ1 (hC t) (hm t)
    rw [hmo t] at h2
    exact (pos_iff_pos_of_mul_pos h2).2 h1
  have hdem : ∀ t, m t = (1 - γ) / γ * ι t ^ (-θ) * C t := fun t =>
    (ces_money_demand_iff hγ0 hγ1 hθ (hC t) (hm t) (hι t)).1 (hmo t)
  refine ⟨hι s, hdem s, ?_⟩
  have he := euler_of_optimal hβ hdiff hopt s
  rw [cesMargC_on_demand hγ0 hγ1 hθ hθ1 hσ (hC s) (hι s) (hdem s),
    cesMargC_on_demand hγ0 hγ1 hθ hθ1 hσ (hC (s + 1)) (hι (s + 1)) (hdem (s + 1))] at he
  exact euler_growth (by positivity) hσ hβ hr (hC s) (hC (s + 1))
    (cesPrice_pos hγ0 hγ1 (hι s)) (cesPrice_pos hγ0 hγ1 (hι (s + 1))) he

/-- **Equilibrium consumption as a function of the price-index path** (O&R Exercise 3(c)–(d),
p. 600, and the equilibrium counterpart of p. 536): if consumption follows
`C_{s+1} = (β(1+r))^σ (P^C_{s+1}/P^C_s)^a C_s` and satisfies the economy's constraint
`Σ(1+r)^{−s}C_s = W` (Exercise 3(a), `aggregate_budget`), then
`C_0 = W / Σ(1+r)^{−s}((β(1+r))^σ)^s (P^C_s/P^C_0)^a`. -/
theorem equilibrium_consumption {σ a β r W : ℝ} {C PC : ℕ → ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    (hC0 : 0 < C 0) (hPC : ∀ s, 0 < PC s)
    (hg : ∀ s, C (s + 1) = (β * (1 + r)) ^ σ * (PC (s + 1) / PC s) ^ a * C s)
    (hW : HasSum (fun s => (1 + r)⁻¹ ^ s * C s) W) :
    C 0 = W / ∑' s, pvWeight σ a β r PC s := by
  have h := consumption_of_pv (g := fun s => ((β * (1 + r)) ^ σ) ^ s * (PC s / PC 0) ^ a) hr hC0
    (by simp [div_self (hPC 0).ne'])
    (fun s => mul_nonneg (pow_nonneg (rpow_nonneg (by positivity) _) _)
      (rpow_nonneg (div_pos (hPC s) (hPC 0)).le _)) (consumption_path hPC hg) hW
  rw [h]
  rfl

/-- **The book's individual consumption function (§8.3.3, p. 536)**: if consumption follows the
Euler growth equation, the price index satisfies `D_s = (P^C_s)^{1−θ}` and total expenditure
`C_s D_s/γ` (`expenditure_on_demand`) has present value `W`, then
`C_0 = γ (P^C_0)^{θ−1} W / Σ(1+r)^{−s}((β(1+r))^σ)^s (P^C_s/P^C_0)^{1−σ}`; by
`pvWeight_eq_book` the denominator is the book's `P^C Σ[Π(1+r^C_v)]^{σ−1}β^{σ(s−t)}`/`P^C`.
Context: O&R §8.3, pp. 530–538. -/
theorem individual_consumption {γ θ σ β r W : ℝ} {C PC D : ℕ → ℝ} (hγ0 : 0 < γ) (hβ : 0 < β)
    (hr : 0 < 1 + r) (hC : ∀ s, 0 < C s) (hPC : ∀ s, 0 < PC s) (hD : ∀ s, D s = PC s ^ (1 - θ))
    (hg : ∀ s, C (s + 1) = (β * (1 + r)) ^ σ * (PC (s + 1) / PC s) ^ (θ - σ) * C s)
    (hW : HasSum (fun s => (1 + r)⁻¹ ^ s * (C s * D s / γ)) W) :
    C 0 = γ * PC 0 ^ (θ - 1) * W / ∑' s, pvWeight σ (1 - σ) β r PC s := by
  have hP0 := hPC 0
  have hpath := consumption_path hPC hg
  have key : ∀ s, C s * D s / γ =
      (((β * (1 + r)) ^ σ) ^ s * (PC s / PC 0) ^ (1 - σ)) * (C 0 * D 0 / γ) := by
    intro s
    rw [hpath s, hD s, hD 0]
    have hx := div_pos (hPC s) hP0
    have h1 : (PC s / PC 0) ^ (1 - σ) = (PC s / PC 0) ^ (θ - σ) * (PC s / PC 0) ^ (1 - θ) := by
      rw [← rpow_add hx]; congr 1; ring
    have h2 : (PC s / PC 0) ^ (1 - θ) * PC 0 ^ (1 - θ) = PC s ^ (1 - θ) := by
      rw [← mul_rpow hx.le hP0.le, div_mul_cancel₀ _ hP0.ne']
    rw [h1]
    linear_combination (-(((β * (1 + r)) ^ σ) ^ s * (PC s / PC 0) ^ (θ - σ) * C 0 / γ)) * h2
  have hD0 : 0 < D 0 := by rw [hD 0]; exact rpow_pos_of_pos hP0 _
  have h := consumption_of_pv (C := fun s => C s * D s / γ)
    (g := fun s => ((β * (1 + r)) ^ σ) ^ s * (PC s / PC 0) ^ (1 - σ)) hr
    (div_pos (mul_pos (hC 0) hD0) hγ0) (by simp [div_self hP0.ne'])
    (fun s => mul_nonneg (pow_nonneg (rpow_nonneg (by positivity) _) _)
      (rpow_nonneg (div_pos (hPC s) hP0).le _)) key hW
  have hsum : ∑' s, (1 + r)⁻¹ ^ s * (((β * (1 + r)) ^ σ) ^ s * (PC s / PC 0) ^ (1 - σ)) =
      ∑' s, pvWeight σ (1 - σ) β r PC s := rfl
  rw [hsum] at h
  have hθ' : PC 0 ^ (θ - 1) * D 0 = 1 := by
    rw [hD 0, ← rpow_add hP0]; simp
  calc C 0 = C 0 * (PC 0 ^ (θ - 1) * D 0) := by rw [hθ', mul_one]
    _ = γ * PC 0 ^ (θ - 1) * (C 0 * D 0 / γ) := by field_simp
    _ = _ := by rw [h]; ring

/-- **The §8.3.3 consumption function, derived from optimality** (O&R p. 536): for
CES-isoelastic preferences (`σ, θ ≠ 1`) and summable discounted income, every optimal plan has
`C_0 = γ (P^C_0)^{θ−1} W / Σ(1+r)^{−s}((β(1+r))^σ)^s (P^C_s/P^C_0)^{1−σ}`, where
`W = (1+r)B_0 + M_{−1}/P_0 + Σ(1+r)^{−s}(Y_s − T_s)` is lifetime wealth. -/
theorem ces_optimal_consumption {γ θ σ β r A0 : ℝ} {y ι C m : ℕ → ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β)
    (hr : 0 < 1 + r) (hy : Summable (fun s => (1 + r)⁻¹ ^ s * y s))
    (hopt : IsOptimal (cesUtility γ θ σ) β r A0 y ι C m) :
    C 0 = γ * cesPrice γ θ (ι 0) ^ (θ - 1) * (A0 + ∑' s, (1 + r)⁻¹ ^ s * y s) /
      ∑' s, pvWeight σ (1 - σ) β r (fun s => cesPrice γ θ (ι s)) s := by
  have hfoc := ces_optimal_foc hγ0 hγ1 hθ hθ1 hσ hσ1 hβ hr hopt
  have hdiff : ∀ c k, 0 < c → 0 < k → HasFDerivAt (fun p : ℝ × ℝ => cesUtility γ θ σ p.1 p.2)
      (grad (cesMargC γ θ σ c k) (cesMargM γ θ σ c k)) (c, k) :=
    fun c k hc hk => cesUtility_hasFDerivAt hγ0 hγ1 hθ hθ1 hσ hσ1 hc hk
  have htvc := transversality_of_optimal hr (fun k hk => strictMonoOn_of_uC_pos hdiff
    (fun _ _ hc hk => (cesMarg_pos (θ := θ) (σ := σ) hγ0 hγ1 hc hk).1) hk) hopt
  obtain ⟨⟨hC, hm, _, hnp⟩, _⟩ := hopt
  have hbud := (intertemporal_budget hr hC hm (fun s => (hfoc s).1.le) hy hnp htvc).2
  refine individual_consumption (D := fun s => cesDenom γ θ (ι s)) hγ0 hβ hr hC
    (fun s => cesPrice_pos hγ0 hγ1 (hfoc s).1)
    (fun s => (cesPrice_rpow_one_sub hγ0 hγ1 (hfoc s).1 hθ1).symm) (fun s => (hfoc s).2.2) ?_
  convert hbud using 1
  funext s
  rw [expenditure_on_demand hγ0 (hfoc s).1 (hfoc s).2.1]

/-- **Equilibrium consumption for CES-isoelastic preferences** (O&R p. 536, Exercise 3(d)):
if the household's plan is optimal and satisfies the economy's constraint
`Σ(1+r)^{−s}C_s = W`, then `C_0 = W / Σ(1+r)^{−s}((β(1+r))^σ)^s (P^C_s/P^C_0)^{θ−σ}`. By
`dichotomy_iff` this is independent of the path of nominal interest rates iff `σ = θ`. -/
theorem ces_equilibrium_consumption {γ θ σ β r A0 W : ℝ} {y ι C m : ℕ → ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β)
    (hr : 0 < 1 + r) (hopt : IsOptimal (cesUtility γ θ σ) β r A0 y ι C m)
    (hW : HasSum (fun s => (1 + r)⁻¹ ^ s * C s) W) :
    C 0 = W / ∑' s, pvWeight σ (θ - σ) β r (fun s => cesPrice γ θ (ι s)) s := by
  have hfoc := ces_optimal_foc hγ0 hγ1 hθ hθ1 hσ hσ1 hβ hr hopt
  exact equilibrium_consumption hβ hr (hopt.1.1 0) (fun s => cesPrice_pos hγ0 hγ1 (hfoc s).1)
    (fun s => (hfoc s).2.2) hW

/-! ### The special case `σ = θ = 1` (p. 536) -/

/-- **Existence and closed form for `σ = θ = 1`** (O&R p. 536): with
`u = γ log C + (1−γ) log(M/P)`, `0 < β < 1`, positive user costs and lifetime wealth
`W = A_0 + Σ(1+r)^{−s} y_s > 0`, the plan `C_s = γ(1−β)W(β(1+r))^s`,
`m_s = (1−γ)(1−β)W(β(1+r))^s/ι_s` is optimal; in particular `C_0 = γ(1−β)W`. (Summability of
`β^s log ι_s` makes lifetime utility finite.) -/
theorem logCD_isOptimal {γ β r A0 W : ℝ} {y ι : ℕ → ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hr : 0 < 1 + r) (hι : ∀ s, 0 < ι s)
    (hy : HasSum (fun s => (1 + r)⁻¹ ^ s * y s) (W - A0)) (hW : 0 < W)
    (hlog : Summable (fun s => β ^ s * Real.log (ι s))) :
    IsOptimal (fun c k => γ * Real.log c + (1 - γ) * Real.log k) β r A0 y ι
      (fun s => γ * (1 - β) * W * (β * (1 + r)) ^ s)
      (fun s => (1 - γ) * (1 - β) * W * (β * (1 + r)) ^ s / ι s) := by
  have h1γ : 0 < 1 - γ := by linarith
  have h1β : 0 < 1 - β := by linarith
  set K := β * (1 + r) with hK
  have hK0 : 0 < K := by positivity
  clear_value K
  have hconc : ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0)
      (fun p : ℝ × ℝ => γ * Real.log p.1 + (1 - γ) * Real.log p.2) :=
    separable_concaveOn (strictConcaveOn_log_Ioi.concaveOn.smul hγ0.le)
      (strictConcaveOn_log_Ioi.concaveOn.smul h1γ.le)
  have hdiff : ∀ c k, 0 < c → 0 < k → HasFDerivAt
      (fun p : ℝ × ℝ => γ * Real.log p.1 + (1 - γ) * Real.log p.2)
      (grad (γ * c⁻¹) ((1 - γ) * k⁻¹)) (c, k) := fun c k hc hk =>
    separable_hasFDerivAt ((Real.hasDerivAt_log hc.ne').const_mul γ)
      ((Real.hasDerivAt_log hk.ne').const_mul (1 - γ))
  have hCpos : ∀ s, 0 < γ * (1 - β) * W * K ^ s := fun s => by positivity
  have hmpos : ∀ s, 0 < (1 - γ) * (1 - β) * W * K ^ s / ι s := fun s => by
    have := hι s; positivity
  -- lifetime utility is finite
  have hu : ∀ s, β ^ s * (γ * Real.log (γ * (1 - β) * W * K ^ s) +
      (1 - γ) * Real.log ((1 - γ) * (1 - β) * W * K ^ s / ι s)) =
      (γ * Real.log (γ * (1 - β) * W) + (1 - γ) * Real.log ((1 - γ) * (1 - β) * W)) * β ^ s +
      Real.log K * ((s : ℝ) ^ 1 * β ^ s) - (1 - γ) * (β ^ s * Real.log (ι s)) := by
    intro s
    have hK' := pow_pos hK0 s
    rw [Real.log_mul (by positivity) hK'.ne', Real.log_div (by positivity) (hι s).ne',
      Real.log_mul (by positivity) hK'.ne', Real.log_pow]
    ring
  have hsum : Summable (fun s => β ^ s * (γ * Real.log (γ * (1 - β) * W * K ^ s) +
      (1 - γ) * Real.log ((1 - γ) * (1 - β) * W * K ^ s / ι s))) := by
    simp only [hu]
    have hβn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
    exact (((summable_geometric_of_lt_one hβ0.le hβ1).mul_left _).add
      ((summable_pow_mul_geometric_of_norm_lt_one 1 hβn).mul_left _)).sub (hlog.mul_left _)
  -- present value of expenditure equals wealth, so the TVC holds with equality
  have hexp : HasSum (fun s => (1 + r)⁻¹ ^ s * (γ * (1 - β) * W * K ^ s +
      ι s * ((1 - γ) * (1 - β) * W * K ^ s / ι s))) (A0 + ∑' s, (1 + r)⁻¹ ^ s * y s) := by
    rw [hy.tsum_eq, show A0 + (W - A0) = (1 - β) * W * (1 - β)⁻¹ by field_simp; ring]
    have := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left ((1 - β) * W)
    convert this using 1
    funext s
    have hιs := (hι s).ne'
    have hd : (1 + r)⁻¹ ^ s * K ^ s = β ^ s := by
      rw [← mul_pow, hK]; congr 1; field_simp
    field_simp
    linear_combination hd
  have hlim := tendsto_wealth_of_budget hr hy.summable hexp
  refine isOptimal_of_foc hβ0 hr hconc hdiff
    ⟨hCpos, hmpos, hsum, noPonzi_of_tendsto hlim⟩ (by have := hCpos 0; positivity)
    (fun s => ?_) (fun s => ?_) (transversality_of_tendsto hlim)
  · have := hCpos s
    rw [pow_succ, hK]
    field_simp
  · have := hCpos s
    have := hι s
    field_simp

/-- **Necessity of the closed form for `σ = θ = 1`** (O&R p. 536): every optimal plan for
`u = γ log C + (1−γ) log(M/P)` (with `0 < β < 1` and summable discounted income) has
`C_0 = γ(1−β)[(1+r)B_0 + M_{−1}/P_0 + Σ(1+r)^{−s}(Y_s − T_s)]`. -/
theorem logCD_optimal_consumption {γ β r A0 W : ℝ} {y ι C m : ℕ → ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hr : 0 < 1 + r)
    (hy : HasSum (fun s => (1 + r)⁻¹ ^ s * y s) (W - A0))
    (hopt : IsOptimal (fun c k => γ * Real.log c + (1 - γ) * Real.log k) β r A0 y ι C m) :
    C 0 = γ * (1 - β) * W := by
  have h1γ : 0 < 1 - γ := by linarith
  have hconc : ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0)
      (fun p : ℝ × ℝ => γ * Real.log p.1 + (1 - γ) * Real.log p.2) :=
    separable_concaveOn (strictConcaveOn_log_Ioi.concaveOn.smul hγ0.le)
      (strictConcaveOn_log_Ioi.concaveOn.smul h1γ.le)
  have hdiff : ∀ c k, 0 < c → 0 < k → HasFDerivAt
      (fun p : ℝ × ℝ => γ * Real.log p.1 + (1 - γ) * Real.log p.2)
      (grad (γ * c⁻¹) ((1 - γ) * k⁻¹)) (c, k) := fun c k hc hk =>
    separable_hasFDerivAt ((Real.hasDerivAt_log hc.ne').const_mul γ)
      ((Real.hasDerivAt_log hk.ne').const_mul (1 - γ))
  obtain ⟨⟨hC, hm, hsu, hnp⟩, he, hmo, htvc⟩ :=
    (isOptimal_iff hβ0 hr hconc hdiff (fun c _ hc _ => by positivity)).1 hopt
  have hιm : ∀ s, ι s * m s = (1 - γ) / γ * C s := fun s => by
    have h := hmo s
    have := hC s
    have := hm s
    field_simp at h ⊢
    linarith
  have hι : ∀ s, 0 ≤ ι s := fun s => by
    have h := hιm s
    have := hC s
    have := hm s
    have h2 : 0 < ι s * m s := by rw [h]; positivity
    exact (pos_of_mul_pos_left h2 (hm s).le).le
  have hpath : ∀ s, C s = (β * (1 + r)) ^ s * C 0 := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      have h := he s
      have := hC s
      have := hC (s + 1)
      field_simp at h
      rw [pow_succ]
      nlinarith [ih]
  have hbud := (intertemporal_budget hr hC hm hι hy.summable hnp htvc).2
  rw [hy.tsum_eq, add_sub_cancel] at hbud
  have hgeo := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left (C 0 / γ)
  have heq : (fun s => (1 + r)⁻¹ ^ s * (C s + ι s * m s)) = fun s => C 0 / γ * β ^ s := by
    funext s
    rw [hιm s, hpath s]
    have hd : (1 + r)⁻¹ ^ s * (β * (1 + r)) ^ s = β ^ s := by
      rw [← mul_pow]; congr 1; field_simp
    field_simp
    linear_combination C 0 * hd
  rw [heq] at hbud
  have := hbud.unique hgeo
  have h1β : 0 < 1 - β := by linarith
  field_simp at this
  linarith

/-- **`σ = θ = 1` in equilibrium** (O&R Exercise 3(c), p. 601, "what happens when `σ = 1`"):
with `u = γ log C + (1−γ) log(M/P)`, an optimal plan that satisfies the economy's constraint
`Σ(1+r)^{−s}C_s = W` has `C_0 = (1−β)W`, whatever the path of nominal interest rates. -/
theorem logCD_equilibrium_consumption {γ β r A0 W : ℝ} {y ι C m : ℕ → ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hr : 0 < 1 + r)
    (hopt : IsOptimal (fun c k => γ * Real.log c + (1 - γ) * Real.log k) β r A0 y ι C m)
    (hW : HasSum (fun s => (1 + r)⁻¹ ^ s * C s) W) : C 0 = (1 - β) * W := by
  have h1γ : 0 < 1 - γ := by linarith
  have hdiff : ∀ c k, 0 < c → 0 < k → HasFDerivAt
      (fun p : ℝ × ℝ => γ * Real.log p.1 + (1 - γ) * Real.log p.2)
      (grad (γ * c⁻¹) ((1 - γ) * k⁻¹)) (c, k) := fun c k hc hk =>
    separable_hasFDerivAt ((Real.hasDerivAt_log hc.ne').const_mul γ)
      ((Real.hasDerivAt_log hk.ne').const_mul (1 - γ))
  have he := euler_of_optimal hβ0 hdiff hopt
  have hC := hopt.1.1
  have hg : ∀ s, C (s + 1) = (β * (1 + r)) ^ (1 : ℝ) * ((fun _ => (1 : ℝ)) (s + 1) /
      (fun _ => (1 : ℝ)) s) ^ (0 : ℝ) * C s := by
    intro s
    have h := he s
    have := hC s
    have := hC (s + 1)
    simp only [rpow_one, rpow_zero, mul_one]
    field_simp at h
    nlinarith
  have h := equilibrium_consumption hβ0 hr (hC 0) (fun _ => one_pos) hg hW
  have hq : ∀ s, pvWeight 1 0 β r (fun _ => (1 : ℝ)) s = β ^ s := fun s => by
    rw [pvWeight, rpow_one, rpow_zero, mul_one, ← mul_pow]
    congr 1
    field_simp
  simp only [hq, tsum_geometric_of_lt_one hβ0.le hβ1] at h
  rw [h]
  field_simp

/-! ### Cobb–Douglas-isoelastic preferences (39) and money demand (40) -/

/-- The period utility (39), O&R p. 534: `u = [C^γ (M/P)^{1−γ}]^{1−1/σ}/(1 − 1/σ)`. -/
noncomputable def cdUtility (γ σ C m : ℝ) : ℝ := (C ^ γ * m ^ (1 - γ)) ^ (1 - 1 / σ) / (1 - 1 / σ)

/-- Marginal utility of consumption for (39): `u_C = γ [C^γ m^{1−γ}]^{1−1/σ}/C`.
Context: O&R §8.3, pp. 530–538. -/
noncomputable def cdMargC (γ σ C m : ℝ) : ℝ := γ * (C ^ γ * m ^ (1 - γ)) ^ (1 - 1 / σ) / C

/-- Marginal utility of real balances for (39): `u_{M/P} = (1−γ)[C^γ m^{1−γ}]^{1−1/σ}/m`.
Context: O&R §8.3, pp. 530–538. -/
noncomputable def cdMargM (γ σ C m : ℝ) : ℝ :=
  (1 - γ) * (C ^ γ * m ^ (1 - γ)) ^ (1 - 1 / σ) / m

/-- **The gradient of (39)** (O&R p. 534): on the positive quadrant the utility (39) is
differentiable with partial derivatives `cdMargC`, `cdMargM`. -/
theorem cdUtility_hasFDerivAt {γ σ c k : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hc : 0 < c)
    (hk : 0 < k) :
    HasFDerivAt (fun p : ℝ × ℝ => cdUtility γ σ p.1 p.2) (grad (cdMargC γ σ c k)
      (cdMargM γ σ c k)) (c, k) := by
  have hσ' : 1 - 1 / σ ≠ 0 := by
    intro h; apply hσ1; field_simp at h; linarith
  have hs : (1 - σ⁻¹)⁻¹ * (1 - σ⁻¹) = 1 := inv_mul_cancel₀ (by rwa [one_div] at hσ')
  have hf1 : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) (c, k) :=
    hasFDerivAt_fst
  have hf2 : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) (c, k) :=
    hasFDerivAt_snd
  have h1 := (Real.hasDerivAt_rpow_const (x := c) (p := γ) (Or.inl hc.ne')).comp_hasFDerivAt
    (c, k) hf1
  have h2 := (Real.hasDerivAt_rpow_const (x := k) (p := 1 - γ) (Or.inl hk.ne')).comp_hasFDerivAt
    (c, k) hf2
  have hX : 0 < c ^ γ * k ^ (1 - γ) := by positivity
  have hU := ((h1.mul h2).rpow_const (p := 1 - 1 / σ) (Or.inl hX.ne')).mul_const
    ((1 - 1 / σ)⁻¹)
  have hfun : (fun p : ℝ × ℝ => cdUtility γ σ p.1 p.2) =
      fun p => (p.1 ^ γ * p.2 ^ (1 - γ)) ^ (1 - 1 / σ) * (1 - 1 / σ)⁻¹ := by
    funext p; rw [cdUtility, div_eq_mul_inv]
  rw [hfun]
  have hXs : (c ^ γ * k ^ (1 - γ)) ^ (1 - 1 / σ) =
      (c ^ γ * k ^ (1 - γ)) * (c ^ γ * k ^ (1 - γ)) ^ (1 - 1 / σ - 1) := by
    rw [rpow_sub_one hX.ne']; field_simp
  have hcγ : c ^ (γ - 1) = c ^ γ / c := rpow_sub_one hc.ne' γ
  have hkγ : k ^ (1 - γ - 1) = k ^ (1 - γ) / k := rpow_sub_one hk.ne' (1 - γ)
  have hA : (1 - 1 / σ)⁻¹ * ((1 - 1 / σ) * (c ^ γ * k ^ (1 - γ)) ^ (1 - 1 / σ - 1) *
      (k ^ (1 - γ) * (γ * c ^ (γ - 1)))) = cdMargC γ σ c k := by
    rw [cdMargC, hXs, hcγ]
    field_simp
  have hB : (1 - 1 / σ)⁻¹ * ((1 - 1 / σ) * (c ^ γ * k ^ (1 - γ)) ^ (1 - 1 / σ - 1) *
      (c ^ γ * ((1 - γ) * k ^ (1 - γ - 1)))) = cdMargM γ σ c k := by
    rw [cdMargM, hXs, hkγ]
    field_simp
  rw [← hA, ← hB]
  refine hU.congr_fderiv ?_
  ext <;> simp [grad_apply]

/-- **Money demand (40)**, O&R p. 534: for the utility (39), the condition (37)
`u_{M/P} = ι u_C` holds iff `M/P = ((1−γ)/γ) C/ι`. -/
theorem cd_money_demand_iff {γ σ c k ι : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hc : 0 < c)
    (hk : 0 < k) (hι : 0 < ι) :
    cdMargM γ σ c k = ι * cdMargC γ σ c k ↔ k = (1 - γ) / γ * c / ι := by
  have hX := rpow_pos_of_pos (mul_pos (rpow_pos_of_pos hc γ) (rpow_pos_of_pos hk (1 - γ)))
    (1 - 1 / σ)
  have h1γ : 0 < 1 - γ := by linarith
  unfold cdMargM cdMargC
  constructor
  · intro h
    field_simp at h ⊢
    nlinarith
  · intro h
    rw [h]
    field_simp

/-- (40) in the book's form, O&R p. 534: with the user cost `ι = i/(1+i)` (`i > 0`),
`((1−γ)/γ) C/ι = ((1−γ)/γ)(1 + 1/i) C`. -/
theorem cd_money_demand_book {γ c i : ℝ} (hi : 0 < i) :
    (1 - γ) / γ * c / (i / (1 + i)) = (1 - γ) / γ * (1 + 1 / i) * c := by
  have : 0 < 1 + i := by linarith
  field_simp
  ring

/-- **Marginal utility of consumption on the money-demand curve for (39)** (O&R p. 534, the
`θ = 1` case of Supplement p. 752): `u_C = γ((1−γ)/γ)^{(1−γ)(1−1/σ)} C^{−1/σ} (ι^{1−γ})^{(1−σ)/σ}`,
so the consumption-based price index is `P^C = ι^{1−γ}`. -/
theorem cdMargC_on_demand {γ σ c ι : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hσ : 0 < σ) (hc : 0 < c)
    (hι : 0 < ι) :
    cdMargC γ σ c ((1 - γ) / γ * c / ι) = γ * ((1 - γ) / γ) ^ ((1 - γ) * (1 - 1 / σ)) *
      c ^ (-(1 / σ)) * (ι ^ (1 - γ)) ^ ((1 - σ) / σ) := by
  have h1γ : 0 < 1 - γ := by linarith
  have hA : 0 < (1 - γ) / γ := by positivity
  have hX : c ^ γ * ((1 - γ) / γ * c / ι) ^ (1 - γ) =
      c * (((1 - γ) / γ) ^ (1 - γ) * (ι ^ (1 - γ))⁻¹) := by
    rw [div_rpow (by positivity) hι.le, mul_rpow hA.le hc.le, ← inv_rpow hι.le]
    have : c ^ γ * c ^ (1 - γ) = c := by rw [← rpow_add hc]; simp
    rw [inv_rpow hι.le]
    field_simp
    linear_combination this
  unfold cdMargC
  rw [hX, mul_rpow hc.le (by positivity), mul_rpow (by positivity) (by positivity),
    ← rpow_mul hA.le, inv_rpow (by positivity), ← rpow_neg (by positivity)]
  have e1 : c ^ (1 - 1 / σ) / c = c ^ (-(1 / σ)) := by
    rw [← rpow_sub_one hc.ne']; congr 1; ring
  have e2 : -(1 - 1 / σ) = (1 - σ) / σ := by field_simp; ring
  rw [e2, ← e1]
  ring

/-- **Exercise 3(c)**, O&R p. 600: with `θ = 1` (utility (39), `σ ≠ 1`), an optimal plan that
satisfies the economy's constraint `Σ(1+r)^{−s}C_s = W` has
`C_0 = W / Σ(1+r)^{−s}((β(1+r))^σ)^s (P^C_s/P^C_0)^{1−σ}` with `P^C_s = ι_s^{1−γ}`; by
`pvWeight_eq_book` the denominator is `Σ [Π_{v=1}^{s}(1 + r^C_v)]^{σ−1} β^{σ s}`, the book's
formula. The Euler equation behind it is the hint's
`C_{s+1} = (P^C_s/P^C_{s+1})^{σ−1}(1+r)^σ β^σ C_s`. -/
theorem cd_equilibrium_consumption {γ σ β r A0 W : ℝ} {y ι C m : ℕ → ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hr : 0 < 1 + r)
    (hopt : IsOptimal (cdUtility γ σ) β r A0 y ι C m)
    (hW : HasSum (fun s => (1 + r)⁻¹ ^ s * C s) W) :
    (∀ s, 0 < ι s) ∧ C 0 = W / ∑' s, pvWeight σ (1 - σ) β r (fun s => ι s ^ (1 - γ)) s := by
  have h1γ : 0 < 1 - γ := by linarith
  have hdiff : ∀ c k, 0 < c → 0 < k → HasFDerivAt (fun p : ℝ × ℝ => cdUtility γ σ p.1 p.2)
      (grad (cdMargC γ σ c k) (cdMargM γ σ c k)) (c, k) :=
    fun c k hc hk => cdUtility_hasFDerivAt hσ hσ1 hc hk
  have hC := hopt.1.1
  have hm := hopt.1.2.1
  have hmo := money_foc_of_optimal hβ hdiff hopt
  have hι : ∀ t, 0 < ι t := fun t => by
    have hX := rpow_pos_of_pos (mul_pos (rpow_pos_of_pos (hC t) γ)
      (rpow_pos_of_pos (hm t) (1 - γ))) (1 - 1 / σ)
    have h1 : 0 < cdMargC γ σ (C t) (m t) := by unfold cdMargC; have := hC t; positivity
    have h2 : 0 < cdMargM γ σ (C t) (m t) := by unfold cdMargM; have := hm t; positivity
    rw [hmo t] at h2
    exact (pos_iff_pos_of_mul_pos h2).2 h1
  have hdem : ∀ t, m t = (1 - γ) / γ * C t / ι t := fun t =>
    (cd_money_demand_iff hγ0 hγ1 (hC t) (hm t) (hι t)).1 (hmo t)
  refine ⟨hι, equilibrium_consumption hβ hr (hC 0) (fun s => rpow_pos_of_pos (hι s) _)
    (fun s => ?_) hW⟩
  have he := euler_of_optimal hβ hdiff hopt s
  rw [hdem s, hdem (s + 1), cdMargC_on_demand hγ0 hγ1 hσ (hC s) (hι s),
    cdMargC_on_demand hγ0 hγ1 hσ (hC (s + 1)) (hι (s + 1))] at he
  exact euler_growth (by positivity) hσ hβ hr (hC s) (hC (s + 1))
    (rpow_pos_of_pos (hι s) _) (rpow_pos_of_pos (hι (s + 1)) _) he

/-! ## Dollarization (§8.3.8) -/

/-- The foreign-currency transactions technology (62), O&R p. 551: `g(x) = a₀x − (a₁/2)x²`. -/
noncomputable def gDollar (a0 a1 x : ℝ) : ℝ := a0 * x - a1 / 2 * x ^ 2

/-- `g'(x) = a₀ − a₁x` (O&R (62)). -/
theorem gDollar_hasDerivAt (a0 a1 x : ℝ) : HasDerivAt (gDollar a0 a1) (a0 - a1 * x) x := by
  have h := ((hasDerivAt_id' x).const_mul a0).sub ((hasDerivAt_pow 2 x).const_mul (a1 / 2))
  unfold gDollar
  convert h using 1
  push_cast
  ring

/-- Footnote 41, O&R p. 552: the quadratic (62) is increasing exactly where
`a₀ − a₁x > 0`, i.e. `x < a₀/a₁`. -/
theorem gDollar_increasing_iff {a0 a1 x : ℝ} (ha1 : 0 < a1) : 0 < a0 - a1 * x ↔ x < a0 / a1 := by
  rw [lt_div_iff₀ ha1]
  constructor <;> intro h <;> linarith

/-- **The currency-substitution condition**, O&R p. 552: from (65) and (66) (after (64),
`u'(C_t) = u'(C_{t+1}) = U`), `g'(M_F/P^*) = (1 − βP^*_t/P^*_{t+1})/(1 − βP_t/P_{t+1})`, provided
home nominal rates are positive, `1 − βP_t/P_{t+1} > 0` (implicit in the book). -/
theorem dollar_foc_ratio {U V g' β P0 P1 Q0 Q1 : ℝ} (hU : 0 < U) (hP0 : 0 < P0) (hP1 : 0 < P1)
    (hQ0 : 0 < Q0) (hQ1 : 0 < Q1) (h65 : U / P0 = V / P0 + β * U / P1)
    (h66 : U / Q0 = V * g' / Q0 + β * U / Q1) (hpos : 0 < 1 - β * P0 / P1) :
    g' = (1 - β * Q0 / Q1) / (1 - β * P0 / P1) := by
  have hV : V = U * (1 - β * P0 / P1) := by field_simp at h65 ⊢; linarith
  have hVg : V * g' = U * (1 - β * Q0 / Q1) := by field_simp at h66 ⊢; linarith
  rw [eq_div_iff hpos.ne']
  rw [hV] at hVg
  have := mul_left_cancel₀ hU.ne' (by linarith : U * (g' * (1 - β * P0 / P1)) =
    U * (1 - β * Q0 / Q1))
  exact this

/-- **Foreign-currency demand (67) with its corner**, O&R p. 553: with `a₁ > 0` and
`R = (1 − βP^*_t/P^*_{t+1})/(1 − βP_t/P_{t+1})`, the Kuhn–Tucker conditions of the choice of
`x = M_F/P^* ≥ 0` (marginal liquidity `g'(x) = a₀ − a₁x` at most `R`, with equality if `x > 0`)
hold iff `x = max(0, (a₀ − R)/a₁)`. -/
theorem dollar_demand_iff {a0 a1 R x : ℝ} (ha1 : 0 < a1) :
    (0 ≤ x ∧ a0 - a1 * x ≤ R ∧ (0 < x → a0 - a1 * x = R)) ↔ x = max 0 ((a0 - R) / a1) := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    rcases h0.lt_or_eq with hpos | hzero
    · have := h2 hpos
      have hx : x = (a0 - R) / a1 := by field_simp; linarith
      rw [max_eq_right (by rw [← hx]; exact h0)]
      exact hx
    · subst hzero
      rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) ha1.le)]
  · intro hx
    rcases le_or_gt (a0 - R) 0 with hle | hgt
    · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg hle ha1.le)] at hx
      subst hx
      exact ⟨le_rfl, by linarith, fun h => absurd h (lt_irrefl 0)⟩
    · have hd : 0 < (a0 - R) / a1 := div_pos hgt ha1
      rw [max_eq_right hd.le] at hx
      subst hx
      refine ⟨hd.le, ?_, fun _ => ?_⟩ <;> field_simp <;> linarith

/-- The currency-substitution ratio `R(pi, pi^*) = (1 − β/pi^*)/(1 − β/pi)` in terms of gross home
and foreign inflation (O&R (67), p. 553). -/
noncomputable def substRatio (β pi pis : ℝ) : ℝ := (1 - β / pis) / (1 - β / pi)

/-- O&R p. 552: "no point using foreign currency when anticipated home inflation is less than or
equal to foreign inflation": if `β < pi ≤ pi^*` then `R ≥ 1 ≥ a₀`, so `M_F = 0`. -/
theorem dollar_zero_of_low_inflation {β pi pis a0 a1 : ℝ} (hβ : 0 < β) (hpi : β < pi)
    (hpipi : pi ≤ pis) (ha0 : a0 ≤ 1) (ha1 : 0 < a1) :
    max 0 ((a0 - substRatio β pi pis) / a1) = 0 := by
  have hpi0 : 0 < pi := by linarith
  have hden : 0 < 1 - β / pi := by rw [sub_pos, div_lt_one hpi0]; exact hpi
  have hR : 1 ≤ substRatio β pi pis := by
    rw [substRatio, le_div_iff₀ hden, one_mul]
    have : β / pis ≤ β / pi := div_le_div_of_nonneg_left hβ.le hpi0 hpipi
    linarith
  exact max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) ha1.le)

/-- O&R p. 553: on the interior region foreign-currency holdings `(a₀ − R)/a₁` are strictly
increasing in home inflation, since `R` falls as `pi` rises (for `β < pi < pi'` and `β < pi^*`). -/
theorem substRatio_strictAnti {β pi pi' pis : ℝ} (hβ : 0 < β) (hpi : β < pi) (hpipi' : pi < pi')
    (hpis : β < pis) : substRatio β pi' pis < substRatio β pi pis := by
  have hpi0 : 0 < pi := by linarith
  have hpis0 : 0 < pis := by linarith
  have hnum : 0 < 1 - β / pis := by rw [sub_pos, div_lt_one hpis0]; exact hpis
  have hden : 0 < 1 - β / pi := by rw [sub_pos, div_lt_one hpi0]; exact hpi
  have hlt : 1 - β / pi < 1 - β / pi' := by
    have : β / pi' < β / pi := div_lt_div_of_pos_left hβ hpi0 hpipi'
    linarith
  exact div_lt_div_of_pos_left hnum hden hlt

/-- **When does dollarization occur?** (O&R p. 552, the role of `a₀ > 1 − β`, made precise):
foreign currency is held at all sufficiently high home inflation rates iff
`a₀ > 1 − β/pi^*`; with constant foreign prices (`pi^* = 1`) this is the book's `a₀ > 1 − β`. -/
theorem dollar_eventually_iff {β pis a0 : ℝ} (hβ : 0 < β) (hpis : β < pis) (ha0 : 0 < a0) :
    (∃ pi0, ∀ pi, pi0 ≤ pi → substRatio β pi pis < a0) ↔ 1 - β / pis < a0 := by
  have hpis0 : 0 < pis := by linarith
  have hn : 0 < 1 - β / pis := by rw [sub_pos, div_lt_one hpis0]; exact hpis
  constructor
  · rintro ⟨pi0, h⟩
    set pi := max pi0 (β + 1) with hpidef
    have hpi : β < pi := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hpi0 : 0 < pi := by linarith
    have hden : 0 < 1 - β / pi := by rw [sub_pos, div_lt_one hpi0]; exact hpi
    have hden1 : 1 - β / pi < 1 := by have := div_pos hβ hpi0; linarith
    have h1 := h pi (le_max_left _ _)
    have h2 : 1 - β / pis < substRatio β pi pis := by
      rw [substRatio, lt_div_iff₀ hden]
      nlinarith
    linarith
  · intro h
    set n := 1 - β / pis with hndef
    set δ := 1 - n / a0 with hδ
    have hδ0 : 0 < δ := by
      rw [hδ, sub_pos, div_lt_one ha0]; exact h
    refine ⟨2 * β / δ, fun pi hpi => ?_⟩
    have hpi0 : 0 < pi := lt_of_lt_of_le (by positivity) hpi
    have hb : β / pi ≤ δ / 2 := by
      rw [div_le_iff₀ hpi0]
      rw [div_le_iff₀ hδ0] at hpi
      nlinarith
    have hden : n / a0 < 1 - β / pi := by
      have : n / a0 = 1 - δ := by rw [hδ]; ring
      linarith
    have hna : 0 < n / a0 := div_pos hn ha0
    rw [substRatio, ← hndef, div_lt_iff₀ (by linarith)]
    rw [div_lt_iff₀ ha0] at hden
    linarith

/-! ## Fixing the exchange rate with government spending (§8.4.1.2) -/

/-- **(69)**, O&R p. 557: with `u = log C + log(M/P)`, PPP and `P^* = 1` (so `P = ℰ`), the
money-demand condition `(1/m)/(1/C̄) = 1 − (ℰ_t/ℰ_{t+1})/(1+r)` holds iff
`M_t/ℰ_t = C̄(1+r)/(1 + r − ℰ_t/ℰ_{t+1})` (given a positive nominal rate). -/
theorem fiscal_fixing_iff {Cbar r E0 E1 m : ℝ} (hC : 0 < Cbar) (hm : 0 < m) (hr : 0 < 1 + r)
    (hpos : 0 < 1 + r - E0 / E1) :
    m⁻¹ / Cbar⁻¹ = 1 - E0 / E1 / (1 + r) ↔ m = Cbar * (1 + r) / (1 + r - E0 / E1) := by
  rw [inv_div_inv]
  constructor
  · intro h
    rw [eq_div_iff hpos.ne']
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp

/-- (69) with constant depreciation `ℰ_{t+1}/ℰ_t = 1 + μ`, O&R p. 557:
`M_t/ℰ_t = C̄(1+μ)(1+r)/((1+μ)(1+r) − 1)`. -/
theorem fiscal_fixing_constant {Cbar r μ E0 E1 : ℝ} (hE0 : 0 < E0) (hμ : 0 < 1 + μ)
    (hdep : E1 = (1 + μ) * E0) (hpos : 1 < (1 + μ) * (1 + r)) :
    Cbar * (1 + r) / (1 + r - E0 / E1) = Cbar * ((1 + μ) * (1 + r) / ((1 + μ) * (1 + r) - 1)) := by
  have h1 : (1 + μ) * (1 + r) - 1 ≠ 0 := by linarith
  have h2 : 1 + r - E0 / E1 = ((1 + μ) * (1 + r) - 1) / (1 + μ) := by
    rw [hdep]; field_simp
  rw [h2]
  field_simp

/-- O&R p. 557: real balances in the constant-depreciation equilibrium are positive iff
`(1+μ)(1+r) > 1`, i.e. iff the steady-state nominal interest rate is positive. -/
theorem fiscal_fixing_pos_iff {Cbar r μ : ℝ} (hC : 0 < Cbar) (hr : 0 < 1 + r) (hμ : 0 < 1 + μ) :
    0 < Cbar * ((1 + μ) * (1 + r) / ((1 + μ) * (1 + r) - 1)) ↔ 1 < (1 + μ) * (1 + r) := by
  have hp : 0 < (1 + μ) * (1 + r) := by positivity
  constructor
  · intro h
    have h2 : 0 < (1 + μ) * (1 + r) / ((1 + μ) * (1 + r) - 1) :=
      (pos_iff_pos_of_mul_pos h).1 hC
    rcases div_pos_iff.1 h2 with ⟨_, h4⟩ | ⟨h4, _⟩
    · linarith
    · linarith
  · intro h
    have : 0 < (1 + μ) * (1 + r) - 1 := by linarith
    positivity

/-- **A rise in government spending depreciates the currency**, O&R p. 557: with
`C̄ = Ȳ + rB − Ḡ` (from (44)) and a given money supply, `ℰ_t = M_t/(C̄K)` with
`K = (1+μ)(1+r)/((1+μ)(1+r) − 1) > 0` is strictly increasing in `Ḡ` (while `C̄ > 0`). -/
theorem exchange_rate_increasing_in_G {M K Y rB G G' : ℝ} (hM : 0 < M) (hK : 0 < K)
    (hGG' : G < G') (hC' : 0 < Y + rB - G') :
    M / ((Y + rB - G) * K) < M / ((Y + rB - G') * K) := by
  have hC : 0 < Y + rB - G := by linarith
  apply div_lt_div_of_pos_left hM (by positivity)
  exact mul_lt_mul_of_pos_right (by linarith) hK

/-! ## Money demand: comparative statics and the steady-state nominal rate -/

/-- O&R p. 535: CES money demand `M/P = ((1−γ)/γ) ι^{−θ} C` is strictly decreasing in the user
cost `ι = i/(1+i)` (hence in the nominal interest rate) and linear in consumption. -/
theorem ces_money_demand_strictAnti {γ θ c : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hc : 0 < c) : StrictAntiOn (fun ι : ℝ => (1 - γ) / γ * ι ^ (-θ) * c) (Set.Ioi 0) := by
  intro a ha b hb hab
  have h1γ : 0 < 1 - γ := by linarith
  have := rpow_lt_rpow_of_neg ha hab (neg_lt_zero.2 hθ)
  simp only
  have hA : 0 < (1 - γ) / γ := by positivity
  nlinarith [mul_lt_mul_of_pos_left this hA]

/-- The user cost `i/(1+i)` is strictly increasing in the nominal rate `i > −1` (O&R (37)). -/
theorem userCost_fisher_strictMono : StrictMonoOn (fun i : ℝ => i / (1 + i)) (Set.Ioi (-1)) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have ha' : 0 < 1 + a := by linarith
  have hb' : 0 < 1 + b := by linarith
  simp only
  rw [div_lt_div_iff₀ ha' hb']
  nlinarith

/-- **The steady-state nominal interest rate** (O&R fn 27, p. 539): with `(1+r)β = 1` and constant
inflation `P_{t+1}/P_t = 1 + μ`, the user cost is `1 − β/(1+μ)` and Fisher parity gives
`i = (1+μ)/β − 1`, which is positive iff `1 + μ > β`. -/
theorem steady_nominal_rate {r β μ : ℝ} {P : ℕ → ℝ} (hβ : 0 < β)
    (hβr : (1 + r) * β = 1) (hμ : 0 < 1 + μ) (hP : ∀ s, 0 < P s)
    (hinfl : ∀ s, P (s + 1) = (1 + μ) * P s) (s : ℕ) :
    userCost r P s = 1 - β / (1 + μ) ∧ (1 + r) * P (s + 1) / P s = 1 + ((1 + μ) / β - 1) ∧
      (0 < (1 + μ) / β - 1 ↔ β < 1 + μ) := by
  have hPs := (hP s).ne'
  have h1r : 1 + r = 1 / β := by field_simp; linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold userCost
    rw [hinfl s, h1r]
    field_simp
  · rw [hinfl s, h1r]
    field_simp
    ring
  · rw [sub_pos, one_lt_div hβ]

/-! ## CES-isoelastic preferences: concavity, sufficiency and existence (§8.3.3) -/

/-- Every interior bundle lies on the demand curve of some user cost `p > 0`, at which
`Ω(C, m) = (C + p m)/P^C(p)` (O&R p. 535; the CES index is the lower envelope of the linear
functions `(C + p m)/P^C(p)`). -/
theorem cesIndex_eq_cost_div_price {γ θ c k : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hc : 0 < c) (hk : 0 < k) :
    ∃ p, 0 < p ∧ cesIndex γ θ c k = (c + p * k) / cesPrice γ θ p := by
  have h1γ : 0 < 1 - γ := by linarith
  set p := (γ * k / ((1 - γ) * c)) ^ (-(1 / θ)) with hp
  have hp0 : 0 < p := by positivity
  have hpθ : p ^ (-θ) = γ * k / ((1 - γ) * c) := by
    rw [hp, ← rpow_mul (by positivity), show -(1 / θ) * -θ = 1 by field_simp, rpow_one]
  have hdem : k = (1 - γ) / γ * p ^ (-θ) * c := by rw [hpθ]; field_simp
  refine ⟨p, hp0, ?_⟩
  rw [cesIndex_on_demand hγ0 hγ1 hθ hθ1 hc hp0 hdem, expenditure_on_demand hγ0 hp0 hdem]

/-- **The CES index is concave** on the positive quadrant (O&R p. 535): it is the infimum of
the linear functions `(C + p m)/P^C(p)` (duality, `cesIndex_le_div_price`), attained at every
interior bundle (`cesIndex_eq_cost_div_price`). -/
theorem cesIndex_concaveOn {γ θ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ) (hθ1 : θ ≠ 1) :
    ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) (fun q : ℝ × ℝ => cesIndex γ θ q.1 q.2) := by
  have hK : Convex ℝ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := (convex_Ioi 0).prod (convex_Ioi 0)
  refine ⟨hK, fun x hx y hy a b ha hb hab => ?_⟩
  have hz := hK hx hy ha hb hab
  obtain ⟨p, hp0, hpz⟩ := cesIndex_eq_cost_div_price hγ0 hγ1 hθ hθ1 hz.1 hz.2
  have hP := cesPrice_pos (θ := θ) hγ0 hγ1 hp0
  have hx' := cesIndex_le_div_price hγ0 hγ1 hθ hθ1 hp0 (le_of_lt hx.1) (le_of_lt hx.2)
    (fun _ => ⟨hx.1, hx.2⟩) (add_pos hx.1 (mul_pos hp0 hx.2))
  have hy' := cesIndex_le_div_price hγ0 hγ1 hθ hθ1 hp0 (le_of_lt hy.1) (le_of_lt hy.2)
    (fun _ => ⟨hy.1, hy.2⟩) (add_pos hy.1 (mul_pos hp0 hy.2))
  simp only [smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd] at hpz ⊢
  rw [hpz]
  have e : (a * x.1 + b * y.1 + p * (a * x.2 + b * y.2)) / cesPrice γ θ p =
      a * ((x.1 + p * x.2) / cesPrice γ θ p) + b * ((y.1 + p * y.2) / cesPrice γ θ p) := by
    field_simp; ring
  rw [e]
  exact add_le_add (mul_le_mul_of_nonneg_left hx' ha) (mul_le_mul_of_nonneg_left hy' hb)

/-- The outer isoelastic function `z ↦ z^{1−1/σ}/(1 − 1/σ)` has derivative `z^{−1/σ}`
(O&R p. 535). -/
theorem isoelastic_hasDerivAt {σ z : ℝ} (hσ1 : σ ≠ 1) (hσ : 0 < σ) (hz : 0 < z) :
    HasDerivAt (fun z => z ^ (1 - 1 / σ) / (1 - 1 / σ)) (z ^ (-(1 / σ))) z := by
  have hσ' : 1 - 1 / σ ≠ 0 := by
    intro h; apply hσ1; field_simp at h; linarith
  have := (Real.hasDerivAt_rpow_const (x := z) (p := 1 - 1 / σ) (Or.inl hz.ne')).div_const
    (1 - 1 / σ)
  refine this.congr_deriv ?_
  rw [show 1 - 1 / σ - 1 = -(1 / σ) by ring]
  field_simp

/-- **CES-isoelastic utility is jointly concave** on the positive quadrant (O&R p. 535): it is a
concave nondecreasing function (`z^{1−1/σ}/(1−1/σ)`, derivative `z^{−1/σ}` positive and
decreasing) of the concave index `Ω`. -/
theorem cesUtility_concaveOn {γ θ σ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hσ : 0 < σ) (hσ1 : σ ≠ 1) :
    ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) (fun q : ℝ × ℝ => cesUtility γ θ σ q.1 q.2) := by
  set f : ℝ → ℝ := fun z => z ^ (1 - 1 / σ) / (1 - 1 / σ) with hf
  have hfd : ∀ z, 0 < z → HasDerivAt f (z ^ (-(1 / σ))) z := fun z hz =>
    isoelastic_hasDerivAt hσ1 hσ hz
  have hfc : ContinuousOn f (Set.Ioi 0) := fun z hz => (hfd z hz).continuousAt.continuousWithinAt
  have hfconc : ConcaveOn ℝ (Set.Ioi 0) f := by
    refine AntitoneOn.concaveOn_of_deriv (convex_Ioi 0) hfc
      (fun z hz => by
        rw [interior_Ioi] at hz; exact (hfd z hz).differentiableAt.differentiableWithinAt)
      (fun x hx y hy hxy => ?_)
    rw [interior_Ioi] at hx hy
    rw [(hfd x hx).deriv, (hfd y hy).deriv]
    exact rpow_le_rpow_of_nonpos hx hxy (by have := one_div_pos.2 hσ; linarith)
  have hfmono : MonotoneOn f (Set.Ioi 0) :=
    (strictMonoOn_of_deriv_pos (convex_Ioi 0) hfc (fun z hz => by
      rw [interior_Ioi] at hz; rw [(hfd z hz).deriv]; exact rpow_pos_of_pos hz _)).monotoneOn
  have hΩ := cesIndex_concaveOn hγ0 hγ1 hθ hθ1
  refine ⟨hΩ.1, fun x hx y hy a b ha hb hab => ?_⟩
  have hΩx := cesIndex_pos (θ := θ) hγ0 hγ1 hx.1 hx.2
  have hΩy := cesIndex_pos (θ := θ) hγ0 hγ1 hy.1 hy.2
  have hz := hΩ.1 hx hy ha hb hab
  have hΩz := cesIndex_pos (θ := θ) hγ0 hγ1 hz.1 hz.2
  have h1 := hΩ.2 hx hy ha hb hab
  have hcomb : 0 < a • cesIndex γ θ x.1 x.2 + b • cesIndex γ θ y.1 y.2 := by
    simp only [smul_eq_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_pos ha' hΩx, mul_nonneg hb hΩy.le]
    · subst ha'; simp only [zero_add] at hab; subst hab; simpa using hΩy
  have h2 := hfconc.2 (Set.mem_Ioi.2 hΩx) (Set.mem_Ioi.2 hΩy) ha hb hab
  have h3 := hfmono (Set.mem_Ioi.2 hcomb) (Set.mem_Ioi.2 hΩz) h1
  exact h2.trans h3

/-- **Exact characterisation of the CES-isoelastic optimum** (O&R §8.3.2–8.3.3): for
`σ, θ ≠ 1`, an admissible plan is optimal IFF it satisfies the Euler equation (35), the
money-demand condition (37) and the transversality condition. -/
theorem ces_isOptimal_iff {γ θ σ β r A0 : ℝ} {y ι C m : ℕ → ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hr : 0 < 1 + r) :
    IsOptimal (cesUtility γ θ σ) β r A0 y ι C m ↔ Admissible (cesUtility γ θ σ) β r A0 y ι C m ∧
      (∀ s, cesMargC γ θ σ (C s) (m s) = (1 + r) * β * cesMargC γ θ σ (C (s + 1)) (m (s + 1))) ∧
      (∀ s, cesMargM γ θ σ (C s) (m s) = ι s * cesMargC γ θ σ (C s) (m s)) ∧
      Transversality r (wealth r A0 y ι C m) :=
  isOptimal_iff hβ hr (cesUtility_concaveOn hγ0 hγ1 hθ hθ1 hσ hσ1)
    (fun _ _ hc hk => cesUtility_hasFDerivAt hγ0 hγ1 hθ hθ1 hσ hσ1 hc hk)
    (fun _ _ hc hk => (cesMarg_pos (θ := θ) (σ := σ) hγ0 hγ1 hc hk).1)

/-- **Marginal utility times expenditure equals `Ω^{1−1/σ}`** on the money-demand locus
(O&R p. 535): `u_C (C + ι M/P) = Ω^{1−1/σ} = (1 − 1/σ) u`, Euler's theorem for the
homogeneous utility combined with `u_{M/P} = ι u_C`. -/
theorem cesMargC_mul_expenditure {γ θ σ c k ι : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hσ : 0 < σ) (hc : 0 < c) (hι : 0 < ι)
    (hk : k = (1 - γ) / γ * ι ^ (-θ) * c) :
    cesMargC γ θ σ c k * (c + ι * k) = cesIndex γ θ c k ^ (1 - 1 / σ) := by
  have hP := cesPrice_pos (θ := θ) hγ0 hγ1 hι
  have hD : cesDenom γ θ ι = cesPrice γ θ ι ^ (1 - θ) :=
    (cesPrice_rpow_one_sub hγ0 hγ1 hι hθ1).symm
  rw [cesMargC_on_demand hγ0 hγ1 hθ hθ1 hσ hc hι hk, cesIndex_on_demand' hγ0 hγ1 hθ hθ1 hc hι hk,
    expenditure_on_demand hγ0 hι hk, hD]
  set P := cesPrice γ θ ι with hPdef
  rw [div_rpow (by positivity) hγ0.le, mul_rpow hc.le (by positivity), ← rpow_mul hP.le]
  have e1 : c ^ (1 - 1 / σ) = c * c ^ (-(1 / σ)) := by
    rw [sub_eq_add_neg, rpow_add hc, rpow_one]
  have e2 : γ ^ (1 - 1 / σ) = γ / γ ^ (1 / σ) := by rw [rpow_sub hγ0, rpow_one]
  have e3 : P ^ (-θ * (1 - 1 / σ)) = P ^ ((θ - σ) / σ) * P ^ (1 - θ) := by
    rw [← rpow_add hP]; congr 1; field_simp; ring
  have hg := rpow_pos_of_pos hγ0 (1 / σ)
  rw [e1, e2, e3]
  field_simp

/-- **Existence of the CES-isoelastic optimum** (O&R §8.3.3, p. 536, and Exercise 3): for
`σ, θ ≠ 1`, positive user costs `ι_s`, lifetime resources `W = A_0 + Σ(1+r)^{−s} y_s > 0` and a
summable weight series `S = Σ(1+r)^{−s}((β(1+r))^σ)^s (P^C_s/P^C_0)^{1−σ}`, the book's closed
form `C_s = γ (P^C_0)^{θ−1} (W/S) ((β(1+r))^σ)^s (P^C_s/P^C_0)^{θ−σ}` with real balances on the
money-demand curve `M_s/P_s = ((1−γ)/γ) ι_s^{−θ} C_s` IS optimal: it is admissible, satisfies
(35), (37) and exhausts wealth, so `ces_isOptimal_iff` applies. -/
theorem ces_isOptimal_of_closedForm {γ θ σ β r A0 W : ℝ} {y ι C m : ℕ → ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β)
    (hr : 0 < 1 + r) (hι : ∀ s, 0 < ι s) (hy : HasSum (fun s => (1 + r)⁻¹ ^ s * y s) (W - A0))
    (hW : 0 < W) (hS : Summable (pvWeight σ (1 - σ) β r (fun s => cesPrice γ θ (ι s))))
    (hC : ∀ s, C s = γ * cesPrice γ θ (ι 0) ^ (θ - 1) * W /
      (∑' t, pvWeight σ (1 - σ) β r (fun s => cesPrice γ θ (ι s)) t) *
      (((β * (1 + r)) ^ σ) ^ s * (cesPrice γ θ (ι s) / cesPrice γ θ (ι 0)) ^ (θ - σ)))
    (hm : ∀ s, m s = (1 - γ) / γ * ι s ^ (-θ) * C s) :
    IsOptimal (cesUtility γ θ σ) β r A0 y ι C m := by
  have hP : ∀ s, 0 < cesPrice γ θ (ι s) := fun s => cesPrice_pos hγ0 hγ1 (hι s)
  have hx : 0 < β * (1 + r) := mul_pos hβ hr
  have hpw : ∀ s, 0 < pvWeight σ (1 - σ) β r (fun s => cesPrice γ θ (ι s)) s := fun s => by
    unfold pvWeight; have := hP s; have := hP 0; positivity
  have hS0 : 0 < ∑' t, pvWeight σ (1 - σ) β r (fun s => cesPrice γ θ (ι s)) t :=
    hS.tsum_pos (fun s => (hpw s).le) 0 (hpw 0)
  set S := ∑' t, pvWeight σ (1 - σ) β r (fun s => cesPrice γ θ (ι s)) t with hSdef
  set C0 := γ * cesPrice γ θ (ι 0) ^ (θ - 1) * W / S with hC0
  have hC0p : 0 < C0 := by have := hP 0; positivity
  have hCpos : ∀ s, 0 < C s := fun s => by rw [hC s]; have := hP s; have := hP 0; positivity
  have hmpos : ∀ s, 0 < m s := fun s => by
    rw [hm s]; have := hι s; have := hCpos s; have : 0 < 1 - γ := (by linarith); positivity
  -- discounted expenditure is proportional to the weights
  have hZ : ∀ s, (1 + r)⁻¹ ^ s * (C s + ι s * m s) = C0 * cesPrice γ θ (ι 0) ^ (1 - θ) / γ *
      pvWeight σ (1 - σ) β r (fun s => cesPrice γ θ (ι s)) s := fun s => by
    rw [expenditure_on_demand hγ0 (hι s) (hm s),
      show cesDenom γ θ (ι s) = cesPrice γ θ (ι s) ^ (1 - θ) from
        (cesPrice_rpow_one_sub hγ0 hγ1 (hι s) hθ1).symm, hC s, pvWeight]
    have hPs := hP s
    have hP0 := hP 0
    set Ps := cesPrice γ θ (ι s)
    set P0 := cesPrice γ θ (ι 0)
    have e : (Ps / P0) ^ (1 - σ) = (Ps / P0) ^ (θ - σ) * (Ps ^ (1 - θ) / P0 ^ (1 - θ)) := by
      rw [← div_rpow hPs.le hP0.le, ← rpow_add (div_pos hPs hP0)]; congr 1; ring
    rw [e]
    have := rpow_pos_of_pos hP0 (1 - θ)
    field_simp
  have hexp : HasSum (fun s => (1 + r)⁻¹ ^ s * (C s + ι s * m s))
      (A0 + ∑' s, (1 + r)⁻¹ ^ s * y s) := by
    rw [hy.tsum_eq, show A0 + (W - A0) = C0 * cesPrice γ θ (ι 0) ^ (1 - θ) / γ * S by
      rw [hC0]
      have h1 : cesPrice γ θ (ι 0) ^ (θ - 1) * cesPrice γ θ (ι 0) ^ (1 - θ) = 1 := by
        rw [← rpow_add (hP 0)]; simp
      field_simp
      linear_combination -W * h1]
    simp only [hZ]
    exact hS.hasSum.mul_left _
  have hlim := tendsto_wealth_of_budget hr hy.summable hexp
  -- marginal utility along the path decays like (β(1+r))^{-s}
  set G := γ ^ (1 / σ) * C0 ^ (-(1 / σ)) * cesPrice γ θ (ι 0) ^ ((θ - σ) / σ) with hG
  have hmarg : ∀ s, cesMargC γ θ σ (C s) (m s) * (β * (1 + r)) ^ s = G := fun s => by
    rw [cesMargC_on_demand hγ0 hγ1 hθ hθ1 hσ (hCpos s) (hι s) (hm s), hC s]
    have hPs := hP s
    have hP0 := hP 0
    set Ps := cesPrice γ θ (ι s)
    set P0 := cesPrice γ θ (ι 0)
    set x := β * (1 + r)
    have k1 : (((x ^ σ) ^ s) : ℝ) ^ (-(1 / σ)) = (x ^ s)⁻¹ := by
      rw [← rpow_mul_natCast hx.le, ← rpow_mul hx.le,
        show σ * (s : ℝ) * -(1 / σ) = -(s : ℝ) by field_simp, rpow_neg hx.le, rpow_natCast]
    have k2 : ((Ps / P0) ^ (θ - σ)) ^ (-(1 / σ)) = P0 ^ ((θ - σ) / σ) / Ps ^ ((θ - σ) / σ) := by
      rw [← rpow_mul (div_pos hPs hP0).le, show (θ - σ) * -(1 / σ) = -((θ - σ) / σ) by ring,
        rpow_neg (div_pos hPs hP0).le, div_rpow hPs.le hP0.le, inv_div]
    rw [mul_rpow hC0p.le (by positivity), mul_rpow (by positivity) (by positivity), k1, k2]
    have := rpow_pos_of_pos hPs ((θ - σ) / σ)
    have := pow_pos hx s
    field_simp
    rw [hG]
  refine (ces_isOptimal_iff hγ0 hγ1 hθ hθ1 hσ hσ1 hβ hr).2
    ⟨⟨hCpos, hmpos, ?_, noPonzi_of_tendsto hlim⟩, fun s => ?_,
      fun s => (ces_money_demand_iff hγ0 hγ1 hθ (hCpos s) (hmpos s) (hι s)).2 (hm s),
      transversality_of_tendsto hlim⟩
  · refine (hS.mul_left (G / (1 - 1 / σ) * (C0 * cesPrice γ θ (ι 0) ^ (1 - θ) / γ))).congr
      (fun s => ?_)
    have hu : cesUtility γ θ σ (C s) (m s) =
        cesMargC γ θ σ (C s) (m s) * (C s + ι s * m s) / (1 - 1 / σ) := by
      rw [cesMargC_mul_expenditure hγ0 hγ1 hθ hθ1 hσ (hCpos s) (hι s) (hm s), cesUtility]
    have hb : β ^ s = (1 + r)⁻¹ ^ s * (β * (1 + r)) ^ s := by
      rw [← mul_pow]; congr 1; field_simp
    rw [hu, hb, mul_assoc, ← hZ s, ← hmarg s]
    ring
  · have h1 := hmarg s
    have h2 := hmarg (s + 1)
    have hxs := pow_pos hx s
    rw [pow_succ] at h2
    have : cesMargC γ θ σ (C s) (m s) * (β * (1 + r)) ^ s =
        ((1 + r) * β * cesMargC γ θ σ (C (s + 1)) (m (s + 1))) * (β * (1 + r)) ^ s := by
      rw [h1, ← h2]; ring
    exact mul_right_cancel₀ hxs.ne' this

/-! ## Dollarization from primitives (§8.3.8) -/

/-- **The two-money budget constraint (63) in wealth form**, O&R p. 551. `N s` and `F s` are the
home and foreign nominal balances brought into date `s`, `P` and `Pstar` the home and foreign
price levels. With `A_s = (1+r)B_s + N_s/P_s + F_s/P^*_s`, real balances `m_s = N_{s+1}/P_s`,
`x_s = F_{s+1}/P^*_s` and user costs `ι = userCost r P`, `ι^* = userCost r Pstar`, (63) is
`A_{s+1} = (1+r)(A_s + y_s − (C_s + ι^*_s x_s) − ι_s m_s)`, i.e. `wealth` with expenditure
`C + ι^* x`. -/
theorem dollar_wealth_of_budget {r : ℝ} (hr : 0 < 1 + r) {P Pstar B N F Y T C : ℕ → ℝ}
    (hP : ∀ s, 0 < P s) (hPs : ∀ s, 0 < Pstar s)
    (hbud : ∀ s, B (s + 1) + N (s + 1) / P s + F (s + 1) / Pstar s =
      (1 + r) * B s + N s / P s + F s / Pstar s + Y s - C s - T s) (s : ℕ) :
    (1 + r) * B s + N s / P s + F s / Pstar s =
      wealth r ((1 + r) * B 0 + N 0 / P 0 + F 0 / Pstar 0) (fun s => Y s - T s) (userCost r P)
        (fun s => C s + userCost r Pstar s * (F (s + 1) / Pstar s))
        (fun s => N (s + 1) / P s) s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [wealth_succ, ← ih]
    have h := hbud s
    have h0 := (hP s).ne'
    have h1 := (hP (s + 1)).ne'
    have h2 := (hPs s).ne'
    have h3 := (hPs (s + 1)).ne'
    have hr' := hr.ne'
    have e1 : (1 + r) * (userCost r Pstar s * (F (s + 1) / Pstar s)) =
        (1 + r) * (F (s + 1) / Pstar s) - F (s + 1) / Pstar (s + 1) := by
      unfold userCost; field_simp
    have e2 : (1 + r) * (userCost r P s * (N (s + 1) / P s)) =
        (1 + r) * (N (s + 1) / P s) - N (s + 1) / P (s + 1) := by
      unfold userCost; field_simp
    linear_combination (1 + r) * h + e1 + e2

/-- The two-money household's lifetime utility `Σ β^s [u(C_s) + v(M_s/P_s + g(M^F_s/P^*_s))]`,
O&R (61)–(62), p. 551, with `g` the quadratic technology (62). -/
noncomputable def dollarUtility (u v : ℝ → ℝ) (a0 a1 β : ℝ) (C m x : ℕ → ℝ) : ℝ :=
  ∑' s, β ^ s * (u (C s) + v (m s + gDollar a0 a1 (x s)))

/-- An admissible two-money plan (O&R §8.3.8, p. 551): positive consumption, NONNEGATIVE foreign
balances `x_s ≥ 0` (the constraint behind the corner of (67)), positive liquidity
`m_s + g(x_s)`, summable utility and no Ponzi scheme on the budget (63). Home balances are not
sign-restricted separately (only total liquidity enters `v`). -/
def DollarAdmissible (u v : ℝ → ℝ) (a0 a1 β r A0 : ℝ) (y ι ιs C m x : ℕ → ℝ) : Prop :=
  (∀ s, 0 < C s) ∧ (∀ s, 0 ≤ x s) ∧ (∀ s, 0 < m s + gDollar a0 a1 (x s)) ∧
    Summable (fun s => β ^ s * (u (C s) + v (m s + gDollar a0 a1 (x s)))) ∧
    NoPonzi r (wealth r A0 y ι (fun s => C s + ιs s * x s) m)

/-- An optimal two-money plan: admissible and at least as good as every admissible plan
(O&R §8.3.8, p. 551). -/
def DollarOptimal (u v : ℝ → ℝ) (a0 a1 β r A0 : ℝ) (y ι ιs C m x : ℕ → ℝ) : Prop :=
  DollarAdmissible u v a0 a1 β r A0 y ι ιs C m x ∧ ∀ C' m' x',
    DollarAdmissible u v a0 a1 β r A0 y ι ιs C' m' x' →
      dollarUtility u v a0 a1 β C' m' x' ≤ dollarUtility u v a0 a1 β C m x

/-- Holding foreign money fixed, the two-money budget is the one-money budget (34) for total
liquidity `L = m + g(x)` with income `y + ι g(x) − ι^* x` (O&R (63), p. 551). -/
theorem dollar_wealth_shift (r A0 a0 a1 : ℝ) (y ι ιs C m x : ℕ → ℝ) (T : ℕ) :
    wealth r A0 y ι (fun s => C s + ιs s * x s) m T =
      wealth r A0 (fun s => y s + ι s * gDollar a0 a1 (x s) - ιs s * x s) ι C
        (fun s => m s + gDollar a0 a1 (x s)) T := by
  induction T with
  | zero => rfl
  | succ T ih => rw [wealth_succ, wealth_succ, ih]; ring

/-- **Reduction to the one-money problem** (O&R §8.3.8): at an optimal two-money plan,
`(C, m + g(x))` is optimal in the money-in-utility problem (33)–(34) with separable utility
`u(C) + v(L)` and income `y + ι g(x) − ι^* x`. -/
theorem dollar_reduce {u v : ℝ → ℝ} {a0 a1 β r A0 : ℝ} {y ι ιs C m x : ℕ → ℝ}
    (hopt : DollarOptimal u v a0 a1 β r A0 y ι ιs C m x) :
    IsOptimal (fun c k => u c + v k) β r A0
      (fun s => y s + ι s * gDollar a0 a1 (x s) - ιs s * x s) ι C
      (fun s => m s + gDollar a0 a1 (x s)) := by
  obtain ⟨⟨hC, hx, hL, hsum, hnp⟩, hmax⟩ := hopt
  refine ⟨⟨hC, hL, hsum, ?_⟩, fun C' k' hadm' => ?_⟩
  · rw [← funext (dollar_wealth_shift r A0 a0 a1 y ι ιs C m x)]
    exact hnp
  · obtain ⟨hC', hk', hsum', hnp'⟩ := hadm'
    have hadm : DollarAdmissible u v a0 a1 β r A0 y ι ιs C'
        (fun s => k' s - gDollar a0 a1 (x s)) x := by
      refine ⟨hC', hx, fun s => by simpa using hk' s, by simpa using hsum', ?_⟩
      rw [funext (dollar_wealth_shift r A0 a0 a1 y ι ιs C'
        (fun s => k' s - gDollar a0 a1 (x s)) x)]
      simpa using hnp'
    have := hmax _ _ _ hadm
    simpa [dollarUtility, lifetimeUtility] using this

/-- **The consumption Euler equation (64)**, derived from two-money optimality (O&R p. 552):
`u'(C_s) = (1+r)β u'(C_{s+1})`. -/
theorem dollar_euler_of_optimal {u v u' v' : ℝ → ℝ} {a0 a1 β r A0 : ℝ} {y ι ιs C m x : ℕ → ℝ}
    (hβ : 0 < β) (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hv : ∀ L, 0 < L → HasDerivAt v (v' L) L)
    (hopt : DollarOptimal u v a0 a1 β r A0 y ι ιs C m x) (s : ℕ) :
    u' (C s) = (1 + r) * β * u' (C (s + 1)) :=
  euler_of_optimal (uC := fun c _ => u' c) (um := fun _ k => v' k) hβ
    (fun c k hc hk => separable_hasFDerivAt (hu c hc) (hv k hk)) (dollar_reduce hopt) s

/-- **The home-money condition behind (65)**, derived from two-money optimality (O&R p. 552):
`v'(m_s + g(x_s)) = ι_s u'(C_s)`. -/
theorem dollar_money_foc_of_optimal {u v u' v' : ℝ → ℝ} {a0 a1 β r A0 : ℝ}
    {y ι ιs C m x : ℕ → ℝ} (hβ : 0 < β) (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hv : ∀ L, 0 < L → HasDerivAt v (v' L) L)
    (hopt : DollarOptimal u v a0 a1 β r A0 y ι ιs C m x) (s : ℕ) :
    v' (m s + gDollar a0 a1 (x s)) = ι s * u' (C s) :=
  money_foc_of_optimal (uC := fun c _ => u' c) (um := fun _ k => v' k) hβ
    (fun c k hc hk => separable_hasFDerivAt (hu c hc) (hv k hk)) (dollar_reduce hopt) s

/-- **Necessity of the transversality condition** for the two-money household (O&R p. 551):
if `u' > 0`, an optimal plan exhausts wealth, `liminf (1+r)^{−T} A_T ≤ 0`. -/
theorem dollar_tvc_of_optimal {u v u' v' : ℝ → ℝ} {a0 a1 β r A0 : ℝ} {y ι ιs C m x : ℕ → ℝ}
    (hr : 0 < 1 + r) (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hv : ∀ L, 0 < L → HasDerivAt v (v' L) L) (hupos : ∀ c, 0 < c → 0 < u' c)
    (hopt : DollarOptimal u v a0 a1 β r A0 y ι ιs C m x) :
    Transversality r (wealth r A0 y ι (fun s => C s + ιs s * x s) m) := by
  rw [funext (dollar_wealth_shift r A0 a0 a1 y ι ιs C m x)]
  exact transversality_of_optimal hr (fun k hk => strictMonoOn_of_uC_pos
    (u := fun c k => u c + v k) (uC := fun c _ => u' c) (um := fun _ k => v' k)
    (fun c k hc hk => separable_hasFDerivAt (hu c hc) (hv k hk))
    (fun c _ hc _ => hupos c hc) hk) (dollar_reduce hopt)

/-- **The foreign-money Kuhn–Tucker condition behind (66)**, derived from two-money optimality
(O&R p. 552): `v'(L_s) g'(x_s) ≤ ι^*_s u'(C_s)`, with equality when `x_s > 0`. Proof: buy `ε`
more foreign balances and consume `ι^*_s ε` less (`ε ≥ 0`, or `ε` of either sign at an interior
point); the wealth path is unchanged, so the one-sided derivative of utility is `≤ 0`. -/
theorem dollar_foreign_kkt_of_optimal {u v u' v' : ℝ → ℝ} {a0 a1 β r A0 : ℝ}
    {y ι ιs C m x : ℕ → ℝ} (hβ : 0 < β) (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hv : ∀ L, 0 < L → HasDerivAt v (v' L) L)
    (hopt : DollarOptimal u v a0 a1 β r A0 y ι ιs C m x) (s : ℕ) :
    v' (m s + gDollar a0 a1 (x s)) * (a0 - a1 * x s) ≤ ιs s * u' (C s) ∧
      (0 < x s → v' (m s + gDollar a0 a1 (x s)) * (a0 - a1 * x s) = ιs s * u' (C s)) := by
  obtain ⟨⟨hC, hx, hL, hsum, hnp⟩, hmax⟩ := hopt
  let DC : ℝ → ℕ → ℝ := fun ε t => if t = s then C s - ιs s * ε else C t
  let Dx : ℝ → ℕ → ℝ := fun ε t => if t = s then x s + ε else x t
  have hDC : ∀ ε, DC ε s = C s - ιs s * ε := fun ε => by simp [DC]
  have hDx : ∀ ε, Dx ε s = x s + ε := fun ε => by simp [Dx]
  have hoffC : ∀ ε t, t ∉ ({s} : Finset ℕ) → DC ε t = C t := fun ε t ht => by
    simp only [Finset.mem_singleton] at ht; simp [DC, ht]
  have hoffx : ∀ ε t, t ∉ ({s} : Finset ℕ) → Dx ε t = x t := fun ε t ht => by
    simp only [Finset.mem_singleton] at ht; simp [Dx, ht]
  have hw : ∀ ε T, wealth r A0 y ι (fun t => DC ε t + ιs t * Dx ε t) m T =
      wealth r A0 y ι (fun t => C t + ιs t * x t) m T := fun ε T => by
    refine wealth_congr_expenditure (fun t => ?_) T
    by_cases ht : t = s
    · subst ht; rw [hDC, hDx]; ring
    · rw [hoffC ε t (by simpa using ht), hoffx ε t (by simpa using ht)]
  set φ : ℝ → ℝ := fun ε => β ^ s * (u (C s - ιs s * ε) + v (m s + gDollar a0 a1 (x s + ε)))
    with hφ
  have hcmp : ∀ ε, 0 < C s - ιs s * ε → 0 ≤ x s + ε → 0 < m s + gDollar a0 a1 (x s + ε) →
      φ ε ≤ φ 0 := by
    intro ε h1 h2 h3
    obtain ⟨hs', heq⟩ := tsum_eq_add_of_eqOn_compl hsum {s}
      (g := fun t => β ^ t * (u (DC ε t) + v (m t + gDollar a0 a1 (Dx ε t))))
      (fun t ht => by rw [hoffC ε t ht, hoffx ε t ht])
    have hadm : DollarAdmissible u v a0 a1 β r A0 y ι ιs (DC ε) m (Dx ε) := by
      refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, hs', ?_⟩
      · by_cases ht : t = s
        · subst ht; rw [hDC]; exact h1
        · rw [hoffC ε t (by simpa using ht)]; exact hC t
      · by_cases ht : t = s
        · subst ht; rw [hDx]; exact h2
        · rw [hoffx ε t (by simpa using ht)]; exact hx t
      · by_cases ht : t = s
        · subst ht; rw [hDx]; exact h3
        · rw [hoffx ε t (by simpa using ht)]; exact hL t
      · exact noPonzi_congr hnp (Filter.Eventually.of_forall (fun T => hw ε T))
    have := hmax _ _ _ hadm
    unfold dollarUtility at this
    rw [heq, Finset.sum_singleton, hDC, hDx] at this
    simp only [φ, mul_zero, sub_zero, add_zero]
    linarith
  -- the derivative of the perturbation
  have g1 : HasDerivAt (fun ε : ℝ => m s + gDollar a0 a1 (x s + ε)) (a0 - a1 * x s) 0 := by
    have := (gDollar_hasDerivAt a0 a1 (x s + 0)).comp (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).const_add (x s))
    simp only [add_zero, mul_one] at this
    exact this.const_add (m s)
  have hA : HasDerivAt (fun ε : ℝ => u (C s - ιs s * ε)) (u' (C s) * (-ιs s)) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => C s - ιs s * ε) (-ιs s) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (ιs s)).const_sub (C s)
    have h2 : HasDerivAt u (u' (C s)) ((fun ε : ℝ => C s - ιs s * ε) 0) := by
      simpa using hu _ (hC s)
    exact h2.comp (0 : ℝ) h1
  have hB : HasDerivAt (fun ε : ℝ => v (m s + gDollar a0 a1 (x s + ε)))
      (v' (m s + gDollar a0 a1 (x s)) * (a0 - a1 * x s)) 0 := by
    have h2 : HasDerivAt v (v' (m s + gDollar a0 a1 (x s)))
        ((fun ε : ℝ => m s + gDollar a0 a1 (x s + ε)) 0) := by
      simpa using hv _ (hL s)
    exact h2.comp (0 : ℝ) g1
  have hd := (hA.add hB).const_mul (β ^ s)
  have hβs : 0 < β ^ s := pow_pos hβ s
  have hev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C s - ιs s * ε :=
    ((by fun_prop : Continuous fun ε : ℝ => C s - ιs s * ε).tendsto 0).eventually
      (lt_mem_nhds (by simpa using hC s))
  have hev3 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < m s + gDollar a0 a1 (x s + ε) :=
    g1.continuousAt.tendsto.eventually (lt_mem_nhds (by simpa using hL s))
  refine ⟨?_, fun hxs => ?_⟩
  · have hslope : Tendsto (slope φ 0) (𝓝[>] 0)
        (𝓝 (β ^ s * (u' (C s) * (-ιs s) + v' (m s + gDollar a0 a1 (x s)) * (a0 - a1 * x s)))) :=
      (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
        (nhdsWithin_mono _ (fun τ (hτ : 0 < τ) => ne_of_gt hτ))
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), slope φ 0 ε ≤ 0 := by
      filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev3, self_mem_nhdsWithin]
        with ε h1 h3 (h2 : 0 < ε)
      have := hcmp ε h1 (by linarith [hx s]) h3
      rw [slope_def_field, sub_zero]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) h2.le
    have hle := le_of_tendsto hslope hev
    by_contra hcon
    push Not at hcon
    have := mul_pos hβs (show 0 < u' (C s) * (-ιs s) +
      v' (m s + gDollar a0 a1 (x s)) * (a0 - a1 * x s) by linarith)
    linarith
  · have hev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < x s + ε :=
      ((by fun_prop : Continuous fun ε : ℝ => x s + ε).tendsto 0).eventually
        (lt_mem_nhds (by simpa using hxs))
    have hloc : IsLocalMax φ 0 := by
      filter_upwards [hev1, hev2, hev3] with ε h1 h2 h3
      exact hcmp ε h1 h2.le h3
    have h0 := hloc.hasDerivAt_eq_zero hd
    have := (mul_eq_zero.1 h0).resolve_left hβs.ne'
    linarith

/-- **Sufficiency for the two-money household** (O&R (64)–(66) with the TVC, made precise):
with `u`, `v` concave and differentiable, `v' ≥ 0`, `a₁ ≥ 0`, an admissible plan satisfying the
Euler equation (64), the home-money condition `v'(L) = ι u'(C)`, the foreign-money Kuhn–Tucker
condition and the transversality condition is optimal. Proof: tangent inequalities for
`u(C) + v(L)`, the exact bound `g(x') − g(x) ≤ g'(x)(x' − x)`, the Kuhn–Tucker sign argument
`(x' − x ≥ 0` when `x = 0)`, then the telescoping argument of `isOptimal_of_foc`. -/
theorem dollar_isOptimal_of_foc {u v u' v' : ℝ → ℝ} {a0 a1 β r A0 : ℝ} {y ι ιs C m x : ℕ → ℝ}
    (hβ : 0 < β) (hr : 0 < 1 + r) (ha1 : 0 ≤ a1)
    (hcu : ConcaveOn ℝ (Set.Ioi 0) u) (hcv : ConcaveOn ℝ (Set.Ioi 0) v)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hv : ∀ L, 0 < L → HasDerivAt v (v' L) L)
    (hv0 : ∀ L, 0 < L → 0 ≤ v' L)
    (hadm : DollarAdmissible u v a0 a1 β r A0 y ι ιs C m x) (hpos : 0 ≤ u' (C 0))
    (heuler : ∀ s, u' (C s) = (1 + r) * β * u' (C (s + 1)))
    (hmoney : ∀ s, v' (m s + gDollar a0 a1 (x s)) = ι s * u' (C s))
    (hkkt : ∀ s, v' (m s + gDollar a0 a1 (x s)) * (a0 - a1 * x s) ≤ ιs s * u' (C s) ∧
      (0 < x s → v' (m s + gDollar a0 a1 (x s)) * (a0 - a1 * x s) = ιs s * u' (C s)))
    (htvc : Transversality r (wealth r A0 y ι (fun s => C s + ιs s * x s) m)) :
    DollarOptimal u v a0 a1 β r A0 y ι ιs C m x := by
  refine ⟨hadm, fun C' m' x' hadm' => ?_⟩
  obtain ⟨hC, hx, hL, hsum, -⟩ := hadm
  obtain ⟨hC', hx', hL', hsum', hnp'⟩ := hadm'
  set lam0 := u' (C 0) with hlam0
  set d := (1 + r)⁻¹ with hd
  have hdisc : ∀ s, β ^ s * u' (C s) = lam0 * d ^ s :=
    discounted_marginal_utility hr (lam := fun s => u' (C s)) heuler
  have hterm : ∀ s, β ^ s * (u (C' s) + v (m' s + gDollar a0 a1 (x' s))) -
      β ^ s * (u (C s) + v (m s + gDollar a0 a1 (x s))) ≤
      lam0 * (d ^ s * ((C' s + ιs s * x' s) + ι s * m' s) -
        d ^ s * ((C s + ιs s * x s) + ι s * m s)) := by
    intro s
    have t := concave_le_tangent (separable_concaveOn hcu hcv)
      (x := (C s, m s + gDollar a0 a1 (x s))) (y := (C' s, m' s + gDollar a0 a1 (x' s)))
      ⟨hC s, hL s⟩ ⟨hC' s, hL' s⟩ (separable_hasFDerivAt (hu _ (hC s)) (hv _ (hL s)))
    simp only [grad_apply, Prod.fst_sub, Prod.snd_sub] at t
    have hg : gDollar a0 a1 (x' s) - gDollar a0 a1 (x s) ≤ (a0 - a1 * x s) * (x' s - x s) := by
      unfold gDollar; nlinarith [sq_nonneg (x' s - x s)]
    have hk : v' (m s + gDollar a0 a1 (x s)) * (a0 - a1 * x s) * (x' s - x s) ≤
        ιs s * u' (C s) * (x' s - x s) := by
      rcases (hx s).lt_or_eq with hp | hz
      · rw [(hkkt s).2 hp]
      · have hx0 : x' s - x s = x' s := by rw [← hz, sub_zero]
        rw [hx0]; exact mul_le_mul_of_nonneg_right (hkkt s).1 (hx' s)
    have hvg := mul_le_mul_of_nonneg_left hg (hv0 _ (hL s))
    have e : v' (m s + gDollar a0 a1 (x s)) * (m' s - m s) = ι s * u' (C s) * (m' s - m s) := by
      rw [hmoney s]
    have hb := pow_pos hβ s
    have h2 := mul_le_mul_of_nonneg_left (show u (C' s) + v (m' s + gDollar a0 a1 (x' s)) -
      (u (C s) + v (m s + gDollar a0 a1 (x s))) ≤ u' (C s) * ((C' s - C s) +
        ι s * (m' s - m s) + ιs s * (x' s - x s)) by nlinarith) hb.le
    have key : β ^ s * (u' (C s) * ((C' s - C s) + ι s * (m' s - m s) + ιs s * (x' s - x s))) =
        lam0 * (d ^ s * ((C' s + ιs s * x' s) + ι s * m' s) -
          d ^ s * ((C s + ιs s * x s) + ι s * m s)) := by
      linear_combination ((C' s - C s) + ι s * (m' s - m s) + ιs s * (x' s - x s)) * hdisc s
    linarith
  have hpartial : ∀ T, ∑ s ∈ Finset.range T, (β ^ s * (u (C' s) + v (m' s + gDollar a0 a1 (x' s)))
      - β ^ s * (u (C s) + v (m s + gDollar a0 a1 (x s)))) ≤
      lam0 * (d ^ T * wealth r A0 y ι (fun s => C s + ιs s * x s) m T -
        d ^ T * wealth r A0 y ι (fun s => C' s + ιs s * x' s) m' T) := by
    intro T
    have h1 := wealth_pv_identity hr A0 y ι (fun s => C s + ιs s * x s) m T
    have h2 := wealth_pv_identity hr A0 y ι (fun s => C' s + ιs s * x' s) m' T
    beta_reduce at h1 h2
    have hle := Finset.sum_le_sum fun s (_ : s ∈ Finset.range T) => hterm s
    have heq : ∑ i ∈ Finset.range T, d ^ i * ((C' i + ιs i * x' i) + ι i * m' i) -
        ∑ i ∈ Finset.range T, d ^ i * ((C i + ιs i * x i) + ι i * m i) =
        d ^ T * wealth r A0 y ι (fun s => C s + ιs s * x s) m T -
          d ^ T * wealth r A0 y ι (fun s => C' s + ιs s * x' s) m' T := by linarith
    have hR : ∑ i ∈ Finset.range T, lam0 * (d ^ i * ((C' i + ιs i * x' i) + ι i * m' i) -
        d ^ i * ((C i + ιs i * x i) + ι i * m i)) =
        lam0 * (d ^ T * wealth r A0 y ι (fun s => C s + ιs s * x s) m T -
          d ^ T * wealth r A0 y ι (fun s => C' s + ιs s * x' s) m' T) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, heq]
    exact hle.trans hR.le
  have hlim : Tendsto (fun T => ∑ s ∈ Finset.range T,
      (β ^ s * (u (C' s) + v (m' s + gDollar a0 a1 (x' s))) -
        β ^ s * (u (C s) + v (m s + gDollar a0 a1 (x s))))) atTop
      (𝓝 (dollarUtility u v a0 a1 β C' m' x' - dollarUtility u v a0 a1 β C m x)) :=
    (hsum'.hasSum.sub hsum.hasSum).tendsto_sum_nat
  by_contra hlt
  push Not at hlt
  set δ := dollarUtility u v a0 a1 β C' m' x' - dollarUtility u v a0 a1 β C m x with hδdef
  have hδ : 0 < δ := by linarith
  have hl1 : 0 < lam0 + 1 := by linarith
  set ε := δ / (4 * (lam0 + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hsmall : 2 * lam0 * ε < δ := by
    have h4 : ε * (4 * (lam0 + 1)) = δ := by rw [hεdef]; field_simp
    nlinarith
  obtain ⟨T, hT3, hT1, hT2⟩ :=
    ((htvc ε hε).and_eventually ((hlim.eventually (lt_mem_nhds hsmall)).and (hnp' ε hε))).exists
  have hP := hpartial T
  have hab : d ^ T * wealth r A0 y ι (fun s => C s + ιs s * x s) m T -
      d ^ T * wealth r A0 y ι (fun s => C' s + ιs s * x' s) m' T ≤ 2 * ε := by
    linarith
  have := mul_le_mul_of_nonneg_left hab hpos
  linarith

/-- **Exact characterisation of the two-money optimum** (O&R §8.3.8, (64)–(66)): with `u, v`
concave and differentiable, `u' > 0`, `v' ≥ 0` and `a₁ ≥ 0`, a plan is optimal IFF it is
admissible and satisfies (64), the home-money condition, the foreign-money Kuhn–Tucker
condition and the transversality condition. -/
theorem dollar_optimal_iff {u v u' v' : ℝ → ℝ} {a0 a1 β r A0 : ℝ} {y ι ιs C m x : ℕ → ℝ}
    (hβ : 0 < β) (hr : 0 < 1 + r) (ha1 : 0 ≤ a1)
    (hcu : ConcaveOn ℝ (Set.Ioi 0) u) (hcv : ConcaveOn ℝ (Set.Ioi 0) v)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hv : ∀ L, 0 < L → HasDerivAt v (v' L) L)
    (hupos : ∀ c, 0 < c → 0 < u' c) (hv0 : ∀ L, 0 < L → 0 ≤ v' L) :
    DollarOptimal u v a0 a1 β r A0 y ι ιs C m x ↔
      DollarAdmissible u v a0 a1 β r A0 y ι ιs C m x ∧
      (∀ s, u' (C s) = (1 + r) * β * u' (C (s + 1))) ∧
      (∀ s, v' (m s + gDollar a0 a1 (x s)) = ι s * u' (C s)) ∧
      (∀ s, v' (m s + gDollar a0 a1 (x s)) * (a0 - a1 * x s) ≤ ιs s * u' (C s) ∧
        (0 < x s → v' (m s + gDollar a0 a1 (x s)) * (a0 - a1 * x s) = ιs s * u' (C s))) ∧
      Transversality r (wealth r A0 y ι (fun s => C s + ιs s * x s) m) := by
  constructor
  · intro hopt
    exact ⟨hopt.1, dollar_euler_of_optimal hβ hu hv hopt, dollar_money_foc_of_optimal hβ hu hv hopt,
      dollar_foreign_kkt_of_optimal hβ hu hv hopt, dollar_tvc_of_optimal hr hu hv hupos hopt⟩
  · rintro ⟨hadm, he, hm, hk, htvc⟩
    exact dollar_isOptimal_of_foc hβ hr ha1 hcu hcv hu hv hv0 hadm
      (hupos _ (hadm.1 0)).le he hm hk htvc

/-- **The book's first-order conditions (65) and (66) in nominal form**, derived from
two-money optimality (O&R p. 552): with `ι = userCost r P`, `ι^* = userCost r Pstar`,
`u'(C_t)/P_t = v'(L_t)/P_t + βu'(C_{t+1})/P_{t+1}` and, when `x_t > 0`,
`u'(C_t)/P^*_t = v'(L_t)g'(x_t)/P^*_t + βu'(C_{t+1})/P^*_{t+1}`. -/
theorem dollar_65_66_of_optimal {u v u' v' : ℝ → ℝ} {a0 a1 β r A0 : ℝ}
    {y P Pstar C m x : ℕ → ℝ} (hβ : 0 < β) (hr : 0 < 1 + r) (hP : ∀ s, 0 < P s)
    (hPs : ∀ s, 0 < Pstar s) (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hv : ∀ L, 0 < L → HasDerivAt v (v' L) L)
    (hopt : DollarOptimal u v a0 a1 β r A0 y (userCost r P) (userCost r Pstar) C m x) (t : ℕ) :
    u' (C t) / P t = v' (m t + gDollar a0 a1 (x t)) / P t + β * u' (C (t + 1)) / P (t + 1) ∧
      (0 < x t → u' (C t) / Pstar t = v' (m t + gDollar a0 a1 (x t)) * (a0 - a1 * x t) /
        Pstar t + β * u' (C (t + 1)) / Pstar (t + 1)) := by
  have he := dollar_euler_of_optimal hβ hu hv hopt t
  have hm := dollar_money_foc_of_optimal hβ hu hv hopt t
  have hk := (dollar_foreign_kkt_of_optimal hβ hu hv hopt t).2
  have hr' := hr.ne'
  have h0 := (hP t).ne'
  have h1 := (hP (t + 1)).ne'
  have h2 := (hPs t).ne'
  have h3 := (hPs (t + 1)).ne'
  have hb : β * u' (C (t + 1)) = u' (C t) / (1 + r) := by
    rw [eq_div_iff hr', he]; ring
  refine ⟨?_, fun hxt => ?_⟩
  · rw [hm, mul_div_assoc, hb]
    unfold userCost
    field_simp
    ring
  · rw [hk hxt, mul_div_assoc, hb]
    unfold userCost
    field_simp
    ring

/-- **Foreign-currency demand (67) with its corner, derived from primitives** (O&R p. 553): at
an optimal two-money plan with `a₁ > 0`, `u' > 0` and a positive home user cost `ι_s > 0`,
`x_s = max(0, (a₀ − ι^*_s/ι_s)/a₁)`. -/
theorem dollar_demand_of_optimal {u v u' v' : ℝ → ℝ} {a0 a1 β r A0 : ℝ}
    {y ι ιs C m x : ℕ → ℝ} (hβ : 0 < β) (ha1 : 0 < a1)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hv : ∀ L, 0 < L → HasDerivAt v (v' L) L)
    (hupos : ∀ c, 0 < c → 0 < u' c)
    (hopt : DollarOptimal u v a0 a1 β r A0 y ι ιs C m x) (s : ℕ) (hι : 0 < ι s) :
    x s = max 0 ((a0 - ιs s / ι s) / a1) := by
  have hm := dollar_money_foc_of_optimal hβ hu hv hopt s
  have hk := dollar_foreign_kkt_of_optimal hβ hu hv hopt s
  have hU := hupos _ (hopt.1.1 s)
  rw [hm] at hk
  refine (dollar_demand_iff ha1).1 ⟨hopt.1.2.1 s, ?_, fun hxs => ?_⟩
  · rw [le_div_iff₀ hι]
    exact le_of_mul_le_mul_right (by linarith [hk.1] : (a0 - a1 * x s) * ι s * u' (C s) ≤
      ιs s * u' (C s)) hU
  · rw [eq_div_iff hι.ne']
    exact mul_right_cancel₀ hU.ne' (by linarith [hk.2 hxs] : (a0 - a1 * x s) * ι s * u' (C s) =
      ιs s * u' (C s))

/-- **(67) in the book's notation, from primitives** (O&R p. 553): with `β(1+r) = 1`,
`ι = userCost r P`, `ι^* = userCost r Pstar` and positive home nominal interest
(`1 − βP_s/P_{s+1} > 0`), optimal foreign balances are
`M^F_s/P^*_s = max(0, (a₀ − (1 − βP^*_s/P^*_{s+1})/(1 − βP_s/P_{s+1}))/a₁)`. -/
theorem dollar_67_of_optimal {u v u' v' : ℝ → ℝ} {a0 a1 β r A0 : ℝ}
    {y P Pstar C m x : ℕ → ℝ} (hβ : 0 < β) (ha1 : 0 < a1) (hr : 0 < 1 + r)
    (hβr : β * (1 + r) = 1)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hv : ∀ L, 0 < L → HasDerivAt v (v' L) L)
    (hupos : ∀ c, 0 < c → 0 < u' c)
    (hopt : DollarOptimal u v a0 a1 β r A0 y (userCost r P) (userCost r Pstar) C m x) (s : ℕ)
    (hι : 0 < 1 - β * P s / P (s + 1)) :
    x s = max 0 ((a0 - (1 - β * Pstar s / Pstar (s + 1)) / (1 - β * P s / P (s + 1))) / a1) := by
  have hb : β = (1 + r)⁻¹ := by
    have := hr.ne'
    field_simp
    exact hβr
  have e : ∀ Q : ℕ → ℝ, userCost r Q s = 1 - β * Q s / Q (s + 1) := fun Q => by
    unfold userCost; rw [hb]; ring
  have := dollar_demand_of_optimal hβ ha1 hu hv hupos hopt s (by rw [e]; exact hι)
  rw [e, e] at this
  exact this

end ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility
