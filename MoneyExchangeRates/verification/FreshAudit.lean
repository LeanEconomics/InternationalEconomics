import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Moments.Covariance
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Cagan money-demand equation

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§8.2, pp. 515–517. In logs, money demand is `m_t − p_t = −η(p_{t+1} − p_t)`, so the
price level satisfies `p_t = (m_t + η p_{t+1})/(1 + η)`.
-/

namespace ObstfeldRogoff.MoneyExchangeRates

/-- The Cagan money-demand residual `m − p + η(p′ − p)` (O&R (8.2), p. 516). -/
def caganResidual (η m p p' : ℝ) : ℝ := m - p + η * (p' - p)

/-- **The price level from money demand** (O&R (8.3), p. 516): the residual vanishes iff
`p = (m + η p′)/(1 + η)`. -/
theorem cagan_price_iff {η m p p' : ℝ} (hη : 1 + η ≠ 0) :
    caganResidual η m p p' = 0 ↔ p = (m + η * p') / (1 + η) := by
  unfold caganResidual
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- A constant money supply supports a constant price level equal to it (O&R §8.2). -/
theorem cagan_steady (η m : ℝ) : caganResidual η m m m = 0 := by
  unfold caganResidual
  ring

end ObstfeldRogoff.MoneyExchangeRates

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Cagan model in discrete time

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §8.2.1–8.2.4,
§8.2.6–8.2.7, §8.4.1, §8.4.3 and Exercise 1, pp. 515–530, 554–557, 566–567, 599.

* The perfect-foresight Cagan equation (5)–(6); the forward iteration (7); the no-bubble
  condition (8) and its growth-rate form (fn 6); the fundamental solution (9), which is the
  unique solution satisfying (8); every solution is (9) plus a bubble `b₀((1+η)/η)^t` (11);
  neutrality (weights sum to one); the examples (10), fn 8 and Figure 8.1.
* The stochastic Cagan model (12)–(14) on a finite Markov chain: the Neumann-series solution
  is the unique bounded solution; along an event tree every solution is the fundamental plus
  a bubble `B = q E B`; bounded bubbles vanish and unbounded ones exist; the AR(1) analogue
  `K f = ρ f` gives (14).
* Seignorage (20)–(23) and fn 13: `μ(1+μ)^{−η−1}` has the unique *global* maximiser
  `μ = 1/η` on `(−1, ∞)` (the book gives only the first-order condition).
* The monetary model of the exchange rate (24)–(32), with the Markov version of (31).
* Fixed rates, crawling pegs and the interest-rate-peg indeterminacy (68), fn 44; the
  two-country relation (78); Exercise 1 (future fixing), deterministic and stochastic.

Conventions: `q = η/(1+η)` is the discount factor on future money; paths are `ℕ → ℝ`.
-/

namespace ObstfeldRogoff.MoneyExchangeRates.CaganModel

open Filter Topology

/-! ## The discount factor `q = η/(1+η)` -/

/-- O&R (7), p. 518: the weight `η/(1+η)` on next period's price level. -/
noncomputable def disc (η : ℝ) : ℝ := η / (1 + η)

/-- O&R (7), p. 518: `q > 0` for `η > 0`. -/
theorem disc_pos {η : ℝ} (hη : 0 < η) : 0 < disc η := by
  unfold disc; positivity

/-- O&R (7), p. 518: `q < 1`. -/
theorem disc_lt_one {η : ℝ} (hη : 0 < η) : disc η < 1 := by
  unfold disc; rw [div_lt_one (by linarith)]; linarith

/-- O&R p. 519: `1 − q = 1/(1+η)`. -/
theorem one_sub_disc {η : ℝ} (hη : 0 < η) : 1 - disc η = 1 / (1 + η) := by
  unfold disc; field_simp; ring

/-- O&R (11), p. 520: `1/q = (1+η)/η`, the growth factor of bubbles. -/
theorem inv_disc (η : ℝ) : (disc η)⁻¹ = (1 + η) / η := by
  unfold disc; rw [inv_div]

/-- O&R p. 520: `1/q > 1`. -/
theorem one_lt_inv_disc {η : ℝ} (hη : 0 < η) : 1 < (disc η)⁻¹ := by
  rw [inv_disc η, one_lt_div hη]; linarith

/-! ## A generic forward-solution lemma -/

/-- O&R (7), p. 518 (generic form): if `x_t = a_t + q x_{t+1}` for all `t`, then
`x_t = Σ_{j<T} q^j a_{t+j} + q^T x_{t+T}` for every horizon `T`. -/
theorem forward_iterate_generic (q : ℝ) (a x : ℕ → ℝ) (h : ∀ t, x t = a t + q * x (t + 1))
    (t T : ℕ) :
    x t = (∑ j ∈ Finset.range T, q ^ j * a (t + j)) + q ^ T * x (t + T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [ih, Finset.sum_range_succ, h (t + T)]
    rw [show t + T + 1 = t + (T + 1) by ring]
    ring

/-- O&R (7)–(9), p. 518 (generic form): if `x_t = a_t + q x_{t+1}`, the series
`Σ q^j a_{t+j}` converges and `q^T x_{t+T} → 0`, then `x_t = Σ' q^j a_{t+j}`. -/
theorem eq_tsum_of_forward_generic (q : ℝ) (a x : ℕ → ℝ) (h : ∀ t, x t = a t + q * x (t + 1))
    (t : ℕ) (hs : Summable fun j => q ^ j * a (t + j))
    (hlim : Tendsto (fun T => q ^ T * x (t + T)) atTop (𝓝 0)) :
    x t = ∑' j, q ^ j * a (t + j) := by
  have h1 : Tendsto (fun T => (∑ j ∈ Finset.range T, q ^ j * a (t + j)) + q ^ T * x (t + T))
      atTop (𝓝 ((∑' j, q ^ j * a (t + j)) + 0)) :=
    hs.tendsto_sum_tsum_nat.add hlim
  have h2 : (fun T => (∑ j ∈ Finset.range T, q ^ j * a (t + j)) + q ^ T * x (t + T)) =
      fun _ => x t := by
    funext T; exact (forward_iterate_generic q a x h t T).symm
  rw [h2, add_zero] at h1
  exact tendsto_nhds_unique tendsto_const_nhds h1

/-- O&R fn 6, p. 518 (generic form): summability of `q^s a_s` is inherited by every shifted
series `q^j a_{t+j}` (for `q ≠ 0`). -/
theorem summable_shift_generic {q : ℝ} (hq : q ≠ 0) {a : ℕ → ℝ}
    (hs : Summable fun s => q ^ s * a s) (t : ℕ) : Summable fun j => q ^ j * a (t + j) := by
  have h1 : Summable fun n => q ^ (n + t) * a (n + t) :=
    (summable_nat_add_iff (f := fun s => q ^ s * a s) t).2 hs
  have h2 := h1.mul_left ((q ^ t)⁻¹)
  refine h2.congr fun j => ?_
  rw [pow_add, add_comm j t]
  field_simp

/-- O&R (8), p. 518 (generic form): the tail `q^T Σ' q^j a_{t+T+j}` of the forward sum tends
to zero (for a non-summable series both sides are the junk value `0`, so no hypothesis is
needed; callers always supply summability). -/
theorem tendsto_tail_generic {q : ℝ} (hq : q ≠ 0) (a : ℕ → ℝ) (t : ℕ) :
    Tendsto (fun T => q ^ T * ∑' j, q ^ j * a (t + T + j)) atTop (𝓝 0) := by
  have key : ∀ T, q ^ T * ∑' j, q ^ j * a (t + T + j) =
      (q ^ t)⁻¹ * ∑' k, q ^ (k + (t + T)) * a (k + (t + T)) := by
    intro T
    rw [← tsum_mul_left, ← tsum_mul_left]
    congr 1; funext k
    rw [show k + (t + T) = t + T + k by ring, pow_add, pow_add]
    field_simp
  simp_rw [key]
  have h0 := tendsto_sum_nat_add (fun s => q ^ s * a s)
  have h1 : Tendsto (fun T => ∑' k, q ^ (k + (t + T)) * a (k + (t + T))) atTop (𝓝 0) :=
    h0.comp (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega)
      (fun b => ⟨b, by omega⟩))
  simpa using h1.const_mul ((q ^ t)⁻¹)

/-! ## The perfect-foresight Cagan model -/

/-- O&R (5), p. 518: `p` is a perfect-foresight equilibrium price path for the money path `m`
when `m_t − p_t = −η(p_{t+1} − p_t)` at every date. -/
def IsCaganPath (η : ℝ) (m p : ℕ → ℝ) : Prop :=
  ∀ t, caganResidual η (m t) (p t) (p (t + 1)) = 0

/-- O&R (6), p. 518: the Cagan equation is `p_t = m_t/(1+η) + q p_{t+1}`. -/
theorem isCaganPath_iff {η : ℝ} (hη : 0 < η) (m p : ℕ → ℝ) :
    IsCaganPath η m p ↔ ∀ t, p t = m t / (1 + η) + disc η * p (t + 1) := by
  unfold IsCaganPath
  refine forall_congr' fun t => ?_
  rw [cagan_price_iff (by linarith)]
  unfold disc
  constructor <;> intro h <;> rw [h] <;> field_simp

/-- O&R (7), p. 518: every equilibrium path satisfies, for each horizon `T`,
`p_t = (1/(1+η)) Σ_{j<T} q^j m_{t+j} + q^T p_{t+T}`. -/
theorem forward_iteration {η : ℝ} (hη : 0 < η) {m p : ℕ → ℝ} (hp : IsCaganPath η m p)
    (t T : ℕ) :
    p t = 1 / (1 + η) * (∑ j ∈ Finset.range T, disc η ^ j * m (t + j)) +
      disc η ^ T * p (t + T) := by
  have h := (isCaganPath_iff hη m p).1 hp
  rw [forward_iterate_generic (disc η) (fun s => m s / (1 + η)) p h t T, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- O&R fn 6, p. 518: the summability condition on the money path under which (9) converges,
`Σ q^s m_s < ∞`. -/
def CaganSummable (η : ℝ) (m : ℕ → ℝ) : Prop := Summable fun s => disc η ^ s * m s

/-- O&R (9), p. 518: the fundamental (no-bubble) price level
`p_t = (1/(1+η)) Σ_{s ≥ t} (η/(1+η))^{s−t} m_s`. -/
noncomputable def fundamental (η : ℝ) (m : ℕ → ℝ) (t : ℕ) : ℝ :=
  1 / (1 + η) * ∑' j, disc η ^ j * m (t + j)

/-- O&R fn 6, p. 518, made precise: if `|m_s| ≤ A κ^s` with `0 ≤ κ < (1+η)/η` (log money
grows more slowly than the rate `(1+η)/η`), then `Σ q^s m_s` converges. -/
theorem caganSummable_of_growth {η : ℝ} (hη : 0 < η) {m : ℕ → ℝ} {A κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : κ < (1 + η) / η) (hm : ∀ s, |m s| ≤ A * κ ^ s) : CaganSummable η m := by
  have hq := disc_pos hη
  have hqk : disc η * κ < 1 := by
    have : disc η * ((1 + η) / η) = 1 := by unfold disc; field_simp
    nlinarith
  have hg : Summable fun s : ℕ => A * (disc η * κ) ^ s :=
    (summable_geometric_of_lt_one (by positivity) hqk).mul_left A
  refine Summable.of_norm_bounded hg fun s => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hq s), mul_pow]
  calc disc η ^ s * |m s| ≤ disc η ^ s * (A * κ ^ s) :=
        mul_le_mul_of_nonneg_left (hm s) (pow_pos hq s).le
    _ = A * (disc η ^ s * κ ^ s) := by ring

/-- O&R fn 6, p. 518: a bounded money path satisfies the summability condition. -/
theorem caganSummable_of_bounded {η : ℝ} (hη : 0 < η) {m : ℕ → ℝ} {A : ℝ}
    (hm : ∀ s, |m s| ≤ A) : CaganSummable η m :=
  caganSummable_of_growth (κ := 1) hη zero_le_one
    (by rw [lt_div_iff₀ hη]; linarith) (by simpa using hm)

/-- O&R (9), p. 518: under fn 6 every shifted forward sum converges. -/
theorem summable_shift {η : ℝ} (hη : 0 < η) {m : ℕ → ℝ} (hm : CaganSummable η m) (t : ℕ) :
    Summable fun j => disc η ^ j * m (t + j) :=
  summable_shift_generic (disc_pos hη).ne' hm t

/-- O&R (6), (9), p. 518: the fundamental satisfies the one-step recursion
`p_t = m_t/(1+η) + q p_{t+1}`. -/
theorem fundamental_recursion {η : ℝ} (hη : 0 < η) {m : ℕ → ℝ} (hm : CaganSummable η m)
    (t : ℕ) : fundamental η m t = m t / (1 + η) + disc η * fundamental η m (t + 1) := by
  unfold fundamental
  rw [(summable_shift hη hm t).tsum_eq_zero_add]
  have e : ∀ b : ℕ, disc η ^ (b + 1) * m (t + (b + 1)) =
      disc η * (disc η ^ b * m (t + 1 + b)) := by
    intro b; rw [show t + (b + 1) = t + 1 + b by ring]; ring
  simp_rw [e, tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero]
  ring

/-- O&R (9), p. 518: the fundamental price path is an equilibrium. -/
theorem fundamental_isCaganPath {η : ℝ} (hη : 0 < η) {m : ℕ → ℝ} (hm : CaganSummable η m) :
    IsCaganPath η m (fundamental η m) :=
  (isCaganPath_iff hη m _).2 (fundamental_recursion hη hm)

/-- O&R (8), p. 518: the fundamental satisfies the no-bubble condition
`lim_{T→∞} q^T p_{t+T} = 0` at every date `t`. -/
theorem fundamental_noBubble {η : ℝ} (hη : 0 < η) (m : ℕ → ℝ) (t : ℕ) :
    Tendsto (fun T => disc η ^ T * fundamental η m (t + T)) atTop (𝓝 0) := by
  unfold fundamental
  have h := (tendsto_tail_generic (disc_pos hη).ne' m t).const_mul (1 / (1 + η))
  rw [mul_zero] at h
  refine h.congr fun T => ?_
  ring

/-- O&R (8), p. 518: the date-0 no-bubble condition `q^T p_T → 0` implies the condition at
every date `t`. -/
theorem noBubble_shift {η : ℝ} (hη : 0 < η) {p : ℕ → ℝ}
    (h0 : Tendsto (fun T => disc η ^ T * p T) atTop (𝓝 0)) (t : ℕ) :
    Tendsto (fun T => disc η ^ T * p (t + T)) atTop (𝓝 0) := by
  have hq := (disc_pos hη).ne'
  have h1 : Tendsto (fun T => disc η ^ (t + T) * p (t + T)) atTop (𝓝 0) :=
    h0.comp (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega) (fun b => ⟨b, by omega⟩))
  have h2 := h1.const_mul ((disc η ^ t)⁻¹)
  rw [mul_zero] at h2
  refine h2.congr fun T => ?_
  rw [pow_add]; field_simp

/-- O&R (7)–(9), p. 518: an equilibrium path satisfying the no-bubble condition (8) equals
the fundamental (9). -/
theorem eq_fundamental_of_noBubble {η : ℝ} (hη : 0 < η) {m p : ℕ → ℝ}
    (hm : CaganSummable η m) (hp : IsCaganPath η m p)
    (h8 : Tendsto (fun T => disc η ^ T * p T) atTop (𝓝 0)) : p = fundamental η m := by
  funext t
  have h := (isCaganPath_iff hη m p).1 hp
  have hs : Summable fun j => disc η ^ j * (m (t + j) / (1 + η)) :=
    ((summable_shift hη hm t).mul_left (1 / (1 + η))).congr fun j => by ring
  rw [eq_tsum_of_forward_generic (disc η) (fun s => m s / (1 + η)) p h t hs
    (noBubble_shift hη h8 t), fundamental, ← tsum_mul_left]
  congr 1; funext j; ring

/-- O&R (8)–(9), p. 518: **existence and uniqueness**: there is exactly one equilibrium price
path satisfying the no-bubble condition, namely (9). -/
theorem existsUnique_noBubble {η : ℝ} (hη : 0 < η) {m : ℕ → ℝ} (hm : CaganSummable η m) :
    ∃! p : ℕ → ℝ, IsCaganPath η m p ∧ Tendsto (fun T => disc η ^ T * p T) atTop (𝓝 0) := by
  refine ⟨fundamental η m, ⟨fundamental_isCaganPath hη hm, ?_⟩, fun p hp => ?_⟩
  · simpa using fundamental_noBubble hη m 0
  · exact eq_fundamental_of_noBubble hη hm hp.1 hp.2

/-- O&R (11), p. 520: the price paths `(9) + b₀((1+η)/η)^t` are equilibria for every `b₀`. -/
theorem bubble_isCaganPath {η : ℝ} (hη : 0 < η) {m : ℕ → ℝ} (hm : CaganSummable η m)
    (b₀ : ℝ) :
    IsCaganPath η m (fun t => fundamental η m t + b₀ * ((1 + η) / η) ^ t) := by
  rw [isCaganPath_iff hη]
  intro t
  rw [fundamental_recursion hη hm t, pow_succ]
  unfold disc
  field_simp
  ring

/-- O&R (11), p. 520: **every** equilibrium path is the fundamental plus a bubble:
`p_t = (9) + b₀((1+η)/η)^t` with `b₀ = p₀ − (fundamental at 0)`. -/
theorem eq_fundamental_add_bubble {η : ℝ} (hη : 0 < η) {m p : ℕ → ℝ}
    (hm : CaganSummable η m) (hp : IsCaganPath η m p) (t : ℕ) :
    p t = fundamental η m t + (p 0 - fundamental η m 0) * ((1 + η) / η) ^ t := by
  have h := (isCaganPath_iff hη m p).1 hp
  have hf := fundamental_recursion hη hm
  have hd : ∀ s, p (s + 1) - fundamental η m (s + 1) =
      (1 + η) / η * (p s - fundamental η m s) := by
    intro s
    have e1 := h s
    have e2 := hf s
    unfold disc at e1 e2
    have hη' : η ≠ 0 := hη.ne'
    have h1 : (1 + η) ≠ 0 := by linarith
    field_simp
    field_simp at e1 e2
    linarith
  induction t with
  | zero => simp
  | succ s ih =>
    have e : p (s + 1) = fundamental η m (s + 1) + (1 + η) / η * (p s - fundamental η m s) := by
      linarith [hd s]
    rw [e, ih, pow_succ]
    ring

/-- O&R (11), p. 520: the characterisation of the equilibrium set: `p` is an equilibrium iff
it is the fundamental plus `b₀((1+η)/η)^t` for some (necessarily unique) `b₀`. -/
theorem isCaganPath_iff_bubble {η : ℝ} (hη : 0 < η) {m p : ℕ → ℝ} (hm : CaganSummable η m) :
    IsCaganPath η m p ↔ ∃ b₀ : ℝ, ∀ t, p t = fundamental η m t + b₀ * ((1 + η) / η) ^ t := by
  constructor
  · intro hp; exact ⟨_, eq_fundamental_add_bubble hη hm hp⟩
  · rintro ⟨b₀, hb⟩
    have : p = fun t => fundamental η m t + b₀ * ((1 + η) / η) ^ t := funext hb
    rw [this]; exact bubble_isCaganPath hη hm b₀

/-- O&R (11), p. 520: the bubble coefficient is unique. -/
theorem bubble_coeff_unique {η : ℝ} {m p : ℕ → ℝ} {b b' : ℝ}
    (hb : ∀ t, p t = fundamental η m t + b * ((1 + η) / η) ^ t)
    (hb' : ∀ t, p t = fundamental η m t + b' * ((1 + η) / η) ^ t) : b = b' := by
  have := (hb 0).symm.trans (hb' 0)
  simpa using this

/-- O&R (8), (11), pp. 518–520: along any equilibrium, `q^t p_t → b₀`: the discounted price
converges to the bubble coefficient. -/
theorem disc_pow_mul_tendsto_bubble {η : ℝ} (hη : 0 < η) {m p : ℕ → ℝ}
    (hm : CaganSummable η m) (hp : IsCaganPath η m p) :
    Tendsto (fun t => disc η ^ t * p t) atTop (𝓝 (p 0 - fundamental η m 0)) := by
  have h0 := fundamental_noBubble hη m 0
  simp only [zero_add] at h0
  have h1 := h0.add_const (p 0 - fundamental η m 0)
  rw [zero_add] at h1
  refine h1.congr fun t => ?_
  have hq := (disc_pos hη).ne'
  rw [eq_fundamental_add_bubble hη hm hp t, ← inv_disc η, inv_pow]
  field_simp

/-- O&R (8), (11), pp. 518–520: an equilibrium satisfies the no-bubble condition iff its
bubble coefficient `b₀` is zero. -/
theorem noBubble_iff_bubble_zero {η : ℝ} (hη : 0 < η) {m p : ℕ → ℝ}
    (hm : CaganSummable η m) (hp : IsCaganPath η m p) :
    Tendsto (fun T => disc η ^ T * p T) atTop (𝓝 0) ↔ p 0 - fundamental η m 0 = 0 := by
  constructor
  · intro h; exact tendsto_nhds_unique (disc_pow_mul_tendsto_bubble hη hm hp) h
  · intro h; rw [← h]; exact disc_pow_mul_tendsto_bubble hη hm hp

/-- O&R fn 6 and (11), pp. 518–520: a bubble solution (`b₀ ≠ 0`) has `|p_t| → ∞`, growing
like `((1+η)/η)^t`: it violates (8). -/
theorem abs_tendsto_atTop_of_bubble {η : ℝ} (hη : 0 < η) {m p : ℕ → ℝ}
    (hm : CaganSummable η m) (hp : IsCaganPath η m p) (hb : p 0 - fundamental η m 0 ≠ 0) :
    Tendsto (fun t => |p t|) atTop atTop := by
  have hq := disc_pos hη
  have h1 : Tendsto (fun t => |disc η ^ t * p t|) atTop (𝓝 |p 0 - fundamental η m 0|) :=
    (disc_pow_mul_tendsto_bubble hη hm hp).abs
  have h2 : Tendsto (fun t : ℕ => ((disc η)⁻¹) ^ t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv_disc hη)
  have h3 := h1.pos_mul_atTop (abs_pos.2 hb) h2
  refine h3.congr fun t => ?_
  rw [abs_mul, abs_of_pos (pow_pos hq t), mul_comm, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ hq.ne', one_pow, one_mul]

/-! ## Neutrality, monotonicity and examples -/

/-- O&R p. 519: the weights in (9) sum to one: `(1/(1+η)) Σ q^j = 1`. -/
theorem weights_sum_one {η : ℝ} (hη : 0 < η) : 1 / (1 + η) * ∑' j : ℕ, disc η ^ j = 1 := by
  rw [tsum_geometric_of_lt_one (disc_pos hη).le (disc_lt_one hη), one_sub_disc hη]
  field_simp

/-- O&R p. 519: a constant money supply `m̄` gives the constant price level `p = m̄`. -/
theorem fundamental_const {η : ℝ} (hη : 0 < η) (c : ℝ) (t : ℕ) :
    fundamental η (fun _ => c) t = c := by
  unfold fundamental
  rw [tsum_mul_right, ← mul_assoc, weights_sum_one hη, one_mul]

/-- O&R p. 519 (**neutrality**): adding a constant `c` to the whole log-money path adds `c` to
the price level at every date. -/
theorem fundamental_add_const {η : ℝ} (hη : 0 < η) {m : ℕ → ℝ} (hm : CaganSummable η m)
    (c : ℝ) (t : ℕ) : fundamental η (fun s => m s + c) t = fundamental η m t + c := by
  have hg : Summable fun j : ℕ => disc η ^ j * c :=
    (summable_geometric_of_lt_one (disc_pos hη).le (disc_lt_one hη)).mul_right c
  have := fundamental_const hη c t
  unfold fundamental at this ⊢
  simp_rw [mul_add]
  rw [(summable_shift hη hm t).tsum_add hg, mul_add, this]

/-- O&R (9), p. 518: the fundamental is linear in the money path. -/
theorem fundamental_add {η : ℝ} (hη : 0 < η) {m m' : ℕ → ℝ} (hm : CaganSummable η m)
    (hm' : CaganSummable η m') (t : ℕ) :
    fundamental η (fun s => m s + m' s) t = fundamental η m t + fundamental η m' t := by
  unfold fundamental
  simp_rw [mul_add]
  rw [(summable_shift hη hm t).tsum_add (summable_shift hη hm' t), mul_add]

/-- O&R (9), p. 518: the fundamental is homogeneous in the money path. -/
theorem fundamental_smul (η c : ℝ) (m : ℕ → ℝ) (t : ℕ) :
    fundamental η (fun s => c * m s) t = c * fundamental η m t := by
  unfold fundamental
  rw [show (fun j => disc η ^ j * (c * m (t + j))) = fun j => c * (disc η ^ j * m (t + j)) by
    funext j; ring, tsum_mul_left]
  ring

/-- O&R (9), p. 518: the price level is monotone in the money path (the weights are
positive). -/
theorem fundamental_mono {η : ℝ} (hη : 0 < η) {m m' : ℕ → ℝ} (hm : CaganSummable η m)
    (hm' : CaganSummable η m') (hle : ∀ s, m s ≤ m' s) (t : ℕ) :
    fundamental η m t ≤ fundamental η m' t := by
  unfold fundamental
  refine mul_le_mul_of_nonneg_left ?_ (by have : 0 < 1 + η := by linarith
                                          positivity)
  exact (summable_shift hη hm t).tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (hle _) (pow_pos (disc_pos hη) j).le)
    (summable_shift hη hm' t)

/-- O&R fn 8, p. 519: `Σ_j j q^j = q/(1−q)² = η(1+η)`. -/
theorem tsum_nat_mul_disc_pow {η : ℝ} (hη : 0 < η) :
    ∑' j : ℕ, (j : ℝ) * disc η ^ j = η * (1 + η) := by
  have hq := disc_pos hη
  have hn : ‖disc η‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq]; exact disc_lt_one hη
  rw [tsum_coe_mul_geometric_of_norm_lt_one hn, one_sub_disc hη]
  unfold disc
  field_simp

/-- O&R (10) and fn 8, p. 519: a linearly growing money supply `m_t = m̄ + μt` has
`CaganSummable`. -/
theorem caganSummable_linear {η : ℝ} (hη : 0 < η) (mbar μ : ℝ) :
    CaganSummable η (fun s => mbar + μ * s) := by
  have hq := disc_pos hη
  have hn : ‖disc η‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq]; exact disc_lt_one hη
  have h1 := (summable_geometric_of_lt_one hq.le (disc_lt_one hη)).mul_left mbar
  have h2 := (hasSum_coe_mul_geometric_of_norm_lt_one hn).summable.mul_left μ
  refine (h1.add h2).congr fun s => ?_
  ring

/-- O&R (10) and fn 8, p. 519: with `m_t = m̄ + μt` the fundamental price level is
`p_t = m_t + ημ`. -/
theorem fundamental_linear {η : ℝ} (hη : 0 < η) (mbar μ : ℝ) (t : ℕ) :
    fundamental η (fun s => mbar + μ * s) t = mbar + μ * t + η * μ := by
  have hq := disc_pos hη
  have hn : ‖disc η‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq]; exact disc_lt_one hη
  have hg := summable_geometric_of_lt_one hq.le (disc_lt_one hη)
  have h2 := (hasSum_coe_mul_geometric_of_norm_lt_one hn).summable
  have e : (fun j : ℕ => disc η ^ j * (mbar + μ * ((t + j : ℕ) : ℝ))) =
      fun j : ℕ => (mbar + μ * t) * disc η ^ j + μ * ((j : ℝ) * disc η ^ j) := by
    funext j; push_cast; ring
  unfold fundamental
  rw [e, (hg.mul_left _).tsum_add (h2.mul_left μ), tsum_mul_left, tsum_mul_left,
    tsum_nat_mul_disc_pow hη, tsum_geometric_of_lt_one hq.le (disc_lt_one hη), one_sub_disc hη]
  field_simp

/-- O&R (10), p. 519: the guess `p_t = m_t + ημ` solves (5) directly (constant inflation
`μ`). -/
theorem linear_isCaganPath (η mbar μ : ℝ) :
    IsCaganPath η (fun s => mbar + μ * s) (fun s => mbar + μ * s + η * μ) := by
  intro t; unfold caganResidual; push_cast; ring

/-- O&R (9), p. 518: if the money path is constant at `c` from date `t` on, the fundamental
price level at `t` is `c`. -/
theorem fundamental_eventually_const {η : ℝ} (hη : 0 < η) {m : ℕ → ℝ} {c : ℝ} {t : ℕ}
    (hc : ∀ j, m (t + j) = c) : fundamental η m t = c := by
  have := fundamental_const hη c t
  unfold fundamental at this ⊢
  simp_rw [hc]; exact this

/-- O&R p. 520, Figure 8.1: the money path of an announced permanent rise from `m̄` to `m̄′`
at date `T`. -/
def stepMoney (mbar mbar' : ℝ) (T : ℕ) (t : ℕ) : ℝ := if t < T then mbar else mbar'

/-- O&R p. 520: the announced step path is bounded, hence satisfies fn 6. -/
theorem caganSummable_stepMoney {η : ℝ} (hη : 0 < η) (mbar mbar' : ℝ) (T : ℕ) :
    CaganSummable η (stepMoney mbar mbar' T) := by
  refine caganSummable_of_bounded (A := |mbar| + |mbar'|) hη fun s => ?_
  unfold stepMoney
  split_ifs <;> linarith [abs_nonneg mbar, abs_nonneg mbar']

/-- O&R p. 520, Figure 8.1: after the rise the price level is `m̄′`. -/
theorem fundamental_stepMoney_ge {η : ℝ} (hη : 0 < η) (mbar mbar' : ℝ) {T t : ℕ}
    (ht : T ≤ t) : fundamental η (stepMoney mbar mbar' T) t = mbar' :=
  fundamental_eventually_const hη fun j => by simp [stepMoney, show ¬ (t + j < T) by omega]

/-- O&R p. 520, Figure 8.1: before the rise, `p_t = m̄ + (η/(1+η))^{T−t}(m̄′ − m̄)` for
`t ≤ T` (at `t = T` this is `m̄′`: the price level reaches its new level with no jump). -/
theorem fundamental_stepMoney_le {η : ℝ} (hη : 0 < η) (mbar mbar' : ℝ) {T t : ℕ}
    (ht : t ≤ T) :
    fundamental η (stepMoney mbar mbar' T) t = mbar + disc η ^ (T - t) * (mbar' - mbar) := by
  have hs := caganSummable_stepMoney hη mbar mbar' T
  have aux : ∀ k, k ≤ T → fundamental η (stepMoney mbar mbar' T) (T - k) =
      mbar + disc η ^ k * (mbar' - mbar) := by
    intro k
    induction k with
    | zero => intro _; simp [fundamental_stepMoney_ge hη mbar mbar' (le_refl T)]
    | succ k ih =>
      intro hk
      have e1 := fundamental_recursion hη hs (T - (k + 1))
      rw [show T - (k + 1) + 1 = T - k by omega, ih (by omega)] at e1
      have hm : stepMoney mbar mbar' T (T - (k + 1)) = mbar := by
        simp [stepMoney, show T - (k + 1) < T by omega]
      rw [e1, hm]
      have hsum : 1 / (1 + η) + disc η = 1 := by rw [← one_sub_disc hη]; ring
      linear_combination mbar * hsum
  have := aux (T - t) (by omega)
  rwa [show T - (T - t) = t by omega] at this

/-- O&R p. 520, Figure 8.1: the unanticipated announcement at date 0 makes the price level
jump from `m̄` to `m̄ + (η/(1+η))^T(m̄′ − m̄)`, a jump strictly between `0` and `m̄′ − m̄` when
`m̄′ > m̄` and `T ≥ 1`. -/
theorem stepMoney_jump_at_zero {η : ℝ} (hη : 0 < η) {mbar mbar' : ℝ} (hup : mbar < mbar')
    {T : ℕ} (hT : 1 ≤ T) :
    0 < fundamental η (stepMoney mbar mbar' T) 0 - mbar ∧
      fundamental η (stepMoney mbar mbar' T) 0 - mbar < mbar' - mbar := by
  rw [fundamental_stepMoney_le hη mbar mbar' (Nat.zero_le T), Nat.sub_zero]
  have hq := disc_pos hη
  have h1 : disc η ^ T < 1 := pow_lt_one₀ hq.le (disc_lt_one hη) (by omega)
  constructor <;> nlinarith [pow_pos hq T]

/-- O&R p. 520, Figure 8.1: between the announcement and the rise the price level is
strictly increasing. -/
theorem stepMoney_strictly_increasing {η : ℝ} (hη : 0 < η) {mbar mbar' : ℝ}
    (hup : mbar < mbar') {T t : ℕ} (ht : t < T) :
    fundamental η (stepMoney mbar mbar' T) t < fundamental η (stepMoney mbar mbar' T) (t + 1) := by
  rw [fundamental_stepMoney_le hη mbar mbar' ht.le, fundamental_stepMoney_le hη mbar mbar' ht]
  have : disc η ^ (T - t) < disc η ^ (T - (t + 1)) :=
    pow_lt_pow_right_of_lt_one₀ (disc_pos hη) (disc_lt_one hη) (by omega)
  nlinarith

/-- O&R p. 520, Figure 8.1: the price path "accelerates": it is strictly convex in `t` up to
the date of the rise. -/
theorem stepMoney_strictly_convex {η : ℝ} (hη : 0 < η) {mbar mbar' : ℝ} (hup : mbar < mbar')
    {T t : ℕ} (ht : t + 2 ≤ T) :
    fundamental η (stepMoney mbar mbar' T) (t + 1) - fundamental η (stepMoney mbar mbar' T) t <
      fundamental η (stepMoney mbar mbar' T) (t + 2) -
        fundamental η (stepMoney mbar mbar' T) (t + 1) := by
  rw [fundamental_stepMoney_le hη mbar mbar' (by omega : t ≤ T),
    fundamental_stepMoney_le hη mbar mbar' (by omega : t + 1 ≤ T),
    fundamental_stepMoney_le hη mbar mbar' ht]
  obtain ⟨n, hn⟩ : ∃ n, T - (t + 2) = n := ⟨_, rfl⟩
  rw [show T - t = n + 2 by omega, show T - (t + 1) = n + 1 by omega, hn]
  have hq := disc_pos hη
  have hq1 := disc_lt_one hη
  have ha := pow_pos hq n
  have hd : 0 < mbar' - mbar := by linarith
  have key : disc η ^ (n + 1) - disc η ^ (n + 2) < disc η ^ n - disc η ^ (n + 1) := by
    rw [pow_succ, pow_succ, pow_succ]
    nlinarith [mul_pos ha (mul_pos (sub_pos.2 hq1) (sub_pos.2 hq1))]
  nlinarith

/-! ## The stochastic Cagan model on a finite Markov chain -/

/-- O&R §8.2.4, p. 521: a Markov transition kernel on a finite state space (rows are
probability vectors). -/
structure MarkovKernel (S : Type) [Fintype S] where
  K : S → S → ℝ
  nonneg : ∀ s s', 0 ≤ K s s'
  rowSum : ∀ s, ∑ s', K s s' = 1

variable {S : Type} [Fintype S]

/-- O&R (12), p. 521: the conditional expectation `E_t g(s_{t+1})` given `s_t = s`. -/
def kernelApply (P : MarkovKernel S) (g : S → ℝ) (s : S) : ℝ := ∑ s', P.K s s' * g s'

/-- O&R (12), p. 521: the `n`-step conditional expectation `E_t g(s_{t+n})`. -/
def kernelPow (P : MarkovKernel S) (n : ℕ) (g : S → ℝ) : S → ℝ := (kernelApply P)^[n] g

/-- O&R (12), p. 521: the conditional expectation of a constant is that constant. -/
theorem kernelApply_const (P : MarkovKernel S) (c : ℝ) (s : S) :
    kernelApply P (fun _ => c) s = c := by
  unfold kernelApply; rw [← Finset.sum_mul, P.rowSum, one_mul]

/-- O&R (12), p. 521: conditional expectation is linear. -/
theorem kernelApply_linear (P : MarkovKernel S) (a b : ℝ) (g h : S → ℝ) (s : S) :
    kernelApply P (fun x => a * g x + b * h x) s =
      a * kernelApply P g s + b * kernelApply P h s := by
  unfold kernelApply
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- O&R (12), p. 521: conditional expectation is monotone. -/
theorem kernelApply_mono (P : MarkovKernel S) {g h : S → ℝ} (hgh : ∀ x, g x ≤ h x) (s : S) :
    kernelApply P g s ≤ kernelApply P h s :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hgh x) (P.nonneg s x)

/-- O&R (12), p. 521: conditional expectation does not increase the sup bound
(`|E g| ≤ M` whenever `|g| ≤ M`). -/
theorem kernelApply_abs_le (P : MarkovKernel S) {g : S → ℝ} {M : ℝ} (hg : ∀ x, |g x| ≤ M)
    (s : S) : |kernelApply P g s| ≤ M := by
  unfold kernelApply
  calc |∑ s', P.K s s' * g s'| ≤ ∑ s', |P.K s s' * g s'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', P.K s s' * M := Finset.sum_le_sum fun x _ => by
        rw [abs_mul, abs_of_nonneg (P.nonneg s x)]
        exact mul_le_mul_of_nonneg_left (hg x) (P.nonneg s x)
    _ = M := by rw [← Finset.sum_mul, P.rowSum, one_mul]

/-- O&R (12), p. 521: the `n`-step expectation obeys the same sup bound. -/
theorem kernelPow_abs_le (P : MarkovKernel S) {g : S → ℝ} {M : ℝ} (hg : ∀ x, |g x| ≤ M)
    (n : ℕ) (s : S) : |kernelPow P n g s| ≤ M := by
  induction n generalizing s with
  | zero => exact hg s
  | succ n ih =>
    unfold kernelPow at ih ⊢
    rw [Function.iterate_succ_apply']
    exact kernelApply_abs_le P ih s

/-- O&R (12), p. 521: `E^{n+1} g = E(E^n g)`. -/
theorem kernelPow_succ (P : MarkovKernel S) (n : ℕ) (g : S → ℝ) :
    kernelPow P (n + 1) g = kernelApply P (kernelPow P n g) := by
  unfold kernelPow; rw [Function.iterate_succ_apply']

/-- O&R (12), p. 521: `E^{n+1} g = E^n (E g)`. -/
theorem kernelPow_succ' (P : MarkovKernel S) (n : ℕ) (g : S → ℝ) :
    kernelPow P (n + 1) g = kernelPow P n (kernelApply P g) := by
  unfold kernelPow; rw [Function.iterate_succ_apply]

/-- O&R (12), p. 521: conditional expectation commutes with convergent infinite sums. -/
theorem kernelApply_tsum (P : MarkovKernel S) (a : ℕ → S → ℝ) (ha : ∀ x, Summable fun n => a n x)
    (s : S) : kernelApply P (fun x => ∑' n, a n x) s = ∑' n, kernelApply P (a n) s := by
  unfold kernelApply
  simp_rw [← tsum_mul_left]
  exact (Summable.tsum_finsetSum fun x _ => (ha x).mul_left _).symm

/-- O&R (12), p. 521: a sup bound for a function on a finite state space. -/
theorem abs_le_sum_abs (g : S → ℝ) (s : S) : |g s| ≤ ∑ x, |g x| :=
  Finset.single_le_sum (f := fun x => |g x|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)

/-- O&R (12), p. 521: the forward series `Σ q^n E_t m_{t+n}` converges. -/
theorem summable_markov {η : ℝ} (hη : 0 < η) (P : MarkovKernel S) (f : S → ℝ) (s : S) :
    Summable fun n => disc η ^ n * kernelPow P n f s := by
  have hq := disc_pos hη
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hq.le (disc_lt_one hη)).mul_right (∑ x, |f x|)) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hq n)]
  exact mul_le_mul_of_nonneg_left (kernelPow_abs_le P (abs_le_sum_abs f) n s) (pow_pos hq n).le

/-- O&R (12), p. 521: the no-bubble stochastic price level
`p(s) = (1/(1+η)) Σ_n (η/(1+η))^n E[m_{t+n} | s_t = s]`, with money `m_t = f(s_t)`. -/
noncomputable def markovFundamental (η : ℝ) (P : MarkovKernel S) (f : S → ℝ) (s : S) : ℝ :=
  1 / (1 + η) * ∑' n, disc η ^ n * kernelPow P n f s

/-- O&R (4), p. 517, on a finite Markov chain: `p` is a (state-dependent) rational-expectations
equilibrium price level when `p = f/(1+η) + q E p`. -/
def IsMarkovEqm (η : ℝ) (P : MarkovKernel S) (f p : S → ℝ) : Prop :=
  ∀ s, p s = f s / (1 + η) + disc η * kernelApply P p s

/-- O&R (12), p. 521: the Neumann-series price level solves the stochastic Cagan equation. -/
theorem markovFundamental_isMarkovEqm {η : ℝ} (hη : 0 < η) (P : MarkovKernel S)
    (f : S → ℝ) : IsMarkovEqm η P f (markovFundamental η P f) := by
  intro s
  unfold markovFundamental
  have hsum := summable_markov hη P f
  have hK : kernelApply P (fun x => 1 / (1 + η) * ∑' n, disc η ^ n * kernelPow P n f x) s =
      1 / (1 + η) * ∑' n, disc η ^ n * kernelPow P (n + 1) f s := by
    have e := kernelApply_linear P (1 / (1 + η)) 0 (fun x => ∑' n, disc η ^ n * kernelPow P n f x)
      (fun _ => 0) s
    simp only [zero_mul, add_zero] at e
    rw [e, kernelApply_tsum P _ hsum]
    congr 1; congr 1; funext n
    have e2 := kernelApply_linear P (disc η ^ n) 0 (kernelPow P n f) (fun _ => 0) s
    simp only [zero_mul, add_zero] at e2
    rw [e2, kernelPow_succ]
  rw [hK, (hsum s).tsum_eq_zero_add]
  have e3 : ∀ n : ℕ, disc η ^ (n + 1) * kernelPow P (n + 1) f s =
      disc η * (disc η ^ n * kernelPow P (n + 1) f s) := fun n => by ring
  simp_rw [e3, tsum_mul_left]
  simp only [pow_zero, one_mul]
  unfold kernelPow
  simp only [Function.iterate_zero, id_eq]
  ring

/-- A generic uniqueness lemma used for O&R §8.2.3–8.2.4 (pp. 520–521): if an operator `E`
never increases a sup bound, `0 ≤ q < 1`, and `B = q E B` is bounded, then `B = 0`
(bounded bubbles vanish). -/
theorem bubble_eq_zero_of_bounded {X : Type} (E : (X → ℝ) → X → ℝ)
    (hE : ∀ (g : X → ℝ) (M : ℝ), (∀ x, |g x| ≤ M) → ∀ x, |E g x| ≤ M) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) {B : X → ℝ} (hB : ∀ x, B x = q * E B x) {M : ℝ} (hM : ∀ x, |B x| ≤ M) :
    B = 0 := by
  have hk : ∀ k : ℕ, ∀ x, |B x| ≤ q ^ k * M := by
    intro k
    induction k with
    | zero => simpa using hM
    | succ k ih =>
      intro x
      rw [hB x, abs_mul, abs_of_nonneg hq0, pow_succ, mul_comm (q ^ k) q, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hE B _ ih x) hq0
  funext x
  have ht : Tendsto (fun k : ℕ => q ^ k * M) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const M
  have : |B x| ≤ 0 := ge_of_tendsto' ht fun k => hk k x
  simpa using abs_nonpos_iff.1 this

/-- O&R (12), p. 521: **uniqueness**: every state-dependent equilibrium equals the
Neumann-series solution (12) (on a finite chain every state-dependent solution is bounded). -/
theorem isMarkovEqm_unique {η : ℝ} (hη : 0 < η) (P : MarkovKernel S) {f p : S → ℝ}
    (hp : IsMarkovEqm η P f p) : p = markovFundamental η P f := by
  have hF := markovFundamental_isMarkovEqm hη P f
  set d : S → ℝ := fun s => p s - markovFundamental η P f s with hd
  have hB : ∀ s, d s = disc η * kernelApply P d s := by
    intro s
    have e := kernelApply_linear P 1 (-1) p (markovFundamental η P f) s
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at e
    change p s - markovFundamental η P f s =
      disc η * kernelApply P (fun x => p x - markovFundamental η P f x) s
    rw [e]
    linear_combination hp s - hF s
  have h0 := bubble_eq_zero_of_bounded (kernelApply P)
    (fun g M hg x => kernelApply_abs_le P hg x) (disc_pos hη).le (disc_lt_one hη) hB
    (abs_le_sum_abs d)
  funext s
  have := congrFun h0 s
  simp only [hd, Pi.zero_apply] at this
  linarith

/-- O&R (12), p. 521: existence and uniqueness of the stochastic no-bubble equilibrium. -/
theorem existsUnique_markovEqm {η : ℝ} (hη : 0 < η) (P : MarkovKernel S) (f : S → ℝ) :
    ∃! p : S → ℝ, IsMarkovEqm η P f p :=
  ⟨_, markovFundamental_isMarkovEqm hη P f, fun _ hp => isMarkovEqm_unique hη P hp⟩

/-- O&R (12), p. 521: the stochastic price level is monotone in the money process. -/
theorem markovFundamental_mono {η : ℝ} (hη : 0 < η) (P : MarkovKernel S) {f g : S → ℝ}
    (hfg : ∀ s, f s ≤ g s) (s : S) : markovFundamental η P f s ≤ markovFundamental η P g s := by
  have hmono : ∀ n x, kernelPow P n f x ≤ kernelPow P n g x := by
    intro n
    induction n with
    | zero => exact hfg
    | succ n ih => intro x; rw [kernelPow_succ, kernelPow_succ]; exact kernelApply_mono P ih x
  unfold markovFundamental
  refine mul_le_mul_of_nonneg_left ?_ (by have : 0 < 1 + η := by linarith
                                          positivity)
  exact (summable_markov hη P f s).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (hmono n s) (pow_pos (disc_pos hη) n).le)
    (summable_markov hη P g s)

/-- O&R (13)–(14), p. 521, Markov form: if money is an eigenfunction, `E_t m_{t+1} = ρ m_t`
(`K f = ρ f`, the analogue of the AR(1) (13)), with `ρ ≤ 1`, then
`p = m/(1 + η − ηρ)`. -/
theorem markovFundamental_eigen {η : ℝ} (hη : 0 < η) (P : MarkovKernel S) {f : S → ℝ}
    {ρ : ℝ} (hρ : ρ ≤ 1) (hK : ∀ s, kernelApply P f s = ρ * f s) (s : S) :
    markovFundamental η P f s = f s / (1 + η - η * ρ) := by
  have hD : 0 < 1 + η - η * ρ := by nlinarith
  have hcand : IsMarkovEqm η P f (fun x => f x / (1 + η - η * ρ)) := by
    intro x
    have e := kernelApply_linear P (1 / (1 + η - η * ρ)) 0 f (fun _ => 0) x
    simp only [zero_mul, add_zero] at e
    have e' : kernelApply P (fun x => f x / (1 + η - η * ρ)) x =
        1 / (1 + η - η * ρ) * kernelApply P f x := by
      rw [← e]; congr 1; funext y; ring
    rw [e', hK x]
    unfold disc
    field_simp
    ring
  rw [← isMarkovEqm_unique hη P hcand]

/-- O&R (14), p. 521: with permanent shocks (`ρ = 1`) the price level equals the money
supply. -/
theorem markovFundamental_eigen_one {η : ℝ} (hη : 0 < η) (P : MarkovKernel S) {f : S → ℝ}
    (hK : ∀ s, kernelApply P f s = f s) (s : S) : markovFundamental η P f s = f s := by
  rw [markovFundamental_eigen hη P le_rfl (fun x => by rw [hK x, one_mul]) s]
  field_simp; simp

/-- O&R (14), p. 521: the denominator `1 + η − ηρ` is at least one for `ρ ∈ [0, 1]`, so the
response of prices to money is at most one-for-one. -/
theorem one_le_eigen_denominator {η ρ : ℝ} (hη : 0 < η) (hρ : ρ ≤ 1) :
    1 ≤ 1 + η - η * ρ := by nlinarith

/-- O&R (13)–(14), p. 521: a concrete two-state chain (switch probability `π`). -/
def twoStateKernel (π : ℝ) (h0 : 0 ≤ π) (h1 : π ≤ 1) : MarkovKernel Bool where
  K s s' := if s = s' then 1 - π else π
  nonneg s s' := by split_ifs <;> linarith
  rowSum s := by cases s <;> simp

/-- O&R (13)–(14), p. 521: in the symmetric two-state chain with money `±1`, `E_t m_{t+1} =
(1 − 2π) m_t` and so `p = m/(1 + 2ηπ)`. -/
theorem twoState_price {η π : ℝ} (hη : 0 < η) (h0 : 0 ≤ π) (h1 : π ≤ 1) (s : Bool) :
    markovFundamental η (twoStateKernel π h0 h1) (fun b => if b then 1 else -1) s =
      (if s then 1 else -1) / (1 + 2 * η * π) := by
  rw [markovFundamental_eigen hη _ (ρ := 1 - 2 * π) (by linarith) ?_ s]
  · congr 1; ring
  · intro x
    unfold kernelApply twoStateKernel
    cases x <;> simp <;> ring

/-! ## Rational bubbles along an event tree -/

/-- O&R §8.2.3–8.2.4, pp. 520–521: nodes of the event tree: the current state and the list of
past states (most recent first). -/
abbrev TreeNode (S : Type) := S × List S

/-- O&R (4), p. 517: the conditional expectation at a node of a node-dependent variable
next period. -/
def treeExp (P : MarkovKernel S) (X : TreeNode S → ℝ) (n : TreeNode S) : ℝ :=
  ∑ s', P.K n.1 s' * X (s', n.1 :: n.2)

/-- O&R (4), p. 517: history-dependent equilibrium prices along the event tree,
`p_t = m_t/(1+η) + q E_t p_{t+1}`. -/
def IsTreeEqm (η : ℝ) (P : MarkovKernel S) (m p : TreeNode S → ℝ) : Prop :=
  ∀ n, p n = m n / (1 + η) + disc η * treeExp P p n

/-- O&R (4), p. 517: the tree expectation does not increase a sup bound. -/
theorem treeExp_abs_le (P : MarkovKernel S) {X : TreeNode S → ℝ} {M : ℝ}
    (hX : ∀ n, |X n| ≤ M) (n : TreeNode S) : |treeExp P X n| ≤ M :=
  kernelApply_abs_le P (g := fun s' => X (s', n.1 :: n.2)) (fun _ => hX _) n.1

/-- O&R (4), p. 517: the tree expectation is linear. -/
theorem treeExp_linear (P : MarkovKernel S) (a b : ℝ) (X Y : TreeNode S → ℝ) (n : TreeNode S) :
    treeExp P (fun k => a * X k + b * Y k) n = a * treeExp P X n + b * treeExp P Y n :=
  kernelApply_linear P a b (fun s' => X (s', n.1 :: n.2)) (fun s' => Y (s', n.1 :: n.2)) n.1

/-- O&R (4), p. 517: for a variable that depends only on the current state, the tree
expectation is the Markov expectation. -/
theorem treeExp_state (P : MarkovKernel S) (g : S → ℝ) (n : TreeNode S) :
    treeExp P (fun k => g k.1) n = kernelApply P g n.1 := rfl

/-- O&R (4), p. 517: the tree expectation of a constant is that constant. -/
theorem treeExp_const (P : MarkovKernel S) (c : ℝ) (n : TreeNode S) :
    treeExp P (fun _ => c) n = c := kernelApply_const P c n.1

/-- O&R (12), p. 521: the state-dependent fundamental is a tree equilibrium. -/
theorem markovFundamental_isTreeEqm {η : ℝ} (hη : 0 < η) (P : MarkovKernel S) (f : S → ℝ) :
    IsTreeEqm η P (fun n => f n.1) (fun n => markovFundamental η P f n.1) :=
  fun n => markovFundamental_isMarkovEqm hη P f n.1

/-- O&R (11)–(12), pp. 520–521: the difference of two tree equilibria (same money process)
is a bubble: `B = q E B`. -/
theorem treeEqm_sub_isBubble {η : ℝ} (P : MarkovKernel S) {m p p' : TreeNode S → ℝ}
    (hp : IsTreeEqm η P m p) (hp' : IsTreeEqm η P m p') (n : TreeNode S) :
    p n - p' n = disc η * treeExp P (fun k => p k - p' k) n := by
  have e := treeExp_linear P 1 (-1) p p' n
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at e
  rw [e, hp n, hp' n]; ring

/-- O&R (11)–(12), pp. 520–521: conversely, an equilibrium plus a bubble is an equilibrium. -/
theorem treeEqm_add_bubble {η : ℝ} (P : MarkovKernel S) {m p B : TreeNode S → ℝ}
    (hp : IsTreeEqm η P m p) (hB : ∀ n, B n = disc η * treeExp P B n) :
    IsTreeEqm η P m (fun n => p n + B n) := by
  intro n
  have e := treeExp_linear P 1 1 p B n
  simp only [one_mul] at e
  change p n + B n = m n / (1 + η) + disc η * treeExp P (fun k => p k + B k) n
  rw [e]
  linear_combination hp n + hB n

/-- O&R (11)–(12), pp. 520–521: **every** tree equilibrium with money `m_t = f(s_t)` is the
fundamental (12) plus a bubble `B` with `B_t = q E_t B_{t+1}`. -/
theorem treeEqm_iff_bubble {η : ℝ} (hη : 0 < η) (P : MarkovKernel S) (f : S → ℝ)
    (p : TreeNode S → ℝ) :
    IsTreeEqm η P (fun n => f n.1) p ↔
      ∀ n, p n - markovFundamental η P f n.1 =
        disc η * treeExp P (fun k => p k - markovFundamental η P f k.1) n := by
  constructor
  · intro hp n; exact treeEqm_sub_isBubble P hp (markovFundamental_isTreeEqm hη P f) n
  · intro hB
    have := treeEqm_add_bubble P (markovFundamental_isTreeEqm hη P f) hB
    simpa using this

/-- O&R (8), (12), pp. 518–521: two tree equilibria for the same money process whose
difference is bounded coincide (bounded bubbles vanish). -/
theorem treeEqm_unique_of_bounded {η : ℝ} (hη : 0 < η) (P : MarkovKernel S)
    {m p p' : TreeNode S → ℝ} (hp : IsTreeEqm η P m p) (hp' : IsTreeEqm η P m p') {M : ℝ}
    (hM : ∀ n, |p n - p' n| ≤ M) : p = p' := by
  have h0 := bubble_eq_zero_of_bounded (treeExp P) (fun g M hg x => treeExp_abs_le P hg x)
    (disc_pos hη).le (disc_lt_one hη) (treeEqm_sub_isBubble P hp hp') hM
  funext n
  have := congrFun h0 n
  simp only [Pi.zero_apply] at this
  linarith

/-- O&R (12), p. 521: the **bounded** tree equilibria are exactly the fundamental (12):
bounded price processes cannot contain bubbles. -/
theorem treeEqm_bounded_eq_fundamental {η : ℝ} (hη : 0 < η) (P : MarkovKernel S) (f : S → ℝ)
    {p : TreeNode S → ℝ} (hp : IsTreeEqm η P (fun n => f n.1) p) {M : ℝ}
    (hM : ∀ n, |p n| ≤ M) : p = fun n => markovFundamental η P f n.1 := by
  refine treeEqm_unique_of_bounded hη P hp (markovFundamental_isTreeEqm hη P f)
    (M := M + ∑ x, |markovFundamental η P f x|) fun n => ?_
  calc |p n - markovFundamental η P f n.1| ≤ |p n| + |markovFundamental η P f n.1| :=
        abs_sub _ _
    _ ≤ _ := add_le_add (hM n) (abs_le_sum_abs _ _)

/-- O&R (11), p. 520, stochastic form: a deterministic bubble `B = c((1+η)/η)^t` (with `t`
the date of the node) satisfies `B = q E B`. -/
theorem deterministic_bubble {η : ℝ} (hη : 0 < η) (P : MarkovKernel S) (c : ℝ)
    (n : TreeNode S) :
    c * ((1 + η) / η) ^ n.2.length =
      disc η * treeExp P (fun k => c * ((1 + η) / η) ^ k.2.length) n := by
  unfold treeExp
  simp only [List.length_cons]
  rw [← Finset.sum_mul, P.rowSum, one_mul, pow_succ]
  unfold disc
  field_simp

/-- O&R (11), p. 520, stochastic form: bubbles exist, so the stochastic equation alone does
not pin down prices: for every `c` the fundamental plus `c((1+η)/η)^t` is an equilibrium. -/
theorem treeEqm_with_deterministic_bubble {η : ℝ} (hη : 0 < η) (P : MarkovKernel S)
    (f : S → ℝ) (c : ℝ) :
    IsTreeEqm η P (fun n => f n.1)
      (fun n => markovFundamental η P f n.1 + c * ((1 + η) / η) ^ n.2.length) :=
  treeEqm_add_bubble P (markovFundamental_isTreeEqm hη P f) (deterministic_bubble hη P c)

/-! ## Seignorage -/

/-- O&R fn 13, p. 523: seignorage equals the change in real balances plus the inflation tax,
`(M_t − M_{t−1})/P_t = (M_t/P_t − M_{t−1}/P_{t−1}) + (M_{t−1}/P_{t−1} − M_{t−1}/P_t)`. -/
theorem seignorage_decomposition (M M' P P' : ℝ) :
    (M - M') / P = (M / P - M' / P') + (M' / P' - M' / P) := by ring

/-- O&R fn 13, p. 524: the inflation tax is the capital loss on real balances,
`M_{t−1}/P_{t−1} − M_{t−1}/P_t = ((P_t − P_{t−1})/P_t)(M_{t−1}/P_{t−1})`. -/
theorem inflation_tax_identity {M' P P' : ℝ} (hP : P ≠ 0) (hP' : P' ≠ 0) :
    M' / P' - M' / P = (P - P') / P * (M' / P') := by field_simp

/-- O&R (22), p. 524: seignorage as a function of the constant money growth rate,
`μ(1+μ)^{−η−1}`. -/
noncomputable def seignorage (η μ : ℝ) : ℝ := μ * (1 + μ) ^ (-η - 1)

/-- O&R (21)–(22), p. 524: on a constant-growth path, with `M_t = (1+μ)M_{t−1}` and real
balances `M_t/P_t = (P_{t+1}/P_t)^{−η} = (1+μ)^{−η}`, seignorage equals `μ(1+μ)^{−η−1}`. -/
theorem seignorage_constant_growth {η μ M M' P : ℝ} (hμ : -1 < μ) (hP : P ≠ 0)
    (hM : M = (1 + μ) * M') (hreal : M / P = (1 + μ) ^ (-η)) :
    (M - M') / P = seignorage η μ := by
  have h1 : (0 : ℝ) < 1 + μ := by linarith
  have hM' : M' = M / (1 + μ) := by field_simp; linarith
  unfold seignorage
  rw [Real.rpow_sub_one h1.ne', ← hreal, hM']
  field_simp
  ring

/-- O&R (22), p. 524: the derivative of seignorage,
`S′(μ) = (1+μ)^{−η−2}(1 − ημ)` for `μ > −1`. -/
theorem hasDerivAt_seignorage (η : ℝ) {μ : ℝ} (hμ : -1 < μ) :
    HasDerivAt (seignorage η) ((1 + μ) ^ (-η - 2) * (1 - η * μ)) μ := by
  have h1 : (0 : ℝ) < 1 + μ := by linarith
  have hd : HasDerivAt (fun x : ℝ => 1 + x) 1 μ := by
    simpa using (hasDerivAt_id μ).const_add 1
  have hr := hd.rpow_const (p := -η - 1) (Or.inl h1.ne')
  have hprod := (hasDerivAt_id' μ).mul hr
  unfold seignorage
  convert hprod using 1
  have e : (1 + μ) ^ (-η - 1) = (1 + μ) * (1 + μ) ^ (-η - 2) := by
    rw [show -η - 1 = (-η - 2) + 1 by ring, Real.rpow_add_one h1.ne']; ring
  rw [show -η - 1 - 1 = -η - 2 by ring, e]
  ring

/-- O&R (22)–(23), p. 524: seignorage is continuous on `(−1, ∞)`. -/
theorem continuousOn_seignorage (η : ℝ) : ContinuousOn (seignorage η) (Set.Ioi (-1)) :=
  fun _ hx => (hasDerivAt_seignorage η hx).continuousAt.continuousWithinAt

/-- O&R (23), p. 525: seignorage is strictly increasing on `(−1, 1/η]`. -/
theorem seignorage_strictMonoOn {η : ℝ} (hη : 0 < η) :
    StrictMonoOn (seignorage η) (Set.Ioc (-1) (1 / η)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioc _ _)
    ((continuousOn_seignorage η).mono Set.Ioc_subset_Ioi_self) fun x hx => ?_
  rw [interior_Ioc] at hx
  rw [(hasDerivAt_seignorage η hx.1).deriv]
  have h1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
  have h2 : η * x < 1 := by
    have := hx.2; rw [lt_div_iff₀ hη] at this; linarith
  exact mul_pos (Real.rpow_pos_of_pos h1 _) (by linarith)

/-- O&R (23), p. 525: seignorage is strictly decreasing on `[1/η, ∞)` (the wrong side of the
inflation Laffer curve). -/
theorem seignorage_strictAntiOn {η : ℝ} (hη : 0 < η) :
    StrictAntiOn (seignorage η) (Set.Ici (1 / η)) := by
  have hsub : Set.Ici (1 / η) ⊆ Set.Ioi (-1) := fun x hx => by
    have : (0 : ℝ) < 1 / η := by positivity
    simp only [Set.mem_Ici] at hx; simp only [Set.mem_Ioi]; linarith
  refine strictAntiOn_of_deriv_neg (convex_Ici _)
    ((continuousOn_seignorage η).mono hsub) fun x hx => ?_
  rw [interior_Ici] at hx
  have hx1 : -1 < x := hsub (Set.mem_Ici.2 (le_of_lt hx))
  rw [(hasDerivAt_seignorage η hx1).deriv]
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have h2 : 1 < η * x := by
    have := Set.mem_Ioi.1 hx; rw [div_lt_iff₀ hη] at this; linarith
  exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos h1 _) (by linarith)

/-- O&R (23), p. 525, sharpened: `μ^MAX = 1/η` is the unique **global** maximiser of
seignorage on `(−1, ∞)` (the book states only the first-order condition). -/
theorem seignorage_lt_max {η : ℝ} (hη : 0 < η) {μ : ℝ} (hμ : -1 < μ) (hne : μ ≠ 1 / η) :
    seignorage η μ < seignorage η (1 / η) := by
  have hpos : (0 : ℝ) < 1 / η := by positivity
  rcases lt_or_gt_of_ne hne with h | h
  · exact seignorage_strictMonoOn hη ⟨hμ, h.le⟩ ⟨by linarith, le_rfl⟩ h
  · exact seignorage_strictAntiOn hη (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h.le) h

/-- O&R (23), p. 525: the first-order condition: `S′(μ) = 0` iff `μ = 1/η`. -/
theorem seignorage_foc {η : ℝ} (hη : 0 < η) {μ : ℝ} (hμ : -1 < μ) :
    (1 + μ) ^ (-η - 2) * (1 - η * μ) = 0 ↔ μ = 1 / η := by
  have h1 : (0 : ℝ) < 1 + μ := by linarith
  rw [mul_eq_zero, or_iff_right (Real.rpow_pos_of_pos h1 _).ne', eq_div_iff hη.ne']
  constructor <;> intro h <;> linarith

/-- O&R p. 525: real balances at the revenue-maximising growth rate are
`[(1+η)/η]^{−η}`. -/
theorem real_balances_at_max {η : ℝ} (hη : 0 < η) :
    (1 + 1 / η) ^ (-η) = ((1 + η) / η) ^ (-η) := by
  congr 1; field_simp; ring

/-- O&R (22), p. 524: seignorage vanishes at zero money growth. -/
theorem seignorage_zero (η : ℝ) : seignorage η 0 = 0 := by simp [seignorage]

/-- O&R (22), p. 524: seignorage is positive for positive money growth. -/
theorem seignorage_pos {η μ : ℝ} (hμ : 0 < μ) : 0 < seignorage η μ :=
  mul_pos hμ (Real.rpow_pos_of_pos (by linarith) _)

/-- O&R p. 525 (the inflation Laffer curve): seignorage tends to zero as money growth tends to
infinity (for `η > 0`). -/
theorem seignorage_tendsto_zero {η : ℝ} (hη : 0 < η) :
    Tendsto (seignorage η) atTop (𝓝 0) := by
  have h1 : Tendsto (fun μ : ℝ => (1 + μ) ^ (-η)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hη).comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with μ hμ using (seignorage_pos hμ).le
  · filter_upwards [eventually_gt_atTop 0] with μ hμ
    have h2 : (0 : ℝ) < 1 + μ := by linarith
    unfold seignorage
    rw [show -η - 1 = -η - 1 by ring, Real.rpow_sub_one h2.ne']
    rw [mul_div_assoc', div_le_iff₀ h2]
    nlinarith [Real.rpow_pos_of_pos h2 (-η)]

/-- O&R §8.2.6, continuous-time analogue: seignorage `μ e^{−ημ}` has the unique global
maximiser `μ = 1/η` on `ℝ`. -/
theorem continuous_seignorage_lt_max {η : ℝ} (hη : 0 < η) {μ : ℝ} (hne : μ ≠ 1 / η) :
    μ * Real.exp (-η * μ) < 1 / η * Real.exp (-η * (1 / η)) := by
  -- `μ e^{−ημ} = (1/η)(ημ) e^{−ημ}` and `x e^{−x} < e^{−1}` for `x ≠ 1`
  have key : ∀ x : ℝ, x ≠ 1 → x * Real.exp (-x) < Real.exp (-1) := by
    intro x hx
    have h := Real.add_one_lt_exp (show x - 1 ≠ 0 by intro h; apply hx; linarith)
    have : x * Real.exp (-x) = x * Real.exp (-1) * Real.exp (-(x - 1)) := by
      rw [mul_assoc, ← Real.exp_add]; ring_nf
    rw [this]
    have hpos : 0 < Real.exp (-1) := Real.exp_pos _
    rw [Real.exp_neg (x - 1)]
    rw [mul_inv_lt_iff₀ (Real.exp_pos _)]
    nlinarith
  have h1 := key (η * μ) (by intro h; apply hne; field_simp; linarith)
  have e1 : μ * Real.exp (-η * μ) = 1 / η * (η * μ * Real.exp (-(η * μ))) := by
    field_simp
  have e2 : 1 / η * Real.exp (-η * (1 / η)) = 1 / η * Real.exp (-1) := by
    congr 2; field_simp
  rw [e1, e2]
  exact mul_lt_mul_of_pos_left h1 (by positivity)

/-! ## The monetary model of the exchange rate -/

/-- O&R (24), (26), (28), (29), pp. 526–528: the exchange-rate fundamentals
`k_t = m_t − φ y_t + η i*_{t+1} − p*_t`. -/
def exchangeFundamentals (η φ : ℝ) (m y istar pstar : ℕ → ℝ) (t : ℕ) : ℝ :=
  m t - φ * y t + η * istar (t + 1) - pstar t

/-- O&R (24)–(29), pp. 526–528: money demand (24), PPP (26) and (log) UIP (28) hold iff the
exchange rate satisfies the Cagan equation (29) in the fundamentals `k`, with `p` and `i`
then given by PPP and UIP. -/
theorem monetary_model_iff (η φ : ℝ) (m y istar pstar e p i : ℕ → ℝ) :
    ((∀ t, m t - p t = -η * i (t + 1) + φ * y t) ∧ (∀ t, p t = e t + pstar t) ∧
        ∀ t, i (t + 1) = istar (t + 1) + e (t + 1) - e t) ↔
      IsCaganPath η (exchangeFundamentals η φ m y istar pstar) e ∧
        (∀ t, p t = e t + pstar t) ∧ ∀ t, i (t + 1) = istar (t + 1) + e (t + 1) - e t := by
  constructor
  · rintro ⟨h24, h26, h28⟩
    refine ⟨fun t => ?_, h26, h28⟩
    unfold caganResidual exchangeFundamentals
    have := h24 t; rw [h26 t, h28 t] at this; linarith
  · rintro ⟨h29, h26, h28⟩
    refine ⟨fun t => ?_, h26, h28⟩
    have := h29 t
    unfold caganResidual exchangeFundamentals at this
    rw [h26 t, h28 t]; linarith

/-- O&R (30), p. 528: the unique no-bubble exchange rate is
`e_t = (1/(1+η)) Σ (η/(1+η))^{s−t} (m_s − φ y_s + η i*_{s+1} − p*_s)`. -/
theorem exchange_rate_existsUnique {η : ℝ} (hη : 0 < η) (φ : ℝ) (m y istar pstar : ℕ → ℝ)
    (hk : CaganSummable η (exchangeFundamentals η φ m y istar pstar)) :
    ∃! e : ℕ → ℝ, IsCaganPath η (exchangeFundamentals η φ m y istar pstar) e ∧
      Tendsto (fun T => disc η ^ T * e T) atTop (𝓝 0) :=
  existsUnique_noBubble hη hk

/-- O&R p. 528: comparative statics of (30): the no-bubble exchange rate rises with the paths
of home money and the foreign interest rate, and falls with the paths of home output
(`φ ≥ 0`) and the foreign price level. -/
theorem exchange_rate_comparative_statics {η φ : ℝ} (hη : 0 < η) (hφ : 0 ≤ φ)
    {m y istar pstar m' y' istar' pstar' : ℕ → ℝ}
    (hk : CaganSummable η (exchangeFundamentals η φ m y istar pstar))
    (hk' : CaganSummable η (exchangeFundamentals η φ m' y' istar' pstar'))
    (hm : ∀ t, m t ≤ m' t) (hy : ∀ t, y' t ≤ y t) (hi : ∀ t, istar t ≤ istar' t)
    (hp : ∀ t, pstar' t ≤ pstar t) (t : ℕ) :
    fundamental η (exchangeFundamentals η φ m y istar pstar) t ≤
      fundamental η (exchangeFundamentals η φ m' y' istar' pstar') t := by
  refine fundamental_mono hη hk hk' (fun s => ?_) t
  unfold exchangeFundamentals
  nlinarith [hm s, hy s, hi (s + 1), hp s, mul_le_mul_of_nonneg_left (hy s) hφ,
    mul_le_mul_of_nonneg_left (hi (s + 1)) hη.le]

/-- O&R (31)–(32), p. 529: the coefficient `ηρ/(1+η−ηρ)` with which money growth moves the
exchange rate. -/
noncomputable def magnification (η ρ : ℝ) : ℝ := η * ρ / (1 + η - η * ρ)

/-- O&R p. 529: the magnification coefficient is nonnegative for `ρ ∈ [0, 1]`. -/
theorem magnification_nonneg {η ρ : ℝ} (hη : 0 < η) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    0 ≤ magnification η ρ := by
  unfold magnification
  have : 0 < 1 + η - η * ρ := by nlinarith
  positivity

/-- O&R p. 529: the magnification coefficient is strictly increasing in the persistence `ρ`
of money growth on `[0, 1]`. -/
theorem magnification_strictMonoOn {η : ℝ} (hη : 0 < η) :
    StrictMonoOn (magnification η) (Set.Icc 0 1) := by
  intro a ha b hb hab
  unfold magnification
  have hA : 0 < 1 + η - η * a := by nlinarith [ha.2]
  have hB : 0 < 1 + η - η * b := by nlinarith [hb.2]
  rw [div_lt_div_iff₀ hA hB]
  nlinarith [mul_pos (mul_pos hη (show (0 : ℝ) < 1 + η by linarith)) (sub_pos.2 hab)]

/-- O&R p. 529: with permanent money-growth shocks (`ρ = 1`) the coefficient is `η`. -/
theorem magnification_one (η : ℝ) : magnification η 1 = η := by
  unfold magnification; simp

/-- O&R (31), p. 529, Markov form: the tree money process has increments `Δm_{t+1} =
g(s_{t+1})`, with `E_t Δm_{t+1} = ρ Δm_t` (`K g = ρ g`). Then `E_t m_{t+1} = m_t + ρ g(s_t)`. -/
theorem treeExp_money (P : MarkovKernel S) {m : TreeNode S → ℝ} {g : S → ℝ} {ρ : ℝ}
    (hm : ∀ s' n, m (s', n.1 :: n.2) = m n + g s') (hK : ∀ s, kernelApply P g s = ρ * g s)
    (n : TreeNode S) : treeExp P m n = m n + ρ * g n.1 := by
  have : treeExp P m n = kernelApply P (fun s' => m n + g s') n.1 := by
    unfold treeExp kernelApply; exact Finset.sum_congr rfl fun s' _ => by rw [hm]
  rw [this]
  have e := kernelApply_linear P (m n) 1 (fun _ => 1) g n.1
  simp only [mul_one, one_mul] at e
  rw [e, kernelApply_const, hK]; ring

/-- O&R (29), (31)–(32), p. 529: with persistent money growth (Markov form of (31)), the
exchange rate `e_t = m_t + (ηρ/(1+η−ηρ)) Δm_t` is an equilibrium of (29) (normalising
`ηi* − φy − p* = 0`). -/
theorem exchange_rate_persistent_growth {η : ℝ} (hη : 0 < η) (P : MarkovKernel S)
    {m : TreeNode S → ℝ} {g : S → ℝ} {ρ : ℝ} (hρ : ρ ≤ 1)
    (hm : ∀ s' n, m (s', n.1 :: n.2) = m n + g s') (hK : ∀ s, kernelApply P g s = ρ * g s) :
    IsTreeEqm η P m (fun n => m n + magnification η ρ * g n.1) := by
  intro n
  have hD : 0 < 1 + η - η * ρ := by nlinarith
  have e := treeExp_linear P 1 (magnification η ρ) m (fun k => g k.1) n
  simp only [one_mul] at e
  rw [e, treeExp_money P hm hK, treeExp_state, hK]
  unfold magnification disc
  field_simp
  ring

/-- O&R p. 529: in that equilibrium, expected depreciation is
`E_t e_{t+1} − e_t = ρ Δm_t/(1+η−ηρ)`. -/
theorem expected_depreciation_persistent_growth {η : ℝ} (hη : 0 < η) (P : MarkovKernel S)
    {m : TreeNode S → ℝ} {g : S → ℝ} {ρ : ℝ} (hρ : ρ ≤ 1)
    (hm : ∀ s' n, m (s', n.1 :: n.2) = m n + g s') (hK : ∀ s, kernelApply P g s = ρ * g s)
    (n : TreeNode S) :
    treeExp P (fun k => m k + magnification η ρ * g k.1) n - (m n + magnification η ρ * g n.1) =
      ρ * g n.1 / (1 + η - η * ρ) := by
  have hD : 0 < 1 + η - η * ρ := by nlinarith
  have e := treeExp_linear P 1 (magnification η ρ) m (fun k => g k.1) n
  simp only [one_mul] at e
  rw [e, treeExp_money P hm hK, treeExp_state, hK, eq_div_iff hD.ne']
  have hc : magnification η ρ * (1 + η - η * ρ) = η * ρ := by
    unfold magnification; field_simp
  linear_combination (g n.1 * (ρ - 1)) * hc

/-- O&R (30)–(32), p. 529: uniqueness: any equilibrium exchange rate whose deviation from
money is bounded coincides with `m_t + (ηρ/(1+η−ηρ))Δm_t`. -/
theorem exchange_rate_persistent_growth_unique {η : ℝ} (hη : 0 < η) (P : MarkovKernel S)
    {m e : TreeNode S → ℝ} {g : S → ℝ} {ρ : ℝ} (hρ : ρ ≤ 1)
    (hm : ∀ s' n, m (s', n.1 :: n.2) = m n + g s') (hK : ∀ s, kernelApply P g s = ρ * g s)
    (he : IsTreeEqm η P m e) {M : ℝ} (hM : ∀ n, |e n - m n| ≤ M) :
    e = fun n => m n + magnification η ρ * g n.1 := by
  refine treeEqm_unique_of_bounded hη P he (exchange_rate_persistent_growth hη P hρ hm hK)
    (M := M + |magnification η ρ| * ∑ x, |g x|) fun n => ?_
  calc |e n - (m n + magnification η ρ * g n.1)|
      = |(e n - m n) - magnification η ρ * g n.1| := by ring_nf
    _ ≤ |e n - m n| + |magnification η ρ * g n.1| := abs_sub _ _
    _ ≤ _ := by
        rw [abs_mul]
        exact add_le_add (hM n)
          (mul_le_mul_of_nonneg_left (abs_le_sum_abs g n.1) (abs_nonneg _))

/-- O&R (32), p. 529: the forward-sum form of expected depreciation,
`(1/(1+η)) Σ_j q^j E_t(m_{t+j+1} − m_{t+j}) = ρΔm_t/(1+η−ηρ)` when
`E_t Δm_{t+j+1} = ρ^{j+1} Δm_t`, `0 ≤ ρ ≤ 1`. -/
theorem expected_depreciation_forward_sum {η ρ : ℝ} (hη : 0 < η) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (dm : ℝ) :
    1 / (1 + η) * ∑' j : ℕ, disc η ^ j * (ρ ^ (j + 1) * dm) = ρ * dm / (1 + η - η * ρ) := by
  have hq := disc_pos hη
  have hqρ : disc η * ρ < 1 := by nlinarith [disc_lt_one hη]
  have e : (fun j : ℕ => disc η ^ j * (ρ ^ (j + 1) * dm)) =
      fun j => ρ * dm * (disc η * ρ) ^ j := by
    funext j; rw [mul_pow, pow_succ]; ring
  rw [e, tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hqρ]
  have hD : 0 < 1 + η - η * ρ := by nlinarith
  unfold disc
  field_simp

/-! ## Fixed exchange rates, crawling pegs and interest-rate pegs -/

/-- O&R (68), p. 554: under (68) a permanently fixed exchange rate `ē` requires the money
supply to be permanently fixed at `m̄ = ē`. -/
theorem fixed_rate_money {η : ℝ} {m e : ℕ → ℝ} {ebar : ℝ} (he : IsCaganPath η m e)
    (hfix : ∀ t, e t = ebar) (t : ℕ) : m t = ebar := by
  have := he t
  unfold caganResidual at this
  rw [hfix t, hfix (t + 1)] at this
  linarith

/-- O&R p. 555: conversely, with `m ≡ ē` the unique no-bubble exchange rate is `e ≡ ē`. -/
theorem fixed_money_rate {η : ℝ} (hη : 0 < η) {e : ℕ → ℝ} {ebar : ℝ}
    (he : IsCaganPath η (fun _ => ebar) e) (h8 : Tendsto (fun T => disc η ^ T * e T) atTop (𝓝 0))
    (t : ℕ) : e t = ebar := by
  rw [eq_fundamental_of_noBubble hη (caganSummable_of_bounded (A := |ebar|) hη fun _ => le_rfl)
    he h8, fundamental_const hη]

/-- O&R p. 556 (crawling peg): if `ē_{s+1} − ē_s = μ`, (68) forces `m_t = ē_t − ημ`, so
money also grows by `μ` per period. -/
theorem crawling_peg_money {η μ : ℝ} {m e : ℕ → ℝ} (he : IsCaganPath η m e)
    (hcrawl : ∀ t, e (t + 1) - e t = μ) (t : ℕ) :
    m t = e t - η * μ ∧ m (t + 1) - m t = μ := by
  have h1 := he t
  have h2 := he (t + 1)
  unfold caganResidual at h1 h2
  constructor
  · rw [hcrawl t] at h1; linarith
  · rw [hcrawl t] at h1; rw [hcrawl (t + 1)] at h2; linarith [hcrawl t]

/-- O&R p. 556 (crawling peg): uncovered interest parity then gives `i = i* + μ`. -/
theorem crawling_peg_interest {μ istar : ℝ} {e i : ℕ → ℝ}
    (huip : ∀ t, i (t + 1) = istar + e (t + 1) - e t) (hcrawl : ∀ t, e (t + 1) - e t = μ)
    (t : ℕ) : i (t + 1) = istar + μ := by
  rw [huip t]; linarith [hcrawl t]

/-- O&R fn 44, p. 556: an equilibrium under an interest-rate peg `i ≡ ī`: money demand
`m_t − e_t = −η i_t` and UIP `i_t = i* + e_{t+1} − e_t`. -/
def IsInterestPegEqm (η ibar istar : ℝ) (m e : ℕ → ℝ) : Prop :=
  (∀ t, m t - e t = -η * ibar) ∧ ∀ t, ibar = istar + e (t + 1) - e t

/-- O&R fn 44, p. 556 (**indeterminacy**): for every initial exchange rate `e₀` there is an
equilibrium under the interest-rate peg, `e_t = e₀ + (ī − i*)t`, `m_t = e_t − ηī`. -/
theorem interestPeg_eqm_exists (η ibar istar e₀ : ℝ) :
    IsInterestPegEqm η ibar istar (fun t => e₀ + (ibar - istar) * t - η * ibar)
      (fun t => e₀ + (ibar - istar) * t) := by
  constructor
  · intro t; ring
  · intro t; push_cast; ring

/-- O&R fn 44, p. 556: every interest-peg equilibrium belongs to that one-parameter family,
indexed by `e₀ = e_0`. -/
theorem interestPeg_eqm_form {η ibar istar : ℝ} {m e : ℕ → ℝ}
    (h : IsInterestPegEqm η ibar istar m e) (t : ℕ) :
    e t = e 0 + (ibar - istar) * t ∧ m t = e t - η * ibar := by
  refine ⟨?_, by linarith [h.1 t]⟩
  induction t with
  | zero => simp
  | succ n ih => have := h.2 n; push_cast; linarith

/-- O&R fn 44, p. 556: the indeterminacy is real: two different initial rates give two
different equilibria. -/
theorem interestPeg_indeterminate (η ibar istar : ℝ) {e₀ e₁ : ℝ} (hne : e₀ ≠ e₁) :
    ∃ m e m' e' : ℕ → ℝ, IsInterestPegEqm η ibar istar m e ∧
      IsInterestPegEqm η ibar istar m' e' ∧ e ≠ e' :=
  ⟨_, _, _, _, interestPeg_eqm_exists η ibar istar e₀, interestPeg_eqm_exists η ibar istar e₁,
    fun h => hne (by simpa using congrFun h 0)⟩

/-- O&R fn 44, p. 556: specifying the money supply at a single date `s` pins down the
interest-peg equilibrium uniquely. -/
theorem interestPeg_pinned {η ibar istar : ℝ} {m e m' e' : ℕ → ℝ}
    (h : IsInterestPegEqm η ibar istar m e) (h' : IsInterestPegEqm η ibar istar m' e') {s : ℕ}
    (hs : m s = m' s) : e = e' ∧ m = m' := by
  have hf := interestPeg_eqm_form h
  have hf' := interestPeg_eqm_form h'
  have h0 : e 0 = e' 0 := by
    have a := hf s; have b := hf' s
    linarith [a.1, a.2, b.1, b.2]
  have he : e = e' := funext fun t => by rw [(hf t).1, (hf' t).1, h0]
  refine ⟨he, funext fun t => ?_⟩
  rw [(hf t).2, (hf' t).2, he]

/-- O&R (78), p. 567: the two-country exchange-rate equation
`e_t = m_t − m*_t − φ(y_t − y*_t) + η(e_{t+1} − e_t)` (perfect foresight). -/
def IsTwoCountryEqm (η φ : ℝ) (m mstar y ystar e : ℕ → ℝ) : Prop :=
  ∀ t, e t = m t - mstar t - φ * (y t - ystar t) + η * (e (t + 1) - e t)

/-- O&R p. 567: given relative output, the exchange rate is fixed at `ē` iff relative money is
fixed at `m − m* = ē + φ(y − y*)`. -/
theorem twoCountry_fixed_iff {η φ : ℝ} {m mstar y ystar e : ℕ → ℝ} {ebar : ℝ}
    (he : IsTwoCountryEqm η φ m mstar y ystar e) (hfix : ∀ t, e t = ebar) (t : ℕ) :
    m t - mstar t = ebar + φ * (y t - ystar t) := by
  have := he t; rw [hfix t, hfix (t + 1)] at this; linarith

/-- O&R p. 567: conversely, **any** foreign money path can be accommodated: setting home money
`m = m* + φ(y − y*) + ē` supports the fixed rate `ē` for every path of `m*`, with no
reference to reserves (cooperating authorities can never run out of reserves). -/
theorem twoCountry_fixed_implementable (η φ ebar : ℝ) (mstar y ystar : ℕ → ℝ) :
    IsTwoCountryEqm η φ (fun t => mstar t + φ * (y t - ystar t) + ebar) mstar y ystar
      (fun _ => ebar) := by
  intro t; ring

/-! ## Exercise 1: future fixing of the exchange rate -/

/-- O&R Exercise 1, p. 599: the money path when money is exogenous up to `T − 1` and then held
at its date-`(T−1)` value. -/
def truncMoney (mexo : ℕ → ℝ) (T : ℕ) (t : ℕ) : ℝ := mexo (min t (T - 1))

/-- O&R Exercise 1, p. 599: an equilibrium under the future-fixing policy: money is exogenous
for `t ≤ T − 1`, (68) holds at every date, and from `T` on the exchange rate is fixed at the
rate that prevailed at `T − 1`. -/
def IsFutureFixEqm (η : ℝ) (T : ℕ) (mexo m e : ℕ → ℝ) : Prop :=
  (∀ t, t ≤ T - 1 → m t = mexo t) ∧ IsCaganPath η m e ∧ ∀ s, T ≤ s → e s = e (T - 1)

/-- O&R Exercise 1, p. 599: in any future-fixing equilibrium the "market-chosen" rate is
`e_{T−1} = m_{T−1}`, and from `T − 1` on money must stay at that value. -/
theorem futureFix_rate {η : ℝ} {T : ℕ} (hT : 1 ≤ T) {mexo m e : ℕ → ℝ}
    (h : IsFutureFixEqm η T mexo m e) :
    e (T - 1) = mexo (T - 1) ∧ ∀ s, T - 1 ≤ s → m s = mexo (T - 1) ∧ e s = mexo (T - 1) := by
  obtain ⟨hm, hc, hfix⟩ := h
  have hfix' : ∀ s, T - 1 ≤ s → e s = e (T - 1) := by
    intro s hs
    rcases Nat.eq_or_lt_of_le hs with h | h
    · rw [h]
    · exact hfix s (by omega)
  have hms : ∀ s, T - 1 ≤ s → m s = e (T - 1) := by
    intro s hs
    have := hc s
    unfold caganResidual at this
    rw [hfix' s hs, hfix' (s + 1) (by omega)] at this
    linarith
  have h1 : e (T - 1) = mexo (T - 1) := by rw [← hm (T - 1) le_rfl, hms (T - 1) le_rfl]
  exact ⟨h1, fun s hs => ⟨by rw [hms s hs, h1], by rw [hfix' s hs, h1]⟩⟩

/-- O&R Exercise 1, p. 599: the future-fixing policy is **coherent**: there is exactly one
equilibrium exchange-rate path, the fundamental (9) of the truncated money path (finite
backward induction, so no bubble condition is needed). -/
theorem futureFix_existsUnique {η : ℝ} (hη : 0 < η) {T : ℕ} (hT : 1 ≤ T) (mexo : ℕ → ℝ) :
    (∃ m, IsFutureFixEqm η T mexo m (fundamental η (truncMoney mexo T))) ∧
      ∀ m e, IsFutureFixEqm η T mexo m e → e = fundamental η (truncMoney mexo T) := by
  have hs : CaganSummable η (truncMoney mexo T) := by
    refine caganSummable_of_bounded (A := ∑ j ∈ Finset.range T, |mexo j|) hη fun s => ?_
    unfold truncMoney
    exact Finset.single_le_sum (f := fun j => |mexo j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega))
  have hconst : ∀ s, T - 1 ≤ s → fundamental η (truncMoney mexo T) s = mexo (T - 1) :=
    fun s hs => fundamental_eventually_const hη fun j => by
      unfold truncMoney; rw [min_eq_right (by omega)]
  constructor
  · refine ⟨truncMoney mexo T, fun t ht => by unfold truncMoney; rw [min_eq_left ht],
      fundamental_isCaganPath hη hs, fun s hs' => ?_⟩
    rw [hconst s (by omega), hconst (T - 1) le_rfl]
  · intro m e h
    have hr := futureFix_rate hT h
    have hc := (isCaganPath_iff hη m e).1 h.2.1
    have hF := fundamental_recursion hη hs
    funext t
    -- downward induction on `T − 1 − t`
    have aux : ∀ k t, T - 1 - t = k → e t = fundamental η (truncMoney mexo T) t := by
      intro k
      induction k with
      | zero =>
        intro t ht
        rw [(hr.2 t (by omega)).2, hconst t (by omega)]
      | succ k ih =>
        intro t ht
        rw [hc t, hF t, ih (t + 1) (by omega), h.1 t (by omega)]
        unfold truncMoney; rw [min_eq_left (by omega)]
    exact aux _ t rfl

/-- O&R Exercise 1 and fn 44, pp. 556, 599: if instead money at `T − 1` is allowed to
accommodate the market rate, the rule has no nominal anchor: **every** value `c` of `e_{T−1}`
is an equilibrium. -/
theorem futureFix_indeterminate_without_anchor {η : ℝ} (hη : 0 < η) {T : ℕ} (hT : 1 ≤ T)
    (mexo : ℕ → ℝ) (c : ℝ) :
    ∃ m e : ℕ → ℝ, (∀ t, t < T - 1 → m t = mexo t) ∧ IsCaganPath η m e ∧
      (∀ s, T ≤ s → e s = e (T - 1)) ∧ e (T - 1) = c := by
  obtain ⟨⟨m, hm⟩, -⟩ := futureFix_existsUnique hη hT (Function.update mexo (T - 1) c)
  refine ⟨m, _, fun t ht => ?_, hm.2.1, hm.2.2, ?_⟩
  · rw [hm.1 t (by omega), Function.update_of_ne (by omega)]
  · rw [(futureFix_rate hT hm).1, Function.update_self]

/-- O&R Exercise 1, p. 599, stochastic version: a future-fixing equilibrium on the event
tree. Money is exogenous at nodes of date `≤ T − 1`; from date `T` on the exchange rate at
every node equals its value at the parent node (so it is frozen at the date-`(T−1)` value
along each branch). -/
def IsStochFutureFixEqm (η : ℝ) (P : MarkovKernel S) (T : ℕ) (mexo m e : TreeNode S → ℝ) :
    Prop :=
  (∀ n : TreeNode S, n.2.length ≤ T - 1 → m n = mexo n) ∧ IsTreeEqm η P m e ∧
    ∀ (s' : S) (n : TreeNode S), T ≤ n.2.length + 1 → e (s', n.1 :: n.2) = e n

/-- O&R Exercise 1, p. 599, stochastic version: at every node of date `≥ T − 1` the
exchange rate equals the money supply (expected depreciation is zero there). -/
theorem stochFutureFix_rate_eq_money {η : ℝ} (hη : 0 < η) {P : MarkovKernel S} {T : ℕ}
    {mexo m e : TreeNode S → ℝ} (h : IsStochFutureFixEqm η P T mexo m e) (n : TreeNode S)
    (hn : T - 1 ≤ n.2.length) : e n = m n := by
  obtain ⟨-, hc, hfix⟩ := h
  have hE : treeExp P e n = e n := by
    have : treeExp P e n = treeExp P (fun _ => e n) n := by
      unfold treeExp; exact Finset.sum_congr rfl fun s' _ => by rw [hfix s' n (by omega)]
    rw [this, treeExp_const]
  have := hc n
  rw [hE] at this
  have h1 := one_sub_disc hη
  have hq : e n * (1 - disc η) = m n / (1 + η) := by linarith
  rw [h1] at hq
  have : (0 : ℝ) < 1 + η := by linarith
  field_simp at hq
  linarith

/-- O&R Exercise 1, p. 599, stochastic version: **uniqueness**: two future-fixing equilibria
with the same exogenous money process have the same exchange rate at every node. -/
theorem stochFutureFix_unique {η : ℝ} (hη : 0 < η) {P : MarkovKernel S} {T : ℕ} (hT : 1 ≤ T)
    {mexo m e m' e' : TreeNode S → ℝ} (h : IsStochFutureFixEqm η P T mexo m e)
    (h' : IsStochFutureFixEqm η P T mexo m' e') : e = e' := by
  -- nodes of date `≥ T − 1`, by induction on the date
  have up : ∀ d (n : TreeNode S), n.2.length = T - 1 + d → e n = e' n := by
    intro d
    induction d with
    | zero =>
      intro n hn
      rw [stochFutureFix_rate_eq_money hη h n (by omega),
        stochFutureFix_rate_eq_money hη h' n (by omega), h.1 n (by omega), h'.1 n (by omega)]
    | succ d ih =>
      rintro ⟨s', l⟩ hn
      match l, hn with
      | s :: past, hn =>
        simp only [List.length_cons] at hn
        have hp : T ≤ past.length + 1 := by omega
        rw [h.2.2 s' (s, past) hp, h'.2.2 s' (s, past) hp]
        exact ih (s, past) (by simp only; omega)
  -- nodes of date `< T − 1`, by downward induction
  have down : ∀ k (n : TreeNode S), n.2.length + k = T - 1 → e n = e' n := by
    intro k
    induction k with
    | zero => intro n hn; exact up 0 n (by omega)
    | succ k ih =>
      intro n hn
      have hE : treeExp P e n = treeExp P e' n := by
        unfold treeExp
        exact Finset.sum_congr rfl fun s' _ => by
          rw [ih (s', n.1 :: n.2) (by simp only [List.length_cons]; omega)]
      rw [h.2.1 n, h'.2.1 n, hE, h.1 n (by omega), h'.1 n (by omega)]
  funext n
  rcases le_or_gt (T - 1) n.2.length with hn | hn
  · exact up (n.2.length - (T - 1)) n (by omega)
  · exact down (T - 1 - n.2.length) n (by omega)

omit [Fintype S] in
/-- O&R Exercise 1, p. 599: the ancestor of a node at date `d` (for `d` at most the node's
date). -/
def treeAncestor (d : ℕ) (n : TreeNode S) : TreeNode S :=
  match (n.1 :: n.2).drop (n.2.length - d) with
  | x :: r => (x, r)
  | [] => n

omit [Fintype S] in
/-- O&R Exercise 1, p. 599: a node is its own ancestor at its own date. -/
theorem treeAncestor_self (n : TreeNode S) : treeAncestor n.2.length n = n := by
  unfold treeAncestor; simp

omit [Fintype S] in
/-- O&R Exercise 1, p. 599: a child has the same ancestor as its parent at any date up to
the parent's date. -/
theorem treeAncestor_child {d : ℕ} (s' : S) (n : TreeNode S) (hd : d ≤ n.2.length) :
    treeAncestor d (s', n.1 :: n.2) = treeAncestor d n := by
  unfold treeAncestor
  simp only [List.length_cons]
  rw [show n.2.length + 1 - d = (n.2.length - d) + 1 by omega, List.drop_succ_cons]
  cases hX : List.drop (n.2.length - d) (n.1 :: n.2) with
  | nil =>
    rw [List.drop_eq_nil_iff] at hX
    simp only [List.length_cons] at hX
    omega
  | cons x r => rfl

/-- O&R Exercise 1, p. 599: backward-induction values `k` periods before the fixing date. -/
noncomputable def futureFixValue (η : ℝ) (P : MarkovKernel S) (mexo : TreeNode S → ℝ) :
    ℕ → TreeNode S → ℝ
  | 0 => mexo
  | k + 1 => fun n => mexo n / (1 + η) + disc η * treeExp P (futureFixValue η P mexo k) n

/-- O&R Exercise 1, p. 599: the candidate exchange rate under future fixing: backward
induction before date `T − 1`, and the date-`(T−1)` money value of the ancestor afterwards. -/
noncomputable def futureFixRate (η : ℝ) (P : MarkovKernel S) (T : ℕ) (mexo : TreeNode S → ℝ)
    (n : TreeNode S) : ℝ :=
  if T - 1 ≤ n.2.length then mexo (treeAncestor (T - 1) n)
  else futureFixValue η P mexo (T - 1 - n.2.length) n

/-- O&R Exercise 1, p. 599, stochastic version: **existence**: the future-fixing policy is
coherent under uncertainty: the backward-induction rate is an equilibrium (money after
`T − 1` being set to the frozen exchange rate). -/
theorem stochFutureFix_exists {η : ℝ} (hη : 0 < η) (P : MarkovKernel S) {T : ℕ} (hT : 1 ≤ T)
    (mexo : TreeNode S → ℝ) :
    IsStochFutureFixEqm η P T mexo
      (fun n => if n.2.length ≤ T - 1 then mexo n else futureFixRate η P T mexo n)
      (futureFixRate η P T mexo) := by
  have hchild : ∀ (s' : S) (n : TreeNode S), T - 1 ≤ n.2.length →
      futureFixRate η P T mexo (s', n.1 :: n.2) = futureFixRate η P T mexo n := by
    intro s' n hn
    unfold futureFixRate
    rw [ite_eq_left (by simp only [List.length_cons]; omega), ite_eq_left hn,
      treeAncestor_child s' n hn]
  refine ⟨fun n hn => by simp only [ite_eq_left hn], fun n => ?_, fun s' n hn => hchild s' n
    (by omega)⟩
  rcases le_or_gt (T - 1) n.2.length with hn | hn
  · -- dates `≥ T − 1`: the rate is frozen and equals money
    have hE : treeExp P (futureFixRate η P T mexo) n = futureFixRate η P T mexo n := by
      have : treeExp P (futureFixRate η P T mexo) n =
          treeExp P (fun _ => futureFixRate η P T mexo n) n := by
        unfold treeExp; exact Finset.sum_congr rfl fun s' _ => by rw [hchild s' n hn]
      rw [this, treeExp_const]
    have hm : (if n.2.length ≤ T - 1 then mexo n else futureFixRate η P T mexo n) =
        futureFixRate η P T mexo n := by
      split_ifs with h
      · have hd : n.2.length = T - 1 := by omega
        unfold futureFixRate
        rw [ite_eq_left hn, ← hd, treeAncestor_self]
      · rfl
    simp only
    rw [hm, hE]
    linear_combination (futureFixRate η P T mexo n) * one_sub_disc hη
  · -- dates `< T − 1`: backward induction
    obtain ⟨k, hk⟩ : ∃ k, T - 1 - n.2.length = k + 1 := ⟨T - 2 - n.2.length, by omega⟩
    have hE : treeExp P (futureFixRate η P T mexo) n = treeExp P (futureFixValue η P mexo k) n := by
      unfold treeExp
      refine Finset.sum_congr rfl fun s' _ => ?_
      congr 1
      unfold futureFixRate
      simp only [List.length_cons]
      split_ifs with h
      · have hk0 : k = 0 := by omega
        have hd : n.2.length + 1 = T - 1 := by omega
        rw [hk0, ← hd]
        have := treeAncestor_self (s', n.1 :: n.2)
        simp only [List.length_cons] at this
        rw [this]; rfl
      · rw [show T - 1 - (n.2.length + 1) = k by omega]
    simp only [ite_eq_left hn.le]
    rw [hE]
    unfold futureFixRate
    rw [ite_eq_right (by omega), hk]
    rfl

/-! ## Arithmetic checks -/

/-- O&R p. 515: inflation of 50 percent per month compounds to `1.5^12 − 1 ≈ 128.75`, i.e.
about 12,875 percent a year ("almost 13,000 percent"). -/
theorem monthly_fifty_percent_annualised :
    (128.7 : ℝ) < (1.5 : ℝ) ^ 12 - 1 ∧ (1.5 : ℝ) ^ 12 - 1 < (128.8 : ℝ) := by
  constructor <;> norm_num

/-- O&R Box 8.1, p. 527: the verbal claims about the table: seignorage is below 1 percent of
GDP for every listed country except Sweden (1.52); above 2 percent of government spending for
the United States (2.19) and Germany (2.89); above 3 percent for Italy (3.11) and Sweden
(3.22). -/
theorem box_8_1_claims :
    ((0.31 : ℝ) < 1 ∧ (0.09 : ℝ) < 1 ∧ (-0.23 : ℝ) < 1 ∧ (0.56 : ℝ) < 1 ∧ (0.32 : ℝ) < 1 ∧
        (0.01 : ℝ) < 1 ∧ (0.44 : ℝ) < 1 ∧ (1 : ℝ) < 1.52) ∧
      ((2 : ℝ) < 2.19 ∧ (2 : ℝ) < 2.89) ∧ ((3 : ℝ) < 3.11 ∧ (3 : ℝ) < 3.22) := by
  norm_num

end ObstfeldRogoff.MoneyExchangeRates.CaganModel

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Cagan model in continuous time

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §8.2.5,
pp. 521–523.

* The continuous-time Cagan equation (15) `m − p = −η ṗ`, with `ṗ` a right derivative
  (fn 10) so that money may jump (announced policy changes).
* The fundamental solution (16) `p_t = (1/η)∫_t^∞ e^{−(s−t)/η} m_s ds` (with `b₀ = 0`) is
  continuous, has right derivative `(p_t − m_t)/η` everywhere and a two-sided derivative at
  every continuity point of `m` (fn 9, Leibniz rule).
* Every continuous solution on a half-line `[t₀, ∞)` is (16) plus `b₀ e^{t/η}` for a unique
  `b₀`; the no-bubble condition `e^{−t/η} p_t → 0` holds iff `b₀ = 0`, so (16) with `b₀ = 0`
  is the unique no-bubble solution; bubble paths have `|p_t| → ∞`.
* Neutrality (weights integrate to one), monotonicity, constant money, and (18)–(19) for
  constant money growth; the integration-by-parts form of (18) (fn 11) in general.
* The period-`h` model (17): its forward solution (with weights `(1+h/η)^{−(s−t)/h}`), the
  limit `h → 0` of the equation (17) is (15), the limit of the weights is `e^{−(s−t)/η}`, and
  the period-`h` no-bubble price level converges to (16) as `h → 0`.

Standing assumptions on money (`AdmissibleMoney`): measurable, locally integrable, and
growing at most like `e^{κs}` with `κ < 1/η` (the continuous-time analogue of fn 6).
-/

namespace ObstfeldRogoff.MoneyExchangeRates.CaganContinuous

open Filter Topology MeasureTheory Set

/-- O&R (16) and fn 6, pp. 518, 522: money paths for which the forward integral (16)
converges: measurable, locally integrable, and `|m_s| ≤ A e^{κ s}` for `s ≥ 0` with
`κ < 1/η`. -/
structure AdmissibleMoney (η : ℝ) (m : ℝ → ℝ) : Prop where
  meas : Measurable m
  locInt : ∀ a b : ℝ, IntervalIntegrable m volume a b
  growth : ∃ A κ : ℝ, κ < 1 / η ∧ ∀ s : ℝ, 0 ≤ s → |m s| ≤ A * Real.exp (κ * s)

/-- O&R (16), p. 522: the discounted money integrand `e^{−s/η} m_s`. -/
noncomputable def weighted (η : ℝ) (m : ℝ → ℝ) (s : ℝ) : ℝ := Real.exp (-s / η) * m s

/-- O&R (16), p. 522: the discounted integrand is locally integrable. -/
theorem weighted_intervalIntegrable {η : ℝ} {m : ℝ → ℝ} (hm : AdmissibleMoney η m)
    (a b : ℝ) : IntervalIntegrable (weighted η m) volume a b :=
  (hm.locInt a b).continuousOn_mul (by fun_prop)

/-- O&R (16), p. 522: the discounted integrand is measurable. -/
theorem weighted_measurable {η : ℝ} {m : ℝ → ℝ} (hm : AdmissibleMoney η m) :
    Measurable (weighted η m) :=
  (Real.continuous_exp.comp (continuous_id.neg.div_const η)).measurable.mul hm.meas

/-- O&R (16), p. 522: the discounted integrand is integrable on `(0, ∞)`. -/
theorem weighted_integrableOn_Ioi_zero {η : ℝ} {m : ℝ → ℝ}
    (hm : AdmissibleMoney η m) : IntegrableOn (weighted η m) (Ioi 0) := by
  obtain ⟨A, κ, hκ, hA⟩ := hm.growth
  have hneg : κ - 1 / η < 0 := by linarith
  have hint : IntegrableOn (fun s => A * Real.exp ((κ - 1 / η) * s)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi hneg 0).const_mul A
  refine Integrable.mono' hint (weighted_measurable hm).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 ≤ s := le_of_lt hs
  rw [Real.norm_eq_abs, weighted, abs_mul, Real.abs_exp]
  calc Real.exp (-s / η) * |m s| ≤ Real.exp (-s / η) * (A * Real.exp (κ * s)) :=
        mul_le_mul_of_nonneg_left (hA s hs0) (Real.exp_pos _).le
    _ = A * Real.exp ((κ - 1 / η) * s) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- O&R (16), p. 522: the discounted integrand is integrable on every half-line `(t, ∞)`. -/
theorem weighted_integrableOn_Ioi {η : ℝ} {m : ℝ → ℝ}
    (hm : AdmissibleMoney η m) (t : ℝ) : IntegrableOn (weighted η m) (Ioi t) := by
  have h0 := weighted_integrableOn_Ioi_zero hm
  rcases le_or_gt 0 t with ht | ht
  · exact h0.mono_set (Ioi_subset_Ioi ht)
  · have h1 : IntegrableOn (weighted η m) (Ioc t 0) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).1 (weighted_intervalIntegrable hm t 0)
    rw [← Ioc_union_Ioi_eq_Ioi ht.le]
    exact h1.union h0

/-- O&R (16), p. 522: the fundamental (no-bubble, `b₀ = 0`) price level
`p_t = (1/η) ∫_t^∞ e^{−(s−t)/η} m_s ds`. -/
noncomputable def contFundamental (η : ℝ) (m : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 / η * ∫ s in Ioi t, Real.exp (-(s - t) / η) * m s

/-- O&R (16), p. 522: `p_t = (1/η) e^{t/η} ∫_t^∞ e^{−s/η} m_s ds`. -/
theorem contFundamental_eq_exp_mul (η : ℝ) (m : ℝ → ℝ) (t : ℝ) :
    contFundamental η m t = 1 / η * Real.exp (t / η) * ∫ s in Ioi t, weighted η m s := by
  have h := integral_const_mul (μ := volume.restrict (Ioi t)) (Real.exp (t / η)) (weighted η m)
  unfold contFundamental
  rw [mul_assoc, ← h]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [weighted]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- O&R (16), p. 522: with a fixed base point, `∫_t^∞ e^{−s/η} m_s = I₀ − ∫_0^t e^{−s/η} m_s`
where `I₀ = ∫_0^∞ e^{−s/η} m_s`. -/
theorem integral_Ioi_weighted {η : ℝ} {m : ℝ → ℝ} (hm : AdmissibleMoney η m)
    (t : ℝ) :
    ∫ s in Ioi t, weighted η m s =
      (∫ s in Ioi 0, weighted η m s) - ∫ s in (0 : ℝ)..t, weighted η m s := by
  rw [← intervalIntegral.integral_interval_add_Ioi (weighted_integrableOn_Ioi_zero hm)
    (weighted_integrableOn_Ioi hm t)]
  ring

/-- O&R (16), p. 522: the representation of the fundamental with a fixed base point. -/
theorem contFundamental_eq {η : ℝ} {m : ℝ → ℝ} (hm : AdmissibleMoney η m)
    (t : ℝ) :
    contFundamental η m t = 1 / η * Real.exp (t / η) *
      ((∫ s in Ioi 0, weighted η m s) - ∫ s in (0 : ℝ)..t, weighted η m s) := by
  rw [contFundamental_eq_exp_mul, integral_Ioi_weighted hm]

/-- O&R fn 10, p. 522: the fundamental price level is continuous even when money jumps. -/
theorem contFundamental_continuous {η : ℝ} {m : ℝ → ℝ}
    (hm : AdmissibleMoney η m) : Continuous (contFundamental η m) := by
  have hc : Continuous fun t => ∫ s in (0 : ℝ)..t, weighted η m s :=
    intervalIntegral.continuous_primitive (weighted_intervalIntegrable hm) 0
  have : contFundamental η m = fun t => 1 / η * Real.exp (t / η) *
      ((∫ s in Ioi 0, weighted η m s) - ∫ s in (0 : ℝ)..t, weighted η m s) :=
    funext (contFundamental_eq hm)
  rw [this]
  fun_prop

/-- O&R fn 9–10, p. 522: at every point where money is right-continuous the fundamental has
right derivative `(p_t − m_t)/η`, i.e. it solves (15) with `ṗ` the right derivative. -/
theorem contFundamental_hasDerivWithinAt {η : ℝ} (hη : 0 < η) {m : ℝ → ℝ}
    (hm : AdmissibleMoney η m) {t : ℝ} (hrc : ContinuousWithinAt m (Ici t) t) :
    HasDerivWithinAt (contFundamental η m) ((contFundamental η m t - m t) / η) (Ici t) t := by
  have hwc : ContinuousWithinAt (weighted η m) (Ioi t) t :=
    ((Real.continuous_exp.comp (continuous_id.neg.div_const η)).continuousAt.continuousWithinAt
      ).mul (hrc.mono Ioi_subset_Ici_self)
  have hF : HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, weighted η m s) (weighted η m t)
      (Ici t) t :=
    intervalIntegral.integral_hasDerivWithinAt_right (weighted_intervalIntegrable hm 0 t)
      (weighted_measurable hm).stronglyMeasurable.stronglyMeasurableAtFilter hwc
  have hE : HasDerivWithinAt (fun u => 1 / η * Real.exp (u / η)) (1 / η * (Real.exp (t / η) *
      (1 / η))) (Ici t) t := by
    have := ((hasDerivAt_id t).div_const η).exp.const_mul (1 / η)
    simpa using this.hasDerivWithinAt
  have hprod := hE.mul ((hasDerivWithinAt_const t (Ici t)
    (∫ s in Ioi 0, weighted η m s)).sub hF)
  have heq : contFundamental η m = fun u => 1 / η * Real.exp (u / η) *
      ((∫ s in Ioi 0, weighted η m s) - ∫ s in (0 : ℝ)..u, weighted η m s) :=
    funext (contFundamental_eq hm)
  rw [heq]
  convert hprod using 1
  have h1 : Real.exp (-t / η) = (Real.exp (t / η))⁻¹ := by rw [neg_div, Real.exp_neg]
  simp only [Pi.sub_apply, weighted, h1]
  field_simp
  ring

/-- O&R fn 9, p. 522: at every continuity point of money the fundamental is differentiable with
`ṗ_t = (p_t − m_t)/η` (Leibniz rule). -/
theorem contFundamental_hasDerivAt {η : ℝ} (hη : 0 < η) {m : ℝ → ℝ}
    (hm : AdmissibleMoney η m) {t : ℝ} (hc : ContinuousAt m t) :
    HasDerivAt (contFundamental η m) ((contFundamental η m t - m t) / η) t := by
  have hwc : ContinuousAt (weighted η m) t :=
    (Real.continuous_exp.comp (continuous_id.neg.div_const η)).continuousAt.mul hc
  have hF : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, weighted η m s) (weighted η m t) t :=
    intervalIntegral.integral_hasDerivAt_right (weighted_intervalIntegrable hm 0 t)
      (weighted_measurable hm).stronglyMeasurable.stronglyMeasurableAtFilter hwc
  have hE : HasDerivAt (fun u => 1 / η * Real.exp (u / η)) (1 / η * (Real.exp (t / η) *
      (1 / η))) t := by
    simpa using ((hasDerivAt_id t).div_const η).exp.const_mul (1 / η)
  have hprod := hE.mul ((hasDerivAt_const t (∫ s in Ioi 0, weighted η m s)).sub hF)
  have heq : contFundamental η m = fun u => 1 / η * Real.exp (u / η) *
      ((∫ s in Ioi 0, weighted η m s) - ∫ s in (0 : ℝ)..u, weighted η m s) :=
    funext (contFundamental_eq hm)
  rw [heq]
  convert hprod using 1
  have h1 : Real.exp (-t / η) = (Real.exp (t / η))⁻¹ := by rw [neg_div, Real.exp_neg]
  simp only [Pi.sub_apply, weighted, h1]
  field_simp
  ring

/-- O&R (15), fn 10, pp. 521–522: `p` solves the continuous-time Cagan equation on the
half-line `[t₀, ∞)`: it is continuous there (no anticipated jumps) and at every `t ≥ t₀` its
right derivative is `(p_t − m_t)/η`. -/
def IsCaganSolOn (η : ℝ) (m p : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  ContinuousOn p (Ici t₀) ∧ ∀ t, t₀ ≤ t → HasDerivWithinAt p ((p t - m t) / η) (Ici t) t

/-- O&R (16), p. 522: the fundamental solves (15) on every half-line when money is
right-continuous. -/
theorem contFundamental_isSol {η : ℝ} (hη : 0 < η) {m : ℝ → ℝ} (hm : AdmissibleMoney η m)
    (hrc : ∀ t, ContinuousWithinAt m (Ici t) t) (t₀ : ℝ) :
    IsCaganSolOn η m (contFundamental η m) t₀ :=
  ⟨(contFundamental_continuous hm).continuousOn,
    fun t _ => contFundamental_hasDerivWithinAt hη hm (hrc t)⟩

/-- O&R (16), p. 522: the bubble term `b₀ e^{t/η}` solves the homogeneous equation. -/
theorem hasDerivAt_bubble {η : ℝ} (b t : ℝ) :
    HasDerivAt (fun u => b * Real.exp (u / η)) (b * Real.exp (t / η) / η) t := by
  have := (((hasDerivAt_id' t).div_const η).exp).const_mul b
  convert this using 1; ring

/-- O&R (16), p. 522: adding a bubble `b₀ e^{t/η}` to a solution gives a solution. -/
theorem isCaganSolOn_add_bubble {η : ℝ} {m p : ℝ → ℝ} {t₀ : ℝ} (hp : IsCaganSolOn η m p t₀)
    (b : ℝ) : IsCaganSolOn η m (fun t => p t + b * Real.exp (t / η)) t₀ := by
  refine ⟨hp.1.add (by fun_prop), fun t ht => ?_⟩
  have := (hp.2 t ht).add (hasDerivAt_bubble (η := η) b t).hasDerivWithinAt
  convert this using 1
  ring

/-- O&R (16), p. 522: **every** continuous solution of (15) on `[t₀, ∞)` is the fundamental
plus a bubble: `p_t = (16) + b₀ e^{t/η}` for all `t ≥ t₀`, with
`b₀ = (p_{t₀} − p^F_{t₀}) e^{−t₀/η}`. -/
theorem isCaganSolOn_eq_fundamental_add_bubble {η : ℝ} (hη : 0 < η) {m p : ℝ → ℝ}
    (hm : AdmissibleMoney η m) (hrc : ∀ t, ContinuousWithinAt m (Ici t) t) {t₀ : ℝ}
    (hp : IsCaganSolOn η m p t₀) (t : ℝ) (ht : t₀ ≤ t) :
    p t = contFundamental η m t +
      (p t₀ - contFundamental η m t₀) * Real.exp (-t₀ / η) * Real.exp (t / η) := by
  set F := contFundamental η m with hFdef
  set w : ℝ → ℝ := fun u => (p u - F u) * Real.exp (-u / η) with hw
  have hFsol := contFundamental_isSol hη hm hrc t₀
  have hwc : ContinuousOn w (Icc t₀ t) :=
    ((hp.1.sub hFsol.1).mul (by fun_prop)).mono Icc_subset_Ici_self
  have hwd : ∀ x ∈ Ico t₀ t, HasDerivWithinAt w 0 (Ici x) x := by
    intro x hx
    have hx0 : t₀ ≤ x := hx.1
    have h1 := (hp.2 x hx0).sub (hFsol.2 x hx0)
    have h2 : HasDerivAt (fun u => Real.exp (-u / η)) (Real.exp (-x / η) * (-1 / η)) x := by
      have := ((hasDerivAt_id x).neg.div_const η).exp
      simpa [neg_div] using this
    have h3 := h1.mul h2.hasDerivWithinAt
    convert h3 using 1
    simp only [Pi.sub_apply]
    field_simp
    ring
  have hconst := constant_of_has_deriv_right_zero hwc hwd t ⟨ht, le_rfl⟩
  simp only [hw] at hconst
  have he : Real.exp (-t / η) * Real.exp (t / η) = 1 := by rw [← Real.exp_add]; simp [neg_div]
  have key : p t - F t = (p t₀ - F t₀) * Real.exp (-t₀ / η) * Real.exp (t / η) := by
    rw [← hconst]
    linear_combination (-(p t - F t)) * he
  linarith

/-- O&R (16), p. 522: the characterisation of all solutions on `[t₀, ∞)`: `p` solves (15) iff
`p = (16) + b₀ e^{t/η}` on `[t₀, ∞)` for some `b₀` (necessarily unique). -/
theorem isCaganSolOn_iff {η : ℝ} (hη : 0 < η) {m p : ℝ → ℝ} (hm : AdmissibleMoney η m)
    (hrc : ∀ t, ContinuousWithinAt m (Ici t) t) (t₀ : ℝ) :
    IsCaganSolOn η m p t₀ ↔
      ∃ b : ℝ, ∀ t, t₀ ≤ t → p t = contFundamental η m t + b * Real.exp (t / η) := by
  constructor
  · intro hp
    exact ⟨_, fun t ht => isCaganSolOn_eq_fundamental_add_bubble hη hm hrc hp t ht⟩
  · rintro ⟨b, hb⟩
    have hq := isCaganSolOn_add_bubble (contFundamental_isSol hη hm hrc t₀) b
    refine ⟨hq.1.congr fun t ht => hb t ht, fun t ht => ?_⟩
    have := (hq.2 t ht).congr_of_mem (fun u hu => hb u (le_trans ht hu)) self_mem_Ici
    rw [hb t ht]; exact this

/-- O&R (16), p. 522: the bubble coefficient is unique. -/
theorem bubble_coeff_unique {η : ℝ} {m p : ℝ → ℝ} {t₀ b b' : ℝ}
    (hb : ∀ t, t₀ ≤ t → p t = contFundamental η m t + b * Real.exp (t / η))
    (hb' : ∀ t, t₀ ≤ t → p t = contFundamental η m t + b' * Real.exp (t / η)) : b = b' := by
  have := (hb t₀ le_rfl).symm.trans (hb' t₀ le_rfl)
  have hpos := Real.exp_pos (t₀ / η)
  have : (b - b') * Real.exp (t₀ / η) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

/-- O&R (16), p. 522: the discounted fundamental vanishes at infinity:
`e^{−t/η} p^F_t → 0` (the continuous-time no-bubble condition). -/
theorem contFundamental_noBubble {η : ℝ} {m : ℝ → ℝ} (hm : AdmissibleMoney η m) :
    Tendsto (fun t => Real.exp (-t / η) * contFundamental η m t) atTop (𝓝 0) := by
  have hI := intervalIntegral_tendsto_integral_Ioi (μ := volume) 0
    (weighted_integrableOn_Ioi_zero hm) tendsto_id
  have h1 := (tendsto_const_nhds (x := ∫ s in Ioi 0, weighted η m s)).sub hI
  rw [sub_self] at h1
  have h2 := h1.const_mul (1 / η)
  rw [mul_zero] at h2
  refine h2.congr fun t => ?_
  rw [contFundamental_eq hm]
  have he : Real.exp (-t / η) * Real.exp (t / η) = 1 := by rw [← Real.exp_add]; simp [neg_div]
  simp only [id]
  linear_combination (-(1 / η * ((∫ s in Ioi 0, weighted η m s) -
    ∫ s in (0 : ℝ)..t, weighted η m s))) * he

/-- O&R (16), p. 522: along a solution, `e^{−t/η} p_t` converges to the bubble coefficient. -/
theorem isCaganSolOn_discounted_tendsto {η : ℝ} (hη : 0 < η) {m p : ℝ → ℝ}
    (hm : AdmissibleMoney η m) (hrc : ∀ t, ContinuousWithinAt m (Ici t) t) {t₀ : ℝ}
    (hp : IsCaganSolOn η m p t₀) :
    Tendsto (fun t => Real.exp (-t / η) * p t) atTop
      (𝓝 ((p t₀ - contFundamental η m t₀) * Real.exp (-t₀ / η))) := by
  have h := (contFundamental_noBubble hm).add_const
    ((p t₀ - contFundamental η m t₀) * Real.exp (-t₀ / η))
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop t₀] with t ht
  rw [isCaganSolOn_eq_fundamental_add_bubble hη hm hrc hp t ht]
  have he : Real.exp (-t / η) * Real.exp (t / η) = 1 := by rw [← Real.exp_add]; simp [neg_div]
  linear_combination (-((p t₀ - contFundamental η m t₀) * Real.exp (-t₀ / η))) * he

/-- O&R (16), p. 522: a solution satisfies the no-bubble condition `e^{−t/η} p_t → 0` iff it
coincides with the fundamental on `[t₀, ∞)` (`b₀ = 0`). -/
theorem noBubble_iff_eq_fundamental {η : ℝ} (hη : 0 < η) {m p : ℝ → ℝ}
    (hm : AdmissibleMoney η m) (hrc : ∀ t, ContinuousWithinAt m (Ici t) t) {t₀ : ℝ}
    (hp : IsCaganSolOn η m p t₀) :
    Tendsto (fun t => Real.exp (-t / η) * p t) atTop (𝓝 0) ↔
      ∀ t, t₀ ≤ t → p t = contFundamental η m t := by
  have hlim := isCaganSolOn_discounted_tendsto hη hm hrc hp
  constructor
  · intro h t ht
    have hb := tendsto_nhds_unique hlim h
    have hb0 : p t₀ - contFundamental η m t₀ = 0 := by
      rcases mul_eq_zero.1 hb with h | h
      · exact h
      · exact absurd h (Real.exp_pos _).ne'
    rw [isCaganSolOn_eq_fundamental_add_bubble hη hm hrc hp t ht, hb0]; ring
  · intro h
    rw [h t₀ le_rfl, sub_self, zero_mul] at hlim
    exact hlim

/-- O&R (16), p. 522: **existence and uniqueness**: on every half-line `[t₀, ∞)` the
fundamental is the unique solution of (15) satisfying the no-bubble condition. -/
theorem existsUnique_noBubble {η : ℝ} (hη : 0 < η) {m : ℝ → ℝ} (hm : AdmissibleMoney η m)
    (hrc : ∀ t, ContinuousWithinAt m (Ici t) t) (t₀ : ℝ) :
    (IsCaganSolOn η m (contFundamental η m) t₀ ∧
        Tendsto (fun t => Real.exp (-t / η) * contFundamental η m t) atTop (𝓝 0)) ∧
      ∀ p, IsCaganSolOn η m p t₀ → Tendsto (fun t => Real.exp (-t / η) * p t) atTop (𝓝 0) →
        ∀ t, t₀ ≤ t → p t = contFundamental η m t :=
  ⟨⟨contFundamental_isSol hη hm hrc t₀, contFundamental_noBubble hm⟩,
    fun _ hp h => (noBubble_iff_eq_fundamental hη hm hrc hp).1 h⟩

/-- O&R (16), p. 522: a solution with a bubble (`p_{t₀} ≠ p^F_{t₀}`) explodes:
`|p_t| → ∞`. -/
theorem bubble_abs_tendsto_atTop {η : ℝ} (hη : 0 < η) {m p : ℝ → ℝ}
    (hm : AdmissibleMoney η m) (hrc : ∀ t, ContinuousWithinAt m (Ici t) t) {t₀ : ℝ}
    (hp : IsCaganSolOn η m p t₀) (hb : p t₀ ≠ contFundamental η m t₀) :
    Tendsto (fun t => |p t|) atTop atTop := by
  have hlim := (isCaganSolOn_discounted_tendsto hη hm hrc hp).abs
  have hpos : 0 < |(p t₀ - contFundamental η m t₀) * Real.exp (-t₀ / η)| :=
    abs_pos.2 (mul_ne_zero (sub_ne_zero.2 hb) (Real.exp_pos _).ne')
  have hexp : Tendsto (fun t => Real.exp (t / η)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const hη)
  have h3 := hlim.pos_mul_atTop hpos hexp
  refine h3.congr fun t => ?_
  have he : Real.exp (-t / η) * Real.exp (t / η) = 1 := by rw [← Real.exp_add]; simp [neg_div]
  rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm, ← mul_assoc, mul_comm (Real.exp _), he,
    one_mul]

/-! ## Examples: constant money, constant money growth, integration by parts -/

/-- O&R (18), p. 523: the discounted time trend vanishes: `e^{−t/η}(a + b t) → 0`. -/
theorem tendsto_exp_neg_mul_affine {η : ℝ} (hη : 0 < η) (a b : ℝ) :
    Tendsto (fun t => Real.exp (-t / η) * (a + b * t)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t => Real.exp (-t / η)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const hη)
    refine this.congr fun t => ?_; simp [neg_div]
  have h2 : Tendsto (fun t => (t / η) * Real.exp (-(t / η))) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.atTop_div_const hη)
    refine this.congr fun t => ?_
    simp
  have h3 := (h1.const_mul a).add (h2.const_mul (b * η))
  simp only [mul_zero, add_zero] at h3
  refine h3.congr fun t => ?_
  rw [neg_div]
  field_simp

/-- O&R (18), p. 523: an affine money path `m_s = m₀ + μ s` is admissible. -/
theorem admissible_affine {η : ℝ} (hη : 0 < η) (m₀ μ : ℝ) :
    AdmissibleMoney η (fun s => m₀ + μ * s) := by
  refine ⟨by fun_prop, fun a b => (by fun_prop : Continuous fun s : ℝ => m₀ + μ * s)
    |>.intervalIntegrable a b, ⟨|m₀| + 2 * η * |μ|, 1 / (2 * η), ?_, fun s hs => ?_⟩⟩
  · rw [div_lt_div_iff₀ (by positivity) hη]; linarith
  · have h1 : 1 ≤ Real.exp (1 / (2 * η) * s) := Real.one_le_exp (by positivity)
    have h2 : 1 / (2 * η) * s + 1 ≤ Real.exp (1 / (2 * η) * s) := Real.add_one_le_exp _
    have h3 : s ≤ 2 * η * Real.exp (1 / (2 * η) * s) := by
      have : s = 2 * η * (1 / (2 * η) * s) := by field_simp
      nlinarith
    calc |m₀ + μ * s| ≤ |m₀| + |μ| * s := by
          calc |m₀ + μ * s| ≤ |m₀| + |μ * s| := abs_add_le _ _
            _ = |m₀| + |μ| * s := by rw [abs_mul, abs_of_nonneg hs]
      _ ≤ |m₀| * Real.exp (1 / (2 * η) * s) + |μ| * (2 * η * Real.exp (1 / (2 * η) * s)) :=
          add_le_add (le_mul_of_one_le_right (abs_nonneg _) h1)
            (mul_le_mul_of_nonneg_left h3 (abs_nonneg _))
      _ = (|m₀| + 2 * η * |μ|) * Real.exp (1 / (2 * η) * s) := by ring

/-- O&R (18), p. 523: with constant money growth `ṁ = μ` (`m_s = m₀ + μ s`), the
fundamental price level is `p_t = m_t + ημ`. -/
theorem contFundamental_affine {η : ℝ} (hη : 0 < η) (m₀ μ t : ℝ) :
    contFundamental η (fun s => m₀ + μ * s) t = m₀ + μ * t + η * μ := by
  have hm := admissible_affine hη m₀ μ
  have hrc : ∀ u, ContinuousWithinAt (fun s => m₀ + μ * s) (Ici u) u :=
    fun u => (by fun_prop : Continuous fun s : ℝ => m₀ + μ * s).continuousWithinAt
  have hsol : IsCaganSolOn η (fun s => m₀ + μ * s) (fun s => m₀ + μ * s + η * μ) t := by
    refine ⟨by fun_prop, fun u _ => ?_⟩
    have : HasDerivAt (fun s => m₀ + μ * s + η * μ) μ u := by
      simpa using (((hasDerivAt_id u).const_mul μ).const_add m₀).add_const (η * μ)
    convert this.hasDerivWithinAt using 1
    field_simp; ring
  have hnb : Tendsto (fun s => Real.exp (-s / η) * (m₀ + μ * s + η * μ)) atTop (𝓝 0) := by
    have := tendsto_exp_neg_mul_affine hη (m₀ + η * μ) μ
    refine this.congr fun s => by ring
  exact ((noBubble_iff_eq_fundamental hη hm hrc hsol).1 hnb t le_rfl).symm

/-- O&R (19), p. 523: with constant money growth, every solution on `[0, ∞)` is
`p_t = m_t + ημ + b₀ e^{t/η}` with `b₀ = p₀ − m₀ − ημ`. -/
theorem affine_general_solution {η : ℝ} (hη : 0 < η) {m₀ μ : ℝ} {p : ℝ → ℝ}
    (hp : IsCaganSolOn η (fun s => m₀ + μ * s) p 0) (t : ℝ) (ht : 0 ≤ t) :
    p t = m₀ + μ * t + η * μ + (p 0 - m₀ - η * μ) * Real.exp (t / η) := by
  have hrc : ∀ u, ContinuousWithinAt (fun s => m₀ + μ * s) (Ici u) u :=
    fun u => (by fun_prop : Continuous fun s : ℝ => m₀ + μ * s).continuousWithinAt
  rw [isCaganSolOn_eq_fundamental_add_bubble hη (admissible_affine hη m₀ μ) hrc hp t ht,
    contFundamental_affine hη, contFundamental_affine hη]
  simp only [mul_zero, add_zero, neg_zero, zero_div, Real.exp_zero, mul_one]
  ring

/-- O&R p. 519 and (16): a constant money supply `m̄` gives the constant price level `m̄`. -/
theorem contFundamental_const {η : ℝ} (hη : 0 < η) (c t : ℝ) :
    contFundamental η (fun _ => c) t = c := by
  have := contFundamental_affine hη c 0 t
  simpa using this

/-- O&R (16), p. 522 (neutrality): the weights `(1/η) e^{−(s−t)/η}` integrate to one over
`[t, ∞)`. -/
theorem weights_integrate_to_one {η : ℝ} (hη : 0 < η) (t : ℝ) :
    1 / η * ∫ s in Ioi t, Real.exp (-(s - t) / η) = 1 := by
  have := contFundamental_const hη 1 t
  unfold contFundamental at this
  simpa using this

/-- O&R (16), p. 522: the forward integrand `e^{−(s−t)/η} m_s` is integrable on `(t, ∞)`. -/
theorem integrableOn_forward {η : ℝ} {m : ℝ → ℝ} (hm : AdmissibleMoney η m) (t : ℝ) :
    IntegrableOn (fun s => Real.exp (-(s - t) / η) * m s) (Ioi t) := by
  have := (weighted_integrableOn_Ioi hm t).const_mul (Real.exp (t / η))
  refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
  simp only [weighted]
  rw [← mul_assoc, ← Real.exp_add]; congr 2; ring

/-- O&R p. 519 and (16) (**neutrality**): adding a constant to the money path adds it to the
price level. -/
theorem contFundamental_add_const {η : ℝ} (hη : 0 < η) {m : ℝ → ℝ}
    (hm : AdmissibleMoney η m) (c t : ℝ) :
    contFundamental η (fun s => m s + c) t = contFundamental η m t + c := by
  have hc := contFundamental_const hη c t
  have h1 := integrableOn_forward hm t
  have h2 := integrableOn_forward (admissible_affine hη c 0) t
  simp only [zero_mul, add_zero] at h2
  unfold contFundamental at hc ⊢
  simp_rw [mul_add]
  rw [integral_add h1 h2, mul_add, hc]

/-- O&R (16), p. 522: the price level is monotone in the money path. -/
theorem contFundamental_mono {η : ℝ} (hη : 0 < η) {m m' : ℝ → ℝ} (hm : AdmissibleMoney η m)
    (hm' : AdmissibleMoney η m') (hle : ∀ s, m s ≤ m' s) (t : ℝ) :
    contFundamental η m t ≤ contFundamental η m' t := by
  unfold contFundamental
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact setIntegral_mono_on (integrableOn_forward hm t) (integrableOn_forward hm' t)
    measurableSet_Ioi fun s _ => mul_le_mul_of_nonneg_left (hle s) (Real.exp_pos _).le

/-- O&R (18) and fn 11, p. 523 (integration by parts): if money is differentiable with an
admissible right-continuous derivative `ṁ`, then
`p_t = m_t + ∫_t^∞ e^{−(s−t)/η} ṁ_s ds`. -/
theorem contFundamental_integration_by_parts {η : ℝ} (hη : 0 < η) {m dm : ℝ → ℝ}
    (hm : AdmissibleMoney η m) (hdm : AdmissibleMoney η dm) (hd : ∀ t, HasDerivAt m (dm t) t)
    (hdrc : ∀ t, ContinuousWithinAt dm (Ici t) t) (t : ℝ) :
    contFundamental η m t = m t + ∫ s in Ioi t, Real.exp (-(s - t) / η) * dm s := by
  have hmc : Continuous m := continuous_iff_continuousAt.2 fun u => (hd u).continuousAt
  have hrc : ∀ u, ContinuousWithinAt m (Ici u) u := fun u => hmc.continuousWithinAt
  set q : ℝ → ℝ := fun u => m u + η * contFundamental η dm u with hq
  have hqe : ∀ u, q u = m u + ∫ s in Ioi u, Real.exp (-(s - u) / η) * dm s := by
    intro u; simp only [hq, contFundamental]; field_simp
  have hsol : IsCaganSolOn η m q t := by
    refine ⟨(hmc.add ((contFundamental_continuous hdm).const_smul η)).continuousOn,
      fun u _ => ?_⟩
    have := (hd u).hasDerivWithinAt.add
      ((contFundamental_hasDerivWithinAt hη hdm (hdrc u)).const_mul η)
    convert this using 1
    simp only [hq]; field_simp; ring
  have hnb : Tendsto (fun u => Real.exp (-u / η) * q u) atTop (𝓝 0) := by
    obtain ⟨A, κ, hκ, hA⟩ := hm.growth
    have hneg : κ - 1 / η < 0 := by linarith
    have h1 : Tendsto (fun u => A * Real.exp ((κ - 1 / η) * u)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg hneg)).const_mul A
      simpa using this
    have h2 : Tendsto (fun u => Real.exp (-u / η) * m u) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ h1
      filter_upwards [eventually_ge_atTop 0] with u hu
      rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
      calc Real.exp (-u / η) * |m u| ≤ Real.exp (-u / η) * (A * Real.exp (κ * u)) :=
            mul_le_mul_of_nonneg_left (hA u hu) (Real.exp_pos _).le
        _ = A * Real.exp ((κ - 1 / η) * u) := by
            rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
    have h3 := h2.add ((contFundamental_noBubble hdm).const_mul η)
    simp only [mul_zero, add_zero] at h3
    refine h3.congr fun u => ?_
    simp only [hq]; ring
  rw [← hqe t]
  exact ((noBubble_iff_eq_fundamental hη hm hrc hsol).1 hnb t le_rfl).symm

/-! ## The period-`h` model (17) and the limit `h → 0` -/

/-- O&R (17), p. 522: along the grid `t, t+h, t+2h, …` the period-`h` Cagan equation
`m − p = −(η/h)(p_{t+h} − p_t)` is the discrete Cagan model (5) with semielasticity `η/h`. -/
theorem periodH_iff {η h : ℝ} (m p : ℝ → ℝ) (t : ℝ) :
    (∀ j : ℕ, m (t + j * h) - p (t + j * h) =
        -(η / h) * (p (t + ((j + 1 : ℕ) : ℝ) * h) - p (t + j * h))) ↔
      CaganModel.IsCaganPath (η / h) (fun j : ℕ => m (t + j * h))
        (fun j : ℕ => p (t + j * h)) := by
  unfold CaganModel.IsCaganPath caganResidual
  refine forall_congr' fun j => ?_
  constructor <;> intro H <;> linarith

/-- O&R p. 522: the period-`h` discount factor is `(η/h)/(1+η/h) = (1 + h/η)^{−1}`. -/
theorem periodH_disc {η h : ℝ} (hη : 0 < η) (hh : 0 < h) :
    CaganModel.disc (η / h) = (1 + h / η)⁻¹ := by
  unfold CaganModel.disc; field_simp; ring

/-- O&R p. 522: the period-`h` scale factor is `1/(1 + η/h) = h/(h + η)`. -/
theorem periodH_scale {η h : ℝ} (hη : 0 < η) (hh : 0 < h) : 1 / (1 + η / h) = h / (h + η) := by
  field_simp

/-- O&R p. 522: period-`h` bubbles grow by the factor `1 + h/η` per period, i.e. like
`b₀(1 + h/η)^{t/h}`. -/
theorem periodH_bubble_factor {η h : ℝ} (hη : 0 < η) (hh : 0 < h) :
    (CaganModel.disc (η / h))⁻¹ = 1 + h / η := by
  rw [periodH_disc hη hh, inv_inv]

/-- O&R p. 522: the period-`h` no-bubble price level
`p_t = (1/(h+η)) Σ_{s=t,t+h,…} (1 + h/η)^{−(s−t)/h} m_s h`. -/
noncomputable def periodHPrice (η h : ℝ) (m : ℝ → ℝ) (t : ℝ) : ℝ :=
  h / (h + η) * ∑' j : ℕ, (1 + h / η)⁻¹ ^ j * m (t + j * h)

/-- O&R p. 522: the period-`h` no-bubble price level is the discrete fundamental (9) with
semielasticity `η/h`. -/
theorem periodHPrice_eq_fundamental {η h : ℝ} (hη : 0 < η) (hh : 0 < h) (m : ℝ → ℝ)
    (t : ℝ) :
    periodHPrice η h m t = CaganModel.fundamental (η / h) (fun j : ℕ => m (t + j * h)) 0 := by
  unfold periodHPrice CaganModel.fundamental
  rw [periodH_disc hη hh, periodH_scale hη hh]
  simp

/-- O&R (17), p. 522: a solution of the period-`h` equation along the grid that satisfies the
period-`h` no-bubble condition equals the period-`h` forward solution. -/
theorem periodH_solution_eq {η h : ℝ} (hη : 0 < η) (hh : 0 < h) {m p : ℝ → ℝ} {t : ℝ}
    (hsum : CaganModel.CaganSummable (η / h) (fun j : ℕ => m (t + j * h)))
    (hp : ∀ j : ℕ, m (t + j * h) - p (t + j * h) =
        -(η / h) * (p (t + ((j + 1 : ℕ) : ℝ) * h) - p (t + j * h)))
    (hnb : Tendsto (fun T : ℕ => CaganModel.disc (η / h) ^ T * p (t + T * h)) atTop (𝓝 0)) :
    p t = periodHPrice η h m t := by
  have hηh : 0 < η / h := div_pos hη hh
  have := CaganModel.eq_fundamental_of_noBubble hηh hsum ((periodH_iff m p t).1 hp) hnb
  have h0 := congrFun this 0
  simp only [Nat.cast_zero, zero_mul, add_zero] at h0
  rw [h0, periodHPrice_eq_fundamental hη hh]

/-- O&R (15), (17) and fn 10, p. 522: letting `h → 0` in the period-`h` equation gives the
continuous-time equation: `(η/h)(p_{t+h} − p_t) → η ṗ_t` with `ṗ` the right derivative. -/
theorem periodH_equation_limit {η : ℝ} {p : ℝ → ℝ} {t d : ℝ}
    (hd : HasDerivWithinAt p d (Ici t) t) :
    Tendsto (fun h => η / h * (p (t + h) - p t)) (𝓝[>] 0) (𝓝 (η * d)) := by
  have h1 := (hasDerivWithinAt_iff_tendsto_slope.1 hd)
  rw [Ici_sdiff_left] at h1
  have h2 : Tendsto (fun h : ℝ => t + h) (𝓝[>] 0) (𝓝[>] t) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 (t + 0)) :=
        tendsto_const_nhds.add tendsto_id
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [mem_Ioi] at hh ⊢; linarith
  have h3 := (h1.comp h2).const_mul η
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [Function.comp, slope_def_field]
  rw [add_sub_cancel_left]
  ring

/-- O&R p. 522: the period-`h` weights converge to the continuous-time weights:
`(1 + h/η)^{−u/h} → e^{−u/η}` as `h → 0⁺`. -/
theorem periodH_weight_limit {η : ℝ} (hη : 0 < η) (u : ℝ) :
    Tendsto (fun h => (1 + h / η) ^ (-u / h)) (𝓝[>] 0) (𝓝 (Real.exp (-u / η))) := by
  have h1 : Tendsto (fun x : ℝ => (1 + (1 / η) / x) ^ x) atTop (𝓝 (Real.exp (1 / η))) :=
    Real.tendsto_one_add_div_rpow_exp (1 / η)
  have h2 := h1.comp tendsto_inv_nhdsGT_zero
  have h3 : ContinuousAt (fun y : ℝ => y ^ (-u)) (Real.exp (1 / η)) :=
    Real.continuousAt_rpow_const _ _ (Or.inl (Real.exp_pos _).ne')
  have h4 := h3.tendsto.comp h2
  rw [← Real.exp_mul] at h4
  have e : 1 / η * -u = -u / η := by ring
  rw [e] at h4
  refine h4.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [mem_Ioi] at hh
  simp only [Function.comp]
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  · field_simp
  · field_simp

/-- O&R p. 522: the grid index `⌈(s − t)/h⌉ − 1` of the period containing `s`. -/
noncomputable def stepIndex (t h s : ℝ) : ℕ := ⌈(s - t) / h⌉₊ - 1

/-- O&R p. 522: on `(t + jh, t + (j+1)h]` the grid index is `j`. -/
theorem stepIndex_eq {t h : ℝ} (hh : 0 < h) {j : ℕ} {s : ℝ}
    (hs : s ∈ Ioc (t + j * h) (t + (j + 1) * h)) : stepIndex t h s = j := by
  unfold stepIndex
  have hc : ⌈(s - t) / h⌉₊ = j + 1 := by
    rw [Nat.ceil_eq_iff (by omega)]
    simp only [Nat.add_sub_cancel]
    constructor
    · rw [lt_div_iff₀ hh]; linarith [hs.1]
    · rw [div_le_iff₀ hh]; push_cast; linarith [hs.2]
  omega

/-- O&R p. 522: for `s > t`, `(s − t)/h − 1 ≤ index < (s − t)/h`. -/
theorem stepIndex_bounds {t h s : ℝ} (hh : 0 < h) (hs : t < s) :
    (s - t) / h - 1 ≤ (stepIndex t h s : ℝ) ∧ (stepIndex t h s : ℝ) < (s - t) / h := by
  have hx : 0 < (s - t) / h := div_pos (by linarith) hh
  have h1 : 1 ≤ ⌈(s - t) / h⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; exact hx)
  have h2 := Nat.le_ceil ((s - t) / h)
  have h3 := Nat.ceil_lt_add_one hx.le
  unfold stepIndex
  rw [Nat.cast_sub h1]
  push_cast
  constructor <;> linarith

/-- O&R p. 522: the integral of a grid-step function over `[t, t + Nh]` is the Riemann sum
`h Σ_{j<N} d_j`. -/
theorem step_intervalIntegral (d : ℕ → ℝ) {t h : ℝ} (hh : 0 < h) (N : ℕ) :
    ∫ s in t..t + N * h, d (stepIndex t h s) = h * ∑ j ∈ Finset.range N, d j := by
  have hpiece : ∀ k : ℕ, EqOn (fun s => d (stepIndex t h s)) (fun _ => d k)
      (uIoc (t + k * h) (t + ((k + 1 : ℕ) : ℝ) * h)) := by
    intro k s hs
    rw [uIoc_of_le (by push_cast; nlinarith)] at hs
    simp only
    rw [stepIndex_eq hh (j := k) (by push_cast at hs; exact hs)]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun s => d (stepIndex t h s)) (a := fun k : ℕ => t + k * h) (n := N)
    (fun k _ => (intervalIntegrable_const (c := d k)).congr (hpiece k).symm)
  simp only [Nat.cast_zero, zero_mul, add_zero] at hsum
  rw [← hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => hpiece k hs),
    intervalIntegral.integral_const]
  push_cast
  simp only [smul_eq_mul]
  ring

/-- O&R p. 522 (**the limit `h → 0`**): for continuous admissible money, the period-`h`
no-bubble price level converges to the continuous-time fundamental (16) as `h → 0⁺`
(dominated convergence applied to the Riemann-sum representation). -/
theorem periodHPrice_tendsto {η : ℝ} (hη : 0 < η) {m : ℝ → ℝ} (hm : AdmissibleMoney η m)
    (hmc : Continuous m) (t : ℝ) :
    Tendsto (fun h => periodHPrice η h m t) (𝓝[>] 0) (𝓝 (contFundamental η m t)) := by
  obtain ⟨A, κ, hκ, hA⟩ := hm.growth
  set κ' := max κ 0 with hκ'def
  have hκ'0 : 0 ≤ κ' := le_max_right _ _
  have hκ' : κ' < 1 / η := max_lt hκ (by positivity)
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := t) (b := 0)).exists_bound_of_continuousOn
    hmc.continuousOn
  set D := |A| + |K| * Real.exp (-κ' * t) with hD
  have hmD : ∀ x, t ≤ x → |m x| ≤ D * Real.exp (κ' * x) := by
    intro x hx
    rcases le_or_gt 0 x with h0 | h0
    · have e1 : A * Real.exp (κ * x) ≤ |A| * Real.exp (κ' * x) :=
        mul_le_mul (le_abs_self A) (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
          (le_max_left _ _) h0)) (Real.exp_pos _).le (abs_nonneg _)
      have e2 : 0 ≤ |K| * Real.exp (-κ' * t) * Real.exp (κ' * x) := by positivity
      calc |m x| ≤ A * Real.exp (κ * x) := hA x h0
        _ ≤ |A| * Real.exp (κ' * x) := e1
        _ ≤ D * Real.exp (κ' * x) := by rw [hD, add_mul]; linarith
    · have e1 : |m x| ≤ K := by simpa using hK x ⟨hx, h0.le⟩
      have e2 : 1 ≤ Real.exp (-κ' * t) * Real.exp (κ' * x) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
      have e3 : 0 ≤ |A| * Real.exp (κ' * x) := by positivity
      calc |m x| ≤ |K| := e1.trans (le_abs_self K)
        _ ≤ |K| * (Real.exp (-κ' * t) * Real.exp (κ' * x)) := le_mul_of_one_le_right
            (abs_nonneg _) e2
        _ ≤ D * Real.exp (κ' * x) := by rw [hD, add_mul]; nlinarith
  set ρ := (κ' + 1 / η) / 2 with hρ
  have hρ1 : κ' < ρ := by rw [hρ]; linarith
  have hρ2 : ρ < 1 / η := by rw [hρ]; linarith
  have hρ0 : 0 < ρ := lt_of_le_of_lt hκ'0 hρ1
  set h₀ := 1 / ρ - η with hh₀
  have hh₀pos : 0 < h₀ := by
    rw [hh₀, sub_pos, lt_div_iff₀ hρ0]
    rw [lt_div_iff₀ hη] at hρ2; linarith
  -- the step-function integrand
  set F : ℝ → ℝ → ℝ := fun h s => 1 / (h + η) * ((1 + h / η)⁻¹ ^ stepIndex t h s *
    m (t + (stepIndex t h s : ℝ) * h)) with hF
  set C := 1 / η * D * Real.exp (1 + ρ * t) with hC
  set bound : ℝ → ℝ := fun s => C * Real.exp ((κ' - ρ) * s) with hbound
  have hbound_int : IntegrableOn bound (Ioi t) :=
    (integrableOn_exp_mul_Ioi (by linarith) t).const_mul C
  have hF_meas : ∀ h, Measurable (F h) := by
    intro h
    have : F h = fun s => (fun k : ℕ => 1 / (h + η) * ((1 + h / η)⁻¹ ^ (k - 1) *
        m (t + ((k - 1 : ℕ) : ℝ) * h))) ⌈(s - t) / h⌉₊ := rfl
    rw [this]
    exact (measurable_from_nat (f := fun k : ℕ => 1 / (h + η) * ((1 + h / η)⁻¹ ^ (k - 1) *
        m (t + ((k - 1 : ℕ) : ℝ) * h)))).comp
      ((measurable_id'.sub_const t).div_const h).nat_ceil
  have hF_bound : ∀ h, 0 < h → h < h₀ → ∀ s, t < s → |F h s| ≤ bound s := by
    intro h hh hhh s hs
    obtain ⟨hn1, hn2⟩ := stepIndex_bounds hh hs
    set n := stepIndex t h s
    have hnh : (n : ℝ) * h < s - t := by rwa [lt_div_iff₀ hh] at hn2
    have hnh0 : 0 ≤ (n : ℝ) * h := by positivity
    have hL : h / (η + h) ≤ Real.log (1 + h / η) := by
      have := Real.one_sub_inv_le_log_of_pos (x := 1 + h / η) (by positivity)
      have e : 1 - (1 + h / η)⁻¹ = h / (η + h) := by field_simp; ring
      linarith
    have hρh : ρ < 1 / (η + h) := by
      have : η + h < 1 / ρ := by rw [hh₀] at hhh; linarith
      rw [lt_div_iff₀ (by linarith)]
      rw [lt_div_iff₀ hρ0] at this; linarith
    have hpow : (1 + h / η)⁻¹ ^ n ≤ Real.exp (1 - ρ * (s - t)) := by
      have e : (1 + h / η)⁻¹ ^ n = Real.exp (-(n * Real.log (1 + h / η))) := by
        rw [← Real.exp_log (show (0 : ℝ) < (1 + h / η)⁻¹ by positivity), ← Real.exp_nat_mul,
          Real.log_inv]
        congr 1; ring
      rw [e, Real.exp_le_exp]
      have k1 : (n : ℝ) * (h / (η + h)) ≤ n * Real.log (1 + h / η) :=
        mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg n)
      have k2 : ((s - t) / h - 1) * (h / (η + h)) ≤ (n : ℝ) * (h / (η + h)) :=
        mul_le_mul_of_nonneg_right hn1 (by positivity)
      have k3 : ((s - t) / h - 1) * (h / (η + h)) = (s - t) / (η + h) - h / (η + h) := by
        field_simp
      have k4 : ρ * (s - t) ≤ (s - t) / (η + h) := by
        rw [div_eq_mul_one_div]; nlinarith
      have k5 : h / (η + h) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    have hmn : |m (t + n * h)| ≤ D * Real.exp (κ' * s) := by
      refine (hmD _ (by linarith)).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hκ'0)) ?_)
      have := (abs_nonneg (m t)).trans (hmD t le_rfl)
      exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
    have hD0 : 0 ≤ D := by rw [hD]; positivity
    have hsc : 1 / (h + η) ≤ 1 / η := one_div_le_one_div_of_le hη (by linarith)
    simp only [hF, hbound, hC]
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (h + η)),
      abs_of_pos (by positivity : (0 : ℝ) < (1 + h / η)⁻¹ ^ n)]
    calc 1 / (h + η) * ((1 + h / η)⁻¹ ^ n * |m (t + n * h)|)
        ≤ 1 / η * (Real.exp (1 - ρ * (s - t)) * (D * Real.exp (κ' * s))) := by
          gcongr
      _ = 1 / η * D * Real.exp (1 + ρ * t) * Real.exp ((κ' - ρ) * s) := by
          have ee : Real.exp (1 - ρ * (s - t)) * Real.exp (κ' * s) =
              Real.exp (1 + ρ * t) * Real.exp ((κ' - ρ) * s) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          linear_combination (1 / η * D) * ee
  -- the pointwise limit
  have hlim : ∀ s, t < s → Tendsto (fun h => F h s) (𝓝[>] 0)
      (𝓝 (1 / η * (Real.exp (-(s - t) / η) * m s))) := by
    intro s hs
    have hNh : Tendsto (fun h => (stepIndex t h s : ℝ) * h) (𝓝[>] 0) (𝓝 (s - t)) := by
      have hlow : Tendsto (fun h : ℝ => s - t - h) (𝓝[>] 0) (𝓝 (s - t)) := by
        have : Tendsto (fun h : ℝ => s - t - h) (𝓝 0) (𝓝 (s - t - 0)) :=
          tendsto_const_nhds.sub tendsto_id
        rw [sub_zero] at this; exact this.mono_left nhdsWithin_le_nhds
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with h hh
        have k1 := mul_le_mul_of_nonneg_right (stepIndex_bounds hh hs).1 hh.le
        have k2 : (s - t) / h * h = s - t := div_mul_cancel₀ _ (ne_of_gt hh)
        nlinarith
      · filter_upwards [self_mem_nhdsWithin] with h hh
        have := (stepIndex_bounds hh hs).2
        rw [lt_div_iff₀ hh] at this; linarith
    have hscale : Tendsto (fun h : ℝ => 1 / (h + η)) (𝓝[>] 0) (𝓝 (1 / η)) := by
      have : Tendsto (fun h : ℝ => 1 / (h + η)) (𝓝 0) (𝓝 (1 / (0 + η))) :=
        tendsto_const_nhds.div (tendsto_id.add tendsto_const_nhds) (by simp [hη.ne'])
      rw [zero_add] at this; exact this.mono_left nhdsWithin_le_nhds
    have hlog : Tendsto (fun h : ℝ => h⁻¹ * Real.log (1 + (1 / η) / h⁻¹)) (𝓝[>] 0)
        (𝓝 (1 / η)) :=
      (Real.tendsto_mul_log_one_add_div_atTop (1 / η)).comp tendsto_inv_nhdsGT_zero
    have hpow : Tendsto (fun h => (1 + h / η)⁻¹ ^ stepIndex t h s) (𝓝[>] 0)
        (𝓝 (Real.exp (-(s - t) / η))) := by
      have h1 := (hNh.mul hlog).neg
      have h2 := (Real.continuous_exp.tendsto _).comp h1
      have e : -((s - t) * (1 / η)) = -(s - t) / η := by ring
      rw [e] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [mem_Ioi] at hh
      simp only [Function.comp]
      rw [← Real.exp_log (show (0 : ℝ) < (1 + h / η)⁻¹ by positivity), ← Real.exp_nat_mul,
        Real.log_inv]
      have e2 : (1 / η) / h⁻¹ = h / η := by field_simp
      rw [e2]
      congr 1
      field_simp
    have hm_lim : Tendsto (fun h => m (t + (stepIndex t h s : ℝ) * h)) (𝓝[>] 0) (𝓝 (m s)) := by
      have h' : Tendsto (fun h => t + (stepIndex t h s : ℝ) * h) (𝓝[>] 0) (𝓝 (t + (s - t))) :=
        tendsto_const_nhds.add hNh
      rw [add_sub_cancel] at h'
      exact (hmc.tendsto s).comp h'
    exact hscale.mul (hpow.mul hm_lim)
  -- for small `h` the integral of the step function is the period-`h` price
  have hint_eq : ∀ h, 0 < h → h < h₀ → ∫ s in Ioi t, F h s = periodHPrice η h m t := by
    intro h hh hhh
    set c : ℕ → ℝ := fun j => 1 / (h + η) * ((1 + h / η)⁻¹ ^ j * m (t + j * h)) with hc
    have hFint : IntegrableOn (F h) (Ioi t) := by
      refine Integrable.mono' hbound_int (hF_meas h).aestronglyMeasurable ?_
      exact ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => by
        rw [Real.norm_eq_abs]; exact hF_bound h hh hhh s hs
    have hFabs : IntegrableOn (fun s => |F h s|) (Ioi t) := hFint.abs
    have hpart : ∀ N : ℕ, ∫ s in t..t + N * h, F h s = h * ∑ j ∈ Finset.range N, c j :=
      fun N => step_intervalIntegral c hh N
    have hpartabs : ∀ N : ℕ, ∫ s in t..t + N * h, |F h s| =
        h * ∑ j ∈ Finset.range N, |c j| :=
      fun N => step_intervalIntegral (fun j => |c j|) hh N
    have hle : ∀ N : ℕ, ∑ j ∈ Finset.range N, |c j| ≤ (∫ s in Ioi t, |F h s|) / h := by
      intro N
      rw [le_div_iff₀ hh, mul_comm, ← hpartabs N,
        intervalIntegral.integral_of_le (le_add_of_nonneg_right (by positivity))]
      exact setIntegral_mono_set hFabs (ae_of_all _ fun _ => abs_nonneg _)
        Ioc_subset_Ioi_self.eventuallyLE
    have hsumm : Summable c :=
      Summable.of_abs (summable_of_sum_range_le (fun _ => abs_nonneg _) hle)
    have hlim1 : Tendsto (fun N : ℕ => ∫ s in t..t + N * h, F h s) atTop
        (𝓝 (∫ s in Ioi t, F h s)) :=
      intervalIntegral_tendsto_integral_Ioi t hFint
        (tendsto_atTop_add_const_left _ t (tendsto_natCast_atTop_atTop.atTop_mul_const hh))
    have hlim2 : Tendsto (fun N : ℕ => ∫ s in t..t + N * h, F h s) atTop
        (𝓝 (h * ∑' j, c j)) := by
      simp_rw [hpart]; exact hsumm.tendsto_sum_tsum_nat.const_mul h
    rw [tendsto_nhds_unique hlim1 hlim2]
    unfold periodHPrice
    rw [hc, tsum_mul_left]
    ring
  -- dominated convergence
  have hDCT : Tendsto (fun h => ∫ s in Ioi t, F h s) (𝓝[>] 0)
      (𝓝 (∫ s in Ioi t, 1 / η * (Real.exp (-(s - t) / η) * m s))) := by
    refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbound_int ?_
    · exact Eventually.of_forall fun h => (hF_meas h).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT hh₀pos] with h hh
      exact ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => by
        rw [Real.norm_eq_abs]; exact hF_bound h hh.1 hh.2 s hs
    · exact ae_restrict_of_forall_mem measurableSet_Ioi hlim
  have hlimval : (∫ s in Ioi t, 1 / η * (Real.exp (-(s - t) / η) * m s)) =
      contFundamental η m t := by
    unfold contFundamental; rw [integral_const_mul]
  rw [← hlimval]
  refine hDCT.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hh₀pos] with h hh
  exact hint_eq h hh.1 hh.2

end ObstfeldRogoff.MoneyExchangeRates.CaganContinuous

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Speculative attacks on fixed exchange rates

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §8.4.2,
pp. 558–566 (Figure 8.4, Table 8.1).

A perfect-foresight Krugman–Flood–Garber model in continuous time: money-market equilibrium
(70) `m − e = −η ė`; under the peg money is fixed at `m̄ = ē` (71); the central-bank balance
sheet (72) `M = B_H + ℰ̄ B_F`; domestic credit grows at rate `μ` (73), so reserves fall (74).

Results (stronger than the book):
* The post-attack float with no bubble is the shadow rate `ẽ_t = b_{H,t} + ημ` (75); every
  continuous post-attack float is `ẽ_t + b_T e^{(t−T)/η}`.
* **Existence and uniqueness of the attack equilibrium**: with `μ > 0` the equilibrium (peg
  before `T`, no-bubble float after `T`, no anticipated jump at `T`) exists and is unique, with
  `T = (ē − b_{H,0} − ημ)/μ` (76). Switching earlier would be an anticipated discrete
  appreciation, later an anticipated discrete depreciation.
* The attack comes exactly `η` before natural exhaustion `T₀ = (ē − b_{H,0})/μ`; reserves just
  before the attack are `ℰ̄ B_{F,T} = M̄(1 − e^{−ημ}) > 0`; log money drops by exactly `ημ`;
  log reserves decline at an increasing rate (Figure 8.4).
* (77) with the misprint corrected: `ē = log(B_{H,0} + ℰ̄ B_{F,0})` (the book prints
  `log(B_{H,0} + B_{F,0})`, which is right only when `ℰ̄ = 1`); `T > 0` iff
  `log(1 + ℰ̄B_{F,0}/B_{H,0}) > ημ`; `T` rises with reserves and falls with `μ`; when the formula
  is negative the shadow rate already exceeds the peg at date 0 (immediate attack).
* Bubbles: without the no-bubble condition the attack equilibria form a one-parameter family
  indexed by `b_T`, with `T = (ē − b_{H,0} − ημ − b_T)/μ`, strictly decreasing in `b_T`. The
  `μ = 0` case (where the book's formula divides by zero): with no bubble there is never an
  attack when reserves are positive; with bubbles, **every** date is an attack date for the
  bubble `b_T = ē − b_{H,0} = log(1 + ℰ̄B_{F,0}/B_{H,0})`.
* Table 8.1 arithmetic.
-/

namespace ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack

open Filter Topology Set CaganContinuous

/-! ## Domestic credit, reserves and the shadow rate -/

/-- O&R (73) and fn 52, p. 562: domestic credit grows at rate `μ`,
`B_{H,t} = B_{H,0} e^{μt}`, so `b_{H,t} = b_{H,0} + μt`. -/
theorem log_domestic_credit {BH0 : ℝ} (hB : 0 < BH0) (μ t : ℝ) :
    Real.log (BH0 * Real.exp (μ * t)) = Real.log BH0 + μ * t := by
  rw [Real.log_mul hB.ne' (Real.exp_pos _).ne', Real.log_exp]

/-- O&R (72), p. 560: under the peg the reserves `ℰ̄B_{F,t} = M̄ − B_{H,t}` keep the money
supply fixed; by (74) `ℰ̄ Ḃ_F = −Ḃ_H`: reserve losses exactly match credit expansion. -/
theorem reserves_hasDerivAt (Mbar Ebar BH0 μ t : ℝ) :
    HasDerivAt (fun s => (Mbar - BH0 * Real.exp (μ * s)) / Ebar)
      (-(BH0 * Real.exp (μ * t) * μ) / Ebar) t := by
  have h1 : HasDerivAt (fun s => BH0 * Real.exp (μ * s)) (BH0 * (Real.exp (μ * t) * μ)) t := by
    have := ((hasDerivAt_id' t).const_mul μ).exp.const_mul BH0
    simpa using this
  have := (h1.const_sub Mbar).div_const Ebar
  convert this using 1
  ring

/-- O&R (75), p. 562: the shadow floating rate `ẽ_t = b_{H,t} + ημ`. -/
def shadowRate (η μ bH0 t : ℝ) : ℝ := bH0 + μ * t + η * μ

/-- O&R (75) and fn 50, p. 562: the shadow rate solves (70) with money `m = b_H`
(`ẽ̇ = μ` and `m − ẽ = −ημ`). -/
theorem shadowRate_solves (η μ bH0 t : ℝ) :
    HasDerivAt (shadowRate η μ bH0) μ t ∧
      (bH0 + μ * t) - shadowRate η μ bH0 t = -η * μ := by
  refine ⟨?_, by unfold shadowRate; ring⟩
  have := (((hasDerivAt_id' t).const_mul μ).const_add bH0).add_const (η * μ)
  unfold shadowRate; simpa using this

/-- O&R (75), p. 562: the shadow rate is the no-bubble (fundamental) float (16) for the money
path `b_{H,t} = b_{H,0} + μt`. -/
theorem shadowRate_eq_fundamental {η : ℝ} (hη : 0 < η) (μ bH0 t : ℝ) :
    shadowRate η μ bH0 t = contFundamental η (fun s => bH0 + μ * s) t := by
  rw [contFundamental_affine hη]; rfl

/-- O&R (70), p. 559: a path that agrees on `[t₀, ∞)` with a solution of (70) is itself a
solution there. -/
theorem isCaganSolOn_of_eqOn {η : ℝ} {m p q : ℝ → ℝ} {t₀ : ℝ} (hq : IsCaganSolOn η m q t₀)
    (heq : ∀ t, t₀ ≤ t → p t = q t) : IsCaganSolOn η m p t₀ := by
  refine ⟨hq.1.congr fun t ht => heq t ht, fun t ht => ?_⟩
  have := (hq.2 t ht).congr_of_mem (fun u hu => heq u (le_trans ht hu)) self_mem_Ici
  rw [heq t ht]; exact this

/-- O&R p. 564: every continuous post-attack float on `[T, ∞)` is the shadow rate plus a
bubble, `ẽ_t + b_T e^{(t−T)/η}`. -/
theorem float_eq_shadow_add_bubble {η : ℝ} (hη : 0 < η) {μ bH0 T : ℝ} {e : ℝ → ℝ}
    (he : IsCaganSolOn η (fun s => bH0 + μ * s) e T) (t : ℝ) (ht : T ≤ t) :
    e t = shadowRate η μ bH0 t + (e T - shadowRate η μ bH0 T) * Real.exp ((t - T) / η) := by
  have hrc : ∀ u, ContinuousWithinAt (fun s => bH0 + μ * s) (Ici u) u :=
    fun u => (by fun_prop : Continuous fun s : ℝ => bH0 + μ * s).continuousWithinAt
  rw [isCaganSolOn_eq_fundamental_add_bubble hη (admissible_affine hη bH0 μ) hrc he t ht,
    ← shadowRate_eq_fundamental hη, ← shadowRate_eq_fundamental hη, mul_assoc,
    ← Real.exp_add]
  congr 3; ring

/-- O&R p. 564: conversely the shadow rate plus any bubble `b_T e^{(t−T)/η}` solves (70) on
`[T, ∞)`. -/
theorem shadow_add_bubble_isSol {η : ℝ} (hη : 0 < η) (μ bH0 T b : ℝ) :
    IsCaganSolOn η (fun s => bH0 + μ * s)
      (fun t => shadowRate η μ bH0 t + b * Real.exp ((t - T) / η)) T := by
  refine ⟨by unfold shadowRate; fun_prop, fun t _ => ?_⟩
  have h1 := (shadowRate_solves η μ bH0 t).1
  have h2 : HasDerivAt (fun u => b * Real.exp ((u - T) / η))
      (b * (Real.exp ((t - T) / η) * (1 / η))) t := by
    have := (((hasDerivAt_id' t).sub_const T).div_const η).exp.const_mul b
    simpa using this
  have := (h1.add h2).hasDerivWithinAt (s := Ici t)
  convert this using 1
  unfold shadowRate
  field_simp
  ring

/-! ## The attack equilibrium -/

/-- O&R §8.4.2.3–8.4.2.4, pp. 561–562: an attack equilibrium with collapse date `T`: the rate
is pegged at `ē` before `T`, floats according to (70) with money `b_H` from `T` on (with no
bubble), and there is no anticipated discrete jump at `T` (the path is continuous at `T`). -/
def IsAttackEqm (η μ ebar bH0 T : ℝ) (e : ℝ → ℝ) : Prop :=
  (∀ t, t < T → e t = ebar) ∧ IsCaganSolOn η (fun s => bH0 + μ * s) e T ∧ ContinuousAt e T ∧
    Tendsto (fun t => Real.exp (-t / η) * e t) atTop (𝓝 0)

/-- O&R (76), p. 562: the attack date `T = (ē − b_{H,0} − ημ)/μ`. -/
noncomputable def attackTime (η μ ebar bH0 : ℝ) : ℝ := (ebar - bH0 - η * μ) / μ

/-- O&R p. 562: at the attack date the shadow rate equals the peg. -/
theorem shadowRate_attackTime {η μ ebar bH0 : ℝ} (hμ : μ ≠ 0) :
    shadowRate η μ bH0 (attackTime η μ ebar bH0) = ebar := by
  unfold shadowRate attackTime; field_simp; ring

/-- O&R p. 561: a path pegged at `ē` before `T` and continuous at `T` has `e_T = ē` (no
anticipated jump). -/
theorem eq_peg_of_continuousAt {e : ℝ → ℝ} {ebar T : ℝ} (hpeg : ∀ t, t < T → e t = ebar)
    (hc : ContinuousAt e T) : e T = ebar := by
  have h1 : Tendsto e (𝓝[<] T) (𝓝 (e T)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto e (𝓝[<] T) (𝓝 ebar) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (hpeg t ht).symm)
  exact tendsto_nhds_unique h1 h2

/-- O&R (75)–(76), p. 562: in any attack equilibrium the post-attack float is the shadow rate
and the collapse date is `T = (ē − b_{H,0} − ημ)/μ`. -/
theorem attackEqm_characterisation {η μ ebar bH0 T : ℝ} (hη : 0 < η) (hμ : μ ≠ 0)
    {e : ℝ → ℝ} (h : IsAttackEqm η μ ebar bH0 T e) :
    T = attackTime η μ ebar bH0 ∧ ∀ t, T ≤ t → e t = shadowRate η μ bH0 t := by
  obtain ⟨hpeg, hsol, hc, hnb⟩ := h
  have hrc : ∀ u, ContinuousWithinAt (fun s => bH0 + μ * s) (Ici u) u :=
    fun u => (by fun_prop : Continuous fun s : ℝ => bH0 + μ * s).continuousWithinAt
  have hfl : ∀ t, T ≤ t → e t = shadowRate η μ bH0 t := fun t ht => by
    rw [(noBubble_iff_eq_fundamental hη (admissible_affine hη bH0 μ) hrc hsol).1 hnb t ht,
      shadowRate_eq_fundamental hη]
  refine ⟨?_, hfl⟩
  have h1 := eq_peg_of_continuousAt hpeg hc
  rw [hfl T le_rfl] at h1
  unfold attackTime; unfold shadowRate at h1
  field_simp
  linarith

/-- O&R (76), p. 562: with `μ > 0` the attack equilibrium **exists**: the path
`max(ē, ẽ_t)` (peg until the shadow rate reaches the peg, float afterwards). -/
theorem attackEqm_exists {η μ : ℝ} (hη : 0 < η) (hμ : 0 < μ) (ebar bH0 : ℝ) :
    IsAttackEqm η μ ebar bH0 (attackTime η μ ebar bH0)
      (fun t => max ebar (shadowRate η μ bH0 t)) := by
  set T := attackTime η μ ebar bH0
  have hT : shadowRate η μ bH0 T = ebar := shadowRate_attackTime hμ.ne'
  have hlt : ∀ t, t < T → shadowRate η μ bH0 t < ebar := by
    intro t ht; rw [← hT]; unfold shadowRate; nlinarith
  have hge : ∀ t, T ≤ t → ebar ≤ shadowRate η μ bH0 t := by
    intro t ht; rw [← hT]; unfold shadowRate; nlinarith
  have heq : ∀ t, T ≤ t → max ebar (shadowRate η μ bH0 t) = shadowRate η μ bH0 t :=
    fun t ht => max_eq_right (hge t ht)
  have hsh : IsCaganSolOn η (fun s => bH0 + μ * s) (shadowRate η μ bH0) T := by
    have := shadow_add_bubble_isSol hη μ bH0 T 0
    simp only [zero_mul, add_zero] at this
    exact this
  refine ⟨fun t ht => max_eq_left (hlt t ht).le, isCaganSolOn_of_eqOn hsh heq, ?_, ?_⟩
  · exact (by unfold shadowRate; fun_prop : Continuous fun t =>
      max ebar (shadowRate η μ bH0 t)).continuousAt
  · have := tendsto_exp_neg_mul_affine hη (bH0 + η * μ) μ
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop T] with t ht
    rw [heq t ht]; unfold shadowRate; ring

/-- O&R (76), p. 562: **uniqueness**: every attack equilibrium has the collapse date (76) and
coincides with `max(ē, ẽ_t)`. -/
theorem attackEqm_unique {η μ : ℝ} (hη : 0 < η) (hμ : 0 < μ) {ebar bH0 T : ℝ} {e : ℝ → ℝ}
    (h : IsAttackEqm η μ ebar bH0 T e) :
    T = attackTime η μ ebar bH0 ∧ e = fun t => max ebar (shadowRate η μ bH0 t) := by
  obtain ⟨hT, hfl⟩ := attackEqm_characterisation hη hμ.ne' h
  refine ⟨hT, funext fun t => ?_⟩
  have hTe : shadowRate η μ bH0 T = ebar := by rw [hT]; exact shadowRate_attackTime hμ.ne'
  rcases lt_or_ge t T with ht | ht
  · rw [h.1 t ht, max_eq_left]
    rw [← hTe]; unfold shadowRate; nlinarith
  · rw [hfl t ht, max_eq_right]
    rw [← hTe]; unfold shadowRate; nlinarith

/-- O&R p. 562: a switch to the no-bubble float at any other date `T′` would involve a
discrete jump `ẽ_{T′} − ē = μ(T′ − T)`: an anticipated appreciation if `T′ < T` (so nobody
attacks early) and an anticipated depreciation if `T′ > T` (so speculators attack before). -/
theorem jump_at_other_date {η μ ebar bH0 : ℝ} (hμ : μ ≠ 0) (T' : ℝ) :
    shadowRate η μ bH0 T' - ebar = μ * (T' - attackTime η μ ebar bH0) := by
  unfold shadowRate attackTime; field_simp; ring

/-- O&R p. 565: before the attack the rate is constant (`ė = 0`, so `i = i*`); after it the
rate depreciates at `μ` (so the home interest rate jumps up by `μ`). -/
theorem depreciation_before_after {η μ : ℝ} (hμ : 0 < μ) (ebar bH0 t : ℝ) :
    (t < attackTime η μ ebar bH0 →
        HasDerivAt (fun s => max ebar (shadowRate η μ bH0 s)) 0 t) ∧
      (attackTime η μ ebar bH0 < t →
        HasDerivAt (fun s => max ebar (shadowRate η μ bH0 s)) μ t) := by
  have hT : shadowRate η μ bH0 (attackTime η μ ebar bH0) = ebar := shadowRate_attackTime hμ.ne'
  constructor
  · intro ht
    have hev : (fun s => max ebar (shadowRate η μ bH0 s)) =ᶠ[𝓝 t] fun _ => ebar := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      refine max_eq_left ?_
      rw [← hT]; unfold shadowRate; simp only [mem_Iio] at hs; nlinarith
    exact (hasDerivAt_const t ebar).congr_of_eventuallyEq hev
  · intro ht
    have hev : (fun s => max ebar (shadowRate η μ bH0 s)) =ᶠ[𝓝 t] shadowRate η μ bH0 := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      refine max_eq_right ?_
      rw [← hT]; unfold shadowRate; simp only [mem_Ioi] at hs; nlinarith
    exact (shadowRate_solves η μ bH0 t).1.congr_of_eventuallyEq hev

/-! ## Timing relative to natural exhaustion, reserves at the attack -/

/-- O&R p. 561: the date at which reserves would run out without an attack,
`T₀ = (ē − b_{H,0})/μ` (when `b_{H,T₀} = ē`). -/
noncomputable def exhaustionTime (μ ebar bH0 : ℝ) : ℝ := (ebar - bH0) / μ

/-- O&R p. 561, sharpened: the attack comes **exactly `η`** before natural exhaustion. -/
theorem attackTime_eq_exhaustion_sub {η μ ebar bH0 : ℝ} (hμ : μ ≠ 0) :
    attackTime η μ ebar bH0 = exhaustionTime μ ebar bH0 - η := by
  unfold attackTime exhaustionTime; field_simp

/-- O&R p. 561: without an attack, reserves `M̄ − B_{H,t}` (with `M̄ = e^{ē}`) would reach
zero exactly at `T₀`. -/
theorem reserves_zero_at_exhaustion {μ ebar bH0 : ℝ} (hμ : μ ≠ 0) :
    Real.exp ebar - Real.exp (bH0 + μ * exhaustionTime μ ebar bH0) = 0 := by
  unfold exhaustionTime; rw [mul_div_cancel₀ _ hμ]; ring_nf

/-- O&R p. 562 and Figure 8.4: just before the attack, reserves are
`ℰ̄B_{F,T} = M̄ − B_{H,T} = M̄(1 − e^{−ημ})`, strictly positive. -/
theorem reserves_at_attack {η μ ebar bH0 : ℝ} (hμ : μ ≠ 0) :
    Real.exp ebar - Real.exp (bH0 + μ * attackTime η μ ebar bH0) =
      Real.exp ebar * (1 - Real.exp (-(η * μ))) := by
  have : bH0 + μ * attackTime η μ ebar bH0 = ebar + -(η * μ) := by
    unfold attackTime; field_simp; ring
  rw [this, Real.exp_add]; ring

/-- O&R p. 562: the reserves remaining at the attack are strictly positive when `ημ > 0`. -/
theorem reserves_at_attack_pos {η μ ebar bH0 : ℝ} (hη : 0 < η) (hμ : 0 < μ) :
    0 < Real.exp ebar - Real.exp (bH0 + μ * attackTime η μ ebar bH0) := by
  rw [reserves_at_attack hμ.ne']
  have : Real.exp (-(η * μ)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
  have := Real.exp_pos ebar
  nlinarith

/-- O&R p. 561 and Figure 8.4: at the attack log money drops from `ē` to `b_{H,T} = ē − ημ`,
i.e. by exactly `ημ` (the fall in real balances required by the jump in expected
depreciation from `0` to `μ`). -/
theorem money_drop_at_attack {η μ ebar bH0 : ℝ} (hμ : μ ≠ 0) :
    ebar - (bH0 + μ * attackTime η μ ebar bH0) = η * μ := by
  unfold attackTime; field_simp; ring

/-- O&R Figure 8.4: reserves are strictly positive throughout the fixed-rate period
`t ≤ T` (for `μ > 0`). -/
theorem reserves_pos_before_attack {η μ ebar bH0 : ℝ} (hη : 0 < η) (hμ : 0 < μ) {t : ℝ}
    (ht : t ≤ attackTime η μ ebar bH0) : 0 < Real.exp ebar - Real.exp (bH0 + μ * t) := by
  have h1 := reserves_at_attack_pos (ebar := ebar) (bH0 := bH0) hη hμ
  have h2 : Real.exp (bH0 + μ * t) ≤ Real.exp (bH0 + μ * attackTime η μ ebar bH0) :=
    Real.exp_le_exp.2 (by nlinarith)
  linarith

/-- O&R Figure 8.4: the derivative of log reserves `log(M̄ − B_{H,t})` is
`−μB_{H,t}/(M̄ − B_{H,t})`. -/
theorem log_reserves_hasDerivAt {Mbar BH0 μ t : ℝ} (hpos : 0 < Mbar - BH0 * Real.exp (μ * t)) :
    HasDerivAt (fun s => Real.log (Mbar - BH0 * Real.exp (μ * s)))
      (-(μ * (BH0 * Real.exp (μ * t))) / (Mbar - BH0 * Real.exp (μ * t))) t := by
  have h1 : HasDerivAt (fun s => Mbar - BH0 * Real.exp (μ * s))
      (-(BH0 * (Real.exp (μ * t) * μ))) t := by
    have := (((hasDerivAt_id' t).const_mul μ).exp.const_mul BH0).const_sub Mbar
    simpa using this
  have := h1.log hpos.ne'
  convert this using 1
  ring

/-- O&R p. 562 and Figure 8.4: log reserves decline at an increasing rate: the rate of decline
`μB_{H,t}/(M̄ − B_{H,t})` is strictly increasing in `t` while reserves are positive
(`B_{H,0} > 0`, `μ > 0`). -/
theorem log_reserves_decline_accelerates {Mbar BH0 μ : ℝ} (hB : 0 < BH0) (hμ : 0 < μ)
    {t₁ t₂ : ℝ} (h12 : t₁ < t₂) (hpos : 0 < Mbar - BH0 * Real.exp (μ * t₂)) :
    μ * (BH0 * Real.exp (μ * t₁)) / (Mbar - BH0 * Real.exp (μ * t₁)) <
      μ * (BH0 * Real.exp (μ * t₂)) / (Mbar - BH0 * Real.exp (μ * t₂)) := by
  have he : Real.exp (μ * t₁) < Real.exp (μ * t₂) := Real.exp_lt_exp.2 (by nlinarith)
  have hB1 : BH0 * Real.exp (μ * t₁) < BH0 * Real.exp (μ * t₂) := mul_lt_mul_of_pos_left he hB
  have hpos1 : 0 < Mbar - BH0 * Real.exp (μ * t₁) := by linarith
  have hx1 : 0 < BH0 * Real.exp (μ * t₁) := by positivity
  have hM : 0 < Mbar := by linarith
  rw [div_lt_div_iff₀ hpos1 hpos]
  nlinarith [mul_pos (mul_pos hμ hM) (sub_pos.2 hB1)]

/-! ## Formula (77), corrected -/

/-- O&R (77), p. 564, corrected: with `ē = log(B_{H,0} + ℰ̄B_{F,0})` (from (71)–(72)) the
attack date is `T = [log(B_{H,0} + ℰ̄B_{F,0}) − b_{H,0} − ημ]/μ =
[log(1 + ℰ̄B_{F,0}/B_{H,0}) − ημ]/μ`. -/
theorem attackTime_corrected {η μ Ebar BH0 BF0 : ℝ} (hB : 0 < BH0) (hE : 0 < Ebar)
    (hF : 0 ≤ BF0) :
    attackTime η μ (Real.log (BH0 + Ebar * BF0)) (Real.log BH0) =
      (Real.log (1 + Ebar * BF0 / BH0) - η * μ) / μ := by
  unfold attackTime
  congr 1
  rw [show 1 + Ebar * BF0 / BH0 = (BH0 + Ebar * BF0) / BH0 by field_simp,
    Real.log_div (by positivity) hB.ne']

/-- O&R (77), p. 564: the printed version `log(B_{H,0} + B_{F,0})` agrees with the correct
`log(B_{H,0} + ℰ̄B_{F,0})` only if `ℰ̄ = 1` (or `B_{F,0} = 0`). -/
theorem printed_77_wrong {Ebar BH0 BF0 : ℝ} (hB : 0 < BH0) (hE : 0 < Ebar) (hF : 0 < BF0)
    (hE1 : Ebar ≠ 1) : Real.log (BH0 + BF0) ≠ Real.log (BH0 + Ebar * BF0) := by
  intro h
  have := Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity) h
  apply hE1
  have : (Ebar - 1) * BF0 = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · linarith

/-- O&R p. 564: the fixed-rate period has positive length iff
`log(1 + ℰ̄B_{F,0}/B_{H,0}) > ημ` (`μ > 0`). -/
theorem attackTime_pos_iff {η μ Ebar BH0 BF0 : ℝ} (hμ : 0 < μ) (hB : 0 < BH0) (hE : 0 < Ebar)
    (hF : 0 ≤ BF0) :
    0 < attackTime η μ (Real.log (BH0 + Ebar * BF0)) (Real.log BH0) ↔
      η * μ < Real.log (1 + Ebar * BF0 / BH0) := by
  rw [attackTime_corrected hB hE hF, div_pos_iff_of_pos_right hμ, sub_pos]

/-- O&R p. 564: the larger the initial reserves, the later the attack. -/
theorem attackTime_strictMono_reserves {η μ Ebar BH0 : ℝ} (hμ : 0 < μ) (hB : 0 < BH0)
    (hE : 0 < Ebar) {BF0 BF0' : ℝ} (hF : 0 ≤ BF0) (hlt : BF0 < BF0') :
    attackTime η μ (Real.log (BH0 + Ebar * BF0)) (Real.log BH0) <
      attackTime η μ (Real.log (BH0 + Ebar * BF0')) (Real.log BH0) := by
  unfold attackTime
  have : Real.log (BH0 + Ebar * BF0) < Real.log (BH0 + Ebar * BF0') :=
    Real.log_lt_log (by positivity) (by nlinarith)
  exact div_lt_div_of_pos_right (by linarith) hμ

/-- O&R p. 564: faster credit growth brings the attack forward (`B_{F,0} > 0`). -/
theorem attackTime_strictAnti_growth {η Ebar BH0 BF0 : ℝ} (hB : 0 < BH0)
    (hE : 0 < Ebar) (hF : 0 < BF0) {μ μ' : ℝ} (hμ : 0 < μ) (hlt : μ < μ') :
    attackTime η μ' (Real.log (BH0 + Ebar * BF0)) (Real.log BH0) <
      attackTime η μ (Real.log (BH0 + Ebar * BF0)) (Real.log BH0) := by
  rw [attackTime_corrected hB hE hF.le, attackTime_corrected hB hE hF.le]
  have hL : 0 < Real.log (1 + Ebar * BF0 / BH0) := Real.log_pos (by
    have : 0 < Ebar * BF0 / BH0 := by positivity
    linarith)
  have hμ' : 0 < μ' := by linarith
  have e1 : (Real.log (1 + Ebar * BF0 / BH0) - η * μ') / μ' =
      Real.log (1 + Ebar * BF0 / BH0) / μ' - η := by field_simp
  have e2 : (Real.log (1 + Ebar * BF0 / BH0) - η * μ) / μ =
      Real.log (1 + Ebar * BF0 / BH0) / μ - η := by field_simp
  have : Real.log (1 + Ebar * BF0 / BH0) / μ' < Real.log (1 + Ebar * BF0 / BH0) / μ :=
    div_lt_div_of_pos_left hL hμ hlt
  rw [e1, e2]; linarith

/-- O&R p. 564: if the formula gives `T < 0`, the shadow rate already exceeds the peg at date
0, so the attack must take place immediately. -/
theorem immediate_attack {η μ ebar bH0 : ℝ} (hμ : 0 < μ) (hT : attackTime η μ ebar bH0 < 0) :
    ebar < shadowRate η μ bH0 0 := by
  unfold attackTime at hT; unfold shadowRate
  rw [div_neg_iff] at hT
  rcases hT with ⟨-, h⟩ | ⟨h1, -⟩
  · linarith
  · linarith

/-! ## Bubbles and the `μ = 0` case -/

/-- O&R p. 564: an attack equilibrium in which post-attack bubbles are not ruled out. -/
def IsBubbleAttackEqm (η μ ebar bH0 T : ℝ) (e : ℝ → ℝ) : Prop :=
  (∀ t, t < T → e t = ebar) ∧ IsCaganSolOn η (fun s => bH0 + μ * s) e T ∧ ContinuousAt e T

/-- O&R p. 564: with a post-attack bubble `b_T`, the float is `log B_{H,t} + ημ +
b_T e^{(t−T)/η}` and the attack date satisfies `ē = b_{H,0} + μT + ημ + b_T`. -/
theorem bubbleAttackEqm_characterisation {η μ ebar bH0 T : ℝ} (hη : 0 < η) {e : ℝ → ℝ}
    (h : IsBubbleAttackEqm η μ ebar bH0 T e) :
    ∃ bT : ℝ, (∀ t, T ≤ t → e t = shadowRate η μ bH0 t + bT * Real.exp ((t - T) / η)) ∧
      ebar = shadowRate η μ bH0 T + bT := by
  obtain ⟨hpeg, hsol, hc⟩ := h
  refine ⟨e T - shadowRate η μ bH0 T, fun t ht => float_eq_shadow_add_bubble hη hsol t ht, ?_⟩
  have := eq_peg_of_continuousAt hpeg hc
  linarith

/-- O&R p. 564: with a bubble `b_T` the attack date is `T = (ē − b_{H,0} − ημ − b_T)/μ`. -/
theorem bubble_attackTime {η μ ebar bH0 T bT : ℝ} (hμ : μ ≠ 0)
    (h : ebar = shadowRate η μ bH0 T + bT) : T = attackTime η μ ebar bH0 - bT / μ := by
  unfold attackTime; unfold shadowRate at h; field_simp; linarith

/-- O&R p. 564: for every bubble size `b_T` there is an attack equilibrium (collapse date
`T = (ē − b_{H,0} − ημ − b_T)/μ`): the attack equilibria without the no-bubble condition
form a one-parameter family. -/
theorem bubbleAttackEqm_exists {η μ : ℝ} (hη : 0 < η) (hμ : μ ≠ 0) (ebar bH0 bT : ℝ) :
    IsBubbleAttackEqm η μ ebar bH0 (attackTime η μ ebar bH0 - bT / μ)
      (fun t => shadowRate η μ bH0 (max t (attackTime η μ ebar bH0 - bT / μ)) +
        bT * Real.exp ((max t (attackTime η μ ebar bH0 - bT / μ) -
          (attackTime η μ ebar bH0 - bT / μ)) / η)) := by
  set T := attackTime η μ ebar bH0 - bT / μ with hTdef
  refine ⟨fun t ht => ?_, isCaganSolOn_of_eqOn (shadow_add_bubble_isSol hη μ bH0 T bT)
    fun t ht => by simp only [max_eq_left ht], by unfold shadowRate; fun_prop⟩
  simp only
  rw [max_eq_right ht.le, sub_self, zero_div, Real.exp_zero, mul_one, hTdef]
  unfold shadowRate attackTime; field_simp; ring

/-- O&R p. 564: the attack date is strictly decreasing in the bubble `b_T` (for `μ > 0`):
bubbles bring attacks forward. -/
theorem bubble_attackTime_strictAnti {η μ ebar bH0 : ℝ} (hμ : 0 < μ) {b b' : ℝ} (hbb : b < b') :
    attackTime η μ ebar bH0 - b' / μ < attackTime η μ ebar bH0 - b / μ := by
  have := div_lt_div_of_pos_right hbb hμ
  linarith

/-- O&R p. 564 (the `μ = 0` case, where the displayed formula is undefined): with no bubble
there is **no** attack equilibrium when reserves are positive (`ē > b_{H,0}`): the peg
survives forever. -/
theorem no_attack_without_growth {η ebar bH0 T : ℝ} (hη : 0 < η) (hres : bH0 < ebar)
    {e : ℝ → ℝ} : ¬ IsAttackEqm η 0 ebar bH0 T e := by
  intro h
  obtain ⟨hpeg, hsol, hc, hnb⟩ := h
  have hrc : ∀ u, ContinuousWithinAt (fun s => bH0 + 0 * s) (Ici u) u :=
    fun u => (by fun_prop : Continuous fun s : ℝ => bH0 + 0 * s).continuousWithinAt
  have hfl := (noBubble_iff_eq_fundamental hη (admissible_affine hη bH0 0) hrc hsol).1 hnb T le_rfl
  rw [contFundamental_affine hη] at hfl
  have := eq_peg_of_continuousAt hpeg hc
  simp only [zero_mul, add_zero, mul_zero] at hfl
  linarith

/-- O&R p. 564 (the `μ = 0` case made precise): with bubbles, an attack at date `T` is an
equilibrium iff the bubble is `b_T = ē − b_{H,0}`, whatever `T` is: attack timing is
indeterminate and bubbles can make **any** date an attack date. -/
theorem attack_without_growth_iff {η ebar bH0 T : ℝ} (hη : 0 < η) {e : ℝ → ℝ}
    (h : IsBubbleAttackEqm η 0 ebar bH0 T e) :
    ∀ t, T ≤ t → e t = bH0 + (ebar - bH0) * Real.exp ((t - T) / η) := by
  obtain ⟨bT, hfl, hT⟩ := bubbleAttackEqm_characterisation hη h
  intro t ht
  rw [hfl t ht]
  unfold shadowRate at hT ⊢
  have : bT = ebar - bH0 := by linarith
  rw [this]; ring

/-- O&R p. 564: with `μ = 0`, **every** date `T` is the date of some bubble-driven attack
equilibrium. -/
theorem attack_without_growth_any_date {η : ℝ} (hη : 0 < η) (ebar bH0 T : ℝ) :
    IsBubbleAttackEqm η 0 ebar bH0 T
      (fun t => shadowRate η 0 bH0 (max t T) +
        (ebar - bH0) * Real.exp ((max t T - T) / η)) := by
  refine ⟨fun t ht => ?_, isCaganSolOn_of_eqOn (shadow_add_bubble_isSol hη 0 bH0 T (ebar - bH0))
    fun t ht => by simp only [max_eq_left ht], by unfold shadowRate; fun_prop⟩
  simp only
  rw [max_eq_right ht.le, sub_self, zero_div, Real.exp_zero, mul_one]
  unfold shadowRate; ring

/-- O&R p. 564: the `μ = 0` attack bubble is `b_T = log(1 + ℰ̄B_{F,0}/B_{H,0})`, positive when
reserves are positive. -/
theorem zero_growth_bubble_size {Ebar BH0 BF0 : ℝ} (hB : 0 < BH0) (hE : 0 < Ebar)
    (hF : 0 < BF0) :
    Real.log (BH0 + Ebar * BF0) - Real.log BH0 = Real.log (1 + Ebar * BF0 / BH0) ∧
      0 < Real.log (1 + Ebar * BF0 / BH0) := by
  constructor
  · rw [show 1 + Ebar * BF0 / BH0 = (BH0 + Ebar * BF0) / BH0 by field_simp,
      Real.log_div (by positivity) hB.ne']
  · exact Real.log_pos (by have : 0 < Ebar * BF0 / BH0 := by positivity
                           linarith)

/-! ## Table 8.1 -/

/-- O&R Table 8.1, p. 566: reserves/base ratios recomputed from the GNP shares: Belgium
`12.1/6.7 ≈ 1.806` (printed 180), Norway `18.7/6.3 ≈ 2.968` (printed 297), Ireland
`16.1/9.1 ≈ 1.769` (printed 177). -/
theorem table_8_1_ratios :
    ((1.80 : ℝ) < 12.1 / 6.7 ∧ (12.1 : ℝ) / 6.7 < 1.81) ∧
      ((2.96 : ℝ) < 18.7 / 6.3 ∧ (18.7 : ℝ) / 6.3 < 2.97) ∧
      ((1.76 : ℝ) < 16.1 / 9.1 ∧ (16.1 : ℝ) / 9.1 < 1.77) := by
  norm_num

/-- O&R Table 8.1, p. 566: Italy's printed ratio 48 is not an error: the rounded entries give
`5.6/11.9 ≈ 0.471`, but unrounded values within the rounding intervals (e.g. base `11.85`,
reserves `5.65`) give a ratio that rounds to 48 percent. -/
theorem table_8_1_italy :
    (0.47 : ℝ) < 5.6 / 11.9 ∧ (5.6 : ℝ) / 11.9 < 0.475 ∧
      (0.475 : ℝ) ≤ 5.65 / 11.85 ∧ (5.65 : ℝ) / 11.85 < 0.485 := by
  norm_num

end ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Target zones for exchange rates

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §8.5–8.6 and
Exercise 5, pp. 569–579, 601.

* The target-zone ODE (84) `G(k) = k + (ηv²/2)G″(k)` and, with trending fundamentals
  (Exercise 5), `G = k + ημG′ + (ηv²/2)G″`: on any open interval its (twice differentiable)
  solutions are **exactly** `ημ + k + b₁e^{λ₁k} + b₂e^{λ₂k}` (for `μ = 0`: `λ₁,₂ = ±λ`,
  `λ = √(2/(ηv²))`); `b₂ = 0` iff `G(k) − k − ημ → 0` as `k → −∞` (§8.6).
* The symmetric zone (85): there are **unique** `b, k̄ > 0` with value matching `S(k̄) = ē` and
  smooth pasting `S′(k̄) = 0`; `k̄` is the unique positive root of `k − tanh(λk)/λ = ē` and
  `b = 1/(2λ cosh λk̄)`. Properties 1–3 of Figure 8.5: `S` is odd, `S′ = 1 − cosh λk/cosh λk̄ ∈
  [0, 1)` on the band with zeros exactly at `±k̄`, `S` maps `[−k̄, k̄]` increasingly onto
  `[−ē, ē]`, concave/convex on the positive/negative side; the **honeymoon effect**
  `|S(k)| < |k|`, so `ē < k̄ < ē + 1/λ`; `k̄ → ē` as `v → 0`.
* Smooth pasting in continuous time (the Itô/local-time argument of *8.5.5, flagged in the
  survey as T13) is *not* formalised; its rigorous substitute here is the **discrete target
  zone**: fundamentals on a lattice `k_i = iΔ`, `|i| ≤ N`, moving `±Δ` with probability ½,
  with the step out of the band suppressed (intervention). The equilibrium condition
  `e = k + (η/h)(E e − e)` has a **unique** solution, given in closed form
  `e_i = iΔ − D sinh(θi)` (`cosh θ = 1 + h/η`); it is odd, strictly increasing, obeys the
  honeymoon effect, its increments are `Δ(1 − cosh θ(i+½)/cosh θ(N+½))` (the discrete
  `S′ = 1 − cosh λk/cosh λk̄`), it pastes smoothly at the ghost node (`e_{N+1} = e_N`), and its
  boundary slope is `O(Δ)`. Without barriers the free float `e = k` is the unique solution with
  `e − k` bounded. The lattice equilibrium *is* CaganModel's `markovFundamental` for the
  regulated band kernel, i.e. (80) holds with expectations under the regulated process.
* **Lattice → continuous** (scaling `h = Δ²/v²`): `θ_Δ = 2 arsinh(λΔ/2)` solves the lattice
  characteristic equation, `θ_Δ/Δ → λ`, the smooth-pasting constant is exactly
  `1/(λ cosh(θ_Δ K/Δ))`, the error is bounded uniformly on the band by `(2K/λ)|θ_Δ/Δ − λ|`,
  so the lattice equilibrium converges uniformly to `S`; for a prescribed ceiling the lattice
  spacing is unique and the lattice band edge converges to `k̄`.
* p. 578: on the lattice the ceiling is hit, and interventions recur, with probability one:
  for every `r`, P(at most `r` interventions by date `n`) → 0, so any finite reserve stock is
  exhausted.
* The one-sided zone of §8.6: (88)–(89) give `k̄ = ē + ℜ`, `b₁ = −ℜe^{−λk̄} < 0`; smooth pasting
  (90) holds iff `ℜ = ℜ′ = 1/λ`; the fully credible zone `k̄′ = ē + 1/λ`; for `ℜ > ℜ′` an attack
  would be an anticipated appreciation (impossible); for `ℜ < ℜ′` the locus `S₁` lacks smooth
  pasting.
* Exercise 5: roots `λ₁ > 0 > λ₂` with `λ₁λ₂ = −2/(ηv²)`; for given fundamental barriers
  `k̲ < k̄`, smooth pasting at both determines `(b₁, b₂)` uniquely; and for **every** drift and
  every prescribed currency band `e̲ < ē` the full 4-equation system (value matching and
  smooth pasting at both edges) has exactly one solution `(b₁, b₂, k̲, k̄)`: by translation
  invariance it reduces to `W(k̄ − k̲) = ē − e̲`, with `W` strictly increasing from 0 to ∞.
* §8.5.6 and fn 60: in a band, `(1+i)/(1+i*)` lies in the range of possible exchange-rate
  changes, by no-arbitrage alone (whatever the preferences); the numbers 2%, 4%, 24%.
* The flag on (86): for a symmetric increment, the regulated increment `min(dk, 0)` has second
  moment `E(dk)²/2`, not `E(dk)²`, and first moment `−E|dk|/2`.
-/

namespace ObstfeldRogoff.MoneyExchangeRates.TargetZone

open Filter Topology Set

/-! ## The target-zone ODE and its general solution -/

/-- A constancy lemma used for O&R (84), p. 572: a function with zero derivative on an open
interval is constant there. -/
theorem const_of_hasDerivAt_zero {f : ℝ → ℝ} {a b : ℝ} (h : ∀ x ∈ Ioo a b, HasDerivAt f 0 x)
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) : f x = f y :=
  IsOpen.is_const_of_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo
    (fun z hz => (h z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (h z hz).deriv) hx hy

/-- O&R (84), p. 572, and Exercise 5, p. 601: the candidate solutions
`G(k) = d + k + b₁e^{λ₁k} + b₂e^{λ₂k}` (`d = ημ`). -/
noncomputable def zoneSolution (d b₁ b₂ l₁ l₂ k : ℝ) : ℝ :=
  d + k + b₁ * Real.exp (l₁ * k) + b₂ * Real.exp (l₂ * k)

/-- O&R (84) and Exercise 5: if `λ₁, λ₂` are the roots of `cλ² + dλ − 1 = 0`
(`c = ηv²/2`, `d = ημ`), the candidates solve `G = k + dG′ + cG″`. -/
theorem zoneSolution_solves {c d l₁ l₂ : ℝ} (h1 : c * l₁ ^ 2 + d * l₁ - 1 = 0)
    (h2 : c * l₂ ^ 2 + d * l₂ - 1 = 0) (b₁ b₂ k : ℝ) :
    HasDerivAt (zoneSolution d b₁ b₂ l₁ l₂)
        (1 + b₁ * l₁ * Real.exp (l₁ * k) + b₂ * l₂ * Real.exp (l₂ * k)) k ∧
      HasDerivAt (fun x => 1 + b₁ * l₁ * Real.exp (l₁ * x) + b₂ * l₂ * Real.exp (l₂ * x))
        (b₁ * l₁ ^ 2 * Real.exp (l₁ * k) + b₂ * l₂ ^ 2 * Real.exp (l₂ * k)) k ∧
      zoneSolution d b₁ b₂ l₁ l₂ k =
        k + d * (1 + b₁ * l₁ * Real.exp (l₁ * k) + b₂ * l₂ * Real.exp (l₂ * k)) +
          c * (b₁ * l₁ ^ 2 * Real.exp (l₁ * k) + b₂ * l₂ ^ 2 * Real.exp (l₂ * k)) := by
  have e1 : ∀ l : ℝ, HasDerivAt (fun x => Real.exp (l * x)) (Real.exp (l * k) * l) k := fun l =>
    by simpa using ((hasDerivAt_id' k).const_mul l).exp
  refine ⟨?_, ?_, ?_⟩
  · have := ((((hasDerivAt_id' k).const_add d).add ((e1 l₁).const_mul b₁)).add
      ((e1 l₂).const_mul b₂))
    unfold zoneSolution; convert this using 1; ring
  · have := ((((e1 l₁).const_mul (b₁ * l₁)).const_add 1).add ((e1 l₂).const_mul (b₂ * l₂)))
    convert this using 1; ring
  · unfold zoneSolution
    linear_combination (-(b₁ * Real.exp (l₁ * k))) * h1 - (b₂ * Real.exp (l₂ * k)) * h2

/-- O&R (84), p. 572, and Exercise 5, p. 601 (**all solutions**): on an open interval, every
twice-differentiable solution of `G = k + dG′ + cG″` is `d + k + b₁e^{λ₁k} + b₂e^{λ₂k}`, where
`λ₁ ≠ λ₂` are the roots of `cλ² + dλ − 1 = 0`. -/
theorem zone_ode_general {c d l₁ l₂ a b : ℝ} (hc : 0 < c) (h1 : c * l₁ ^ 2 + d * l₁ - 1 = 0)
    (h2 : c * l₂ ^ 2 + d * l₂ - 1 = 0) (hne : l₁ ≠ l₂) (hab : a < b) {G G' G'' : ℝ → ℝ}
    (hG : ∀ k ∈ Ioo a b, HasDerivAt G (G' k) k) (hG' : ∀ k ∈ Ioo a b, HasDerivAt G' (G'' k) k)
    (hode : ∀ k ∈ Ioo a b, G k = k + d * G' k + c * G'' k) :
    ∃ b₁ b₂ : ℝ, ∀ k ∈ Ioo a b, G k = zoneSolution d b₁ b₂ l₁ l₂ k := by
  -- Vieta
  have hsum : c * (l₁ + l₂) + d = 0 := by
    have : (l₁ - l₂) * (c * (l₁ + l₂) + d) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  have hprod : c * (l₁ * l₂) = -1 := by linear_combination l₁ * hsum - h1
  have hl : l₂ - l₁ ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  set x₀ := (a + b) / 2 with hx₀
  have hx₀m : x₀ ∈ Ioo a b := ⟨by rw [hx₀]; linarith, by rw [hx₀]; linarith⟩
  set u : ℝ → ℝ := fun k => (G' k - 1 - l₁ * (G k - k - d)) * Real.exp (-l₂ * k) with hu
  have hu' : ∀ k ∈ Ioo a b, HasDerivAt u 0 k := by
    intro k hk
    have hw' : HasDerivAt (fun x => G' x - 1 - l₁ * (G x - x - d))
        (G'' k - l₁ * (G' k - 1)) k := by
      have := ((hG' k hk).sub_const 1).sub ((((hG k hk).sub (hasDerivAt_id' k)).sub_const
        d).const_mul l₁)
      convert this using 1
    have he : HasDerivAt (fun x => Real.exp (-l₂ * x)) (Real.exp (-l₂ * k) * (-l₂)) k := by
      simpa using ((hasDerivAt_id' k).const_mul (-l₂)).exp
    have := hw'.mul he
    convert this using 1
    have hG'' : c * G'' k = G k - k - d * G' k := by linarith [hode k hk]
    have hE := Real.exp_pos (-l₂ * k)
    have key : G'' k - l₁ * (G' k - 1) + (G' k - 1 - l₁ * (G k - k - d)) * (-l₂) = 0 := by
      have hcc : c ≠ 0 := hc.ne'
      have : c * (G'' k - l₁ * (G' k - 1) + (G' k - 1 - l₁ * (G k - k - d)) * (-l₂)) = 0 := by
        linear_combination hG'' - (G' k - 1) * hsum + (G k - k - d) * hprod
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hcc
      · exact h
    linear_combination (-(Real.exp (-l₂ * k))) * key
  obtain ⟨A, hAdef⟩ : ∃ A, A = u x₀ := ⟨_, rfl⟩
  have huA : ∀ k ∈ Ioo a b, u k = A := fun k hk => hAdef ▸ const_of_hasDerivAt_zero hu' hk hx₀m
  set v : ℝ → ℝ := fun k => (G k - k - d) * Real.exp (-l₁ * k) -
    A / (l₂ - l₁) * Real.exp ((l₂ - l₁) * k) with hv
  have hv' : ∀ k ∈ Ioo a b, HasDerivAt v 0 k := by
    intro k hk
    have hw : HasDerivAt (fun x => G x - x - d) (G' k - 1) k :=
      ((hG k hk).sub (hasDerivAt_id' k)).sub_const d
    have he1 : HasDerivAt (fun x => Real.exp (-l₁ * x)) (Real.exp (-l₁ * k) * (-l₁)) k := by
      simpa using ((hasDerivAt_id' k).const_mul (-l₁)).exp
    have he2 : HasDerivAt (fun x => Real.exp ((l₂ - l₁) * x))
        (Real.exp ((l₂ - l₁) * k) * (l₂ - l₁)) k := by
      simpa using ((hasDerivAt_id' k).const_mul (l₂ - l₁)).exp
    have := (hw.mul he1).sub (he2.const_mul (A / (l₂ - l₁)))
    convert this using 1
    have hA := huA k hk
    simp only [hu] at hA
    have x1 : Real.exp (-l₂ * k) * Real.exp ((l₂ - l₁) * k) = Real.exp (-l₁ * k) := by
      rw [← Real.exp_add]; congr 1; ring
    have hAl : A / (l₂ - l₁) * (l₂ - l₁) = A := div_mul_cancel₀ _ hl
    linear_combination (G' k - 1 - l₁ * (G k - k - d)) * x1 -
      Real.exp ((l₂ - l₁) * k) * hA + Real.exp ((l₂ - l₁) * k) * hAl
  obtain ⟨V, hVdef⟩ : ∃ V, V = v x₀ := ⟨_, rfl⟩
  refine ⟨V, A / (l₂ - l₁), fun k hk => ?_⟩
  have hvk : v k = V := hVdef ▸ const_of_hasDerivAt_zero hv' hk hx₀m
  simp only [hv] at hvk
  have y1 : Real.exp (-l₁ * k) * Real.exp (l₁ * k) = 1 := by
    rw [← Real.exp_add]; simp
  have y2 : Real.exp ((l₂ - l₁) * k) * Real.exp (l₁ * k) = Real.exp (l₂ * k) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold zoneSolution
  linear_combination (Real.exp (l₁ * k)) * hvk - (G k - k - d) * y1 +
    (A / (l₂ - l₁)) * y2

/-- O&R p. 572: `λ = √(2/(ηv²))` satisfies `(ηv²/2)λ² = 1`. -/
theorem lambda_spec {η v : ℝ} (hη : 0 < η) (hv : 0 < v) :
    0 < Real.sqrt (2 / (η * v ^ 2)) ∧ η * v ^ 2 / 2 * Real.sqrt (2 / (η * v ^ 2)) ^ 2 = 1 := by
  have hpos : 0 < 2 / (η * v ^ 2) := by positivity
  refine ⟨Real.sqrt_pos.2 hpos, ?_⟩
  rw [Real.sq_sqrt hpos.le]; field_simp

/-- O&R (84), p. 572 (no drift): every twice-differentiable solution of
`G = k + (ηv²/2)G″` on an open interval is `k + b₁e^{λk} + b₂e^{−λk}`,
`λ = √(2/(ηv²))`. -/
theorem zone_ode_no_drift {η v a b : ℝ} (hη : 0 < η) (hv : 0 < v) (hab : a < b)
    {G G' G'' : ℝ → ℝ} (hG : ∀ k ∈ Ioo a b, HasDerivAt G (G' k) k)
    (hG' : ∀ k ∈ Ioo a b, HasDerivAt G' (G'' k) k)
    (hode : ∀ k ∈ Ioo a b, G k = k + η * v ^ 2 / 2 * G'' k) :
    ∃ b₁ b₂ : ℝ, ∀ k ∈ Ioo a b, G k = k + b₁ * Real.exp (Real.sqrt (2 / (η * v ^ 2)) * k) +
      b₂ * Real.exp (-Real.sqrt (2 / (η * v ^ 2)) * k) := by
  obtain ⟨hl, hl2⟩ := lambda_spec hη hv
  set l := Real.sqrt (2 / (η * v ^ 2))
  obtain ⟨b₁, b₂, h⟩ := zone_ode_general (c := η * v ^ 2 / 2) (d := 0) (l₁ := l) (l₂ := -l)
    (by positivity) (by linear_combination hl2) (by linear_combination hl2)
    (by intro h; linarith) hab hG hG' (fun k hk => by rw [hode k hk]; ring)
  exact ⟨b₁, b₂, fun k hk => by rw [h k hk]; unfold zoneSolution; ring⟩

/-- O&R Exercise 5, p. 601: the roots `λ₁,₂ = [−ημ ± √(η²μ² + 2ηv²)]/(ηv²)` of
`(ηv²/2)λ² + ημλ − 1 = 0`. -/
noncomputable def driftRoot (η μ v : ℝ) (sgn : ℝ) : ℝ :=
  (-(η * μ) + sgn * Real.sqrt ((η * μ) ^ 2 + 2 * η * v ^ 2)) / (η * v ^ 2)

/-- O&R Exercise 5, p. 601: both roots solve the characteristic equation. -/
theorem driftRoot_spec {η μ v : ℝ} (hη : 0 < η) (hv : 0 < v) {sgn : ℝ} (hs : sgn ^ 2 = 1) :
    η * v ^ 2 / 2 * driftRoot η μ v sgn ^ 2 + η * μ * driftRoot η μ v sgn - 1 = 0 := by
  have hq : 0 ≤ (η * μ) ^ 2 + 2 * η * v ^ 2 := by positivity
  have hD : 0 < η * v ^ 2 := by positivity
  have key : (sgn * Real.sqrt ((η * μ) ^ 2 + 2 * η * v ^ 2)) ^ 2 =
      (η * μ) ^ 2 + η * v ^ 2 * 2 := by
    rw [mul_pow, hs, one_mul, Real.sq_sqrt hq]; ring
  unfold driftRoot
  generalize Real.sqrt ((η * μ) ^ 2 + 2 * η * v ^ 2) = R at key ⊢
  field_simp
  linear_combination key

/-- O&R Exercise 5, p. 601: `λ₁ > 0 > λ₂`, and `λ₁λ₂ = −2/(ηv²)`. -/
theorem driftRoot_props {η μ v : ℝ} (hη : 0 < η) (hv : 0 < v) :
    0 < driftRoot η μ v 1 ∧ driftRoot η μ v (-1) < 0 ∧
      driftRoot η μ v 1 * driftRoot η μ v (-1) = -2 / (η * v ^ 2) := by
  have hq : 0 ≤ (η * μ) ^ 2 + 2 * η * v ^ 2 := by positivity
  have hsq := Real.sq_sqrt hq
  have hD : 0 < η * v ^ 2 := by positivity
  have hgt : |η * μ| < Real.sqrt ((η * μ) ^ 2 + 2 * η * v ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith [mul_pos hη (pow_pos hv 2)])
  have ha := abs_lt.1 hgt
  refine ⟨?_, ?_, ?_⟩
  · unfold driftRoot; apply div_pos _ hD; linarith [ha.2, ha.1]
  · unfold driftRoot; apply div_neg_of_neg_of_pos _ hD; linarith [ha.2, ha.1]
  · have key : Real.sqrt ((η * μ) ^ 2 + 2 * η * v ^ 2) ^ 2 = (η * μ) ^ 2 + η * v ^ 2 * 2 := by
      rw [hsq]; ring
    unfold driftRoot
    generalize Real.sqrt ((η * μ) ^ 2 + 2 * η * v ^ 2) = R at key ⊢
    field_simp
    linear_combination -key

/-- O&R Exercise 5, p. 601: with `μ = 0` the roots are `±√(2/(ηv²))`. -/
theorem driftRoot_no_drift {η v : ℝ} (hη : 0 < η) (hv : 0 < v) :
    driftRoot η 0 v 1 = Real.sqrt (2 / (η * v ^ 2)) ∧
      driftRoot η 0 v (-1) = -Real.sqrt (2 / (η * v ^ 2)) := by
  have hD : 0 < η * v ^ 2 := by positivity
  have e : Real.sqrt (2 / (η * v ^ 2)) = Real.sqrt (2 * η * v ^ 2) / (η * v ^ 2) := by
    have h1 : Real.sqrt (2 * η * v ^ 2) =
        Real.sqrt (2 / (η * v ^ 2)) * Real.sqrt ((η * v ^ 2) ^ 2) := by
      rw [← Real.sqrt_mul (by positivity)]; congr 1; field_simp
    rw [Real.sqrt_sq hD.le] at h1
    rw [h1]; field_simp
  unfold driftRoot
  simp only [mul_zero, neg_zero, zero_add, one_mul, neg_one_mul, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [e]
  constructor
  · rfl
  · ring

/-- O&R §8.6, p. 577: for `λ₁ > 0 > λ₂`, `G(k) − k − d → 0` as `k → −∞` iff `b₂ = 0`
(so a one-sided zone has `S = k + b₁e^{λk}`). -/
theorem tendsto_atBot_iff {d b₁ b₂ l₁ l₂ : ℝ} (hl₁ : 0 < l₁) (hl₂ : l₂ < 0) :
    Tendsto (fun k => zoneSolution d b₁ b₂ l₁ l₂ k - k - d) atBot (𝓝 0) ↔ b₂ = 0 := by
  have h1 : Tendsto (fun k => Real.exp (l₁ * k)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hl₁)
  have h2 : Tendsto (fun k => Real.exp (-l₂ * k)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot (by linarith))
  have e : ∀ k, zoneSolution d b₁ b₂ l₁ l₂ k - k - d =
      b₁ * Real.exp (l₁ * k) + b₂ * Real.exp (l₂ * k) := fun k => by unfold zoneSolution; ring
  simp_rw [e]
  constructor
  · intro h
    have h3 : Tendsto (fun k => b₂ * Real.exp (l₂ * k)) atBot (𝓝 0) := by
      have := h.sub (h1.const_mul b₁)
      simpa using this
    have h4 := h3.mul h2
    rw [zero_mul] at h4
    have h5 : (fun k => b₂ * Real.exp (l₂ * k) * Real.exp (-l₂ * k)) = fun _ => b₂ := by
      funext k; rw [mul_assoc, ← Real.exp_add]; simp
    rw [h5] at h4
    exact tendsto_nhds_unique tendsto_const_nhds h4
  · intro h; subst h; simpa using h1.const_mul b₁

/-! ## The symmetric target zone -/

/-- O&R (85), p. 572: the symmetric-zone locus `S(k) = k − b[e^{λk} − e^{−λk}] =
k − 2b sinh(λk)`. -/
noncomputable def symS (l b k : ℝ) : ℝ := k - 2 * b * Real.sinh (l * k)

/-- O&R (85), p. 572: the two forms of the locus agree. -/
theorem symS_eq_exp (l b k : ℝ) :
    symS l b k = k - b * (Real.exp (l * k) - Real.exp (-(l * k))) := by
  unfold symS; rw [Real.sinh_eq]; ring

/-- O&R p. 575: `S′(k) = 1 − 2bλ cosh(λk)`. -/
theorem hasDerivAt_symS (l b k : ℝ) :
    HasDerivAt (symS l b) (1 - 2 * b * l * Real.cosh (l * k)) k := by
  have := (hasDerivAt_id' k).sub ((((hasDerivAt_id' k).const_mul l).sinh).const_mul (2 * b))
  unfold symS; convert this using 1; ring

/-- O&R p. 575: `S″(k) = −2bλ² sinh(λk)`. -/
theorem hasDerivAt_symS' (l b k : ℝ) :
    HasDerivAt (fun x => 1 - 2 * b * l * Real.cosh (l * x))
      (-(2 * b * l ^ 2 * Real.sinh (l * k))) k := by
  have := ((((hasDerivAt_id' k).const_mul l).cosh).const_mul (2 * b * l)).const_sub 1
  convert this using 1; ring

/-- O&R (84)–(85), p. 572: `S` solves (84) `S = k + (1/λ²)S″` (i.e. `(ηv²/2) = 1/λ²`). -/
theorem symS_solves_ode {l : ℝ} (hl : l ≠ 0) (b k : ℝ) :
    symS l b k = k + 1 / l ^ 2 * (-(2 * b * l ^ 2 * Real.sinh (l * k))) := by
  unfold symS; field_simp; ring

/-- O&R (85), Figure 8.5: `S` is odd (symmetric zone). -/
theorem symS_odd (l b k : ℝ) : symS l b (-k) = -symS l b k := by
  unfold symS; rw [mul_neg, Real.sinh_neg]; ring

/-- O&R *8.5.5, p. 575: the function `φ(k) = k − tanh(λk)/λ` whose root gives `k̄`. -/
noncomputable def edgeMap (l k : ℝ) : ℝ := k - Real.sinh (l * k) / (l * Real.cosh (l * k))

/-- O&R *8.5.5: `φ′(k) = tanh²(λk)`. -/
theorem hasDerivAt_edgeMap {l : ℝ} (hl : 0 < l) (k : ℝ) :
    HasDerivAt (edgeMap l) ((Real.sinh (l * k) / Real.cosh (l * k)) ^ 2) k := by
  have hs := ((hasDerivAt_id' k).const_mul l).sinh
  have hc := (((hasDerivAt_id' k).const_mul l).cosh).const_mul l
  have hcne : l * Real.cosh (l * k) ≠ 0 := mul_ne_zero hl.ne' (Real.cosh_pos _).ne'
  have := (hasDerivAt_id' k).sub (hs.div hc hcne)
  unfold edgeMap
  convert this using 1
  have hc0 := (Real.cosh_pos (l * k)).ne'
  field_simp
  ring

/-- O&R *8.5.5: `φ` is continuous. -/
theorem continuous_edgeMap {l : ℝ} (hl : 0 < l) : Continuous (edgeMap l) :=
  continuous_iff_continuousAt.2 fun k => (hasDerivAt_edgeMap hl k).continuousAt

/-- O&R *8.5.5: `φ` is strictly increasing on `[0, ∞)`. -/
theorem edgeMap_strictMonoOn {l : ℝ} (hl : 0 < l) : StrictMonoOn (edgeMap l) (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) (continuous_edgeMap hl).continuousOn
    fun x hx => ?_
  rw [interior_Ici] at hx
  rw [(hasDerivAt_edgeMap hl x).deriv]
  have : 0 < Real.sinh (l * x) := Real.sinh_pos_iff.2 (mul_pos hl hx)
  positivity

/-- O&R *8.5.5: `k − 1/λ < φ(k) < k` for `k > 0` (`0 < tanh < 1`). -/
theorem edgeMap_bounds {l : ℝ} (hl : 0 < l) {k : ℝ} (hk : 0 < k) :
    k - 1 / l < edgeMap l k ∧ edgeMap l k < k := by
  have hs : 0 < Real.sinh (l * k) := Real.sinh_pos_iff.2 (mul_pos hl hk)
  have hlt := Real.sinh_lt_cosh (l * k)
  have hc := Real.cosh_pos (l * k)
  unfold edgeMap
  constructor
  · have : Real.sinh (l * k) / (l * Real.cosh (l * k)) < 1 / l := by
      rw [div_lt_div_iff₀ (by positivity) hl]; nlinarith
    linarith
  · have : 0 < Real.sinh (l * k) / (l * Real.cosh (l * k)) := by positivity
    linarith

/-- O&R *8.5.5, p. 575 (**existence and uniqueness of the band edge**): for `ē > 0` there is a
unique `k̄ > 0` with `k̄ − tanh(λk̄)/λ = ē`. -/
theorem existsUnique_edge {l : ℝ} (hl : 0 < l) {ebar : ℝ} (he : 0 < ebar) :
    ∃! kb : ℝ, 0 < kb ∧ edgeMap l kb = ebar := by
  have hx : 0 ≤ ebar + 1 / l := by positivity
  have h0 : edgeMap l 0 = 0 := by simp [edgeMap]
  have h1 : ebar ≤ edgeMap l (ebar + 1 / l) := by
    have := (edgeMap_bounds hl (show 0 < ebar + 1 / l by positivity)).1; linarith
  obtain ⟨kb, hkb, hval⟩ := intermediate_value_Icc hx (continuous_edgeMap hl).continuousOn
    ⟨by rw [h0]; exact he.le, h1⟩
  have hkb0 : 0 < kb := by
    rcases eq_or_lt_of_le hkb.1 with h | h
    · rw [← h, h0] at hval; linarith
    · exact h
  refine ⟨kb, ⟨hkb0, hval⟩, fun y hy => ?_⟩
  exact (edgeMap_strictMonoOn hl).injOn (le_of_lt hy.1) (le_of_lt hkb0) (hy.2.trans hval.symm)

/-- O&R *8.5.5, p. 575 (**the symmetric target-zone solution exists and is unique**): there is
exactly one pair `(b, k̄)` with `k̄ > 0`, value matching `S(k̄) = ē` and smooth pasting
`S′(k̄) = 0`; it has `b = 1/(2λ cosh λk̄)` and `k̄ − tanh(λk̄)/λ = ē`. -/
theorem existsUnique_symmetric_zone {l : ℝ} (hl : 0 < l) {ebar : ℝ} (he : 0 < ebar) :
    ∃! p : ℝ × ℝ, 0 < p.2 ∧ symS l p.1 p.2 = ebar ∧
      1 - 2 * p.1 * l * Real.cosh (l * p.2) = 0 := by
  obtain ⟨kb, ⟨hkb, hval⟩, huniq⟩ := existsUnique_edge hl he
  have hc := Real.cosh_pos (l * kb)
  refine ⟨(1 / (2 * l * Real.cosh (l * kb)), kb), ⟨hkb, ?_, ?_⟩, ?_⟩
  · simp only; unfold symS; unfold edgeMap at hval; rw [← hval]; field_simp
  · simp only; field_simp; ring
  · rintro ⟨b, k⟩ ⟨hk, hS, hS'⟩
    simp only at hk hS hS'
    have hb : b = 1 / (2 * l * Real.cosh (l * k)) := by
      have := Real.cosh_pos (l * k)
      field_simp; linarith
    have hedge : edgeMap l k = ebar := by
      unfold edgeMap; unfold symS at hS; rw [← hS, hb]; field_simp
    have := huniq k ⟨hk, hedge⟩
    subst this
    rw [hb]

/-- O&R Figure 8.5: the properties of the symmetric solution. Given `k̄ > 0` and
`b = 1/(2λ cosh λk̄)` (smooth pasting): `S′(k) = 1 − cosh(λk)/cosh(λk̄)`. -/
theorem symS_deriv_formula {l kb : ℝ} (hl : 0 < l) (k : ℝ) :
    1 - 2 * (1 / (2 * l * Real.cosh (l * kb))) * l * Real.cosh (l * k) =
      1 - Real.cosh (l * k) / Real.cosh (l * kb) := by
  have := (Real.cosh_pos (l * kb)).ne'
  field_simp

/-- O&R Figure 8.5, properties 2–3: `S′(k) ≥ 0` iff `|k| ≤ k̄` (so `0 ≤ S′` on the band),
`S′(k) = 0` iff `|k| = k̄` (smooth pasting exactly at the edges), and `S′ < 1` everywhere
(less sensitive than the free float). -/
theorem symS_deriv_props {l kb : ℝ} (hl : 0 < l) (hkb : 0 < kb) (k : ℝ) :
    (0 ≤ 1 - Real.cosh (l * k) / Real.cosh (l * kb) ↔ |k| ≤ kb) ∧
      (1 - Real.cosh (l * k) / Real.cosh (l * kb) = 0 ↔ |k| = kb) ∧
      1 - Real.cosh (l * k) / Real.cosh (l * kb) < 1 := by
  have hc := Real.cosh_pos (l * kb)
  have hck := Real.cosh_pos (l * k)
  have habs : ∀ x, |l * x| = l * |x| := fun x => by rw [abs_mul, abs_of_pos hl]
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_nonneg, div_le_one hc, Real.cosh_le_cosh, habs, habs, abs_of_pos hkb]
    constructor <;> intro h <;> nlinarith
  · rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq hc.ne']
    constructor
    · intro h
      have h1 : Real.cosh (l * k) ≤ Real.cosh (l * kb) := h.le
      have h2 : Real.cosh (l * kb) ≤ Real.cosh (l * k) := h.ge
      rw [Real.cosh_le_cosh, habs, habs, abs_of_pos hkb] at h1 h2
      nlinarith
    · intro h
      rw [← Real.cosh_abs, habs, h, ← Real.cosh_abs (l * kb), habs, abs_of_pos hkb]
  · have : 0 < Real.cosh (l * k) / Real.cosh (l * kb) := div_pos hck hc
    linarith

/-- O&R Figure 8.5: `S` (with smooth pasting) is strictly increasing on `[−k̄, k̄]`. -/
theorem symS_strictMonoOn {l kb : ℝ} (hl : 0 < l) (hkb : 0 < kb) :
    StrictMonoOn (symS l (1 / (2 * l * Real.cosh (l * kb)))) (Icc (-kb) kb) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (continuous_iff_continuousAt.2 fun x => (hasDerivAt_symS _ _ x).continuousAt).continuousOn
    fun x hx => ?_
  rw [interior_Icc] at hx
  rw [(hasDerivAt_symS _ _ x).deriv, symS_deriv_formula hl]
  have hx' : |x| < kb := abs_lt.2 hx
  have hc := Real.cosh_pos (l * kb)
  rw [sub_pos, div_lt_one hc, Real.cosh_lt_cosh, abs_mul, abs_mul, abs_of_pos hl,
    abs_of_pos hkb]
  nlinarith

/-- O&R Figure 8.5, property 1: with value matching and smooth pasting, `S(±k̄) = ±ē` and `S`
maps `[−k̄, k̄]` onto `[−ē, ē]`. -/
theorem symS_maps_band {l kb ebar : ℝ} (hl : 0 < l) (hkb : 0 < kb)
    (hS : symS l (1 / (2 * l * Real.cosh (l * kb))) kb = ebar) :
    symS l (1 / (2 * l * Real.cosh (l * kb))) (-kb) = -ebar ∧
      symS l (1 / (2 * l * Real.cosh (l * kb))) '' Icc (-kb) kb = Icc (-ebar) ebar := by
  set b := 1 / (2 * l * Real.cosh (l * kb))
  have hodd : symS l b (-kb) = -ebar := by rw [symS_odd, hS]
  refine ⟨hodd, ?_⟩
  have hmono := symS_strictMonoOn hl hkb
  have hcont : ContinuousOn (symS l b) (Icc (-kb) kb) :=
    (continuous_iff_continuousAt.2 fun x => (hasDerivAt_symS _ _ x).continuousAt).continuousOn
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    constructor
    · rw [← hodd]; exact hmono.monotoneOn ⟨le_rfl, by linarith⟩ hx hx.1
    · rw [← hS]; exact hmono.monotoneOn hx ⟨by linarith, le_rfl⟩ hx.2
  · have := intermediate_value_Icc (by linarith : -kb ≤ kb) hcont
    rw [hodd, hS] at this
    exact this

/-- O&R p. 575: `S″ < 0` on `(0, ∞)` (concave above the centre) and `S″ > 0` on `(−∞, 0)`
(convex below), for `b > 0`. -/
theorem symS_curvature {l b : ℝ} (hl : 0 < l) (hb : 0 < b) (k : ℝ) :
    (0 < k → -(2 * b * l ^ 2 * Real.sinh (l * k)) < 0) ∧
      (k < 0 → 0 < -(2 * b * l ^ 2 * Real.sinh (l * k))) := by
  constructor
  · intro hk
    have := Real.sinh_pos_iff.2 (mul_pos hl hk)
    have : 0 < 2 * b * l ^ 2 * Real.sinh (l * k) := by positivity
    linarith
  · intro hk
    have h1 : Real.sinh (l * k) < 0 := by
      have := Real.sinh_lt_sinh.2 (show l * k < 0 by nlinarith)
      simpa using this
    have : 0 < 2 * b * l ^ 2 := by positivity
    nlinarith

/-- O&R p. 575 (**honeymoon effect**): for `b > 0`, `|S(k)| < |k|` for `0 < |k| ≤ k̄`; more
precisely `0 < S(k) < k` for `0 < k ≤ k̄` (and symmetrically). -/
theorem honeymoon {l kb : ℝ} (hl : 0 < l) (hkb : 0 < kb) {k : ℝ} (hk : 0 < k) (hkk : k ≤ kb) :
    0 < symS l (1 / (2 * l * Real.cosh (l * kb))) k ∧
      symS l (1 / (2 * l * Real.cosh (l * kb))) k < k := by
  have hb : 0 < 1 / (2 * l * Real.cosh (l * kb)) := by
    have := Real.cosh_pos (l * kb); positivity
  constructor
  · have h0 : symS l (1 / (2 * l * Real.cosh (l * kb))) 0 = 0 := by simp [symS]
    rw [← h0]
    exact symS_strictMonoOn hl hkb ⟨by linarith, by linarith⟩ ⟨by linarith, hkk⟩ hk
  · unfold symS
    have := Real.sinh_pos_iff.2 (mul_pos hl hk)
    have : 0 < 2 * (1 / (2 * l * Real.cosh (l * kb))) * Real.sinh (l * k) := by positivity
    linarith

/-- O&R p. 575–576: the fundamentals band is strictly wider than the currency band, and not
by more than `1/λ`: `ē < k̄ < ē + 1/λ`. -/
theorem edge_bounds {l kb ebar : ℝ} (hl : 0 < l) (hkb : 0 < kb) (h : edgeMap l kb = ebar) :
    ebar < kb ∧ kb < ebar + 1 / l := by
  have := edgeMap_bounds hl hkb
  constructor <;> linarith

/-- O&R p. 575: as the variance of fundamentals vanishes (`λ → ∞`), the fundamentals band
shrinks to the currency band: `k̄(λ) → ē`. -/
theorem edge_tendsto {ebar : ℝ} {kb : ℝ → ℝ}
    (hkb : ∀ l, 0 < l → 0 < kb l ∧ edgeMap l (kb l) = ebar) :
    Tendsto kb atTop (𝓝 ebar) := by
  have hup : Tendsto (fun l : ℝ => ebar + 1 / l) atTop (𝓝 ebar) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id :
      Tendsto (fun l : ℝ => (1 : ℝ) / l) atTop (𝓝 0))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with l hl
    exact (edge_bounds hl (hkb l hl).1 (hkb l hl).2).1.le
  · filter_upwards [eventually_gt_atTop 0] with l hl
    exact (edge_bounds hl (hkb l hl).1 (hkb l hl).2).2.le

/-- O&R p. 572: `λ = √(2/(ηv²)) → ∞` as `v → 0⁺`. -/
theorem lambda_tendsto {η : ℝ} (hη : 0 < η) :
    Tendsto (fun v => Real.sqrt (2 / (η * v ^ 2))) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun v : ℝ => η * v ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun v : ℝ => η * v ^ 2) (𝓝 0) (𝓝 (η * 0 ^ 2)) :=
        ((continuous_const.mul (continuous_pow 2)).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with v hv
      simp only [mem_Ioi] at hv ⊢; positivity
  have h2 : Tendsto (fun v : ℝ => 2 / (η * v ^ 2)) (𝓝[>] 0) atTop :=
    (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop (by norm_num : (0 : ℝ) < 2) |>.congr
      fun v => by simp [div_eq_mul_inv]
  exact Real.tendsto_sqrt_atTop.comp h2

/-! ## The discrete target zone (a finite Markov chain) -/

/-- O&R (79), (81), pp. 570–571, discretised: an equilibrium of the lattice target zone.
Fundamentals are `k_i = iΔ`, `|i| ≤ N`; each period they move `±Δ` with probability ½, the
step out of the band being suppressed by intervention; the equilibrium condition is
`e_i = k_i + (η/h)(E[e_next | i] − e_i)` with `a = η/h`. -/
def IsLatticeEqm (a Δ : ℝ) (N : ℤ) (e : ℤ → ℝ) : Prop :=
  ∀ i : ℤ, -N ≤ i → i ≤ N →
    e i = i * Δ + a * ((e (min (i + 1) N) + e (max (i - 1) (-N))) / 2 - e i)

/-- O&R §8.5 (discrete version): **uniqueness**: two lattice equilibria coincide on the band
(the equilibrium system is strictly diagonally dominant; discrete maximum principle). -/
theorem latticeEqm_unique {a Δ : ℝ} (ha : 0 < a) {N : ℤ} (hN : 0 ≤ N) {e e' : ℤ → ℝ}
    (he : IsLatticeEqm a Δ N e) (he' : IsLatticeEqm a Δ N e') :
    ∀ i : ℤ, -N ≤ i → i ≤ N → e i = e' i := by
  set d : ℤ → ℝ := fun i => e i - e' i with hd
  have hdeq : ∀ i : ℤ, -N ≤ i → i ≤ N →
      (1 + a) * d i = a * ((d (min (i + 1) N) + d (max (i - 1) (-N))) / 2) := by
    intro i h1 h2
    have := he i h1 h2; have := he' i h1 h2
    simp only [hd]; linarith
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image (Finset.Icc (-N) N) (fun i => |d i|)
    ⟨0, Finset.mem_Icc.2 ⟨by omega, hN⟩⟩
  rw [Finset.mem_Icc] at hi₀
  have hup : min (i₀ + 1) N ∈ Finset.Icc (-N) N := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hdn : max (i₀ - 1) (-N) ∈ Finset.Icc (-N) N := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have h0 : |d i₀| = 0 := by
    have key := hdeq i₀ hi₀.1 hi₀.2
    have hb1 := hmax _ hup
    have hb2 := hmax _ hdn
    have : (1 + a) * |d i₀| ≤ a * |d i₀| := by
      calc (1 + a) * |d i₀| = |(1 + a) * d i₀| := by
            rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 + a by linarith)]
        _ = |a * ((d (min (i₀ + 1) N) + d (max (i₀ - 1) (-N))) / 2)| := by rw [key]
        _ ≤ a * ((|d (min (i₀ + 1) N)| + |d (max (i₀ - 1) (-N))|) / 2) := by
            rw [abs_mul, abs_of_pos ha, abs_div, abs_two]
            gcongr; exact abs_add_le _ _
        _ ≤ a * |d i₀| := by gcongr; linarith
    linarith [abs_nonneg (d i₀)]
  intro i h1 h2
  have := hmax i (Finset.mem_Icc.2 ⟨h1, h2⟩)
  rw [h0] at this
  have : d i = 0 := abs_nonpos_iff.1 this
  simp only [hd] at this; linarith

/-- O&R §8.5 (discrete version): the characteristic root: there is `θ > 0` with
`cosh θ = 1 + 1/a`. -/
theorem exists_theta {a : ℝ} (ha : 0 < a) : ∃ θ : ℝ, 0 < θ ∧ Real.cosh θ = 1 + 1 / a := by
  set c := 1 + 1 / a with hc
  have hc1 : 1 < c := by
    have : 0 < 1 / a := by positivity
    rw [hc]; linarith
  have hcc : c ≤ Real.cosh c := by
    have h1 := Real.quadratic_le_exp_of_nonneg (show 0 ≤ c by linarith)
    have h2 := Real.exp_pos (-c)
    rw [Real.cosh_eq]; nlinarith
  obtain ⟨θ, hθ, hval⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ c by linarith)
    Real.continuous_cosh.continuousOn ⟨by rw [Real.cosh_zero]; linarith, hcc⟩
  refine ⟨θ, ?_, hval⟩
  rcases eq_or_lt_of_le hθ.1 with h | h
  · rw [← h, Real.cosh_zero] at hval; linarith
  · exact h

/-- O&R §8.5 (discrete version): the closed-form lattice solution `e_i = iΔ − D sinh(θi)`. -/
noncomputable def latticeSol (Δ θ D : ℝ) (i : ℤ) : ℝ := i * Δ - D * Real.sinh (θ * i)

/-- O&R §8.5 (discrete version): the smooth-pasting coefficient
`D = Δ/(sinh θ(N+1) − sinh θN)`. -/
noncomputable def latticeCoeff (Δ θ : ℝ) (N : ℤ) : ℝ :=
  Δ / (Real.sinh (θ * (N + 1)) - Real.sinh (θ * N))

/-- A hyperbolic identity used for the lattice solution:
`sinh(x + θ) + sinh(x − θ) = 2 sinh x cosh θ`. -/
theorem sinh_add_add_sinh_sub (x θ : ℝ) :
    Real.sinh (x + θ) + Real.sinh (x - θ) = 2 * Real.sinh x * Real.cosh θ := by
  rw [Real.sinh_add, Real.sinh_sub]; ring

/-- A hyperbolic identity used for the lattice increments:
`sinh(u + v) − sinh(u − v) = 2 cosh u sinh v`. -/
theorem sinh_add_sub_sinh_sub (u v : ℝ) :
    Real.sinh (u + v) - Real.sinh (u - v) = 2 * Real.cosh u * Real.sinh v := by
  rw [Real.sinh_add, Real.sinh_sub]; ring

/-- O&R §8.5 (discrete version): `sinh θ(j+1) − sinh θj = 2 cosh(θ(j+½)) sinh(θ/2)`. -/
theorem sinh_step (θ x : ℝ) :
    Real.sinh (θ * (x + 1)) - Real.sinh (θ * x) =
      2 * Real.cosh (θ * (x + 1 / 2)) * Real.sinh (θ / 2) := by
  rw [← sinh_add_sub_sinh_sub]; congr 2 <;> ring

/-- O&R §8.5 (discrete version): the smooth-pasting coefficient is positive. -/
theorem latticeCoeff_pos {Δ θ : ℝ} (hΔ : 0 < Δ) (hθ : 0 < θ) (N : ℤ) :
    0 < latticeCoeff Δ θ N := by
  unfold latticeCoeff
  rw [sinh_step]
  have := Real.sinh_pos_iff.2 (show 0 < θ / 2 by linarith)
  have := Real.cosh_pos (θ * (N + 1 / 2))
  positivity

/-- O&R §8.5 (discrete version): **existence**: the closed form solves the lattice equilibrium
conditions, interior and boundary (`N ≥ 1`, `cosh θ = 1 + 1/a`). -/
theorem latticeSol_isEqm {a Δ θ : ℝ} (ha : 0 < a) (hΔ : 0 < Δ) (hθ : 0 < θ)
    (hcosh : Real.cosh θ = 1 + 1 / a) {N : ℤ} (hN : 1 ≤ N) :
    IsLatticeEqm a Δ N (latticeSol Δ θ (latticeCoeff Δ θ N)) := by
  set D := latticeCoeff Δ θ N with hD
  have hDdef : D * (Real.sinh (θ * (N + 1)) - Real.sinh (θ * N)) = Δ := by
    rw [hD]; unfold latticeCoeff
    have : 0 < Real.sinh (θ * (N + 1)) - Real.sinh (θ * N) := by
      rw [sinh_step]
      have := Real.sinh_pos_iff.2 (show 0 < θ / 2 by linarith)
      have := Real.cosh_pos (θ * (N + 1 / 2))
      positivity
    field_simp
  have hid : ∀ x : ℝ, Real.sinh (θ * (x + 1)) + Real.sinh (θ * (x - 1)) =
      2 * Real.sinh (θ * x) * (1 + 1 / a) := by
    intro x; rw [← hcosh, ← sinh_add_add_sinh_sub]; congr 2 <;> ring
  have ha1 : a * (1 / a) = 1 := by field_simp
  intro i h1 h2
  unfold latticeSol
  rcases eq_or_lt_of_le h2 with hi | hi
  · -- the upper boundary `i = N`
    subst hi
    rw [min_eq_right (by omega), max_eq_left (by omega)]
    push_cast
    have := hid (i : ℝ)
    linear_combination (-(a / 2)) * hDdef + (a * D / 2) * this + D * Real.sinh (θ * i) * ha1
  rcases eq_or_lt_of_le h1 with hi' | hi'
  · -- the lower boundary `i = −N`
    rw [← hi', min_eq_left (by omega), max_eq_right (by omega)]
    push_cast
    have := hid (N : ℝ)
    have e1 : Real.sinh (θ * (-(N : ℝ) + 1)) = -Real.sinh (θ * (N - 1)) := by
      rw [← Real.sinh_neg]; congr 1; ring
    have e2 : Real.sinh (θ * (-(N : ℝ))) = -Real.sinh (θ * N) := by
      rw [← Real.sinh_neg]; congr 1; ring
    rw [e1, e2]
    linear_combination (a / 2) * hDdef - (a * D / 2) * this - D * Real.sinh (θ * N) * ha1
  · -- interior nodes
    rw [min_eq_left (by omega), max_eq_left (by omega)]
    push_cast
    have := hid (i : ℝ)
    linear_combination (a * D / 2) * this + D * Real.sinh (θ * i) * ha1

/-- O&R §8.5 (discrete version): **existence and uniqueness** of the lattice equilibrium. -/
theorem latticeEqm_existsUnique {a Δ : ℝ} (ha : 0 < a) (hΔ : 0 < Δ) {N : ℤ} (hN : 1 ≤ N) :
    ∃ e : ℤ → ℝ, IsLatticeEqm a Δ N e ∧
      ∀ e' : ℤ → ℝ, IsLatticeEqm a Δ N e' → ∀ i : ℤ, -N ≤ i → i ≤ N → e' i = e i := by
  obtain ⟨θ, hθ, hcosh⟩ := exists_theta ha
  have he := latticeSol_isEqm ha hΔ hθ hcosh hN
  exact ⟨_, he, fun e' he' => latticeEqm_unique ha (by omega) he' he⟩

/-- O&R Figure 8.5 (discrete version): the lattice solution is odd (symmetric zone). -/
theorem latticeSol_odd (Δ θ D : ℝ) (i : ℤ) : latticeSol Δ θ D (-i) = -latticeSol Δ θ D i := by
  unfold latticeSol; push_cast; rw [mul_neg, Real.sinh_neg]; ring

/-- O&R p. 575 (discrete version): the increments of the lattice solution are
`e_{i+1} − e_i = Δ(1 − cosh θ(i+½)/cosh θ(N+½))`, the discrete analogue of
`S′(k) = 1 − cosh λk/cosh λk̄` (with `k̄` at `N + ½`). -/
theorem latticeSol_increment {Δ θ : ℝ} (hθ : 0 < θ) (N i : ℤ) :
    latticeSol Δ θ (latticeCoeff Δ θ N) (i + 1) - latticeSol Δ θ (latticeCoeff Δ θ N) i =
      Δ * (1 - Real.cosh (θ * (i + 1 / 2)) / Real.cosh (θ * (N + 1 / 2))) := by
  unfold latticeSol latticeCoeff
  push_cast
  have h1 := sinh_step θ (i : ℝ)
  have h2 := sinh_step θ (N : ℝ)
  have hs := Real.sinh_pos_iff.2 (show 0 < θ / 2 by linarith)
  have hc := Real.cosh_pos (θ * (N + 1 / 2))
  rw [h2]
  have e : Δ / (2 * Real.cosh (θ * (N + 1 / 2)) * Real.sinh (θ / 2)) *
      Real.sinh (θ * (i + 1)) - Δ / (2 * Real.cosh (θ * (N + 1 / 2)) * Real.sinh (θ / 2)) *
      Real.sinh (θ * i) = Δ * (Real.cosh (θ * (i + 1 / 2)) / Real.cosh (θ * (N + 1 / 2))) := by
    rw [← mul_sub, h1]; field_simp
  linear_combination -e

/-- O&R Figure 8.5 (discrete version): the lattice solution is strictly increasing on the band
and responds less than one-for-one to fundamentals: `0 < e_{i+1} − e_i < Δ` for
`−N ≤ i ≤ N − 1`. -/
theorem latticeSol_increment_bounds {Δ θ : ℝ} (hΔ : 0 < Δ) (hθ : 0 < θ) {N i : ℤ}
    (h1 : -N ≤ i) (h2 : i ≤ N - 1) :
    0 < latticeSol Δ θ (latticeCoeff Δ θ N) (i + 1) - latticeSol Δ θ (latticeCoeff Δ θ N) i ∧
      latticeSol Δ θ (latticeCoeff Δ θ N) (i + 1) - latticeSol Δ θ (latticeCoeff Δ θ N) i <
        Δ := by
  rw [latticeSol_increment hθ]
  have hc := Real.cosh_pos (θ * (N + 1 / 2))
  have hci := Real.cosh_pos (θ * (i + 1 / 2))
  have hlt : Real.cosh (θ * (i + 1 / 2)) < Real.cosh (θ * (N + 1 / 2)) := by
    rw [Real.cosh_lt_cosh, abs_mul, abs_mul, abs_of_pos hθ]
    refine mul_lt_mul_of_pos_left ?_ hθ
    have hi1 : (-(N : ℝ)) ≤ i := by exact_mod_cast h1
    have hi2 : (i : ℝ) ≤ N - 1 := by exact_mod_cast h2
    rw [abs_of_pos (by linarith : (0 : ℝ) < N + 1 / 2)]
    exact abs_lt.2 ⟨by linarith, by linarith⟩
  constructor
  · have : Real.cosh (θ * (i + 1 / 2)) / Real.cosh (θ * (N + 1 / 2)) < 1 :=
      (div_lt_one hc).2 hlt
    nlinarith
  · have : 0 < Real.cosh (θ * (i + 1 / 2)) / Real.cosh (θ * (N + 1 / 2)) := div_pos hci hc
    nlinarith

/-- O&R p. 573, property 3 (discrete version, **smooth pasting at the ghost node**): extending
the closed form one step beyond the band, `e_{N+1} = e_N`. -/
theorem latticeSol_smooth_pasting {Δ θ : ℝ} (hθ : 0 < θ) (N : ℤ) :
    latticeSol Δ θ (latticeCoeff Δ θ N) (N + 1) = latticeSol Δ θ (latticeCoeff Δ θ N) N := by
  have := latticeSol_increment (Δ := Δ) hθ N N
  rw [div_self (Real.cosh_pos _).ne'] at this
  linarith

/-- O&R p. 575 (discrete honeymoon effect): `0 < e_i < k_i = iΔ` for `0 < i ≤ N`. -/
theorem latticeSol_honeymoon {Δ θ : ℝ} (hΔ : 0 < Δ) (hθ : 0 < θ) {N : ℤ} {i : ℤ} (hi : 0 < i)
    (hiN : i ≤ N) :
    0 < latticeSol Δ θ (latticeCoeff Δ θ N) i ∧ latticeSol Δ θ (latticeCoeff Δ θ N) i < i * Δ := by
  constructor
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
    induction n with
    | zero =>
      have := (latticeSol_increment_bounds hΔ hθ (N := N) (i := 0) (by omega) (by omega)).1
      simp only [zero_add] at this
      have h0 : latticeSol Δ θ (latticeCoeff Δ θ N) 0 = 0 := by simp [latticeSol]
      simp only [Nat.cast_zero, zero_add]; linarith
    | succ n ih =>
      have := (latticeSol_increment_bounds hΔ hθ (N := N) (i := (n : ℤ) + 1) (by omega)
        (by omega)).1
      have h' := ih (by omega) (by omega)
      push_cast at this ⊢
      linarith
  · unfold latticeSol
    have hi' : (0 : ℝ) < i := by exact_mod_cast hi
    have := Real.sinh_pos_iff.2 (mul_pos hθ hi')
    have := latticeCoeff_pos hΔ hθ N
    have : 0 < latticeCoeff Δ θ N * Real.sinh (θ * i) := by positivity
    linarith

/-- O&R (79) at the band edge (discrete version): the boundary equation gives
`e_N − e_{N−1} = (2/a)(k_N − e_N)`; with `a = η/h`, `h = Δ²/v²`, the boundary slope is
`O(Δ)`: `(e_N − e_{N−1})/Δ ≤ 2Δ k_N/(ηv²)` (discrete smooth pasting; `e_N ≥ 0` holds for the
equilibrium by `latticeSol_honeymoon`). -/
theorem lattice_boundary_slope {η v Δ : ℝ} (hη : 0 < η) (hv : 0 < v) (hΔ : 0 < Δ) {N : ℤ}
    (hN : 1 ≤ N) {e : ℤ → ℝ} (he : IsLatticeEqm (η * v ^ 2 / Δ ^ 2) Δ N e)
    (heN : 0 ≤ e N) :
    e N - e (N - 1) = 2 / (η * v ^ 2 / Δ ^ 2) * (N * Δ - e N) ∧
      (e N - e (N - 1)) / Δ ≤ 2 * Δ * (N * Δ) / (η * v ^ 2) := by
  have h := he N (by omega) le_rfl
  rw [min_eq_right (by omega), max_eq_left (by omega)] at h
  have ha : 0 < η * v ^ 2 / Δ ^ 2 := by positivity
  have key : e N - e (N - 1) = 2 / (η * v ^ 2 / Δ ^ 2) * (N * Δ - e N) := by
    field_simp; field_simp at h; linarith
  refine ⟨key, ?_⟩
  have e1 : 2 / (η * v ^ 2 / Δ ^ 2) = 2 * Δ ^ 2 / (η * v ^ 2) := by field_simp
  have hden : 0 < η * v ^ 2 := by positivity
  rw [key, e1, div_le_iff₀ hΔ, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right hden]
  nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sq_nonneg Δ)) heN]

/-- O&R p. 571 (the free float): without barriers, `e = k` solves the lattice equation on all
of `ℤ`. -/
theorem freeFloat_solves (a Δ : ℝ) (i : ℤ) :
    (i : ℝ) * Δ = i * Δ + a * ((((i + 1 : ℤ) : ℝ) * Δ + ((i - 1 : ℤ) : ℝ) * Δ) / 2 - i * Δ) := by
  push_cast; ring

/-- O&R p. 571 (the free float): it is the unique solution on the unrestricted lattice whose
deviation from fundamentals is bounded (no bubbles). -/
theorem freeFloat_unique {a Δ : ℝ} (ha : 0 < a) {e : ℤ → ℝ}
    (he : ∀ i : ℤ, e i = i * Δ + a * ((e (i + 1) + e (i - 1)) / 2 - e i)) {M : ℝ}
    (hM : ∀ i, |e i - i * Δ| ≤ M) : ∀ i, e i = i * Δ := by
  set B : ℤ → ℝ := fun i => e i - i * Δ with hB
  have hbub : ∀ i, B i = a / (1 + a) * ((B (i + 1) + B (i - 1)) / 2) := by
    intro i
    have := he i
    simp only [hB]; push_cast
    rw [div_mul_eq_mul_div, eq_div_iff (by linarith)]
    linear_combination this
  have h0 := CaganModel.bubble_eq_zero_of_bounded (fun g i => (g (i + 1) + g (i - 1)) / 2)
    (fun g M hg i => by
      rw [abs_div, abs_two]
      linarith [abs_add_le (g (i + 1)) (g (i - 1)), hg (i + 1), hg (i - 1)])
    (by positivity) (by rw [div_lt_one (by linarith)]; linarith) hbub (M := M) hM
  intro i
  have := congrFun h0 i
  simp only [hB, Pi.zero_apply] at this
  linarith

/-! ## Speculative attacks on a one-sided target zone (§8.6) -/

/-- O&R §8.6, p. 577: the one-sided zone locus `S(k) = k + b₁e^{λk}`. -/
noncomputable def oneS (l b₁ k : ℝ) : ℝ := k + b₁ * Real.exp (l * k)

/-- O&R (88)–(89), p. 577: value matching at the attack point and no jump into the float hold
iff `k̄ = ē + ℜ` and `b₁ = −ℜe^{−λk̄}`; hence `b₁ < 0` for `ℜ > 0`. -/
theorem oneSided_attack_iff (l ebar R b₁ kb : ℝ) :
    (oneS l b₁ kb = ebar ∧ oneS l b₁ kb = kb - R) ↔
      kb = ebar + R ∧ b₁ = -R * Real.exp (-(l * kb)) := by
  have he := Real.exp_pos (l * kb)
  have hinv : Real.exp (l * kb) * Real.exp (-(l * kb)) = 1 := by rw [← Real.exp_add]; simp
  unfold oneS
  constructor
  · rintro ⟨h1, h2⟩
    have hb : b₁ * Real.exp (l * kb) = -R := by linarith
    refine ⟨by linarith, ?_⟩
    linear_combination Real.exp (-(l * kb)) * hb - b₁ * hinv
  · rintro ⟨h1, h2⟩
    have hb : b₁ * Real.exp (l * kb) = -R := by rw [h2]; linear_combination (-R) * hinv
    constructor <;> linarith

/-- O&R p. 577: for `ℜ > 0` the attack locus has `b₁ < 0`. -/
theorem oneSided_b_neg {l R kb : ℝ} (hR : 0 < R) : -R * Real.exp (-(l * kb)) < 0 := by
  have := Real.exp_pos (-(l * kb)); nlinarith

/-- O&R (90), p. 578: under (88)–(89), smooth pasting `S′(k̄) = 1 + λb₁e^{λk̄} = 0` holds iff
`ℜ = ℜ′ = 1/λ`. -/
theorem oneSided_smooth_pasting_iff {l ebar R : ℝ} (hl : 0 < l) :
    1 + l * (-R * Real.exp (-(l * (ebar + R)))) * Real.exp (l * (ebar + R)) = 0 ↔ R = 1 / l := by
  have hinv : Real.exp (-(l * (ebar + R))) * Real.exp (l * (ebar + R)) = 1 := by
    rw [← Real.exp_add]; simp
  have e : 1 + l * (-R * Real.exp (-(l * (ebar + R)))) * Real.exp (l * (ebar + R)) =
      1 - l * R := by linear_combination (-(l * R)) * hinv
  rw [e, eq_div_iff hl.ne']
  constructor <;> intro h <;> linarith

/-- O&R p. 578–579 (the fully credible zone): there is a unique `(b₁, k̄′)` with value matching
`S(k̄′) = ē` and smooth pasting `S′(k̄′) = 0`: `k̄′ = ē + 1/λ`, `b₁ = −(1/λ)e^{−λk̄′}`. -/
theorem credible_zone_existsUnique {l : ℝ} (hl : 0 < l) (ebar : ℝ) :
    ∃! p : ℝ × ℝ, oneS l p.1 p.2 = ebar ∧ 1 + l * p.1 * Real.exp (l * p.2) = 0 := by
  have hinv : ∀ x, Real.exp x * Real.exp (-x) = 1 := fun x => by rw [← Real.exp_add]; simp
  refine ⟨(-(1 / l) * Real.exp (-(l * (ebar + 1 / l))), ebar + 1 / l), ⟨?_, ?_⟩, ?_⟩
  · simp only; unfold oneS
    have := hinv (l * (ebar + 1 / l))
    linear_combination (-(1 / l)) * this
  · simp only
    have := hinv (l * (ebar + 1 / l))
    have hl1 : l * (1 / l) = 1 := by field_simp
    linear_combination (-1) * this - (Real.exp (-(l * (ebar + 1 / l))) *
      Real.exp (l * (ebar + 1 / l))) * hl1
  · rintro ⟨b, k⟩ ⟨h1, h2⟩
    simp only at h1 h2
    unfold oneS at h1
    have hb : b * Real.exp (l * k) = -(1 / l) := by field_simp; linarith
    have hk : k = ebar + 1 / l := by linarith
    subst hk
    have := hinv (l * (ebar + 1 / l))
    simp only [Prod.mk.injEq, and_true]
    linear_combination Real.exp (-(l * (ebar + 1 / l))) * hb - b * this

/-- O&R p. 579: if reserves are large (`ℜ > ℜ′ = 1/λ`) an attack at `k̄′` would move the rate
to the float value `k̄′ − ℜ < ē`, an anticipated appreciation: no attack can occur; attacks are
possible only if `ℜ ≤ ℜ′`. -/
theorem attack_impossible_iff {l ebar R : ℝ} :
    ebar + 1 / l - R < ebar ↔ 1 / l < R := by constructor <;> intro h <;> linarith

/-- O&R Figure 8.6 (`S₂`): the fully credible locus satisfies `S₂′(k) = 1 − e^{λ(k−k̄′)}`,
which is `≥ 0` exactly for `k ≤ k̄′` and vanishes only at `k̄′`. -/
theorem credible_zone_deriv {l k kb : ℝ} (hl : 0 < l) :
    1 + l * (-(1 / l) * Real.exp (-(l * kb))) * Real.exp (l * k) = 1 - Real.exp (l * (k - kb)) ∧
      (0 ≤ 1 - Real.exp (l * (k - kb)) ↔ k ≤ kb) ∧ (1 - Real.exp (l * (k - kb)) = 0 ↔ k = kb) := by
  refine ⟨?_, ?_, ?_⟩
  · have : Real.exp (-(l * kb)) * Real.exp (l * k) = Real.exp (l * (k - kb)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hl1 : l * (1 / l) = 1 := by field_simp
    linear_combination (-(Real.exp (-(l * kb)) * Real.exp (l * k))) * hl1 - this
  · rw [sub_nonneg]
    constructor
    · intro h; by_contra hc; push Not at hc
      have := Real.one_lt_exp_iff.2 (show 0 < l * (k - kb) by nlinarith); linarith
    · intro h; exact Real.exp_le_one_iff.2 (by nlinarith)
  · rw [sub_eq_zero, eq_comm, Real.exp_eq_one_iff]
    constructor
    · intro h; rcases mul_eq_zero.1 h with h | h
      · linarith
      · linarith
    · intro h; rw [h, sub_self, mul_zero]

/-- O&R Figure 8.6: the fully credible locus lies strictly below the free float
(`S₂(k) < k`, honeymoon) and never above the ceiling `ē` (its maximum, `ē`, is at `k̄′`). -/
theorem credible_zone_below {l ebar k : ℝ} (hl : 0 < l) :
    oneS l (-(1 / l) * Real.exp (-(l * (ebar + 1 / l)))) k < k ∧
      oneS l (-(1 / l) * Real.exp (-(l * (ebar + 1 / l)))) k ≤ ebar := by
  set kb := ebar + 1 / l
  have hE : Real.exp (-(l * kb)) * Real.exp (l * k) = Real.exp (l * (k - kb)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos := Real.exp_pos (l * (k - kb))
  unfold oneS
  constructor
  · have : 0 < 1 / l * (Real.exp (-(l * kb)) * Real.exp (l * k)) := by rw [hE]; positivity
    nlinarith
  · -- `k − e^{λ(k−k̄′)}/λ ≤ k̄′ − 1/λ` since `x − e^{λ x}/λ` is maximal at `x = 0`
    have h1 := Real.add_one_le_exp (l * (k - kb))
    have : k - 1 / l * Real.exp (l * (k - kb)) ≤ kb - 1 / l := by
      have : 1 / l * (l * (k - kb) + 1) ≤ 1 / l * Real.exp (l * (k - kb)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have e : 1 / l * (l * (k - kb) + 1) = k - kb + 1 / l := by field_simp
      linarith
    have e2 : k + -(1 / l) * Real.exp (-(l * kb)) * Real.exp (l * k) =
        k - 1 / l * Real.exp (l * (k - kb)) := by rw [← hE]; ring
    rw [e2]; simp only [kb] at this ⊢; linarith

/-- O&R Figure 8.6 (`S₁`): when reserves are small (`ℜ < 1/λ`) the attack locus has no smooth
pasting (`S₁′(k̄) = 1 − λℜ > 0`) and is strictly increasing up to `k̄`. -/
theorem small_reserves_locus {l R ebar : ℝ} (hl : 0 < l) (hRl : R < 1 / l) :
    0 < 1 - l * R ∧ StrictMonoOn (oneS l (-R * Real.exp (-(l * (ebar + R))))) (Iic (ebar + R)) := by
  have hlR : l * R < 1 := by rw [lt_div_iff₀ hl] at hRl; linarith
  refine ⟨by linarith, ?_⟩
  set kb := ebar + R
  have hd : ∀ x, HasDerivAt (oneS l (-R * Real.exp (-(l * kb))))
      (1 - l * R * Real.exp (l * (x - kb))) x := by
    intro x
    have := (hasDerivAt_id' x).add ((((hasDerivAt_id' x).const_mul l).exp).const_mul
      (-R * Real.exp (-(l * kb))))
    unfold oneS
    convert this using 1
    have : Real.exp (-(l * kb)) * Real.exp (l * x) = Real.exp (l * (x - kb)) := by
      rw [← Real.exp_add]; congr 1; ring
    linear_combination (l * R) * this
  refine strictMonoOn_of_deriv_pos (convex_Iic _)
    (continuous_iff_continuousAt.2 fun x => (hd x).continuousAt).continuousOn fun x hx => ?_
  rw [interior_Iic] at hx
  rw [(hd x).deriv]
  have : Real.exp (l * (x - kb)) < 1 := Real.exp_lt_one_iff.2 (by
    simp only [mem_Iio] at hx; nlinarith)
  nlinarith [Real.exp_pos (l * (x - kb))]

/-! ## Exercise 5: trending fundamentals with given barriers -/

/-- O&R Exercise 5, p. 601: for fundamental barriers `k̲ < k̄` and distinct nonzero roots
`λ₁ ≠ λ₂`, smooth pasting at both barriers,
`1 + λ₁b₁e^{λ₁k} + λ₂b₂e^{λ₂k} = 0` at `k = k̲, k̄`, has a unique solution `(b₁, b₂)`. -/
theorem drift_band_smooth_pasting {l₁ l₂ kl kh : ℝ} (h1 : l₁ ≠ 0) (h2 : l₂ ≠ 0)
    (hne : l₁ ≠ l₂) (hk : kl < kh) :
    ∃! p : ℝ × ℝ,
      1 + l₁ * p.1 * Real.exp (l₁ * kl) + l₂ * p.2 * Real.exp (l₂ * kl) = 0 ∧
        1 + l₁ * p.1 * Real.exp (l₁ * kh) + l₂ * p.2 * Real.exp (l₂ * kh) = 0 := by
  set E1 := Real.exp (l₁ * kl); set E2 := Real.exp (l₂ * kl)
  set F1 := Real.exp (l₁ * kh); set F2 := Real.exp (l₂ * kh)
  have hdet : E1 * F2 - E2 * F1 ≠ 0 := by
    intro h
    have : Real.exp (l₁ * kl + l₂ * kh) = Real.exp (l₂ * kl + l₁ * kh) := by
      rw [Real.exp_add, Real.exp_add]; linarith
    have := Real.exp_injective this
    have : (l₁ - l₂) * (kl - kh) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact hne (by linarith)
    · linarith
  set det := l₁ * l₂ * (E1 * F2 - E2 * F1) with hdd
  have hdet' : det ≠ 0 := mul_ne_zero (mul_ne_zero h1 h2) hdet
  refine ⟨(l₂ * (E2 - F2) / det, l₁ * (F1 - E1) / det), ⟨?_, ?_⟩, ?_⟩
  · simp only; field_simp; rw [hdd]; ring
  · simp only; field_simp; rw [hdd]; ring
  · rintro ⟨x, y⟩ ⟨hx1, hx2⟩
    simp only at hx1 hx2
    have hxd : x * det = l₂ * (E2 - F2) := by
      rw [hdd]; linear_combination (l₂ * F2) * hx1 - (l₂ * E2) * hx2
    have hyd : y * det = l₁ * (F1 - E1) := by
      rw [hdd]; linear_combination (-(l₁ * F1)) * hx1 + (l₁ * E1) * hx2
    simp only [Prod.mk.injEq]
    constructor
    · field_simp; linarith
    · field_simp; linarith

/-! ## Interest differentials in a band (§8.5.6, fn 60) -/

/-- O&R §8.5.6 and fn 60, p. 576: if the exchange-rate change `ℰ_{t+τ}/ℰ_t` lies in `[a, b]` in
every state, and there is no arbitrage between home and foreign bonds (no zero-cost position
with a strictly positive payoff in every state), then `(1+i)/(1+i*) ∈ [a, b]`, whatever the
preferences (risk aversion is irrelevant). -/
theorem band_interest_bounds {Ω : Type} [Nonempty Ω] (R : Ω → ℝ) {a b i istar : ℝ}
    (hR : ∀ ω, a ≤ R ω ∧ R ω ≤ b) (hi : 0 < 1 + istar)
    (noArb : ¬ ∃ x : ℝ, ∀ ω, 0 < x * ((1 + i) - (1 + istar) * R ω)) :
    a ≤ (1 + i) / (1 + istar) ∧ (1 + i) / (1 + istar) ≤ b := by
  constructor
  · by_contra h
    push Not at h
    rw [div_lt_iff₀ hi] at h
    exact noArb ⟨-1, fun ω => by nlinarith [(hR ω).1]⟩
  · by_contra h
    push Not at h
    rw [lt_div_iff₀ hi] at h
    exact noArb ⟨1, fun ω => by nlinarith [(hR ω).2]⟩

/-- O&R fn 60, p. 576: equivalently, with positive state prices `π` pricing both bonds
(`1/(1+i) = Σπ`, `1/(1+i*) = Σ π R`, prices in home currency per unit), the ratio
`(1+i)/(1+i*) = Σ πR/Σ π` is a weighted average of the possible changes. -/
theorem band_interest_state_prices {Ω : Type} [Fintype Ω] [Nonempty Ω] (R π : Ω → ℝ)
    {a b : ℝ} (hR : ∀ ω, a ≤ R ω ∧ R ω ≤ b) (hπ : ∀ ω, 0 < π ω) :
    a ≤ (∑ ω, π ω * R ω) / ∑ ω, π ω ∧ (∑ ω, π ω * R ω) / ∑ ω, π ω ≤ b := by
  have hS : 0 < ∑ ω, π ω := Finset.sum_pos (fun ω _ => hπ ω) Finset.univ_nonempty
  constructor
  · rw [le_div_iff₀ hS, Finset.mul_sum]
    exact Finset.sum_le_sum fun ω _ => by nlinarith [(hR ω).1, hπ ω]
  · rw [div_le_iff₀ hS, Finset.mul_sum]
    exact Finset.sum_le_sum fun ω _ => by nlinarith [(hR ω).2, hπ ω]

/-- O&R p. 576: a ±1% band allows a maximal change of about 2% (`1.01/0.99 ≈ 1.0202`); a 2%
change over six months is 4% per annum, and over one month 24% per annum. -/
theorem band_interest_numbers :
    ((1.0202 : ℝ) < 1.01 / 0.99 ∧ (1.01 : ℝ) / 0.99 < 1.0203) ∧
      (2 : ℝ) * (12 / 6) = 4 ∧ (2 : ℝ) * (12 / 1) = 24 := by
  norm_num

/-! ## The flag on (86): regulated increments -/

/-- O&R (86), p. 574 (flag): for a symmetric increment `dk` (an involution `σ` of the finite
state space preserving probabilities with `dk ∘ σ = −dk`), the regulated increment
`min(dk, 0)` has second moment `E(dk)²/2`, not `E(dk)² = hv²`. -/
theorem regulated_second_moment {Ω : Type} [Fintype Ω] (p X : Ω → ℝ) (σ : Ω → Ω)
    (hσ : Function.Involutive σ) (hp : ∀ ω, p (σ ω) = p ω) (hX : ∀ ω, X (σ ω) = -X ω) :
    ∑ ω, p ω * min (X ω) 0 ^ 2 = (∑ ω, p ω * X ω ^ 2) / 2 := by
  have hre : ∑ ω, p ω * min (X ω) 0 ^ 2 = ∑ ω, p ω * min (-X ω) 0 ^ 2 := by
    rw [← Equiv.sum_comp (hσ.toPerm σ)]
    exact Finset.sum_congr rfl fun ω _ => by
      simp only [Function.Involutive.coe_toPerm, hp, hX]
  have hpt : ∀ x : ℝ, min x 0 ^ 2 + min (-x) 0 ^ 2 = x ^ 2 := by
    intro x
    rcases le_total x 0 with h | h
    · rw [min_eq_left h, min_eq_right (by linarith)]; ring
    · rw [min_eq_right h, min_eq_left (by linarith)]; ring
  have : 2 * ∑ ω, p ω * min (X ω) 0 ^ 2 = ∑ ω, p ω * X ω ^ 2 := by
    rw [two_mul]
    nth_rewrite 2 [hre]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ω _ => by rw [← mul_add, hpt]
  linarith

/-- O&R (86), p. 574 (flag): the regulated increment has mean `E min(dk, 0) = −E|dk|/2 < 0`
(the `O(h^{1/2})` term that drives smooth pasting). -/
theorem regulated_mean {Ω : Type} [Fintype Ω] (p X : Ω → ℝ) (σ : Ω → Ω)
    (hσ : Function.Involutive σ) (hp : ∀ ω, p (σ ω) = p ω) (hX : ∀ ω, X (σ ω) = -X ω) :
    ∑ ω, p ω * min (X ω) 0 = -(∑ ω, p ω * |X ω|) / 2 := by
  have hre : ∑ ω, p ω * min (X ω) 0 = ∑ ω, p ω * min (-X ω) 0 := by
    rw [← Equiv.sum_comp (hσ.toPerm σ)]
    exact Finset.sum_congr rfl fun ω _ => by
      simp only [Function.Involutive.coe_toPerm, hp, hX]
  have hpt : ∀ x : ℝ, min x 0 + min (-x) 0 = -|x| := by
    intro x
    rcases le_total x 0 with h | h
    · rw [min_eq_left h, min_eq_right (by linarith), abs_of_nonpos h]; ring
    · rw [min_eq_right h, min_eq_left (by linarith), abs_of_nonneg h]; ring
  have : 2 * ∑ ω, p ω * min (X ω) 0 = -∑ ω, p ω * |X ω| := by
    rw [two_mul]
    nth_rewrite 2 [hre]
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun ω _ => by rw [← mul_add, hpt]; ring
  linarith

/-! ## Reserve exhaustion is inevitable (§8.6, p. 578) -/

/-- O&R p. 578, discrete version: the probability that the lattice fundamentals, started at
`i`, have **not** reached the ceiling `N` by date `n` (steps `±1` with probability ½, the
downward step at the floor `−N` suppressed). -/
noncomputable def notHitProb (N : ℕ) : ℕ → ℤ → ℝ
  | 0 => fun i => if i = N then 0 else 1
  | n + 1 => fun i => if i = N then 0 else
      (notHitProb N n (min (i + 1) N) + notHitProb N n (max (i - 1) (-N))) / 2

/-- O&R p. 578: `notHitProb` is a probability. -/
theorem notHitProb_mem (N : ℕ) (n : ℕ) (i : ℤ) :
    0 ≤ notHitProb N n i ∧ notHitProb N n i ≤ 1 := by
  induction n generalizing i with
  | zero => unfold notHitProb; split_ifs <;> norm_num
  | succ n ih =>
    unfold notHitProb
    split_ifs
    · norm_num
    · have := ih (min (i + 1) N); have := ih (max (i - 1) (-N))
      constructor <;> linarith

/-- O&R p. 578: the ceiling state itself has been hit. -/
theorem notHitProb_ceiling (N n : ℕ) : notHitProb N n N = 0 := by
  cases n <;> simp [notHitProb]

/-- O&R p. 578: the not-yet-hit probability is non-increasing in `n`. -/
theorem notHitProb_antitone (N : ℕ) (i : ℤ) : Antitone fun n => notHitProb N n i := by
  have e : ∀ n j, notHitProb N (n + 1) j = if j = N then 0 else
      (notHitProb N n (min (j + 1) N) + notHitProb N n (max (j - 1) (-N))) / 2 :=
    fun _ _ => rfl
  have step : ∀ n j, notHitProb N (n + 1) j ≤ notHitProb N n j := by
    intro n
    induction n with
    | zero =>
      intro j
      rw [e 0 j]
      simp only [notHitProb]
      split_ifs <;> norm_num
    | succ n ih =>
      intro j
      rw [e (n + 1) j, e n j]
      split_ifs
      · exact le_rfl
      · have := ih (min (j + 1) N); have := ih (max (j - 1) (-N))
        linarith
  exact antitone_nat_of_succ_le fun n => step n i

/-- O&R p. 578: the one-block estimate: if `q_n ≤ S` on the band, then after `m` more steps
`q ≤ S` on the band, and `q ≤ S(1 − 2^{−m})` from every state within `m` steps of the
ceiling (the all-up path has probability `2^{−m}`). -/
theorem notHitProb_block (N : ℕ) (n : ℕ) {S : ℝ} (hS : 0 ≤ S)
    (hb : ∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ N → notHitProb N n j ≤ S) (m : ℕ) :
    ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N → notHitProb N (n + m) i ≤ S ∧
      ((N : ℤ) - i ≤ m → notHitProb N (n + m) i ≤ S * (1 - (1 / 2) ^ m)) := by
  induction m with
  | zero =>
    intro i h1 h2
    refine ⟨hb i h1 h2, fun h => ?_⟩
    have : i = N := by omega
    rw [this, notHitProb_ceiling]; simp
  | succ m ih =>
    intro i h1 h2
    have hx : (0 : ℝ) ≤ (1 / 2) ^ (m + 1) := by positivity
    have hx1 : ((1 : ℝ) / 2) ^ (m + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    by_cases hi : i = N
    · rw [hi, notHitProb_ceiling]
      exact ⟨hS, fun _ => mul_nonneg hS (by linarith)⟩
    · have hup := ih (min (i + 1) N) (by omega) (by omega)
      have hdn := ih (max (i - 1) (-N)) (by omega) (by omega)
      have e : notHitProb N (n + (m + 1)) i =
          (notHitProb N (n + m) (min (i + 1) N) + notHitProb N (n + m) (max (i - 1) (-N))) /
            2 := by
        rw [show n + (m + 1) = (n + m) + 1 by ring]
        simp only [notHitProb, ite_eq_right hi]
      rw [e]
      refine ⟨by linarith [hup.1, hdn.1], fun hd => ?_⟩
      have hup' := hup.2 (by omega)
      rw [pow_succ]
      nlinarith [hdn.1]

/-- O&R p. 578: from every state of the band, the probability of not having reached the
ceiling after `k` blocks of `2N` steps is at most `(1 − 2^{−2N})^k`. -/
theorem notHitProb_blocks (N : ℕ) (k : ℕ) :
    ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N →
      notHitProb N (k * (2 * N)) i ≤ (1 - (1 / 2) ^ (2 * N)) ^ k := by
  have hc : (0 : ℝ) ≤ 1 - (1 / 2) ^ (2 * N) := by
    have : ((1 : ℝ) / 2) ^ (2 * N) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  induction k with
  | zero => intro i _ _; simpa using (notHitProb_mem N 0 i).2
  | succ k ih =>
    intro i h1 h2
    have := (notHitProb_block N (k * (2 * N)) (pow_nonneg hc k) ih (2 * N) i h1 h2).2
      (by push_cast; omega)
    rw [show (k + 1) * (2 * N) = k * (2 * N) + 2 * N by ring, pow_succ]
    exact this

/-- O&R p. 578 (**reserve exhaustion is inevitable**): with random-walk fundamentals and no
floor intervention on the upside, the ceiling is reached with probability one from every
state of the band: the not-yet-hit probability tends to zero. (Each visit to the ceiling
costs reserves, so with the chain restarting at the ceiling a finite stock is eventually
exhausted; the repeated-visit statement is the strong Markov property, not formalised.) -/
theorem ceiling_hit_almost_surely {N : ℕ} (hN : 0 < N) {i : ℤ} (h1 : -(N : ℤ) ≤ i)
    (h2 : i ≤ N) : Tendsto (fun n => notHitProb N n i) atTop (𝓝 0) := by
  set K := 2 * N with hK
  have hKpos : 0 < K := by omega
  set c : ℝ := 1 - (1 / 2) ^ K with hc
  have hc0 : 0 ≤ c := by
    have : ((1 : ℝ) / 2) ^ K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hc1 : c < 1 := by
    have : (0 : ℝ) < (1 / 2) ^ K := by positivity
    linarith
  have hdiv : Tendsto (fun n : ℕ => n / K) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨b * K, fun n hn => ?_⟩
    exact (Nat.le_div_iff_mul_le hKpos).2 hn
  have hup : Tendsto (fun n : ℕ => c ^ (n / K)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).comp hdiv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => (notHitProb_mem N n i).1) fun n => ?_
  have hle : (n / K) * K ≤ n := Nat.div_mul_le_self n K
  calc notHitProb N n i ≤ notHitProb N ((n / K) * K) i := notHitProb_antitone N i hle
    _ ≤ c ^ (n / K) := notHitProb_blocks N (n / K) i h1 h2

/-! ## The lattice equilibrium as the stochastic Cagan solution (80) -/

/-- O&R (80)–(81), pp. 570–571: the up-step on the band `{0, …, 2N}` (state `j` ↔
fundamentals `(j − N)Δ`), suppressed at the ceiling. -/
def bandUp (N : ℕ) (j : Fin (2 * N + 1)) : Fin (2 * N + 1) :=
  ⟨min (j.val + 1) (2 * N), by omega⟩

/-- O&R (80)–(81): the down-step on the band, suppressed at the floor. -/
def bandDown (N : ℕ) (j : Fin (2 * N + 1)) : Fin (2 * N + 1) :=
  ⟨j.val - 1, by omega⟩

/-- O&R (81), p. 571, discretised: the regulated random walk on the band as a Markov kernel
(`±Δ` with probability ½; the step out of the band is suppressed). -/
noncomputable def bandKernel (N : ℕ) : CaganModel.MarkovKernel (Fin (2 * N + 1)) where
  K j j' := (if j' = bandUp N j then 1 / 2 else 0) + (if j' = bandDown N j then 1 / 2 else 0)
  nonneg j j' := by split_ifs <;> norm_num
  rowSum j := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]; norm_num

/-- O&R (80): the conditional expectation under the regulated walk is the average of the up
and down states. -/
theorem bandKernel_apply (N : ℕ) (g : Fin (2 * N + 1) → ℝ) (j : Fin (2 * N + 1)) :
    CaganModel.kernelApply (bandKernel N) g j = (g (bandUp N j) + g (bandDown N j)) / 2 := by
  unfold CaganModel.kernelApply bandKernel
  simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring

/-- O&R (80), p. 570 (**identification**): the lattice target-zone equilibrium is exactly the
no-bubble solution of the stochastic Cagan equation (79) for the regulated fundamentals
process, i.e. CaganModel's `markovFundamental` with semielasticity `a = η/h` for the band
kernel. The reflecting boundary does not change the form of (80): the expectations in (80)
are simply taken under the regulated (intervention-adjusted) process. -/
theorem lattice_eq_markovFundamental {a Δ : ℝ} (ha : 0 < a) {N : ℕ} {e : ℤ → ℝ}
    (he : IsLatticeEqm a Δ N e) (j : Fin (2 * N + 1)) :
    CaganModel.markovFundamental a (bandKernel N) (fun j => ((j : ℤ) - N : ℝ) * Δ) j =
      e ((j : ℤ) - N) := by
  have hp : CaganModel.IsMarkovEqm a (bandKernel N) (fun j => ((j : ℤ) - N : ℝ) * Δ)
      (fun j => e ((j : ℤ) - N)) := by
    intro j
    rw [bandKernel_apply]
    have hj := j.isLt
    have h := he ((j : ℤ) - N) (by omega) (by omega)
    have hu : ((bandUp N j : ℕ) : ℤ) - N = min ((j : ℤ) - N + 1) N := by
      unfold bandUp; simp only; omega
    have hd : ((bandDown N j : ℕ) : ℤ) - N = max ((j : ℤ) - N - 1) (-N) := by
      unfold bandDown; simp only; omega
    simp only
    rw [hu, hd]
    push_cast at h ⊢
    unfold CaganModel.disc
    rw [div_mul_eq_mul_div, ← add_div, eq_div_iff (by linarith)]
    linear_combination h
  rw [← CaganModel.isMarkovEqm_unique ha (bandKernel N) hp]

/-- O&R (80), p. 570, in the book's form: with `a = η/h` the lattice equilibrium is
`e_t = (h/(h+η)) Σ_n (1 + h/η)^{−n} E_t k_{t+n}`, expectations under the regulated walk. -/
theorem lattice_eq_80 {η h Δ : ℝ} (hη : 0 < η) (hh : 0 < h) {N : ℕ} {e : ℤ → ℝ}
    (he : IsLatticeEqm (η / h) Δ N e) (j : Fin (2 * N + 1)) :
    e ((j : ℤ) - N) = h / (h + η) * ∑' n : ℕ, (1 + h / η)⁻¹ ^ n *
      CaganModel.kernelPow (bandKernel N) n (fun j => ((j : ℤ) - N : ℝ) * Δ) j := by
  rw [← lattice_eq_markovFundamental (div_pos hη hh) he j]
  unfold CaganModel.markovFundamental
  have e1 : CaganModel.disc (η / h) = (1 + h / η)⁻¹ := by
    unfold CaganModel.disc; field_simp; ring
  have e2 : 1 / (1 + η / h) = h / (h + η) := by field_simp
  rw [e1, e2]

/-! ## Repeated interventions: reserves are exhausted with probability one (p. 578) -/

/-- O&R p. 578, discrete version: `intervProb N n r i` is the probability that, starting from
state `i`, at most `r` ceiling interventions occur in the first `n` periods. At the ceiling an
attempted up-step (probability ½) is blocked by selling reserves (an intervention) and the
state stays at the ceiling; otherwise the walk moves `±1`, the down-step at the floor being
suppressed. -/
noncomputable def intervProb (N : ℕ) : ℕ → ℕ → ℤ → ℝ
  | 0 => fun _ _ => 1
  | n + 1 => fun r i =>
      if i = N then
        ((if r = 0 then 0 else intervProb N n (r - 1) N) + intervProb N n r (N - 1)) / 2
      else (intervProb N n r (min (i + 1) N) + intervProb N n r (max (i - 1) (-N))) / 2

/-- O&R p. 578: the one-step recursion for `intervProb`. -/
theorem intervProb_succ (N n r : ℕ) (i : ℤ) :
    intervProb N (n + 1) r i =
      if i = N then
        ((if r = 0 then 0 else intervProb N n (r - 1) N) + intervProb N n r (N - 1)) / 2
      else (intervProb N n r (min (i + 1) N) + intervProb N n r (max (i - 1) (-N))) / 2 :=
  rfl

/-- O&R p. 578: `intervProb` is a probability. -/
theorem intervProb_mem (N n r : ℕ) (i : ℤ) :
    0 ≤ intervProb N n r i ∧ intervProb N n r i ≤ 1 := by
  induction n generalizing r i with
  | zero => simp [intervProb]
  | succ n ih =>
    rw [intervProb_succ]
    split_ifs with h1 h2
    · have := ih r (N - 1); constructor <;> linarith
    · have := ih (r - 1) N; have := ih r (N - 1); constructor <;> linarith
    · have := ih r (min (i + 1) N); have := ih r (max (i - 1) (-N))
      constructor <;> linarith

/-- O&R p. 578: allowing more interventions makes the event more likely (monotone in `r`). -/
theorem intervProb_mono_r (N n r : ℕ) (i : ℤ) :
    intervProb N n r i ≤ intervProb N n (r + 1) i := by
  induction n generalizing r i with
  | zero => simp [intervProb]
  | succ n ih =>
    rw [intervProb_succ N n r i, intervProb_succ N n (r + 1) i]
    by_cases hi : i = N
    · rw [ite_eq_left hi, ite_eq_left hi, ite_eq_right (Nat.succ_ne_zero r), Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr
        rw [ite_eq_left rfl]
        have := (intervProb_mem N n 0 N).1; have := ih 0 (N - 1); linarith
      · rw [ite_eq_right (by omega)]
        have h5 := ih (r - 1) N
        rw [Nat.sub_add_cancel hr] at h5
        have := ih r (N - 1); linarith
    · rw [ite_eq_right hi, ite_eq_right hi]
      have := ih r (min (i + 1) N); have := ih r (max (i - 1) (-N)); linarith

/-- O&R p. 578: more time makes the event less likely (antitone in `n`). -/
theorem intervProb_antitone (N r : ℕ) (i : ℤ) : Antitone fun n => intervProb N n r i := by
  have step : ∀ n r j, intervProb N (n + 1) r j ≤ intervProb N n r j := by
    intro n
    induction n with
    | zero =>
      intro r j
      rw [show intervProb N 0 r j = 1 from rfl]; exact (intervProb_mem N 1 r j).2
    | succ n ih =>
      intro r j
      rw [intervProb_succ N (n + 1) r j, intervProb_succ N n r j]
      by_cases hj : j = N
      · rw [ite_eq_left hj, ite_eq_left hj]
        by_cases hr : r = 0
        · rw [ite_eq_left hr, ite_eq_left hr]; have := ih r (N - 1); linarith
        · rw [ite_eq_right hr, ite_eq_right hr]
          have := ih (r - 1) N; have := ih r (N - 1); linarith
      · rw [ite_eq_right hj, ite_eq_right hj]
        have := ih r (min (j + 1) N); have := ih r (max (j - 1) (-N)); linarith
  exact antitone_nat_of_succ_le fun n => step n r i

/-- O&R p. 578: a bound on the band is preserved over time. -/
theorem intervProb_bound (N : ℕ) (hN : 1 ≤ N) (n r : ℕ) {S : ℝ}
    (hb : ∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ N → intervProb N n r j ≤ S) (m : ℕ) :
    ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N → intervProb N (n + m) r i ≤ S := by
  induction m with
  | zero => exact hb
  | succ m ih =>
    intro i h1 h2
    rw [show n + (m + 1) = (n + m) + 1 by ring, intervProb_succ]
    split_ifs with h3 h4
    · have := ih (N - 1) (by omega) (by omega)
      have := (intervProb_mem N (n + m) r N).1 |>.trans (ih N (by omega) le_rfl)
      linarith
    · have h5 := intervProb_mono_r N (n + m) (r - 1) N
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h4)] at h5
      have := ih N (by omega) le_rfl; have := ih (N - 1) (by omega) (by omega)
      linarith
    · have := ih (min (i + 1) N) (by omega) (by omega)
      have := ih (max (i - 1) (-N)) (by omega) (by omega)
      linarith

/-- O&R p. 578: the block estimate: if on the band `intervProb n r ≤ S` and
`intervProb n (r−1) ≤ S′` (with `S′ = 0`-bound when `r = 0`), then from any state within
`m` steps of an intervention (`N − i + 1 ≤ m`), after `m` more periods
`intervProb ≤ S − 2^{−m}(S − S′)`: the path running straight up and intervening has
probability `2^{−m}`. -/
theorem intervProb_block (N : ℕ) (hN : 1 ≤ N) (n r : ℕ) {S S' : ℝ} (hS' : 0 ≤ S')
    (hSS : S' ≤ S) (hb : ∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ N → intervProb N n r j ≤ S)
    (hb' : ∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ N → r ≠ 0 → intervProb N n (r - 1) j ≤ S') (m : ℕ) :
    ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N → (N : ℤ) - i + 1 ≤ m →
      intervProb N (n + m) r i ≤ S - (1 / 2) ^ m * (S - S') := by
  induction m with
  | zero => intro i _ h2 h3; push_cast at h3; omega
  | succ m ih =>
    intro i h1 h2 h3
    rw [show n + (m + 1) = (n + m) + 1 by ring, intervProb_succ]
    have hx : ((1 : ℝ) / 2) ^ (m + 1) ≤ 1 / 2 := by
      rw [pow_succ]; have : ((1 : ℝ) / 2) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have hS0 : 0 ≤ S - S' := by linarith
    split_ifs with h4 h5
    · -- at the ceiling with no interventions allowed
      have := intervProb_bound N hN n r hb m (N - 1) (by omega) (by omega)
      nlinarith
    · -- at the ceiling: intervene (prob ½) or step down
      have e1 := intervProb_bound N hN n (r - 1) (fun j h1 h2 => hb' j h1 h2 h5) m N
        (by omega) le_rfl
      have e2 := intervProb_bound N hN n r hb m (N - 1) (by omega) (by omega)
      nlinarith
    · -- below the ceiling: step up (prob ½)
      have hi : i < N := lt_of_le_of_ne h2 h4
      have e1 := ih (i + 1) (by omega) (by omega) (by push_cast at h3 ⊢; omega)
      rw [min_eq_left (by omega)]
      have e2 := intervProb_bound N hN n r hb m (max (i - 1) (-N)) (by omega) (by omega)
      rw [pow_succ]
      nlinarith

/-- O&R p. 578: the explicit bound `U_k(r) = (k+1)^r (1−c)^k/(1−c)^r` used for block `k`. -/
noncomputable def intervBound (c : ℝ) (k r : ℕ) : ℝ := ((k : ℝ) + 1) ^ r * (1 - c) ^ k / (1 - c) ^ r

/-- O&R p. 578: after `k` blocks of `L = 2N + 1` periods, the probability of at most `r`
interventions is at most `U_k(r)` with `c = 2^{−L}`. -/
theorem intervProb_blocks (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    ∀ r : ℕ, ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N →
      intervProb N (k * (2 * N + 1)) r i ≤ intervBound ((1 / 2) ^ (2 * N + 1)) k r := by
  set c : ℝ := (1 / 2) ^ (2 * N + 1) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have h1c : 0 < 1 - c := by linarith
  have hU0 : ∀ k r, 0 ≤ intervBound c k r := fun k r => by unfold intervBound; positivity
  have hUmono : ∀ k r, intervBound c k r ≤ intervBound c k (r + 1) := by
    intro k r
    unfold intervBound
    rw [pow_succ, pow_succ, div_le_div_iff₀ (by positivity) (by positivity)]
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
    have hp : 0 ≤ ((k : ℝ) + 1) ^ r * (1 - c) ^ k * (1 - c) ^ r := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (show 1 - c ≤ (k : ℝ) + 1 by linarith) hp]
  induction k with
  | zero =>
    intro r i _ _
    simp only [zero_mul, intervProb, intervBound, Nat.cast_zero, zero_add, one_pow, pow_zero,
      one_mul]
    rw [le_div_iff₀ (by positivity), one_mul]
    exact pow_le_one₀ h1c.le (by linarith)
  | succ k ih =>
    intro r i h1 h2
    have hbl := intervProb_block N hN (k * (2 * N + 1)) r
      (S := intervBound c k r) (S' := if r = 0 then 0 else intervBound c k (r - 1))
      (by split_ifs <;> [exact le_rfl; exact hU0 k (r - 1)])
      (by split_ifs with h
          · exact hU0 k r
          · have := hUmono k (r - 1); rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h)]
                at this)
      (ih r) (fun j h1 h2 hr => by rw [ite_eq_right hr]; exact ih (r - 1) j h1 h2)
      (2 * N + 1) i h1 h2
      (by push_cast; omega)
    rw [show (k + 1) * (2 * N + 1) = k * (2 * N + 1) + (2 * N + 1) by ring]
    refine hbl.trans ?_
    rw [← hc]
    have hcomb : intervBound c k r - c * (intervBound c k r -
        (if r = 0 then 0 else intervBound c k (r - 1))) ≤ intervBound c (k + 1) r := by
      split_ifs with hr
      · subst hr; unfold intervBound; simp only [pow_zero, div_one, one_mul]
        rw [pow_succ]; ring_nf; exact le_rfl
      · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        unfold intervBound
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hpow : ((k : ℝ) + 1) ^ (r' + 1) + ((k : ℝ) + 1) ^ r' ≤
            ((k : ℝ) + 1 + 1) ^ (r' + 1) := by
          have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)
            (show (k : ℝ) + 1 ≤ (k : ℝ) + 1 + 1 by linarith) r'
          rw [pow_succ, pow_succ ((k : ℝ) + 1 + 1)]
          nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1) r']
        have hx : 0 < (1 - c) ^ (r' + 1) := by positivity
        push_cast
        rw [show ((k : ℝ) + 1 + 1) = ((k + 1 : ℕ) : ℝ) + 1 by push_cast; ring] at hpow
        push_cast at hpow
        have e : ((k : ℝ) + 1) ^ (r' + 1) * (1 - c) ^ k / (1 - c) ^ (r' + 1) -
            c * (((k : ℝ) + 1) ^ (r' + 1) * (1 - c) ^ k / (1 - c) ^ (r' + 1) -
              ((k : ℝ) + 1) ^ r' * (1 - c) ^ k / (1 - c) ^ r') =
            (1 - c) ^ (k + 1) / (1 - c) ^ (r' + 1) *
              (((k : ℝ) + 1) ^ (r' + 1) + c * ((k : ℝ) + 1) ^ r') := by
          field_simp; ring
        rw [e, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hx]
        have hc' : c * ((k : ℝ) + 1) ^ r' ≤ ((k : ℝ) + 1) ^ r' :=
          mul_le_of_le_one_left (by positivity) hc1.le
        have : 0 ≤ (1 - c) ^ (k + 1) := by positivity
        nlinarith
    exact hcomb

/-- O&R p. 578 (**repeated visits**): on the finite lattice, for every `r` the probability of
at most `r` ceiling interventions in the first `n` periods tends to zero: interventions occur
infinitely often with probability one. -/
theorem interventions_infinitely_often {N : ℕ} (hN : 1 ≤ N) (r : ℕ) {i : ℤ}
    (h1 : -(N : ℤ) ≤ i) (h2 : i ≤ N) : Tendsto (fun n => intervProb N n r i) atTop (𝓝 0) := by
  set L := 2 * N + 1 with hL
  set c : ℝ := (1 / 2) ^ L with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hLpos : 0 < L := by omega
  have hdiv : Tendsto (fun n : ℕ => n / L) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b * L, fun n hn => (Nat.le_div_iff_mul_le hLpos).2 hn⟩
  have hU : Tendsto (fun k : ℕ => intervBound c k r) atTop (𝓝 0) := by
    have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one r
      (show |1 - c| < 1 by rw [abs_of_pos (by linarith)]; linarith)).comp
      (tendsto_add_atTop_nat 1)
    have h' := h.div_const ((1 - c) ^ (r + 1))
    rw [zero_div] at h'
    refine h'.congr fun k => ?_
    unfold intervBound
    simp only [Function.comp]
    push_cast
    have : (0 : ℝ) < 1 - c := by linarith
    field_simp
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hU.comp hdiv)
    (fun n => (intervProb_mem N n r i).1) fun n => ?_
  calc intervProb N n r i ≤ intervProb N ((n / L) * L) r i :=
        intervProb_antitone N r i (Nat.div_mul_le_self n L)
    _ ≤ intervBound c (n / L) r := intervProb_blocks N hN (n / L) r i h1 h2

/-- O&R p. 578 (**any finite reserve stock is exhausted**): if each intervention costs at least
`c₀ > 0` of reserves and the stock is `R`, the probability that the stock survives the first
`n` periods (at most `⌊R/c₀⌋` interventions) tends to zero. -/
theorem reserves_exhausted_almost_surely {N : ℕ} (hN : 1 ≤ N) (R c₀ : ℝ) {i : ℤ}
    (h1 : -(N : ℤ) ≤ i) (h2 : i ≤ N) :
    Tendsto (fun n => intervProb N n ⌊R / c₀⌋₊ i) atTop (𝓝 0) :=
  interventions_infinitely_often hN _ h1 h2

/-! ## Exercise 5: the full band solution with drift -/

/-- O&R Exercise 5, p. 601: the currency-band width generated by a fundamentals band of width
`L` when the locus pastes smoothly at both edges (`α = λ₁ > 0`, `β = −λ₂ > 0`):
`W(L) = L − (1/α + 1/β)(e^{αL} − 1)(e^{βL} − 1)/(e^{αL}e^{βL} − 1)`. -/
noncomputable def bandWidth (α β L : ℝ) : ℝ :=
  L - (1 / α + 1 / β) * ((Real.exp (α * L) - 1) * (Real.exp (β * L) - 1) /
    (Real.exp (α * L) * Real.exp (β * L) - 1))

/-- Two elementary exponential inequalities used for O&R Exercise 5: for `x > 0`,
`x < e^x − 1 < x e^x`. -/
theorem exp_sub_one_bounds {x : ℝ} (hx : 0 < x) :
    x < Real.exp x - 1 ∧ Real.exp x - 1 < x * Real.exp x := by
  constructor
  · linarith [Real.add_one_lt_exp hx.ne']
  · have h := Real.add_one_lt_exp (show -x ≠ 0 by linarith)
    have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos x
    nlinarith

/-- O&R Exercise 5: the width function has derivative
`W′(L) = 1 − (1/α + 1/β)(αA(B−1)² + βB(A−1)²)/(AB − 1)²` (`A = e^{αL}`, `B = e^{βL}`). -/
theorem hasDerivAt_bandWidth {α β L : ℝ} (hα : 0 < α) (hβ : 0 < β) (hL : 0 < L) :
    HasDerivAt (bandWidth α β) (1 - (1 / α + 1 / β) *
      ((α * Real.exp (α * L) * (Real.exp (β * L) - 1) ^ 2 +
        β * Real.exp (β * L) * (Real.exp (α * L) - 1) ^ 2) /
        (Real.exp (α * L) * Real.exp (β * L) - 1) ^ 2)) L := by
  set A := Real.exp (α * L) with hAdef
  set B := Real.exp (β * L) with hBdef
  have hA : HasDerivAt (fun x => Real.exp (α * x)) (A * α) L := by
    simpa using ((hasDerivAt_id' L).const_mul α).exp
  have hB : HasDerivAt (fun x => Real.exp (β * x)) (B * β) L := by
    simpa using ((hasDerivAt_id' L).const_mul β).exp
  have hA1 : 1 < A := Real.one_lt_exp_iff.2 (by positivity)
  have hB1 : 1 < B := Real.one_lt_exp_iff.2 (by positivity)
  have hD : A * B - 1 ≠ 0 := by nlinarith
  have hN := (hA.sub_const 1).mul (hB.sub_const 1)
  have hDd := (hA.mul hB).sub_const 1
  have hq := hN.div hDd hD
  have := (hasDerivAt_id' L).sub (hq.const_mul (1 / α + 1 / β))
  unfold bandWidth
  convert this using 1
  simp only [Pi.mul_apply, ← hAdef, ← hBdef]
  rw [show ((A * α) * (B - 1) + (A - 1) * (B * β)) * (A * B - 1) -
      (A - 1) * (B - 1) * (A * α * B + A * (B * β)) = α * A * (B - 1) ^ 2 + β * B * (A - 1) ^ 2
      by ring]

/-- O&R Exercise 5 (key inequality): the width is strictly increasing: `W′(L) > 0` for `L > 0`.
(Proof: `αβ(AB−1)² − (α+β)(αA(B−1)² + βB(A−1)²) = (βB(A−1) − α(B−1))(αA(B−1) − β(A−1))`, and
both factors are positive by `x < e^x − 1 < xe^x`.) -/
theorem bandWidth_deriv_pos {α β L : ℝ} (hα : 0 < α) (hβ : 0 < β) (hL : 0 < L) :
    0 < 1 - (1 / α + 1 / β) *
      ((α * Real.exp (α * L) * (Real.exp (β * L) - 1) ^ 2 +
        β * Real.exp (β * L) * (Real.exp (α * L) - 1) ^ 2) /
        (Real.exp (α * L) * Real.exp (β * L) - 1) ^ 2) := by
  set A := Real.exp (α * L) with hAdef
  set B := Real.exp (β * L) with hBdef
  obtain ⟨hs1, hs2⟩ := exp_sub_one_bounds (show 0 < α * L by positivity)
  obtain ⟨ht1, ht2⟩ := exp_sub_one_bounds (show 0 < β * L by positivity)
  rw [← hAdef] at hs1 hs2; rw [← hBdef] at ht1 ht2
  have hA1 : 1 < A := by nlinarith
  have hB1 : 1 < B := by nlinarith
  have hDpos : 0 < (A * B - 1) ^ 2 := by
    have : 0 < A * B - 1 := by nlinarith
    positivity
  -- the two factors, scaled by `L`
  have f1 : 0 < β * B * (A - 1) - α * (B - 1) := by
    have : 0 < L * (β * B * (A - 1) - α * (B - 1)) := by nlinarith
    exact pos_of_mul_pos_right this hL.le
  have f2 : 0 < α * A * (B - 1) - β * (A - 1) := by
    have : 0 < L * (α * A * (B - 1) - β * (A - 1)) := by nlinarith
    exact pos_of_mul_pos_right this hL.le
  have key : α * β * (A * B - 1) ^ 2 - (α + β) * (α * A * (B - 1) ^ 2 + β * B * (A - 1) ^ 2) =
      (β * B * (A - 1) - α * (B - 1)) * (α * A * (B - 1) - β * (A - 1)) := by ring
  have hlt : (α + β) * (α * A * (B - 1) ^ 2 + β * B * (A - 1) ^ 2) <
      α * β * (A * B - 1) ^ 2 := by nlinarith [mul_pos f1 f2]
  rw [sub_pos, show 1 / α + 1 / β = (α + β) / (α * β) by field_simp; ring, div_mul_div_comm,
    div_lt_one (by positivity)]
  exact hlt

/-- O&R Exercise 5: the width is continuous on `(0, ∞)`. -/
theorem continuousOn_bandWidth {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ContinuousOn (bandWidth α β) (Ioi 0) :=
  fun _ hL => (hasDerivAt_bandWidth hα hβ hL).continuousAt.continuousWithinAt

/-- O&R Exercise 5: `W` is strictly increasing on `(0, ∞)`. -/
theorem bandWidth_strictMonoOn {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    StrictMonoOn (bandWidth α β) (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) (continuousOn_bandWidth hα hβ) fun L hL => ?_
  rw [interior_Ioi] at hL
  rw [(hasDerivAt_bandWidth hα hβ hL).deriv]
  exact bandWidth_deriv_pos hα hβ hL

/-- O&R Exercise 5: bounds `L − (1/α + 1/β)(e^{αL} − 1) ≤ W(L)` and
`L − (1/α + 1/β) < W(L) < L` for `L > 0`. -/
theorem bandWidth_bounds {α β L : ℝ} (hα : 0 < α) (hβ : 0 < β) (hL : 0 < L) :
    L - (1 / α + 1 / β) * (Real.exp (α * L) - 1) ≤ bandWidth α β L ∧
      L - (1 / α + 1 / β) < bandWidth α β L ∧ bandWidth α β L < L := by
  set A := Real.exp (α * L); set B := Real.exp (β * L)
  have hA1 : 1 < A := Real.one_lt_exp_iff.2 (by positivity)
  have hB1 : 1 < B := Real.one_lt_exp_iff.2 (by positivity)
  have hD : 0 < A * B - 1 := by nlinarith
  have hk : 0 < 1 / α + 1 / β := by positivity
  have hP0 : 0 < (A - 1) * (B - 1) / (A * B - 1) := by
    apply div_pos _ hD; nlinarith
  have hP1 : (A - 1) * (B - 1) / (A * B - 1) < 1 := by
    rw [div_lt_one hD]; nlinarith
  have hP2 : (A - 1) * (B - 1) / (A * B - 1) ≤ A - 1 := by
    rw [div_le_iff₀ hD]
    nlinarith [mul_le_mul_of_nonneg_left (show B - 1 ≤ A * B - 1 by nlinarith)
      (show 0 ≤ A - 1 by linarith)]
  unfold bandWidth
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hP2 hk.le]
  · nlinarith [mul_lt_mul_of_pos_left hP1 hk]
  · nlinarith [mul_pos hk hP0]

/-- O&R Exercise 5: `W(L) → 0` as `L → 0⁺`. -/
theorem bandWidth_tendsto_zero {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (bandWidth α β) (𝓝[>] 0) (𝓝 0) := by
  have hlow : Tendsto (fun L => L - (1 / α + 1 / β) * (Real.exp (α * L) - 1)) (𝓝[>] 0)
      (𝓝 0) := by
    have : Tendsto (fun L => L - (1 / α + 1 / β) * (Real.exp (α * L) - 1)) (𝓝 0)
        (𝓝 (0 - (1 / α + 1 / β) * (Real.exp (α * 0) - 1))) :=
      ((continuous_id.sub (continuous_const.mul
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub
          continuous_const)))).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hup : Tendsto (fun L : ℝ => L) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with L hL using (bandWidth_bounds hα hβ hL).1
  · filter_upwards [self_mem_nhdsWithin] with L hL using (bandWidth_bounds hα hβ hL).2.2.le

/-- O&R Exercise 5: every positive currency-band width is generated by exactly one
fundamentals-band width `L > 0`. -/
theorem bandWidth_existsUnique {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {w : ℝ} (hw : 0 < w) :
    ∃! L : ℝ, 0 < L ∧ bandWidth α β L = w := by
  obtain ⟨δ, hδ, hδw⟩ : ∃ δ, 0 < δ ∧ bandWidth α β δ < w := by
    have := (bandWidth_tendsto_zero hα hβ).eventually (gt_mem_nhds hw)
    obtain ⟨δ, hδ⟩ := (this.and self_mem_nhdsWithin).exists
    exact ⟨δ, hδ.2, hδ.1⟩
  set M := max δ (w + (1 / α + 1 / β)) with hM
  have hMpos : 0 < M := lt_of_lt_of_le hδ (le_max_left _ _)
  have hMw : w ≤ bandWidth α β M := by
    have := (bandWidth_bounds hα hβ hMpos).2.1
    have : w + (1 / α + 1 / β) ≤ M := le_max_right _ _
    linarith
  obtain ⟨L, hL, hval⟩ := intermediate_value_Icc (le_max_left δ _)
    ((continuousOn_bandWidth hα hβ).mono fun x hx => lt_of_lt_of_le hδ hx.1) ⟨hδw.le, hMw⟩
  have hL0 : 0 < L := lt_of_lt_of_le hδ hL.1
  exact ⟨L, ⟨hL0, hval⟩, fun y hy => (bandWidth_strictMonoOn hα hβ).injOn hy.1 hL0
    (hy.2.trans hval.symm)⟩

/-- O&R Exercise 5: the four band conditions: value matching `G(k̲) = e̲`, `G(k̄) = ē` and smooth
pasting `G′(k̲) = G′(k̄) = 0`, for `G(k) = ημ + k + b₁e^{λ₁k} + b₂e^{λ₂k}`. -/
def IsDriftBand (d l₁ l₂ elo ehi b₁ b₂ kl kh : ℝ) : Prop :=
  kl < kh ∧ zoneSolution d b₁ b₂ l₁ l₂ kl = elo ∧ zoneSolution d b₁ b₂ l₁ l₂ kh = ehi ∧
    1 + l₁ * b₁ * Real.exp (l₁ * kl) + l₂ * b₂ * Real.exp (l₂ * kl) = 0 ∧
    1 + l₁ * b₁ * Real.exp (l₁ * kh) + l₂ * b₂ * Real.exp (l₂ * kh) = 0

/-- O&R Exercise 5: under smooth pasting at both edges, `X = b₁e^{λ₁k̲}` and `Y = b₂e^{λ₂k̲}`
are determined by the band width: `αX = (1 − B)/(AB − 1)`, `βY = (A − 1)B/(AB − 1)`. -/
theorem drift_band_XY {α β L X Y : ℝ} (hα : 0 < α) (hβ : 0 < β) (hL : 0 < L)
    (h1 : 1 + α * X + -β * Y = 0)
    (h2 : 1 + α * X * Real.exp (α * L) + -β * Y * (Real.exp (β * L))⁻¹ = 0) :
    X = (1 - Real.exp (β * L)) / (α * (Real.exp (α * L) * Real.exp (β * L) - 1)) ∧
      Y = (Real.exp (α * L) - 1) * Real.exp (β * L) /
        (β * (Real.exp (α * L) * Real.exp (β * L) - 1)) := by
  set A := Real.exp (α * L); set B := Real.exp (β * L)
  have hA1 : 1 < A := Real.one_lt_exp_iff.2 (by positivity)
  have hB1 : 1 < B := Real.one_lt_exp_iff.2 (by positivity)
  have hD : 0 < A * B - 1 := by nlinarith
  have hB0 : B ≠ 0 := by positivity
  have hBB : B * B⁻¹ = 1 := mul_inv_cancel₀ hB0
  have h2' : B + α * X * A * B - β * Y = 0 := by linear_combination B * h2 + β * Y * hBB
  have hY : β * Y * (A * B - 1) = (A - 1) * B := by linear_combination h2' - A * B * h1
  have hX : α * X * (A * B - 1) = 1 - B := by linear_combination h2' - h1
  constructor
  · rw [eq_div_iff (by positivity)]; linear_combination hX
  · rw [eq_div_iff (by positivity)]; linear_combination hY

/-- O&R Exercise 5: with smooth pasting at both edges, the currency band is
`G(k̄) − G(k̲) = W(k̄ − k̲)`. -/
theorem drift_band_width {α β L X Y : ℝ} (hα : 0 < α) (hβ : 0 < β) (hL : 0 < L)
    (h1 : 1 + α * X + -β * Y = 0)
    (h2 : 1 + α * X * Real.exp (α * L) + -β * Y * (Real.exp (β * L))⁻¹ = 0) :
    L + X * (Real.exp (α * L) - 1) + Y * ((Real.exp (β * L))⁻¹ - 1) = bandWidth α β L := by
  obtain ⟨hX, hY⟩ := drift_band_XY hα hβ hL h1 h2
  have hA1 : 1 < Real.exp (α * L) := Real.one_lt_exp_iff.2 (by positivity)
  have hB1 : 1 < Real.exp (β * L) := Real.one_lt_exp_iff.2 (by positivity)
  have hD : Real.exp (α * L) * Real.exp (β * L) - 1 ≠ 0 := by nlinarith
  rw [hX, hY]
  unfold bandWidth
  field_simp
  ring

/-- O&R Exercise 5: the pasting constant `X = b₁e^{λ₁k̲}` as a function of the band width. -/
noncomputable def driftX (α β L : ℝ) : ℝ :=
  (1 - Real.exp (β * L)) / (α * (Real.exp (α * L) * Real.exp (β * L) - 1))

/-- O&R Exercise 5: the pasting constant `Y = b₂e^{λ₂k̲}` as a function of the band width. -/
noncomputable def driftY (α β L : ℝ) : ℝ :=
  (Real.exp (α * L) - 1) * Real.exp (β * L) / (β * (Real.exp (α * L) * Real.exp (β * L) - 1))

/-- O&R Exercise 5: the explicit pasting constants satisfy both smooth-pasting conditions. -/
theorem driftXY_paste {α β L : ℝ} (hα : 0 < α) (hβ : 0 < β) (hL : 0 < L) :
    1 + α * driftX α β L + -β * driftY α β L = 0 ∧
      1 + α * driftX α β L * Real.exp (α * L) + -β * driftY α β L * (Real.exp (β * L))⁻¹ =
        0 := by
  have hA1 : 1 < Real.exp (α * L) := Real.one_lt_exp_iff.2 (by positivity)
  have hB1 : 1 < Real.exp (β * L) := Real.one_lt_exp_iff.2 (by positivity)
  have hD : Real.exp (α * L) * Real.exp (β * L) - 1 ≠ 0 := by nlinarith
  have hB0 : Real.exp (β * L) ≠ 0 := by positivity
  unfold driftX driftY
  generalize Real.exp (α * L) = A at hA1 hD ⊢
  generalize Real.exp (β * L) = B at hB1 hD hB0 ⊢
  have e1 : α * ((1 - B) / (α * (A * B - 1))) = (1 - B) / (A * B - 1) := by
    rw [mul_div_assoc', mul_div_mul_left _ _ hα.ne']
  have e2 : -β * ((A - 1) * B / (β * (A * B - 1))) = -((A - 1) * B / (A * B - 1)) := by
    rw [neg_mul, mul_div_assoc', mul_div_mul_left _ _ hβ.ne']
  rw [e1, e2]
  have hI := mul_inv_cancel₀ hD
  have hb := mul_inv_cancel₀ hB0
  constructor
  · rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination -hI
  · rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination -hI - (A - 1) * (A * B - 1)⁻¹ * hb

/-- O&R Exercise 5: any solution of the four band conditions has fundamentals width `L` with
`W(L) = ē − e̲`, pasting constants `driftX`, `driftY` and lower edge `k̲ = e̲ − ημ − X − Y`. -/
theorem driftBand_characterisation {d l₁ l₂ elo ehi b₁ b₂ kl kh : ℝ} (hl₁ : 0 < l₁)
    (hl₂ : l₂ < 0) (h : IsDriftBand d l₁ l₂ elo ehi b₁ b₂ kl kh) :
    bandWidth l₁ (-l₂) (kh - kl) = ehi - elo ∧
      b₁ * Real.exp (l₁ * kl) = driftX l₁ (-l₂) (kh - kl) ∧
      b₂ * Real.exp (l₂ * kl) = driftY l₁ (-l₂) (kh - kl) ∧
      kl = elo - d - driftX l₁ (-l₂) (kh - kl) - driftY l₁ (-l₂) (kh - kl) := by
  obtain ⟨hk, hlo, hhi, hp1, hp2⟩ := h
  set L := kh - kl with hLdef
  have hL : 0 < L := by linarith
  have hβ : 0 < -l₂ := by linarith
  set X := b₁ * Real.exp (l₁ * kl)
  set Y := b₂ * Real.exp (l₂ * kl)
  have e1 : Real.exp (l₁ * kh) = Real.exp (l₁ * kl) * Real.exp (l₁ * L) := by
    rw [← Real.exp_add]; congr 1; rw [hLdef]; ring
  have e2 : Real.exp (l₂ * kh) = Real.exp (l₂ * kl) * (Real.exp (-l₂ * L))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; congr 1; rw [hLdef]; ring
  have h1 : 1 + l₁ * X + -(-l₂) * Y = 0 := by rw [neg_neg]; linear_combination hp1
  have h2 : 1 + l₁ * X * Real.exp (l₁ * L) + -(-l₂) * Y * (Real.exp (-l₂ * L))⁻¹ = 0 := by
    rw [neg_neg]; rw [e1, e2] at hp2; linear_combination hp2
  have hw := drift_band_width hl₁ hβ hL h1 h2
  obtain ⟨hX, hY⟩ := drift_band_XY hl₁ hβ hL h1 h2
  have hwidth : ehi - elo = L + X * (Real.exp (l₁ * L) - 1) +
      Y * ((Real.exp (-l₂ * L))⁻¹ - 1) := by
    unfold zoneSolution at hlo hhi
    rw [e1, e2] at hhi
    have : kh = kl + L := by rw [hLdef]; ring
    rw [this] at hhi
    linear_combination hlo - hhi
  refine ⟨by rw [← hw, hwidth], hX, hY, ?_⟩
  unfold zoneSolution at hlo
  have : kl = elo - d - X - Y := by linarith
  rw [this, hX, hY]; rfl

/-- O&R Exercise 5, p. 601 (**the full band solution with drift**): for any drift and any
prescribed currency band `e̲ < ē`, there is exactly one quadruple `(b₁, b₂, k̲, k̄)` satisfying
value matching and smooth pasting at both edges (`λ₁ > 0 > λ₂` the characteristic roots).
The proof reduces the 4×4 system by translation invariance to the one equation
`W(k̄ − k̲) = ē − e̲` for the width, which has a unique root since `W` rises strictly from `0`
to `∞`. -/
theorem driftBand_existsUnique {d l₁ l₂ elo ehi : ℝ} (hl₁ : 0 < l₁) (hl₂ : l₂ < 0)
    (hband : elo < ehi) :
    ∃! q : ℝ × ℝ × ℝ × ℝ, IsDriftBand d l₁ l₂ elo ehi q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have hβ : 0 < -l₂ := by linarith
  obtain ⟨L, ⟨hL, hWL⟩, hLu⟩ := bandWidth_existsUnique hl₁ hβ (sub_pos.2 hband)
  obtain ⟨hp1, hp2⟩ := driftXY_paste hl₁ hβ hL
  generalize hX : driftX l₁ (-l₂) L = X at hp1 hp2
  generalize hY : driftY l₁ (-l₂) L = Y at hp1 hp2
  have hw := drift_band_width hl₁ hβ hL hp1 hp2
  obtain ⟨kl, hkl⟩ : ∃ kl, kl = elo - d - X - Y := ⟨_, rfl⟩
  have ex1 : ∀ c x, Real.exp (-c * x) * Real.exp (c * x) = 1 := fun c x => by
    rw [← Real.exp_add]; simp
  have hEneg : Real.exp (l₂ * L) = (Real.exp (-l₂ * L))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have hX' : X * Real.exp (-l₁ * kl) * Real.exp (l₁ * kl) = X := by rw [mul_assoc, ex1, mul_one]
  have hY' : Y * Real.exp (-l₂ * kl) * Real.exp (l₂ * kl) = Y := by rw [mul_assoc, ex1, mul_one]
  have eA : Real.exp (l₁ * (kl + L)) = Real.exp (l₁ * kl) * Real.exp (l₁ * L) := by
    rw [← Real.exp_add]; congr 1; ring
  have eB : Real.exp (l₂ * (kl + L)) = Real.exp (l₂ * kl) * Real.exp (l₂ * L) := by
    rw [← Real.exp_add]; congr 1; ring
  refine ⟨(X * Real.exp (-l₁ * kl), Y * Real.exp (-l₂ * kl), kl, kl + L), ?_, ?_⟩
  · refine ⟨by linarith, ?_, ?_, ?_, ?_⟩
    · unfold zoneSolution; linear_combination hX' + hY' + hkl
    · unfold zoneSolution; rw [eA, eB, hEneg]
      linear_combination Real.exp (l₁ * L) * hX' + (Real.exp (-l₂ * L))⁻¹ * hY' + hkl + hw + hWL
    · linear_combination hp1 + l₁ * hX' + l₂ * hY'
    · rw [eA, eB, hEneg]
      linear_combination hp2 + l₁ * Real.exp (l₁ * L) * hX' +
        l₂ * (Real.exp (-l₂ * L))⁻¹ * hY'
  · rintro ⟨b₁, b₂, kl', kh'⟩ h
    obtain ⟨hw', hX1, hY1, hkl1⟩ := driftBand_characterisation hl₁ hl₂ h
    have hk' := h.1
    simp only at hw' hX1 hY1 hkl1 hk'
    have hLL : kh' - kl' = L := hLu _ ⟨by linarith, hw'⟩
    rw [hLL] at hX1 hY1 hkl1
    rw [hX] at hX1 hkl1
    rw [hY] at hY1 hkl1
    have hkk : kl' = kl := by rw [hkl1, hkl]
    subst hkk
    have hb1 : b₁ = X * Real.exp (-l₁ * kl') := by
      linear_combination (-b₁) * ex1 l₁ kl' + Real.exp (-l₁ * kl') * hX1
    have hb2 : b₂ = Y * Real.exp (-l₂ * kl') := by
      linear_combination (-b₂) * ex1 l₂ kl' + Real.exp (-l₂ * kl') * hY1
    simp only [Prod.mk.injEq]
    exact ⟨hb1, hb2, trivial, by linarith⟩

/-! ## Convergence of the lattice zone to the continuous zone as `Δ → 0` -/

/-- O&R §8.5 (lattice scaling `h = Δ²/v²`): the lattice characteristic root
`θ_Δ = 2 arsinh(λΔ/2)`. -/
noncomputable def latTheta (l Δ : ℝ) : ℝ := 2 * Real.arsinh (l * Δ / 2)

/-- O&R §8.5: `sinh(θ_Δ/2) = λΔ/2`. -/
theorem sinh_half_latTheta (l Δ : ℝ) : Real.sinh (latTheta l Δ / 2) = l * Δ / 2 := by
  unfold latTheta; rw [mul_div_cancel_left₀ _ two_ne_zero, Real.sinh_arsinh]

/-- O&R §8.5: `cosh θ_Δ = 1 + λ²Δ²/2`. -/
theorem cosh_latTheta (l Δ : ℝ) : Real.cosh (latTheta l Δ) = 1 + l ^ 2 * Δ ^ 2 / 2 := by
  have h := sinh_half_latTheta l Δ
  have e : latTheta l Δ = 2 * (latTheta l Δ / 2) := by ring
  rw [e, Real.cosh_two_mul, Real.cosh_sq, h]; ring

/-- O&R §8.5 (lattice scaling): with `λ = √(2/(ηv²))`, `a = η/h = ηv²/Δ²` and
`θ = θ_Δ`, the characteristic equation `cosh θ = 1 + 1/a` of the lattice holds. -/
theorem latTheta_char {η v Δ : ℝ} (hη : 0 < η) (hv : 0 < v) (hΔ : 0 < Δ) :
    Real.cosh (latTheta (Real.sqrt (2 / (η * v ^ 2))) Δ) = 1 + 1 / (η * v ^ 2 / Δ ^ 2) := by
  rw [cosh_latTheta, Real.sq_sqrt (by positivity)]
  field_simp

/-- O&R §8.5: `θ_Δ > 0` for `λ, Δ > 0`. -/
theorem latTheta_pos {l Δ : ℝ} (hl : 0 < l) (hΔ : 0 < Δ) : 0 < latTheta l Δ := by
  unfold latTheta; have := Real.arsinh_pos_iff.2 (show 0 < l * Δ / 2 by positivity)
  linarith

/-- O&R §8.5: `θ_Δ/Δ → λ` as `Δ → 0⁺`. -/
theorem latTheta_div_tendsto {l : ℝ} (hl : 0 < l) :
    Tendsto (fun Δ => latTheta l Δ / Δ) (𝓝[>] 0) (𝓝 l) := by
  have hd := Real.hasDerivAt_arsinh 0
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    Real.sqrt_one, inv_one] at hd
  have hs := hasDerivAt_iff_tendsto_slope.1 hd
  have hy : Tendsto (fun Δ : ℝ => l * Δ / 2) (𝓝[>] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun Δ : ℝ => l * Δ / 2) (𝓝 0) (𝓝 (l * 0 / 2)) :=
        ((continuous_const.mul continuous_id).div_const 2).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with Δ hΔ
      simp only [mem_Ioi] at hΔ; simp only [mem_compl_iff, mem_singleton_iff]; positivity
  have h2 := (hs.comp hy).const_mul l
  rw [mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with Δ hΔ
  simp only [mem_Ioi] at hΔ
  simp only [Function.comp, slope_def_field, Real.arsinh_zero, sub_zero, latTheta]
  field_simp

/-- O&R §8.5: the lattice solution written as a function of fundamentals
`e(k) = k − sinh(μk)/(λ cosh μK)` (`μ = θ/Δ`, `K` the pasting point); `μ = λ` gives the
continuous `S`. -/
noncomputable def latRate (l μ K k : ℝ) : ℝ := k - Real.sinh (μ * k) / (l * Real.cosh (μ * K))

/-- O&R (85): the continuous smooth-pasting locus with pasting point `K` is `latRate λ λ K`. -/
theorem symS_eq_latRate {l : ℝ} (hl : 0 < l) (K k : ℝ) :
    symS l (1 / (2 * l * Real.cosh (l * K))) k = latRate l l K k := by
  unfold symS latRate
  have := Real.cosh_pos (l * K)
  field_simp

/-- O&R §8.5: at the lattice nodes, with `(N + ½)Δ = K` and `θ = θ_Δ`, the closed-form
lattice solution is `latRate λ (θ/Δ) K (iΔ)`. -/
theorem latticeSol_eq_latRate {l Δ : ℝ} (hl : 0 < l) (hΔ : 0 < Δ) (N i : ℤ) :
    latticeSol Δ (latTheta l Δ) (latticeCoeff Δ (latTheta l Δ) N) i =
      latRate l (latTheta l Δ / Δ) ((N + 1 / 2) * Δ) (i * Δ) := by
  unfold latticeSol latRate latticeCoeff
  rw [sinh_step, sinh_half_latTheta]
  have hc := Real.cosh_pos (latTheta l Δ * (N + 1 / 2))
  have e1 : latTheta l Δ / Δ * (i * Δ) = latTheta l Δ * i := by field_simp
  have e2 : latTheta l Δ / Δ * ((N + 1 / 2) * Δ) = latTheta l Δ * (N + 1 / 2) := by field_simp
  rw [e1, e2]
  field_simp

/-- O&R §8.5: `|sinh x| ≤ cosh x`. -/
theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  rw [abs_le]
  constructor
  · have := Real.sinh_lt_cosh (-x); rw [Real.sinh_neg, Real.cosh_neg] at this; linarith
  · exact (Real.sinh_lt_cosh x).le

/-- O&R §8.5 (**uniform error bound**): for `|k| ≤ K`,
`|latRate λ μ K k − S_K(k)| ≤ (2K/λ)|μ − λ|`. -/
theorem latRate_uniform_bound {l K : ℝ} (hl : 0 < l) (hK : 0 ≤ K) (μ : ℝ) {k : ℝ}
    (hk : |k| ≤ K) : |latRate l μ K k - latRate l l K k| ≤ 2 * K / l * |μ - l| := by
  set F : ℝ → ℝ := fun m => Real.sinh (m * k) / Real.cosh (m * K) with hF
  set F' : ℝ → ℝ := fun m => (k * Real.cosh (m * k) * Real.cosh (m * K) -
    Real.sinh (m * k) * (K * Real.sinh (m * K))) / Real.cosh (m * K) ^ 2 with hF'
  have hder : ∀ m ∈ (univ : Set ℝ), HasDerivWithinAt F (F' m) univ m := by
    intro m _
    have h1 : HasDerivAt (fun x => Real.sinh (x * k)) (Real.cosh (m * k) * k) m := by
      simpa using ((hasDerivAt_id' m).mul_const k).sinh
    have h2 : HasDerivAt (fun x => Real.cosh (x * K)) (Real.sinh (m * K) * K) m := by
      simpa using ((hasDerivAt_id' m).mul_const K).cosh
    have := (h1.div h2 (Real.cosh_pos _).ne').hasDerivWithinAt (s := univ)
    convert this using 1
    simp only [hF']; ring
  have hbound : ∀ m ∈ (univ : Set ℝ), ‖F' m‖ ≤ 2 * K := by
    intro m _
    have hc := Real.cosh_pos (m * K)
    have hck : Real.cosh (m * k) ≤ Real.cosh (m * K) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hk.trans (le_abs_self K)) (abs_nonneg m)
    have hsk := (abs_sinh_le_cosh (m * k)).trans hck
    have hsK := abs_sinh_le_cosh (m * K)
    rw [Real.norm_eq_abs, hF', abs_div, abs_of_pos (by positivity : 0 < Real.cosh (m * K) ^ 2),
      div_le_iff₀ (by positivity)]
    calc |k * Real.cosh (m * k) * Real.cosh (m * K) - Real.sinh (m * k) * (K * Real.sinh (m * K))|
        ≤ |k * Real.cosh (m * k) * Real.cosh (m * K)| +
            |Real.sinh (m * k) * (K * Real.sinh (m * K))| := abs_sub _ _
      _ ≤ K * Real.cosh (m * K) * Real.cosh (m * K) +
            Real.cosh (m * K) * (K * Real.cosh (m * K)) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.cosh_pos (m * k)),
            abs_of_pos hc, abs_of_nonneg hK]
          gcongr
      _ = 2 * K * Real.cosh (m * K) ^ 2 := by ring
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound convex_univ
    (mem_univ μ) (mem_univ l)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have e : latRate l μ K k - latRate l l K k = (F l - F μ) / l := by
    simp only [latRate, hF]; field_simp; ring
  rw [e, abs_div, abs_of_pos hl, div_le_iff₀ hl, abs_sub_comm μ l]
  calc |F l - F μ| ≤ 2 * K * |l - μ| := hmvt
    _ = 2 * K / l * |l - μ| * l := by field_simp

/-- O&R §8.5 (**uniform convergence on the band**): the extended lattice solution converges to
the continuous locus uniformly on `[−K, K]` as `Δ → 0`. -/
theorem latRate_uniform_tendsto {l K : ℝ} (hl : 0 < l) (hK : 0 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Δ in 𝓝[>] 0, ∀ k : ℝ, |k| ≤ K →
      |latRate l (latTheta l Δ / Δ) K k - latRate l l K k| < ε := by
  have ht := latTheta_div_tendsto hl
  have hC : 0 ≤ 2 * K / l := by positivity
  have hev : ∀ᶠ Δ in 𝓝[>] 0, 2 * K / l * |latTheta l Δ / Δ - l| < ε := by
    have h1 : Tendsto (fun Δ => 2 * K / l * |latTheta l Δ / Δ - l|) (𝓝[>] 0)
        (𝓝 (2 * K / l * |l - l|)) := ((ht.sub_const l).abs).const_mul _
    rw [sub_self, abs_zero, mul_zero] at h1
    exact h1.eventually (gt_mem_nhds hε)
  filter_upwards [hev] with Δ hΔ k hk
  exact lt_of_le_of_lt (latRate_uniform_bound hl hK _ hk) hΔ

/-- O&R §8.5 (**convergence of the lattice equilibrium**): fix the fundamental pasting point
`K > 0` and put `Δ_N = K/(N + ½)`, `h_N = Δ_N²/v²`. Then for every `ε > 0`, for all large `N`,
every lattice equilibrium `e` (with `a = η/h_N`) satisfies `|e_i − S(iΔ_N)| < ε` at every node
`|i| ≤ N`, where `S` is the continuous smooth-pasting locus with pasting point `K`. -/
theorem lattice_converges {η v K : ℝ} (hη : 0 < η) (hv : 0 < v) (hK : 0 < K) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ e : ℤ → ℝ,
      IsLatticeEqm (η * v ^ 2 / (K / (N + 1 / 2)) ^ 2) (K / (N + 1 / 2)) N e →
      ∀ i : ℤ, -(N : ℤ) ≤ i → i ≤ N →
        |e i - symS (Real.sqrt (2 / (η * v ^ 2)))
          (1 / (2 * Real.sqrt (2 / (η * v ^ 2)) *
            Real.cosh (Real.sqrt (2 / (η * v ^ 2)) * K))) (i * (K / (N + 1 / 2)))| < ε := by
  set l := Real.sqrt (2 / (η * v ^ 2)) with hl
  have hl0 : 0 < l := (lambda_spec hη hv).1
  have hΔ : Tendsto (fun N : ℕ => K / ((N : ℝ) + 1 / 2)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun N => by
      simp only [mem_Ioi]; positivity⟩
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _
      tendsto_natCast_atTop_atTop)
  filter_upwards [hΔ.eventually (latRate_uniform_tendsto hl0 hK.le hε),
    eventually_ge_atTop 1] with N hN hN1 e he i h1 h2
  set Δ := K / ((N : ℝ) + 1 / 2) with hΔdef
  have hΔ0 : 0 < Δ := by positivity
  have hKΔ : ((N : ℤ) + 1 / 2 : ℝ) * Δ = K := by
    rw [hΔdef]; push_cast; field_simp
  have hsol := latticeSol_isEqm (by positivity) hΔ0 (latTheta_pos hl0 hΔ0)
    (latTheta_char hη hv hΔ0) (N := N) (by exact_mod_cast hN1)
  have heq := latticeEqm_unique (by positivity) (by positivity) he hsol i h1 h2
  rw [heq, latticeSol_eq_latRate hl0 hΔ0, hKΔ, symS_eq_latRate hl0]
  apply hN
  have hi : |(i : ℝ)| ≤ N := by
    rw [abs_le]; constructor <;> [exact_mod_cast (by omega : -(N : ℤ) ≤ i);
      exact_mod_cast h2]
  rw [abs_mul, abs_of_pos hΔ0]
  calc |(i : ℝ)| * Δ ≤ N * Δ := mul_le_mul_of_nonneg_right hi hΔ0.le
    _ ≤ K := by rw [← hKΔ]; push_cast; nlinarith

/-- O&R §8.5: the lattice rate at the top node `N` as a function of the spacing `Δ`
(lattice value matching sets it equal to the currency ceiling `ē`). -/
noncomputable def topValue (l : ℝ) (N : ℕ) (Δ : ℝ) : ℝ :=
  N * Δ - Real.sinh (N * latTheta l Δ) / (l * Real.cosh ((N + 1 / 2) * latTheta l Δ))

/-- O&R §8.5: for `Δ > 0` the top value is the lattice solution at node `N` (pasting point
`(N + ½)Δ`). -/
theorem topValue_eq_latticeSol {l Δ : ℝ} (hl : 0 < l) (hΔ : 0 < Δ) (N : ℕ) :
    topValue l N Δ = latticeSol Δ (latTheta l Δ) (latticeCoeff Δ (latTheta l Δ) N) N ∧
      topValue l N Δ = latRate l (latTheta l Δ / Δ) ((N + 1 / 2) * Δ) (N * Δ) := by
  have h := latticeSol_eq_latRate hl hΔ N N
  push_cast at h
  have e : topValue l N Δ = latRate l (latTheta l Δ / Δ) ((N + 1 / 2) * Δ) (N * Δ) := by
    unfold topValue latRate
    have e1 : latTheta l Δ / Δ * (N * Δ) = N * latTheta l Δ := by field_simp
    have e2 : latTheta l Δ / Δ * ((N + 1 / 2) * Δ) = (N + 1 / 2) * latTheta l Δ := by
      field_simp
    rw [e1, e2]
  exact ⟨e.trans h.symm, e⟩

/-- O&R §8.5: the top value is continuous in `Δ`. -/
theorem continuous_topValue {l : ℝ} (hl : 0 < l) (N : ℕ) : Continuous (topValue l N) := by
  have hθ : Continuous (latTheta l) := by
    unfold latTheta
    exact continuous_const.mul (Real.continuous_arsinh.comp
      ((continuous_const.mul continuous_id).div_const 2))
  unfold topValue
  refine Continuous.sub (continuous_const.mul continuous_id)
    (Continuous.div (Real.continuous_sinh.comp (continuous_const.mul hθ))
      (continuous_const.mul (Real.continuous_cosh.comp (continuous_const.mul hθ)))
      fun x => mul_ne_zero hl.ne' (Real.cosh_pos _).ne')

/-- O&R §8.5: `NΔ − 1/λ ≤ topValue ≤ NΔ` for `Δ ≥ 0`. -/
theorem topValue_bounds {l : ℝ} (hl : 0 < l) (N : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    N * Δ - 1 / l ≤ topValue l N Δ ∧ topValue l N Δ ≤ N * Δ := by
  have hθ : 0 ≤ latTheta l Δ := by
    unfold latTheta; have := Real.arsinh_nonneg_iff.2 (show 0 ≤ l * Δ / 2 by positivity)
    linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hs : 0 ≤ Real.sinh (N * latTheta l Δ) := Real.sinh_nonneg_iff.2 (mul_nonneg hN0 hθ)
  have hc := Real.cosh_pos ((N + 1 / 2) * latTheta l Δ)
  have hle : Real.sinh (N * latTheta l Δ) ≤ Real.cosh ((N + 1 / 2) * latTheta l Δ) := by
    refine (Real.sinh_lt_cosh _).le.trans ?_
    rw [Real.cosh_le_cosh, abs_of_nonneg (mul_nonneg hN0 hθ),
      abs_of_nonneg (mul_nonneg (by linarith) hθ)]
    nlinarith
  unfold topValue
  constructor
  · have : Real.sinh (N * latTheta l Δ) / (l * Real.cosh ((N + 1 / 2) * latTheta l Δ)) ≤ 1 / l :=
      by rw [div_le_div_iff₀ (by positivity) hl]; nlinarith
    linarith
  · have : 0 ≤ Real.sinh (N * latTheta l Δ) / (l * Real.cosh ((N + 1 / 2) * latTheta l Δ)) :=
      by positivity
    linarith

/-- A product inequality for `cosh` used for O&R §8.5: for `0 ≤ a ≤ b` and `0 ≤ θ₁ ≤ θ₂`,
`cosh(aθ₂) cosh(bθ₁) ≤ cosh(aθ₁) cosh(bθ₂)` (the ratio `cosh(aθ)/cosh(bθ)` decreases). -/
theorem cosh_ratio_antitone {a b θ₁ θ₂ : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (h1 : 0 ≤ θ₁)
    (h12 : θ₁ ≤ θ₂) :
    Real.cosh (a * θ₂) * Real.cosh (b * θ₁) ≤ Real.cosh (a * θ₁) * Real.cosh (b * θ₂) := by
  have prod : ∀ x y, 2 * (Real.cosh x * Real.cosh y) = Real.cosh (x + y) + Real.cosh (x - y) := by
    intro x y; rw [Real.cosh_add, Real.cosh_sub]; ring
  have c1 : Real.cosh (a * θ₂ + b * θ₁) ≤ Real.cosh (a * θ₁ + b * θ₂) := by
    have hθ2 : 0 ≤ θ₂ := le_trans h1 h12
    rw [Real.cosh_le_cosh, abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)]
    nlinarith
  have c2 : Real.cosh (a * θ₂ - b * θ₁) ≤ Real.cosh (a * θ₁ - b * θ₂) := by
    rw [Real.cosh_le_cosh]
    have hr : |a * θ₂ - b * θ₁| ≤ b * θ₂ - a * θ₁ := abs_le.2 ⟨by nlinarith, by nlinarith⟩
    have : |a * θ₁ - b * θ₂| = b * θ₂ - a * θ₁ := by
      rw [abs_sub_comm]; exact abs_of_nonneg (by nlinarith)
    linarith
  nlinarith [prod (a * θ₂) (b * θ₁), prod (a * θ₁) (b * θ₂)]

/-- O&R §8.5: the top value is the sum of the lattice increments,
`topValue = Σ_{i<N} Δ(1 − cosh θ(i+½)/cosh θ(N+½))`. -/
theorem topValue_eq_sum {l Δ : ℝ} (hl : 0 < l) (hΔ : 0 < Δ) (N : ℕ) :
    topValue l N Δ = ∑ i ∈ Finset.range N, Δ * (1 - Real.cosh (latTheta l Δ * (i + 1 / 2)) /
      Real.cosh (latTheta l Δ * (N + 1 / 2))) := by
  rw [(topValue_eq_latticeSol hl hΔ N).1]
  have hθ := latTheta_pos hl hΔ
  have h0 : latticeSol Δ (latTheta l Δ) (latticeCoeff Δ (latTheta l Δ) N) 0 = 0 := by
    simp [latticeSol]
  have htel := Finset.sum_range_sub
    (fun i : ℕ => latticeSol Δ (latTheta l Δ) (latticeCoeff Δ (latTheta l Δ) N) i) N
  simp only [Nat.cast_zero] at htel
  rw [h0, sub_zero] at htel
  rw [← htel]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := latticeSol_increment (Δ := Δ) hθ N i
  push_cast at this ⊢
  exact this

/-- O&R §8.5: the top value is strictly increasing in the spacing `Δ > 0` (`N ≥ 1`). -/
theorem topValue_strictMonoOn {l : ℝ} (hl : 0 < l) {N : ℕ} (hN : 1 ≤ N) :
    StrictMonoOn (topValue l N) (Ioi 0) := by
  intro Δ₁ h1 Δ₂ h2 h12
  simp only [mem_Ioi] at h1 h2
  rw [topValue_eq_sum hl h1, topValue_eq_sum hl h2]
  have hθ1 := latTheta_pos hl h1
  have hθ12 : latTheta l Δ₁ < latTheta l Δ₂ := by
    unfold latTheta
    have := Real.arsinh_strictMono (show l * Δ₁ / 2 < l * Δ₂ / 2 by nlinarith)
    linarith
  refine Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.2 (by omega)⟩ fun i hi => ?_
  have hiN : (i : ℝ) + 1 / 2 < N + 1 / 2 := by
    have h3 : (i : ℝ) < N := by exact_mod_cast Finset.mem_range.1 hi
    linarith
  set r₁ := Real.cosh (latTheta l Δ₁ * (i + 1 / 2)) / Real.cosh (latTheta l Δ₁ * (N + 1 / 2))
  set r₂ := Real.cosh (latTheta l Δ₂ * (i + 1 / 2)) / Real.cosh (latTheta l Δ₂ * (N + 1 / 2))
  have hc1 := Real.cosh_pos (latTheta l Δ₁ * (N + 1 / 2))
  have hc2 := Real.cosh_pos (latTheta l Δ₂ * (N + 1 / 2))
  have hr1 : r₁ < 1 := by
    rw [div_lt_one hc1, Real.cosh_lt_cosh, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    nlinarith
  have hr21 : r₂ ≤ r₁ := by
    rw [div_le_div_iff₀ hc2 hc1]
    have := cosh_ratio_antitone (a := (i : ℝ) + 1 / 2) (b := (N : ℝ) + 1 / 2) (by positivity)
      hiN.le hθ1.le hθ12.le
    rw [mul_comm (latTheta l Δ₂) _, mul_comm (latTheta l Δ₁) ((N : ℝ) + 1 / 2),
      mul_comm (latTheta l Δ₁) ((i : ℝ) + 1 / 2), mul_comm (latTheta l Δ₂) ((N : ℝ) + 1 / 2)]
    linarith
  nlinarith

/-- O&R §8.5 (**lattice value matching**): for each `N ≥ 1` and ceiling `ē > 0` there is a
unique spacing `Δ_N > 0` for which the lattice rate at the top node equals `ē`. -/
theorem existsUnique_lattice_spacing {l : ℝ} (hl : 0 < l) {N : ℕ} (hN : 1 ≤ N) {ebar : ℝ}
    (he : 0 < ebar) : ∃! Δ : ℝ, 0 < Δ ∧ topValue l N Δ = ebar := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set M := (ebar + 1 / l) / N with hM
  have hM0 : 0 ≤ M := by positivity
  have h0 : topValue l N 0 = 0 := by simp [topValue, latTheta]
  have hMv : ebar ≤ topValue l N M := by
    have := (topValue_bounds hl N hM0).1
    have e : (N : ℝ) * M = ebar + 1 / l := by rw [hM]; field_simp
    linarith
  obtain ⟨Δ, hΔ, hval⟩ := intermediate_value_Icc hM0 (continuous_topValue hl N).continuousOn
    ⟨by rw [h0]; exact he.le, hMv⟩
  have hΔ0 : 0 < Δ := by
    rcases eq_or_lt_of_le hΔ.1 with h | h
    · rw [← h, h0] at hval; linarith
    · exact h
  exact ⟨Δ, ⟨hΔ0, hval⟩, fun y hy => (topValue_strictMonoOn hl hN).injOn hy.1 hΔ0
    (hy.2.trans hval.symm)⟩

/-- O&R §8.5: the continuous locus with pasting point `K` moves by at most `δ` between
`K − δ` and `K` (its slope `1 − cosh λk/cosh λK` lies in `[0, 1]` on the band). -/
theorem latRate_near_edge {l K δ : ℝ} (hl : 0 < l) (hδ : 0 ≤ δ) (hδK : δ ≤ 2 * K) :
    |latRate l l K K - latRate l l K (K - δ)| ≤ δ := by
  have hK : 0 ≤ K := by linarith
  have hder : ∀ x ∈ Icc (K - δ) K, HasDerivWithinAt (latRate l l K)
      (1 - Real.cosh (l * x) / Real.cosh (l * K)) (Icc (K - δ) K) x := by
    intro x _
    have h1 : HasDerivAt (fun y => Real.sinh (l * y)) (Real.cosh (l * x) * l) x := by
      simpa using ((hasDerivAt_id' x).const_mul l).sinh
    have := ((hasDerivAt_id' x).sub (h1.div_const (l * Real.cosh (l * K)))).hasDerivWithinAt
      (s := Icc (K - δ) K)
    unfold latRate
    convert this using 1
    have := Real.cosh_pos (l * K)
    field_simp
  have hbound : ∀ x ∈ Icc (K - δ) K, ‖1 - Real.cosh (l * x) / Real.cosh (l * K)‖ ≤ 1 := by
    intro x hx
    have hc := Real.cosh_pos (l * K)
    have hle : Real.cosh (l * x) ≤ Real.cosh (l * K) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos hl, abs_of_nonneg hK]
      exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith [hx.1], hx.2⟩) hl.le
    have hr : Real.cosh (l * x) / Real.cosh (l * K) ≤ 1 := (div_le_one hc).2 hle
    have hr0 : 0 < Real.cosh (l * x) / Real.cosh (l * K) := div_pos (Real.cosh_pos _) hc
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_Icc _ _)
    (⟨le_rfl, by linarith⟩ : K - δ ∈ Icc (K - δ) K) (⟨by linarith, le_rfl⟩ : K ∈ Icc (K - δ) K)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, show K - (K - δ) = δ by ring, abs_of_nonneg hδ,
    one_mul] at this
  exact this

/-- O&R §8.5 (**the lattice band edge converges**): if `Δ_N` solves the lattice
value-matching condition for the ceiling `ē` (for every `N ≥ 1`) and `k̄ > 0` is the
continuous band edge (`k̄ − tanh(λk̄)/λ = ē`), then the lattice pasting point
`(N + ½)Δ_N → k̄` (and `Δ_N → 0`). -/
theorem lattice_edge_tendsto {l : ℝ} (hl : 0 < l) {ebar kb : ℝ} (he : 0 < ebar) (hkb : 0 < kb)
    (hedge : edgeMap l kb = ebar) {Δ : ℕ → ℝ}
    (hΔ : ∀ N : ℕ, 1 ≤ N → 0 < Δ N ∧ topValue l N (Δ N) = ebar) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1 / 2) * Δ N) atTop (𝓝 kb) := by
  set C := ebar + 1 / l with hC
  have hC0 : 0 < C := by positivity
  -- `Δ_N ≤ C/N`
  have hΔle : ∀ N : ℕ, 1 ≤ N → Δ N ≤ C / N := by
    intro N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have := (topValue_bounds hl N (hΔ N hN).1.le).1
    rw [(hΔ N hN).2] at this
    rw [le_div_iff₀ hN']; linarith
  have hΔ0 : Tendsto Δ atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := (0 : ℝ)))
        ((tendsto_const_nhds (x := C)).div_atTop tendsto_natCast_atTop_atTop) ?_ ?_
      · filter_upwards [eventually_ge_atTop 1] with N hN using (hΔ N hN).1.le
      · filter_upwards [eventually_ge_atTop 1] with N hN using hΔle N hN
    · filter_upwards [eventually_ge_atTop 1] with N hN using (hΔ N hN).1
  have hμ := (latTheta_div_tendsto hl).comp hΔ0
  -- the error bound `|edgeMap(K_N) − ē| ≤ (3C/λ)|μ_N − λ| + Δ_N/2`
  have hbnd : ∀ N : ℕ, 1 ≤ N → |edgeMap l (((N : ℝ) + 1 / 2) * Δ N) - ebar| ≤
      2 * (2 * C) / l * |latTheta l (Δ N) / Δ N - l| + Δ N / 2 := by
    intro N hN
    obtain ⟨hpos, hval⟩ := hΔ N hN
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    set K := ((N : ℝ) + 1 / 2) * Δ N with hK
    have hK0 : 0 ≤ K := by positivity
    have hKC : K ≤ 2 * C := by
      have := hΔle N hN
      calc K = ((N : ℝ) + 1 / 2) * Δ N := rfl
        _ ≤ ((N : ℝ) + 1 / 2) * (C / N) := mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ 2 * C := by rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    have hval' := (topValue_eq_latticeSol hl hpos N).2
    rw [hval] at hval'
    have hk : |(N : ℝ) * Δ N| ≤ K := by
      rw [abs_of_nonneg (by positivity), hK]; nlinarith
    have e1 := latRate_uniform_bound hl hK0 (latTheta l (Δ N) / Δ N) hk
    rw [← hval'] at e1
    have e2 := latRate_near_edge (K := K) hl (show 0 ≤ Δ N / 2 by positivity)
      (by rw [hK]; nlinarith)
    have e3 : K - Δ N / 2 = (N : ℝ) * Δ N := by rw [hK]; ring
    rw [e3] at e2
    have e4 : latRate l l K K = edgeMap l K := rfl
    rw [e4] at e2
    have e5 : 2 * K / l * |latTheta l (Δ N) / Δ N - l| ≤
        2 * (2 * C) / l * |latTheta l (Δ N) / Δ N - l| := by gcongr
    calc |edgeMap l K - ebar| = |(edgeMap l K - latRate l l K (N * Δ N)) +
          (latRate l l K (N * Δ N) - ebar)| := by ring_nf
      _ ≤ |edgeMap l K - latRate l l K (N * Δ N)| + |latRate l l K (N * Δ N) - ebar| :=
          abs_add_le _ _
      _ ≤ Δ N / 2 + 2 * K / l * |latTheta l (Δ N) / Δ N - l| := by
          rw [abs_sub_comm (latRate l l K _) ebar]; exact add_le_add e2 e1
      _ ≤ _ := by linarith
  have hlim : Tendsto (fun N : ℕ => edgeMap l (((N : ℝ) + 1 / 2) * Δ N)) atTop (𝓝 ebar) := by
    have hr : Tendsto (fun N : ℕ => 2 * (2 * C) / l * |latTheta l (Δ N) / Δ N - l| + Δ N / 2)
        atTop (𝓝 (2 * (2 * C) / l * |l - l| + 0 / 2)) :=
      (((hμ.sub_const l).abs).const_mul _).add
        ((hΔ0.mono_right nhdsWithin_le_nhds).div_const 2)
    rw [sub_self, abs_zero, mul_zero, zero_div, add_zero] at hr
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hr
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]; exact hbnd N hN
  -- invert the strictly increasing continuous `edgeMap`
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := min ε (kb / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by positivity)
  have hmono := edgeMap_strictMonoOn hl
  have hup : ebar < edgeMap l (kb + ε') := by
    rw [← hedge]; exact hmono (le_of_lt hkb) (by simp only [mem_Ici]; positivity) (by linarith)
  have hlo : edgeMap l (kb - ε') < ebar := by
    rw [← hedge]
    exact hmono (by simp only [mem_Ici]; linarith [min_le_right ε (kb / 2)]) (le_of_lt hkb)
      (by linarith)
  have hev := (hlim.eventually (Ioo_mem_nhds hlo hup)).and (eventually_ge_atTop 1)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨⟨h1, h2⟩, hN1⟩ := hN₀ N hN
  have hKpos : 0 ≤ ((N : ℝ) + 1 / 2) * Δ N := by
    have := (hΔ N hN1).1; positivity
  have hlt1 : ((N : ℝ) + 1 / 2) * Δ N < kb + ε' := by
    by_contra hc; push Not at hc
    have := hmono.monotoneOn (by simp only [mem_Ici]; positivity) (by simpa using hKpos) hc
    linarith
  have hlt2 : kb - ε' < ((N : ℝ) + 1 / 2) * Δ N := by
    by_contra hc; push Not at hc
    have := hmono.monotoneOn (by simpa using hKpos)
      (by simp only [mem_Ici]; linarith [min_le_right ε (kb / 2)]) hc
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [min_le_left ε (kb / 2)]

/-- O&R §8.5 (**lattice → continuous, prescribed band**): for a ceiling `ē > 0`, the lattice
spacings `Δ_N` fixed by lattice value matching exist, and the lattice pasting points
`(N + ½)Δ_N` converge to the unique continuous band edge `k̄`. -/
theorem lattice_edge_converges {l : ℝ} (hl : 0 < l) {ebar : ℝ} (he : 0 < ebar) :
    ∃ kb : ℝ, 0 < kb ∧ edgeMap l kb = ebar ∧ ∃ Δ : ℕ → ℝ,
      (∀ N : ℕ, 1 ≤ N → 0 < Δ N ∧ topValue l N (Δ N) = ebar) ∧
      Tendsto (fun N : ℕ => ((N : ℝ) + 1 / 2) * Δ N) atTop (𝓝 kb) := by
  obtain ⟨kb, ⟨hkb, hedge⟩, -⟩ := existsUnique_edge hl he
  have hex : ∀ N : ℕ, ∃ d : ℝ, 1 ≤ N → 0 < d ∧ topValue l N d = ebar := by
    intro N
    by_cases hN : 1 ≤ N
    · obtain ⟨d, hd, -⟩ := existsUnique_lattice_spacing hl hN he
      exact ⟨d, fun _ => hd⟩
    · exact ⟨0, fun h => absurd h hN⟩
  choose Δ hΔ using hex
  exact ⟨kb, hkb, hedge, Δ, hΔ, lattice_edge_tendsto hl he hkb hedge hΔ⟩

end ObstfeldRogoff.MoneyExchangeRates.TargetZone

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Speculative bubbles in the money-in-the-utility model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §8.3.5
(pp. 538–546) and Exercise 2 (pp. 599–600).

With `u = log C + v(M/P)` (45), `(1+r)β = 1` and money growing at `1 + μ`, real balances obey
(46): `(β/(1+μ)) m_{t+1} = m_t(1 − C̄v'(m_t))`. We prove:

* **equilibrium ⟺ (46) + the individual TVC** (`equilibrium_iff`): a price path supports the
  equilibrium plan (optimal for the household, via `MoneyInUtility.isOptimal_iff`) iff (46)
  holds at every date and `liminf β^T m_T = 0` (fn 31);
* **the log case with money growth** (Fig. 8.2): the explicit saddle-path solution; paths below
  the steady state reach NEGATIVE real balances in finite time (so they are infeasible, not
  merely divergent); `β^T m_T = β^T m̄ + (1+μ)^T(m_0 − m̄)`; the steady state is the UNIQUE
  equilibrium when `μ ≥ 0` and is an equilibrium whenever `1 + μ > β`; but when
  `β < 1 + μ < 1` EVERY `m_0 ≥ m̄` is an equilibrium (a correction: the book's TVC argument
  needs `μ ≥ 0`);
* (48) and **(49) ⟺ (50)**; for general concave `v` with constant money, deflationary paths
  grow geometrically and `β^T m_T = m_0 Π(1 − C̄v'(m_s))`, so **the TVC holds iff
  `Σ v'(m_t) = ∞`** (`tvc_iff_not_summable`). If `v` is bounded above the sum is finite and
  deflations are ruled out (fn 32, made precise); so too for `v = log`. **Counterexamples**:
  `v = am + log m` and the logarithmic-integral utility `v(m) = ∫₀^m dt/log(t+e)`
  (`v' ≈ 1/log m`) are strictly concave, increasing and unbounded, and admit GENUINE
  deflationary-bubble equilibria (`linlog_deflation_equilibrium`,
  `logInt_deflation_equilibrium`);
* **hyperinflations** (§8.3.5.4): fn 34 (`(54) ⇒ v(0+) = −∞`), its sharpened contrapositive
  (`v` bounded below ⇒ (52)), and a counterexample to the converse
  (`v = −log(1 + log(1 + 1/m))`); the precise Fig. 8.3: for every collapse date `T` a unique
  initial price level, converging to the steady state as `T → ∞` (`backOrbit_*`); and
  asymptotic hyperinflation with no collapse date when `C̄v' < 1` everywhere;
* **fractional backing** (§8.3.5.5): every positive path starting below the steady state falls
  to zero, hence below any floor `M̄/P^MIN`;
* **Exercise 2**: the first-order conditions of the transactions-technology models (a) and (c)
  derived from optimality, the dynamics and steady state (b), and (d): deflations are ruled
  out (`g` bounded) while hyperinflations are not (`g(0+)` finite gives (52)).
-/

namespace ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles

open Real Filter Topology Set
open ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility

/-! ## The difference equation for real balances (46) -/

/-- With `(1+r)β = 1` the user cost of money is `1 − β P_s/P_{s+1}` (O&R p. 538). -/
theorem userCost_of_beta {r β : ℝ} {P : ℕ → ℝ} (hβr : (1 + r) * β = 1) (s : ℕ) :
    userCost r P s = 1 - β * (P s / P (s + 1)) := by
  have hβ : β = (1 + r)⁻¹ := by
    have h1 : 1 + r ≠ 0 := by intro h; rw [h, zero_mul] at hβr; exact zero_ne_one hβr
    field_simp; linarith
  unfold userCost
  rw [hβ]
  ring

/-- **The dynamics of real balances (46)**, O&R p. 538: with money growing at the gross rate
`1 + μ` (`N_{s+1} = (1+μ)N_s`, `N_s` the money brought into date `s`) and real balances
`m_s = N_{s+1}/P_s`, the money-demand condition `h(m_s) = 1 − β P_s/P_{s+1}` holds iff
`(β/(1+μ)) m_{s+1} = m_s (1 − h(m_s))`. For MIU preferences `h = C̄ v'`; in Exercise 2
`h = Y g'`. -/
theorem bubble_dynamics_iff {β μ : ℝ} {N P : ℕ → ℝ} {h : ℝ → ℝ} (hμ : 0 < 1 + μ)
    (hN : ∀ s, 0 < N s) (hP : ∀ s, 0 < P s) (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s)
    (s : ℕ) :
    h (N (s + 1) / P s) = 1 - β * (P s / P (s + 1)) ↔
      β / (1 + μ) * (N (s + 1 + 1) / P (s + 1)) =
        N (s + 1) / P s * (1 - h (N (s + 1) / P s)) := by
  have hPs := (hP s).ne'
  have hPs1 := (hP (s + 1)).ne'
  have hm : 0 < N (s + 1) / P s := div_pos (hN _) (hP s)
  have key : β / (1 + μ) * (N (s + 1 + 1) / P (s + 1)) =
      N (s + 1) / P s * (β * (P s / P (s + 1))) := by
    rw [hgrowth (s + 1)]; field_simp
  rw [key]
  constructor
  · intro h1; rw [h1]; ring
  · intro h1
    have := mul_left_cancel₀ hm.ne' h1
    linarith

/-! ## Equilibrium: the Euler equation plus the transversality condition -/

/-- The individual transversality condition of fn 31, O&R p. 542, in its exact (liminf) form:
`liminf β^T m_T ≤ 0` (with constant consumption `C̄`). -/
def BubbleTVC (β : ℝ) (m : ℕ → ℝ) : Prop := ∀ ε > 0, ∃ᶠ T in atTop, β ^ T * m T < ε

/-- Along the candidate equilibrium plan (constant consumption `C̄ = Ȳ + rB_0`, bonds constant,
transfers (43) rebating seignorage), financial wealth is `(1+r)B_0 + N_s/P_s` (O&R §8.3.4–8.3.5). -/
theorem candidate_wealth {r Ybar B0 : ℝ} {N P : ℕ → ℝ} (hr : 0 < 1 + r) (hP : ∀ s, 0 < P s)
    (s : ℕ) :
    wealth r ((1 + r) * B0 + N 0 / P 0) (fun s => Ybar + (N (s + 1) - N s) / P s) (userCost r P)
      (fun _ => Ybar + r * B0) (fun s => N (s + 1) / P s) s = (1 + r) * B0 + N s / P s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [wealth_succ, ih]
    have hPs := (hP s).ne'
    have hPs1 := (hP (s + 1)).ne'
    unfold userCost
    field_simp
    ring

/-- **Equilibrium ⟺ (46) and the transversality condition** (O&R §8.3.5.1 and §8.3.5.3, made
exact). Consider the small open economy with `u = log C + v(M/P)` (45), `v` concave and
differentiable, `(1+r)β = 1`, `0 < β < 1`, constant output `Ȳ`, initial bonds `B_0`, zero
government spending and seignorage rebated as transfers (43), and money growing at `1 + μ`.
A positive price path `P` supports the equilibrium plan (constant consumption `C̄ = Ȳ + rB_0`,
real balances `m_s = N_{s+1}/P_s`) — i.e. that plan is OPTIMAL for the household at those
prices — iff real balances satisfy (46) at every date and the individual TVC (fn 31)
`liminf β^T m_T = 0` holds. (Summability of lifetime utility is assumed.) -/
theorem equilibrium_iff {v v' : ℝ → ℝ} {β r μ Ybar B0 : ℝ} {N P : ℕ → ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hβr : (1 + r) * β = 1) (hμ : 0 < 1 + μ) (hC : 0 < Ybar + r * B0)
    (hN : ∀ s, 0 < N s) (hP : ∀ s, 0 < P s) (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s)
    (hv : ConcaveOn ℝ (Set.Ioi 0) v) (hv' : ∀ k, 0 < k → HasDerivAt v (v' k) k)
    (hsum : Summable (fun s => β ^ s * (Real.log (Ybar + r * B0) + v (N (s + 1) / P s)))) :
    IsOptimal (fun c k => Real.log c + v k) β r ((1 + r) * B0 + N 0 / P 0)
        (fun s => Ybar + (N (s + 1) - N s) / P s) (userCost r P) (fun _ => Ybar + r * B0)
        (fun s => N (s + 1) / P s) ↔
      (∀ s, β / (1 + μ) * (N (s + 1 + 1) / P (s + 1)) =
        N (s + 1) / P s * (1 - (Ybar + r * B0) * v' (N (s + 1) / P s))) ∧
      BubbleTVC β (fun s => N (s + 1) / P s) := by
  set Cbar := Ybar + r * B0 with hCbar
  have hr : 0 < 1 + r := by
    by_contra h; push Not at h; nlinarith
  have hd : (1 + r)⁻¹ = β := by field_simp; linarith
  have hwealth : ∀ T, (1 + r)⁻¹ ^ T * wealth r ((1 + r) * B0 + N 0 / P 0)
      (fun s => Ybar + (N (s + 1) - N s) / P s) (userCost r P) (fun _ => Cbar)
      (fun s => N (s + 1) / P s) T =
        (1 + r) * B0 * β ^ T + β ^ T * (N (T + 1) / P T) / (1 + μ) := by
    intro T
    rw [candidate_wealth hr hP T, hd, hgrowth T]
    have := (hP T).ne'
    field_simp
  have hβT : Tendsto (fun T : ℕ => (1 + r) * B0 * β ^ T) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul ((1 + r) * B0)
    rwa [mul_zero] at this
  have hmpos : ∀ T, 0 < β ^ T * (N (T + 1) / P T) / (1 + μ) := fun T => by
    have := hN (T + 1); have := hP T; positivity
  rw [logSeparable_isOptimal_iff hβ0 hr hv hv']
  constructor
  · rintro ⟨_, _, hmo, htvc⟩
    refine ⟨fun s => ?_, fun ε hε => ?_⟩
    · have h1 := hmo s
      rw [userCost_of_beta hβr] at h1
      refine (bubble_dynamics_iff (h := fun k => Cbar * v' k) hμ hN hP hgrowth s).1 ?_
      rw [h1]
      field_simp
    · have h2 := htvc (ε / (1 + μ) / 2) (by positivity)
      have h3 := hβT.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (1 + μ) / 2 by positivity))
      have h4 := hβT.eventually (lt_mem_nhds (show -(ε / (1 + μ) / 2) < 0 by
        have : 0 < ε / (1 + μ) / 2 := by positivity
        linarith))
      refine (h2.and_eventually (h3.and h4)).mono fun T ⟨hT, _, hT4⟩ => ?_
      rw [hwealth T] at hT
      have : β ^ T * (N (T + 1) / P T) / (1 + μ) < ε / (1 + μ) := by linarith
      rwa [div_lt_div_iff_of_pos_right hμ] at this
  · rintro ⟨hdyn, htvc⟩
    refine ⟨⟨fun _ => hC, fun s => div_pos (hN _) (hP s), hsum, fun ε hε => ?_⟩,
      fun _ => by rw [hβr, one_mul], fun s => ?_, fun ε hε => ?_⟩
    · filter_upwards [hβT.eventually (lt_mem_nhds (show -ε < 0 by linarith))] with T hT
      rw [hwealth T]
      linarith [hmpos T]
    · have h1 := (bubble_dynamics_iff (h := fun k => Cbar * v' k) hμ hN hP hgrowth s).2 (hdyn s)
      rw [userCost_of_beta hβr, ← h1]
      field_simp
    · have h2 := htvc (ε * (1 + μ) / 2) (by positivity)
      have h3 := hβT.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
      refine (h2.and_eventually h3).mono fun T ⟨hT, hT3⟩ => ?_
      rw [hwealth T]
      have : β ^ T * (N (T + 1) / P T) / (1 + μ) < ε / 2 := by
        rw [div_lt_iff₀ hμ]; linarith
      linarith

/-! ## The logarithmic case (Figure 8.2), with money growth -/

/-- The steady-state level of real balances, O&R p. 539: `M/P‾ = C̄/(1 − β/(1+μ))`. -/
noncomputable def mbar (β μ Cbar : ℝ) : ℝ := Cbar / (1 - β / (1 + μ))

/-- **(46) for `v = log`**, O&R p. 539: `(β/(1+μ)) m_{t+1} = m_t(1 − C̄/m_t)` iff
`m_{t+1} = ((1+μ)/β)(m_t − C̄)`. -/
theorem log_dynamics_iff {β μ Cbar m0 m1 : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hm0 : 0 < m0) :
    β / (1 + μ) * m1 = m0 * (1 - Cbar * m0⁻¹) ↔ m1 = (1 + μ) / β * (m0 - Cbar) := by
  constructor <;> intro h
  · field_simp at h ⊢; linarith
  · rw [h]; field_simp

/-- **The saddle-path solution of the log case**, O&R Fig. 8.2: every solution of
`m_{t+1} = ((1+μ)/β)(m_t − C̄)` is `m_t = M/P‾ + ((1+μ)/β)^t (m_0 − M/P‾)`. -/
theorem log_orbit {β μ Cbar : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hβμ : β < 1 + μ)
    (hdyn : ∀ t, m (t + 1) = (1 + μ) / β * (m t - Cbar)) (t : ℕ) :
    m t = mbar β μ Cbar + ((1 + μ) / β) ^ t * (m 0 - mbar β μ Cbar) := by
  have h1 : 1 + μ - β ≠ 0 := by linarith
  have hm : mbar β μ Cbar = Cbar * (1 + μ) / (1 + μ - β) := by
    unfold mbar
    rw [show 1 - β / (1 + μ) = (1 + μ - β) / (1 + μ) by field_simp]
    field_simp
  have hfix : (1 + μ) / β * (mbar β μ Cbar - Cbar) = mbar β μ Cbar := by
    rw [hm]
    field_simp
    ring
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hdyn t, ih, pow_succ]
    linear_combination hfix

/-- **(a) Hyperinflationary paths are infeasible in the log case**, O&R p. 539 (made precise):
with `1 + μ > β`, a solution starting below the steady state reaches NEGATIVE real balances in
finite time, so every solution with positive real balances at all dates starts at or above
`M/P‾`. -/
theorem log_no_hyperinflation {β μ Cbar : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hβμ : β < 1 + μ) (hdyn : ∀ t, m (t + 1) = (1 + μ) / β * (m t - Cbar))
    (hpos : ∀ t, 0 < m t) : mbar β μ Cbar ≤ m 0 := by
  by_contra hlt
  push Not at hlt
  have hlam : 1 < (1 + μ) / β := (one_lt_div hβ).2 hβμ
  obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlam).eventually
    (eventually_gt_atTop (mbar β μ Cbar / (mbar β μ Cbar - m 0)))).exists
  have hd : 0 < mbar β μ Cbar - m 0 := by linarith
  have h1 := log_orbit hβ hμ hβμ hdyn t
  have h2 := hpos t
  rw [div_lt_iff₀ hd] at ht
  nlinarith

/-- **(b) The TVC along deflationary paths**, O&R pp. 542–543 with money growth:
`β^T m_T = β^T M/P‾ + (1+μ)^T (m_0 − M/P‾)`. -/
theorem log_discounted_balances {β μ Cbar : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hβμ : β < 1 + μ) (hdyn : ∀ t, m (t + 1) = (1 + μ) / β * (m t - Cbar)) (T : ℕ) :
    β ^ T * m T = β ^ T * mbar β μ Cbar + (1 + μ) ^ T * (m 0 - mbar β μ Cbar) := by
  rw [log_orbit hβ hμ hβμ hdyn T, div_pow]
  have := pow_pos hβ T
  field_simp

/-- **(c) Uniqueness for `μ ≥ 0`**, O&R pp. 539–543 (made precise): with nonnegative money
growth, the only positive solution of the log-case dynamics that satisfies the individual TVC
is the steady state `m_t = M/P‾` for all `t`. -/
theorem log_unique_of_nonneg_growth {β μ Cbar : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ0 : 0 ≤ μ)
    (hβμ : β < 1 + μ) (hC : 0 < Cbar) (hdyn : ∀ t, m (t + 1) = (1 + μ) / β * (m t - Cbar))
    (hpos : ∀ t, 0 < m t) (htvc : BubbleTVC β m) : ∀ t, m t = mbar β μ Cbar := by
  have hμ : 0 < 1 + μ := by linarith
  have hge := log_no_hyperinflation hβ hμ hβμ hdyn hpos
  have heq : m 0 = mbar β μ Cbar := by
    by_contra hne
    have hgt : 0 < m 0 - mbar β μ Cbar := by
      rcases lt_or_gt_of_ne hne with h | h
      · linarith
      · linarith
    obtain ⟨T, hT⟩ := (htvc (m 0 - mbar β μ Cbar) hgt).exists
    rw [log_discounted_balances hβ hμ hβμ hdyn T] at hT
    have h1 : 0 ≤ β ^ T * mbar β μ Cbar := by
      have : β / (1 + μ) < 1 := (div_lt_one hμ).2 hβμ
      exact mul_nonneg (pow_pos hβ T).le (div_pos hC (by linarith)).le
    have h2 : 1 ≤ (1 + μ) ^ T := one_le_pow₀ (by linarith)
    nlinarith
  intro t
  rw [log_orbit hβ hμ hβμ hdyn t, heq, sub_self, mul_zero, add_zero]

/-- **(d) Deflationary bubbles when `β < 1 + μ < 1`** (a correction to O&R pp. 541–543, whose
argument assumes constant money): with money shrinking at a rate below the rate of time
preference, EVERY initial real balance `m_0 ≥ M/P‾` generates a positive path satisfying the
individual TVC, `β^T m_T → 0`. -/
theorem log_deflation_tvc {β μ Cbar : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hβμ : β < 1 + μ)
    (hμ1 : 1 + μ < 1) (hC : 0 < Cbar) (hdyn : ∀ t, m (t + 1) = (1 + μ) / β * (m t - Cbar))
    (hm0 : mbar β μ Cbar ≤ m 0) :
    (∀ t, 0 < m t) ∧ Tendsto (fun T => β ^ T * m T) atTop (𝓝 0) := by
  have hμ : 0 < 1 + μ := by linarith
  have hmbar : 0 < mbar β μ Cbar := by
    unfold mbar
    have : β / (1 + μ) < 1 := (div_lt_one hμ).2 hβμ
    exact div_pos hC (by linarith)
  have hlam : 1 ≤ (1 + μ) / β := by rw [le_div_iff₀ hβ]; linarith
  refine ⟨fun t => ?_, ?_⟩
  · rw [log_orbit hβ hμ hβμ hdyn t]
    have := one_le_pow₀ hlam (n := t)
    nlinarith
  · have h1 : Tendsto (fun T : ℕ => β ^ T * mbar β μ Cbar + (1 + μ) ^ T * (m 0 - mbar β μ Cbar))
        atTop (𝓝 (0 * mbar β μ Cbar + 0 * (m 0 - mbar β μ Cbar))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le (by linarith)).mul_const _).add
        ((tendsto_pow_atTop_nhds_zero_of_lt_one hμ.le hμ1).mul_const _)
    simp only [zero_mul, add_zero] at h1
    exact h1.congr fun T => (log_discounted_balances hβ hμ hβμ hdyn T).symm

/-- The log-case dynamics are (46) for `v = log` (O&R p. 539), as a statement about a price path
through `m_s = N_{s+1}/P_s`. -/
theorem log_dynamics_path {β μ Cbar : ℝ} {N P : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hN : ∀ s, 0 < N s) (hP : ∀ s, 0 < P s) :
    (∀ s, β / (1 + μ) * (N (s + 1 + 1) / P (s + 1)) =
        N (s + 1) / P s * (1 - Cbar * (N (s + 1) / P s)⁻¹)) ↔
      ∀ s, N (s + 1 + 1) / P (s + 1) = (1 + μ) / β * (N (s + 1) / P s - Cbar) :=
  forall_congr' fun s => log_dynamics_iff hβ hμ (div_pos (hN _) (hP s))

/-- **Existence: the steady state is an equilibrium** (O&R p. 539 and p. 538, log case): with
`1 + μ > β` the constant real-balance path `M/P_s = M/P‾` (price level `P_s = N_{s+1}/M/P‾`,
growing at `1 + μ`) is an equilibrium. -/
theorem log_steady_state_equilibrium {β r μ Ybar B0 : ℝ} {N : ℕ → ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hβr : (1 + r) * β = 1) (hβμ : β < 1 + μ) (hC : 0 < Ybar + r * B0)
    (hN : ∀ s, 0 < N s) (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s) :
    IsOptimal (fun c k => Real.log c + Real.log k) β r
      ((1 + r) * B0 + N 0 / (N 1 / mbar β μ (Ybar + r * B0)))
      (fun s => Ybar + (N (s + 1) - N s) / (N (s + 1) / mbar β μ (Ybar + r * B0)))
      (userCost r (fun s => N (s + 1) / mbar β μ (Ybar + r * B0))) (fun _ => Ybar + r * B0)
      (fun s => N (s + 1) / (N (s + 1) / mbar β μ (Ybar + r * B0))) := by
  have hμ : 0 < 1 + μ := by linarith
  set mb := mbar β μ (Ybar + r * B0) with hmb
  have hmb0 : 0 < mb := by
    have : β / (1 + μ) < 1 := (div_lt_one hμ).2 hβμ
    exact div_pos hC (by linarith)
  have hP : ∀ s, 0 < N (s + 1) / mb := fun s => div_pos (hN _) hmb0
  have hm : ∀ s, N (s + 1) / (N (s + 1) / mb) = mb := fun s => by
    have := (hN (s + 1)).ne'; field_simp
  have hsum : Summable (fun s => β ^ s * (Real.log (Ybar + r * B0) +
      Real.log (N (s + 1) / (N (s + 1) / mb)))) := by
    simp only [hm]
    exact (summable_geometric_of_lt_one hβ0.le hβ1).mul_right _
  refine (equilibrium_iff (v' := fun k => k⁻¹) hβ0 hβ1 hβr hμ hC hN hP hgrowth
    strictConcaveOn_log_Ioi.concaveOn (fun k hk => Real.hasDerivAt_log hk.ne') hsum).2 ⟨?_, ?_⟩
  · intro s
    simp only [hm]
    rw [(log_dynamics_iff hβ0 hμ hmb0)]
    have h1 : 1 + μ - β ≠ 0 := by linarith
    have hm' : mb = (Ybar + r * B0) * (1 + μ) / (1 + μ - β) := by
      rw [hmb]; unfold mbar
      rw [show 1 - β / (1 + μ) = (1 + μ - β) / (1 + μ) by field_simp]
      field_simp
    rw [hm']
    field_simp
    ring
  · intro ε hε
    simp only [hm]
    exact ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const mb |>.eventually
      (gt_mem_nhds (by rw [zero_mul]; exact hε))).frequently

/-- **Uniqueness for `μ ≥ 0`**, O&R §8.3.5 (made precise, log case): if money grows at a
nonnegative rate, the ONLY equilibrium price path is the steady state `M/P_s = M/P‾`:
hyperinflationary paths reach negative real balances and deflationary paths violate the
individual transversality condition. -/
theorem log_equilibrium_unique {β r μ Ybar B0 : ℝ} {N P : ℕ → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβr : (1 + r) * β = 1) (hμ0 : 0 ≤ μ) (hC : 0 < Ybar + r * B0) (hN : ∀ s, 0 < N s)
    (hP : ∀ s, 0 < P s) (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s)
    (hopt : IsOptimal (fun c k => Real.log c + Real.log k) β r ((1 + r) * B0 + N 0 / P 0)
        (fun s => Ybar + (N (s + 1) - N s) / P s) (userCost r P) (fun _ => Ybar + r * B0)
        (fun s => N (s + 1) / P s)) :
    ∀ s, N (s + 1) / P s = mbar β μ (Ybar + r * B0) := by
  have hμ : 0 < 1 + μ := by linarith
  have hβμ : β < 1 + μ := by linarith
  have hsum := hopt.1.2.2.1
  obtain ⟨hdyn, htvc⟩ := (equilibrium_iff (v' := fun k => k⁻¹) hβ0 hβ1 hβr hμ hC hN hP hgrowth
    strictConcaveOn_log_Ioi.concaveOn (fun k hk => Real.hasDerivAt_log hk.ne') hsum).1 hopt
  exact log_unique_of_nonneg_growth (m := fun s => N (s + 1) / P s) hβ0 hμ0 hβμ hC
    ((log_dynamics_path hβ0 hμ hN hP).1 hdyn) (fun s => div_pos (hN _) (hP s)) htvc

/-- **A continuum of deflationary equilibria when `β < 1 + μ < 1`** (a correction to O&R
§8.3.5.3, whose TVC argument needs `μ ≥ 0`): for every `m_0 ≥ M/P‾` the price path
`P_s = N_{s+1}/m_s`, `m_s = M/P‾ + ((1+μ)/β)^s (m_0 − M/P‾)`, is an equilibrium. -/
theorem log_equilibria_multiple {β r μ Ybar B0 m0 : ℝ} {N : ℕ → ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hβr : (1 + r) * β = 1) (hβμ : β < 1 + μ) (hμ1 : 1 + μ < 1)
    (hC : 0 < Ybar + r * B0) (hN : ∀ s, 0 < N s) (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s)
    (hm0 : mbar β μ (Ybar + r * B0) ≤ m0) :
    let m : ℕ → ℝ := fun s => mbar β μ (Ybar + r * B0) +
      ((1 + μ) / β) ^ s * (m0 - mbar β μ (Ybar + r * B0))
    IsOptimal (fun c k => Real.log c + Real.log k) β r ((1 + r) * B0 + N 0 / (N 1 / m 0))
      (fun s => Ybar + (N (s + 1) - N s) / (N (s + 1) / m s))
      (userCost r (fun s => N (s + 1) / m s)) (fun _ => Ybar + r * B0)
      (fun s => N (s + 1) / (N (s + 1) / m s)) := by
  intro m
  have hμ : 0 < 1 + μ := by linarith
  set Cbar := Ybar + r * B0 with hCbar
  set mb := mbar β μ Cbar with hmb
  have hlam : 1 ≤ (1 + μ) / β := by rw [le_div_iff₀ hβ0]; linarith
  have hmb0 : 0 < mb := by
    have : β / (1 + μ) < 1 := (div_lt_one hμ).2 hβμ
    exact div_pos hC (by linarith)
  have hdynm : ∀ t, m (t + 1) = (1 + μ) / β * (m t - Cbar) := by
    have h1 : 1 + μ - β ≠ 0 := by linarith
    have hm' : mb = Cbar * (1 + μ) / (1 + μ - β) := by
      rw [hmb]; unfold mbar
      rw [show 1 - β / (1 + μ) = (1 + μ - β) / (1 + μ) by field_simp]
      field_simp
    intro t
    simp only [m, pow_succ]
    rw [← hmb, hm']
    field_simp
    ring
  obtain ⟨hpos, hlim⟩ := log_deflation_tvc (m := m) hβ0 hβμ hμ1 hC hdynm (by simp [m]; linarith)
  have hmlow : ∀ t, mb ≤ m t := fun t => by
    have := one_le_pow₀ hlam (n := t)
    simp only [m]
    nlinarith
  have hmup : ∀ t, m t ≤ m0 * ((1 + μ) / β) ^ t := fun t => by
    have := one_le_pow₀ hlam (n := t)
    simp only [m]
    nlinarith
  have hP : ∀ s, 0 < N (s + 1) / m s := fun s => div_pos (hN _) (hpos s)
  have hmm : ∀ s, N (s + 1) / (N (s + 1) / m s) = m s := fun s => by
    have := (hN (s + 1)).ne'; have := (hpos s).ne'; field_simp
  have hsum : Summable (fun s => β ^ s * (Real.log Cbar + Real.log (N (s + 1) / (N (s + 1) /
      m s)))) := by
    simp only [hmm]
    have hβn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
    set K := |Real.log Cbar| + |Real.log mb| + |Real.log m0| with hK
    refine Summable.of_norm_bounded (g := fun s => K * β ^ s + Real.log ((1 + μ) / β) *
      ((s : ℝ) ^ 1 * β ^ s)) (((summable_geometric_of_lt_one hβ0.le hβ1).mul_left K).add
      ((summable_pow_mul_geometric_of_norm_lt_one 1 hβn).mul_left _)) fun s => ?_
    have hms := hpos s
    have hl1 : Real.log mb ≤ Real.log (m s) := Real.log_le_log hmb0 (hmlow s)
    have hl2 : Real.log (m s) ≤ Real.log m0 + s * Real.log ((1 + μ) / β) := by
      have hm0' : 0 < m0 := by linarith
      calc Real.log (m s) ≤ Real.log (m0 * ((1 + μ) / β) ^ s) :=
            Real.log_le_log hms (hmup s)
        _ = _ := by rw [Real.log_mul hm0'.ne' (by positivity), Real.log_pow]
    have hll : 0 ≤ Real.log ((1 + μ) / β) := Real.log_nonneg hlam
    have hβs := pow_pos hβ0 s
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hβs, pow_one]
    have habs : |Real.log Cbar + Real.log (m s)| ≤ K + s * Real.log ((1 + μ) / β) := by
      have e1 := abs_le.1 (le_refl |Real.log Cbar|)
      rw [abs_le]
      constructor
      · have := neg_abs_le (Real.log Cbar)
        have := neg_abs_le (Real.log mb)
        have := abs_nonneg (Real.log m0)
        have : 0 ≤ (s : ℝ) * Real.log ((1 + μ) / β) := mul_nonneg (Nat.cast_nonneg s) hll
        linarith
      · have := le_abs_self (Real.log Cbar)
        have := le_abs_self (Real.log m0)
        have := abs_nonneg (Real.log mb)
        linarith
    nlinarith
  refine (equilibrium_iff (v' := fun k => k⁻¹) hβ0 hβ1 hβr hμ hC hN hP hgrowth
    strictConcaveOn_log_Ioi.concaveOn (fun k hk => Real.hasDerivAt_log hk.ne') hsum).2 ⟨?_, ?_⟩
  · intro s
    simp only [hmm]
    rw [log_dynamics_iff hβ0 hμ (hpos s)]
    exact hdynm s
  · intro ε hε
    simp only [hmm]
    exact (hlim.eventually (gt_mem_nhds hε)).frequently

/-! ## Steady states and the iterated money Euler equation (48)–(50) -/

/-- **Steady states of (46)**, O&R p. 539: a constant level `m̄ > 0` solves (46) iff
`C̄v'(m̄) = 1 − β/(1+μ)`. -/
theorem steady_state_iff {β μ Cbar mb : ℝ} {v' : ℝ → ℝ} (hmb : 0 < mb) :
    β / (1 + μ) * mb = mb * (1 - Cbar * v' mb) ↔ Cbar * v' mb = 1 - β / (1 + μ) := by
  constructor
  · intro h
    have := mul_left_cancel₀ hmb.ne' (show mb * (β / (1 + μ)) = mb * (1 - Cbar * v' mb) by
      linarith)
    linarith
  · intro h; rw [h]; ring

/-- O&R p. 539: for strictly concave `v` (`C̄v'` strictly decreasing) there is at most one steady
state; for `v = log` it is `M/P‾ = C̄/(1 − β/(1+μ))`, which is positive iff `1 + μ > β`. -/
theorem steady_state_unique {β μ Cbar m1 m2 : ℝ} {v' : ℝ → ℝ}
    (hanti : StrictAntiOn (fun k => Cbar * v' k) (Set.Ioi 0)) (h1 : 0 < m1) (h2 : 0 < m2)
    (hs1 : Cbar * v' m1 = 1 - β / (1 + μ)) (hs2 : Cbar * v' m2 = 1 - β / (1 + μ)) : m1 = m2 :=
  hanti.injOn h1 h2 (hs1.trans hs2.symm)

/-- The log steady state is positive iff `1 + μ > β` (O&R p. 539 and fn 27). -/
theorem mbar_pos_iff {β μ Cbar : ℝ} (hμ : 0 < 1 + μ) (hC : 0 < Cbar) :
    0 < mbar β μ Cbar ↔ β < 1 + μ := by
  unfold mbar
  rw [div_pos_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · rwa [sub_pos, div_lt_one hμ] at h
    · linarith
  · intro h
    exact Or.inl ⟨hC, by rwa [sub_pos, div_lt_one hμ]⟩

/-- **The iterated money Euler equation (48)**, O&R p. 541: with constant `M̄` and `C̄`, (47)
`1/(P_t C̄) = v'(M̄/P_t)/P_t + β/(P_{t+1} C̄)` implies, for every horizon `T`,
`1/(P_0 C̄) = Σ_{s<T} β^s v'(M̄/P_s)/P_s + β^T/(P_T C̄)`. -/
theorem iterated_money_euler {β Cbar M : ℝ} {v' : ℝ → ℝ} {P : ℕ → ℝ}
    (h47 : ∀ s, 1 / (P s * Cbar) = v' (M / P s) / P s + β / (P (s + 1) * Cbar)) (T : ℕ) :
    1 / (P 0 * Cbar) = ∑ s ∈ Finset.range T, β ^ s * (v' (M / P s) / P s) +
      β ^ T / (P T * Cbar) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have e : β ^ T / (P T * Cbar) = β ^ T * (1 / (P T * Cbar)) := by ring
    rw [Finset.sum_range_succ, ih, e, h47 T, pow_succ]
    ring

/-- **(49) holds iff the transversality condition (50) holds**, O&R p. 542: when marginal utility
of money is nonnegative, the infinite-horizon money Euler equation
`1/(P_0 C̄) = Σ_s β^s v'(M̄/P_s)/P_s` holds exactly when `β^T/(P_T C̄) → 0`. -/
theorem money_euler_limit_iff {β Cbar M : ℝ} {v' : ℝ → ℝ} {P : ℕ → ℝ} (hβ : 0 ≤ β)
    (hP : ∀ s, 0 < P s) (hnn : ∀ s, 0 ≤ v' (M / P s))
    (h47 : ∀ s, 1 / (P s * Cbar) = v' (M / P s) / P s + β / (P (s + 1) * Cbar)) :
    HasSum (fun s => β ^ s * (v' (M / P s) / P s)) (1 / (P 0 * Cbar)) ↔
      Tendsto (fun T => β ^ T / (P T * Cbar)) atTop (𝓝 0) := by
  have hnn' : ∀ s, 0 ≤ β ^ s * (v' (M / P s) / P s) := fun s =>
    mul_nonneg (pow_nonneg hβ s) (div_nonneg (hnn s) (hP s).le)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn']
  have hid := iterated_money_euler h47
  constructor
  · intro h
    have := (tendsto_const_nhds (x := 1 / (P 0 * Cbar))).sub h
    rw [sub_self] at this
    exact this.congr fun T => by have := hid T; linarith
  · intro h
    have := (tendsto_const_nhds (x := 1 / (P 0 * Cbar))).sub h
    rw [sub_zero] at this
    exact this.congr fun T => by have := hid T; linarith

/-! ## General `v`, constant money: the transversality condition and deflations (§8.3.5.3) -/

/-- **Deflationary paths grow at least geometrically**, O&R p. 542: along a positive solution of
(46) with constant money, `β m_{t+1} = m_t(1 − h(m_t))` (`h = C̄v'`, antitone because `v` is
concave), starting where `h(m_0) < 1 − β` (above the steady state), real balances never fall
below `m_0` and grow by at least the factor `λ₀ = (1 − h(m_0))/β > 1` every period. -/
theorem deflation_growth {β : ℝ} {h : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hpos : ∀ t, 0 < m t)
    (hdyn : ∀ t, β * m (t + 1) = m t * (1 - h (m t))) (hanti : AntitoneOn h (Set.Ioi 0))
    (hm0 : h (m 0) < 1 - β) (t : ℕ) :
    m 0 ≤ m t ∧ (1 - h (m 0)) / β * m t ≤ m (t + 1) := by
  have hlam : 1 < (1 - h (m 0)) / β := by rw [one_lt_div hβ]; linarith
  have key : ∀ t, m 0 ≤ m t → (1 - h (m 0)) / β * m t ≤ m (t + 1) := by
    intro t ht
    have h1 : h (m t) ≤ h (m 0) := hanti (hpos 0) (hpos t) ht
    have h2 := hdyn t
    rw [div_mul_eq_mul_div, div_le_iff₀ hβ]
    nlinarith [hpos t]
  have hge : ∀ t, m 0 ≤ m t := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ t ih =>
      have := key t ih
      nlinarith [hpos t]
  exact ⟨hge t, key t (hge t)⟩

/-- **The discounted real balances as a product**, O&R (48)–(50) with constant `C̄` and `M̄`:
`β^T m_T = m_0 Π_{s<T}(1 − h(m_s))`. -/
theorem discounted_product {β : ℝ} {h : ℝ → ℝ} {m : ℕ → ℝ}
    (hdyn : ∀ t, β * m (t + 1) = m t * (1 - h (m t))) (T : ℕ) :
    β ^ T * m T = m 0 * ∏ s ∈ Finset.range T, (1 - h (m s)) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.prod_range_succ, pow_succ, mul_assoc, hdyn T, ← mul_assoc, ih]
    ring

/-- Upper exponential bound for a product of factors `1 − a_s` with `0 ≤ a_s ≤ 1`:
`Π_{s<T}(1 − a_s) ≤ exp(−Σ_{s<T} a_s)` (used for O&R (50)). -/
theorem prod_le_exp_neg_sum {a : ℕ → ℝ} (ha1 : ∀ s, a s ≤ 1) (T : ℕ) :
    ∏ s ∈ Finset.range T, (1 - a s) ≤ Real.exp (-∑ s ∈ Finset.range T, a s) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, neg_add, Real.exp_add]
    have h1 : 1 - a T ≤ Real.exp (-a T) := by linarith [Real.add_one_le_exp (-a T)]
    have h2 : 0 ≤ 1 - a T := by linarith [ha1 T]
    have h3 : 0 ≤ ∏ s ∈ Finset.range T, (1 - a s) :=
      Finset.prod_nonneg fun s _ => by linarith [ha1 s]
    exact mul_le_mul ih h1 h2 (Real.exp_pos _).le

/-- Lower exponential bound: if `0 ≤ a_s ≤ 1 − β` with `0 < β`, then
`exp(−(1/β) Σ_{s<T} a_s) ≤ Π_{s<T}(1 − a_s)` (used for O&R (50)). -/
theorem exp_neg_sum_le_prod {β : ℝ} (hβ : 0 < β) {a : ℕ → ℝ} (ha0 : ∀ s, 0 ≤ a s)
    (ha1 : ∀ s, a s ≤ 1 - β) (T : ℕ) :
    Real.exp (-(1 / β) * ∑ s ∈ Finset.range T, a s) ≤ ∏ s ∈ Finset.range T, (1 - a s) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, mul_add, Real.exp_add]
    have hpos : 0 < 1 - a T := by linarith [ha1 T]
    have h1 : Real.exp (-(1 / β) * a T) ≤ 1 - a T := by
      have e1 : 1 + a T / (1 - a T) ≤ Real.exp (a T / (1 - a T)) := by
        linarith [Real.add_one_le_exp (a T / (1 - a T))]
      have e2 : a T / (1 - a T) ≤ a T / β :=
        div_le_div_of_nonneg_left (ha0 T) hβ (by linarith [ha1 T])
      have e3 : Real.exp (a T / (1 - a T)) ≤ Real.exp (a T / β) := Real.exp_le_exp.2 e2
      have e4 : 1 + a T / (1 - a T) = 1 / (1 - a T) := by field_simp; ring
      have e5 : 1 / (1 - a T) ≤ Real.exp (a T / β) := by linarith
      rw [div_le_iff₀ hpos] at e5
      have e6 : Real.exp (-(1 / β) * a T) * Real.exp (a T / β) = 1 := by
        rw [← Real.exp_add]; simp; ring_nf
      nlinarith [Real.exp_pos (-(1 / β) * a T)]
    exact mul_le_mul ih h1 (Real.exp_pos _).le
      (Finset.prod_nonneg fun s _ => by linarith [ha1 s])

/-- **The exact transversality criterion for deflations** (O&R (50) and fn 32, made precise):
along a positive deflationary solution of (46) with constant money (`h = C̄v' ≥ 0`, antitone,
`h(m_0) < 1 − β`), the individual TVC `liminf β^T m_T = 0` holds IF AND ONLY IF
`Σ_t h(m_t) = ∞`, i.e. iff `Σ_t v'(m_t)` diverges. When it holds, `β^T m_T → 0`. -/
theorem tvc_iff_not_summable {β : ℝ} {h : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β)
    (hpos : ∀ t, 0 < m t) (hdyn : ∀ t, β * m (t + 1) = m t * (1 - h (m t)))
    (hanti : AntitoneOn h (Set.Ioi 0)) (hnn : ∀ x, 0 < x → 0 ≤ h x) (hm0 : h (m 0) < 1 - β) :
    BubbleTVC β m ↔ ¬ Summable (fun t => h (m t)) := by
  have ha1 : ∀ t, h (m t) ≤ 1 - β := fun t =>
    (hanti (hpos 0) (hpos t) (deflation_growth hβ hpos hdyn hanti hm0 t).1).trans hm0.le
  have ha0 : ∀ t, 0 ≤ h (m t) := fun t => hnn _ (hpos t)
  constructor
  · intro htvc hsum
    set S := ∑' t, h (m t) with hS
    have hlow : ∀ T, m 0 * Real.exp (-(1 / β) * S) ≤ β ^ T * m T := by
      intro T
      rw [discounted_product hdyn T]
      have h1 := exp_neg_sum_le_prod hβ ha0 ha1 T
      have h2 : ∑ s ∈ Finset.range T, h (m s) ≤ S := hsum.sum_le_tsum _ fun s _ => ha0 s
      have h3 : Real.exp (-(1 / β) * S) ≤ Real.exp (-(1 / β) * ∑ s ∈ Finset.range T, h (m s)) :=
        Real.exp_le_exp.2 (by
          have : 0 < 1 / β := by positivity
          nlinarith)
      exact mul_le_mul_of_nonneg_left (h3.trans h1) (hpos 0).le
    have hε : 0 < m 0 * Real.exp (-(1 / β) * S) := mul_pos (hpos 0) (Real.exp_pos _)
    obtain ⟨T, hT⟩ := (htvc _ hε).exists
    linarith [hlow T]
  · intro hns ε hε
    have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg ha0).1 hns
    have hexp : Tendsto (fun T => m 0 * Real.exp (-∑ s ∈ Finset.range T, h (m s))) atTop
        (𝓝 (m 0 * 0)) :=
      (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hdiv)).const_mul _
    rw [mul_zero] at hexp
    refine (hexp.eventually (gt_mem_nhds hε)).mono (fun T hT => ?_) |>.frequently
    rw [discounted_product hdyn T]
    have := prod_le_exp_neg_sum (fun t => (ha1 t).trans (by linarith)) T
    calc m 0 * ∏ s ∈ Finset.range T, (1 - h (m s))
        ≤ m 0 * Real.exp (-∑ s ∈ Finset.range T, h (m s)) :=
          mul_le_mul_of_nonneg_left this (hpos 0).le
      _ < ε := hT

/-- The tangent-line inequality for a concave function of one variable (copied from the
`SmallOpenEconomyDynamics` project's `ConsumptionOptimality` so that this project builds on its
own; used for fn 32, O&R p. 542). -/
theorem concave_le_tangent' {f : ℝ → ℝ} {S : Set ℝ} (hf : ConcaveOn ℝ S f) {x y d : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f d x) : f y ≤ f x + d * (y - x) := by
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · have h := hf.le_slope_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    linarith
  · simp
  · have h := hf.slope_le_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    linarith

/-- **Footnote 32, made precise**, O&R p. 542: if `v` is concave, increasing and BOUNDED ABOVE,
then along a positive deflationary path with constant money `Σ_t v'(m_t) < ∞`: the telescoping
bound `v'(m_{t+1})(m_{t+1} − m_t) ≤ v(m_{t+1}) − v(m_t)` with `m_{t+1} − m_t ≥ (λ₀ − 1)m_0`. -/
theorem summable_deriv_of_bounded {β Cbar V : ℝ} {v v' : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β)
    (hpos : ∀ t, 0 < m t)
    (hdyn : ∀ t, β * m (t + 1) = m t * (1 - Cbar * v' (m t)))
    (hv : ConcaveOn ℝ (Set.Ioi 0) v) (hv' : ∀ k, 0 < k → HasDerivAt v (v' k) k)
    (hanti : AntitoneOn (fun k => Cbar * v' k) (Set.Ioi 0)) (hnn : ∀ k, 0 < k → 0 ≤ v' k)
    (hV : ∀ k, 0 < k → v k ≤ V) (hm0 : Cbar * v' (m 0) < 1 - β) :
    Summable (fun t => v' (m t)) := by
  set lam := (1 - Cbar * v' (m 0)) / β with hlam
  have hlam1 : 1 < lam := by rw [hlam, one_lt_div hβ]; linarith
  set δ := (lam - 1) * m 0 with hδ
  have hδ0 : 0 < δ := mul_pos (by linarith) (hpos 0)
  have hgr := deflation_growth (h := fun k => Cbar * v' k) hβ hpos hdyn hanti hm0
  have hstep : ∀ t, δ ≤ m (t + 1) - m t := fun t => by
    have h1 := (hgr t).2
    have h2 := (hgr t).1
    rw [← hlam] at h1
    nlinarith
  have hterm : ∀ t, v' (m (t + 1)) ≤ (v (m (t + 1)) - v (m t)) / δ := fun t => by
    rw [le_div_iff₀ hδ0]
    have h1 := concave_le_tangent' hv (hpos (t + 1)) (hpos t) (hv' _ (hpos (t + 1)))
    have h2 := hstep t
    have h3 := hnn _ (hpos (t + 1))
    nlinarith
  have hbound : ∀ n, ∑ t ∈ Finset.range n, v' (m (t + 1)) ≤ (V - v (m 0)) / δ := by
    intro n
    calc ∑ t ∈ Finset.range n, v' (m (t + 1))
        ≤ ∑ t ∈ Finset.range n, (v (m (t + 1)) - v (m t)) / δ := Finset.sum_le_sum fun t _ =>
          hterm t
      _ = (v (m n) - v (m 0)) / δ := by
          rw [← Finset.sum_div, Finset.sum_range_sub (fun t => v (m t))]
      _ ≤ (V - v (m 0)) / δ := by
          have := hV _ (hpos n)
          exact div_le_div_of_nonneg_right (by linarith) hδ0.le
  have hs : Summable (fun t => v' (m (t + 1))) :=
    summable_of_sum_range_le (fun t => hnn _ (hpos _)) hbound
  exact (summable_nat_add_iff 1).1 hs

/-- **Deflationary bubbles are ruled out when `v` is bounded above** (O&R p. 542 and fn 32,
constant money): the individual TVC fails along every positive deflationary solution of (46). -/
theorem bounded_rules_out_deflation {β Cbar V : ℝ} {v v' : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β)
    (hC : 0 < Cbar) (hpos : ∀ t, 0 < m t)
    (hdyn : ∀ t, β * m (t + 1) = m t * (1 - Cbar * v' (m t)))
    (hv : ConcaveOn ℝ (Set.Ioi 0) v) (hv' : ∀ k, 0 < k → HasDerivAt v (v' k) k)
    (hanti : AntitoneOn (fun k => Cbar * v' k) (Set.Ioi 0)) (hnn : ∀ k, 0 < k → 0 ≤ v' k)
    (hV : ∀ k, 0 < k → v k ≤ V) (hm0 : Cbar * v' (m 0) < 1 - β) : ¬ BubbleTVC β m := by
  rw [tvc_iff_not_summable (h := fun k => Cbar * v' k) hβ hpos hdyn hanti
    (fun k hk => mul_nonneg hC.le (hnn k hk)) hm0, not_not]
  exact (summable_deriv_of_bounded hβ hpos hdyn hv hv' hanti hnn hV hm0).mul_left Cbar

/-- **The log case satisfies `Σ 1/m_t < ∞`** (O&R fn 32: "true even for some standard cases in
which `v` isn't bounded above, for example the logarithmic case"): with constant money and
`v = log`, the TVC fails along every positive deflationary path. -/
theorem log_rules_out_deflation {β Cbar : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hC : 0 < Cbar)
    (hpos : ∀ t, 0 < m t) (hdyn : ∀ t, β * m (t + 1) = m t * (1 - Cbar * (m t)⁻¹))
    (hm0 : Cbar * (m 0)⁻¹ < 1 - β) : ¬ BubbleTVC β m := by
  have hanti : AntitoneOn (fun k : ℝ => Cbar * k⁻¹) (Set.Ioi 0) := fun x hx y hy hxy =>
    mul_le_mul_of_nonneg_left (inv_anti₀ hx hxy) hC.le
  rw [tvc_iff_not_summable (h := fun k => Cbar * k⁻¹) hβ hpos hdyn hanti
    (fun k hk => mul_nonneg hC.le (inv_pos.2 hk).le) hm0, not_not]
  set lam := (1 - Cbar * (m 0)⁻¹) / β with hlam
  have hlam1 : 1 < lam := by rw [hlam, one_lt_div hβ]; linarith
  have hgr := deflation_growth (h := fun k => Cbar * k⁻¹) hβ hpos hdyn hanti hm0
  have hgeo : ∀ t, m 0 * lam ^ t ≤ m t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have := (hgr t).2
      rw [← hlam] at this
      rw [pow_succ]
      nlinarith [hlam1]
  have hq : lam⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlam1
  refine Summable.of_nonneg_of_le (fun t => mul_nonneg hC.le (inv_pos.2 (hpos t)).le)
    (fun t => ?_) (((summable_geometric_of_lt_one (by positivity) hq).mul_left
      (Cbar * (m 0)⁻¹)))
  have h1 : (m t)⁻¹ ≤ (m 0 * lam ^ t)⁻¹ := inv_anti₀ (by have := hpos 0; positivity) (hgeo t)
  rw [mul_inv] at h1
  calc Cbar * (m t)⁻¹ ≤ Cbar * ((m 0)⁻¹ * (lam ^ t)⁻¹) := mul_le_mul_of_nonneg_left h1 hC.le
    _ = _ := by rw [inv_pow]; ring

/-! ### A deflationary-bubble equilibrium with unbounded concave `v` -/

/-- **Counterexample to "the TVC rules out deflations" for unbounded `v`** (O&R p. 542, fn 32):
`v(m) = a m + log m` (`a > 0`) is strictly increasing, concave and unbounded above; its
derivative `a + 1/m ≥ a` is not summable along any path, so by `tvc_iff_not_summable` the TVC
holds along every deflationary path. Concavity. -/
theorem linlog_concaveOn {a : ℝ} (ha : 0 ≤ a) :
    ConcaveOn ℝ (Set.Ioi 0) (fun k => a * k + Real.log k) :=
  ((concaveOn_id (convex_Ioi 0)).smul ha).add strictConcaveOn_log_Ioi.concaveOn

/-- `v(m) = a m + log m` is unbounded above (O&R fn 32 counterexample). -/
theorem linlog_unbounded {a : ℝ} (ha : 0 < a) (K : ℝ) : ∃ k, 0 < k ∧ K < a * k + Real.log k := by
  refine ⟨max 1 (K / a + 1), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  have h1 : 1 ≤ max 1 (K / a + 1) := le_max_left _ _
  have h2 : K / a + 1 ≤ max 1 (K / a + 1) := le_max_right _ _
  have h3 : 0 ≤ Real.log (max 1 (K / a + 1)) := Real.log_nonneg h1
  have h4 : K < a * (K / a + 1) := by field_simp; linarith
  nlinarith

/-- The saddle-path solution `m_s = m̄ + κ^s (m_0 − m̄)` of an affine difference equation
`m_{s+1} − m̄ = κ(m_s − m̄)` (O&R Fig. 8.2). -/
noncomputable def affinePath (mb κ m0 : ℝ) (s : ℕ) : ℝ := mb + κ ^ s * (m0 - mb)

/-- **A deflationary bubble IS an equilibrium when `v = a m + log m`** (constant money,
`μ = 0`): with `C̄ = Ȳ + rB_0`, `1 − C̄a > β` and steady state `m̄ = C̄/(1 − C̄a − β)`, EVERY
`m_0 ≥ m̄` generates an equilibrium price path `P_s = M̄/m_s`,
`m_s = m̄ + ((1 − C̄a)/β)^s (m_0 − m̄)`; for `m_0 > m̄` the price level falls to zero. So the
book's conclusion (p. 543) needs `v` bounded above (or `Σ v'(m_t) < ∞`); it fails for this
unbounded concave `v`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem linlog_deflation_equilibrium {a β r Ybar B0 Cbar Mbar m0 : ℝ} (ha : 0 < a)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hβr : (1 + r) * β = 1) (hCbar : Ybar + r * B0 = Cbar)
    (hC : 0 < Cbar) (hstab : β < 1 - Cbar * a) (hM : 0 < Mbar)
    (hm0 : Cbar / (1 - Cbar * a - β) ≤ m0) :
    IsOptimal (fun c k => Real.log c + (a * k + Real.log k)) β r
      ((1 + r) * B0 + Mbar / (Mbar / affinePath (Cbar / (1 - Cbar * a - β))
        ((1 - Cbar * a) / β) m0 0))
      (fun s => Ybar + (Mbar - Mbar) / (Mbar / affinePath (Cbar / (1 - Cbar * a - β))
        ((1 - Cbar * a) / β) m0 s))
      (userCost r (fun s => Mbar / affinePath (Cbar / (1 - Cbar * a - β))
        ((1 - Cbar * a) / β) m0 s)) (fun _ => Cbar)
      (fun s => Mbar / (Mbar / affinePath (Cbar / (1 - Cbar * a - β))
        ((1 - Cbar * a) / β) m0 s)) := by
  set mb := Cbar / (1 - Cbar * a - β) with hmbdef
  set κ := (1 - Cbar * a) / β with hκ
  set m := affinePath mb κ m0 with hmdef
  have hden : 0 < 1 - Cbar * a - β := by linarith
  have hmb0 : 0 < mb := div_pos hC hden
  have hκ1 : 1 ≤ κ := by rw [hκ, le_div_iff₀ hβ0]; linarith
  have hq0 : 0 ≤ 1 - Cbar * a := by linarith
  have hq1 : 1 - Cbar * a < 1 := by nlinarith
  have e : β * κ = 1 - Cbar * a := by rw [hκ]; field_simp
  have hmb' : mb * (1 - Cbar * a - β) = Cbar := by rw [hmbdef]; field_simp
  have hmlow : ∀ t, mb ≤ m t := fun t => by
    have := one_le_pow₀ hκ1 (n := t); simp only [hmdef, affinePath]; nlinarith
  have hmup : ∀ t, m t ≤ m0 * κ ^ t := fun t => by
    have := one_le_pow₀ hκ1 (n := t); simp only [hmdef, affinePath]; nlinarith
  have hpos : ∀ t, 0 < m t := fun t => lt_of_lt_of_le hmb0 (hmlow t)
  have hm0' : 0 < m0 := lt_of_lt_of_le hmb0 hm0
  have hmm : ∀ s, Mbar / (Mbar / m s) = m s := fun s => by
    have := (hpos s).ne'; field_simp
  have hβm : ∀ T, β ^ T * m T = β ^ T * mb + (1 - Cbar * a) ^ T * (m0 - mb) := fun T => by
    simp only [hmdef, affinePath]
    rw [mul_add, ← mul_assoc, ← mul_pow, e]
  have hN : ∀ s : ℕ, 0 < (fun _ => Mbar) s := fun _ => hM
  have hP : ∀ s, 0 < Mbar / m s := fun s => div_pos hM (hpos s)
  have hsum : Summable (fun s => β ^ s * (Real.log (Ybar + r * B0) + (a * (Mbar / (Mbar / m s)) +
      Real.log (Mbar / (Mbar / m s))))) := by
    simp only [hmm, hCbar]
    have hβn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
    have hA : Summable (fun s => a * (β ^ s * m s)) := by
      simp only [hβm]
      exact ((((summable_geometric_of_lt_one hβ0.le hβ1).mul_right mb).add
        ((summable_geometric_of_lt_one hq0 hq1).mul_right (m0 - mb))).mul_left a)
    set K := |Real.log Cbar| + |Real.log mb| + |Real.log m0| with hK
    have hB : Summable (fun s => β ^ s * (Real.log Cbar + Real.log (m s))) := by
      refine Summable.of_norm_bounded (g := fun s => K * β ^ s + Real.log κ *
        ((s : ℝ) ^ 1 * β ^ s)) (((summable_geometric_of_lt_one hβ0.le hβ1).mul_left K).add
        ((summable_pow_mul_geometric_of_norm_lt_one 1 hβn).mul_left _)) fun s => ?_
      have hl1 : Real.log mb ≤ Real.log (m s) := Real.log_le_log hmb0 (hmlow s)
      have hl2 : Real.log (m s) ≤ Real.log m0 + s * Real.log κ := by
        calc Real.log (m s) ≤ Real.log (m0 * κ ^ s) := Real.log_le_log (hpos s) (hmup s)
          _ = _ := by rw [Real.log_mul hm0'.ne' (by positivity), Real.log_pow]
      have hll : 0 ≤ Real.log κ := Real.log_nonneg hκ1
      have hβs := pow_pos hβ0 s
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hβs, pow_one]
      have habs : |Real.log Cbar + Real.log (m s)| ≤ K + s * Real.log κ := by
        rw [abs_le]
        have := neg_abs_le (Real.log Cbar)
        have := neg_abs_le (Real.log mb)
        have := abs_nonneg (Real.log m0)
        have := le_abs_self (Real.log Cbar)
        have := le_abs_self (Real.log m0)
        have := abs_nonneg (Real.log mb)
        have : 0 ≤ (s : ℝ) * Real.log κ := mul_nonneg (Nat.cast_nonneg s) hll
        constructor <;> linarith
      nlinarith
    convert hA.add hB using 1
    funext s
    ring
  have key := equilibrium_iff (μ := 0) (N := fun _ => Mbar) (P := fun s => Mbar / m s)
    (v' := fun k => a + k⁻¹) hβ0 hβ1 hβr (by norm_num) (hCbar ▸ hC) hN hP (fun _ => by ring)
    (linlog_concaveOn ha.le)
    (fun k hk => (((hasDerivAt_id k).const_mul a).add (Real.hasDerivAt_log hk.ne')).congr_deriv
      (by simp)) hsum
  simp only [hCbar] at key
  refine key.2 ⟨fun s => ?_, fun ε hε => ?_⟩
  · simp only [hmm, add_zero, div_one]
    have hX := (hpos s).ne'
    have hR : m s * (1 - Cbar * (a + (m s)⁻¹)) = m s * (1 - Cbar * a) - Cbar := by
      field_simp; ring
    rw [hR]
    simp only [hmdef, affinePath, pow_succ]
    linear_combination (κ ^ s * (m0 - mb)) * e - hmb'
  · simp only [hmm]
    have h1 : Tendsto (fun T : ℕ => β ^ T * mb + (1 - Cbar * a) ^ T * (m0 - mb)) atTop
        (𝓝 (0 * mb + 0 * (m0 - mb))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const _).add
        ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const _)
    simp only [zero_mul, add_zero] at h1
    exact ((h1.congr fun T => (hβm T).symm).eventually (gt_mem_nhds hε)).frequently

/-! ### The survey's counterexample `v'(m) = 1/log(m + e)` -/

/-- The integrand `1/log(t + e)` of the logarithmic-integral utility (fn 32 counterexample).
Context: O&R §8.3.5, pp. 538–546. -/
noncomputable def logIntDeriv (t : ℝ) : ℝ := 1 / Real.log (t + Real.exp 1)

/-- A logarithmic-integral utility of money, `v(m) = ∫₀^m dt/log(t + e)`, whose marginal utility
`1/log(m + e)` behaves like `1/log m` (the counterexample to fn 32, O&R p. 542). -/
noncomputable def logIntUtility (m : ℝ) : ℝ := ∫ t in (0 : ℝ)..m, logIntDeriv t

/-- `log(t + e) ≥ 1` for `t ≥ 0`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem one_le_log_add_exp {t : ℝ} (ht : 0 ≤ t) : 1 ≤ Real.log (t + Real.exp 1) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  linarith

/-- `1/log(t + e)` is continuous on `(0, ∞)` (indeed on `t > 1 − e`).
Context: O&R §8.3.5, pp. 538–546. -/
theorem logIntDeriv_continuousOn : ContinuousOn logIntDeriv (Set.Ioi (1 - Real.exp 1)) := by
  intro t ht
  simp only [Set.mem_Ioi] at ht
  have h1 : 1 < t + Real.exp 1 := by linarith
  have h2 : 0 < Real.log (t + Real.exp 1) := Real.log_pos h1
  have h3 : t + Real.exp 1 ≠ 0 := by linarith
  have hc : ContinuousAt (fun x : ℝ => x + Real.exp 1) t := continuousAt_id.add continuousAt_const
  have hl : ContinuousAt (fun x : ℝ => Real.log (x + Real.exp 1)) t := hc.log h3
  exact (continuousAt_const.div hl h2.ne').continuousWithinAt

/-- **`v' (m) = 1/log(m + e)`** for the logarithmic-integral utility (FTC).
Context: O&R §8.3.5, pp. 538–546. -/
theorem logIntUtility_hasDerivAt {m : ℝ} (hm : 0 < m) :
    HasDerivAt logIntUtility (logIntDeriv m) m := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hsub : Set.uIcc 0 m ⊆ Set.Ioi (1 - Real.exp 1) := by
    intro x hx
    rw [Set.uIcc_of_le hm.le] at hx
    simp only [Set.mem_Ioi]
    have := Real.add_one_le_exp 1
    linarith [hx.1]
  have hint : IntervalIntegrable logIntDeriv MeasureTheory.volume 0 m :=
    (logIntDeriv_continuousOn.mono hsub).intervalIntegrable
  have hm' : m ∈ Set.Ioi (1 - Real.exp 1) := by
    simp only [Set.mem_Ioi]; have := Real.add_one_le_exp 1; linarith
  exact intervalIntegral.integral_hasDerivAt_right hint
    (logIntDeriv_continuousOn.stronglyMeasurableAtFilter isOpen_Ioi m hm')
    (logIntDeriv_continuousOn.continuousAt (isOpen_Ioi.mem_nhds hm'))

/-- `1/log(t + e)` lies in `(0, 1]` for `t ≥ 0`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem logIntDeriv_mem {t : ℝ} (ht : 0 ≤ t) : 0 < logIntDeriv t ∧ logIntDeriv t ≤ 1 := by
  have h1 := one_le_log_add_exp ht
  unfold logIntDeriv
  exact ⟨by positivity, by rw [div_le_one (by linarith)]; exact h1⟩

/-- `1/log(t + e)` is strictly decreasing on `[0, ∞)`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem logIntDeriv_strictAntiOn : StrictAntiOn logIntDeriv (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have h1 := one_le_log_add_exp hx
  have h2 : Real.log (x + Real.exp 1) < Real.log (y + Real.exp 1) :=
    Real.log_lt_log (by positivity) (by linarith)
  unfold logIntDeriv
  exact one_div_lt_one_div_of_lt (by linarith) h2

/-- **The logarithmic-integral utility is strictly increasing and strictly concave**, with
`0 ≤ v(m) ≤ m` for `m ≥ 0`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem logIntUtility_props :
    StrictConcaveOn ℝ (Set.Ioi 0) logIntUtility ∧ StrictMonoOn logIntUtility (Set.Ioi 0) ∧
      ∀ m, 0 ≤ m → 0 ≤ logIntUtility m ∧ logIntUtility m ≤ m := by
  have hcont : ContinuousOn logIntUtility (Set.Ioi 0) :=
    fun m hm => (logIntUtility_hasDerivAt hm).continuousAt.continuousWithinAt
  have hder : ∀ m, 0 < m → deriv logIntUtility m = logIntDeriv m :=
    fun m hm => (logIntUtility_hasDerivAt hm).deriv
  refine ⟨StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0) hcont ?_, ?_, fun m hm => ?_⟩
  · intro x hx y hy hxy
    rw [interior_Ioi] at hx hy
    rw [hder x hx, hder y hy]
    exact logIntDeriv_strictAntiOn (Set.mem_Ici.2 (le_of_lt hx)) (Set.mem_Ici.2 (le_of_lt hy)) hxy
  · refine strictMonoOn_of_deriv_pos (convex_Ioi 0) hcont fun x hx => ?_
    rw [interior_Ioi] at hx
    rw [hder x hx]
    exact (logIntDeriv_mem (le_of_lt hx)).1
  · have hsub : Set.uIcc 0 m ⊆ Set.Ioi (1 - Real.exp 1) := by
      intro x hx
      rw [Set.uIcc_of_le hm] at hx
      simp only [Set.mem_Ioi]
      have := Real.add_one_le_exp 1
      linarith [hx.1]
    have hint : IntervalIntegrable logIntDeriv MeasureTheory.volume 0 m :=
      (logIntDeriv_continuousOn.mono hsub).intervalIntegrable
    constructor
    · exact intervalIntegral.integral_nonneg hm fun t ht => (logIntDeriv_mem ht.1).1.le
    · have := intervalIntegral.integral_mono_on hm hint
        (intervalIntegrable_const (c := (1 : ℝ))) fun t ht => (logIntDeriv_mem ht.1).2
      unfold logIntUtility
      simpa using this

/-- The deflationary orbit of (46) with constant money: `m_{t+1} = m_t(1 − h(m_t))/β`.
Context: O&R §8.3.5, pp. 538–546. -/
noncomputable def deflOrbit (β : ℝ) (h : ℝ → ℝ) (m0 : ℝ) (t : ℕ) : ℝ :=
  (fun x => x * (1 - h x) / β)^[t] m0

/-- The orbit satisfies (46) with constant money.
Context: O&R §8.3.5, pp. 538–546. -/
theorem deflOrbit_succ {β : ℝ} (hβ : 0 < β) (h : ℝ → ℝ) (m0 : ℝ) (t : ℕ) :
    β * deflOrbit β h m0 (t + 1) = deflOrbit β h m0 t * (1 - h (deflOrbit β h m0 t)) := by
  simp only [deflOrbit]
  rw [Function.iterate_succ_apply']
  field_simp

/-- **The fn 32 counterexample with `v'(m) = 1/log(m + e)`** (O&R p. 542, made precise):
`v(m) = ∫₀^m dt/log(t+e)` is strictly increasing and strictly concave, and with constant money,
`0 < β < 1`, `C̄ > 0`, any `m_0` with `C̄/log(m_0 + e) < 1 − β` starts a positive deflationary
path of (46) along which `Σ v'(m_t) = ∞`; so the individual TVC HOLDS (`β^T m_T → 0`
frequently, `tvc_iff_not_summable`). The proof uses the growth bound `m_t ≤ m_0 β^{−t}`, hence
`v'(m_t) ≥ 1/(log(m_0 + e) + t log(1/β))`, which is not summable. -/
theorem logInt_deflation_tvc {β Cbar m0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hC : 0 < Cbar)
    (hm00 : 0 < m0) (hm0 : Cbar * logIntDeriv m0 < 1 - β) :
    (∀ t, 0 < deflOrbit β (fun x => Cbar * logIntDeriv x) m0 t) ∧
      ¬ Summable (fun t => Cbar * logIntDeriv (deflOrbit β (fun x => Cbar * logIntDeriv x) m0 t)) ∧
      BubbleTVC β (deflOrbit β (fun x => Cbar * logIntDeriv x) m0) := by
  set h : ℝ → ℝ := fun x => Cbar * logIntDeriv x with hh
  set m := deflOrbit β h m0 with hm
  have hdyn := deflOrbit_succ hβ0 h m0
  have hanti : AntitoneOn h (Set.Ioi 0) := fun x hx y hy hxy =>
    mul_le_mul_of_nonneg_left (logIntDeriv_strictAntiOn.antitoneOn (Set.mem_Ici.2 (le_of_lt hx))
      (Set.mem_Ici.2 (le_of_lt hy)) hxy) hC.le
  have hnn : ∀ x, 0 < x → 0 ≤ h x := fun x hx =>
    mul_nonneg hC.le (logIntDeriv_mem (le_of_lt hx)).1.le
  -- positivity and monotonicity of the orbit
  have hstep : ∀ t, m0 ≤ m t → m t ≤ m (t + 1) := by
    intro t ht
    have h1 : h (m t) ≤ h m0 := hanti hm00 (lt_of_lt_of_le hm00 ht) ht
    have h2 := hdyn t
    have hmt : 0 < m t := lt_of_lt_of_le hm00 ht
    have : β ≤ 1 - h (m t) := by linarith
    nlinarith
  have hge : ∀ t, m0 ≤ m t := by
    intro t
    induction t with
    | zero => simp [hm, deflOrbit]
    | succ t ih => exact ih.trans (hstep t ih)
  have hpos : ∀ t, 0 < m t := fun t => lt_of_lt_of_le hm00 (hge t)
  have hm0' : h (m 0) < 1 - β := by simpa [hm, deflOrbit] using hm0
  -- the growth bound `m_t ≤ m_0 β^{-t}`
  have hup : ∀ t, m t ≤ m0 * (β⁻¹) ^ t := by
    intro t
    induction t with
    | zero => simp [hm, deflOrbit]
    | succ t ih =>
      have h2 := hdyn t
      have h3 := hnn _ (hpos t)
      have : m (t + 1) ≤ m t / β := by
        rw [le_div_iff₀ hβ0]; nlinarith [hpos t]
      calc m (t + 1) ≤ m t / β := this
        _ ≤ m0 * β⁻¹ ^ t / β := div_le_div_of_nonneg_right ih hβ0.le
        _ = m0 * β⁻¹ ^ (t + 1) := by rw [pow_succ]; field_simp
  set L0 := Real.log (m0 + Real.exp 1) with hL0
  set ell := Real.log β⁻¹ with hell
  have hell0 : 0 < ell := Real.log_pos (one_lt_inv_iff₀.2 ⟨hβ0, hβ1⟩)
  have hL01 : 1 ≤ L0 := one_le_log_add_exp hm00.le
  have hlow : ∀ t, Cbar * (1 / (L0 + t * ell)) ≤ h (m t) := by
    intro t
    have hbt : 1 ≤ β⁻¹ ^ t := one_le_pow₀ (one_le_inv_iff₀.2 ⟨hβ0, hβ1.le⟩)
    have h1 : m t + Real.exp 1 ≤ (m0 + Real.exp 1) * β⁻¹ ^ t := by
      have := hup t; nlinarith [Real.exp_pos 1]
    have h2 : Real.log (m t + Real.exp 1) ≤ L0 + t * ell := by
      calc Real.log (m t + Real.exp 1) ≤ Real.log ((m0 + Real.exp 1) * β⁻¹ ^ t) :=
            Real.log_le_log (by have := hpos t; positivity) h1
        _ = L0 + t * ell := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have h3 : 0 < Real.log (m t + Real.exp 1) := by
      linarith [one_le_log_add_exp (hpos t).le]
    simp only [hh, logIntDeriv]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le h3 h2) hC.le
  have hns : ¬ Summable (fun t => h (m t)) := by
    intro hs
    have hharm : ¬ Summable (fun t : ℕ => 1 / ((t : ℝ) + 1)) := by
      have := Real.not_summable_natCast_inv
      rwa [← summable_nat_add_iff 1, show (fun n : ℕ => ((↑(n + 1) : ℝ))⁻¹) =
        fun t : ℕ => 1 / ((t : ℝ) + 1) by funext t; push_cast; rw [one_div]] at this
    apply hharm
    refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_)
      (hs.mul_left ((L0 + ell) / Cbar))
    have h1 := hlow t
    have h2 : L0 + t * ell ≤ (L0 + ell) * (t + 1) := by
      have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      nlinarith
    have h3 : 1 / ((L0 + ell) * (t + 1)) ≤ 1 / (L0 + t * ell) :=
      one_div_le_one_div_of_le (by have : (0 : ℝ) ≤ t := Nat.cast_nonneg t; positivity) h2
    have h4 : 1 / ((t : ℝ) + 1) = (L0 + ell) * (1 / ((L0 + ell) * (t + 1))) := by
      field_simp
    rw [h4]
    calc (L0 + ell) * (1 / ((L0 + ell) * (t + 1))) ≤ (L0 + ell) * (1 / (L0 + t * ell)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (L0 + ell) / Cbar * (Cbar * (1 / (L0 + t * ell))) := by field_simp
      _ ≤ (L0 + ell) / Cbar * h (m t) := mul_le_mul_of_nonneg_left h1 (by positivity)
  exact ⟨hpos, hns, (tvc_iff_not_summable hβ0 hpos hdyn hanti hnn hm0').2 hns⟩

/-- The logarithmic-integral utility is unbounded above (as it must be, by
`bounded_rules_out_deflation`, since the TVC holds along its deflationary paths).
Context: O&R §8.3.5, pp. 538–546. -/
theorem logIntUtility_unbounded (V : ℝ) : ∃ k, 0 < k ∧ V < logIntUtility k := by
  by_contra hcon
  push Not at hcon
  set m0 := Real.exp 2 with hm0
  have hm00 : 0 < m0 := Real.exp_pos 2
  have hlog : 2 < Real.log (m0 + Real.exp 1) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    linarith [Real.exp_pos 1]
  have hm0' : 1 * logIntDeriv m0 < 1 - 1 / 2 := by
    unfold logIntDeriv
    rw [one_mul, div_lt_iff₀ (by linarith)]
    linarith
  obtain ⟨hpos, -, htvc⟩ := logInt_deflation_tvc (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num) one_pos hm00 hm0'
  have hanti : AntitoneOn (fun k => 1 * logIntDeriv k) (Set.Ioi 0) := fun x hx y hy hxy => by
    simp only [one_mul]
    exact logIntDeriv_strictAntiOn.antitoneOn (Set.mem_Ici.2 (le_of_lt hx))
      (Set.mem_Ici.2 (le_of_lt hy)) hxy
  exact bounded_rules_out_deflation (by norm_num) one_pos hpos
    (deflOrbit_succ (by norm_num) _ m0) logIntUtility_props.1.concaveOn
    (fun k hk => logIntUtility_hasDerivAt hk) hanti
    (fun k hk => (logIntDeriv_mem (le_of_lt hk)).1.le) hcon (by simpa [deflOrbit] using hm0') htvc

/-- The telescoping lower bound `Σ_{t<s} 1/(L₀ + tℓ) ≥ (log(L₀ + sℓ) − log L₀)/ℓ`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem sum_inv_linear_ge {L0 ell : ℝ} (hL0 : 0 < L0) (hell : 0 < ell) (s : ℕ) :
    (Real.log (L0 + s * ell) - Real.log L0) / ell ≤
      ∑ t ∈ Finset.range s, 1 / (L0 + t * ell) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ]
    have ha : 0 < L0 + s * ell := by have : (0 : ℝ) ≤ s := Nat.cast_nonneg s; positivity
    have hstep : Real.log (L0 + (s + 1 : ℕ) * ell) - Real.log (L0 + s * ell) ≤
        ell / (L0 + s * ell) := by
      rw [← Real.log_div (by push_cast; positivity) ha.ne']
      have := Real.log_le_sub_one_of_pos (show 0 < (L0 + (s + 1 : ℕ) * ell) / (L0 + s * ell) by
        push_cast; positivity)
      have e : (L0 + (s + 1 : ℕ) * ell) / (L0 + s * ell) - 1 = ell / (L0 + s * ell) := by
        push_cast; field_simp; ring
      linarith
    have h2 : (Real.log (L0 + (s + 1 : ℕ) * ell) - Real.log L0) / ell =
        (Real.log (L0 + s * ell) - Real.log L0) / ell +
          (Real.log (L0 + (s + 1 : ℕ) * ell) - Real.log (L0 + s * ell)) / ell := by ring
    have h3 : (Real.log (L0 + (s + 1 : ℕ) * ell) - Real.log (L0 + s * ell)) / ell ≤
        1 / (L0 + s * ell) := by
      rw [div_le_iff₀ hell]
      calc _ ≤ ell / (L0 + s * ell) := hstep
        _ = 1 / (L0 + s * ell) * ell := by ring
    linarith

/-- **The fn 32 counterexample is a genuine equilibrium** (constant money, `μ = 0`): with
`u = log C + ∫₀^{M/P} dt/log(t+e)`, `(1+r)β = 1`, `C̄ = Ȳ + rB_0 > log(1/β)` and
`C̄/log(m_0 + e) < 1 − β`, the deflationary price path `P_s = M̄/m_s` (`m` the orbit of (46)
from `m_0`) is an equilibrium: the household's plan is optimal (lifetime utility is finite
because `β^s m_s ≤ m_0 (L₀/(L₀ + s log(1/β)))^{C̄/log(1/β)}` with exponent above one). So a
strictly concave, increasing `v` with `v' ≈ 1/log m` admits speculative deflations.
Context: O&R §8.3.5, pp. 538–546. -/
theorem logInt_deflation_equilibrium {β r Ybar B0 Cbar Mbar m0 : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hβr : (1 + r) * β = 1) (hCbar : Ybar + r * B0 = Cbar) (hC : 0 < Cbar)
    (hCell : Real.log β⁻¹ < Cbar) (hM : 0 < Mbar) (hm00 : 0 < m0)
    (hm0 : Cbar * logIntDeriv m0 < 1 - β) :
    IsOptimal (fun c k => Real.log c + logIntUtility k) β r
      ((1 + r) * B0 + Mbar / (Mbar / deflOrbit β (fun x => Cbar * logIntDeriv x) m0 0))
      (fun s => Ybar + (Mbar - Mbar) / (Mbar / deflOrbit β (fun x => Cbar * logIntDeriv x) m0 s))
      (userCost r (fun s => Mbar / deflOrbit β (fun x => Cbar * logIntDeriv x) m0 s))
      (fun _ => Cbar)
      (fun s => Mbar / (Mbar / deflOrbit β (fun x => Cbar * logIntDeriv x) m0 s)) := by
  set h : ℝ → ℝ := fun x => Cbar * logIntDeriv x with hh
  set m := deflOrbit β h m0 with hm
  obtain ⟨hpos, hns, htvc⟩ := logInt_deflation_tvc hβ0 hβ1 hC hm00 hm0
  have hdyn := deflOrbit_succ hβ0 h m0
  have hmm : ∀ s, Mbar / (Mbar / m s) = m s := fun s => by
    have := (hpos s).ne'; field_simp
  have hN : ∀ s : ℕ, 0 < (fun _ => Mbar) s := fun _ => hM
  have hP : ∀ s, 0 < Mbar / m s := fun s => div_pos hM (hpos s)
  -- summability of lifetime utility
  set L0 := Real.log (m0 + Real.exp 1) with hL0
  set ell := Real.log β⁻¹ with hell
  have hell0 : 0 < ell := Real.log_pos (one_lt_inv_iff₀.2 ⟨hβ0, hβ1⟩)
  have hL01 : 1 ≤ L0 := one_le_log_add_exp hm00.le
  set p := Cbar / ell with hp
  have hp1 : 1 < p := by rw [hp, one_lt_div hell0]; exact hCell
  have hle1 : ∀ t, h (m t) ≤ 1 := fun t => by
    have hanti : h (m t) ≤ h m0 := by
      have hge : m0 ≤ m t := by
        induction t with
        | zero => simp [hm, deflOrbit]
        | succ t ih =>
          have h2 := hdyn t
          have h1 : h (m t) ≤ h m0 := mul_le_mul_of_nonneg_left
            (logIntDeriv_strictAntiOn.antitoneOn (Set.mem_Ici.2 hm00.le)
              (Set.mem_Ici.2 (le_of_lt (hpos t))) ih) hC.le
          have : β ≤ 1 - h (m t) := by linarith
          nlinarith [hpos t]
      exact mul_le_mul_of_nonneg_left (logIntDeriv_strictAntiOn.antitoneOn
        (Set.mem_Ici.2 hm00.le) (Set.mem_Ici.2 (le_of_lt (hpos t))) hge) hC.le
    linarith
  have hup : ∀ t, m t ≤ m0 * (β⁻¹) ^ t := by
    intro t
    induction t with
    | zero => simp [hm, deflOrbit]
    | succ t ih =>
      have h2 := hdyn t
      have h3 : 0 ≤ h (m t) := mul_nonneg hC.le (logIntDeriv_mem (hpos t).le).1.le
      have : m (t + 1) ≤ m t / β := by
        rw [le_div_iff₀ hβ0]; nlinarith [hpos t]
      calc m (t + 1) ≤ m t / β := this
        _ ≤ m0 * β⁻¹ ^ t / β := div_le_div_of_nonneg_right ih hβ0.le
        _ = m0 * β⁻¹ ^ (t + 1) := by rw [pow_succ]; field_simp
  have hlow : ∀ t, Cbar * (1 / (L0 + t * ell)) ≤ h (m t) := by
    intro t
    have hbt : 1 ≤ β⁻¹ ^ t := one_le_pow₀ (one_le_inv_iff₀.2 ⟨hβ0, hβ1.le⟩)
    have h1 : m t + Real.exp 1 ≤ (m0 + Real.exp 1) * β⁻¹ ^ t := by
      have := hup t; nlinarith [Real.exp_pos 1]
    have h2 : Real.log (m t + Real.exp 1) ≤ L0 + t * ell := by
      calc Real.log (m t + Real.exp 1) ≤ Real.log ((m0 + Real.exp 1) * β⁻¹ ^ t) :=
            Real.log_le_log (by have := hpos t; positivity) h1
        _ = L0 + t * ell := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have h3 : 0 < Real.log (m t + Real.exp 1) := by
      linarith [one_le_log_add_exp (hpos t).le]
    simp only [hh, logIntDeriv]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le h3 h2) hC.le
  set c := min L0 ell with hc
  have hc0 : 0 < c := lt_min (by linarith) hell0
  have hbound : ∀ s, β ^ s * m s ≤ m0 * (L0 / c) ^ p * (((s + 1 : ℕ) : ℝ) ^ p)⁻¹ := by
    intro s
    rw [discounted_product hdyn s]
    have h1 := prod_le_exp_neg_sum hle1 s
    have h2 : Cbar * ((Real.log (L0 + s * ell) - Real.log L0) / ell) ≤
        ∑ t ∈ Finset.range s, h (m t) := by
      calc Cbar * ((Real.log (L0 + s * ell) - Real.log L0) / ell)
          ≤ Cbar * ∑ t ∈ Finset.range s, 1 / (L0 + t * ell) :=
            mul_le_mul_of_nonneg_left (sum_inv_linear_ge (by linarith) hell0 s) hC.le
        _ = ∑ t ∈ Finset.range s, Cbar * (1 / (L0 + t * ell)) := by rw [Finset.mul_sum]
        _ ≤ _ := Finset.sum_le_sum fun t _ => hlow t
    have hX : 0 < L0 + s * ell := by have : (0 : ℝ) ≤ s := Nat.cast_nonneg s; positivity
    have h3 : Real.exp (-∑ t ∈ Finset.range s, h (m t)) ≤ (L0 / (L0 + s * ell)) ^ p := by
      rw [rpow_def_of_pos (div_pos (by linarith) hX), Real.log_div (by linarith) hX.ne']
      apply Real.exp_le_exp.2
      have : Cbar * ((Real.log (L0 + s * ell) - Real.log L0) / ell) =
          (Real.log (L0 + s * ell) - Real.log L0) * p := by rw [hp]; field_simp
      linarith
    have h4 : (L0 / (L0 + s * ell)) ^ p ≤ (L0 / c) ^ p * (((s + 1 : ℕ) : ℝ) ^ p)⁻¹ := by
      have hcs : c * ((s + 1 : ℕ) : ℝ) ≤ L0 + s * ell := by
        push_cast
        have h5 : c ≤ L0 := min_le_left _ _
        have h6 : c ≤ ell := min_le_right _ _
        have : (0 : ℝ) ≤ s := Nat.cast_nonneg s
        nlinarith
      have h7 : L0 / (L0 + s * ell) ≤ L0 / (c * ((s + 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_left (by linarith) (by positivity) hcs
      calc (L0 / (L0 + s * ell)) ^ p ≤ (L0 / (c * ((s + 1 : ℕ) : ℝ))) ^ p :=
            rpow_le_rpow (by positivity) h7 (by linarith)
        _ = (L0 / c) ^ p * (((s + 1 : ℕ) : ℝ) ^ p)⁻¹ := by
            rw [div_mul_eq_div_div, div_rpow (by positivity) (by positivity), div_eq_mul_inv]
    calc m 0 * ∏ t ∈ Finset.range s, (1 - h (m t)) ≤ m 0 * Real.exp (-∑ t ∈ Finset.range s,
          h (m t)) := mul_le_mul_of_nonneg_left h1 (hpos 0).le
      _ ≤ m 0 * ((L0 / c) ^ p * (((s + 1 : ℕ) : ℝ) ^ p)⁻¹) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) (hpos 0).le
      _ = m0 * (L0 / c) ^ p * (((s + 1 : ℕ) : ℝ) ^ p)⁻¹ := by simp [hm, deflOrbit]; ring
  have hps : Summable (fun s : ℕ => (((s + 1 : ℕ) : ℝ) ^ p)⁻¹) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.2 hp1)
  have hbm : Summable (fun s => β ^ s * m s) :=
    Summable.of_nonneg_of_le (fun s => mul_nonneg (pow_pos hβ0 s).le (hpos s).le) hbound
      (hps.mul_left _)
  have hsum : Summable (fun s => β ^ s * (Real.log (Ybar + r * B0) +
      logIntUtility (Mbar / (Mbar / m s)))) := by
    simp only [hmm, hCbar, mul_add]
    refine ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right _).add ?_
    refine Summable.of_nonneg_of_le (fun s => mul_nonneg (pow_pos hβ0 s).le
      (logIntUtility_props.2.2 _ (hpos s).le).1) (fun s => ?_) hbm
    exact mul_le_mul_of_nonneg_left (logIntUtility_props.2.2 _ (hpos s).le).2 (pow_pos hβ0 s).le
  have key := equilibrium_iff (μ := 0) (N := fun _ => Mbar) (P := fun s => Mbar / m s)
    (v := logIntUtility) (v' := logIntDeriv) hβ0 hβ1 hβr (by norm_num) (hCbar ▸ hC) hN hP
    (fun _ => by ring) logIntUtility_props.1.concaveOn (fun k hk => logIntUtility_hasDerivAt hk)
    hsum
  simp only [hCbar] at key
  refine key.2 ⟨fun s => ?_, fun ε hε => ?_⟩
  · simp only [hmm, add_zero, div_one]
    exact hdyn s
  · simp only [hmm]
    exact htvc ε hε

/-! ## Speculative hyperinflations: (52), (54) and footnote 34 (§8.3.5.4) -/

/-- **Footnote 34**, O&R p. 545: if (54) holds in the form `m v'(m) ≥ c₀ > 0` for all small
`m`, then `lim_{m→0} v(m) = −∞`. (The book's proof, made quantitative: along `m_k = y/2^k`,
concavity gives `v(m_{k+1}) ≤ v(m_k) − c₀/2`.) -/
theorem fn34_tendsto_atBot {v v' : ℝ → ℝ} {c0 δ : ℝ} (hc0 : 0 < c0) (hδ : 0 < δ)
    (hv : ConcaveOn ℝ (Set.Ioi 0) v) (hmono : MonotoneOn v (Set.Ioi 0))
    (hv' : ∀ k, 0 < k → HasDerivAt v (v' k) k) (h54 : ∀ x, 0 < x → x < δ → c0 ≤ x * v' x) :
    Tendsto v (𝓝[>] 0) atBot := by
  set y := δ / 2 with hydef
  have hy : 0 < y := by positivity
  have hstep : ∀ k : ℕ, v (y / 2 ^ k) ≤ v y - k * (c0 / 2) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hx : 0 < y / 2 ^ k := by positivity
      have hxy : y / 2 ^ k ≤ y := div_le_self hy.le (one_le_pow₀ (by norm_num))
      have hxδ : y / 2 ^ k < δ := by linarith
      have h1 := concave_le_tangent' hv hx (show (0 : ℝ) < y / 2 ^ k / 2 by positivity)
        (hv' _ hx)
      have h2 := h54 _ hx hxδ
      rw [pow_succ, ← div_div]
      push_cast
      nlinarith
  rw [tendsto_atBot]
  intro b
  obtain ⟨k, hk⟩ := exists_nat_gt ((v y - b) / (c0 / 2))
  have hk' : v y - k * (c0 / 2) < b := by
    rw [div_lt_iff₀ (by positivity)] at hk; linarith
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < y / 2 ^ k by positivity)] with x hx
  exact (hmono hx.1 (show (0 : ℝ) < y / 2 ^ k by positivity) hx.2.le).trans
    ((hstep k).trans hk'.le)

/-- **Footnote 34 sharpened** (its contrapositive, quantitative): if `v` is concave,
nondecreasing and BOUNDED BELOW near zero, then (52) holds: `m v'(m) → 0` as `m → 0`. Indeed
`0 ≤ m v'(m) ≤ v(m) − inf v`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem fn34_sharpened {v v' : ℝ → ℝ} {L : ℝ} (hv : ConcaveOn ℝ (Set.Ioi 0) v)
    (hv' : ∀ k, 0 < k → HasDerivAt v (v' k) k) (hnn : ∀ k, 0 < k → 0 ≤ v' k)
    (hL : ∀ k, 0 < k → L ≤ v k) : Tendsto (fun x => x * v' x) (𝓝[>] 0) (𝓝 0) := by
  set S := v '' Set.Ioi 0 with hS
  have hne : S.Nonempty := ⟨v 1, 1, Set.mem_Ioi.2 one_pos, rfl⟩
  have hbdd : BddBelow S := ⟨L, by rintro _ ⟨k, hk, rfl⟩; exact hL k hk⟩
  set ℓ := sInf S with hℓ
  have hℓle : ∀ k, 0 < k → ℓ ≤ v k := fun k hk => csInf_le hbdd ⟨k, hk, rfl⟩
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun ε hε => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact lt_of_lt_of_le ha (mul_nonneg (le_of_lt hx) (hnn x hx))
  · obtain ⟨_, ⟨y0, hy0, rfl⟩, hy0lt⟩ := exists_lt_of_csInf_lt hne
      (show ℓ < ℓ + ε / 2 by linarith)
    filter_upwards [Ioo_mem_nhdsGT hy0] with x hx
    obtain ⟨hx0, hxy0⟩ := hx
    have hvx : v x ≤ v y0 := by
      have := concave_le_tangent' hv hy0 hx0 (hv' y0 hy0)
      have := hnn y0 hy0
      nlinarith
    have hd := hnn x hx0
    set y := min (x / 2) (ε / (4 * (v' x + 1))) with hydef
    have hy0' : 0 < y := lt_min (by positivity) (by positivity)
    have hyx : y < x := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have htan := concave_le_tangent' hv hx0 hy0' (hv' x hx0)
    have hℓy := hℓle y hy0'
    have h1 : v' x * (x - y) < ε / 2 := by nlinarith
    have h2 : v' x * y ≤ ε / 4 := by
      have hy2 : y ≤ ε / (4 * (v' x + 1)) := min_le_right _ _
      have : v' x * y ≤ v' x * (ε / (4 * (v' x + 1))) := mul_le_mul_of_nonneg_left hy2 hd
      have h3 : v' x * (ε / (4 * (v' x + 1))) ≤ ε / 4 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    nlinarith

/-- The slowly diverging function `L(m) = log(1 + 1/m)` used in the counterexample to the
converse of footnote 34.
Context: O&R §8.3.5, pp. 538–546. -/
noncomputable def slowLog (m : ℝ) : ℝ := Real.log (1 + m⁻¹)

/-- `L(m) = log(1 + 1/m) ≥ 0` for `m > 0`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem slowLog_nonneg {m : ℝ} (hm : 0 < m) : 0 ≤ slowLog m :=
  Real.log_nonneg (by have := inv_pos.2 hm; linarith)

/-- `L'(m) = −1/(m(m+1))`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem slowLog_hasDerivAt {m : ℝ} (hm : 0 < m) :
    HasDerivAt slowLog (-1 / (m * (m + 1))) m := by
  have h1 : 0 < 1 + m⁻¹ := by have := inv_pos.2 hm; linarith
  have h := ((hasDerivAt_inv hm.ne').const_add 1).log h1.ne'
  refine h.congr_deriv ?_
  field_simp

/-- The counterexample to the converse of footnote 34: `v(m) = −log(1 + log(1 + 1/m))`.
Context: O&R §8.3.5, pp. 538–546. -/
noncomputable def vSlow (m : ℝ) : ℝ := -Real.log (1 + slowLog m)

/-- `v'(m) = 1/((1 + L(m)) m (m+1))` for the counterexample.
Context: O&R §8.3.5, pp. 538–546. -/
theorem vSlow_hasDerivAt {m : ℝ} (hm : 0 < m) :
    HasDerivAt vSlow (1 / ((1 + slowLog m) * m * (m + 1))) m := by
  have hL := slowLog_nonneg hm
  have h := ((slowLog_hasDerivAt hm).const_add 1).log (by linarith)
  refine h.neg.congr_deriv ?_
  field_simp

/-- **The converse of footnote 34 fails** (O&R p. 545, "necessary (but not sufficient)"):
`v(m) = −log(1 + log(1 + 1/m))` is strictly increasing and concave on `(0, ∞)`, satisfies (52),
`m v'(m) → 0`, and yet `v(m) → −∞` as `m → 0`. -/
theorem vSlow_counterexample :
    StrictMonoOn vSlow (Set.Ioi 0) ∧ ConcaveOn ℝ (Set.Ioi 0) vSlow ∧
      Tendsto (fun m => m * (1 / ((1 + slowLog m) * m * (m + 1)))) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto vSlow (𝓝[>] 0) atBot := by
  have hder : ∀ m, 0 < m → deriv vSlow m = 1 / ((1 + slowLog m) * m * (m + 1)) :=
    fun m hm => (vSlow_hasDerivAt hm).deriv
  have hcont : ContinuousOn vSlow (Set.Ioi 0) :=
    fun m hm => (vSlow_hasDerivAt hm).continuousAt.continuousWithinAt
  -- `g(m) = (1 + L(m)) m (m+1)` is strictly increasing
  set g : ℝ → ℝ := fun m => (1 + slowLog m) * (m * (m + 1)) with hg
  have hgd : ∀ m, 0 < m → HasDerivAt g ((1 + slowLog m) * (2 * m + 1) - 1) m := by
    intro m hm
    have h1 := ((slowLog_hasDerivAt hm).const_add 1).mul
      (((hasDerivAt_id m).mul ((hasDerivAt_id m).add_const 1)))
    refine h1.congr_deriv ?_
    simp only [Pi.mul_apply, id]
    field_simp
    ring
  have hgmono : StrictMonoOn g (Set.Ioi 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
      (fun m hm => (hgd m hm).continuousAt.continuousWithinAt) (fun m hm => ?_)
    rw [interior_Ioi] at hm
    rw [(hgd m hm).deriv]
    have := slowLog_nonneg hm
    have hm' : (0 : ℝ) < m := hm
    nlinarith
  have hgpos : ∀ m, 0 < m → 0 < g m := fun m hm => by
    have := slowLog_nonneg hm; simp only [hg]; positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine strictMonoOn_of_deriv_pos (convex_Ioi 0) hcont (fun m hm => ?_)
    rw [interior_Ioi] at hm
    rw [hder m hm]
    have := slowLog_nonneg hm
    have hm' : (0 : ℝ) < m := hm
    positivity
  · refine AntitoneOn.concaveOn_of_deriv (convex_Ioi 0) hcont
      (fun m hm => by
        rw [interior_Ioi] at hm
        exact (vSlow_hasDerivAt hm).differentiableAt.differentiableWithinAt)
      (fun x hx y hy hxy => ?_)
    rw [interior_Ioi] at hx hy
    rw [hder x hx, hder y hy]
    have h1 := hgmono.monotoneOn hx hy hxy
    have hgx := hgpos x hx
    simp only [hg] at h1 hgx
    rw [show (1 + slowLog x) * x * (x + 1) = (1 + slowLog x) * (x * (x + 1)) by ring,
      show (1 + slowLog y) * y * (y + 1) = (1 + slowLog y) * (y * (y + 1)) by ring]
    exact one_div_le_one_div_of_le hgx h1
  · have hL : Tendsto slowLog (𝓝[>] 0) atTop :=
      Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ 1 tendsto_inv_nhdsGT_zero)
    have hinv : Tendsto (fun m => 1 / (1 + slowLog m)) (𝓝[>] 0) (𝓝 0) := by
      have := tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 hL)
      simpa [Function.comp_def, one_div] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with m hm
      have := slowLog_nonneg hm
      have hm' : (0 : ℝ) < m := hm
      positivity
    · filter_upwards [self_mem_nhdsWithin] with m hm
      have := slowLog_nonneg hm
      have hm' : (0 : ℝ) < m := hm
      rw [show m * (1 / ((1 + slowLog m) * m * (m + 1))) = 1 / ((1 + slowLog m) * (m + 1)) by
        field_simp]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
  · have hL : Tendsto slowLog (𝓝[>] 0) atTop :=
      Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ 1 tendsto_inv_nhdsGT_zero)
    exact tendsto_neg_atTop_atBot.comp
      (Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ 1 hL))

/-! ### Hyperinflationary paths (Figure 8.3) and fractional backing (§8.3.5.5) -/

/-- The forward map of (46): `φ(m) = ((1+μ)/β) m (1 − h(m))` with `h = C̄v'` (O&R Fig. 8.3);
`λ = (1+μ)/β`. -/
noncomputable def phiMap (lam : ℝ) (h : ℝ → ℝ) (m : ℝ) : ℝ := lam * m * (1 - h m)

/-- On `[m*, ∞)`, where `h(m*) = 1` (i.e. `C̄v'(m*) = 1`, condition (53)), the map `φ` is strictly
increasing (O&R Fig. 8.3). -/
theorem phiMap_strictMonoOn {lam mstar : ℝ} {h : ℝ → ℝ} (hlam : 0 < lam) (hms : 0 < mstar)
    (hanti : StrictAntiOn h (Set.Ioi 0)) (hstar : h mstar = 1) :
    StrictMonoOn (phiMap lam h) (Set.Ici mstar) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have hx0 : 0 < x := lt_of_lt_of_le hms hx
  have hy0 : 0 < y := lt_of_lt_of_le hms hy
  have h1 : h y < h x := hanti hx0 hy0 hxy
  have h2 : h x ≤ 1 := by
    rcases hx.lt_or_eq with hlt | heq
    · exact (hanti hms hx0 hlt).le.trans hstar.le
    · rw [← heq, hstar]
  unfold phiMap
  have : 0 ≤ 1 - h x := by linarith
  have e1 : x * (1 - h x) ≤ y * (1 - h x) := mul_le_mul_of_nonneg_right hxy.le this
  have e2 : y * (1 - h x) < y * (1 - h y) := mul_lt_mul_of_pos_left (by linarith) hy0
  calc lam * x * (1 - h x) = lam * (x * (1 - h x)) := by ring
    _ < lam * (y * (1 - h y)) := mul_lt_mul_of_pos_left (e1.trans_lt e2) hlam
    _ = lam * y * (1 - h y) := by ring

/-- **Every point of `[0, m̄]` has a unique preimage in `[m*, m̄]`** (IVT; O&R Fig. 8.3). -/
theorem phiMap_preimage {lam mstar mb : ℝ} {h : ℝ → ℝ} (hlam : 0 < lam) (hms : 0 < mstar)
    (hlt : mstar < mb) (hcont : ContinuousOn h (Set.Ioi 0)) (hanti : StrictAntiOn h (Set.Ioi 0))
    (hstar : h mstar = 1) (hbar : lam * (1 - h mb) = 1) {y : ℝ} (hy : y ∈ Set.Icc 0 mb) :
    ∃! x, x ∈ Set.Icc mstar mb ∧ phiMap lam h x = y := by
  have hφs : phiMap lam h mstar = 0 := by simp [phiMap, hstar]
  have hφb : phiMap lam h mb = mb := by
    simp only [phiMap]; linear_combination mb * hbar
  have hc : ContinuousOn (phiMap lam h) (Set.Icc mstar mb) := by
    have : ContinuousOn h (Set.Icc mstar mb) :=
      hcont.mono fun x hx => lt_of_lt_of_le hms hx.1
    exact ((continuousOn_const.mul continuousOn_id).mul (continuousOn_const.sub this))
  obtain ⟨x, hx, hφx⟩ := intermediate_value_Icc hlt.le hc (by rw [hφs, hφb]; exact hy)
  refine ⟨x, ⟨hx, hφx⟩, fun x' ⟨hx', hφx'⟩ => ?_⟩
  exact (phiMap_strictMonoOn hlam hms hanti hstar).injOn hx'.1 hx.1 (hφx'.trans hφx.symm)

/-- The chosen preimage in `[m*, m̄]` (O&R Fig. 8.3). -/
noncomputable def phiPre (lam : ℝ) (h : ℝ → ℝ) (mstar mb y : ℝ) : ℝ :=
  Classical.epsilon (fun x => x ∈ Set.Icc mstar mb ∧ phiMap lam h x = y)

/-- The backward orbit `b_0 = m*`, `b_{k+1} = φ^{−1}(b_k)`: `b_{T−1}` is the initial real
balance from which the economy reaches `m*` at date `T − 1` and money becomes worthless at `T`
(O&R (53) and Fig. 8.3). -/
noncomputable def backOrbit (lam : ℝ) (h : ℝ → ℝ) (mstar mb : ℝ) : ℕ → ℝ
  | 0 => mstar
  | k + 1 => phiPre lam h mstar mb (backOrbit lam h mstar mb k)

/-- **Hyperinflationary paths (Figure 8.3), made precise**: under (52)-type assumptions — `h = C̄v'`
continuous and strictly decreasing, `h(m*) = 1` for some `0 < m* < m̄` (condition (53)) and
`λ(1 − h(m̄)) = 1` (the steady state) — the backward orbit satisfies `b_k ∈ [m*, m̄)`,
`φ(b_{k+1}) = b_k`, and is strictly increasing. So for every `T ≥ 1` the initial real balance
`b_{T−1}` leads to `m_{T−1} = m*` and `m_T = φ(m*) = 0`: the price level becomes infinite at `T`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem backOrbit_spec {lam mstar mb : ℝ} {h : ℝ → ℝ} (hlam : 0 < lam) (hms : 0 < mstar)
    (hlt : mstar < mb) (hcont : ContinuousOn h (Set.Ioi 0)) (hanti : StrictAntiOn h (Set.Ioi 0))
    (hstar : h mstar = 1) (hbar : lam * (1 - h mb) = 1) (k : ℕ) :
    backOrbit lam h mstar mb k ∈ Set.Ico mstar mb ∧
      phiMap lam h (backOrbit lam h mstar mb (k + 1)) = backOrbit lam h mstar mb k ∧
      backOrbit lam h mstar mb k < backOrbit lam h mstar mb (k + 1) := by
  have hφb : phiMap lam h mb = mb := by
    simp only [phiMap]; linear_combination mb * hbar
  have hmono := phiMap_strictMonoOn hlam hms hanti hstar
  have hstep : ∀ y, y ∈ Set.Ico mstar mb → phiPre lam h mstar mb y ∈ Set.Icc mstar mb ∧
      phiMap lam h (phiPre lam h mstar mb y) = y := by
    intro y hy
    have hex := (phiMap_preimage hlam hms hlt hcont hanti hstar hbar
      ⟨hms.le.trans hy.1, hy.2.le⟩).exists
    exact Classical.epsilon_spec hex
  have hin : ∀ k, backOrbit lam h mstar mb k ∈ Set.Ico mstar mb := by
    intro k
    induction k with
    | zero => exact ⟨le_rfl, hlt⟩
    | succ k ih =>
      obtain ⟨⟨h1, h2⟩, h3⟩ := hstep _ ih
      have hb1 : backOrbit lam h mstar mb (k + 1) =
          phiPre lam h mstar mb (backOrbit lam h mstar mb k) := rfl
      refine ⟨h1, lt_of_le_of_ne h2 fun heq => ?_⟩
      rw [← hb1, heq, hφb] at h3
      exact absurd h3.symm (ne_of_lt ih.2)
  refine ⟨hin k, (hstep _ (hin k)).2, ?_⟩
  -- strict increase
  induction k with
  | zero =>
    have h1 := (hstep _ (hin 0)).1
    rcases h1.1.lt_or_eq with hlt' | heq
    · exact hlt'
    · exfalso
      have h3 := (hstep _ (hin 0)).2
      rw [← heq] at h3
      simp only [backOrbit, phiMap, hstar, sub_self, mul_zero] at h3
      linarith
  | succ k ih =>
    have h1 := (hstep _ (hin k)).2
    have h2 := (hstep _ (hin (k + 1))).2
    have hk1 := hin (k + 1)
    have hk2 := hin (k + 2)
    by_contra hle
    push Not at hle
    have := hmono.monotoneOn (show backOrbit lam h mstar mb (k + 2) ∈ Set.Ici mstar from hk2.1)
      (show backOrbit lam h mstar mb (k + 1) ∈ Set.Ici mstar from hk1.1) hle
    simp only [backOrbit] at h1 h2 this ih ⊢
    linarith

/-- **The collapse date** (O&R (53)): starting from `b_k` the forward orbit of (46) reaches `m*`
(where `C̄v'(m*) = 1`) after `k` periods and zero real balances (`P = ∞`) after `k + 1`. -/
theorem backOrbit_iterate {lam mstar mb : ℝ} {h : ℝ → ℝ} (hlam : 0 < lam) (hms : 0 < mstar)
    (hlt : mstar < mb) (hcont : ContinuousOn h (Set.Ioi 0)) (hanti : StrictAntiOn h (Set.Ioi 0))
    (hstar : h mstar = 1) (hbar : lam * (1 - h mb) = 1) (k : ℕ) :
    (phiMap lam h)^[k] (backOrbit lam h mstar mb k) = mstar ∧
      (phiMap lam h)^[k + 1] (backOrbit lam h mstar mb k) = 0 := by
  have hspec := backOrbit_spec hlam hms hlt hcont hanti hstar hbar
  have h1 : ∀ k, (phiMap lam h)^[k] (backOrbit lam h mstar mb k) = mstar := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply, (hspec k).2.1, ih]
  refine ⟨h1 k, ?_⟩
  rw [Function.iterate_succ_apply', h1 k]
  simp [phiMap, hstar]

/-- **Uniqueness of the initial price level for each collapse date** (O&R Fig. 8.3): if an
initial real balance `x ∈ [m*, m̄]` keeps the orbit in `[m*, m̄]` and reaches `m*` after exactly
`k` periods, then `x = b_k`. -/
theorem backOrbit_unique {lam mstar mb : ℝ} {h : ℝ → ℝ} (hlam : 0 < lam) (hms : 0 < mstar)
    (hlt : mstar < mb) (hcont : ContinuousOn h (Set.Ioi 0)) (hanti : StrictAntiOn h (Set.Ioi 0))
    (hstar : h mstar = 1) (hbar : lam * (1 - h mb) = 1) (k : ℕ) :
    ∀ x, (∀ j, j ≤ k → (phiMap lam h)^[j] x ∈ Set.Icc mstar mb) →
      (phiMap lam h)^[k] x = mstar → x = backOrbit lam h mstar mb k := by
  have hspec := backOrbit_spec hlam hms hlt hcont hanti hstar hbar
  have hmono := phiMap_strictMonoOn hlam hms hanti hstar
  induction k with
  | zero => intro x _ hx; simpa [backOrbit] using hx
  | succ k ih =>
    intro x hin hx
    have h1 : phiMap lam h x = backOrbit lam h mstar mb k := by
      refine ih (phiMap lam h x) (fun j hj => ?_) ?_
      · have := hin (j + 1) (by omega)
        rwa [Function.iterate_succ_apply] at this
      · rwa [Function.iterate_succ_apply] at hx
    have hx0 := hin 0 (Nat.zero_le _)
    simp only [Function.iterate_zero, id] at hx0
    exact hmono.injOn hx0.1 ((hspec (k + 1)).1.1)
      (h1.trans ((hspec k).2.1).symm)

/-- **`m_0^{(T)} ↑ m̄`** (O&R Fig. 8.3: the later the collapse date, the closer the initial price
level to the steady state): the backward orbit converges to the steady state `m̄`. -/
theorem backOrbit_tendsto {lam mstar mb : ℝ} {h : ℝ → ℝ} (hlam : 0 < lam) (hms : 0 < mstar)
    (hlt : mstar < mb) (hcont : ContinuousOn h (Set.Ioi 0)) (hanti : StrictAntiOn h (Set.Ioi 0))
    (hstar : h mstar = 1) (hbar : lam * (1 - h mb) = 1) :
    Tendsto (backOrbit lam h mstar mb) atTop (𝓝 mb) := by
  have hspec := backOrbit_spec hlam hms hlt hcont hanti hstar hbar
  set b := backOrbit lam h mstar mb with hb
  have hmono : Monotone b := monotone_nat_of_le_succ fun k => (hspec k).2.2.le
  have hbdd : BddAbove (Set.range b) := ⟨mb, by rintro _ ⟨k, rfl⟩; exact (hspec k).1.2.le⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ k, b k with hL
  have hLle : L ≤ mb := ciSup_le fun k => (hspec k).1.2.le
  have hLge : mstar ≤ L := (hspec 0).1.1.trans (le_ciSup hbdd 0)
  have hL0 : 0 < L := lt_of_lt_of_le hms hLge
  -- `φ(b_{k+1}) = b_k` passes to the limit: `φ(L) = L`
  have hcφ : ContinuousAt (phiMap lam h) L := by
    have : ContinuousAt h L := hcont.continuousAt (Ioi_mem_nhds hL0)
    exact ((continuousAt_const.mul continuousAt_id).mul (continuousAt_const.sub this))
  have h1 : Tendsto (fun k => phiMap lam h (b (k + 1))) atTop (𝓝 (phiMap lam h L)) :=
    hcφ.tendsto.comp ((tendsto_add_atTop_iff_nat 1).2 hlim)
  have h2 : Tendsto (fun k => phiMap lam h (b (k + 1))) atTop (𝓝 L) :=
    hlim.congr fun k => ((hspec k).2.1).symm
  have hfix : phiMap lam h L = L := tendsto_nhds_unique h1 h2
  have hhL : h L = h mb := by
    unfold phiMap at hfix
    have : lam * (1 - h L) = 1 := by
      have := mul_right_cancel₀ hL0.ne' (by linarith : lam * (1 - h L) * L = 1 * L)
      linarith
    have := mul_left_cancel₀ hlam.ne' (show lam * (1 - h L) = lam * (1 - h mb) by linarith)
    linarith
  have : L = mb := hanti.injOn hL0 (lt_trans hms hlt) hhL
  rwa [this] at hlim

/-- **Asymptotic hyperinflation and fractional backing** (O&R §8.3.5.4–8.3.5.5, made precise):
with `h = C̄v'` continuous and strictly decreasing and the steady state `λ(1 − h(m̄)) = 1`, every
solution of (46) that stays positive and starts below `m̄` is strictly decreasing and
converges to zero. In particular it falls below any floor `M̄/P^MIN > 0` in finite time, so a
credible floor rules out every hyperinflationary path. -/
theorem hyperinflation_tendsto_zero {lam mb : ℝ} {h : ℝ → ℝ} {m : ℕ → ℝ} (hlam : 0 < lam)
    (hmb : 0 < mb) (hcont : ContinuousOn h (Set.Ioi 0)) (hanti : StrictAntiOn h (Set.Ioi 0))
    (hbar : lam * (1 - h mb) = 1) (hpos : ∀ t, 0 < m t)
    (hdyn : ∀ t, m (t + 1) = phiMap lam h (m t)) (hm0 : m 0 < mb) :
    StrictAnti m ∧ Tendsto m atTop (𝓝 0) := by
  have hdec : ∀ t, m t < mb → m (t + 1) < m t := by
    intro t ht
    have h1 : h mb < h (m t) := hanti (hpos t) hmb ht
    rw [hdyn t]
    unfold phiMap
    have e : lam * (1 - h (m t)) = 1 - lam * (h (m t) - h mb) := by linear_combination hbar
    have e2 : 0 < lam * (h (m t) - h mb) := mul_pos hlam (by linarith)
    have e3 : lam * (1 - h (m t)) < 1 := by linarith
    have := hpos t
    calc lam * m t * (1 - h (m t)) = m t * (lam * (1 - h (m t))) := by ring
      _ < m t * 1 := mul_lt_mul_of_pos_left e3 this
      _ = m t := mul_one _
  have hbelow : ∀ t, m t < mb := by
    intro t
    induction t with
    | zero => exact hm0
    | succ t ih => exact (hdec t ih).trans ih
  have hanti' : StrictAnti m := strictAnti_nat_of_succ_lt fun t => hdec t (hbelow t)
  refine ⟨hanti', ?_⟩
  have hbdd : BddBelow (Set.range m) := ⟨0, by rintro _ ⟨t, rfl⟩; exact (hpos t).le⟩
  have hlim := tendsto_atTop_ciInf hanti'.antitone hbdd
  set L := ⨅ t, m t with hL
  have hL0 : 0 ≤ L := le_ciInf fun t => (hpos t).le
  rcases hL0.lt_or_eq with hLpos | hLz
  · exfalso
    have hcφ : ContinuousAt (phiMap lam h) L := by
      have : ContinuousAt h L := hcont.continuousAt (Ioi_mem_nhds hLpos)
      exact ((continuousAt_const.mul continuousAt_id).mul (continuousAt_const.sub this))
    have h1 : Tendsto (fun t => phiMap lam h (m t)) atTop (𝓝 (phiMap lam h L)) :=
      hcφ.tendsto.comp hlim
    have h2 : Tendsto (fun t => phiMap lam h (m t)) atTop (𝓝 L) :=
      ((tendsto_add_atTop_iff_nat 1).2 hlim).congr fun t => hdyn t
    have hfix : phiMap lam h L = L := tendsto_nhds_unique h1 h2
    have hhL : h L = h mb := by
      unfold phiMap at hfix
      have : lam * (1 - h L) = 1 := by
        have := mul_right_cancel₀ hLpos.ne' (by linarith : lam * (1 - h L) * L = 1 * L)
        linarith
      have := mul_left_cancel₀ hlam.ne' (show lam * (1 - h L) = lam * (1 - h mb) by linarith)
      linarith
    have hLm : L = mb := hanti.injOn hLpos hmb hhL
    have : L ≤ m 0 := ciInf_le hbdd 0
    linarith
  · rw [← hLz] at hlim
    exact hlim

/-- **A credible floor on the value of money rules out hyperinflation** (O&R §8.3.5.5): under the
assumptions of `hyperinflation_tendsto_zero`, for every floor `m_min > 0` there is a date at
which real balances fall below it. -/
theorem backing_rules_out_hyperinflation {lam mb mmin : ℝ} {h : ℝ → ℝ} {m : ℕ → ℝ}
    (hlam : 0 < lam) (hmb : 0 < mb) (hcont : ContinuousOn h (Set.Ioi 0))
    (hanti : StrictAntiOn h (Set.Ioi 0)) (hbar : lam * (1 - h mb) = 1) (hpos : ∀ t, 0 < m t)
    (hdyn : ∀ t, m (t + 1) = phiMap lam h (m t)) (hm0 : m 0 < mb) (hmin : 0 < mmin) :
    ∃ T, m T < mmin :=
  ((hyperinflation_tendsto_zero hlam hmb hcont hanti hbar hpos hdyn hm0).2.eventually
    (gt_mem_nhds hmin)).exists

/-- **Hyperinflation without a collapse date** (O&R pp. 543–544, the case the book omits): if
`h = C̄v' < 1` everywhere (e.g. `C̄v'(0+) < 1`), there is no `m*`, and every initial real balance
`0 < m_0 < m̄` generates a positive path that falls to zero asymptotically, with no finite date
at which money becomes worthless. -/
theorem hyperinflation_asymptotic {lam mb m0 : ℝ} {h : ℝ → ℝ} (hlam : 0 < lam) (hmb : 0 < mb)
    (hcont : ContinuousOn h (Set.Ioi 0)) (hanti : StrictAntiOn h (Set.Ioi 0))
    (hbar : lam * (1 - h mb) = 1) (hlt1 : ∀ x, 0 < x → h x < 1) (hm00 : 0 < m0)
    (hm0 : m0 < mb) :
    ∃ m : ℕ → ℝ, m 0 = m0 ∧ (∀ t, m (t + 1) = phiMap lam h (m t)) ∧ (∀ t, 0 < m t) ∧
      StrictAnti m ∧ Tendsto m atTop (𝓝 0) := by
  set m : ℕ → ℝ := fun t => (phiMap lam h)^[t] m0 with hm
  have hdyn : ∀ t, m (t + 1) = phiMap lam h (m t) := fun t => by
    simp only [hm]; rw [Function.iterate_succ_apply']
  have hpos : ∀ t, 0 < m t := by
    intro t
    induction t with
    | zero => simpa [hm] using hm00
    | succ t ih =>
      rw [hdyn t]
      unfold phiMap
      have := hlt1 _ ih
      have : 0 < 1 - h (m t) := by linarith
      positivity
  obtain ⟨h1, h2⟩ := hyperinflation_tendsto_zero hlam hmb hcont hanti hbar hpos hdyn
    (by simpa [hm] using hm0)
  exact ⟨m, by simp [hm], hdyn, hpos, h1, h2⟩

/-- **Utility is finite along paths on which `v` stays bounded** (O&R p. 545: finite utility of
the barter limit requires `v(0+) > −∞`): if `L ≤ v(m_t) ≤ U` for all `t` and `0 ≤ β < 1`, then
`Σβ^t(log C̄ + v(m_t))` converges. -/
theorem utility_summable_of_bounded {β Cbar L U : ℝ} {v : ℝ → ℝ} {m : ℕ → ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hL : ∀ t, L ≤ v (m t)) (hU : ∀ t, v (m t) ≤ U) :
    Summable (fun t => β ^ t * (Real.log Cbar + v (m t))) := by
  refine Summable.of_norm_bounded (g := fun t => (|Real.log Cbar| + |L| + |U|) * β ^ t)
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_left _) fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hβ0 t)
  have h1 := hL t
  have h2 := hU t
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log Cbar), neg_abs_le L, abs_nonneg U]
  · linarith [le_abs_self (Real.log Cbar), le_abs_self U, abs_nonneg L]

/-! ## Exercise 2: transactions technologies instead of money in the utility function -/

/-- Wealth when the period expenditure needed to finance consumption `C` with real balances `m`
is `E_s(C, m)` (Exercise 2, O&R pp. 599–600): `A_{s+1} = (1+r)(A_s + y_s − E_s(C_s, m_s))`. -/
noncomputable def wealthE (r A0 : ℝ) (y : ℕ → ℝ) (E : ℕ → ℝ → ℝ → ℝ) (C m : ℕ → ℝ) : ℕ → ℝ
  | 0 => A0
  | s + 1 => (1 + r) * (wealthE r A0 y E C m s + y s - E s (C s) (m s))

/-- An admissible plan in the transactions-technology model: positive consumption and real
balances, summable utility `Σβ^s u(C_s)` (O&R Exercise 2's (33) replacement) and no Ponzi
scheme. -/
def AdmissibleE (u : ℝ → ℝ) (β r A0 : ℝ) (y : ℕ → ℝ) (E : ℕ → ℝ → ℝ → ℝ) (C m : ℕ → ℝ) :
    Prop :=
  (∀ s, 0 < C s) ∧ (∀ s, 0 < m s) ∧ Summable (fun s => β ^ s * u (C s)) ∧
    NoPonzi r (wealthE r A0 y E C m)

/-- An optimal plan in the transactions-technology model (Exercise 2).
Context: O&R §8.3.5, pp. 538–546. -/
def IsOptimalE (u : ℝ → ℝ) (β r A0 : ℝ) (y : ℕ → ℝ) (E : ℕ → ℝ → ℝ → ℝ) (C m : ℕ → ℝ) :
    Prop :=
  AdmissibleE u β r A0 y E C m ∧ ∀ C' m', AdmissibleE u β r A0 y E C' m' →
    ∑' s, β ^ s * u (C' s) ≤ ∑' s, β ^ s * u (C s)

/-- **Finite perturbations of an optimal plan** (the tool for Exercise 2's first-order
conditions): if a family of plans differs from the optimum only on a finite set `S` of dates,
leaves the wealth path unchanged from some date on, and stays positive for small `ε`, then the
utility of the perturbed dates has a local maximum at `ε = 0`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem localMax_of_optimalE {u : ℝ → ℝ} {β r A0 : ℝ} {y : ℕ → ℝ} {E : ℕ → ℝ → ℝ → ℝ}
    {C m : ℕ → ℝ} (hopt : IsOptimalE u β r A0 y E C m) (S : Finset ℕ) (DC Dm : ℝ → ℕ → ℝ)
    (hoffC : ∀ ε t, t ∉ S → DC ε t = C t)
    (h0 : ∀ t, t ∈ S → DC 0 t = C t)
    (hgood : ∀ᶠ ε in 𝓝 (0 : ℝ), (∀ t, 0 < DC ε t) ∧ (∀ t, 0 < Dm ε t) ∧
      ∀ᶠ T in atTop, wealthE r A0 y E (DC ε) (Dm ε) T = wealthE r A0 y E C m T) :
    IsLocalMax (fun ε => ∑ t ∈ S, β ^ t * u (DC ε t)) 0 := by
  obtain ⟨⟨_, _, hsum, hnp⟩, hmax⟩ := hopt
  filter_upwards [hgood] with ε ⟨hC, hm, hw⟩
  obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hsum S (g := fun t => β ^ t * u (DC ε t))
    fun t ht => by simp only [hoffC ε t ht]
  have hadm : AdmissibleE u β r A0 y E (DC ε) (Dm ε) :=
    ⟨hC, hm, h1, noPonzi_congr hnp hw⟩
  have hle := hmax _ _ hadm
  rw [h2, Finset.sum_sub_distrib] at hle
  have : ∑ t ∈ S, β ^ t * u (DC 0 t) = ∑ t ∈ S, β ^ t * u (C t) :=
    Finset.sum_congr rfl fun t ht => by rw [h0 t ht]
  linarith

/-- Plans agreeing before date `k` have the same wealth at `k` (Exercise 2).
Context: O&R §8.3.5, pp. 538–546. -/
theorem wealthE_congr_before {r A0 : ℝ} {y : ℕ → ℝ} {E : ℕ → ℝ → ℝ → ℝ} {C m C' m' : ℕ → ℝ}
    {k : ℕ} (hC : ∀ t, t < k → C t = C' t) (hm : ∀ t, t < k → m t = m' t) :
    wealthE r A0 y E C m k = wealthE r A0 y E C' m' k := by
  have key : ∀ n, n ≤ k → wealthE r A0 y E C m n = wealthE r A0 y E C' m' n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      simp only [wealthE]
      rw [ih (by omega), hC n (by omega), hm n (by omega)]
  exact key k le_rfl

/-- Plans with the same period expenditure have the same wealth (Exercise 2).
Context: O&R §8.3.5, pp. 538–546. -/
theorem wealthE_congr_expenditure {r A0 : ℝ} {y : ℕ → ℝ} {E : ℕ → ℝ → ℝ → ℝ}
    {C m C' m' : ℕ → ℝ} (h : ∀ t, E t (C' t) (m' t) = E t (C t) (m t)) (T : ℕ) :
    wealthE r A0 y E C' m' T = wealthE r A0 y E C m T := by
  induction T with
  | zero => rfl
  | succ T ih => simp only [wealthE]; rw [ih, h T]

/-- Plans that agree from date `k` on, with equal wealth at `k`, have equal wealth afterwards.
Context: O&R §8.3.5, pp. 538–546. -/
theorem wealthE_congr_after {r A0 : ℝ} {y : ℕ → ℝ} {E : ℕ → ℝ → ℝ → ℝ} {C m C' m' : ℕ → ℝ}
    {k : ℕ} (hk : wealthE r A0 y E C m k = wealthE r A0 y E C' m' k)
    (hC : ∀ s, k ≤ s → C s = C' s) (hm : ∀ s, k ≤ s → m s = m' s) (n : ℕ) :
    wealthE r A0 y E C m (k + n) = wealthE r A0 y E C' m' (k + n) := by
  induction n with
  | zero => exact hk
  | succ n ih =>
    rw [← add_assoc]
    simp only [wealthE]
    rw [ih, hC _ (by omega), hm _ (by omega)]

/-- **Exercise 2(a), the money first-order condition** (O&R p. 600): with the budget
`B_{t+1} + M_t/P_t = (1+r)B_t + M_{t−1}/P_t + Y g(M_t/P_t) − C_t − T_t`, i.e. period expenditure
`C + ι m − Y g(m)`, at an optimum `Y g'(m_s) = ι_s = i_{s+1}/(1 + i_{s+1})` (given `u' > 0`).
Proof: hold `ε` more real balances and adjust consumption to keep expenditure unchanged. -/
theorem ex2_money_foc {u u' g g' : ℝ → ℝ} {β r A0 Y : ℝ} {y ι C m : ℕ → ℝ} (hβ : 0 < β)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hu' : ∀ c, 0 < c → 0 < u' c)
    (hg : ∀ k, 0 < k → HasDerivAt g (g' k) k)
    (hopt : IsOptimalE u β r A0 y (fun s c k => c + ι s * k - Y * g k) C m) (s : ℕ) :
    Y * g' (m s) = ι s := by
  have hC := hopt.1.1
  have hm := hopt.1.2.1
  set DC : ℝ → ℕ → ℝ := fun ε t =>
    if t = s then C s - ι s * ε + Y * (g (m s + ε) - g (m s)) else C t with hDC
  set Dm : ℝ → ℕ → ℝ := fun ε t => if t = s then m s + ε else m t with hDm
  have hg0 : HasDerivAt g (g' (m s)) (m s + 0) := by rw [add_zero]; exact hg _ (hm s)
  have h1 : HasDerivAt (fun ε => g (m s + ε)) (g' (m s)) 0 := hg0.comp_const_add (m s) 0
  have hcontg : ContinuousAt (fun ε => g (m s + ε)) 0 := h1.continuousAt
  have hev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C s - ι s * ε + Y * (g (m s + ε) - g (m s)) := by
    have hc : ContinuousAt (fun ε => C s - ι s * ε + Y * (g (m s + ε) - g (m s))) 0 :=
      ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).add
        (continuousAt_const.mul (hcontg.sub continuousAt_const)))
    exact hc.eventually (lt_mem_nhds (by simpa using hC s))
  have hev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < m s + ε :=
    ((continuous_const.add continuous_id).continuousAt (x := 0)).eventually
      (lt_mem_nhds (by simpa using hm s))
  have hloc := localMax_of_optimalE hopt {s} DC Dm
    (fun ε t ht => by simp only [Finset.mem_singleton] at ht; simp [hDC, ht])
    (fun t ht => by simp only [Finset.mem_singleton] at ht; subst ht; simp [hDC])
    (by
      filter_upwards [hev1, hev2] with ε h1 h2
      refine ⟨fun t => ?_, fun t => ?_, Filter.Eventually.of_forall fun T =>
        wealthE_congr_expenditure (fun t => ?_) T⟩
      · by_cases ht : t = s
        · subst ht; simpa [hDC] using h1
        · simpa [hDC, ht] using hC t
      · by_cases ht : t = s
        · subst ht; simpa [hDm] using h2
        · simpa [hDm, ht] using hm t
      · by_cases ht : t = s
        · subst ht; simp [hDC, hDm]; ring
        · simp [hDC, hDm, ht])
  simp only [Finset.sum_singleton, hDC, ↓reduceIte] at hloc
  have hin : HasDerivAt (fun ε => C s - ι s * ε + Y * (g (m s + ε) - g (m s)))
      (-ι s + Y * g' (m s)) 0 :=
    (((hasDerivAt_const (0 : ℝ) (C s)).sub ((hasDerivAt_id (0 : ℝ)).const_mul (ι s))).add
      ((h1.sub_const (g (m s))).const_mul Y)).congr_deriv (by ring)
  have hU : HasDerivAt u (u' (C s)) (C s - ι s * 0 + Y * (g (m s + 0) - g (m s))) := by
    simpa using hu _ (hC s)
  have hd := ((hU.comp (0 : ℝ) hin).const_mul (β ^ s))
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hb := pow_pos hβ s
  have hu0 := hu' _ (hC s)
  have : u' (C s) * (-ι s + Y * g' (m s)) = 0 := by
    have := (mul_eq_zero.1 h0).resolve_left hb.ne'
    linarith
  have := (mul_eq_zero.1 this).resolve_left hu0.ne'
  linarith

/-- **Exercise 2(a) and 2(c), the consumption Euler equation** (O&R p. 600): if period
expenditure is `C w_s(m) + F_s(m)` with `w > 0` (`w = 1` in part (a), `w = 1/g(m)` in part (c)),
then at an optimum `u'(C_s)/w_s = (1+r)β u'(C_{s+1})/w_{s+1}`. Proof: spend `ε` less at `s` and
`(1+r)ε` more at `s + 1`. -/
theorem euler_of_optimalE {u u' : ℝ → ℝ} {β r A0 : ℝ} {y : ℕ → ℝ} {w F : ℕ → ℝ → ℝ}
    {C m : ℕ → ℝ} (hβ : 0 < β) (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hw : ∀ s, 0 < w s (m s))
    (hopt : IsOptimalE u β r A0 y (fun s c k => c * w s k + F s k) C m) (s : ℕ) :
    u' (C s) / w s (m s) = (1 + r) * β * (u' (C (s + 1)) / w (s + 1) (m (s + 1))) := by
  have hC := hopt.1.1
  set a := (w s (m s))⁻¹ with ha
  set b := (1 + r) * (w (s + 1) (m (s + 1)))⁻¹ with hb
  set DC : ℝ → ℕ → ℝ := fun ε t =>
    if t = s then C s + ε * (-a) else if t = s + 1 then C (s + 1) + ε * b else C t with hDC
  have hne : s + 1 ≠ s := Nat.succ_ne_self s
  have hDs : ∀ ε, DC ε s = C s + ε * (-a) := fun ε => by simp [hDC]
  have hDs1 : ∀ ε, DC ε (s + 1) = C (s + 1) + ε * b := fun ε => by simp [hDC]
  have hoff : ∀ ε t, t ∉ ({s, s + 1} : Finset ℕ) → DC ε t = C t := fun ε t ht => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    simp [hDC, ht.1, ht.2]
  have hwe : ∀ ε n, wealthE r A0 y (fun s c k => c * w s k + F s k) (DC ε) m (s + 2 + n) =
      wealthE r A0 y (fun s c k => c * w s k + F s k) C m (s + 2 + n) := by
    intro ε n
    refine wealthE_congr_after ?_ (fun t ht => hoff ε t (by simp; omega)) (fun _ _ => rfl) n
    have hbef : wealthE r A0 y (fun s c k => c * w s k + F s k) (DC ε) m s =
        wealthE r A0 y (fun s c k => c * w s k + F s k) C m s :=
      wealthE_congr_before (fun t ht => hoff ε t (by simp; omega)) (fun _ _ => rfl)
    rw [show s + 2 = s + 1 + 1 by ring]
    simp only [wealthE]
    rw [hbef, hDs, hDs1]
    have h1 := (hw s).ne'
    have h2 := (hw (s + 1)).ne'
    rw [ha, hb]
    field_simp
    ring
  have hev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C s + ε * (-a) :=
    ((by fun_prop : Continuous fun ε : ℝ => C s + ε * (-a)).tendsto 0).eventually
      (lt_mem_nhds (by simpa using hC s))
  have hev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C (s + 1) + ε * b :=
    ((by fun_prop : Continuous fun ε : ℝ => C (s + 1) + ε * b).tendsto 0).eventually
      (lt_mem_nhds (by simpa using hC (s + 1)))
  have hloc := localMax_of_optimalE hopt {s, s + 1} DC (fun _ => m) hoff
    (fun t ht => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · rw [hDs]; ring
      · rw [hDs1]; ring)
    (by
      filter_upwards [hev1, hev2] with ε h1 h2
      refine ⟨fun t => ?_, hopt.1.2.1, ?_⟩
      · by_cases ht : t = s
        · rw [ht, hDs]; exact h1
        by_cases ht1 : t = s + 1
        · rw [ht1, hDs1]; exact h2
        rw [hoff ε t (by simp [ht, ht1])]
        exact hC t
      · filter_upwards [eventually_ge_atTop (s + 2)] with T hT
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
        exact hwe ε n)
  simp only [Finset.sum_pair hne.symm, hDs, hDs1] at hloc
  have hA : HasDerivAt (fun ε => β ^ s * u (C s + ε * (-a))) (β ^ s * (u' (C s) * (-a))) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => C s + ε * (-a)) (-a) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (-a)).const_add (C s)
    have h2 : HasDerivAt u (u' (C s)) (C s + 0 * (-a)) := by simpa using hu _ (hC s)
    exact (h2.comp (0 : ℝ) h1).const_mul _
  have hB : HasDerivAt (fun ε => β ^ (s + 1) * u (C (s + 1) + ε * b))
      (β ^ (s + 1) * (u' (C (s + 1)) * b)) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => C (s + 1) + ε * b) b 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add (C (s + 1))
    have h2 : HasDerivAt u (u' (C (s + 1))) (C (s + 1) + 0 * b) := by
      simpa using hu _ (hC (s + 1))
    exact (h2.comp (0 : ℝ) h1).const_mul _
  have h0 := hloc.hasDerivAt_eq_zero (hA.add hB)
  rw [pow_succ] at h0
  have hβs : 0 < β ^ s := pow_pos hβ s
  have h3 : β ^ s * (u' (C s) * a - (1 + r) * β * (u' (C (s + 1)) *
      (w (s + 1) (m (s + 1)))⁻¹)) = 0 := by
    rw [hb] at h0; linarith
  have := (mul_eq_zero.1 h3).resolve_left hβs.ne'
  rw [ha] at this
  simp only [div_eq_mul_inv]
  linarith

/-- **Exercise 2(c), the money first-order condition** (O&R p. 600, "don't expect a neat
solution"): with `P_t C_t = X_t g(M_t/P_t)`, real expenditure is `C/g(m) + ι m`, and at an
optimum `ι_s g(m_s)² = g'(m_s) C_s`, i.e. `i/(1+i) = C g'(m)/g(m)²`. -/
theorem ex2c_money_foc {u u' g g' : ℝ → ℝ} {β r A0 : ℝ} {y ι C m : ℕ → ℝ} (hβ : 0 < β)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hu' : ∀ c, 0 < c → 0 < u' c)
    (hg : ∀ k, 0 < k → HasDerivAt g (g' k) k) (hgpos : ∀ k, 0 < k → 0 < g k)
    (hopt : IsOptimalE u β r A0 y (fun s c k => c / g k + ι s * k) C m) (s : ℕ) :
    ι s * g (m s) ^ 2 = g' (m s) * C s := by
  have hC := hopt.1.1
  have hm := hopt.1.2.1
  have hgs := hgpos _ (hm s)
  set K := C s / g (m s) with hK
  set DC : ℝ → ℕ → ℝ := fun ε t =>
    if t = s then g (m s + ε) * (K - ι s * ε) else C t with hDC
  set Dm : ℝ → ℕ → ℝ := fun ε t => if t = s then m s + ε else m t with hDm
  have hg0 : HasDerivAt g (g' (m s)) (m s + 0) := by rw [add_zero]; exact hg _ (hm s)
  have h1 : HasDerivAt (fun ε => g (m s + ε)) (g' (m s)) 0 := hg0.comp_const_add (m s) 0
  have hin : HasDerivAt (fun ε => g (m s + ε) * (K - ι s * ε))
      (g' (m s) * K - g (m s) * ι s) 0 := by
    have h2 : HasDerivAt (fun ε : ℝ => K - ι s * ε) (-ι s) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (ι s)).const_sub K
    exact (h1.mul h2).congr_deriv (by simp; ring)
  have hev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < g (m s + ε) * (K - ι s * ε) :=
    hin.continuousAt.eventually (lt_mem_nhds (by
      simp only [add_zero, mul_zero, sub_zero, hK]; field_simp; exact hC s))
  have hev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < m s + ε :=
    ((continuous_const.add continuous_id).continuousAt (x := 0)).eventually
      (lt_mem_nhds (by simpa using hm s))
  have hloc := localMax_of_optimalE hopt {s} DC Dm
    (fun ε t ht => by simp only [Finset.mem_singleton] at ht; simp [hDC, ht])
    (fun t ht => by
      simp only [Finset.mem_singleton] at ht; subst ht
      simp only [hDC, ↓reduceIte, add_zero, mul_zero, sub_zero, hK]; field_simp)
    (by
      filter_upwards [hev1, hev2] with ε h1 h2
      refine ⟨fun t => ?_, fun t => ?_, Filter.Eventually.of_forall fun T =>
        wealthE_congr_expenditure (fun t => ?_) T⟩
      · by_cases ht : t = s
        · subst ht; simpa [hDC] using h1
        · simpa [hDC, ht] using hC t
      · by_cases ht : t = s
        · subst ht; simpa [hDm] using h2
        · simpa [hDm, ht] using hm t
      · by_cases ht : t = s
        · subst ht
          have := (hgpos _ h2).ne'
          simp only [hDC, hDm, ↓reduceIte, hK]
          field_simp
          ring
        · simp [hDC, hDm, ht])
  simp only [Finset.sum_singleton, hDC, ↓reduceIte] at hloc
  have hU : HasDerivAt u (u' (C s)) (g (m s + 0) * (K - ι s * 0)) := by
    have : g (m s + 0) * (K - ι s * 0) = C s := by
      simp only [add_zero, mul_zero, sub_zero, hK]; field_simp
    rw [this]; exact hu _ (hC s)
  have h0 := hloc.hasDerivAt_eq_zero ((hU.comp (0 : ℝ) hin).const_mul (β ^ s))
  have hb := pow_pos hβ s
  have hu0 := hu' _ (hC s)
  have h3 : u' (C s) * (g' (m s) * K - g (m s) * ι s) = 0 :=
    (mul_eq_zero.1 h0).resolve_left hb.ne'
  have h4 := (mul_eq_zero.1 h3).resolve_left hu0.ne'
  rw [hK] at h4
  field_simp at h4
  linarith

/-- **Exercise 2(b): constant consumption** (O&R p. 600): with `(1+r)β = 1` and `u'` strictly
decreasing, the Euler equation of part (a) forces `C_s = C_0` for all `s`. -/
theorem ex2_constant_consumption {u' : ℝ → ℝ} {β r : ℝ} {C : ℕ → ℝ} (hβr : (1 + r) * β = 1)
    (hC : ∀ s, 0 < C s) (hanti : StrictAntiOn u' (Set.Ioi 0))
    (he : ∀ s, u' (C s) / 1 = (1 + r) * β * (u' (C (s + 1)) / 1)) (s : ℕ) : C s = C 0 := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have h := he s
    rw [hβr, one_mul, div_one, div_one] at h
    rw [← ih]
    exact (hanti.injOn (hC (s + 1)) (hC s) h.symm)

/-- **Exercise 2(b): the dynamics of real balances** (O&R p. 600): with `(1+r)β = 1` and money
growing at `1 + μ`, the money condition `Y g'(m_s) = ι_s` of part (a) is
`(β/(1+μ)) m_{s+1} = m_s (1 − Y g'(m_s))` — (46) with `C̄v'` replaced by `Yg'`. -/
theorem ex2_dynamics_iff {g' : ℝ → ℝ} {β r μ Y : ℝ} {N P : ℕ → ℝ} (hβr : (1 + r) * β = 1)
    (hμ : 0 < 1 + μ) (hN : ∀ s, 0 < N s) (hP : ∀ s, 0 < P s)
    (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s) (s : ℕ) :
    Y * g' (N (s + 1) / P s) = userCost r P s ↔
      β / (1 + μ) * (N (s + 1 + 1) / P (s + 1)) =
        N (s + 1) / P s * (1 - Y * g' (N (s + 1) / P s)) := by
  rw [userCost_of_beta hβr]
  exact bubble_dynamics_iff (h := fun k => Y * g' k) hμ hN hP hgrowth s

/-- **Exercise 2(b): the no-bubble path** (O&R p. 600): if `Y g'(m̄) = 1 − β/(1+μ)`, the price
level `P_s = N_{s+1}/m̄` (inflation `μ`) satisfies the money condition at every date, and `m̄` is
the unique such level when `g'` is strictly decreasing. -/
theorem ex2_steady_state {g' : ℝ → ℝ} {β r μ Y mb : ℝ} {N : ℕ → ℝ} (hβr : (1 + r) * β = 1)
    (hμ : 0 < 1 + μ) (hN : ∀ s, 0 < N s) (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s)
    (hmb : 0 < mb) (hss : Y * g' mb = 1 - β / (1 + μ)) :
    (∀ s, Y * g' (N (s + 1) / (N (s + 1) / mb)) = userCost r (fun s => N (s + 1) / mb) s) ∧
    (∀ s, N (s + 1 + 1) / mb = (1 + μ) * (N (s + 1) / mb)) ∧
    (StrictAntiOn (fun k => Y * g' k) (Set.Ioi 0) →
      ∀ m', 0 < m' → Y * g' m' = 1 - β / (1 + μ) → m' = mb) := by
  refine ⟨fun s => ?_, fun s => by rw [hgrowth (s + 1)]; ring, fun hanti m' hm' h => ?_⟩
  · have h1 := (hN (s + 1)).ne'
    have h2 := (hN (s + 1 + 1)).ne'
    rw [userCost_of_beta hβr, show N (s + 1) / (N (s + 1) / mb) = mb by field_simp, hss,
      hgrowth (s + 1)]
    field_simp
  · exact hanti.injOn hm' hmb (h.trans hss.symm)

/-- **Exercise 2(d), deflations are ruled out** (O&R p. 600, `μ = 0`): if the transactions
technology `g` is concave, nondecreasing and bounded above (`g → 1`), the individual TVC fails
along every positive deflationary path of `β m_{t+1} = m_t(1 − Y g'(m_t))`
(`bounded_rules_out_deflation` with `C̄v'` replaced by `Yg'`). -/
theorem ex2_no_deflation {β Y V : ℝ} {g g' : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hY : 0 < Y)
    (hpos : ∀ t, 0 < m t) (hdyn : ∀ t, β * m (t + 1) = m t * (1 - Y * g' (m t)))
    (hg : ConcaveOn ℝ (Set.Ioi 0) g) (hg' : ∀ k, 0 < k → HasDerivAt g (g' k) k)
    (hnn : ∀ k, 0 < k → 0 ≤ g' k) (hV : ∀ k, 0 < k → g k ≤ V)
    (hm0 : Y * g' (m 0) < 1 - β) : ¬ BubbleTVC β m := by
  have hanti : AntitoneOn (fun k => Y * g' k) (Set.Ioi 0) := by
    intro x hx y hy hxy
    rcases hxy.lt_or_eq with hlt | heq
    · have h1 := hg.slope_le_of_hasDerivAt hx hy hlt (hg' x hx)
      have h2 := hg.le_slope_of_hasDerivAt hx hy hlt (hg' y hy)
      exact mul_le_mul_of_nonneg_left (h2.trans h1) hY.le
    · rw [heq]
  exact bounded_rules_out_deflation hβ hY hpos hdyn hg hg' hanti hnn hV hm0

/-- **Exercise 2(d), hyperinflations cannot be ruled out** (O&R p. 600): since `g ≥ 0`
(so `g(0+) > −∞`), condition (52) holds, `m g'(m) → 0` as `m → 0` (`fn34_sharpened`), which is
exactly what allows speculative hyperinflations in Figure 8.3. -/
theorem ex2_hyperinflation_possible {g g' : ℝ → ℝ} (hg : ConcaveOn ℝ (Set.Ioi 0) g)
    (hg' : ∀ k, 0 < k → HasDerivAt g (g' k) k) (hnn : ∀ k, 0 < k → 0 ≤ g' k)
    (hg0 : ∀ k, 0 < k → 0 ≤ g k) : Tendsto (fun x => x * g' x) (𝓝[>] 0) (𝓝 0) :=
  fn34_sharpened hg hg' hnn hg0

/-- **`equilibrium_iff` without a summability hypothesis, `v` bounded along the path** (O&R
§8.3.5): if `L ≤ v(m_s) ≤ U` for all `s` (e.g. `v` bounded below with real balances bounded
above), lifetime utility is automatically finite and the equilibrium characterisation holds. -/
theorem equilibrium_iff_of_bounded {v v' : ℝ → ℝ} {β r μ Ybar B0 L Ub : ℝ} {N P : ℕ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hβr : (1 + r) * β = 1) (hμ : 0 < 1 + μ)
    (hC : 0 < Ybar + r * B0) (hN : ∀ s, 0 < N s) (hP : ∀ s, 0 < P s)
    (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s) (hv : ConcaveOn ℝ (Set.Ioi 0) v)
    (hv' : ∀ k, 0 < k → HasDerivAt v (v' k) k) (hL : ∀ s, L ≤ v (N (s + 1) / P s))
    (hU : ∀ s, v (N (s + 1) / P s) ≤ Ub) :
    IsOptimal (fun c k => Real.log c + v k) β r ((1 + r) * B0 + N 0 / P 0)
        (fun s => Ybar + (N (s + 1) - N s) / P s) (userCost r P) (fun _ => Ybar + r * B0)
        (fun s => N (s + 1) / P s) ↔
      (∀ s, β / (1 + μ) * (N (s + 1 + 1) / P (s + 1)) =
        N (s + 1) / P s * (1 - (Ybar + r * B0) * v' (N (s + 1) / P s))) ∧
      BubbleTVC β (fun s => N (s + 1) / P s) :=
  equilibrium_iff hβ0 hβ1 hβr hμ hC hN hP hgrowth hv hv'
    (utility_summable_of_bounded (m := fun s => N (s + 1) / P s) hβ0.le hβ1 hL hU)

/-- **`equilibrium_iff` for real balances bounded away from zero and above** (O&R §8.3.5): with
`v` nondecreasing and `0 < m_lo ≤ m_s ≤ m_hi`, no summability hypothesis is needed. -/
theorem equilibrium_iff_of_balances_bounded {v v' : ℝ → ℝ} {β r μ Ybar B0 mlo mhi : ℝ}
    {N P : ℕ → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβr : (1 + r) * β = 1) (hμ : 0 < 1 + μ)
    (hC : 0 < Ybar + r * B0) (hN : ∀ s, 0 < N s) (hP : ∀ s, 0 < P s)
    (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s) (hv : ConcaveOn ℝ (Set.Ioi 0) v)
    (hv' : ∀ k, 0 < k → HasDerivAt v (v' k) k) (hmono : MonotoneOn v (Set.Ioi 0))
    (hlo0 : 0 < mlo) (hlo : ∀ s, mlo ≤ N (s + 1) / P s) (hhi : ∀ s, N (s + 1) / P s ≤ mhi) :
    IsOptimal (fun c k => Real.log c + v k) β r ((1 + r) * B0 + N 0 / P 0)
        (fun s => Ybar + (N (s + 1) - N s) / P s) (userCost r P) (fun _ => Ybar + r * B0)
        (fun s => N (s + 1) / P s) ↔
      (∀ s, β / (1 + μ) * (N (s + 1 + 1) / P (s + 1)) =
        N (s + 1) / P s * (1 - (Ybar + r * B0) * v' (N (s + 1) / P s))) ∧
      BubbleTVC β (fun s => N (s + 1) / P s) :=
  equilibrium_iff_of_bounded hβ0 hβ1 hβr hμ hC hN hP hgrowth hv hv' (L := v mlo) (Ub := v mhi)
    (fun s => hmono hlo0 (lt_of_lt_of_le hlo0 (hlo s)) (hlo s))
    (fun s => hmono (lt_of_lt_of_le hlo0 (hlo s)) (lt_of_lt_of_le hlo0 ((hlo s).trans (hhi s)))
      (hhi s))

end ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Cash-in-advance models of money demand

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §8.3.6
(pp. 547–550), Appendix 8A (pp. 595–597), Appendix 8B and §8.7.6.1 (pp. 597–599, 594) and
Exercise 4 (p. 601).

The household maximises `Σβ^s u(C_s)` (57) subject to (34) and the cash-in-advance constraints
(58) `M_{s−1} ≥ P_sC_s`. We allow time-varying real rates (Exercise 4): the bond bought at `s`
pays `R_s = 1 + r_{s+1}`. With `n_s = M_s/P_s` and `ρ_s = P_s/P_{s+1}`, wealth
`A_s = (1+r_s)B_s + M_{s−1}/P_s` obeys `A_{s+1} = R_s(A_s + y_s − C_s − ι_s n_s)`,
`ι_s = 1 − ρ_s/R_s = i_{s+1}/(1+i_{s+1})`. We prove:

* **(a)** with `u` increasing and `i > 0` the constraint binds (`cia_binds`);
* the Euler equation `ρ_s u'(C_{s+1}) = R_s βρ_{s+1} u'(C_{s+2})` DERIVED from optimality, the
  date-0 condition (`C_t` is predetermined), and the necessity of the transversality condition;
* **sufficiency** of these conditions for concave `u` against every no-Ponzi rival, and hence
  an exact characterisation of the optimum (`cia_optimal_iff`);
* (59), constant velocity, **(60) and Exercise 4** (`euler_60_iff`: (60) holds with the
  time-varying `r_{s+1}`), the stationary case, and the undistorted Euler equation under the
  Helpman–Lucas timing;
* Appendix 8A: PPP from the law of one price, (130) (with the optimality of the CES demands),
  (131), `r = (1−β)/β`, and a **sign correction**: the government budget constraints must read
  `T_t = −(ΔM_H + ΔM^*_H)/P_t` (as in (43)); the printed `+` sign is inconsistent with the
  private budgets and market clearing unless total money is constant;
* Appendix 8B's balance-sheet mechanics (sterilised = nonsterilised + open-market sale) and the
  forward-intervention identity of §8.7.6.1 from covered interest parity.
-/

namespace ObstfeldRogoff.MoneyExchangeRates.CashInAdvance

open Real Filter Topology Set
open ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility

/-! ## The household's problem with a cash-in-advance constraint -/

/-- Wealth in the cash-in-advance model with (possibly time-varying) real interest rates
(O&R (34), p. 548, and Exercise 4): `A_s = (1 + r_s)B_s + M_{s−1}/P_s` evolves as
`A_{s+1} = R_s (A_s + y_s − C_s − ι_s n_s)`, where `R_s = 1 + r_{s+1}` is the gross return on a
bond bought at `s`, `n_s = M_s/P_s` the real balances acquired at `s` and
`ι_s = 1 − (P_s/P_{s+1})/R_s` their user cost. -/
noncomputable def ciaWealth (R : ℕ → ℝ) (A0 : ℝ) (y ι C n : ℕ → ℝ) : ℕ → ℝ
  | 0 => A0
  | s + 1 => R s * (ciaWealth R A0 y ι C n s + y s - C s - ι s * n s)

/-- The market discount factor `Π_{j<T} R_j^{−1}` (O&R p. 534, Exercise 4). -/
noncomputable def ciaDisc (R : ℕ → ℝ) (T : ℕ) : ℝ := ∏ j ∈ Finset.range T, (R j)⁻¹

/-- End-of-period financial assets in present value, `Π_{j<T}R_j^{−1}(B_{T+1} + M_T/P_T)`,
the object of the book's transversality condition (O&R p. 534) in the CIA model. -/
noncomputable def ciaAssets (R : ℕ → ℝ) (A0 : ℝ) (y ι C n : ℕ → ℝ) (T : ℕ) : ℝ :=
  ciaDisc R T * (ciaWealth R A0 y ι C n T + y T - C T)

/-- An admissible plan in the CIA model (O&R (57)–(58), p. 548): positive consumption,
nonnegative money, the cash-in-advance constraints `P_0C_0 ≤ M_{−1}` (`C_0 ≤ c₀`) and
`P_{s+1}C_{s+1} ≤ M_s` (`C_{s+1} ≤ ρ_s n_s`, `ρ_s = P_s/P_{s+1}`), summable utility and no Ponzi
scheme (`liminf` of `ciaAssets` at least zero). -/
def CIAAdmissible (u : ℝ → ℝ) (β : ℝ) (R : ℕ → ℝ) (A0 c0 : ℝ) (y ι ρ C n : ℕ → ℝ) : Prop :=
  (∀ s, 0 < C s) ∧ (∀ s, 0 ≤ n s) ∧ C 0 ≤ c0 ∧ (∀ s, C (s + 1) ≤ ρ s * n s) ∧
    Summable (fun s => β ^ s * u (C s)) ∧
    ∀ ε > 0, ∀ᶠ T in atTop, -ε < ciaAssets R A0 y ι C n T

/-- An optimal plan in the CIA model (O&R p. 548). -/
def CIAOptimal (u : ℝ → ℝ) (β : ℝ) (R : ℕ → ℝ) (A0 c0 : ℝ) (y ι ρ C n : ℕ → ℝ) : Prop :=
  CIAAdmissible u β R A0 c0 y ι ρ C n ∧ ∀ C' n', CIAAdmissible u β R A0 c0 y ι ρ C' n' →
    ∑' s, β ^ s * u (C' s) ≤ ∑' s, β ^ s * u (C s)

/-- The transversality condition of the CIA model, in its exact (`liminf ≤ 0`) form.
Context: O&R §8.3.6, pp. 547–550. -/
def CIATransversality (R : ℕ → ℝ) (A0 : ℝ) (y ι C n : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ᶠ T in atTop, ciaAssets R A0 y ι C n T < ε

/-- The law of motion of CIA wealth (O&R (34)). -/
theorem ciaWealth_succ (R : ℕ → ℝ) (A0 : ℝ) (y ι C n : ℕ → ℝ) (s : ℕ) :
    ciaWealth R A0 y ι C n (s + 1) = R s * (ciaWealth R A0 y ι C n s + y s - C s - ι s * n s) :=
  rfl

/-- `Π_{j<T+1} R_j^{−1} = (Π_{j<T} R_j^{−1}) R_T^{−1}`.
Context: O&R §8.3.6, pp. 547–550. -/
theorem ciaDisc_succ (R : ℕ → ℝ) (T : ℕ) : ciaDisc R (T + 1) = ciaDisc R T * (R T)⁻¹ := by
  simp only [ciaDisc, Finset.prod_range_succ]

/-- The discount factor is positive when gross returns are.
Context: O&R §8.3.6, pp. 547–550. -/
theorem ciaDisc_pos {R : ℕ → ℝ} (hR : ∀ s, 0 < R s) (T : ℕ) : 0 < ciaDisc R T :=
  Finset.prod_pos fun j _ => inv_pos.2 (hR j)

/-- **The budget constraint (34) in wealth form with time-varying rates** (O&R p. 548 and
Exercise 4): with `N_s` the money brought into `s` and the bond bought at `s` paying `R_s`,
`B_{s+1} + N_{s+1}/P_s = R_{s−1}B_s + N_s/P_s + Y_s − C_s − T_s` makes
`R_{s−1}B_s + N_s/P_s` equal to `ciaWealth`. -/
theorem ciaWealth_of_budget {R P B N Y T C : ℕ → ℝ} {Rm1 : ℝ} (hR : ∀ s, 0 < R s)
    (hP : ∀ s, 0 < P s)
    (hbud : ∀ s, B (s + 1) + N (s + 1) / P s =
      (if s = 0 then Rm1 else R (s - 1)) * B s + N s / P s + Y s - C s - T s) (s : ℕ) :
    (if s = 0 then Rm1 else R (s - 1)) * B s + N s / P s =
      ciaWealth R (Rm1 * B 0 + N 0 / P 0) (fun s => Y s - T s)
        (fun s => 1 - P s / P (s + 1) / R s) C (fun s => N (s + 1) / P s) s := by
  induction s with
  | zero => simp [ciaWealth]
  | succ s ih =>
    rw [ciaWealth_succ, ← ih]
    have h := hbud s
    have hPs := (hP s).ne'
    have hPs1 := (hP (s + 1)).ne'
    have hRs := (hR s).ne'
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    field_simp
    field_simp at h
    linear_combination R s * P (s + 1) * h

/-- **Finite-horizon present-value identity** in the CIA model:
`Σ_{s<T} D_s(C_s + ι_s n_s) + D_T A_T = A_0 + Σ_{s<T} D_s y_s` (O&R p. 534). -/
theorem cia_pv_identity {R : ℕ → ℝ} (hR : ∀ s, 0 < R s) (A0 : ℝ) (y ι C n : ℕ → ℝ) (T : ℕ) :
    ∑ s ∈ Finset.range T, ciaDisc R s * (C s + ι s * n s) +
        ciaDisc R T * ciaWealth R A0 y ι C n T =
      A0 + ∑ s ∈ Finset.range T, ciaDisc R s * y s := by
  induction T with
  | zero => simp [ciaDisc, ciaWealth]
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ciaWealth_succ, ciaDisc_succ]
    have h1 : (R T)⁻¹ * R T = 1 := inv_mul_cancel₀ (hR T).ne'
    linear_combination ih + ciaDisc R T *
      (ciaWealth R A0 y ι C n T + y T - C T - ι T * n T) * h1

/-- End-of-period assets in terms of next period's wealth:
`D_T(A_T + y_T − C_T) = D_{T+1}A_{T+1} + D_T ι_T n_T` (O&R p. 534). -/
theorem ciaAssets_eq {R : ℕ → ℝ} (hR : ∀ s, 0 < R s) (A0 : ℝ) (y ι C n : ℕ → ℝ) (T : ℕ) :
    ciaAssets R A0 y ι C n T = ciaDisc R (T + 1) * ciaWealth R A0 y ι C n (T + 1) +
      ciaDisc R T * (ι T * n T) := by
  unfold ciaAssets
  rw [ciaWealth_succ, ciaDisc_succ]
  have h1 : (R T)⁻¹ * R T = 1 := inv_mul_cancel₀ (hR T).ne'
  linear_combination (-(ciaDisc R T * (ciaWealth R A0 y ι C n T + y T - C T - ι T * n T))) * h1

/-- Plans agreeing before `k` have the same CIA wealth at `k`.
Context: O&R §8.3.6, pp. 547–550. -/
theorem ciaWealth_congr_before {R : ℕ → ℝ} {A0 : ℝ} {y ι C n C' n' : ℕ → ℝ} {k : ℕ}
    (hC : ∀ t, t < k → C t = C' t) (hn : ∀ t, t < k → n t = n' t) :
    ciaWealth R A0 y ι C n k = ciaWealth R A0 y ι C' n' k := by
  have key : ∀ j, j ≤ k → ciaWealth R A0 y ι C n j = ciaWealth R A0 y ι C' n' j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [ciaWealth_succ, ciaWealth_succ, ih (by omega), hC j (by omega), hn j (by omega)]
  exact key k le_rfl

/-- Plans agreeing from `k` on with equal wealth at `k` have equal wealth afterwards.
Context: O&R §8.3.6, pp. 547–550. -/
theorem ciaWealth_congr_after {R : ℕ → ℝ} {A0 : ℝ} {y ι C n C' n' : ℕ → ℝ} {k : ℕ}
    (hk : ciaWealth R A0 y ι C n k = ciaWealth R A0 y ι C' n' k)
    (hC : ∀ s, k ≤ s → C s = C' s) (hn : ∀ s, k ≤ s → n s = n' s) (j : ℕ) :
    ciaWealth R A0 y ι C n (k + j) = ciaWealth R A0 y ι C' n' (k + j) := by
  induction j with
  | zero => exact hk
  | succ j ih =>
    rw [← add_assoc, ciaWealth_succ, ciaWealth_succ, ih, hC _ (by omega), hn _ (by omega)]

/-- **Finite perturbations of a CIA optimum**: if a family of plans differs from the optimum only
on a finite set `S` of dates and is admissible (with the same assets eventually) for `ε` near
`0` along a filter `l`, then the utility of the perturbed dates does not exceed its value at the
optimum along `l`.
Context: O&R §8.3.6, pp. 547–550. -/
theorem cia_perturb_le {u : ℝ → ℝ} {β : ℝ} {R : ℕ → ℝ} {A0 c0 : ℝ} {y ι ρ C n : ℕ → ℝ}
    (hopt : CIAOptimal u β R A0 c0 y ι ρ C n) (S : Finset ℕ) (DC Dn : ℝ → ℕ → ℝ)
    (hoffC : ∀ ε t, t ∉ S → DC ε t = C t) {l : Filter ℝ}
    (hgood : ∀ᶠ ε in l, (∀ t, 0 < DC ε t) ∧ (∀ t, 0 ≤ Dn ε t) ∧ DC ε 0 ≤ c0 ∧
      (∀ t, DC ε (t + 1) ≤ ρ t * Dn ε t) ∧
      ∀ᶠ T in atTop, ciaAssets R A0 y ι (DC ε) (Dn ε) T = ciaAssets R A0 y ι C n T) :
    ∀ᶠ ε in l, ∑ t ∈ S, β ^ t * u (DC ε t) ≤ ∑ t ∈ S, β ^ t * u (C t) := by
  obtain ⟨⟨_, _, _, _, hsum, hnp⟩, hmax⟩ := hopt
  filter_upwards [hgood] with ε ⟨hC, hn, h0, hcia, hw⟩
  obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hsum S (g := fun t => β ^ t * u (DC ε t))
    fun t ht => by simp only [hoffC ε t ht]
  have hadm : CIAAdmissible u β R A0 c0 y ι ρ (DC ε) (Dn ε) := by
    refine ⟨hC, hn, h0, hcia, h1, fun e he => ?_⟩
    filter_upwards [hnp e he, hw] with T hT hT'
    rw [hT']; exact hT
  have hle := hmax _ _ hadm
  rw [h2, Finset.sum_sub_distrib] at hle
  linarith

/-- **(a) The cash-in-advance constraint binds when the nominal interest rate is positive**
(O&R p. 548: "people never hold money in excess of next period's consumption requirements when
they could instead earn a higher return by lending the money out"): at an optimum with
`u` strictly increasing and `ι_s > 0` (`i_{s+1} > 0`), `P_{s+1}C_{s+1} = M_s`. Proof: lend the
excess `δ` and consume the return `R_s ι_s δ` at `s + 1`. -/
theorem cia_binds {u : ℝ → ℝ} {β : ℝ} {R : ℕ → ℝ} {A0 c0 : ℝ} {y ι ρ C n : ℕ → ℝ}
    (hβ : 0 < β) (hR : ∀ s, 0 < R s) (hιdef : ∀ s, ι s = 1 - ρ s / R s)
    (hmono : StrictMonoOn u (Set.Ioi 0)) (hopt : CIAOptimal u β R A0 c0 y ι ρ C n) (s : ℕ)
    (hι : 0 < ι s) : C (s + 1) = ρ s * n s := by
  obtain ⟨⟨hC, hn, hC0, hcia, hsum, hnp⟩, hmax⟩ := hopt
  by_contra hne
  have hlt : C (s + 1) < ρ s * n s := lt_of_le_of_ne (hcia s) hne
  set σ := ρ s * n s - C (s + 1) with hσ
  have hσ0 : 0 < σ := by linarith
  set δ := σ / R s with hδ
  have hδ0 : 0 < δ := div_pos hσ0 (hR s)
  have hRι : R s * ι s + ρ s = R s := by rw [hιdef]; field_simp [(hR s).ne']; ring
  set C' : ℕ → ℝ := fun t => if t = s + 1 then C (s + 1) + R s * ι s * δ else C t with hC'
  set n' : ℕ → ℝ := fun t => if t = s then n s - δ else n t with hn'
  have hne1 : s + 1 ≠ s := Nat.succ_ne_self s
  have hwealth : ∀ j, ciaWealth R A0 y ι C' n' (s + 2 + j) =
      ciaWealth R A0 y ι C n (s + 2 + j) := by
    intro j
    refine ciaWealth_congr_after ?_ (fun t ht => by simp [hC']; omega)
      (fun t ht => by simp [hn']; omega) j
    have hbef : ciaWealth R A0 y ι C' n' s = ciaWealth R A0 y ι C n s :=
      ciaWealth_congr_before (fun t ht => by simp [hC']; omega) (fun t ht => by simp [hn']; omega)
    rw [show s + 2 = s + 1 + 1 by ring, ciaWealth_succ, ciaWealth_succ (C := C), ciaWealth_succ,
      ciaWealth_succ (C := C), hbef]
    have hne2 : s ≠ s + 1 := by omega
    simp only [hC', hn', ↓reduceIte, hne1, hne2]
    ring
  have hoff : ∀ t, t ∉ ({s + 1} : Finset ℕ) → C' t = C t := fun t ht => by
    simp only [Finset.mem_singleton] at ht; simp [hC', ht]
  obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hsum {s + 1} (g := fun t => β ^ t * u (C' t))
    fun t ht => by simp only [hoff t ht]
  have hgain : 0 < R s * ι s * δ := by have := hR s; positivity
  have hadm : CIAAdmissible u β R A0 c0 y ι ρ C' n' := by
    refine ⟨fun t => ?_, fun t => ?_, ?_, fun t => ?_, h1, fun e he => ?_⟩
    · by_cases ht : t = s + 1
      · subst ht; simp only [hC', ↓reduceIte]; linarith [hC (s + 1)]
      · simp only [hC', ht, ↓reduceIte]; exact hC t
    · by_cases ht : t = s
      · subst ht; simp only [hn', ↓reduceIte]
        have : δ ≤ n t := by
          rw [hδ, div_le_iff₀ (hR t)]
          have h3 : ρ t < R t := by
            have := hιdef t; rw [this] at hι
            rw [sub_pos, div_lt_one (hR t)] at hι; exact hι
          have := hC (t + 1)
          nlinarith [hn t]
        linarith
      · simp only [hn', ht, ↓reduceIte]; exact hn t
    · simp only [hC', show (0 : ℕ) ≠ s + 1 from (Nat.succ_ne_zero s).symm, ↓reduceIte]; exact hC0
    · by_cases ht : t = s
      · subst ht
        simp only [hC', hn', ↓reduceIte]
        have : ρ t * (n t - δ) = C (t + 1) + σ - ρ t * δ := by rw [hσ]; ring
        rw [this]
        have : σ = R t * δ := by rw [hδ]; field_simp [(hR t).ne']
        nlinarith [hRι]
      · by_cases ht1 : t + 1 = s + 1
        · omega
        · simp only [hC', hn', ht, ht1, ↓reduceIte]; exact hcia t
    · filter_upwards [hnp e he, eventually_ge_atTop (s + 2)] with T hT hT2
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hT2
      unfold ciaAssets at hT ⊢
      have hc : C' (s + 2 + j) = C (s + 2 + j) := by simp [hC']; omega
      rw [hwealth j, hc]
      exact hT
  have hle := hmax _ _ hadm
  rw [h2, Finset.sum_singleton] at hle
  have hu : u (C (s + 1)) < u (C' (s + 1)) := by
    simp only [hC', ↓reduceIte]
    exact hmono (hC (s + 1)) (by simp only [Set.mem_Ioi]; linarith [hC (s + 1)]) (by linarith)
  have hb := pow_pos hβ (s + 1)
  have := mul_lt_mul_of_pos_left hu hb
  linarith

/-- The derivative of `ε ↦ u(c + εa)` at `0` (used for the CIA first-order conditions).
Context: O&R §8.3.6, pp. 547–550. -/
theorem hasDerivAt_affine {u u' : ℝ → ℝ} {c a : ℝ} (hu : HasDerivAt u (u' c) c) :
    HasDerivAt (fun ε => u (c + ε * a)) (u' c * a) 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => c + ε * a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const a).const_add c
  have h2 : HasDerivAt u (u' c) (c + 0 * a) := by simpa using hu
  exact h2.comp (0 : ℝ) h1

/-- **The CIA consumption Euler equation, derived from optimality** (O&R pp. 548–549, and
Exercise 4 with time-varying rates): at an optimum,
`(P_s/P_{s+1}) u'(C_{s+1}) = R_s β (P_{s+1}/P_{s+2}) u'(C_{s+2})` for every `s`, i.e. the
book's `(P_{s−1}/P_s)u'(C_s) = (1 + r_s)(P_s/P_{s+1})βu'(C_{s+1})` for `s > t`. Proof: hold
`ε/ρ_s` less money at `s` (consume `ε` less at `s + 1`), lend it, and hold `R_s ε/ρ_s` more money
at `s + 1` (consume `ρ_{s+1}R_s ε/ρ_s` more at `s + 2`); wealth is unchanged from `s + 3` on. -/
theorem cia_euler_of_optimal {u u' : ℝ → ℝ} {β : ℝ} {R : ℕ → ℝ} {A0 c0 : ℝ}
    {y ι ρ C n : ℕ → ℝ} (hβ : 0 < β) (hR : ∀ s, 0 < R s) (hρ : ∀ s, 0 < ρ s)
    (hιdef : ∀ s, ι s = 1 - ρ s / R s) (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hopt : CIAOptimal u β R A0 c0 y ι ρ C n) (s : ℕ) :
    ρ s * u' (C (s + 1)) = R s * β * ρ (s + 1) * u' (C (s + 2)) := by
  have hC := hopt.1.1
  have hn := hopt.1.2.1
  have hcia := hopt.1.2.2.2.1
  have hC0 := hopt.1.2.2.1
  set k := R s / ρ s with hk
  set DC : ℝ → ℕ → ℝ := fun ε t => if t = s + 1 then C (s + 1) + ε * (-1) else
    if t = s + 2 then C (s + 2) + ε * (ρ (s + 1) * k) else C t with hDC
  set Dn : ℝ → ℕ → ℝ := fun ε t => if t = s then n s - ε / ρ s else
    if t = s + 1 then n (s + 1) + ε * k else n t with hDn
  have h12 : s + 1 ≠ s + 2 := by omega
  have hDs1 : ∀ ε, DC ε (s + 1) = C (s + 1) + ε * (-1) := fun ε => by simp [hDC]
  have hDs2 : ∀ ε, DC ε (s + 2) = C (s + 2) + ε * (ρ (s + 1) * k) := fun ε => by simp [hDC]
  have hoff : ∀ ε t, t ∉ ({s + 1, s + 2} : Finset ℕ) → DC ε t = C t := fun ε t ht => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    simp [hDC, ht.1, ht.2]
  have hnpos : ∀ t, 0 < n t := fun t => by
    have := hcia t; have := hC (t + 1); have := hρ t
    by_contra h; push Not at h; nlinarith [hn t]
  have hw : ∀ ε j, ciaWealth R A0 y ι (DC ε) (Dn ε) (s + 3 + j) =
      ciaWealth R A0 y ι C n (s + 3 + j) := by
    intro ε j
    refine ciaWealth_congr_after ?_ (fun t ht => hoff ε t (by simp; omega))
      (fun t ht => by
        have h1 : t ≠ s := by omega
        have h2 : t ≠ s + 1 := by omega
        simp [hDn, h1, h2]) j
    have hbef : ciaWealth R A0 y ι (DC ε) (Dn ε) s = ciaWealth R A0 y ι C n s :=
      ciaWealth_congr_before (fun t ht => hoff ε t (by simp; omega))
        (fun t ht => by
          have h1 : t ≠ s := by omega
          have h2 : t ≠ s + 1 := by omega
          simp [hDn, h1, h2])
    have hs0 : DC ε s = C s := hoff ε s (by simp)
    have hn2 : Dn ε (s + 2) = n (s + 2) := by simp [hDn]
    rw [show s + 3 = s + 2 + 1 by ring, ciaWealth_succ, ciaWealth_succ (C := C),
      show s + 2 = s + 1 + 1 by ring, ciaWealth_succ, ciaWealth_succ (C := C), ciaWealth_succ,
      ciaWealth_succ (C := C), hbef, hs0, show s + 1 + 1 = s + 2 by ring, hDs2, hDs1, hn2]
    have e1 : Dn ε s = n s - ε / ρ s := by simp [hDn]
    have e2 : Dn ε (s + 1) = n (s + 1) + ε * k := by simp [hDn]
    rw [e1, e2, hιdef s, hιdef (s + 1), hk]
    have := (hρ s).ne'
    have := (hR s).ne'
    have := (hR (s + 1)).ne'
    field_simp
    ring
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C (s + 1) + ε * (-1) ∧
      0 < C (s + 2) + ε * (ρ (s + 1) * k) ∧ 0 ≤ n s - ε / ρ s ∧ 0 ≤ n (s + 1) + ε * k := by
    have c1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C (s + 1) + ε * (-1) :=
      ((by fun_prop : Continuous fun ε : ℝ => C (s + 1) + ε * (-1)).tendsto 0).eventually
        (lt_mem_nhds (by simpa using hC (s + 1)))
    have c2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C (s + 2) + ε * (ρ (s + 1) * k) :=
      ((by fun_prop : Continuous fun ε : ℝ => C (s + 2) + ε * (ρ (s + 1) * k)).tendsto 0).eventually
        (lt_mem_nhds (by simpa using hC (s + 2)))
    have c3 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < n s - ε / ρ s :=
      ((by fun_prop : Continuous fun ε : ℝ => n s - ε / ρ s).tendsto 0).eventually
        (lt_mem_nhds (by simpa using hnpos s))
    have c4 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < n (s + 1) + ε * k :=
      ((by fun_prop : Continuous fun ε : ℝ => n (s + 1) + ε * k).tendsto 0).eventually
        (lt_mem_nhds (by simpa using hnpos (s + 1)))
    filter_upwards [c1, c2, c3, c4] with ε h1 h2 h3 h4 using ⟨h1, h2, h3.le, h4.le⟩
  have hle := cia_perturb_le hopt {s + 1, s + 2} DC Dn hoff (l := 𝓝 0) (by
    filter_upwards [hev] with ε ⟨h1, h2, h3, h4⟩
    refine ⟨fun t => ?_, fun t => ?_, ?_, fun t => ?_, ?_⟩
    · by_cases ht : t = s + 1
      · rw [ht, hDs1]; exact h1
      by_cases ht2 : t = s + 2
      · rw [ht2, hDs2]; exact h2
      rw [hoff ε t (by simp [ht, ht2])]; exact hC t
    · by_cases ht : t = s
      · subst ht; simpa [hDn] using h3
      by_cases ht1 : t = s + 1
      · subst ht1; simpa [hDn] using h4
      simpa [hDn, ht, ht1] using hn t
    · rw [hoff ε 0 (by simp)]; exact hC0
    · by_cases ht : t = s
      · subst ht
        have e2 : Dn ε t = n t - ε / ρ t := by simp [hDn]
        rw [hDs1, e2]
        have := hcia t
        have := (hρ t).ne'
        rw [mul_sub, mul_div_cancel₀ _ this]
        linarith
      by_cases ht1 : t = s + 1
      · subst ht1
        have e2 : Dn ε (s + 1) = n (s + 1) + ε * k := by simp [hDn]
        rw [show s + 1 + 1 = s + 2 by ring, hDs2, e2]
        have := hcia (s + 1)
        rw [show s + 1 + 1 = s + 2 by ring] at this
        nlinarith
      · have e1 : DC ε (t + 1) = C (t + 1) := hoff ε (t + 1) (by simp; omega)
        have e2 : Dn ε t = n t := by simp [hDn, ht, ht1]
        rw [e1, e2]; exact hcia t
    · filter_upwards [eventually_ge_atTop (s + 3)] with T hT
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hT
      unfold ciaAssets
      rw [hw ε j, hoff ε (s + 3 + j) (by simp; omega)])
  have hloc : IsLocalMax (fun ε => β ^ (s + 1) * u (C (s + 1) + ε * (-1)) +
      β ^ (s + 2) * u (C (s + 2) + ε * (ρ (s + 1) * k))) 0 := by
    filter_upwards [hle] with ε hε
    rw [Finset.sum_pair h12, hDs1, hDs2] at hε
    simpa using hε
  have hA := (hasDerivAt_affine (a := -1) (hu _ (hC (s + 1)))).const_mul (β ^ (s + 1))
  have hB := (hasDerivAt_affine (a := ρ (s + 1) * k) (hu _ (hC (s + 2)))).const_mul (β ^ (s + 2))
  have h0 := hloc.hasDerivAt_eq_zero (hA.add hB)
  have hb := pow_pos hβ (s + 1)
  rw [show s + 2 = s + 1 + 1 by ring] at h0
  have h3 : β ^ (s + 1) * (u' (C (s + 1)) - β * u' (C (s + 1 + 1)) * (ρ (s + 1) * k)) = 0 := by
    linear_combination -h0
  have h4 := (mul_eq_zero.1 h3).resolve_left hb.ne'
  have hkρ : k * ρ s = R s := by rw [hk]; field_simp [(hρ s).ne']
  rw [show s + 2 = s + 1 + 1 by ring]
  linear_combination ρ s * h4 + β * u' (C (s + 1 + 1)) * ρ (s + 1) * hkρ

/-- A one-sided first-order condition: if `f` has derivative `d` at `0` and `f ε ≤ f 0` for all
small `ε ≥ 0`, then `d ≤ 0`.
Context: O&R §8.3.6, pp. 547–550. -/
theorem deriv_nonpos_of_right_max {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0)
    (hmax : ∀ᶠ ε in 𝓝[≥] (0 : ℝ), f ε ≤ f 0) : d ≤ 0 := by
  have hs := hasDerivAt_iff_tendsto_slope.mp hf
  have hs' : Tendsto (slope f 0) (𝓝[>] 0) (𝓝 d) :=
    hs.mono_left (nhdsWithin_mono _ fun ε (hε : 0 < ε) => ne_of_gt hε)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), slope f 0 ε ≤ 0 := by
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε ≤ f 0 := nhdsWithin_mono _ Set.Ioi_subset_Ici_self hmax
    filter_upwards [h1, self_mem_nhdsWithin] with ε hε hpos
    rw [slope_def_field, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hpos)
  exact le_of_tendsto hs' hev

/-- **The date-0 condition** (O&R p. 549: `C_t` is predetermined by `M_{t−1}/P_t`): at a CIA
optimum `β(P_0/P_1)u'(C_1) ≤ u'(C_0)`, with equality if the date-0 cash constraint is slack.
Proof: consume `ε` less at date 0 and carry the cash into date 1. -/
theorem cia_date0_of_optimal {u u' : ℝ → ℝ} {β : ℝ} {R : ℕ → ℝ} {A0 c0 : ℝ}
    {y ι ρ C n : ℕ → ℝ} (hR : ∀ s, 0 < R s) (hιdef : ∀ s, ι s = 1 - ρ s / R s)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hopt : CIAOptimal u β R A0 c0 y ι ρ C n) :
    β * ρ 0 * u' (C 1) ≤ u' (C 0) ∧ (C 0 < c0 → u' (C 0) = β * ρ 0 * u' (C 1)) := by
  have hC := hopt.1.1
  have hn := hopt.1.2.1
  have hC0 := hopt.1.2.2.1
  have hcia := hopt.1.2.2.2.1
  set DC : ℝ → ℕ → ℝ := fun ε t => if t = 0 then C 0 + ε * (-1) else
    if t = 1 then C 1 + ε * ρ 0 else C t with hDC
  set Dn : ℝ → ℕ → ℝ := fun ε t => if t = 0 then n 0 + ε else n t with hDn
  have hD0 : ∀ ε, DC ε 0 = C 0 + ε * (-1) := fun ε => by simp [hDC]
  have hD1 : ∀ ε, DC ε 1 = C 1 + ε * ρ 0 := fun ε => by simp [hDC]
  have hoff : ∀ ε t, t ∉ ({0, 1} : Finset ℕ) → DC ε t = C t := fun ε t ht => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    simp [hDC, ht.1, ht.2]
  have hw : ∀ ε j, ciaWealth R A0 y ι (DC ε) (Dn ε) (2 + j) = ciaWealth R A0 y ι C n (2 + j) := by
    intro ε j
    refine ciaWealth_congr_after ?_ (fun t ht => hoff ε t (by simp; omega))
      (fun t ht => by have : t ≠ 0 := by omega
                      simp [hDn, this]) j
    rw [show (2 : ℕ) = 0 + 1 + 1 by rfl, ciaWealth_succ, ciaWealth_succ (C := C), ciaWealth_succ,
      ciaWealth_succ (C := C)]
    rw [hD0, hD1]
    have e1 : Dn ε 0 = n 0 + ε := by simp [hDn]
    have e2 : Dn ε 1 = n 1 := by simp [hDn]
    rw [e1, e2, hιdef 0]
    simp only [ciaWealth]
    have := (hR 0).ne'
    field_simp
    ring
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C 0 + ε * (-1) ∧ 0 < C 1 + ε * ρ 0 ∧ 0 ≤ n 0 + ε := by
    have hn0 : 0 < n 0 := by
      have := hcia 0; have := hC 1
      by_contra h; push Not at h
      have h2 : ρ 0 * n 0 ≤ 0 ∨ True := Or.inr trivial
      rcases le_or_gt (ρ 0) 0 with hr | hr
      · nlinarith [hn 0]
      · nlinarith [hn 0]
    have c1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C 0 + ε * (-1) :=
      ((by fun_prop : Continuous fun ε : ℝ => C 0 + ε * (-1)).tendsto 0).eventually
        (lt_mem_nhds (by simpa using hC 0))
    have c2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C 1 + ε * ρ 0 :=
      ((by fun_prop : Continuous fun ε : ℝ => C 1 + ε * ρ 0).tendsto 0).eventually
        (lt_mem_nhds (by simpa using hC 1))
    have c3 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < n 0 + ε :=
      ((by fun_prop : Continuous fun ε : ℝ => n 0 + ε).tendsto 0).eventually
        (lt_mem_nhds (by simpa using hn0))
    filter_upwards [c1, c2, c3] with ε h1 h2 h3 using ⟨h1, h2, h3.le⟩
  have hgood : ∀ ε, 0 < C 0 + ε * (-1) → 0 < C 1 + ε * ρ 0 → 0 ≤ n 0 + ε →
      C 0 + ε * (-1) ≤ c0 → (∀ t, 0 < DC ε t) ∧ (∀ t, 0 ≤ Dn ε t) ∧ DC ε 0 ≤ c0 ∧
      (∀ t, DC ε (t + 1) ≤ ρ t * Dn ε t) ∧
      ∀ᶠ T in atTop, ciaAssets R A0 y ι (DC ε) (Dn ε) T = ciaAssets R A0 y ι C n T := by
    intro ε h1 h2 h3 h4
    refine ⟨fun t => ?_, fun t => ?_, by rw [hD0]; exact h4, fun t => ?_, ?_⟩
    · by_cases ht : t = 0
      · rw [ht, hD0]; exact h1
      by_cases ht1 : t = 1
      · rw [ht1, hD1]; exact h2
      rw [hoff ε t (by simp [ht, ht1])]; exact hC t
    · by_cases ht : t = 0
      · subst ht; simpa [hDn] using h3
      simpa [hDn, ht] using hn t
    · by_cases ht : t = 0
      · subst ht
        rw [show (0 : ℕ) + 1 = 1 by rfl, hD1]
        simp only [hDn, ↓reduceIte]
        have := hcia 0
        linarith
      · rw [hoff ε (t + 1) (by simp; omega)]
        simp only [hDn, ht, ↓reduceIte]
        exact hcia t
    · filter_upwards [eventually_ge_atTop 2] with T hT
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hT
      unfold ciaAssets
      rw [hw ε j, hoff ε (2 + j) (by simp; omega)]
  have hf := ((hasDerivAt_affine (a := -1) (hu _ (hC 0))).const_mul (β ^ 0)).add
    ((hasDerivAt_affine (a := ρ 0) (hu _ (hC 1))).const_mul (β ^ 1))
  have hsum_eq : ∀ ε, ∑ t ∈ ({0, 1} : Finset ℕ), β ^ t * u (DC ε t) =
      β ^ 0 * u (C 0 + ε * (-1)) + β ^ 1 * u (C 1 + ε * ρ 0) := fun ε => by
    rw [Finset.sum_pair (by norm_num), hD0, hD1]
  refine ⟨?_, fun hlt => ?_⟩
  · have hle := cia_perturb_le hopt {0, 1} DC Dn hoff (l := 𝓝[≥] 0) (by
      filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with ε ⟨h1, h2, h3⟩ hε
      exact hgood ε h1 h2 h3 (by simp only [Set.mem_Ici] at hε; linarith))
    have hd := deriv_nonpos_of_right_max hf (by
      filter_upwards [hle] with ε hε
      rw [hsum_eq, Finset.sum_pair (by norm_num)] at hε
      simpa using hε)
    simp only [pow_zero, pow_one] at hd
    linarith
  · have hev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), C 0 + ε * (-1) ≤ c0 :=
      ((by fun_prop : Continuous fun ε : ℝ => C 0 + ε * (-1)).tendsto 0).eventually
        (ge_mem_nhds (by simpa using hlt))
    have hle := cia_perturb_le hopt {0, 1} DC Dn hoff (l := 𝓝 0) (by
      filter_upwards [hev, hev2] with ε ⟨h1, h2, h3⟩ h4
      exact hgood ε h1 h2 h3 h4)
    have hloc : IsLocalMax (fun ε => β ^ 0 * u (C 0 + ε * (-1)) + β ^ 1 * u (C 1 + ε * ρ 0)) 0 := by
      filter_upwards [hle] with ε hε
      rw [hsum_eq, Finset.sum_pair (by norm_num)] at hε
      simpa using hε
    have h0 := hloc.hasDerivAt_eq_zero hf
    simp only [pow_zero, pow_one] at h0
    linarith

/-- **Necessity of the transversality condition in the CIA model** (O&R p. 534): at an optimum
with `u` strictly increasing, `liminf` of end-of-period assets is at most zero; otherwise one
could consume more at date 1 (financed by holding more cash at date 0) without violating the
no-Ponzi condition. -/
theorem cia_tvc_of_optimal {u : ℝ → ℝ} {β : ℝ} {R : ℕ → ℝ} {A0 c0 : ℝ} {y ι ρ C n : ℕ → ℝ}
    (hβ : 0 < β) (hR : ∀ s, 0 < R s) (hρ : ∀ s, 0 < ρ s) (hιdef : ∀ s, ι s = 1 - ρ s / R s)
    (hmono : StrictMonoOn u (Set.Ioi 0)) (hopt : CIAOptimal u β R A0 c0 y ι ρ C n) :
    CIATransversality R A0 y ι C n := by
  obtain ⟨⟨hC, hn, hC0, hcia, hsum, hnp⟩, hmax⟩ := hopt
  intro ε hε
  by_contra hcon
  rw [not_frequently] at hcon
  set κ := ε * ρ 0 with hκ
  have hκ0 : 0 < κ := mul_pos hε (hρ 0)
  set C' : ℕ → ℝ := fun t => if t = 1 then C 1 + κ else C t with hC'
  set n' : ℕ → ℝ := fun t => if t = 0 then n 0 + ε else n t with hn'
  have hprop : ∀ j, ciaWealth R A0 y ι C' n' (2 + j) =
      ciaWealth R A0 y ι C n (2 + j) - ε * ∏ i ∈ Finset.range (2 + j), R i := by
    intro j
    induction j with
    | zero =>
      rw [show (2 : ℕ) + 0 = 0 + 1 + 1 by rfl, ciaWealth_succ, ciaWealth_succ (C := C),
        ciaWealth_succ, ciaWealth_succ (C := C)]
      simp only [show (0 : ℕ) + 1 = 1 by rfl, hC', hn', ↓reduceIte, ciaWealth,
        show (0 : ℕ) ≠ 1 by norm_num, show (1 : ℕ) ≠ 0 by norm_num]
      rw [hιdef 0, Finset.prod_range_succ, Finset.prod_range_one]
      have := (hR 0).ne'
      rw [hκ]
      field_simp
      ring
    | succ j ih =>
      rw [← add_assoc, ciaWealth_succ, ciaWealth_succ (C := C), ih, Finset.prod_range_succ]
      have h1 : C' (2 + j) = C (2 + j) := by simp [hC']; omega
      have h2 : n' (2 + j) = n (2 + j) := by simp [hn']
      rw [h1, h2]
      ring
  have hoff : ∀ t, t ∉ ({1} : Finset ℕ) → C' t = C t := fun t ht => by
    simp only [Finset.mem_singleton] at ht; simp [hC', ht]
  obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hsum {1} (g := fun t => β ^ t * u (C' t))
    fun t ht => by simp only [hoff t ht]
  have hadm : CIAAdmissible u β R A0 c0 y ι ρ C' n' := by
    refine ⟨fun t => ?_, fun t => ?_, ?_, fun t => ?_, h1, fun e he => ?_⟩
    · by_cases ht : t = 1
      · subst ht; simp only [hC', ↓reduceIte]; linarith [hC 1]
      · simp only [hC', ht, ↓reduceIte]; exact hC t
    · by_cases ht : t = 0
      · subst ht; simp only [hn', ↓reduceIte]; linarith [hn 0]
      · simp only [hn', ht, ↓reduceIte]; exact hn t
    · simp only [hC', show (0 : ℕ) ≠ 1 by norm_num, ↓reduceIte]; exact hC0
    · by_cases ht : t = 0
      · subst ht
        simp only [hC', hn', show (0 : ℕ) + 1 = 1 by rfl, ↓reduceIte]
        have := hcia 0
        rw [hκ]; nlinarith
      · have ht1 : t + 1 ≠ 1 := by omega
        simp only [hC', hn', ht, ht1, ↓reduceIte]; exact hcia t
    · filter_upwards [hcon, eventually_ge_atTop 2] with T hT hT2
      push Not at hT
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hT2
      unfold ciaAssets at hT ⊢
      have hc : C' (2 + j) = C (2 + j) := by simp [hC']; omega
      rw [hprop j, hc]
      have hD : ciaDisc R (2 + j) * ∏ i ∈ Finset.range (2 + j), R i = 1 := by
        unfold ciaDisc
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_eq_one fun i _ => inv_mul_cancel₀ (hR i).ne'
      have : ciaDisc R (2 + j) * (ciaWealth R A0 y ι C n (2 + j) -
          ε * ∏ i ∈ Finset.range (2 + j), R i + y (2 + j) - C (2 + j)) =
          ciaDisc R (2 + j) * (ciaWealth R A0 y ι C n (2 + j) + y (2 + j) - C (2 + j)) - ε := by
        linear_combination (-ε) * hD
      rw [this]
      linarith
  have hle := hmax _ _ hadm
  rw [h2, Finset.sum_singleton] at hle
  have hu : u (C 1) < u (C' 1) := by
    simp only [hC', ↓reduceIte]
    exact hmono (hC 1) (by simp only [Set.mem_Ioi]; linarith [hC 1]) (by linarith)
  have := mul_lt_mul_of_pos_left hu (pow_pos hβ 1)
  linarith

/-- Re-indexing the present value of expenditure so that each date's money purchase is paired
with next date's consumption: `Σ_{s≤T} D_s(C_s + ι_s n_s) =
C_0 + Σ_{s<T}(D_s ι_s n_s + D_{s+1}C_{s+1}) + D_T ι_T n_T` (O&R (59), p. 548). -/
theorem cia_reindex (R : ℕ → ℝ) (ι C n : ℕ → ℝ) (T : ℕ) :
    ∑ s ∈ Finset.range (T + 1), ciaDisc R s * (C s + ι s * n s) =
      C 0 + ∑ s ∈ Finset.range T, (ciaDisc R s * (ι s * n s) + ciaDisc R (s + 1) * C (s + 1)) +
        ciaDisc R T * (ι T * n T) := by
  induction T with
  | zero => simp [ciaDisc]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- **Sufficiency of the CIA first-order conditions** (O&R §8.3.6, made precise): with `u`
concave and differentiable, nonnegative nominal rates (`ι_s ≥ 0`), an admissible plan with
binding cash-in-advance constraints, the Euler equation (60) at every date, the date-0
condition, and the transversality condition is optimal. Proof: the supporting-line inequality,
the iterated Euler equation `β^{s+1}u'(C_{s+1}) = λ D_s/ρ_s` and the budget bound
`D_s ι_s n'_s + D_{s+1}C'_{s+1} ≥ D_s C'_{s+1}/ρ_s` (which uses `ι_s ≥ 0`). -/
theorem cia_isOptimal_of_foc {u u' : ℝ → ℝ} {β : ℝ} {R : ℕ → ℝ} {A0 c0 : ℝ}
    {y ι ρ C n : ℕ → ℝ} (hβ : 0 < β) (hR : ∀ s, 0 < R s) (hρ : ∀ s, 0 < ρ s)
    (hιdef : ∀ s, ι s = 1 - ρ s / R s) (hconc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hι0 : ∀ s, 0 ≤ ι s)
    (hadm : CIAAdmissible u β R A0 c0 y ι ρ C n) (hbind : ∀ s, C (s + 1) = ρ s * n s)
    (heuler : ∀ s, ρ s * u' (C (s + 1)) = R s * β * ρ (s + 1) * u' (C (s + 2)))
    (h0 : β * ρ 0 * u' (C 1) ≤ u' (C 0)) (h0' : C 0 = c0 ∨ u' (C 0) = β * ρ 0 * u' (C 1))
    (hpos : 0 ≤ u' (C 1)) (htvc : CIATransversality R A0 y ι C n) :
    CIAOptimal u β R A0 c0 y ι ρ C n := by
  refine ⟨hadm, fun C' n' hadm' => ?_⟩
  obtain ⟨hC, hn, hC0, hcia, hsum, hnp⟩ := hadm
  obtain ⟨hC', hn', hC0', hcia', hsum', hnp'⟩ := hadm'
  set lam := β * ρ 0 * u' (C 1) with hlam
  have hlam0 : 0 ≤ lam := by have := hρ 0; positivity
  have hdisc : ∀ s, β ^ (s + 1) * u' (C (s + 1)) = lam * ciaDisc R s / ρ s := by
    intro s
    induction s with
    | zero => simp [hlam, ciaDisc]; field_simp [(hρ 0).ne']
    | succ s ih =>
      rw [ciaDisc_succ, pow_succ]
      have he := heuler s
      have h1 := (hρ s).ne'
      have h2 := (hρ (s + 1)).ne'
      have h3 := (hR s).ne'
      have hb : β * u' (C (s + 1 + 1)) = ρ s * u' (C (s + 1)) / (R s * ρ (s + 1)) := by
        rw [show s + 1 + 1 = s + 2 by ring]; field_simp; linarith
      calc β ^ (s + 1) * β * u' (C (s + 1 + 1)) = β ^ (s + 1) * (β * u' (C (s + 1 + 1))) := by
            ring
        _ = β ^ (s + 1) * u' (C (s + 1)) * ρ s / (R s * ρ (s + 1)) := by rw [hb]; ring
        _ = _ := by rw [ih]; field_simp
  -- the supporting-line bounds
  have hterm : ∀ s, β ^ (s + 1) * u (C' (s + 1)) - β ^ (s + 1) * u (C (s + 1)) ≤
      lam * (ciaDisc R s * C' (s + 1) / ρ s - ciaDisc R s * C (s + 1) / ρ s) := by
    intro s
    have t := MonetaryBubbles.concave_le_tangent' hconc (hC (s + 1)) (hC' (s + 1))
      (hu _ (hC (s + 1)))
    have hb := pow_pos hβ (s + 1)
    have := mul_le_mul_of_nonneg_left t hb.le
    have key : β ^ (s + 1) * (u' (C (s + 1)) * (C' (s + 1) - C (s + 1))) =
        lam * (ciaDisc R s * C' (s + 1) / ρ s - ciaDisc R s * C (s + 1) / ρ s) := by
      rw [← mul_assoc, hdisc s]; ring
    linarith
  have hterm0 : u (C' 0) - u (C 0) ≤ lam * (C' 0 - C 0) := by
    have t := MonetaryBubbles.concave_le_tangent' hconc (hC 0) (hC' 0) (hu _ (hC 0))
    rcases h0' with heq | heq
    · have hd : C' 0 - C 0 ≤ 0 := by rw [heq]; linarith
      have : u' (C 0) * (C' 0 - C 0) ≤ lam * (C' 0 - C 0) :=
        mul_le_mul_of_nonpos_right h0 hd
      linarith
    · rw [heq] at t; linarith
  -- the budget bounds
  have hbudget : ∀ (C'' n'' : ℕ → ℝ), (∀ s, C'' (s + 1) ≤ ρ s * n'' s) → (∀ s, 0 ≤ n'' s) →
      ∀ T, C'' 0 + ∑ s ∈ Finset.range T, ciaDisc R s * C'' (s + 1) / ρ s ≤
        A0 + ∑ s ∈ Finset.range (T + 1), ciaDisc R s * y s - ciaAssets R A0 y ι C'' n'' T := by
    intro C'' n'' hc hnn T
    have h1 := cia_pv_identity hR A0 y ι C'' n'' (T + 1)
    rw [cia_reindex] at h1
    have h2 := ciaAssets_eq hR A0 y ι C'' n'' T
    have h3 : ∀ s, ciaDisc R s * C'' (s + 1) / ρ s ≤
        ciaDisc R s * (ι s * n'' s) + ciaDisc R (s + 1) * C'' (s + 1) := by
      intro s
      have hD := ciaDisc_pos hR s
      rw [ciaDisc_succ, hιdef s]
      have hr := (hR s).ne'
      have hρs := hρ s
      have hn2 : C'' (s + 1) / ρ s ≤ n'' s := by rw [div_le_iff₀ hρs]; linarith [hc s]
      have hι2 : 0 ≤ 1 - ρ s / R s := by rw [← hιdef s]; exact hι0 s
      have e : ciaDisc R s * C'' (s + 1) / ρ s = ciaDisc R s * ((1 - ρ s / R s) *
          (C'' (s + 1) / ρ s)) + ciaDisc R s * (R s)⁻¹ * C'' (s + 1) := by
        field_simp; ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hn2 hι2
      have := mul_le_mul_of_nonneg_left this hD.le
      linarith
    have h4 := Finset.sum_le_sum fun s (_ : s ∈ Finset.range T) => h3 s
    linarith
  have hbudgetC : ∀ T, C 0 + ∑ s ∈ Finset.range T, ciaDisc R s * C (s + 1) / ρ s =
      A0 + ∑ s ∈ Finset.range (T + 1), ciaDisc R s * y s - ciaAssets R A0 y ι C n T := by
    intro T
    have h1 := cia_pv_identity hR A0 y ι C n (T + 1)
    rw [cia_reindex] at h1
    have h2 := ciaAssets_eq hR A0 y ι C n T
    have h3 : ∀ s, ciaDisc R s * C (s + 1) / ρ s =
        ciaDisc R s * (ι s * n s) + ciaDisc R (s + 1) * C (s + 1) := by
      intro s
      rw [ciaDisc_succ, hιdef s, hbind s]
      have := (hR s).ne'
      have := (hρ s).ne'
      field_simp
      ring
    rw [Finset.sum_congr rfl fun s _ => h3 s]
    linarith
  have hpartial : ∀ T, ∑ s ∈ Finset.range (T + 1), (β ^ s * u (C' s) - β ^ s * u (C s)) ≤
      lam * (ciaAssets R A0 y ι C n T - ciaAssets R A0 y ι C' n' T) := by
    intro T
    rw [Finset.sum_range_succ']
    have hs := Finset.sum_le_sum fun s (_ : s ∈ Finset.range T) => hterm s
    have hb1 := hbudget C' n' hcia' hn' T
    have hb2 := hbudgetC T
    have hsplit : ∑ s ∈ Finset.range T, lam * (ciaDisc R s * C' (s + 1) / ρ s -
        ciaDisc R s * C (s + 1) / ρ s) = lam * (∑ s ∈ Finset.range T, ciaDisc R s * C' (s + 1) /
        ρ s - ∑ s ∈ Finset.range T, ciaDisc R s * C (s + 1) / ρ s) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hsplit] at hs
    simp only [pow_zero, one_mul]
    have : lam * (C' 0 - C 0) + lam * (∑ s ∈ Finset.range T, ciaDisc R s * C' (s + 1) / ρ s -
        ∑ s ∈ Finset.range T, ciaDisc R s * C (s + 1) / ρ s) ≤
        lam * (ciaAssets R A0 y ι C n T - ciaAssets R A0 y ι C' n' T) := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (by linarith) hlam0
    linarith
  have hlim : Tendsto (fun T => ∑ s ∈ Finset.range (T + 1), (β ^ s * u (C' s) -
      β ^ s * u (C s))) atTop (𝓝 (∑' s, β ^ s * u (C' s) - ∑' s, β ^ s * u (C s))) :=
    (tendsto_add_atTop_iff_nat 1).2 (hsum'.hasSum.sub hsum.hasSum).tendsto_sum_nat
  by_contra hlt
  push Not at hlt
  set δ := ∑' s, β ^ s * u (C' s) - ∑' s, β ^ s * u (C s) with hδ
  have hδ0 : 0 < δ := by linarith
  have hl1 : 0 < lam + 1 := by linarith
  set ε := δ / (4 * (lam + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hsmall : 2 * lam * ε < δ := by
    have h4 : ε * (4 * (lam + 1)) = δ := by rw [hεdef]; field_simp
    nlinarith
  obtain ⟨T, hT3, hT1, hT2⟩ :=
    ((htvc ε hε).and_eventually ((hlim.eventually (lt_mem_nhds hsmall)).and (hnp' ε hε))).exists
  have hP := hpartial T
  have hab : ciaAssets R A0 y ι C n T - ciaAssets R A0 y ι C' n' T ≤ 2 * ε := by linarith
  have := mul_le_mul_of_nonneg_left hab hlam0
  linarith

/-- **Exact characterisation of the CIA optimum** (O&R §8.3.6, made precise): with `u` concave,
differentiable and strictly increasing (`u' > 0`) and positive nominal interest rates
(`ι_s > 0`), an admissible plan is optimal IFF the cash-in-advance constraint binds at every
date after 0, the Euler equation holds at every date, the date-0 condition holds and the
transversality condition holds. -/
theorem cia_optimal_iff {u u' : ℝ → ℝ} {β : ℝ} {R : ℕ → ℝ} {A0 c0 : ℝ} {y ι ρ C n : ℕ → ℝ}
    (hβ : 0 < β) (hR : ∀ s, 0 < R s) (hρ : ∀ s, 0 < ρ s) (hιdef : ∀ s, ι s = 1 - ρ s / R s)
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hu' : ∀ c, 0 < c → 0 < u' c) (hι : ∀ s, 0 < ι s) :
    CIAOptimal u β R A0 c0 y ι ρ C n ↔ CIAAdmissible u β R A0 c0 y ι ρ C n ∧
      (∀ s, C (s + 1) = ρ s * n s) ∧
      (∀ s, ρ s * u' (C (s + 1)) = R s * β * ρ (s + 1) * u' (C (s + 2))) ∧
      β * ρ 0 * u' (C 1) ≤ u' (C 0) ∧ (C 0 = c0 ∨ u' (C 0) = β * ρ 0 * u' (C 1)) ∧
      CIATransversality R A0 y ι C n := by
  have hmono : StrictMonoOn u (Set.Ioi 0) :=
    strictMonoOn_of_deriv_pos (convex_Ioi 0)
      (fun x hx => (hu x hx).continuousAt.continuousWithinAt)
      (fun x hx => by rw [interior_Ioi] at hx; rw [(hu x hx).deriv]; exact hu' x hx)
  constructor
  · intro hopt
    obtain ⟨h1, h2⟩ := cia_date0_of_optimal hR hιdef hu hopt
    refine ⟨hopt.1, fun s => cia_binds hβ hR hιdef hmono hopt s (hι s),
      cia_euler_of_optimal hβ hR hρ hιdef hu hopt, h1, ?_,
      cia_tvc_of_optimal hβ hR hρ hιdef hmono hopt⟩
    rcases hopt.1.2.2.1.lt_or_eq with hlt | heq
    · exact Or.inr (h2 hlt)
    · exact Or.inl heq
  · rintro ⟨hadm, hbind, he, h0, h0', htvc⟩
    exact cia_isOptimal_of_foc hβ hR hρ hιdef hconc hu (fun s => (hι s).le) hadm hbind he h0 h0'
      (hu' _ (hadm.1 1)).le htvc

/-! ## (59), (60), Exercise 4 and variants -/

/-- **(59)**, O&R p. 548: with the cash-in-advance constraint binding, `M_{s−1} = P_sC_s`, the
budget constraint (34) becomes `B_{s+1} = (1+r)B_s + Y_s − T_s − (P_{s+1}/P_s)C_{s+1}`. -/
theorem budget_59 {r : ℝ} {P B N Y T C : ℕ → ℝ} {s : ℕ} (hPs : P s ≠ 0)
    (hbud : B (s + 1) + N (s + 1) / P s = (1 + r) * B s + N s / P s + Y s - C s - T s)
    (hbind : ∀ t, N t = P t * C t) :
    B (s + 1) = (1 + r) * B s + Y s - T s - P (s + 1) / P s * C (s + 1) := by
  rw [hbind (s + 1), hbind s] at hbud
  field_simp at hbud ⊢
  linarith

/-- **Constant velocity** (O&R p. 549): with the constraint binding, `M_{t−1}/P_t = C_t`, so
money demand depends on consumption, not income or the nominal rate. -/
theorem constant_velocity {P N C : ℕ → ℝ} {t : ℕ} (hP : P t ≠ 0) (hbind : N t = P t * C t) :
    N t / P t = C t := by
  rw [hbind]; field_simp

/-- **(60) and Exercise 4**, O&R pp. 549 and 601: with Fisher parity
`1 + i_{s+1} = R_s P_{s+1}/P_s` (so `P_s/P_{s+1} = R_s/(1 + i_{s+1})`), the CIA Euler equation
is equivalent to `u'(C_{s+1})/(1 + i_{s+1}) = R_{s+1} β u'(C_{s+2})/(1 + i_{s+2})`: the book's
(60) holds with the time-varying real rate `1 + r_{s+2} = R_{s+1}` (Exercise 4). -/
theorem euler_60_iff {β : ℝ} {R ρ i : ℕ → ℝ} {u1 u2 : ℝ} (s : ℕ) (hR : 0 < R s)
    (hf1 : ρ s = R s / (1 + i (s + 1))) (hf2 : ρ (s + 1) = R (s + 1) / (1 + i (s + 2))) :
    ρ s * u1 = R s * β * ρ (s + 1) * u2 ↔
      u1 / (1 + i (s + 1)) = R (s + 1) * β * u2 / (1 + i (s + 2)) := by
  rw [hf1, hf2, show R s / (1 + i (s + 1)) * u1 = R s * (u1 / (1 + i (s + 1))) by ring,
    show R s * β * (R (s + 1) / (1 + i (s + 2))) * u2 =
      R s * (R (s + 1) * β * u2 / (1 + i (s + 2))) by ring]
  exact mul_right_inj' hR.ne'

/-- **(60) with a constant real rate**, O&R p. 549:
`u'(C_s)/(1+i_s) = (1+r)βu'(C_{s+1})/(1+i_{s+1})`, and in a stationary equilibrium with a
constant nominal rate it reduces to the usual Euler equation
`u'(C_s) = (1+r)βu'(C_{s+1})` (p. 549). -/
theorem euler_60_stationary {r β ibar u1 u2 : ℝ} (hi : 0 < 1 + ibar)
    (h : u1 / (1 + ibar) = (1 + r) * β * u2 / (1 + ibar)) : u1 = (1 + r) * β * u2 := by
  field_simp at h; linarith

/-- **The Helpman–Lucas timing** (O&R p. 550): if cash acquired in period `t` can be spent in `t`
(`M_t ≥ P_tC_t`), consumption is not taxed by inflation; the inflation tax falls on sellers'
receipts, so disposable income is `y_s = (1 − ι_s)Y_s − T_s` and period expenditure is just
`C_s`. The Euler equation derived from optimality is then the undistorted
`u'(C_s) = (1+r)βu'(C_{s+1})`. -/
theorem helpman_lucas_euler {u u' : ℝ → ℝ} {β r A0 : ℝ} {ι Y T C m : ℕ → ℝ} (hβ : 0 < β)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hopt : MonetaryBubbles.IsOptimalE u β r A0 (fun s => (1 - ι s) * Y s - T s)
      (fun _ c _ => c * 1 + 0) C m) (s : ℕ) :
    u' (C s) = (1 + r) * β * u' (C (s + 1)) := by
  have := MonetaryBubbles.euler_of_optimalE (w := fun _ _ => 1) (F := fun _ _ => 0) hβ hu
    (fun _ => one_pos) hopt s
  simpa using this

/-! ## Appendix 8A: a two-country cash-in-advance model -/

/-- The CES consumption price index (126), O&R p. 596:
`P = [γ p_H^{1−θ} + (1−γ) p_F^{1−θ}]^{1/(1−θ)}`. -/
noncomputable def twoGoodPrice (γ θ pH pF : ℝ) : ℝ :=
  (γ * pH ^ (1 - θ) + (1 - γ) * pF ^ (1 - θ)) ^ (1 / (1 - θ))

/-- **PPP from the law of one price and identical preferences** (O&R (122)–(127), p. 596): if
`p_H = ℰp^*_H` and `p_F = ℰp^*_F`, then `P = ℰP^*` (the price index is homogeneous of degree
one). -/
theorem ppp_of_law_of_one_price {γ θ E pHs pFs : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1)
    (hE : 0 < E) (hH : 0 < pHs) (hF : 0 < pFs) :
    twoGoodPrice γ θ (E * pHs) (E * pFs) = E * twoGoodPrice γ θ pHs pFs := by
  have h1γ : 0 < 1 - γ := by linarith
  have hθ' : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ1)
  unfold twoGoodPrice
  rw [mul_rpow hE.le hH.le, mul_rpow hE.le hF.le,
    show γ * (E ^ (1 - θ) * pHs ^ (1 - θ)) + (1 - γ) * (E ^ (1 - θ) * pFs ^ (1 - θ)) =
      E ^ (1 - θ) * (γ * pHs ^ (1 - θ) + (1 - γ) * pFs ^ (1 - θ)) by ring,
    mul_rpow (by positivity) (by positivity), ← rpow_mul hE.le, mul_one_div_cancel hθ', rpow_one]

/-- **(130), the intratemporal first-order condition**, O&R p. 597: for total spending `Z > 0`
(in units of the Home good) the CES demands at relative price `p_F/p_H` attain the maximal
value of the index among all bundles with the same cost, and they satisfy
`C_H = (γ/(1−γ))(p_F/p_H)^θ C_F`. -/
theorem relative_demand_130 {γ θ pH pF Z : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hH : 0 < pH) (hF : 0 < pF) (hZ : 0 < Z) :
    (∀ CH CF, 0 < CH → 0 < CF → CH + pF / pH * CF = Z →
      cesIndex γ θ CH CF ≤ cesIndex γ θ (cesDemandT γ θ (pF / pH) Z)
        (cesDemandN γ θ (pF / pH) Z)) ∧
    cesDemandT γ θ (pF / pH) Z =
      γ / (1 - γ) * (pF / pH) ^ θ * cesDemandN γ θ (pF / pH) Z := by
  have hp : 0 < pF / pH := div_pos hF hH
  have h1γ : 0 < 1 - γ := by linarith
  refine ⟨fun CH CF hCH hCF hcost => ?_, ?_⟩
  · rw [cesIndex_demand hγ0 hγ1 hθ hθ1 hp hZ]
    have := cesIndex_le_div_price hγ0 hγ1 hθ hθ1 hp hCH.le hCF.le (fun _ => ⟨hCH, hCF⟩)
      (by rw [hcost]; exact hZ)
    rwa [hcost] at this
  · have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
    rw [cesDemandT_eq, cesDemandN_eq]
    have e : (pF / pH) ^ θ * (pF / pH) ^ (-θ) = 1 := by
      rw [← rpow_add hp, add_neg_cancel, rpow_zero]
    field_simp
    linear_combination (-1 : ℝ) * e

/-- **(131), the equilibrium relative price**, O&R p. 597: if Home and Foreign residents both
choose `C_H = k C_F` with `k = (γ/(1−γ))(p_F/p_H)^θ` (identical preferences and the law of one
price) and goods markets clear, then `p_H/p_F = [γY_F/((1−γ)Y_H)]^{1/θ}`. -/
theorem relative_price_131 {γ θ pH pF YH YF CH CF CsH CsF : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hθ : 0 < θ) (hH : 0 < pH) (hF : 0 < pF) (hYF : 0 < YF)
    (hHome : CH = γ / (1 - γ) * (pF / pH) ^ θ * CF)
    (hFor : CsH = γ / (1 - γ) * (pF / pH) ^ θ * CsF) (hmH : CH + CsH = YH)
    (hmF : CF + CsF = YF) :
    pH / pF = (γ * YF / ((1 - γ) * YH)) ^ (1 / θ) := by
  have h1γ : 0 < 1 - γ := by linarith
  have hk : YH = γ / (1 - γ) * (pF / pH) ^ θ * YF := by
    rw [← hmH, ← hmF, hHome, hFor]; ring
  have hpow : (pH / pF) ^ θ = γ * YF / ((1 - γ) * YH) := by
    have hp : (pF / pH) ^ θ = ((pH / pF) ^ θ)⁻¹ := by
      rw [← inv_div, inv_rpow (div_pos hH hF).le]
    rw [hk, hp]
    have := rpow_pos_of_pos (div_pos hH hF) θ
    field_simp
  rw [← hpow, ← rpow_mul (div_pos hH hF).le, mul_one_div_cancel hθ.ne', rpow_one]

/-- **The steady-state real interest rate** (O&R p. 597): with constant consumption and constant
inflation, the Euler equation (129) gives `(1+r)β = 1`, i.e. `r = (1−β)/β`. -/
theorem steady_real_rate {β r ρ u1 : ℝ} (hβ : 0 < β) (hρ : 0 < ρ) (hu : 0 < u1)
    (h : ρ * u1 = (1 + r) * β * ρ * u1) : r = (1 - β) / β := by
  have h1 : (1 + r) * β = 1 := by
    have := mul_right_cancel₀ (mul_pos hρ hu).ne' (by linarith : (1 + r) * β * (ρ * u1) =
      1 * (ρ * u1))
    linarith
  field_simp
  linarith

/-- **The government budget constraints of Appendix 8A, with the sign corrected** (O&R p. 597):
summing the Home budget (128) and the Foreign budget (in Home currency) under PPP, the law of
one price, zero net bond supply and goods-market clearing gives
`P T + ℰP^*T^* = −(ΔM_H^{total} + ℰΔM_F^{total})`. So the corrected taxes
`T = −ΔM_H^{total}/P`, `T^* = −ΔM_F^{total}/P^*` (government spending zero, as in (43)) are
consistent, while the book's printed `T = +ΔM_H^{total}/P` would force total money to be
constant. -/
theorem appendix8A_taxes {P Ps E R pH pF pHs pFs Bh Bh' Bf Bf' MH MH' MF MF' MsH MsH' MsF MsF'
    YH YF CH CF CsH CsF T Ts : ℝ}
    (hHome : P * Bh' + MH' + E * MF' =
      P * R * Bh + MH + E * MF + pH * YH - pH * CH - pF * CF - P * T)
    (hFor : E * Ps * Bf' + MsH' + E * MsF' =
      E * Ps * R * Bf + MsH + E * MsF + E * pFs * YF - E * pHs * CsH - E * pFs * CsF -
        E * Ps * Ts)
    (hppp : P = E * Ps) (hlH : pH = E * pHs) (hlF : pF = E * pFs) (hb : Bh + Bf = 0)
    (hb' : Bh' + Bf' = 0) (hcH : CH + CsH = YH) (hcF : CF + CsF = YF) :
    P * T + E * Ps * Ts = -((MH' + MsH' - MH - MsH) + E * (MF' + MsF' - MF - MsF)) := by
  subst hppp hlH hlF
  have hBf : Bf = -Bh := by linarith
  have hBf' : Bf' = -Bh' := by linarith
  have hYH : YH = CH + CsH := hcH.symm
  have hYF : YF = CF + CsF := hcF.symm
  subst hBf hBf' hYH hYF
  linear_combination hHome + hFor

/-- The printed sign fails (O&R p. 597, a correction): with `T = +ΔM_H^{total}/P` and
`T^* = +ΔM_F^{total}/P^*`, the budgets and market clearing force
`ΔM_H^{total} + ℰΔM_F^{total} = 0`; with the corrected signs no such restriction arises. -/
theorem appendix8A_printed_sign {P Ps E ΔH ΔF T Ts : ℝ} (hP : P ≠ 0) (hPs : Ps ≠ 0)
    (hsum : P * T + E * Ps * Ts = -(ΔH + E * ΔF)) :
    ((T = ΔH / P ∧ Ts = ΔF / Ps) → ΔH + E * ΔF = 0) ∧
    (T = -ΔH / P → Ts = -ΔF / Ps → P * T + E * Ps * Ts = -(ΔH + E * ΔF)) := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [h1, h2] at hsum
    field_simp at hsum
    linarith
  · intro h1 h2
    rw [h1, h2]
    field_simp
    ring

/-! ## Appendix 8B and forward intervention (§8.7.6.1) -/

/-- The central bank's balance-sheet identity, O&R p. 598:
`P^g Gold + ℰB_F + B_H + ℰM_F = M_H + RR + NW` (with `base = M_H + RR`). -/
def BalanceSheet (Pg gold E bF bH mF base nw : ℝ) : Prop :=
  Pg * gold + E * bF + bH + E * mF = base + nw

/-- **Nonsterilised intervention** (O&R p. 598): buying one unit (of home currency) of foreign
bonds with newly issued base money preserves the balance-sheet identity. -/
theorem nonsterilised_preserves {Pg gold E bF bH mF base nw : ℝ} (hE : E ≠ 0)
    (h : BalanceSheet Pg gold E bF bH mF base nw) :
    BalanceSheet Pg gold E (bF + 1 / E) bH mF (base + 1) nw := by
  unfold BalanceSheet at h ⊢
  field_simp
  field_simp at h
  linarith

/-- **Sterilised intervention = nonsterilised purchase + open-market sale** (O&R pp. 598–599):
the combined operation preserves the identity, swaps one unit of home-currency bonds for
foreign-currency bonds and leaves the monetary base unchanged. -/
theorem sterilised_is_swap {Pg gold E bF bH mF base nw : ℝ} (hE : E ≠ 0)
    (h : BalanceSheet Pg gold E bF bH mF base nw) :
    BalanceSheet Pg gold E (bF + 1 / E) (bH - 1) mF base nw ∧
      (base + 1) - 1 = base := by
  refine ⟨?_, by ring⟩
  unfold BalanceSheet at h ⊢
  field_simp
  field_simp at h
  linarith

/-- **Forward intervention is equivalent to sterilised intervention** (O&R §8.7.6.1, p. 594):
covered interest parity (104) `F = ℰ(1+i)/(1+i^*)` gives
`(1 + i)/((1 + i^*)F) = 1/ℰ`, so fixing the forward rate and the interest differential pins the
spot rate exactly as a spot operation does. -/
theorem forward_intervention_identity {E F i is : ℝ} (hE : E ≠ 0) (hi : 1 + i ≠ 0)
    (his : 1 + is ≠ 0) (hcip : F = E * (1 + i) / (1 + is)) :
    (1 + i) / ((1 + is) * F) = 1 / E := by
  rw [hcip]
  field_simp

end ObstfeldRogoff.MoneyExchangeRates.CashInAdvance

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Continuous-time maximisation and the maximum principle

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, Supplement A to
Chapter 8 (pp. 745–753).

We prove:

* **A.1**: the period-`h` first-order conditions (3)–(5) give (35)–(36) at `h = 1`; the exact
  algebra behind (8), (9) and fn 1 and their limits as `h → 0` for right-differentiable paths;
  `(1+δh)^{−(s−t)/h} → e^{−δ(s−t)}`; (7) as the limit of (2)/h; and (10)–(11);
* **A.2, sufficiency (Mangasarian and Arrow)**: the book's box made precise — if the costate
  obeys `λ̇ = δλ − ∂H/∂Q`, `∂H/∂c = 0` and `H` is jointly concave (or the Arrow condition
  holds), then `∫₀^T e^{−δs}[u(c) − u(c^*)] ≤ e^{−δT}λ(T)(Q^*(T) − Q(T))` for every feasible
  rival, hence optimality whenever the boundary term is eventually small. The correct condition
  is therefore the transversality condition (15) for the candidate TOGETHER WITH a no-Ponzi
  condition on rivals: (15) alone is NOT sufficient (`ponzi_counterexample`);
* **necessity**: for the monetary problem (a linear-in-state problem) we derive (8), (3)+(9)
  and the transversality condition directly from optimality by compactly supported
  perturbations (`ct_money_foc`, `ct_costate_of_optimal`, `ct_tvc_of_optimal`), giving an exact
  characterisation of the optimum (`monetary_optimal_iff`). In general the transversality
  condition is NOT necessary: the Halkin (1974) example (`halkin_rival`, `halkin_candidate`);
* **A.3.1**: variation of constants and uniqueness for (11), (16), `λ(t) = λ(0)e^{(δ−r)t}`, the TVC
  in wealth form, (17), integration by parts for seignorage and (18), and (19);
* **A.3.2**: money demand (22), `u_C = γ^{1/σ}C^{−1/σ}(P^C)^{(θ−σ)/σ}`, the integrated Euler
  equation (23), its differential form, and (24)–(25), with the constant-rate and `θ = σ` cases;
* **A.3.3**: with `θ = 1`, `δ = r`, real balances are `K_m i^{−ζ}`, `ζ = γ + (1−γ)σ`; `x = 1/i`
  solves the UNSTABLE linear ODE `ζẋ = (r + g_M)x − 1`; the book's formula is its unique
  no-bubble solution (all others add `c e^{rt/ζ}M^{1/ζ}`); constant money growth gives
  `i = r + μ`; and `P^C → i^{1−γ}` as `θ → 1`.

Remarks on the box (p. 748): "λ must be nonnegative" is problem-specific (here `λ = u_C > 0`);
condition 1 presumes interior controls; existence of an optimum is not addressed.
-/

namespace ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple

open Real Filter Topology Set MeasureTheory
open ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility

/-! ## A.1 The period-`h` model and its continuous-time limit -/

/-- Shifting a right neighbourhood of `0` to a right neighbourhood of `s`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem tendsto_add_nhdsGT (s : ℝ) : Tendsto (fun h : ℝ => s + h) (𝓝[>] 0) (𝓝[>] s) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun h : ℝ => s + h) (𝓝 0) (𝓝 (s + 0)) :=
      tendsto_const_nhds.add tendsto_id
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [Set.mem_Ioi] at hh ⊢; linarith

/-- A right derivative as the limit of right difference quotients (fn 10 of Ch. 8).
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem slope_right_tendsto {P : ℝ → ℝ} {Pd s : ℝ} (hd : HasDerivWithinAt P Pd (Set.Ioi s) s) :
    Tendsto (fun h => (P (s + h) - P s) / h) (𝓝[>] 0) (𝓝 Pd) := by
  have h1 := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl s)).1 hd
  refine (h1.comp (tendsto_add_nhdsGT s)).congr fun h => ?_
  simp only [Function.comp_apply, slope_def_field, add_sub_cancel_left]

/-- Right continuity along `s + h`, `h → 0⁺`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem right_cont_tendsto {P : ℝ → ℝ} {Pd s : ℝ} (hd : HasDerivWithinAt P Pd (Set.Ioi s) s) :
    Tendsto (fun h => P (s + h)) (𝓝[>] 0) (𝓝 (P s)) :=
  (hd.continuousWithinAt.tendsto).comp (tendsto_add_nhdsGT s)


/-- **The period-`h` first-order conditions at `h = 1`** (O&R Supplement A, p. 746): with
`β = 1/(1+δ)`, conditions (3) `u_C = λ_s` and (5) `λ_s = ((1+r)/(1+δ))λ_{s+1}` give the Euler
equation (35) `u_C(s) = (1+r)β u_C(s+1)`, and (3)–(4) give the money Euler equation (36)
`u_C(s)/P_s = u_{M/P}(s)/P_s + β u_C(s+1)/P_{s+1}`. -/
theorem period_one_focs {r δ uCs uCs1 uMs lam0 lam1 P0 P1 : ℝ}
    (h3s : uCs = lam0) (h3s1 : uCs1 = lam1)
    (h4 : 1 / P0 * uMs * 1 = lam0 / P0 - (1 / (1 + δ * 1)) * lam1 / P1)
    (h5 : lam0 = (1 + r * 1) / (1 + δ * 1) * lam1) :
    uCs = (1 + r) * (1 / (1 + δ)) * uCs1 ∧
      uCs / P0 = uMs / P0 + 1 / (1 + δ) * uCs1 / P1 := by
  subst h3s h3s1
  simp only [mul_one] at h4 h5
  refine ⟨by rw [h5]; ring, ?_⟩
  rw [div_eq_mul_one_div uMs P0]
  linarith

/-- The algebra behind (8), O&R p. 746: from (3)–(5),
`u_{M/P}/u_C = (1/h)[1 − P_s/((1+rh)P_{s+h})] = r/(1+rh) + ((P_{s+h} − P_s)/h)/((1+rh)P_{s+h})`. -/
theorem mrs_period_h {r h Ps Psh : ℝ} (hh : h ≠ 0) (hrh : 1 + r * h ≠ 0) (hPsh : Psh ≠ 0) :
    1 / h * (1 - 1 / (1 + r * h) * (Ps / Psh)) =
      r / (1 + r * h) + (Psh - Ps) / h * (1 / ((1 + r * h) * Psh)) := by
  have hrh' : 1 + h * r ≠ 0 := by rwa [mul_comm] at hrh
  field_simp
  ring

/-- **(8) as the limit `h → 0`**, O&R p. 746: if the price path is right-differentiable at `s`
(`Ṗ` the right derivative, fn 10 of Ch. 8) and continuous from the right, then
`r/(1+rh) + ((P_{s+h} − P_s)/h)/((1+rh)P_{s+h}) → r + Ṗ/P = r + π = i`. -/
theorem mrs_limit {r Pd : ℝ} {P : ℝ → ℝ} {s : ℝ} (hP : 0 < P s)
    (hd : HasDerivWithinAt P Pd (Set.Ioi s) s) :
    Tendsto (fun h => r / (1 + r * h) + (P (s + h) - P s) / h * (1 / ((1 + r * h) * P (s + h))))
      (𝓝[>] 0) (𝓝 (r + Pd / P s)) := by
  have hslope : Tendsto (fun h => (P (s + h) - P s) / h) (𝓝[>] 0) (𝓝 Pd) :=
    slope_right_tendsto hd
  have hcont : Tendsto (fun h => P (s + h)) (𝓝[>] 0) (𝓝 (P s)) := right_cont_tendsto hd
  have hrh : Tendsto (fun h : ℝ => 1 + r * h) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun h : ℝ => 1 + r * h) (𝓝 0) (𝓝 (1 + r * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)
    rw [mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun h => r / (1 + r * h)) (𝓝[>] 0) (𝓝 (r / 1)) :=
    tendsto_const_nhds.div hrh one_ne_zero
  have h2 : Tendsto (fun h => 1 / ((1 + r * h) * P (s + h))) (𝓝[>] 0)
      (𝓝 (1 / (1 * P s))) :=
    tendsto_const_nhds.div (hrh.mul hcont) (by rw [one_mul]; exact hP.ne')
  have := h1.add (hslope.mul h2)
  simpa [div_eq_mul_one_div Pd (P s)] using this

/-- **(9) as the limit `h → 0`**, O&R p. 747: (5) is equivalent to
`(λ_{s+h} − λ_s)/h = λ_s(δ − r)/(1 + rh)`, whose limit is `λ_s(δ − r)`; so a
right-differentiable costate path satisfies `λ̇ = λ(δ − r)`. -/
theorem costate_period_h {r δ h lam0 lamh : ℝ} (hh : h ≠ 0) (hrh : 1 + r * h ≠ 0)
    (hδh : 1 + δ * h ≠ 0) (h5 : lam0 = (1 + r * h) / (1 + δ * h) * lamh) :
    (lamh - lam0) / h = lam0 * (δ - r) / (1 + r * h) := by
  have hl : lamh = (1 + δ * h) / (1 + r * h) * lam0 := by
    rw [h5, ← mul_assoc, div_mul_div_comm, mul_comm (1 + δ * h), div_self
      (mul_ne_zero hrh hδh), one_mul]
  rw [hl, div_mul_eq_mul_div, div_sub' hrh, div_div,
    div_eq_div_iff (mul_ne_zero hrh hh) hrh]
  ring

/-- **The costate equation (9)** (O&R p. 747): if the costate satisfies (5) for every small
period length `h > 0` and has right derivative `λ̇` at `s`, then `λ̇ = λ_s(δ − r)`. -/
theorem costate_limit {r δ lamd : ℝ} {lam : ℝ → ℝ} {s : ℝ}
    (hd : HasDerivWithinAt lam lamd (Set.Ioi s) s)
    (h5 : ∀ h, 0 < h → lam s = (1 + r * h) / (1 + δ * h) * lam (s + h))
    (hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 1 + r * h ≠ 0 ∧ 1 + δ * h ≠ 0) :
    lamd = lam s * (δ - r) := by
  have hslope : Tendsto (fun h => (lam (s + h) - lam s) / h) (𝓝[>] 0) (𝓝 lamd) :=
    slope_right_tendsto hd
  have hrh : Tendsto (fun h : ℝ => 1 + r * h) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun h : ℝ => 1 + r * h) (𝓝 0) (𝓝 (1 + r * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)
    rw [mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun h => lam s * (δ - r) / (1 + r * h)) (𝓝[>] 0)
      (𝓝 (lam s * (δ - r) / 1)) := tendsto_const_nhds.div hrh one_ne_zero
  rw [div_one] at h2
  refine tendsto_nhds_unique hslope (h2.congr' ?_)
  filter_upwards [hpos, self_mem_nhdsWithin] with h ⟨h1, h2⟩ hh
  exact (costate_period_h (ne_of_gt hh) h1 h2 (h5 h hh)).symm

/-- **Footnote 1** (O&R Supplement p. 746): with period length `h`, Fisher parity gives
`i_{s+h} = (1+rh)P_{s+h}/(hP_s) − 1/h = r P_{s+h}/P_s + (P_{s+h} − P_s)/(hP_s)`, which tends to
`r + π` as `h → 0` for a right-differentiable, right-continuous price path. -/
theorem fisher_period_h {r Pd : ℝ} {P : ℝ → ℝ} {s : ℝ} (hP : 0 < P s)
    (hd : HasDerivWithinAt P Pd (Set.Ioi s) s) :
    (∀ h, h ≠ 0 → (1 + r * h) * (P (s + h) / (h * P s)) - 1 / h =
      r * (P (s + h) / P s) + (P (s + h) - P s) / (h * P s)) ∧
    Tendsto (fun h => r * (P (s + h) / P s) + (P (s + h) - P s) / (h * P s)) (𝓝[>] 0)
      (𝓝 (r + Pd / P s)) := by
  refine ⟨fun h hh => by field_simp; ring, ?_⟩
  have hslope : Tendsto (fun h => (P (s + h) - P s) / h) (𝓝[>] 0) (𝓝 Pd) :=
    slope_right_tendsto hd
  have hcont : Tendsto (fun h => P (s + h)) (𝓝[>] 0) (𝓝 (P s)) := right_cont_tendsto hd
  have h1 : Tendsto (fun h => r * (P (s + h) / P s)) (𝓝[>] 0) (𝓝 (r * (P s / P s))) :=
    tendsto_const_nhds.mul (hcont.div_const _)
  rw [div_self hP.ne', mul_one] at h1
  have h2 := hslope.div_const (P s)
  refine (h1.add h2).congr fun h => ?_
  rw [div_div]

/-- **The continuous-time discount factor**, O&R p. 746:
`(1 + δh)^{−(s−t)/h} → e^{−δ(s−t)}` as `h → 0⁺`. -/
theorem discount_limit (δ a : ℝ) :
    Tendsto (fun h => (1 + δ * h) ^ (-(a / h))) (𝓝[>] 0) (𝓝 (Real.exp (-(δ * a)))) := by
  have hd : HasDerivAt (fun h : ℝ => Real.log (1 + δ * h)) δ 0 := by
    have h1 : HasDerivAt (fun h : ℝ => 1 + δ * h) δ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul δ).const_add 1
    have := h1.log (by simp)
    simpa using this
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  have hs' : Tendsto (fun h => Real.log (1 + δ * h) / h) (𝓝[>] 0) (𝓝 δ) := by
    refine (hslope.mono_left (nhdsWithin_mono _ fun h (hh : 0 < h) => ne_of_gt hh)).congr
      fun h => ?_
    simp [slope_def_field]
  have hexp : Tendsto (fun h => Real.exp (-(a * (Real.log (1 + δ * h) / h)))) (𝓝[>] 0)
      (𝓝 (Real.exp (-(a * δ)))) :=
    (Real.continuous_exp.tendsto _).comp ((hs'.const_mul a).neg)
  rw [mul_comm δ a]
  refine hexp.congr' ?_
  have hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < 1 + δ * h := by
    have : Tendsto (fun h : ℝ => 1 + δ * h) (𝓝 0) (𝓝 (1 + δ * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)
    rw [mul_zero, add_zero] at this
    exact (this.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds one_pos)
  filter_upwards [hpos] with h hh
  rw [rpow_def_of_pos hh]
  congr 1
  ring

/-- **The flow budget constraint (7) as the limit of (2)/h**, O&R p. 746: if the period-`h`
constraint (2), divided by `h`,
`(B_{s+h} − B_s)/h + (M_s − M_{s−h})/(hP_s) = rB_s + Y_s − C_s − T_s`, holds for every small
`h > 0` along a path with right derivative `Ḃ` and left derivative `Ṁ` at `s`, then
`Ḃ + Ṁ/P = rB + Y − T − C`. -/
theorem flow_budget_limit {B M : ℝ → ℝ} {Bd Md Ps r Y C T : ℝ} {s : ℝ}
    (hB : HasDerivWithinAt B Bd (Set.Ioi s) s) (hM : HasDerivWithinAt M Md (Set.Iio s) s)
    (h2 : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (B (s + h) - B s) / h + (M s - M (s - h)) / (h * Ps) = r * B s + Y - C - T) :
    Bd + Md / Ps = r * B s + Y - T - C := by
  have hBs := slope_right_tendsto hB
  have hMs : Tendsto (fun h => (M s - M (s - h)) / h) (𝓝[>] 0) (𝓝 Md) := by
    have h1 := (hasDerivWithinAt_iff_tendsto_slope' (show s ∉ Set.Iio s from lt_irrefl s)).1 hM
    have h3 : Tendsto (fun h : ℝ => s - h) (𝓝[>] 0) (𝓝[<] s) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun h : ℝ => s - h) (𝓝 0) (𝓝 (s - 0)) :=
          tendsto_const_nhds.sub tendsto_id
        rw [sub_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        simp only [Set.mem_Ioi, Set.mem_Iio] at hh ⊢; linarith
    refine (h1.comp h3).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h _
    simp only [Function.comp_apply, slope_def_field, show s - h - s = -h by ring]
    rw [div_neg, ← neg_div, neg_sub]
  have hlim := hBs.add (hMs.div_const Ps)
  have hc : Tendsto (fun h => (B (s + h) - B s) / h + (M s - M (s - h)) / h / Ps) (𝓝[>] 0)
      (𝓝 (r * B s + Y - C - T)) := tendsto_const_nhds.congr' (by
    filter_upwards [h2] with h hh
    rw [← hh, div_div, mul_comm h Ps])
  have := tendsto_nhds_unique hlim hc
  linarith

/-- **Financial wealth `Q = B + M/P` and (11)**, O&R p. 747: differentiating `Q = B + M/P`
gives `Q̇ = Ḃ + Ṁ/P − π M/P`, so the flow constraint (7) `Ḃ + Ṁ/P = rB + Y − T − C` is
equivalent to (11) `Q̇ = rQ + Y − T − C − i M/P` with `i = r + π`, `π = Ṗ/P`. -/
theorem wealth_flow_equiv {B M P : ℝ → ℝ} {Bd Md Pd r Y T C : ℝ} {s : ℝ} (hP : 0 < P s)
    (hB : HasDerivAt B Bd s) (hM : HasDerivAt M Md s) (hPd : HasDerivAt P Pd s) :
    HasDerivAt (fun t => B t + M t / P t) (Bd + Md / P s - Pd / P s * (M s / P s)) s ∧
      (Bd + Md / P s = r * B s + Y - T - C ↔
        Bd + Md / P s - Pd / P s * (M s / P s) =
          r * (B s + M s / P s) + Y - T - C - (r + Pd / P s) * (M s / P s)) := by
  refine ⟨?_, ?_⟩
  · have := hB.add (hM.div hPd hP.ne')
    refine this.congr_deriv ?_
    field_simp
    ring
  · constructor <;> intro h <;> linarith

/-! ## A.2 The maximum principle: sufficiency (Mangasarian/Arrow) -/

/-- The supporting-hyperplane inequality for a concave function on a real normed space
(generalising `MoneyInUtility.concave_le_tangent`): `U y ≤ U x + L (y − x)`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem concave_le_tangent_gen {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {U : V → ℝ} {S : Set V} (hU : ConcaveOn ℝ S U) {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    {L : V →L[ℝ] ℝ} (hL : HasFDerivAt U L x) : U y ≤ U x + L (y - x) := by
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

/-- The Hamiltonian of problem (12)–(14), O&R p. 748:
`H = u(c) + λ F(Q, c, s) − ν G(Q, c, s)` (current-value form). -/
def hamiltonian {E : Type*} (u : E → ℝ) (F G : ℝ → ℝ → E → ℝ) (lam ν : ℝ) (s : ℝ) (Q : ℝ)
    (c : E) : ℝ :=
  u c + lam * F s Q c - ν * G s Q c

/-- **The maximum principle as a sufficient condition, finite horizon** (Mangasarian 1966;
O&R p. 748 made precise). Let `(Q^*, c^*)` satisfy the state equation (13) and constraint (14),
let the costate obey `λ̇ = δλ − ∂H/∂Q` and `∂H/∂c = 0` (condition 1 of the book's box), and let
the Hamiltonian be jointly concave in `(Q, c)`. Then for every feasible rival `(Q, c)` with the
same initial state and every `T ≥ 0`,
`∫₀^T e^{−δs}[u(c) − u(c^*)] ds ≤ e^{−δT}λ(T)(Q^*(T) − Q(T))`. -/
theorem mangasarian_finite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {F G : ℝ → ℝ → E → ℝ} {δ : ℝ} {lam ν : ℝ → ℝ} {K : Set E}
    {Qs Q : ℝ → ℝ} {cs c : ℝ → E} {L : ℝ → (ℝ × E →L[ℝ] ℝ)}
    (hconc : ∀ s, 0 ≤ s → ConcaveOn ℝ (Set.univ ×ˢ K)
      (fun x : ℝ × E => hamiltonian u F G (lam s) (ν s) s x.1 x.2))
    (hdiff : ∀ s, 0 ≤ s → HasFDerivAt
      (fun x : ℝ × E => hamiltonian u F G (lam s) (ν s) s x.1 x.2) (L s) (Qs s, cs s))
    (hfoc : ∀ s, 0 ≤ s → ∀ e, L s (0, e) = 0)
    (hlam : ∀ s, HasDerivAt lam (δ * lam s - L s (1, 0)) s)
    (hQs : ∀ s, HasDerivAt Qs (F s (Qs s) (cs s)) s)
    (hGs : ∀ s, 0 ≤ s → G s (Qs s) (cs s) = 0) (hcs : ∀ s, 0 ≤ s → cs s ∈ K)
    (hQ : ∀ s, HasDerivAt Q (F s (Q s) (c s)) s) (hG : ∀ s, 0 ≤ s → G s (Q s) (c s) = 0)
    (hc : ∀ s, 0 ≤ s → c s ∈ K) (h0 : Q 0 = Qs 0) {T : ℝ} (hT : 0 ≤ T)
    (hint : IntervalIntegrable (fun s => Real.exp (-δ * s) * (u (c s) - u (cs s))) volume 0 T) :
    ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * (u (c s) - u (cs s)) ≤
      Real.exp (-δ * T) * lam T * (Qs T - Q T) := by
  set g : ℝ → ℝ := fun s => Real.exp (-δ * s) * lam s * (Qs s - Q s) with hg
  set g' : ℝ → ℝ := fun s => Real.exp (-δ * s) *
    (-(L s (1, 0)) * (Qs s - Q s) + lam s * (F s (Qs s) (cs s) - F s (Q s) (c s))) with hg'
  have hgd : ∀ s, HasDerivAt g (g' s) s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (-δ * s)) (Real.exp (-δ * s) * (-δ)) s := by
      have := ((hasDerivAt_id s).const_mul (-δ)).exp
      simp only [id, mul_one] at this
      exact this
    have := (he.mul (hlam s)).mul ((hQs s).sub (hQ s))
    refine this.congr_deriv ?_
    simp only [hg', Pi.mul_apply, Pi.sub_apply]
    ring
  have hle : ∀ s, 0 ≤ s → Real.exp (-δ * s) * (u (c s) - u (cs s)) ≤ g' s := by
    intro s hs
    have t := concave_le_tangent_gen (hconc s hs) (x := (Qs s, cs s)) (y := (Q s, c s))
      ⟨Set.mem_univ _, hcs s hs⟩ ⟨Set.mem_univ _, hc s hs⟩ (hdiff s hs)
    have hsplit : ((Q s, c s) - (Qs s, cs s) : ℝ × E) =
        (Q s - Qs s) • ((1 : ℝ), (0 : E)) + ((0 : ℝ), c s - cs s) := by
      ext <;> simp
    rw [hsplit, map_add, map_smul, hfoc s hs, add_zero, smul_eq_mul] at t
    simp only [hamiltonian, hGs s hs, hG s hs, mul_zero, sub_zero] at t
    have hepos := Real.exp_pos (-δ * s)
    simp only [hg']
    have : u (c s) - u (cs s) ≤ -(L s (1, 0)) * (Qs s - Q s) +
        lam s * (F s (Qs s) (cs s) - F s (Q s) (c s)) := by nlinarith
    exact mul_le_mul_of_nonneg_left this hepos.le
  have hint' : IntegrableOn (fun s => Real.exp (-δ * s) * (u (c s) - u (cs s))) (Set.Icc 0 T) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).2 ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1
      hint)
  have key := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hT
    (fun s _ => (hgd s).continuousAt.continuousWithinAt)
    (fun s _ => (hgd s).hasDerivWithinAt) hint' (fun s hs => hle s hs.1.le)
  have hg0 : g 0 = 0 := by simp [hg, h0]
  rw [hg0, sub_zero] at key
  exact key

/-- **Arrow's sufficiency theorem, finite horizon** (Arrow–Kurz 1970; the alternative concavity
condition of O&R p. 748): instead of joint concavity of `H`, suppose the Hamiltonian evaluated at
any state and feasible control is bounded by its value at the candidate plus a linear term,
`H(Q, c) ≤ H(Q^*, c^*) + H_Q (Q − Q^*)` — which holds when `c^*` maximises `H` and the maximised
Hamiltonian is concave in `Q` with supergradient `H_Q` — and let `λ̇ = δλ − H_Q`. Then the same
bound as in `mangasarian_finite` holds. -/
theorem arrow_finite {E : Type*} {u : E → ℝ} {F G : ℝ → ℝ → E → ℝ} {δ : ℝ} {lam ν LQ : ℝ → ℝ}
    {K : Set E} {Qs Q : ℝ → ℝ} {cs c : ℝ → E}
    (harrow : ∀ s, 0 ≤ s → ∀ q, ∀ x ∈ K, hamiltonian u F G (lam s) (ν s) s q x ≤
      hamiltonian u F G (lam s) (ν s) s (Qs s) (cs s) + LQ s * (q - Qs s))
    (hlam : ∀ s, HasDerivAt lam (δ * lam s - LQ s) s)
    (hQs : ∀ s, HasDerivAt Qs (F s (Qs s) (cs s)) s)
    (hGs : ∀ s, 0 ≤ s → G s (Qs s) (cs s) = 0) (hQ : ∀ s, HasDerivAt Q (F s (Q s) (c s)) s)
    (hG : ∀ s, 0 ≤ s → G s (Q s) (c s) = 0) (hc : ∀ s, 0 ≤ s → c s ∈ K) (h0 : Q 0 = Qs 0)
    {T : ℝ} (hT : 0 ≤ T)
    (hint : IntervalIntegrable (fun s => Real.exp (-δ * s) * (u (c s) - u (cs s))) volume 0 T) :
    ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * (u (c s) - u (cs s)) ≤
      Real.exp (-δ * T) * lam T * (Qs T - Q T) := by
  set g : ℝ → ℝ := fun s => Real.exp (-δ * s) * lam s * (Qs s - Q s) with hg
  set g' : ℝ → ℝ := fun s => Real.exp (-δ * s) *
    (-(LQ s) * (Qs s - Q s) + lam s * (F s (Qs s) (cs s) - F s (Q s) (c s))) with hg'
  have hgd : ∀ s, HasDerivAt g (g' s) s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (-δ * s)) (Real.exp (-δ * s) * (-δ)) s := by
      have := ((hasDerivAt_id s).const_mul (-δ)).exp
      simp only [id, mul_one] at this
      exact this
    have := (he.mul (hlam s)).mul ((hQs s).sub (hQ s))
    refine this.congr_deriv ?_
    simp only [hg', Pi.mul_apply, Pi.sub_apply]
    ring
  have hle : ∀ s, 0 ≤ s → Real.exp (-δ * s) * (u (c s) - u (cs s)) ≤ g' s := by
    intro s hs
    have t := harrow s hs (Q s) (c s) (hc s hs)
    simp only [hamiltonian, hGs s hs, hG s hs, mul_zero, sub_zero] at t
    simp only [hg']
    have : u (c s) - u (cs s) ≤ -(LQ s) * (Qs s - Q s) +
        lam s * (F s (Qs s) (cs s) - F s (Q s) (c s)) := by nlinarith
    exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
  have hint' : IntegrableOn (fun s => Real.exp (-δ * s) * (u (c s) - u (cs s))) (Set.Icc 0 T) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).2 ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1
      hint)
  have key := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hT
    (fun s _ => (hgd s).continuousAt.continuousWithinAt)
    (fun s _ => (hgd s).hasDerivWithinAt) hint' (fun s hs => hle s hs.1.le)
  have hg0 : g 0 = 0 := by simp [hg, h0]
  rw [hg0, sub_zero] at key
  exact key

/-- **The maximum principle as a sufficient condition, infinite horizon** (O&R p. 748, the box and
(15), made precise): under the hypotheses of `mangasarian_finite` for every horizon, if both
utility integrals converge and the boundary term satisfies
`∀ ε > 0, frequently e^{−δT}λ(T)(Q^*(T) − Q(T)) < ε`, then the candidate is at least as good as
the rival: `∫₀^∞ e^{−δs}u(c) ≤ ∫₀^∞ e^{−δs}u(c^*)`. -/
theorem mangasarian_infinite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {F G : ℝ → ℝ → E → ℝ} {δ : ℝ} {lam ν : ℝ → ℝ} {K : Set E}
    {Qs Q : ℝ → ℝ} {cs c : ℝ → E} {L : ℝ → (ℝ × E →L[ℝ] ℝ)} {U Us : ℝ}
    (hconc : ∀ s, 0 ≤ s → ConcaveOn ℝ (Set.univ ×ˢ K)
      (fun x : ℝ × E => hamiltonian u F G (lam s) (ν s) s x.1 x.2))
    (hdiff : ∀ s, 0 ≤ s → HasFDerivAt
      (fun x : ℝ × E => hamiltonian u F G (lam s) (ν s) s x.1 x.2) (L s) (Qs s, cs s))
    (hfoc : ∀ s, 0 ≤ s → ∀ e, L s (0, e) = 0)
    (hlam : ∀ s, HasDerivAt lam (δ * lam s - L s (1, 0)) s)
    (hQs : ∀ s, HasDerivAt Qs (F s (Qs s) (cs s)) s)
    (hGs : ∀ s, 0 ≤ s → G s (Qs s) (cs s) = 0) (hcs : ∀ s, 0 ≤ s → cs s ∈ K)
    (hQ : ∀ s, HasDerivAt Q (F s (Q s) (c s)) s) (hG : ∀ s, 0 ≤ s → G s (Q s) (c s) = 0)
    (hc : ∀ s, 0 ≤ s → c s ∈ K) (h0 : Q 0 = Qs 0)
    (hint1 : ∀ T, IntervalIntegrable (fun s => Real.exp (-δ * s) * u (c s)) volume 0 T)
    (hint2 : ∀ T, IntervalIntegrable (fun s => Real.exp (-δ * s) * u (cs s)) volume 0 T)
    (hU : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (c s)) atTop (𝓝 U))
    (hUs : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (cs s)) atTop (𝓝 Us))
    (hbd : ∀ ε > 0, ∃ᶠ T in atTop, Real.exp (-δ * T) * lam T * (Qs T - Q T) < ε) :
    U ≤ Us := by
  have hdiffT : ∀ T, 0 ≤ T → (∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (c s)) -
      ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (cs s) ≤
      Real.exp (-δ * T) * lam T * (Qs T - Q T) := by
    intro T hT
    rw [← intervalIntegral.integral_sub (hint1 T) (hint2 T)]
    have := mangasarian_finite hconc hdiff hfoc hlam hQs hGs hcs hQ hG hc h0 hT
      (by
        have := (hint1 T).sub (hint2 T)
        exact this.congr fun s _ => (mul_sub _ _ _).symm)
    refine le_trans (le_of_eq ?_) this
    congr 1; funext s; ring
  by_contra hlt
  push Not at hlt
  have hlim := hU.sub hUs
  obtain ⟨T, hT1, hT2, hT3⟩ := ((hbd ((U - Us) / 2) (by linarith)).and_eventually
    ((hlim.eventually (lt_mem_nhds (show (U - Us) / 2 < U - Us by linarith))).and
      (eventually_ge_atTop 0))).exists
  have := hdiffT T hT3
  linarith

/-- **The book's transversality condition (15) plus a no-Ponzi condition on rivals** give the
boundary condition of `mangasarian_infinite` (O&R p. 748): if `e^{−δT}λ(T)Q^*(T) → 0` and
`liminf e^{−δT}λ(T)Q(T) ≥ 0`, then `e^{−δT}λ(T)(Q^*(T) − Q(T)) < ε` eventually, for all `ε > 0`. -/
theorem boundary_of_tvc_noPonzi {δ : ℝ} {lam Qs Q : ℝ → ℝ}
    (htvc : Tendsto (fun T => Real.exp (-δ * T) * lam T * Qs T) atTop (𝓝 0))
    (hnp : ∀ ε > 0, ∀ᶠ T in atTop, -ε < Real.exp (-δ * T) * lam T * Q T) :
    ∀ ε > 0, ∃ᶠ T in atTop, Real.exp (-δ * T) * lam T * (Qs T - Q T) < ε := by
  intro ε hε
  refine ((htvc.eventually (gt_mem_nhds (half_pos hε))).and (hnp (ε / 2) (half_pos hε))).mono
    (fun T ⟨h1, h2⟩ => ?_) |>.frequently
  have : Real.exp (-δ * T) * lam T * (Qs T - Q T) =
      Real.exp (-δ * T) * lam T * Qs T - Real.exp (-δ * T) * lam T * Q T := by ring
  rw [this]
  linarith

/-! ### The costate path and the monetary problem -/

/-- **The costate path (A.3.1)**, O&R p. 750: the solution of `λ̇ = λ(δ − r)` is
`λ(t) = λ(0) e^{(δ−r)t}`; hence `e^{−δT}λ(T) = λ(0)e^{−rT}` (so the TVC (15) is
`λ(0) lim e^{−rT}Q(T) = 0`). -/
theorem costate_solution {r δ : ℝ} {lam : ℝ → ℝ}
    (hlam : ∀ s, HasDerivAt lam (lam s * (δ - r)) s) (t : ℝ) :
    lam t = lam 0 * Real.exp ((δ - r) * t) ∧
      Real.exp (-δ * t) * lam t = lam 0 * Real.exp (-r * t) := by
  have hw : ∀ s, HasDerivAt (fun s => lam s * Real.exp (-(δ - r) * s)) 0 s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (-(δ - r) * s)) (Real.exp (-(δ - r) * s) *
        (-(δ - r))) s := by
      have := ((hasDerivAt_id s).const_mul (-(δ - r))).exp
      simp only [id, mul_one] at this
      exact this
    have := (hlam s).mul he
    refine this.congr_deriv ?_
    ring
  have hconst : ∀ s, lam s * Real.exp (-(δ - r) * s) = lam 0 * Real.exp (-(δ - r) * 0) := by
    intro s
    exact is_const_of_deriv_eq_zero (fun s => (hw s).differentiableAt) (fun s => (hw s).deriv) s 0
  have h1 : lam t = lam 0 * Real.exp ((δ - r) * t) := by
    have := hconst t
    simp only [mul_zero, Real.exp_zero, mul_one] at this
    have he : Real.exp (-(δ - r) * t) * Real.exp ((δ - r) * t) = 1 := by
      rw [← Real.exp_add, show -(δ - r) * t + (δ - r) * t = 0 by ring, Real.exp_zero]
    calc lam t = lam t * (Real.exp (-(δ - r) * t) * Real.exp ((δ - r) * t)) := by rw [he, mul_one]
      _ = lam 0 * Real.exp ((δ - r) * t) := by rw [← mul_assoc, this]
  refine ⟨h1, ?_⟩
  rw [h1, mul_left_comm, ← Real.exp_add]
  congr 2
  ring

/-- **The book's Hamiltonian with money and bonds as separate controls** (O&R p. 749): with
`H = u(C, M/P) + λ(rQ + Y − T − C − iM/P) − ν(Q − B − M/P)`, the conditions `∂H/∂C = 0`,
`∂H/∂M = 0`, `∂H/∂B = 0` and `λ̇ = δλ − ∂H/∂Q` "boil down to" (3), (8) and (9): `ν = 0`,
`u_C = λ`, `u_{M/P} = λi`, `λ̇ = λ(δ − r)`. -/
theorem monetary_hamiltonian_focs {uC uM lam lamd ν i r δ P : ℝ} (hP : P ≠ 0)
    (hC : uC - lam = 0) (hM : 1 / P * (uM - lam * i + ν) = 0) (hB : ν = 0)
    (hQ : lamd = δ * lam - (lam * r - ν)) :
    ν = 0 ∧ uC = lam ∧ uM = lam * i ∧ lamd = lam * (δ - r) := by
  subst hB
  refine ⟨rfl, by linarith, ?_, by rw [hQ]; ring⟩
  have := (mul_eq_zero.1 hM).resolve_left (one_div_ne_zero hP)
  linarith

/-- The Hamiltonian of the monetary problem is jointly concave in wealth and the controls
`(C, M/P)` when `u` is concave (it is `u` plus an affine function), O&R p. 749. -/
theorem monetary_hamiltonian_concave {u : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)} (hK : Convex ℝ K)
    (hconc : ConcaveOn ℝ K u) (a r b c0 d : ℝ) :
    ConcaveOn ℝ (Set.univ ×ˢ K)
      (fun x : ℝ × (ℝ × ℝ) => u x.2 + a * (r * x.1 + b - x.2.1 - c0 * x.2.2) - d * 0) := by
  refine ⟨convex_univ.prod hK, fun x hx y hy α β hα hβ hαβ => ?_⟩
  have h1 := hconc.2 hx.2 hy.2 hα hβ hαβ
  simp only [smul_eq_mul, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] at h1 ⊢
  have hb : β = 1 - α := by linarith
  subst hb
  nlinarith [h1]

/-- **Sufficiency in the monetary problem** (O&R Supplement A.2–A.3, pp. 748–750, made
precise): with `u` concave and differentiable on the positive quadrant, a plan
`c^* = (C, M/P)` with wealth path `Q̇^* = rQ^* + y − C − iM/P` satisfying (3) `u_C = λ`, (8)
`u_{M/P} = λi`, (9) `λ̇ = λ(δ − r)` with `λ(0) > 0`, is at least as good as every feasible
rival with the same initial wealth (and a convergent utility integral) for which
`e^{−rT}(Q^*(T) − Q(T)) < ε` frequently, for every `ε > 0` — which holds when the candidate
satisfies the transversality condition and the rival the no-Ponzi condition
(`monetary_boundary`). -/
theorem monetary_sufficiency {u : ℝ × ℝ → ℝ} {uC um : ℝ × ℝ → ℝ} {r δ U Us : ℝ}
    {y i lam Qs Q : ℝ → ℝ} {cs c : ℝ → ℝ × ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) u)
    (hdiff : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), HasFDerivAt u (grad (uC p) (um p)) p)
    (hcs : ∀ s, 0 ≤ s → cs s ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
    (hc : ∀ s, 0 ≤ s → c s ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
    (hfocC : ∀ s, 0 ≤ s → uC (cs s) = lam s) (hfocM : ∀ s, 0 ≤ s → um (cs s) = lam s * i s)
    (hlam : ∀ s, HasDerivAt lam (lam s * (δ - r)) s) (hlam0 : 0 < lam 0)
    (hQs : ∀ s, HasDerivAt Qs (r * Qs s + y s - (cs s).1 - i s * (cs s).2) s)
    (hQ : ∀ s, HasDerivAt Q (r * Q s + y s - (c s).1 - i s * (c s).2) s) (h0 : Q 0 = Qs 0)
    (hbd' : ∀ ε > 0, ∃ᶠ T in atTop, Real.exp (-r * T) * (Qs T - Q T) < ε)
    (hint1 : ∀ T, IntervalIntegrable (fun s => Real.exp (-δ * s) * u (c s)) volume 0 T)
    (hint2 : ∀ T, IntervalIntegrable (fun s => Real.exp (-δ * s) * u (cs s)) volume 0 T)
    (hU : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (c s)) atTop (𝓝 U))
    (hUs : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (cs s)) atTop (𝓝 Us)) :
    U ≤ Us := by
  set F : ℝ → ℝ → ℝ × ℝ → ℝ := fun s q x => r * q + y s - x.1 - i s * x.2 with hF
  set G : ℝ → ℝ → ℝ × ℝ → ℝ := fun _ _ _ => 0 with hG
  have hK : Convex ℝ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := (convex_Ioi 0).prod (convex_Ioi 0)
  set L : ℝ → (ℝ × (ℝ × ℝ) →L[ℝ] ℝ) := fun s =>
    (grad (uC (cs s)) (um (cs s))).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
      lam s • ((r • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) -
        (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) -
        i s • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) with hL
  have hconcH : ∀ s, 0 ≤ s → ConcaveOn ℝ (Set.univ ×ˢ (Set.Ioi 0 ×ˢ Set.Ioi 0))
      (fun x : ℝ × (ℝ × ℝ) => hamiltonian u F G (lam s) 0 s x.1 x.2) := fun s _ =>
    monetary_hamiltonian_concave hK hconc (lam s) r (y s) (i s) 0
  have hdiffH : ∀ s, 0 ≤ s → HasFDerivAt
      (fun x : ℝ × (ℝ × ℝ) => hamiltonian u F G (lam s) 0 s x.1 x.2) (L s) (Qs s, cs s) := by
    intro s hs
    have h1 : HasFDerivAt (fun x : ℝ × (ℝ × ℝ) => u x.2)
        ((grad (uC (cs s)) (um (cs s))).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
        (Qs s, cs s) := (hdiff _ (hcs s hs)).comp (Qs s, cs s) hasFDerivAt_snd
    have h2 : HasFDerivAt (fun x : ℝ × (ℝ × ℝ) => r * x.1 + y s - x.2.1 - i s * x.2.2)
        ((r • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) -
          (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) -
          i s • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
        (Qs s, cs s) := by
      have a1 := ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt (x := (Qs s, cs s))).const_mul r
      have a2 := ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt (x := (Qs s, cs s))
      have a3 := (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt (x := (Qs s, cs s))).const_mul (i s)
      exact ((a1.add_const (y s)).sub a2).sub a3
    have h3 := (h1.add (h2.const_mul (lam s))).sub_const (0 * 0)
    exact h3
  have hfoc : ∀ s, 0 ≤ s → ∀ e, L s (0, e) = 0 := by
    intro s hs e
    simp [hL, grad_apply, hfocC s hs, hfocM s hs]
    ring
  have hlamL : ∀ s, HasDerivAt lam (δ * lam s - L s (1, 0)) s := by
    intro s
    refine (hlam s).congr_deriv ?_
    simp [hL, grad_apply]
    ring
  have hsol := costate_solution hlam
  refine mangasarian_infinite (G := G) (ν := fun _ => 0) (K := Set.Ioi 0 ×ˢ Set.Ioi 0)
    (L := L) hconcH hdiffH hfoc hlamL hQs (fun _ _ => rfl) hcs hQ (fun _ _ => rfl) hc h0
    hint1 hint2 hU hUs (fun ε hε => ?_)
  refine (hbd' (ε / lam 0) (div_pos hε hlam0)).mono fun T hT => ?_
  rw [(hsol T).2, mul_assoc]
  have := mul_lt_mul_of_pos_left hT hlam0
  rwa [mul_div_cancel₀ _ hlam0.ne'] at this

/-- **Sufficiency with the book's transversality condition (15)–(16) and a no-Ponzi condition on
rivals** (O&R p. 750): `e^{−rT}Q^*(T) → 0` and `liminf e^{−rT}Q(T) ≥ 0` give the boundary
condition of `monetary_sufficiency`. -/
theorem monetary_boundary {r : ℝ} {Qs Q : ℝ → ℝ}
    (htvc : ∀ ε > 0, ∃ᶠ T in atTop, Real.exp (-r * T) * Qs T < ε)
    (hnp : ∀ ε > 0, ∀ᶠ T in atTop, -ε < Real.exp (-r * T) * Q T) :
    ∀ ε > 0, ∃ᶠ T in atTop, Real.exp (-r * T) * (Qs T - Q T) < ε := by
  intro ε hε
  refine ((htvc (ε / 2) (half_pos hε)).and_eventually (hnp (ε / 2) (half_pos hε))).mono
    fun T ⟨h1, h2⟩ => ?_
  have : Real.exp (-r * T) * (Qs T - Q T) = Real.exp (-r * T) * Qs T -
      Real.exp (-r * T) * Q T := by ring
  rw [this]
  linarith

/-! ### Why the no-Ponzi condition on rivals is needed -/

/-- `∫₀^T e^{−rs} ds = (1 − e^{−rT})/r` for `r ≠ 0`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem integral_exp_neg_mul {r T : ℝ} (hr : r ≠ 0) :
    ∫ s in (0 : ℝ)..T, Real.exp (-r * s) = (1 - Real.exp (-r * T)) / r := by
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) T, HasDerivAt (fun s => -Real.exp (-r * s) / r)
      (Real.exp (-r * s)) s := by
    intro s _
    have := (((hasDerivAt_id s).const_mul (-r)).exp.neg).div_const r
    refine this.congr_deriv ?_
    simp only [id, mul_one]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable
      (μ := volume) _ _)]
  simp only [mul_zero, Real.exp_zero]
  field_simp
  ring

/-- **The transversality condition (15) alone is not sufficient** (a correction to the box on
O&R p. 748): with `u = log C`, `Q̇ = rQ − C`, `δ = r > 0` and `Q_0 > 0`, the plan
`C^* = rQ_0`, `Q^* ≡ Q_0` satisfies (13), `∂H/∂C = 0` with `λ ≡ 1/(rQ_0)`, the costate equation
and (15); but the Ponzi scheme `C ≡ rQ_0 + 1`, `Q(t) = Q_0 − (e^{rt} − 1)/r` is feasible and
yields strictly higher utility at every horizon and in the limit (`log(rQ_0+1)/r > log(rQ_0)/r`).
It violates the no-Ponzi condition: `e^{−rT}Q(T) → −1/r`. -/
theorem ponzi_counterexample {r Q0 : ℝ} (hr : 0 < r) (hQ0 : 0 < Q0) :
    (∀ t, HasDerivAt (fun _ : ℝ => Q0) (r * Q0 - r * Q0) t) ∧ (r * Q0)⁻¹ = 1 / (r * Q0) ∧
      (∀ t, HasDerivAt (fun _ : ℝ => 1 / (r * Q0)) (r * (1 / (r * Q0)) - 1 / (r * Q0) * r) t) ∧
      Tendsto (fun T => Real.exp (-r * T) * (1 / (r * Q0)) * Q0) atTop (𝓝 0) ∧
      (∀ t, HasDerivAt (fun t => Q0 - (Real.exp (r * t) - 1) / r)
        (r * (Q0 - (Real.exp (r * t) - 1) / r) - (r * Q0 + 1)) t) ∧
      (fun t => Q0 - (Real.exp (r * t) - 1) / r) 0 = Q0 ∧
      (∀ T, 0 < T → ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * Real.log (r * Q0) <
        ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * Real.log (r * Q0 + 1)) ∧
      Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * Real.log (r * Q0)) atTop
        (𝓝 (Real.log (r * Q0) / r)) ∧
      Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * Real.log (r * Q0 + 1)) atTop
        (𝓝 (Real.log (r * Q0 + 1) / r)) ∧
      Real.log (r * Q0) / r < Real.log (r * Q0 + 1) / r ∧
      Tendsto (fun T => Real.exp (-r * T) * (Q0 - (Real.exp (r * T) - 1) / r)) atTop
        (𝓝 (-(1 / r))) := by
  have hr0 := hr.ne'
  have hrQ : 0 < r * Q0 := mul_pos hr hQ0
  have hexp0 : Tendsto (fun T : ℝ => Real.exp (-r * T)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hr)
    refine this.congr fun T => ?_
    simp [neg_mul]
  have hint : ∀ (κ : ℝ) T, ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * κ =
      κ * ((1 - Real.exp (-r * T)) / r) := by
    intro κ T
    rw [intervalIntegral.integral_mul_const, integral_exp_neg_mul hr0]; ring
  have hlim : ∀ κ : ℝ, Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * κ) atTop
      (𝓝 (κ / r)) := by
    intro κ
    simp only [hint]
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hexp0).div_const r |>.const_mul κ
    rw [sub_zero] at this
    refine this.congr' (Eventually.of_forall fun T => rfl) |>.trans ?_
    rw [mul_one_div]
  have hlog : Real.log (r * Q0) < Real.log (r * Q0 + 1) :=
    Real.log_lt_log hrQ (by linarith)
  refine ⟨fun t => (hasDerivAt_const t Q0).congr_deriv (by ring), by rw [one_div],
    fun t => (hasDerivAt_const t (1 / (r * Q0))).congr_deriv (by ring), ?_, fun t => ?_, by simp,
    fun T hT => ?_,
    hlim _, hlim _, div_lt_div_of_pos_right hlog hr, ?_⟩
  · have := hexp0.mul_const (1 / (r * Q0) * Q0)
    rw [zero_mul] at this
    exact this.congr fun T => by ring
  · have := ((((hasDerivAt_id t).const_mul r).exp.sub_const 1).div_const r).const_sub Q0
    refine this.congr_deriv ?_
    simp only [id, mul_one]
    field_simp
    ring
  · rw [hint, hint]
    have h1 : 0 < (1 - Real.exp (-r * T)) / r := by
      apply div_pos _ hr
      have : Real.exp (-r * T) < 1 := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by nlinarith)
      linarith
    exact mul_lt_mul_of_pos_right hlog h1
  · have h1 : ∀ T, Real.exp (-r * T) * (Q0 - (Real.exp (r * T) - 1) / r) =
        Real.exp (-r * T) * Q0 + Real.exp (-r * T) / r - 1 / r := by
      intro T
      have : Real.exp (-r * T) * Real.exp (r * T) = 1 := by
        rw [← Real.exp_add]; simp
      calc Real.exp (-r * T) * (Q0 - (Real.exp (r * T) - 1) / r)
          = Real.exp (-r * T) * Q0 - (Real.exp (-r * T) * Real.exp (r * T) -
            Real.exp (-r * T)) / r := by ring
        _ = _ := by rw [this]; ring
    simp only [h1]
    have := ((hexp0.mul_const Q0).add (hexp0.div_const r)).sub_const (1 / r)
    simpa using this

/-! ### The Halkin counterexample: the transversality condition is not necessary -/

/-- **Halkin (1974): feasible paths of `ẋ = (1 − x)u`, `x(0) = 0`, `u ∈ [0, 1]` continuous**
never reach `x = 1`: `1 − x(t) = e^{−∫₀^t u}`; and the objective up to `T` is
`∫₀^T (1 − x)u = x(T) < 1`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem halkin_rival {x u : ℝ → ℝ} (hu : Continuous u)
    (hx : ∀ t, HasDerivAt x ((1 - x t) * u t) t) (hx0 : x 0 = 0) (T : ℝ) :
    ∫ s in (0 : ℝ)..T, (1 - x s) * u s = x T ∧ x T < 1 := by
  set Uu : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, u s with hUu
  have hUd : ∀ t, HasDerivAt Uu (u t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hu.intervalIntegrable (μ := volume) _ _)
      (hu.aestronglyMeasurable.stronglyMeasurableAtFilter) hu.continuousAt
  have hw : ∀ t, HasDerivAt (fun t => (1 - x t) * Real.exp (Uu t)) 0 t := by
    intro t
    have := ((hx t).const_sub 1).mul ((hUd t).exp)
    refine this.congr_deriv ?_
    ring
  have hconst : ∀ t, (1 - x t) * Real.exp (Uu t) = 1 := by
    intro t
    have := is_const_of_deriv_eq_zero (fun t => (hw t).differentiableAt)
      (fun t => (hw t).deriv) t 0
    rw [this, hx0]
    simp [hUu]
  have hpos : 0 < 1 - x T := by
    have h := hconst T
    by_contra hle
    push Not at hle
    have := Real.exp_pos (Uu T)
    nlinarith
  refine ⟨?_, by linarith⟩
  have hcont : Continuous fun s => (1 - x s) * u s := by
    have : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hx t)
    (hcont.intervalIntegrable (μ := volume) _ _), hx0, sub_zero]

/-- **Halkin's example: the candidate** (Halkin 1974; O&R p. 748 claims (15) necessary). The
control `u^* = 1/2` gives `x^*(t) = 1 − e^{−t/2}`, and its objective `∫₀^T (1 − x^*)u^* = x^*(T)`
converges to `1`, the supremum over all feasible paths (`halkin_rival`); so it is optimal.
With `H = (1 + λ)(1 − x)u`, the maximum-principle conditions `∂H/∂u = 0` and
`λ̇ = −∂H/∂x = (1+λ)u` hold for `λ ≡ −1`, and that is the ONLY costate satisfying `∂H/∂u = 0`;
yet `λ(T)x^*(T) → −1 ≠ 0`: the transversality condition fails at the optimum. -/
theorem halkin_candidate :
    (∀ t, HasDerivAt (fun t => 1 - Real.exp (-(t / 2)))
      ((1 - (1 - Real.exp (-(t / 2)))) * (1 / 2)) t) ∧
    Tendsto (fun T => ∫ s in (0 : ℝ)..T, (1 - (1 - Real.exp (-(s / 2)))) * (1 / 2)) atTop (𝓝 1) ∧
    (∀ t, (1 + (-1 : ℝ)) * (1 - (1 - Real.exp (-(t / 2)))) = 0) ∧
    (∀ t, HasDerivAt (fun _ : ℝ => (-1 : ℝ)) ((1 + (-1 : ℝ)) * (1 / 2)) t) ∧
    (∀ (lam : ℝ → ℝ) t, (1 + lam t) * (1 - (1 - Real.exp (-(t / 2)))) = 0 → lam t = -1) ∧
    Tendsto (fun T => (-1 : ℝ) * (1 - Real.exp (-(T / 2)))) atTop (𝓝 (-1)) := by
  have hx : ∀ t, HasDerivAt (fun t => 1 - Real.exp (-(t / 2)))
      ((1 - (1 - Real.exp (-(t / 2)))) * (1 / 2)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -(t / 2)) (-(1 / 2)) t :=
      ((hasDerivAt_id t).div_const 2).neg
    have := h1.exp.const_sub 1
    refine this.congr_deriv ?_
    ring
  have hexp : Tendsto (fun T : ℝ => Real.exp (-(T / 2))) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const two_pos)
    exact this.congr fun T => by simp
  refine ⟨hx, ?_, fun t => by ring, fun t => by simpa using hasDerivAt_const t (-1 : ℝ),
    fun lam t h => ?_, ?_⟩
  · have hint : ∀ T, ∫ s in (0 : ℝ)..T, (1 - (1 - Real.exp (-(s / 2)))) * (1 / 2) =
        1 - Real.exp (-(T / 2)) := by
      intro T
      have hcont : Continuous fun s : ℝ => (1 - (1 - Real.exp (-(s / 2)))) * (1 / 2) := by
        fun_prop
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hx t)
        (hcont.intervalIntegrable (μ := volume) _ _)]
      simp
    simp only [hint]
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub hexp
    rwa [sub_zero] at this
  · have h1 : 0 < 1 - (1 - Real.exp (-(t / 2))) := by
      have := Real.exp_pos (-(t / 2)); linarith
    have := (mul_eq_zero.1 h).resolve_right h1.ne'
    linarith
  · have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hexp).const_mul (-1 : ℝ)
    simpa using this

/-! ## A.3.1 The economy's consolidated budget constraint -/

/-- **Variation of constants** (O&R p. 749): for continuous net saving `f = Y − T − C − iM/P`,
`Q(T) = e^{rT}(Q_0 + ∫₀^T e^{−rs} f(s) ds)` solves (11) `Q̇ = rQ + f`, and it is the ONLY
differentiable solution with `Q(0) = Q_0`. -/
theorem variation_of_constants {r Q0 : ℝ} {f : ℝ → ℝ} (hf : Continuous f) :
    (∀ t, HasDerivAt (fun t => Real.exp (r * t) * (Q0 + ∫ s in (0 : ℝ)..t,
      Real.exp (-r * s) * f s)) (r * (Real.exp (r * t) * (Q0 + ∫ s in (0 : ℝ)..t,
        Real.exp (-r * s) * f s)) + f t) t) ∧
    ∀ Q : ℝ → ℝ, (∀ t, HasDerivAt Q (r * Q t + f t) t) → Q 0 = Q0 →
      ∀ t, Q t = Real.exp (r * t) * (Q0 + ∫ s in (0 : ℝ)..t, Real.exp (-r * s) * f s) := by
  have hg : Continuous fun s => Real.exp (-r * s) * f s := by fun_prop
  have hI : ∀ t, HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, Real.exp (-r * s) * f s)
      (Real.exp (-r * t) * f t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable (μ := volume) _ _)
      (hg.aestronglyMeasurable.stronglyMeasurableAtFilter) hg.continuousAt
  have he : ∀ (a t : ℝ), HasDerivAt (fun t => Real.exp (a * t)) (Real.exp (a * t) * a) t := by
    intro a t
    have := ((hasDerivAt_id t).const_mul a).exp
    simp only [id, mul_one] at this
    exact this
  have hsol : ∀ t, HasDerivAt (fun t => Real.exp (r * t) * (Q0 + ∫ s in (0 : ℝ)..t,
      Real.exp (-r * s) * f s)) (r * (Real.exp (r * t) * (Q0 + ∫ s in (0 : ℝ)..t,
        Real.exp (-r * s) * f s)) + f t) t := by
    intro t
    have := (he r t).mul ((hI t).const_add Q0)
    refine this.congr_deriv ?_
    have : Real.exp (r * t) * Real.exp (-r * t) = 1 := by rw [← Real.exp_add]; simp
    linear_combination f t * this
  refine ⟨hsol, fun Q hQ hQ0 t => ?_⟩
  have hw : ∀ t, HasDerivAt (fun t => Real.exp (-r * t) * (Q t - Real.exp (r * t) *
      (Q0 + ∫ s in (0 : ℝ)..t, Real.exp (-r * s) * f s))) 0 t := by
    intro t
    have := (he (-r) t).mul ((hQ t).sub (hsol t))
    refine this.congr_deriv ?_
    simp only [Pi.sub_apply]
    ring
  have hc := is_const_of_deriv_eq_zero (fun t => (hw t).differentiableAt) (fun t => (hw t).deriv)
    t 0
  simp only [mul_zero, Real.exp_zero, intervalIntegral.integral_same, add_zero, one_mul, hQ0,
    sub_self] at hc
  have hpos := Real.exp_pos (-r * t)
  have := (mul_eq_zero.1 hc).resolve_left hpos.ne'
  linarith

/-- **The finite-horizon constraint (16)**, O&R p. 750: a wealth path solving (11) satisfies
`∫₀^T e^{−rs}(C + iM/P) + e^{−rT}Q(T) = Q_0 + ∫₀^T e^{−rs}(Y − T) ds`. -/
theorem budget_16 {r : ℝ} {Q y e : ℝ → ℝ} (hy : Continuous y) (he : Continuous e)
    (hQ : ∀ t, HasDerivAt Q (r * Q t + y t - e t) t) (T : ℝ) :
    (∫ s in (0 : ℝ)..T, Real.exp (-r * s) * e s) + Real.exp (-r * T) * Q T =
      Q 0 + ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * y s := by
  have hf : Continuous fun s => y s - e s := hy.sub he
  have hsol := (variation_of_constants (Q0 := Q 0) (r := r) hf).2 Q
    (fun t => (hQ t).congr_deriv (by ring)) rfl T
  have h1 : ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (y s - e s) =
      (∫ s in (0 : ℝ)..T, Real.exp (-r * s) * y s) -
        ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * e s := by
    simp_rw [mul_sub]
    have c1 : Continuous fun s => Real.exp (-r * s) * y s := by fun_prop
    have c2 : Continuous fun s => Real.exp (-r * s) * e s := by fun_prop
    rw [intervalIntegral.integral_sub (c1.intervalIntegrable (μ := volume) 0 T)
      (c2.intervalIntegrable (μ := volume) 0 T)]
  have hQT : Q T = Real.exp (r * T) * (Q 0 + ((∫ s in (0 : ℝ)..T, Real.exp (-r * s) * y s) -
      ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * e s)) := by
    rw [hsol, h1]
  rw [hQT]
  have : Real.exp (-r * T) * Real.exp (r * T) = 1 := by rw [← Real.exp_add]; simp
  linear_combination (Q 0 + ((∫ s in (0 : ℝ)..T, Real.exp (-r * s) * y s) -
    ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * e s)) * this

/-- **The TVC in wealth form** (O&R p. 750): with `λ(t) = λ(0)e^{(δ−r)t}` and `λ(0) = u_C > 0`,
`e^{−δT}λ(T)Q(T) → 0` iff `e^{−rT}Q(T) → 0`. -/
theorem tvc_iff_wealth {r δ : ℝ} {lam Q : ℝ → ℝ}
    (hlam : ∀ s, HasDerivAt lam (lam s * (δ - r)) s) (hlam0 : 0 < lam 0) :
    Tendsto (fun T => Real.exp (-δ * T) * lam T * Q T) atTop (𝓝 0) ↔
      Tendsto (fun T => Real.exp (-r * T) * Q T) atTop (𝓝 0) := by
  have hs := costate_solution hlam
  have heq : ∀ T, Real.exp (-δ * T) * lam T * Q T = lam 0 * (Real.exp (-r * T) * Q T) := by
    intro T; rw [(hs T).2]; ring
  simp only [heq]
  constructor
  · intro h
    have := h.const_mul (lam 0)⁻¹
    rw [mul_zero] at this
    refine this.congr fun T => ?_
    field_simp
  · intro h
    have := h.const_mul (lam 0)
    rwa [mul_zero] at this

/-- **The infinite-horizon constraint (17)**, O&R p. 750: under the TVC `e^{−rT}Q(T) → 0`, if
the present value of disposable income converges to `Y_∞`, the present value of spending on
consumption and money services converges to `Q_0 + Y_∞`. -/
theorem budget_17 {r Yinf : ℝ} {Q y e : ℝ → ℝ} (hy : Continuous y) (he : Continuous e)
    (hQ : ∀ t, HasDerivAt Q (r * Q t + y t - e t) t)
    (htvc : Tendsto (fun T => Real.exp (-r * T) * Q T) atTop (𝓝 0))
    (hY : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * y s) atTop (𝓝 Yinf)) :
    Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * e s) atTop (𝓝 (Q 0 + Yinf)) := by
  have := ((tendsto_const_nhds (x := Q 0)).add hY).sub htvc
  rw [sub_zero] at this
  refine this.congr fun T => ?_
  have := budget_16 hy he hQ T
  linarith

/-- **Integration by parts for seignorage** (O&R p. 751): with `m = M/P` continuously
differentiable, `Ṁ/P = ṁ + πm`, so
`∫₀^T e^{−rs}(ṁ + πm) = e^{−rT}m(T) − m(0) + ∫₀^T e^{−rs}(r + π)m`. -/
theorem seignorage_by_parts {r : ℝ} {m md infl : ℝ → ℝ} (hm : ∀ s, HasDerivAt m (md s) s)
    (hmd : Continuous md) (hπ : Continuous infl) (T : ℝ) :
    ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (md s + infl s * m s) =
      Real.exp (-r * T) * m T - m 0 +
        ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * ((r + infl s) * m s) := by
  have hmc : Continuous m := continuous_iff_continuousAt.2 fun t => (hm t).continuousAt
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) T, HasDerivAt (fun s => Real.exp (-r * s) * m s)
      (Real.exp (-r * s) * md s - r * (Real.exp (-r * s) * m s)) s := by
    intro s _
    have h1 : HasDerivAt (fun s => Real.exp (-r * s)) (Real.exp (-r * s) * (-r)) s := by
      have := ((hasDerivAt_id s).const_mul (-r)).exp
      simpa using this
    exact (h1.mul (hm s)).congr_deriv (by ring)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun s => Real.exp (-r * s) * md s -
      r * (Real.exp (-r * s) * m s)).intervalIntegrable (μ := volume) _ _)
  simp only [mul_zero, Real.exp_zero, one_mul] at hint
  have c1 : Continuous fun s => Real.exp (-r * s) * md s - r * (Real.exp (-r * s) * m s) := by
    fun_prop
  have c2 : Continuous fun s => Real.exp (-r * s) * ((r + infl s) * m s) := by fun_prop
  have hsplit : ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (md s + infl s * m s) =
      (∫ s in (0 : ℝ)..T, (Real.exp (-r * s) * md s - r * (Real.exp (-r * s) * m s))) +
        ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * ((r + infl s) * m s) := by
    rw [← intervalIntegral.integral_add (c1.intervalIntegrable (μ := volume) _ _)
      (c2.intervalIntegrable (μ := volume) _ _)]
    congr 1; funext s; ring
  rw [hsplit, hint]

/-- **The government's intertemporal constraint (18) after integration by parts** (O&R
p. 751): under the no-hyperdeflation condition `e^{−rT}m(T) → 0`, if the present value of
taxes plus seignorage `T + Ṁ/P` converges to `X`, then the present value of taxes plus
`i m` (with `i = r + π`) converges to `X + m(0)`: `∫G = B^G − M/P + ∫(T + iM/P)`. -/
theorem government_18 {r X : ℝ} {m md infl tax : ℝ → ℝ} (hm : ∀ s, HasDerivAt m (md s) s)
    (hmd : Continuous md) (hπ : Continuous infl) (htax : Continuous tax)
    (hnhd : Tendsto (fun T => Real.exp (-r * T) * m T) atTop (𝓝 0))
    (hX : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (tax s + (md s + infl s * m s)))
      atTop (𝓝 X)) :
    Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (tax s + (r + infl s) * m s)) atTop
      (𝓝 (X + m 0)) := by
  have hmc : Continuous m := continuous_iff_continuousAt.2 fun t => (hm t).continuousAt
  have ct : Continuous fun s => Real.exp (-r * s) * tax s := by fun_prop
  have c1 : Continuous fun s => Real.exp (-r * s) * (md s + infl s * m s) := by fun_prop
  have c2 : Continuous fun s => Real.exp (-r * s) * ((r + infl s) * m s) := by fun_prop
  have key : ∀ T, ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (tax s + (r + infl s) * m s) =
      (∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (tax s + (md s + infl s * m s))) -
        Real.exp (-r * T) * m T + m 0 := by
    intro T
    have h1 : ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (tax s + (r + infl s) * m s) =
        (∫ s in (0 : ℝ)..T, Real.exp (-r * s) * tax s) +
          ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * ((r + infl s) * m s) := by
      rw [← intervalIntegral.integral_add (ct.intervalIntegrable (μ := volume) _ _)
        (c2.intervalIntegrable (μ := volume) _ _)]
      congr 1; funext s; ring
    have h2 : ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (tax s + (md s + infl s * m s)) =
        (∫ s in (0 : ℝ)..T, Real.exp (-r * s) * tax s) +
          ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (md s + infl s * m s) := by
      rw [← intervalIntegral.integral_add (ct.intervalIntegrable (μ := volume) _ _)
        (c1.intervalIntegrable (μ := volume) _ _)]
      congr 1; funext s; ring
    rw [h1, h2, seignorage_by_parts hm hmd hπ T]
    ring
  simp only [key]
  have := (hX.sub hnhd).add_const (m 0)
  rwa [sub_zero] at this

/-- **The economy's consolidated constraint (19)**, O&R p. 751: adding the private constraint
(17) (with private assets `B^p + M/P`) and the government's (18) (after integration by parts),
`∫₀^∞ (C + G)e^{−rs} = B + ∫₀^∞ Y e^{−rs}` with `B = B^p + B^G`: money services net out. -/
theorem consolidated_19 {Bp BG m0 Yinf Tinf Ginf Sinf Cinf : ℝ}
    (hpriv : Cinf + Sinf = Bp + m0 + (Yinf - Tinf)) (hgov : Ginf = BG - m0 + (Tinf + Sinf)) :
    Cinf + Ginf = (Bp + BG) + Yinf := by
  linarith

/-! ## A.3.2 Consumption as a function of nominal interest rates -/

/-- **Money demand (22)**, O&R p. 752: with CES-isoelastic preferences (20), condition (8)
`u_{M/P}/u_C = i` holds iff `M/P = ((1−γ)/γ) i^{−θ} C` (in continuous time the user cost of money
is the nominal rate itself). -/
theorem money_demand_22 {γ θ σ c k i : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ) (hc : 0 < c)
    (hk : 0 < k) (hi : 0 < i) :
    cesMargM γ θ σ c k = i * cesMargC γ θ σ c k ↔ k = (1 - γ) / γ * i ^ (-θ) * c :=
  ces_money_demand_iff hγ0 hγ1 hθ hc hk hi

/-- **Marginal utility along money demand**, O&R p. 752:
`u_C = γ^{1/σ} C^{−1/σ} (P^C)^{(θ−σ)/σ}` with `P^C = [γ + (1−γ)i^{1−θ}]^{1/(1−θ)}` (21). -/
theorem marginal_utility_on_demand {γ θ σ c i : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hσ : 0 < σ) (hc : 0 < c) (hi : 0 < i) :
    cesMargC γ θ σ c ((1 - γ) / γ * i ^ (-θ) * c) =
      γ ^ (1 / σ) * c ^ (-(1 / σ)) * cesPrice γ θ i ^ ((θ - σ) / σ) :=
  cesMargC_on_demand hγ0 hγ1 hθ hθ1 hσ hc hi rfl

/-- Solving `u_C = λ` for consumption: if `K C^{−1/σ} P^{a/σ} = L` then `C = K^σ P^a L^{−σ}`
(O&R p. 752). -/
theorem consumption_of_marginal {K σ a c P L : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hc : 0 < c)
    (hP : 0 < P) (h : K * c ^ (-(1 / σ)) * P ^ (a / σ) = L) :
    c = K ^ σ * P ^ a * L ^ (-σ) := by
  have h1 := congrArg (· ^ (-σ)) h
  rw [mul_rpow (by positivity) (by positivity), mul_rpow hK.le (by positivity),
    ← rpow_mul hc.le, ← rpow_mul hP.le, show -(1 / σ) * -σ = 1 by field_simp,
    show a / σ * -σ = -a by field_simp, rpow_one] at h1
  have e1 : K ^ (-σ) * K ^ σ = 1 := by rw [← rpow_add hK]; simp
  have e2 : P ^ (-a) * P ^ a = 1 := by rw [← rpow_add hP]; simp
  calc c = (K ^ (-σ) * c * P ^ (-a)) * (K ^ σ * P ^ a) := by
        linear_combination (-(c)) * (P ^ (-a) * P ^ a) * e1 - c * e2
    _ = _ := by rw [h1]; ring

/-- **The integrated Euler equation (23)**, O&R p. 752: if `u_C = λ(s) = λ_0 e^{(δ−r)s}` along
the money-demand curve, i.e. `γ^{1/σ}C^{−1/σ}(P^C)^{(θ−σ)/σ} = λ_0 e^{(δ−r)s}`, then
`C_s = C_t (P^C_s/P^C_t)^{θ−σ} e^{σ(r−δ)(s−t)}` — the book's
`C_s = C_t exp ∫_t^s [(θ − σ)Ṗ^C/P^C + σ(r − δ)]`. -/
theorem consumption_23 {γ θ σ lam0 δ r : ℝ} {C PC : ℝ → ℝ} (hγ0 : 0 < γ) (hσ : 0 < σ)
    (hC : ∀ s, 0 < C s) (hPC : ∀ s, 0 < PC s) (hlam0 : 0 < lam0)
    (hfoc : ∀ s, γ ^ (1 / σ) * C s ^ (-(1 / σ)) * PC s ^ ((θ - σ) / σ) =
      lam0 * Real.exp ((δ - r) * s)) (s t : ℝ) :
    C s = C t * (PC s / PC t) ^ (θ - σ) * Real.exp (σ * (r - δ) * (s - t)) := by
  have hK : (γ ^ (1 / σ)) ^ σ = γ := by rw [← rpow_mul hγ0.le, one_div_mul_cancel hσ.ne', rpow_one]
  have hform : ∀ u, C u = γ * PC u ^ (θ - σ) * Real.exp (-σ * ((δ - r) * u)) * lam0 ^ (-σ) := by
    intro u
    have := consumption_of_marginal (by positivity) hσ (hC u) (hPC u) (hfoc u)
    rw [this, hK, mul_rpow hlam0.le (Real.exp_pos _).le, ← Real.exp_mul]
    ring_nf
  rw [hform s, hform t, div_rpow (hPC s).le (hPC t).le]
  have h1 := rpow_pos_of_pos (hPC t) (θ - σ)
  have h2 : Real.exp (-σ * ((δ - r) * s)) = Real.exp (-σ * ((δ - r) * t)) *
      Real.exp (σ * (r - δ) * (s - t)) := by rw [← Real.exp_add]; ring_nf
  rw [h2]
  field_simp

/-- **The consumption Euler equation in differential form**, O&R p. 752:
`Ċ/C = (θ − σ)Ṗ^C/P^C + σ(r − δ)` for a differentiable consumption-price-index path. -/
theorem consumption_euler_ct {θ σ r δ A : ℝ} {PC PCd : ℝ → ℝ} (hPC : ∀ s, 0 < PC s)
    (hd : ∀ s, HasDerivAt PC (PCd s) s) (s : ℝ) :
    HasDerivAt (fun s => A * PC s ^ (θ - σ) * Real.exp (σ * (r - δ) * s))
      (A * PC s ^ (θ - σ) * Real.exp (σ * (r - δ) * s) *
        ((θ - σ) * (PCd s / PC s) + σ * (r - δ))) s := by
  have h1 := (hd s).rpow_const (p := θ - σ) (Or.inl (hPC s).ne')
  have h2 : HasDerivAt (fun s => Real.exp (σ * (r - δ) * s))
      (Real.exp (σ * (r - δ) * s) * (σ * (r - δ))) s := by
    have := ((hasDerivAt_id s).const_mul (σ * (r - δ))).exp
    simp only [id, mul_one] at this
    exact this
  have := (h1.const_mul A).mul h2
  refine this.congr_deriv ?_
  have hp := hPC s
  rw [rpow_sub_one hp.ne']
  field_simp

/-- **(24)–(25), consumption as a function of the price-index path**, O&R pp. 752–753: if
consumption follows (23) from `C_0 > 0` and the economy's constraint (19) gives
`∫₀^T e^{−rs}C_s ds → W`, then the denominator
`∫₀^T e^{[(σ−1)r − σδ]s} (P^C_0/P^C_s)^{σ−θ} ds` converges to `W/C_0`, i.e.
`C_0 = W / ∫₀^∞ e^{[(σ−1)r − σδ]s}(P^C_0/P^C_s)^{σ−θ} ds` (with `W > 0`). With a constant nominal
rate (constant `P^C`) or `θ = σ` the price-index factor is `1`: consumption is as in a model
without money. -/
theorem consumption_25 {θ σ r δ W : ℝ} {C PC : ℝ → ℝ} (hPC : ∀ s, 0 < PC s) (hC0 : 0 < C 0)
    (hpath : ∀ s, C s = C 0 * (PC s / PC 0) ^ (θ - σ) * Real.exp (σ * (r - δ) * s))
    (hW : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * C s) atTop (𝓝 W)) :
    Tendsto (fun T => ∫ s in (0 : ℝ)..T,
      Real.exp (((σ - 1) * r - σ * δ) * s) * (PC 0 / PC s) ^ (σ - θ)) atTop (𝓝 (W / C 0)) ∧
    (∀ T, (∀ s, PC s = PC 0) ∨ θ = σ → ∫ s in (0 : ℝ)..T,
      Real.exp (((σ - 1) * r - σ * δ) * s) * (PC 0 / PC s) ^ (σ - θ) =
        ∫ s in (0 : ℝ)..T, Real.exp (((σ - 1) * r - σ * δ) * s)) := by
  have hint : ∀ s, Real.exp (-r * s) * C s =
      C 0 * (Real.exp (((σ - 1) * r - σ * δ) * s) * (PC 0 / PC s) ^ (σ - θ)) := by
    intro s
    rw [hpath s]
    have h1 : (PC s / PC 0) ^ (θ - σ) = (PC 0 / PC s) ^ (σ - θ) := by
      rw [show θ - σ = -(σ - θ) by ring, rpow_neg (div_pos (hPC s) (hPC 0)).le,
        ← inv_rpow (div_pos (hPC s) (hPC 0)).le, inv_div]
    have h2 : Real.exp (-r * s) * Real.exp (σ * (r - δ) * s) =
        Real.exp (((σ - 1) * r - σ * δ) * s) := by rw [← Real.exp_add]; ring_nf
    rw [h1]
    linear_combination C 0 * (PC 0 / PC s) ^ (σ - θ) * h2
  refine ⟨?_, fun T h => ?_⟩
  · simp only [hint, intervalIntegral.integral_const_mul] at hW
    have := hW.const_mul (C 0)⁻¹
    refine (this.congr fun T => ?_).trans ?_
    · field_simp
    · rw [div_eq_inv_mul]
  · congr 1
    funext s
    rcases h with h | h
    · rw [h s, div_self (hPC 0).ne', one_rpow, mul_one]
    · rw [h, sub_self, rpow_zero, mul_one]

/-! ## A.3.3 A true reduced-form solution -/

/-- **Real balances as a power of the nominal rate** (O&R p. 753, `θ = 1`, `δ = r`): with
`u = [C^γ m^{1−γ}]^{1−1/σ}/(1−1/σ)` and a constant marginal utility of wealth `λ` (from (9) with
`δ = r`), `u_C = λ` along the money-demand curve `m = ((1−γ)/γ)C/i` gives
`C = K i^{(1−γ)(1−σ)}` and `m = K_m i^{−ζ}` with `ζ = γ + (1−γ)σ`. -/
theorem real_balances_power {γ σ lam c i : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hσ : 0 < σ)
    (hc : 0 < c) (hi : 0 < i)
    (hfoc : cdMargC γ σ c ((1 - γ) / γ * c / i) = lam) :
    c = (γ * ((1 - γ) / γ) ^ ((1 - γ) * (1 - 1 / σ))) ^ σ * lam ^ (-σ) *
        i ^ ((1 - γ) * (1 - σ)) ∧
      (1 - γ) / γ * c / i = (1 - γ) / γ * ((γ * ((1 - γ) / γ) ^ ((1 - γ) * (1 - 1 / σ))) ^ σ *
        lam ^ (-σ)) * i ^ (-(γ + (1 - γ) * σ)) := by
  have h1γ : 0 < 1 - γ := by linarith
  set K := γ * ((1 - γ) / γ) ^ ((1 - γ) * (1 - 1 / σ)) with hK
  have hK0 : 0 < K := by positivity
  rw [cdMargC_on_demand hγ0 hγ1 hσ hc hi, ← hK] at hfoc
  have hc' := consumption_of_marginal hK0 hσ hc (rpow_pos_of_pos hi (1 - γ))
    (a := 1 - σ) hfoc
  have hp : (i ^ (1 - γ)) ^ (1 - σ) = i ^ ((1 - γ) * (1 - σ)) := by rw [← rpow_mul hi.le]
  rw [hp] at hc'
  refine ⟨by rw [hc']; ring, ?_⟩
  rw [hc']
  have e : i ^ ((1 - γ) * (1 - σ)) / i = i ^ (-(γ + (1 - γ) * σ)) := by
    rw [← rpow_sub_one hi.ne']; congr 1; ring
  rw [← e]
  ring

/-- **The ODE for the inverse nominal rate** (O&R p. 753, made explicit): if real balances are
`M/P = K_m x^ζ` with `x = 1/i`, money grows at the instantaneous rate `g_M = Ṁ/M`, and Fisher
parity holds, `i = r + Ṗ/P`, then `ζ ẋ = (r + g_M) x − 1`. This equation is UNSTABLE forward
(its homogeneous solutions grow like `e^{rt/ζ}M^{1/ζ}`). -/
theorem inverse_rate_ode {r ζ Km : ℝ} {M x : ℝ → ℝ} {t Md xd Pd : ℝ} (hKm : 0 < Km)
    (hM : 0 < M t) (hx : 0 < x t) (hMd : HasDerivAt M Md t) (hxd : HasDerivAt x xd t)
    (hPd : HasDerivAt (fun t => M t / (Km * x t ^ ζ)) Pd t)
    (hfisher : 1 / x t = r + Pd / (M t / (Km * x t ^ ζ))) :
    ζ * xd = (r + Md / M t) * x t - 1 := by
  have hxz := rpow_pos_of_pos hx ζ
  have hq : HasDerivAt (fun t => M t / (Km * x t ^ ζ))
      ((Md * (Km * x t ^ ζ) - M t * (Km * (xd * ζ * x t ^ (ζ - 1)))) / (Km * x t ^ ζ) ^ 2) t :=
    hMd.div ((hxd.rpow_const (p := ζ) (Or.inl hx.ne')).const_mul Km) (by positivity)
  rw [hq.unique hPd |>.symm] at hfisher
  rw [rpow_sub_one hx.ne'] at hfisher
  field_simp at hfisher
  field_simp
  linarith [hfisher]

/-- The discounted money integrand `f(s) = e^{−rs/ζ} M(s)^{−1/ζ}` of A.3.3.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
noncomputable def rateKernel (r ζ : ℝ) (M : ℝ → ℝ) (s : ℝ) : ℝ :=
  Real.exp (-(r / ζ) * s) * M s ^ (-(1 / ζ))

/-- The no-bubble solution of the inverse-rate ODE, O&R p. 753:
`x^*(t) = (1/ζ) e^{rt/ζ} M(t)^{1/ζ} ∫_t^∞ e^{−rs/ζ} M(s)^{−1/ζ} ds`. -/
noncomputable def xStar (r ζ : ℝ) (M : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 / ζ * Real.exp ((r / ζ) * t) * M t ^ (1 / ζ) * ∫ s in Set.Ioi t, rateKernel r ζ M s

/-- **The book's formula** (O&R p. 753): `x^*(t) = (1/ζ)∫_t^∞ e^{−r(s−t)/ζ}[M(s)/M(t)]^{−1/ζ} ds`,
so `i_t = 1/x^*(t)` is exactly the displayed nominal-rate formula. -/
theorem xStar_eq_book {r ζ : ℝ} {M : ℝ → ℝ} (hM : ∀ s, 0 < M s) (t : ℝ) :
    xStar r ζ M t = 1 / ζ * ∫ s in Set.Ioi t,
      Real.exp (-(r * (s - t) / ζ)) * (M s / M t) ^ (-(1 / ζ)) := by
  unfold xStar
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1
  funext s
  unfold rateKernel
  rw [div_rpow (hM s).le (hM t).le, rpow_neg (hM t).le, div_inv_eq_mul]
  have e : Real.exp (r / ζ * t) * Real.exp (-(r / ζ) * s) = Real.exp (-(r * (s - t) / ζ)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← e]
  ring

/-- `∫_t^∞ f = ∫_0^∞ f − ∫_0^t f` for an integrable continuous kernel.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem tail_integral_eq {f : ℝ → ℝ} (hf : Continuous f) (hint : IntegrableOn f (Set.Ioi 0))
    (t : ℝ) : ∫ s in Set.Ioi t, f s = (∫ s in Set.Ioi 0, f s) - ∫ s in (0 : ℝ)..t, f s := by
  have := intervalIntegral.integral_interval_add_Ioi' (hf.intervalIntegrable (μ := volume) t 0)
    hint
  rw [intervalIntegral.integral_symm] at this
  linarith

/-- **The no-bubble solution solves the ODE** (O&R p. 753): for a positive, differentiable money
path with `Ṁ = g_M M` and an integrable kernel, `ζ ẋ^* = (r + g_M) x^* − 1` at every date. -/
theorem xStar_solves {r ζ : ℝ} {M gM : ℝ → ℝ} (hM : ∀ s, 0 < M s)
    (hMd : ∀ s, HasDerivAt M (gM s * M s) s) (hint : IntegrableOn (rateKernel r ζ M) (Set.Ioi 0))
    (t : ℝ) :
    HasDerivAt (xStar r ζ M) ((r + gM t) * xStar r ζ M t / ζ - 1 / ζ) t := by
  have hMc : Continuous M := continuous_iff_continuousAt.2 fun s => (hMd s).continuousAt
  have hf : Continuous (rateKernel r ζ M) := by
    unfold rateKernel
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (hMc.rpow_const fun s => Or.inl (hM s).ne')
  have hI : ∀ t, HasDerivAt (fun t => ∫ s in Set.Ioi t, rateKernel r ζ M s)
      (-rateKernel r ζ M t) t := by
    intro t
    have h1 := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable (μ := volume) 0 t)
      (hf.aestronglyMeasurable.stronglyMeasurableAtFilter) hf.continuousAt
    have h2 := h1.const_sub (∫ s in Set.Ioi 0, rateKernel r ζ M s)
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun u => tail_integral_eq hf hint u)
  have hE : HasDerivAt (fun t => Real.exp (r / ζ * t)) (Real.exp (r / ζ * t) * (r / ζ)) t := by
    have := ((hasDerivAt_id t).const_mul (r / ζ)).exp
    simp only [id, mul_one] at this
    exact this
  have hMp : HasDerivAt (fun t => M t ^ (1 / ζ)) (gM t * M t * (1 / ζ) * M t ^ (1 / ζ - 1)) t :=
    (hMd t).rpow_const (Or.inl (hM t).ne')
  have := (((hE.const_mul (1 / ζ)).mul hMp).mul (hI t))
  unfold xStar
  refine this.congr_deriv ?_
  have hk : rateKernel r ζ M t = Real.exp (-(r / ζ) * t) * M t ^ (-(1 / ζ)) := rfl
  rw [hk]
  have hMt := hM t
  have e1 : M t * M t ^ (1 / ζ - 1) = M t ^ (1 / ζ) := by
    rw [rpow_sub_one hMt.ne', mul_div_cancel₀ _ hMt.ne']
  have e2 : M t ^ (1 / ζ) * M t ^ (-(1 / ζ)) = 1 := by rw [← rpow_add hMt]; simp
  have e3 : Real.exp (r / ζ * t) * Real.exp (-(r / ζ) * t) = 1 := by
    rw [← Real.exp_add]; simp
  simp only [Pi.mul_apply]
  linear_combination (1 / ζ * (1 / ζ) * Real.exp (r / ζ * t) * gM t *
    ∫ s in Set.Ioi t, rateKernel r ζ M s) * e1 +
    (-(1 / ζ)) * (M t ^ (1 / ζ) * M t ^ (-(1 / ζ))) * e3 + (-(1 / ζ)) * e2

/-- **Every solution of the inverse-rate ODE is the no-bubble solution plus a bubble**, and the
no-bubble solution is the UNIQUE one along which `e^{−rt/ζ}M(t)^{−1/ζ}x(t) → 0` (O&R p. 753,
"one can then show", made precise; the analogue of the Cagan `b₀ = 0` selection):
`x(t) = x^*(t) + c e^{rt/ζ}M(t)^{1/ζ}`, with `c = 0` under the no-bubble condition. -/
theorem xStar_unique {r ζ : ℝ} {M gM x xd : ℝ → ℝ} (hζ : 0 < ζ) (hM : ∀ s, 0 < M s)
    (hMd : ∀ s, HasDerivAt M (gM s * M s) s) (hint : IntegrableOn (rateKernel r ζ M) (Set.Ioi 0))
    (hx : ∀ t, HasDerivAt x (xd t) t) (hode : ∀ t, ζ * xd t = (r + gM t) * x t - 1) :
    (∃ c, ∀ t, x t = xStar r ζ M t + c * (Real.exp ((r / ζ) * t) * M t ^ (1 / ζ))) ∧
    (Tendsto (fun t => Real.exp (-(r / ζ) * t) * M t ^ (-(1 / ζ)) * x t) atTop (𝓝 0) →
      ∀ t, x t = xStar r ζ M t) := by
  have hMc : Continuous M := continuous_iff_continuousAt.2 fun s => (hMd s).continuousAt
  have hf : Continuous (rateKernel r ζ M) := by
    unfold rateKernel
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (hMc.rpow_const fun s => Or.inl (hM s).ne')
  have hI : ∀ t, HasDerivAt (fun t => ∫ s in Set.Ioi t, rateKernel r ζ M s)
      (-rateKernel r ζ M t) t := by
    intro t
    have h1 := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable (μ := volume) 0 t)
      (hf.aestronglyMeasurable.stronglyMeasurableAtFilter) hf.continuousAt
    exact (h1.const_sub (∫ s in Set.Ioi 0, rateKernel r ζ M s)).congr_of_eventuallyEq
      (Eventually.of_forall fun u => tail_integral_eq hf hint u)
  set w : ℝ → ℝ := fun t => Real.exp (-(r / ζ) * t) * M t ^ (-(1 / ζ)) * x t -
    1 / ζ * ∫ s in Set.Ioi t, rateKernel r ζ M s with hw
  have hwd : ∀ t, HasDerivAt w 0 t := by
    intro t
    have hE : HasDerivAt (fun t => Real.exp (-(r / ζ) * t))
        (Real.exp (-(r / ζ) * t) * (-(r / ζ))) t := by
      have := ((hasDerivAt_id t).const_mul (-(r / ζ))).exp
      simp only [id, mul_one] at this
      exact this
    have hMp : HasDerivAt (fun t => M t ^ (-(1 / ζ)))
        (gM t * M t * (-(1 / ζ)) * M t ^ (-(1 / ζ) - 1)) t :=
      (hMd t).rpow_const (Or.inl (hM t).ne')
    have := ((hE.mul hMp).mul (hx t)).sub ((hI t).const_mul (1 / ζ))
    refine this.congr_deriv ?_
    have hk : rateKernel r ζ M t = Real.exp (-(r / ζ) * t) * M t ^ (-(1 / ζ)) := rfl
    rw [hk]
    have hMt := hM t
    have e1 : M t * M t ^ (-(1 / ζ) - 1) = M t ^ (-(1 / ζ)) := by
      rw [rpow_sub_one hMt.ne', mul_div_cancel₀ _ hMt.ne']
    have ho : xd t = ((r + gM t) * x t - 1) / ζ := by
      rw [eq_div_iff hζ.ne']; linarith [hode t]
    simp only [Pi.mul_apply]
    rw [ho]
    linear_combination (Real.exp (-(r / ζ) * t) * gM t * (-(1 / ζ)) * x t) * e1
  have hconst : ∀ t, w t = w 0 := fun t =>
    is_const_of_deriv_eq_zero (fun t => (hwd t).differentiableAt) (fun t => (hwd t).deriv) t 0
  have hsol : ∀ t, x t = xStar r ζ M t + ζ⁻¹ * ζ * w 0 * (Real.exp ((r / ζ) * t) *
      M t ^ (1 / ζ)) := by
    intro t
    have h : Real.exp (-(r / ζ) * t) * M t ^ (-(1 / ζ)) * x t -
        1 / ζ * ∫ s in Set.Ioi t, rateKernel r ζ M s = w 0 := hconst t
    have hMt := hM t
    have e2 : M t ^ (1 / ζ) * M t ^ (-(1 / ζ)) = 1 := by rw [← rpow_add hMt]; simp
    have e3 : Real.exp (r / ζ * t) * Real.exp (-(r / ζ) * t) = 1 := by
      rw [← Real.exp_add]; simp
    unfold xStar
    have hζ' := hζ.ne'
    calc x t = (Real.exp (r / ζ * t) * Real.exp (-(r / ζ) * t)) *
          (M t ^ (1 / ζ) * M t ^ (-(1 / ζ))) * x t := by rw [e2, e3]; ring
      _ = Real.exp (r / ζ * t) * M t ^ (1 / ζ) *
          (Real.exp (-(r / ζ) * t) * M t ^ (-(1 / ζ)) * x t) := by ring
      _ = Real.exp (r / ζ * t) * M t ^ (1 / ζ) *
          (w 0 + 1 / ζ * ∫ s in Set.Ioi t, rateKernel r ζ M s) := by
        rw [show Real.exp (-(r / ζ) * t) * M t ^ (-(1 / ζ)) * x t =
          w 0 + 1 / ζ * ∫ s in Set.Ioi t, rateKernel r ζ M s by linarith [h]]
      _ = _ := by field_simp; ring
  refine ⟨⟨ζ⁻¹ * ζ * w 0, hsol⟩, fun hbub t => ?_⟩
  have hItail : Tendsto (fun t => ∫ s in Set.Ioi t, rateKernel r ζ M s) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := ∫ s in Set.Ioi 0, rateKernel r ζ M s)).sub
      (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id)
    rw [sub_self] at this
    exact this.congr fun u => (tail_integral_eq hf hint u).symm
  have hw0 : w 0 = 0 := by
    have h1 : Tendsto w atTop (𝓝 (0 - 1 / ζ * 0)) := hbub.sub (hItail.const_mul (1 / ζ))
    rw [mul_zero, sub_zero] at h1
    have h2 : Tendsto w atTop (𝓝 (w 0)) :=
      tendsto_const_nhds.congr fun u => (hconst u).symm
    exact tendsto_nhds_unique h2 h1
  rw [hsol t, hw0]
  ring

/-- **Constant money growth**, O&R p. 753: with `M(s) = M_0 e^{μs}` and `r + μ > 0`, the
no-bubble nominal rate is `i = r + μ` at every date (`x^* ≡ 1/(r + μ)`), obtained by checking
that the constant satisfies the ODE and the no-bubble condition and invoking uniqueness. -/
theorem nominal_rate_constant_growth {r ζ μ M0 : ℝ} (hζ : 0 < ζ) (hM0 : 0 < M0)
    (hrμ : 0 < r + μ) (t : ℝ) :
    xStar r ζ (fun s => M0 * Real.exp (μ * s)) t = 1 / (r + μ) ∧
      1 / xStar r ζ (fun s => M0 * Real.exp (μ * s)) t = r + μ := by
  set M : ℝ → ℝ := fun s => M0 * Real.exp (μ * s) with hMdef
  have hM : ∀ s, 0 < M s := fun s => by simp only [hMdef]; positivity
  have hMd : ∀ s, HasDerivAt M (μ * M s) s := by
    intro s
    have := (((hasDerivAt_id s).const_mul μ).exp).const_mul M0
    simp only [id, mul_one] at this
    refine this.congr_deriv ?_
    simp only [hMdef]; ring
  have hker : ∀ s, rateKernel r ζ M s = M0 ^ (-(1 / ζ)) * Real.exp (-((r + μ) / ζ) * s) := by
    intro s
    unfold rateKernel
    simp only [hMdef]
    rw [mul_rpow hM0.le (Real.exp_pos _).le, ← Real.exp_mul]
    have : Real.exp (-(r / ζ) * s) * Real.exp (μ * s * -(1 / ζ)) =
        Real.exp (-((r + μ) / ζ) * s) := by rw [← Real.exp_add]; congr 1; ring
    rw [← this]; ring
  have hint : IntegrableOn (rateKernel r ζ M) (Set.Ioi 0) := by
    have h := (exp_neg_integrableOn_Ioi 0 (show 0 < (r + μ) / ζ by positivity)).const_mul
      (M0 ^ (-(1 / ζ)))
    exact IntegrableOn.congr_fun h (fun s _ => (hker s).symm) measurableSet_Ioi
  have hode : ∀ t : ℝ, ζ * (fun _ : ℝ => (0 : ℝ)) t =
      (r + μ) * (fun _ : ℝ => 1 / (r + μ)) t - 1 := by
    intro t; field_simp; ring
  have hbub : Tendsto (fun t => Real.exp (-(r / ζ) * t) * M t ^ (-(1 / ζ)) *
      (fun _ : ℝ => 1 / (r + μ)) t) atTop (𝓝 0) := by
    have hdec : Tendsto (fun t : ℝ => Real.exp (-((r + μ) / ζ) * t)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (show 0 < (r + μ) / ζ by positivity))
      exact this.congr fun u => by simp [neg_mul]
    have := (hdec.const_mul (M0 ^ (-(1 / ζ)))).mul_const (1 / (r + μ))
    rw [mul_zero, zero_mul] at this
    refine this.congr fun u => ?_
    have := hker u
    unfold rateKernel at this
    simp only
    rw [this]
  have h := (xStar_unique (x := fun _ => 1 / (r + μ)) (xd := fun _ => 0) hζ hM hMd hint
    (fun t => hasDerivAt_const t _) hode).2 hbub t
  refine ⟨h.symm, ?_⟩
  rw [← h]
  field_simp

/-- **The Cobb–Douglas price index** (O&R p. 753): as `θ → 1` the consumption-based price index
(21) `[γ + (1−γ)i^{1−θ}]^{1/(1−θ)}` converges to `i^{1−γ}`. -/
theorem priceIndex_cobbDouglas {γ i : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hi : 0 < i) :
    Tendsto (fun θ => cesPrice γ θ i) (𝓝[≠] 1) (𝓝 (i ^ (1 - γ))) :=
  cesPrice_tendsto_cobbDouglas hγ0 hγ1 hi

/-! ## Necessity of (3), (8), (9) and of the TVC in the monetary problem -/

/-- Financial wealth of a continuous-time plan `c = (C, M/P)` (O&R (11) solved by variation of
constants): `Q(T) = e^{rT}(Q_0 + ∫₀^T e^{−rs}(y_s − C_s − i_s m_s) ds)`. -/
noncomputable def ctWealth (r Q0 : ℝ) (y i : ℝ → ℝ) (c : ℝ → ℝ × ℝ) (T : ℝ) : ℝ :=
  Real.exp (r * T) * (Q0 + ∫ s in (0 : ℝ)..T, Real.exp (-r * s) * (y s - (c s).1 - i s * (c s).2))

/-- An admissible continuous-time plan with value `U` (O&R (6), (7), (10)–(11)): continuous,
with positive consumption and real balances (plans are defined on all of `ℝ`; dates before `0`
play no role), utility integral converging to `U`, and no Ponzi scheme
`liminf e^{−rT}Q(T) ≥ 0`. -/
def CTAdmissible (u : ℝ × ℝ → ℝ) (r δ Q0 : ℝ) (y i : ℝ → ℝ) (c : ℝ → ℝ × ℝ) (U : ℝ) : Prop :=
  Continuous c ∧ (∀ s, c s ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) ∧
    Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (c s)) atTop (𝓝 U) ∧
    ∀ ε > 0, ∀ᶠ T in atTop, -ε < Real.exp (-r * T) * ctWealth r Q0 y i c T

/-- An optimal continuous-time plan: admissible with value `U`, and every admissible plan has
value at most `U` (O&R p. 748). -/
def CTOptimal (u : ℝ × ℝ → ℝ) (r δ Q0 : ℝ) (y i : ℝ → ℝ) (c : ℝ → ℝ × ℝ) (U : ℝ) : Prop :=
  CTAdmissible u r δ Q0 y i c U ∧ ∀ c' U', CTAdmissible u r δ Q0 y i c' U' → U' ≤ U

/-- The wealth path of a plan solves (11): `Q̇ = rQ + y − C − i m`, with `Q(0) = Q_0`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem ctWealth_hasDerivAt {r Q0 : ℝ} {y i : ℝ → ℝ} {c : ℝ → ℝ × ℝ} (hy : Continuous y)
    (hi : Continuous i) (hc : Continuous c) (t : ℝ) :
    HasDerivAt (ctWealth r Q0 y i c)
      (r * ctWealth r Q0 y i c t + (y t - (c t).1 - i t * (c t).2)) t := by
  have hf : Continuous fun s => y s - (c s).1 - i s * (c s).2 := by
    have h1 : Continuous fun s => (c s).1 := continuous_fst.comp hc
    have h2 : Continuous fun s => (c s).2 := continuous_snd.comp hc
    fun_prop
  exact (variation_of_constants (r := r) (Q0 := Q0) hf).1 t

/-- **The first-order condition for a compactly supported perturbation** (the continuous-time
analogue of the one-period perturbations of §8.3.2): at an optimum, for every continuous
direction `Δ` vanishing outside `[a, b] ⊆ [0, ∞)` that leaves the wealth path unchanged from
some date on, `∫_a^b e^{−δs}(u_C Δ_C + u_{M/P} Δ_m) ds = 0`. Proof: optimality gives
`D(ε) := ∫_a^b e^{−δs}[u(c + εΔ) − u(c)] ≤ 0` for small `|ε|`; concavity gives
`D(ε) ≥ ε G(ε)`, `G(ε) = ∫_a^b e^{−δs}∇u(c + εΔ)·Δ`; and `G` is continuous.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem ct_foc_integral {u uC um : ℝ × ℝ → ℝ} {r δ Q0 U a b : ℝ} {y i : ℝ → ℝ}
    {c Δ : ℝ → ℝ × ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) u)
    (hdiff : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), HasFDerivAt u (grad (uC p) (um p)) p)
    (hcC : ContinuousOn uC (Set.Ioi 0 ×ˢ Set.Ioi 0))
    (hcM : ContinuousOn um (Set.Ioi 0 ×ˢ Set.Ioi 0))
    (hopt : CTOptimal u r δ Q0 y i c U) (hΔ : Continuous Δ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hsupp : ∀ s, s ∉ Set.Ioo a b → Δ s = 0)
    (hw : ∀ ε : ℝ, ∀ᶠ T in atTop,
      ctWealth r Q0 y i (fun s => c s + ε • Δ s) T = ctWealth r Q0 y i c T) :
    ∫ s in a..b, Real.exp (-δ * s) * (uC (c s) * (Δ s).1 + um (c s) * (Δ s).2) = 0 := by
  obtain ⟨⟨hc, hcpos, hU, hnp⟩, hmax⟩ := hopt
  set K := Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) with hK
  have hucont : ContinuousOn u K := fun p hp => (hdiff p hp).continuousAt.continuousWithinAt
  -- a uniform lower bound for the plan on `[a, b]` and a bound for `Δ`
  have hmin : Continuous fun s => min (c s).1 (c s).2 :=
    (continuous_fst.comp hc).min (continuous_snd.comp hc)
  obtain ⟨s1, -, hs1⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hab)
    hmin.continuousOn
  set κ := min (c s1).1 (c s1).2 with hκ
  have hκ0 : 0 < κ := lt_min (hcpos s1).1 (hcpos s1).2
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hΔ.continuousOn (s := Set.Icc a b))
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB a ⟨le_rfl, hab⟩)
  set ε0 := κ / (2 * (B + 1)) with hε0
  have hε00 : 0 < ε0 := by positivity
  have hε0B : ε0 * B < κ := by
    rw [hε0]
    have : κ / (2 * (B + 1)) * B ≤ κ / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hmem : ∀ e : ℝ, |e| ≤ ε0 → ∀ s, c s + e • Δ s ∈ K := by
    intro e he s
    by_cases hs : s ∈ Set.Icc a b
    · have h1 : |(Δ s).1| ≤ B := (norm_fst_le (Δ s)).trans (hB s hs)
      have h2 : |(Δ s).2| ≤ B := (norm_snd_le (Δ s)).trans (hB s hs)
      have hk1 : κ ≤ (c s).1 := (hs1 hs).trans (min_le_left _ _)
      have hk2 : κ ≤ (c s).2 := (hs1 hs).trans (min_le_right _ _)
      have e1 : |e * (Δ s).1| ≤ ε0 * B := by
        rw [abs_mul]; exact mul_le_mul he h1 (abs_nonneg _) hε00.le
      have e2 : |e * (Δ s).2| ≤ ε0 * B := by
        rw [abs_mul]; exact mul_le_mul he h2 (abs_nonneg _) hε00.le
      refine ⟨?_, ?_⟩ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, Set.mem_Ioi]
      · linarith [neg_abs_le (e * (Δ s).1)]
      · linarith [neg_abs_le (e * (Δ s).2)]
    · rw [hsupp s (fun h => hs (Set.Ioo_subset_Icc_self h)), smul_zero, add_zero]
      exact hcpos s
  -- the utility gain of a perturbation
  set D : ℝ → ℝ := fun e => ∫ s in a..b, Real.exp (-δ * s) * (u (c s + e • Δ s) - u (c s))
    with hD
  have hcontU : ∀ e : ℝ, |e| ≤ ε0 → Continuous fun s => u (c s + e • Δ s) := fun e he =>
    hucont.comp_continuous (hc.add (hΔ.const_smul e)) (hmem e he)
  have hcontU0 : Continuous fun s => u (c s) :=
    hucont.comp_continuous hc hcpos
  have hDle : ∀ e : ℝ, |e| ≤ ε0 → D e ≤ 0 := by
    intro e he
    have hge : ∀ T, b ≤ T → ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (c s + e • Δ s) =
        (∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (c s)) + D e := by
      intro T hT
      have i1 : ∀ x y, IntervalIntegrable (fun s => Real.exp (-δ * s) * u (c s + e • Δ s))
          volume x y := fun x y =>
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
          (hcontU e he)).intervalIntegrable x y
      have i2 : ∀ x y, IntervalIntegrable (fun s => Real.exp (-δ * s) * u (c s)) volume x y :=
        fun x y => ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
          hcontU0).intervalIntegrable x y
      have ig : ∀ x y, IntervalIntegrable (fun s => Real.exp (-δ * s) *
          (u (c s + e • Δ s) - u (c s))) volume x y := fun x y =>
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
          ((hcontU e he).sub hcontU0)).intervalIntegrable x y
      have hdiffint : ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * (u (c s + e • Δ s) - u (c s)) =
          D e := by
        have hz : ∀ x y, (∀ s ∈ Set.uIcc x y, s ∉ Set.Ioo a b) →
            ∫ s in x..y, Real.exp (-δ * s) * (u (c s + e • Δ s) - u (c s)) = 0 := by
          intro x y hxy
          rw [← intervalIntegral.integral_zero (a := x) (b := y) (μ := volume) (E := ℝ)]
          refine intervalIntegral.integral_congr fun s hs => ?_
          simp only [hsupp s (hxy s hs), smul_zero, add_zero, sub_self, mul_zero]
        rw [← intervalIntegral.integral_add_adjacent_intervals (ig 0 a) (ig a T),
          ← intervalIntegral.integral_add_adjacent_intervals (ig a b) (ig b T),
          hz 0 a (fun s hs h => by rw [Set.uIcc_of_le ha] at hs; linarith [hs.2, h.1]),
          hz b T (fun s hs h => by
            rw [Set.uIcc_of_le hT] at hs; linarith [hs.1, h.2])]
        simp [hD]
      rw [← hdiffint, ← intervalIntegral.integral_add (i2 0 T) (ig 0 T)]
      congr 1; funext s; ring
    have hlim : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (c s + e • Δ s))
        atTop (𝓝 (U + D e)) :=
      (hU.add_const (D e)).congr' (by
        filter_upwards [eventually_ge_atTop b] with T hT using (hge T hT).symm)
    have hadm : CTAdmissible u r δ Q0 y i (fun s => c s + e • Δ s) (U + D e) := by
      refine ⟨hc.add (hΔ.const_smul e), hmem e he, hlim, fun η hη => ?_⟩
      filter_upwards [hnp η hη, hw e] with T h1 h2
      rw [h2]; exact h1
    have := hmax _ _ hadm
    linarith
  -- the directional derivative of utility, `G`
  set F : ℝ → ℝ → ℝ := fun e s => Real.exp (-δ * s) *
    (uC (c s + e • Δ s) * (Δ s).1 + um (c s + e • Δ s) * (Δ s).2) with hF
  have hexpc : Continuous fun s : ℝ => Real.exp (-δ * s) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hFcont : ∀ e : ℝ, |e| ≤ ε0 → Continuous (F e) := by
    intro e he
    have h1 : Continuous fun s => uC (c s + e • Δ s) :=
      hcC.comp_continuous (hc.add (hΔ.const_smul e)) (hmem e he)
    have h2 : Continuous fun s => um (c s + e • Δ s) :=
      hcM.comp_continuous (hc.add (hΔ.const_smul e)) (hmem e he)
    exact hexpc.mul ((h1.mul (continuous_fst.comp hΔ)).add (h2.mul (continuous_snd.comp hΔ)))
  have hDG : ∀ e : ℝ, |e| ≤ ε0 → e * ∫ s in a..b, F e s ≤ D e := by
    intro e he
    have hpt : ∀ s, e * F e s ≤ Real.exp (-δ * s) * (u (c s + e • Δ s) - u (c s)) := by
      intro s
      have t := concave_le_tangent_gen hconc (hmem e he s) (hcpos s) (hdiff _ (hmem e he s))
      rw [grad_apply] at t
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul] at t
      have hep := Real.exp_pos (-δ * s)
      have : e * (uC (c s + e • Δ s) * (Δ s).1 + um (c s + e • Δ s) * (Δ s).2) ≤
          u (c s + e • Δ s) - u (c s) := by linarith
      calc e * F e s = Real.exp (-δ * s) *
            (e * (uC (c s + e • Δ s) * (Δ s).1 + um (c s + e • Δ s) * (Δ s).2)) := by
            simp only [hF]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this hep.le
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hab
      (((hFcont e he).const_smul e).intervalIntegrable a b)
      ((hexpc.mul ((hcontU e he).sub hcontU0)).intervalIntegrable a b) (fun s _ => hpt s)
  -- continuity of `G` at `0`, through a clamped parameter
  set cl : ℝ → ℝ := fun e => max (-ε0) (min ε0 e) with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_const.min continuous_id)
  have hclb : ∀ e, |cl e| ≤ ε0 := fun e => by
    rw [abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hFc : Continuous (Function.uncurry fun e s => F (cl e) s) := by
    have hpath : Continuous fun p : ℝ × ℝ => c p.2 + cl p.1 • Δ p.2 :=
      (hc.comp continuous_snd).add ((hclc.comp continuous_fst).smul (hΔ.comp continuous_snd))
    have hin : ∀ p : ℝ × ℝ, c p.2 + cl p.1 • Δ p.2 ∈ K := fun p => hmem _ (hclb p.1) p.2
    have h1 := hcC.comp_continuous hpath hin
    have h2 := hcM.comp_continuous hpath hin
    exact (hexpc.comp continuous_snd).mul ((h1.mul (continuous_fst.comp (hΔ.comp
      continuous_snd))).add (h2.mul (continuous_snd.comp (hΔ.comp continuous_snd))))
  have hGt := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hFc a b
  have hcl0 : ∀ᶠ e in 𝓝 (0 : ℝ), cl e = e := by
    filter_upwards [Ioo_mem_nhds (show -ε0 < 0 by linarith) hε00] with e he
    simp only [hcl]
    rw [min_eq_right he.2.le, max_eq_right he.1.le]
  have hGcont : ContinuousAt (fun e => ∫ s in a..b, F e s) 0 := by
    have h := hGt.continuousAt (x := 0)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hcl0] with e he
    simp only [he]
  have hG0 : (fun e => ∫ s in a..b, F e s) 0 =
      ∫ s in a..b, Real.exp (-δ * s) * (uC (c s) * (Δ s).1 + um (c s) * (Δ s).2) := by
    simp [hF]
  have hsmall : ∀ᶠ e in 𝓝 (0 : ℝ), |e| ≤ ε0 := by
    filter_upwards [Ioo_mem_nhds (show -ε0 < 0 by linarith) hε00] with e he
    rw [abs_le]; exact ⟨he.1.le, he.2.le⟩
  have hright : ∀ᶠ e in 𝓝[>] (0 : ℝ), (fun e => ∫ s in a..b, F e s) e ≤ 0 := by
    filter_upwards [nhdsWithin_le_nhds hsmall, self_mem_nhdsWithin] with e he hpos
    have h1 := (hDG e he).trans (hDle e he)
    simp only [Set.mem_Ioi] at hpos
    by_contra hc'
    push Not at hc'
    nlinarith
  have hleft : ∀ᶠ e in 𝓝[<] (0 : ℝ), 0 ≤ (fun e => ∫ s in a..b, F e s) e := by
    filter_upwards [nhdsWithin_le_nhds hsmall, self_mem_nhdsWithin] with e he hneg
    have h1 := (hDG e he).trans (hDle e he)
    simp only [Set.mem_Iio] at hneg
    by_contra hc'
    push Not at hc'
    nlinarith
  have h1 := le_of_tendsto (hGcont.tendsto.mono_left nhdsWithin_le_nhds) hright
  have h2 := ge_of_tendsto (hGcont.tendsto.mono_left nhdsWithin_le_nhds) hleft
  rw [← hG0]
  exact le_antisymm h1 h2


/-- A tent function, positive exactly on `(a, b)`: the bump used for the perturbations.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
noncomputable def tent (a b s : ℝ) : ℝ := max 0 (min (s - a) (b - s))

/-- The tent is continuous.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem tent_continuous (a b : ℝ) : Continuous (tent a b) :=
  continuous_const.max ((continuous_id.sub continuous_const).min
    (continuous_const.sub continuous_id))

/-- The tent is nonnegative.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem tent_nonneg (a b s : ℝ) : 0 ≤ tent a b s := le_max_left _ _

/-- The tent vanishes outside `(a, b)`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem tent_eq_zero {a b s : ℝ} (hs : s ∉ Set.Ioo a b) : tent a b s = 0 := by
  unfold tent
  apply max_eq_left
  simp only [Set.mem_Ioo, not_and_or, not_lt] at hs
  rcases hs with h | h
  · exact (min_le_left _ _).trans (by linarith)
  · exact (min_le_right _ _).trans (by linarith)

/-- The tent is positive on `(a, b)`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem tent_pos {a b s : ℝ} (hs : s ∈ Set.Ioo a b) : 0 < tent a b s :=
  lt_of_lt_of_le (lt_min (by linarith [hs.1]) (by linarith [hs.2])) (le_max_right _ _)

/-- A continuous function that is nonnegative on `[a, b]` and positive at an interior point has
positive integral over `[a, b]`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem integral_pos_of_pos_at {f : ℝ → ℝ} {a b s0 : ℝ} (hf : Continuous f)
    (hnn : ∀ s ∈ Set.Icc a b, 0 ≤ f s) (hs0 : s0 ∈ Set.Ioo a b) (hpos : 0 < f s0) :
    0 < ∫ s in a..b, f s := by
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1
    (hf.continuousAt.eventually (lt_mem_nhds hpos))
  set η' := min (η / 2) (min ((s0 - a) / 2) ((b - s0) / 2)) with hη'
  have hη'0 : 0 < η' := lt_min (by linarith) (lt_min (by linarith [hs0.1]) (by linarith [hs0.2]))
  have h1 : η' ≤ (s0 - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have h2 : η' ≤ (b - s0) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have h3 : η' ≤ η / 2 := min_le_left _ _
  have hsub : 0 < ∫ s in (s0 - η')..(s0 + η'), f s := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hf.intervalIntegrable _ _)
      (fun s hs => hball ?_) (by linarith)
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2]
  have hmono := intervalIntegral.integral_mono_interval (f := f) (μ := volume)
    (show a ≤ s0 - η' by linarith) (show s0 - η' ≤ s0 + η' by linarith)
    (show s0 + η' ≤ b by linarith)
    (by
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall fun s hs => hnn s ⟨hs.1.le, hs.2⟩)
    (hf.intervalIntegrable _ _)
  linarith

/-- **Necessity of (8), the money-demand condition** (O&R Supplement (8), p. 746, derived from
optimality rather than as the `h → 0` limit): at a continuous-time optimum,
`u_{M/P}(c_s) = i_s u_C(c_s)` at every date `s ≥ 0`. Proof: perturb along `(−i, 1)` with weight
`φ(s)(u_{M/P} − i u_C)(c_s)` (φ a tent); wealth is unchanged and `ct_foc_integral` gives
`∫ e^{−δs} φ (u_{M/P} − i u_C)² = 0`. -/
theorem ct_money_foc {u uC um : ℝ × ℝ → ℝ} {r δ Q0 U : ℝ} {y i : ℝ → ℝ} {c : ℝ → ℝ × ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) u)
    (hdiff : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), HasFDerivAt u (grad (uC p) (um p)) p)
    (hcC : ContinuousOn uC (Set.Ioi 0 ×ˢ Set.Ioi 0))
    (hcM : ContinuousOn um (Set.Ioi 0 ×ˢ Set.Ioi 0)) (hi : Continuous i)
    (hopt : CTOptimal u r δ Q0 y i c U) {s0 : ℝ} (hs0 : 0 ≤ s0) :
    um (c s0) = i s0 * uC (c s0) := by
  have hc := hopt.1.1
  have hcpos := hopt.1.2.1
  set g : ℝ → ℝ := fun s => um (c s) - i s * uC (c s) with hg
  have hgc : Continuous g :=
    (hcM.comp_continuous hc hcpos).sub (hi.mul (hcC.comp_continuous hc hcpos))
  have key : ∀ s0, 0 < s0 → g s0 = 0 := by
    intro s0 hs0
    have ha0 : 0 < s0 / 2 := by positivity
    set Δ : ℝ → ℝ × ℝ := fun s =>
      (tent (s0 / 2) (3 * s0 / 2) s * g s) • ((-i s, 1) : ℝ × ℝ) with hΔ
    have hΔc : Continuous Δ :=
      ((tent_continuous (s0 / 2) (3 * s0 / 2)).mul hgc).smul ((hi.neg).prodMk continuous_const)
    have hsupp : ∀ s, s ∉ Set.Ioo (s0 / 2) (3 * s0 / 2) → Δ s = 0 := fun s hs => by
      simp [hΔ, tent_eq_zero hs]
    have hw : ∀ ε : ℝ, ∀ᶠ T in atTop,
        ctWealth r Q0 y i (fun s => c s + ε • Δ s) T = ctWealth r Q0 y i c T := by
      intro ε
      refine Eventually.of_forall fun T => ?_
      unfold ctWealth
      congr 2
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [hΔ, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    have hfoc := ct_foc_integral hconc hdiff hcC hcM hopt hΔc ha0.le
      (by linarith) hsupp hw
    have heq : ∀ s, Real.exp (-δ * s) * (uC (c s) * (Δ s).1 + um (c s) * (Δ s).2) =
        Real.exp (-δ * s) * tent (s0 / 2) (3 * s0 / 2) s * g s ^ 2 := fun s => by
      simp only [hΔ, hg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    simp only [heq] at hfoc
    by_contra hne
    have hpos : 0 < Real.exp (-δ * s0) * tent (s0 / 2) (3 * s0 / 2) s0 * g s0 ^ 2 := by
      have := tent_pos (a := s0 / 2) (b := 3 * s0 / 2) (s := s0) ⟨by linarith, by linarith⟩
      have := pow_pos (abs_pos.2 hne) 2
      rw [sq_abs] at this
      positivity
    have hcont : Continuous fun s => Real.exp (-δ * s) * tent (s0 / 2) (3 * s0 / 2) s *
        g s ^ 2 :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (tent_continuous (s0 / 2) (3 * s0 / 2))).mul (hgc.pow 2)
    have := integral_pos_of_pos_at (a := s0 / 2) (b := 3 * s0 / 2) hcont
      (fun s _ => mul_nonneg (mul_nonneg (Real.exp_pos _).le (tent_nonneg _ _ s)) (sq_nonneg _))
      ⟨by linarith, by linarith⟩ hpos
    linarith
  rcases hs0.lt_or_eq with hlt | heq
  · have := key s0 hlt; simp only [hg] at this; linarith
  · subst heq
    have h1 : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := hgc.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
    have h2 : Tendsto g (𝓝[>] 0) (𝓝 0) := tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with s hs using (key s hs).symm)
    have := tendsto_nhds_unique h1 h2
    simp only [hg] at this
    linarith

/-- A continuous function vanishing outside `(a, b) ⊆ [0, T]` has the same integral over `[0, T]`
as over `[a, b]`.
Context: O&R Supplement A to Ch. 8, pp. 745–753. -/
theorem integral_eq_of_vanish {g : ℝ → ℝ} {a b T : ℝ} (hg : Continuous g) (ha : 0 ≤ a)
    (hbT : b ≤ T) (hz : ∀ s, s ∉ Set.Ioo a b → g s = 0) :
    ∫ s in (0 : ℝ)..T, g s = ∫ s in a..b, g s := by
  have hz' : ∀ x y, (∀ s ∈ Set.uIcc x y, s ∉ Set.Ioo a b) → ∫ s in x..y, g s = 0 := by
    intro x y hxy
    rw [← intervalIntegral.integral_zero (a := x) (b := y) (μ := volume) (E := ℝ)]
    exact intervalIntegral.integral_congr fun s hs => hz s (hxy s hs)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable 0 a)
      (hg.intervalIntegrable a T),
    ← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable a b)
      (hg.intervalIntegrable b T),
    hz' 0 a (fun s hs h => by rw [Set.uIcc_of_le ha] at hs; linarith [hs.2, h.1]),
    hz' b T (fun s hs h => by rw [Set.uIcc_of_le hbT] at hs; linarith [hs.1, h.2])]
  ring

/-- **Necessity of (3)–(9), the costate equation** (O&R Supplement (9), p. 747, derived from
optimality): at a continuous-time optimum, `e^{(r−δ)s}u_C(c_s)` is constant on `[0, ∞)`, i.e.
the marginal utility of consumption `λ(s) = u_C(c_s)` equals `λ(0)e^{(δ−r)s}`, so
`λ̇ = λ(δ − r)`. Proof: perturb consumption by `e^{rs}φ(s)(h(s) − A)` with `∫φ(h − A) = 0`
(wealth unchanged after the perturbation), which by `ct_foc_integral` forces
`∫φ(h − A)² = 0`. -/
theorem ct_costate_of_optimal {u uC um : ℝ × ℝ → ℝ} {r δ Q0 U : ℝ} {y i : ℝ → ℝ}
    {c : ℝ → ℝ × ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) u)
    (hdiff : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), HasFDerivAt u (grad (uC p) (um p)) p)
    (hcC : ContinuousOn uC (Set.Ioi 0 ×ˢ Set.Ioi 0))
    (hcM : ContinuousOn um (Set.Ioi 0 ×ˢ Set.Ioi 0)) (hy : Continuous y) (hi : Continuous i)
    (hopt : CTOptimal u r δ Q0 y i c U) {s : ℝ} (hs : 0 ≤ s) :
    uC (c s) = uC (c 0) * Real.exp ((δ - r) * s) := by
  have hc := hopt.1.1
  have hcpos := hopt.1.2.1
  set h : ℝ → ℝ := fun s => Real.exp ((r - δ) * s) * uC (c s) with hh
  have hhc : Continuous h :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (hcC.comp_continuous hc hcpos)
  have hexpc : ∀ k : ℝ, Continuous fun s : ℝ => Real.exp (k * s) := fun k =>
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have claim : ∀ a b, 0 < a → a < b → ∀ s ∈ Set.Ioo a b,
      h s = (∫ t in a..b, tent a b t * h t) / ∫ t in a..b, tent a b t := by
    intro a b ha hab s hsab
    have hφc := tent_continuous a b
    have hΦ : 0 < ∫ t in a..b, tent a b t :=
      integral_pos_of_pos_at hφc (fun t _ => tent_nonneg a b t)
        ⟨show a < (a + b) / 2 by linarith, show (a + b) / 2 < b by linarith⟩
        (tent_pos ⟨by linarith, by linarith⟩)
    set A := (∫ t in a..b, tent a b t * h t) / ∫ t in a..b, tent a b t with hA
    set ψ : ℝ → ℝ := fun t => tent a b t * (h t - A) with hψ
    have hψc : Continuous ψ := hφc.mul (hhc.sub continuous_const)
    have hψz : ∀ t, t ∉ Set.Ioo a b → ψ t = 0 := fun t ht => by simp [hψ, tent_eq_zero ht]
    have hψint : ∫ t in a..b, ψ t = 0 := by
      have e : ∀ t, ψ t = tent a b t * h t - A * tent a b t := fun t => by simp only [hψ]; ring
      simp only [e]
      rw [show (∫ t in a..b, tent a b t * h t - A * tent a b t) =
          (∫ t in a..b, tent a b t * h t) - ∫ t in a..b, A * tent a b t from
        intervalIntegral.integral_sub ((hφc.mul hhc).intervalIntegrable a b)
          ((hφc.intervalIntegrable a b).const_mul A), intervalIntegral.integral_const_mul, hA]
      field_simp
      ring
    set Δ : ℝ → ℝ × ℝ := fun t => (Real.exp (r * t) * ψ t, 0) with hΔ
    have hΔc : Continuous Δ := ((hexpc r).mul hψc).prodMk continuous_const
    have hsupp : ∀ t, t ∉ Set.Ioo a b → Δ t = 0 := fun t ht => by
      simp [hΔ, hψz t ht]
    have hw : ∀ ε : ℝ, ∀ᶠ T in atTop,
        ctWealth r Q0 y i (fun t => c t + ε • Δ t) T = ctWealth r Q0 y i c T := by
      intro ε
      filter_upwards [eventually_ge_atTop b] with T hT
      unfold ctWealth
      have hcf : Continuous fun t => Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2) := by
        have h1 := continuous_fst.comp hc
        have h2 := continuous_snd.comp hc
        exact (hexpc (-r)).mul ((hy.sub h1).sub (hi.mul h2))
      have hpt : ∀ t, Real.exp (-r * t) * (y t - (c t + ε • Δ t).1 - i t * (c t + ε • Δ t).2) =
          Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2) - ε * ψ t := by
        intro t
        simp only [hΔ, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          mul_zero, add_zero]
        have : Real.exp (-r * t) * Real.exp (r * t) = 1 := by rw [← Real.exp_add]; simp
        linear_combination (-(ε * ψ t)) * this
      congr 2
      simp only [hpt]
      rw [show (∫ t in (0 : ℝ)..T, Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2) -
          ε * ψ t) = (∫ t in (0 : ℝ)..T, Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2)) -
          ∫ t in (0 : ℝ)..T, ε * ψ t from
        intervalIntegral.integral_sub (hcf.intervalIntegrable 0 T)
          ((hψc.intervalIntegrable 0 T).const_mul ε),
        intervalIntegral.integral_const_mul, integral_eq_of_vanish hψc ha.le hT hψz, hψint]
      ring
    have hfoc := ct_foc_integral hconc hdiff hcC hcM hopt hΔc ha.le hab.le hsupp hw
    have e1 : ∀ t, Real.exp (-δ * t) * (uC (c t) * (Δ t).1 + um (c t) * (Δ t).2) =
        h t * ψ t := fun t => by
      simp only [hΔ, hh, mul_zero, add_zero]
      have : Real.exp (-δ * t) * Real.exp (r * t) = Real.exp ((r - δ) * t) := by
        rw [← Real.exp_add]; ring_nf
      linear_combination uC (c t) * ψ t * this
    simp only [e1] at hfoc
    have hsq : ∫ t in a..b, tent a b t * (h t - A) ^ 2 = 0 := by
      have e2 : ∀ t, tent a b t * (h t - A) ^ 2 = h t * ψ t - A * ψ t := fun t => by
        simp only [hψ]; ring
      simp only [e2]
      rw [show (∫ t in a..b, h t * ψ t - A * ψ t) =
          (∫ t in a..b, h t * ψ t) - ∫ t in a..b, A * ψ t from
        intervalIntegral.integral_sub ((hhc.mul hψc).intervalIntegrable a b)
          ((hψc.intervalIntegrable a b).const_mul A), intervalIntegral.integral_const_mul, hfoc,
        hψint]
      ring
    by_contra hne
    have hpos : 0 < tent a b s * (h s - A) ^ 2 := by
      have := tent_pos hsab
      have := pow_pos (abs_pos.2 (sub_ne_zero.2 hne)) 2
      rw [sq_abs] at this
      positivity
    have hcont : Continuous fun t => tent a b t * (h t - A) ^ 2 :=
      hφc.mul ((hhc.sub continuous_const).pow 2)
    have := integral_pos_of_pos_at hcont
      (fun t _ => mul_nonneg (tent_nonneg a b t) (sq_nonneg _)) hsab hpos
    linarith
  -- `h` is constant on `(0, ∞)`
  have hconst : ∀ s1 s2, 0 < s1 → 0 < s2 → h s1 = h s2 := by
    intro s1 s2 h1 h2
    set a := min s1 s2 / 2
    set b := max s1 s2 + 1
    have ha : 0 < a := by positivity
    have hab : a < b := by
      have := min_le_max (a := s1) (b := s2)
      have := lt_min h1 h2
      simp only [a, b]; linarith
    have m1 : s1 ∈ Set.Ioo a b := ⟨by
      have := min_le_left s1 s2; have := lt_min h1 h2; simp only [a]; linarith, by
      have := le_max_left s1 s2; simp only [b]; linarith⟩
    have m2 : s2 ∈ Set.Ioo a b := ⟨by
      have := min_le_right s1 s2; have := lt_min h1 h2; simp only [a]; linarith, by
      have := le_max_right s1 s2; simp only [b]; linarith⟩
    rw [claim a b ha hab s1 m1, claim a b ha hab s2 m2]
  have h0 : h 0 = h 1 := by
    have t1 : Tendsto h (𝓝[>] 0) (𝓝 (h 0)) :=
      hhc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have t2 : Tendsto h (𝓝[>] 0) (𝓝 (h 1)) := tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with t ht using hconst 1 t one_pos ht)
    exact tendsto_nhds_unique t1 t2
  have hs' : h s = h 0 := by
    rcases hs.lt_or_eq with hlt | heq
    · rw [h0]; exact hconst s 1 hlt one_pos
    · rw [← heq]
  simp only [hh, mul_zero, Real.exp_zero, one_mul] at hs'
  have e : Real.exp ((r - δ) * s) * Real.exp ((δ - r) * s) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  calc uC (c s) = (Real.exp ((r - δ) * s) * uC (c s)) * Real.exp ((δ - r) * s) := by
        linear_combination (-(uC (c s))) * e
    _ = _ := by rw [hs']

/-- **Necessity of the transversality condition in the monetary problem** (O&R Supplement (15)–(16),
p. 750, derived from optimality): with `u_C > 0`, an optimal plan has
`liminf e^{−rT}Q(T) ≤ 0` (so, with the no-Ponzi condition, `liminf = 0`). Otherwise wealth would
eventually exceed `η > 0` in present value, and consuming `κφ(s)` more on `(0, 1)`
(`φ` a tent, `κ ∫₀¹e^{−rs}φ = η`) would keep the no-Ponzi condition and raise utility. -/
theorem ct_tvc_of_optimal {u uC um : ℝ × ℝ → ℝ} {r δ Q0 U : ℝ} {y i : ℝ → ℝ}
    {c : ℝ → ℝ × ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) u)
    (hdiff : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), HasFDerivAt u (grad (uC p) (um p)) p)
    (huC : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), 0 < uC p) (hy : Continuous y)
    (hi : Continuous i) (hopt : CTOptimal u r δ Q0 y i c U) :
    ∀ ε > 0, ∃ᶠ T in atTop, Real.exp (-r * T) * ctWealth r Q0 y i c T < ε := by
  obtain ⟨⟨hc, hcpos, hU, _⟩, hmax⟩ := hopt
  intro η hη
  by_contra hcon
  rw [not_frequently] at hcon
  set K := Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) with hK
  have hucont : ContinuousOn u K := fun p hp => (hdiff p hp).continuousAt.continuousWithinAt
  have hexpc : ∀ k : ℝ, Continuous fun s : ℝ => Real.exp (k * s) := fun k =>
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hφc := tent_continuous 0 1
  set Φ := ∫ s in (0 : ℝ)..1, Real.exp (-r * s) * tent 0 1 s with hΦ
  have hΦ0 : 0 < Φ := integral_pos_of_pos_at ((hexpc (-r)).mul hφc)
    (fun s _ => mul_nonneg (Real.exp_pos _).le (tent_nonneg 0 1 s))
    ⟨show (0 : ℝ) < 1 / 2 by norm_num, show (1 : ℝ) / 2 < 1 by norm_num⟩
    (mul_pos (Real.exp_pos _) (tent_pos ⟨by norm_num, by norm_num⟩))
  set κ := η / Φ with hκ
  have hκ0 : 0 < κ := div_pos hη hΦ0
  set c' : ℝ → ℝ × ℝ := fun s => c s + ((κ * tent 0 1 s, 0) : ℝ × ℝ) with hc'
  have hc'c : Continuous c' := hc.add ((continuous_const.mul hφc).prodMk continuous_const)
  have hc'pos : ∀ s, c' s ∈ K := fun s => by
    refine ⟨?_, ?_⟩ <;> simp only [hc', Prod.fst_add, Prod.snd_add, add_zero, Set.mem_Ioi]
    · have := (hcpos s).1; have := tent_nonneg 0 1 s; simp only [Set.mem_Ioi] at *; nlinarith
    · exact (hcpos s).2
  -- the rival's utility
  set g : ℝ → ℝ := fun s => Real.exp (-δ * s) * (u (c' s) - u (c s)) with hg
  have hgc : Continuous g :=
    (hexpc (-δ)).mul ((hucont.comp_continuous hc'c hc'pos).sub (hucont.comp_continuous hc hcpos))
  have hgz : ∀ s, s ∉ Set.Ioo 0 1 → g s = 0 := fun s hs => by
    simp [hg, hc', tent_eq_zero hs, Prod.mk_zero_zero]
  have hlim : Tendsto (fun T => ∫ s in (0 : ℝ)..T, Real.exp (-δ * s) * u (c' s)) atTop
      (𝓝 (U + ∫ s in (0 : ℝ)..1, g s)) := by
    refine (hU.add_const _).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    have i1 : IntervalIntegrable (fun s => Real.exp (-δ * s) * u (c s)) volume 0 T :=
      ((hexpc (-δ)).mul (hucont.comp_continuous hc hcpos)).intervalIntegrable 0 T
    rw [← integral_eq_of_vanish hgc le_rfl hT hgz, ← intervalIntegral.integral_add i1
      (hgc.intervalIntegrable 0 T)]
    congr 1; funext s; simp only [hg]; ring
  -- the rival's wealth
  have hwealth : ∀ T, 1 ≤ T → Real.exp (-r * T) * ctWealth r Q0 y i c' T =
      Real.exp (-r * T) * ctWealth r Q0 y i c T - η := by
    intro T hT
    have hcf : Continuous fun t => Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2) :=
      (hexpc (-r)).mul ((hy.sub (continuous_fst.comp hc)).sub (hi.mul (continuous_snd.comp hc)))
    have hk : Continuous fun t => Real.exp (-r * t) * tent 0 1 t := (hexpc (-r)).mul hφc
    have hpt : ∀ t, Real.exp (-r * t) * (y t - (c' t).1 - i t * (c' t).2) =
        Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2) - κ * (Real.exp (-r * t) *
          tent 0 1 t) := fun t => by
      simp only [hc', Prod.fst_add, Prod.snd_add, add_zero]; ring
    have hvan : ∀ t, t ∉ Set.Ioo 0 1 → Real.exp (-r * t) * tent 0 1 t = 0 := fun t ht => by
      rw [tent_eq_zero ht, mul_zero]
    unfold ctWealth
    simp only [hpt]
    rw [show (∫ t in (0 : ℝ)..T, Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2) -
        κ * (Real.exp (-r * t) * tent 0 1 t)) =
        (∫ t in (0 : ℝ)..T, Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2)) -
        ∫ t in (0 : ℝ)..T, κ * (Real.exp (-r * t) * tent 0 1 t) from
      intervalIntegral.integral_sub (hcf.intervalIntegrable 0 T)
        ((hk.intervalIntegrable 0 T).const_mul κ),
      intervalIntegral.integral_const_mul, integral_eq_of_vanish hk le_rfl hT hvan, ← hΦ]
    have e : Real.exp (-r * T) * Real.exp (r * T) = 1 := by rw [← Real.exp_add]; simp
    have hκΦ : κ * Φ = η := by rw [hκ]; field_simp
    linear_combination (Q0 + (∫ t in (0 : ℝ)..T, Real.exp (-r * t) *
      (y t - (c t).1 - i t * (c t).2)) - κ * Φ) * e - hκΦ +
      (-(Q0 + ∫ t in (0 : ℝ)..T, Real.exp (-r * t) * (y t - (c t).1 - i t * (c t).2))) * e
  have hadm : CTAdmissible u r δ Q0 y i c' (U + ∫ s in (0 : ℝ)..1, g s) := by
    refine ⟨hc'c, hc'pos, hlim, fun e he => ?_⟩
    filter_upwards [hcon, eventually_ge_atTop 1] with T hT hT1
    push Not at hT
    rw [hwealth T hT1]
    linarith
  have hle := hmax _ _ hadm
  -- the utility gain is strictly positive
  have hgnn : ∀ s, 0 ≤ g s := by
    intro s
    have t := concave_le_tangent_gen hconc (hc'pos s) (hcpos s) (hdiff _ (hc'pos s))
    rw [grad_apply] at t
    simp only [hc', Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at t
    have h1 : 0 < uC (c s + (κ * tent 0 1 s, 0)) := huC _ (hc'pos s)
    have h2 := tent_nonneg 0 1 s
    simp only [hg]
    have : 0 ≤ u (c s + (κ * tent 0 1 s, 0)) - u (c s) := by
      nlinarith [mul_nonneg (mul_nonneg h1.le hκ0.le) h2]
    exact mul_nonneg (Real.exp_pos _).le this
  have hgpos : 0 < g (1 / 2) := by
    have t := concave_le_tangent_gen hconc (hc'pos (1 / 2)) (hcpos (1 / 2))
      (hdiff _ (hc'pos (1 / 2)))
    rw [grad_apply] at t
    simp only [hc', Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at t
    have h1 : 0 < uC (c (1 / 2) + (κ * tent 0 1 (1 / 2), 0)) := huC _ (hc'pos (1 / 2))
    have h2 := tent_pos (a := 0) (b := 1) (s := 1 / 2) ⟨by norm_num, by norm_num⟩
    simp only [hg]
    have : 0 < u (c (1 / 2) + (κ * tent 0 1 (1 / 2), 0)) - u (c (1 / 2)) := by
      have := mul_pos (mul_pos h1 hκ0) h2
      nlinarith
    exact mul_pos (Real.exp_pos _) this
  have := integral_pos_of_pos_at hgc (fun s _ => hgnn s)
    ⟨show (0 : ℝ) < 1 / 2 by norm_num, show (1 : ℝ) / 2 < 1 by norm_num⟩ hgpos
  linarith

/-- **The maximum principle for the monetary problem, necessary AND sufficient** (O&R Supplement
A.1–A.3, pp. 745–750, made precise): with `u` concave, continuously differentiable and
`u_C > 0` on the positive quadrant, an admissible continuous-time plan is optimal IFF, at every
date `s ≥ 0`, (8) `u_{M/P} = i u_C` and (3)+(9) `u_C(c_s) = u_C(c_0)e^{(δ−r)s}` hold, and the
transversality condition `liminf e^{−rT}Q(T) = 0` holds (the `≥` half being the no-Ponzi
condition built into admissibility). -/
theorem monetary_optimal_iff {u uC um : ℝ × ℝ → ℝ} {r δ Q0 U : ℝ} {y i : ℝ → ℝ}
    {c : ℝ → ℝ × ℝ}
    (hconc : ConcaveOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) u)
    (hdiff : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), HasFDerivAt u (grad (uC p) (um p)) p)
    (hcC : ContinuousOn uC (Set.Ioi 0 ×ˢ Set.Ioi 0))
    (hcM : ContinuousOn um (Set.Ioi 0 ×ˢ Set.Ioi 0))
    (huC : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), 0 < uC p) (hy : Continuous y)
    (hi : Continuous i) (hadm : CTAdmissible u r δ Q0 y i c U) :
    CTOptimal u r δ Q0 y i c U ↔
      (∀ s, 0 ≤ s → um (c s) = i s * uC (c s)) ∧
      (∀ s, 0 ≤ s → uC (c s) = uC (c 0) * Real.exp ((δ - r) * s)) ∧
      ∀ ε > 0, ∃ᶠ T in atTop, Real.exp (-r * T) * ctWealth r Q0 y i c T < ε := by
  constructor
  · intro hopt
    exact ⟨fun s hs => ct_money_foc hconc hdiff hcC hcM hi hopt hs,
      fun s hs => ct_costate_of_optimal hconc hdiff hcC hcM hy hi hopt hs,
      ct_tvc_of_optimal hconc hdiff huC hy hi hopt⟩
  · rintro ⟨hM, hlamc, htvc⟩
    refine ⟨hadm, fun c' U' hadm' => ?_⟩
    obtain ⟨hc, hcpos, hU, _⟩ := hadm
    obtain ⟨hc', hc'pos, hU', hnp'⟩ := hadm'
    set lam : ℝ → ℝ := fun s => uC (c 0) * Real.exp ((δ - r) * s) with hlam
    have hlamd : ∀ s, HasDerivAt lam (lam s * (δ - r)) s := by
      intro s
      have := (((hasDerivAt_id s).const_mul (δ - r)).exp).const_mul (uC (c 0))
      simp only [id, mul_one] at this
      refine this.congr_deriv ?_
      simp only [hlam]; ring
    have hlam0 : 0 < lam 0 := by simp only [hlam, mul_zero, Real.exp_zero, mul_one]
                                 exact huC _ (hcpos 0)
    have hucont : ContinuousOn u (Set.Ioi 0 ×ˢ Set.Ioi 0) := fun p hp =>
      (hdiff p hp).continuousAt.continuousWithinAt
    have hexpc : Continuous fun s : ℝ => Real.exp (-δ * s) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    exact monetary_sufficiency (lam := lam) (y := y) (i := i) (r := r) (δ := δ)
      (Qs := ctWealth r Q0 y i c)
      (Q := ctWealth r Q0 y i c') hconc hdiff (fun s _ => hcpos s) (fun s _ => hc'pos s)
      (fun s hs => hlamc s hs) (fun s hs => by rw [hM s hs, hlamc s hs]; ring) hlamd hlam0
      (fun s => (ctWealth_hasDerivAt hy hi hc s).congr_deriv (by ring))
      (fun s => (ctWealth_hasDerivAt hy hi hc' s).congr_deriv (by ring))
      (by simp [ctWealth]) (monetary_boundary htvc hnp')
      (fun T => (hexpc.mul (hucont.comp_continuous hc' hc'pos)).intervalIntegrable 0 T)
      (fun T => (hexpc.mul (hucont.comp_continuous hc hcpos)).intervalIntegrable 0 T) hU' hU

end ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Nominal asset pricing in a stochastic global monetary equilibrium

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §8.7.1–8.7.4,
pp. 579–585.

Uncertainty is a finite-state Markov chain. Histories (nodes of the event tree) are pairs
`(current state, list of past states)`; the conditional expectation `E_t` is the one-step
operator `oneStep`, and `E_t X_{t+n}` is its `n`-fold iterate `iterStep`.

* Finite probability spaces: expectation, covariance, variance (`FinProb`).
* Euler equations for any asset (93), nominal bonds (95), real bonds (96) and money (98):
  each is NECESSARY (a one-period reallocation cannot raise utility at an optimum) and
  SUFFICIENT (with concave utility, no such reallocation raises utility).
* (97): the certainty-equivalence Fisher equation holds IF AND ONLY IF inflation and
  marginal utility are conditionally uncorrelated (the book says "only if").
* `v′/u′ = i/(1+i)` from (95) and (98).
* (94): proportional CRRA marginal utilities imply constant consumption shares of world
  output.
* (99): with CRRA/log utility, the money Euler equation is EXACTLY LINEAR in the
  output-adjusted real balances `w = M/(P (xY)^ρ)`: `w_t = 1 + γ E_t[w_{t+1}/ε_{t+1}]`,
  `γ = β/(1+μ)`.
* (100)–(101): with `E_t[1/ε] = 1` and `ε > 0` (the book says "nonnegative", which is not
  enough) the constant `ω = (1+μ)/(1+μ−β)` is the unique bounded solution along the whole
  event tree; every positive solution is `ω` plus a NONNEGATIVE bubble; bubbles exist; no
  positive solution exists at all when `1+μ ≤ β`; the transversality condition rules
  bubbles out when `(1+μ) min ε ≥ 1` (so `μ ≥ 0` in the deterministic case) but NOT when
  `μ < 0`. Consequences: the price-level formula, `1+i = (1+μ)/β`, and independence of the
  price level from expected future output.
* The log-linearised model of §8.7.3 is a stochastic Cagan equation; its fundamental
  solution exists (given summability) and is the unique no-bubble solution.
* §8.7.4: the stochastic cash-in-advance model (103).
* The infinite-horizon household problem on the event tree (`Household`): budget constraints
  with an arbitrary finite asset menu (money, nominal and real bonds, output claims); the Euler
  equations plus the stochastic transversality condition are SUFFICIENT for optimality against
  every feasible, positive, no-Ponzi rival (supporting hyperplane summed over the tree), and
  the Euler equations are NECESSARY at every node reached with positive probability.
* `Equilibrium87`: the §8.7 equilibrium plan (`C = xY^W`, money path with `M/P = ω(xY^W)^ρ`,
  no bonds, fund share `x`) satisfies every Euler equation and the transversality condition
  (derived, not assumed), hence is optimal for each household.
-/

namespace ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing

open Finset Filter Topology

/-! ## Finite probability spaces -/

/-- A probability distribution on a finite set of states (O&R §8.7, p. 579: the book's
random outputs and money supplies take finitely many values here). -/
structure FinProb (S : Type) [Fintype S] where
  prob : S → ℝ
  prob_nonneg : ∀ s, 0 ≤ prob s
  prob_sum : ∑ s, prob s = 1

namespace FinProb

variable {S : Type} [Fintype S] (Ω : FinProb S)

/-- Expectation `E[X] = Σ π(s) X(s)` (O&R §8.7, p. 579). -/
def expect (X : S → ℝ) : ℝ := ∑ s, Ω.prob s * X s

/-- Covariance `Cov(X, Y) = E[XY] − E[X]E[Y]` (O&R §8.7.2, p. 581). -/
def cov (X Y : S → ℝ) : ℝ := Ω.expect (fun s => X s * Y s) - Ω.expect X * Ω.expect Y

/-- Variance `Var(X) = Cov(X, X)` (O&R §8.7.5, p. 587). -/
def var (X : S → ℝ) : ℝ := Ω.cov X X

/-- The expectation of a constant is the constant (O&R §8.7). -/
theorem expect_const (c : ℝ) : Ω.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, Ω.prob_sum]

/-- Expectation is additive (O&R §8.7). -/
theorem expect_add (X Y : S → ℝ) :
    Ω.expect (fun s => X s + Y s) = Ω.expect X + Ω.expect Y := by
  simp [expect, mul_add, Finset.sum_add_distrib]

/-- Expectation respects subtraction (O&R §8.7). -/
theorem expect_sub (X Y : S → ℝ) :
    Ω.expect (fun s => X s - Y s) = Ω.expect X - Ω.expect Y := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

/-- Known (date-`t`) factors come out of the expectation (O&R (117), p. 591). -/
theorem expect_mul_left (c : ℝ) (X : S → ℝ) :
    Ω.expect (fun s => c * X s) = c * Ω.expect X := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Expectation is monotone (O&R §8.7). -/
theorem expect_mono {X Y : S → ℝ} (h : ∀ s, X s ≤ Y s) : Ω.expect X ≤ Ω.expect Y :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (Ω.prob_nonneg s)

/-- Some state has positive probability (O&R §8.7). -/
theorem exists_prob_pos : ∃ s, 0 < Ω.prob s := by
  by_contra hc
  push Not at hc
  have : ∑ s, Ω.prob s ≤ 0 := Finset.sum_nonpos fun s _ => hc s
  linarith [Ω.prob_sum]

/-- A strictly positive random variable has strictly positive expectation (O&R §8.7.2,
p. 581: `E_t u′(C_{t+1}) > 0`). -/
theorem expect_pos {X : S → ℝ} (h : ∀ s, 0 < X s) : 0 < Ω.expect X := by
  obtain ⟨s, hs⟩ := Ω.exists_prob_pos
  have hle : Ω.prob s * X s ≤ ∑ t, Ω.prob t * X t :=
    Finset.single_le_sum (f := fun t => Ω.prob t * X t)
      (fun t _ => mul_nonneg (Ω.prob_nonneg t) (h t).le) (Finset.mem_univ s)
  unfold expect
  nlinarith [mul_pos hs (h s)]

/-- The covariance decomposition `E[XY] = E[X]E[Y] + Cov(X, Y)` (O&R §8.7.2, p. 581). -/
theorem expect_mul_eq (X Y : S → ℝ) :
    Ω.expect (fun s => X s * Y s) = Ω.expect X * Ω.expect Y + Ω.cov X Y := by
  unfold cov; ring

/-- The variance as the mean squared deviation (O&R §8.7.5, p. 590). -/
theorem var_eq_expect_sq (X : S → ℝ) :
    Ω.var X = Ω.expect (fun s => (X s - Ω.expect X) ^ 2) := by
  rw [show (fun s => (X s - Ω.expect X) ^ 2) = fun s => (X s * X s + (-2 * Ω.expect X) * X s)
      + Ω.expect X ^ 2 from funext fun s => by ring, expect_add, expect_add, expect_mul_left,
    expect_const]
  simp only [var, cov]; ring

/-- Variances are nonnegative (O&R §8.7.5, p. 590). -/
theorem var_nonneg (X : S → ℝ) : 0 ≤ Ω.var X := by
  rw [var_eq_expect_sq]
  simpa [expect_const] using Ω.expect_mono (X := fun _ => (0 : ℝ))
    (fun s => sq_nonneg (X s - Ω.expect X))

/-- Covariance is additive in its first argument (O&R §8.7.5, p. 590). -/
theorem cov_add_left (X Y Z : S → ℝ) :
    Ω.cov (fun s => X s + Y s) Z = Ω.cov X Z + Ω.cov Y Z := by
  simp only [cov, add_mul, expect_add]; ring

/-- Covariance is additive in its second argument (O&R §8.7.5, p. 590). -/
theorem cov_add_right (X Y Z : S → ℝ) :
    Ω.cov X (fun s => Y s + Z s) = Ω.cov X Y + Ω.cov X Z := by
  simp only [cov, mul_add, expect_add]; ring

/-- Covariance scales in its first argument (O&R §8.7.5). -/
theorem cov_mul_left (c : ℝ) (X Y : S → ℝ) :
    Ω.cov (fun s => c * X s) Y = c * Ω.cov X Y := by
  simp only [cov, mul_assoc, expect_mul_left]; ring

/-- Covariance scales in its second argument (O&R §8.7.5). -/
theorem cov_mul_right (c : ℝ) (X Y : S → ℝ) :
    Ω.cov X (fun s => c * Y s) = c * Ω.cov X Y := by
  simp only [cov, expect_mul_left]
  rw [show (fun s => X s * (c * Y s)) = fun s => c * (X s * Y s) from
    funext fun s => by ring, expect_mul_left]
  ring

/-- Covariance is symmetric (O&R §8.7.5). -/
theorem cov_comm (X Y : S → ℝ) : Ω.cov X Y = Ω.cov Y X := by
  simp only [cov, mul_comm (X _), mul_comm (Ω.expect X)]

/-- A constant has zero covariance with anything (O&R fn 68, p. 584). -/
theorem cov_const_left (c : ℝ) (Y : S → ℝ) : Ω.cov (fun _ => c) Y = 0 := by
  simp only [cov, expect_mul_left, expect_const]; ring

/-- Adding a constant does not change a covariance (O&R p. 592: `Cov(e, c) = Cov(e, y^W)`
when `c = log x + y^W`). -/
theorem cov_add_const_right (a : ℝ) (X Y : S → ℝ) :
    Ω.cov X (fun s => a + Y s) = Ω.cov X Y := by
  rw [cov_add_right, cov_comm Ω X (fun _ => a), cov_const_left]; ring

/-- The variance of a sum (O&R fn 75, p. 588). -/
theorem var_add (X Y : S → ℝ) :
    Ω.var (fun s => X s + Y s) = Ω.var X + Ω.var Y + 2 * Ω.cov X Y := by
  simp only [var, cov_add_left, cov_add_right, cov_comm Ω Y X]; ring

/-- The variance of a difference (O&R fn 75, p. 588: `Var(e − p) = Var e + Var p −
2Cov(e, p)`). -/
theorem var_sub (X Y : S → ℝ) :
    Ω.var (fun s => X s - Y s) = Ω.var X + Ω.var Y - 2 * Ω.cov X Y := by
  rw [show (fun s => X s - Y s) = fun s => X s + (-1) * Y s from funext fun s => by ring,
    var_add]
  simp only [var, cov_mul_left, cov_mul_right]; ring

/-- Adding a constant does not change a variance (O&R fn 75, p. 588). -/
theorem var_const_add (a : ℝ) (X : S → ℝ) : Ω.var (fun s => a + X s) = Ω.var X := by
  rw [var_add, var, var, cov_const_left, cov_const_left]; ring

end FinProb

/-! ## Markov kernels and the event tree -/

/-- A Markov transition kernel on a finite state space (O&R §8.7, p. 579: outputs and money
growth shocks "may be correlated across time"). -/
structure Kernel (S : Type) [Fintype S] where
  trans : S → S → ℝ
  trans_nonneg : ∀ s s', 0 ≤ trans s s'
  trans_sum : ∀ s, ∑ s', trans s s' = 1

/-- The conditional distribution of next period's state (O&R §8.7). -/
def Kernel.row {S : Type} [Fintype S] (K : Kernel S) (s : S) : FinProb S :=
  ⟨K.trans s, K.trans_nonneg s, K.trans_sum s⟩

/-- A node of the event tree: the current state and the list of past states, most recent
first (O&R §8.7: all variables may depend on the whole history). -/
abbrev Hist (S : Type) : Type := S × List S

variable {S : Type} [Fintype S]

/-- The successor node reached when next period's state is `s'` (O&R §8.7). -/
def next (h : Hist S) (s' : S) : Hist S := (s', h.1 :: h.2)

/-- The parent node (the root is its own parent) (O&R §8.7.5.2). -/
def anc : Hist S → Hist S
  | (s, []) => (s, [])
  | (_, t :: past) => (t, past)

/-- The date of a node, counted from the root (O&R §8.7). -/
def depth (h : Hist S) : ℕ := h.2.length

omit [Fintype S] in
/-- The parent of a successor is the node itself (O&R §8.7). -/
theorem anc_next (h : Hist S) (s' : S) : anc (next h s') = h := rfl

omit [Fintype S] in
/-- A successor is one period later (O&R §8.7). -/
theorem depth_next (h : Hist S) (s' : S) : depth (next h s') = depth h + 1 := by
  simp [depth, next]

/-- The conditional expectation `E_t X_{t+1}` for a (not necessarily stochastic) kernel `k`
(O&R §8.7, p. 580, (93)). -/
def oneStep (k : S → S → ℝ) (X : Hist S → ℝ) (h : Hist S) : ℝ :=
  ∑ s', k h.1 s' * X (next h s')

/-- The `n`-period-ahead conditional expectation `E_t X_{t+n}` (O&R §8.7.3, p. 584). -/
def iterStep (k : S → S → ℝ) (n : ℕ) : (Hist S → ℝ) → Hist S → ℝ := (oneStep k)^[n]

/-- `E_t` is additive (O&R §8.7). -/
theorem oneStep_add (k : S → S → ℝ) (X Y : Hist S → ℝ) (h : Hist S) :
    oneStep k (fun g => X g + Y g) h = oneStep k X h + oneStep k Y h := by
  simp [oneStep, mul_add, Finset.sum_add_distrib]

/-- `E_t` respects subtraction (O&R §8.7). -/
theorem oneStep_sub (k : S → S → ℝ) (X Y : Hist S → ℝ) (h : Hist S) :
    oneStep k (fun g => X g - Y g) h = oneStep k X h - oneStep k Y h := by
  simp [oneStep, mul_sub, Finset.sum_sub_distrib]

/-- Constants come out of `E_t` (O&R §8.7). -/
theorem oneStep_mul_left (k : S → S → ℝ) (c : ℝ) (X : Hist S → ℝ) (h : Hist S) :
    oneStep k (fun g => c * X g) h = c * oneStep k X h := by
  simp only [oneStep, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- `E_t` of a constant is the constant, for a stochastic kernel (O&R §8.7). -/
theorem oneStep_const {k : S → S → ℝ} (hk : ∀ s, ∑ s', k s s' = 1) (c : ℝ) (h : Hist S) :
    oneStep k (fun _ => c) h = c := by
  simp [oneStep, ← Finset.sum_mul, hk]

/-- `E_t` is monotone for a nonnegative kernel (O&R §8.7). -/
theorem oneStep_mono {k : S → S → ℝ} (hk : ∀ s s', 0 ≤ k s s') {X Y : Hist S → ℝ}
    (hXY : ∀ g, X g ≤ Y g) (h : Hist S) : oneStep k X h ≤ oneStep k Y h :=
  Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left (hXY _) (hk _ _)

/-- Date-`t` known factors come out of `E_t` (O&R §8.7.5.2: "known at time t"). -/
theorem oneStep_pull (k : S → S → ℝ) (a : Hist S → ℝ) (X : Hist S → ℝ) (h : Hist S) :
    oneStep k (fun g => a (anc g) * X g) h = a h * oneStep k X h := by
  simp only [oneStep, anc_next, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- One more period of expectation (O&R §8.7.3). -/
theorem iterStep_succ (k : S → S → ℝ) (n : ℕ) (X : Hist S → ℝ) :
    iterStep k (n + 1) X = iterStep k n (oneStep k X) :=
  Function.iterate_succ_apply _ _ _

/-- One more period of expectation, applied last: the tower property
`E_t E_{t+n} = E_t` (O&R §8.7.5.2). -/
theorem iterStep_succ' (k : S → S → ℝ) (n : ℕ) (X : Hist S → ℝ) :
    iterStep k (n + 1) X = oneStep k (iterStep k n X) :=
  Function.iterate_succ_apply' _ _ _

/-- The law of iterated expectations `E_t X_{t+m+n} = E_t E_{t+n} X_{t+m+n}`
(O&R §8.7.5.2). -/
theorem iterStep_add (k : S → S → ℝ) (m n : ℕ) (X : Hist S → ℝ) :
    iterStep k (m + n) X = iterStep k m (iterStep k n X) :=
  Function.iterate_add_apply _ _ _ _

/-- `E_t X_{t+n}` is additive (O&R §8.7). -/
theorem iterStep_add_fun (k : S → S → ℝ) (n : ℕ) (X Y : Hist S → ℝ) (h : Hist S) :
    iterStep k n (fun g => X g + Y g) h = iterStep k n X h + iterStep k n Y h := by
  induction n generalizing X Y with
  | zero => rfl
  | succ n ih =>
    rw [iterStep_succ, iterStep_succ, iterStep_succ,
      show oneStep k (fun g => X g + Y g) = fun g => oneStep k X g + oneStep k Y g from
        funext fun g => oneStep_add k X Y g, ih]

/-- `E_t X_{t+n}` respects subtraction (O&R §8.7). -/
theorem iterStep_sub_fun (k : S → S → ℝ) (n : ℕ) (X Y : Hist S → ℝ) (h : Hist S) :
    iterStep k n (fun g => X g - Y g) h = iterStep k n X h - iterStep k n Y h := by
  induction n generalizing X Y with
  | zero => rfl
  | succ n ih =>
    rw [iterStep_succ, iterStep_succ, iterStep_succ,
      show oneStep k (fun g => X g - Y g) = fun g => oneStep k X g - oneStep k Y g from
        funext fun g => oneStep_sub k X Y g, ih]

/-- Constants come out of `E_t X_{t+n}` (O&R §8.7). -/
theorem iterStep_mul_left (k : S → S → ℝ) (n : ℕ) (c : ℝ) (X : Hist S → ℝ) (h : Hist S) :
    iterStep k n (fun g => c * X g) h = c * iterStep k n X h := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    rw [iterStep_succ, iterStep_succ,
      show oneStep k (fun g => c * X g) = fun g => c * oneStep k X g from
        funext fun g => oneStep_mul_left k c X g, ih]

/-- `E_t` of a constant `n` periods ahead is the constant (O&R §8.7). -/
theorem iterStep_const {k : S → S → ℝ} (hk : ∀ s, ∑ s', k s s' = 1) (n : ℕ) (c : ℝ)
    (h : Hist S) : iterStep k n (fun _ => c) h = c := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    rw [iterStep_succ', oneStep, show (fun s' => k h.1 s' * iterStep k n (fun _ => c)
      (next h s')) = fun s' => k h.1 s' * c from funext fun s' => by rw [ih]]
    rw [← Finset.sum_mul, hk, one_mul]

/-- `E_t X_{t+n}` is monotone for a nonnegative kernel (O&R §8.7). -/
theorem iterStep_mono {k : S → S → ℝ} (hk : ∀ s s', 0 ≤ k s s') (n : ℕ) {X Y : Hist S → ℝ}
    (hXY : ∀ g, X g ≤ Y g) (h : Hist S) : iterStep k n X h ≤ iterStep k n Y h := by
  induction n generalizing h with
  | zero => exact hXY h
  | succ n ih =>
    rw [iterStep_succ', iterStep_succ']
    exact oneStep_mono hk (fun g => ih g) h

/-- Date-`t` known factors come out of `E_t X_{t+n}` (O&R §8.7.5.2). -/
theorem iterStep_pull (k : S → S → ℝ) (n : ℕ) (a : Hist S → ℝ) (X : Hist S → ℝ)
    (h : Hist S) :
    iterStep k n (fun g => a (anc^[n] g) * X g) h = a h * iterStep k n X h := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    rw [iterStep_succ, iterStep_succ]
    have hstep : oneStep k (fun g => a (anc^[n + 1] g) * X g)
        = fun g => a (anc^[n] g) * oneStep k X g := by
      funext g
      simp only [Function.iterate_succ_apply]
      exact oneStep_pull k (fun g => a (anc^[n] g)) X g
    rw [hstep, ih]

/-- A function of the date alone moves forward deterministically (O&R §8.7). -/
theorem iterStep_depth {k : S → S → ℝ} (hk : ∀ s, ∑ s', k s s' = 1) (n : ℕ) (f : ℕ → ℝ)
    (h : Hist S) : iterStep k n (fun g => f (depth g)) h = f (depth h + n) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [iterStep_succ]
    have hstep : oneStep k (fun g => f (depth g)) = fun g => f (depth g + 1) := by
      funext g
      simp only [oneStep, depth_next]
      rw [← Finset.sum_mul, hk, one_mul]
    rw [hstep, ih (fun d => f (d + 1))]
    congr 1

/-- Bounds propagate through `E_t X_{t+n}` (O&R §8.7). -/
theorem abs_iterStep_le {k : S → S → ℝ} (hk0 : ∀ s s', 0 ≤ k s s')
    (hk : ∀ s, ∑ s', k s s' = 1) (n : ℕ) {X : Hist S → ℝ} {b : ℝ} (hb : ∀ g, |X g| ≤ b)
    (h : Hist S) : |iterStep k n X h| ≤ b := by
  have h1 := iterStep_mono hk0 n (X := X) (Y := fun _ => b) (fun g => (abs_le.1 (hb g)).2) h
  have h2 := iterStep_mono hk0 n (X := fun _ => -b) (Y := X) (fun g => (abs_le.1 (hb g)).1) h
  rw [iterStep_const hk] at h1 h2
  exact abs_le.2 ⟨h2, h1⟩

/-- `E_t X_{t+n}` of a nonnegative variable is nonnegative (O&R §8.7). -/
theorem iterStep_nonneg {k : S → S → ℝ} (hk : ∀ s s', 0 ≤ k s s') (n : ℕ) {X : Hist S → ℝ}
    (hX : ∀ g, 0 ≤ X g) (h : Hist S) : 0 ≤ iterStep k n X h := by
  induction n generalizing h with
  | zero => exact hX h
  | succ n ih =>
    rw [iterStep_succ']
    exact Finset.sum_nonneg fun s _ => mul_nonneg (hk _ _) (ih _)

/-- Comparison of two kernels on nonnegative variables: if `k₁ ≤ c k₂` entrywise, then
`E¹_t X_{t+n} ≤ cⁿ E²_t X_{t+n}` (used for the transversality argument, O&R (100)). -/
theorem iterStep_le_pow_mul {k₁ k₂ : S → S → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hk₁ : ∀ s s', 0 ≤ k₁ s s') (hk₂ : ∀ s s', 0 ≤ k₂ s s')
    (hle : ∀ s s', k₁ s s' ≤ c * k₂ s s') (n : ℕ) {X : Hist S → ℝ} (hX : ∀ g, 0 ≤ X g)
    (h : Hist S) : iterStep k₁ n X h ≤ c ^ n * iterStep k₂ n X h := by
  have hnn : ∀ m g, 0 ≤ iterStep k₂ m X g := fun m g => iterStep_nonneg hk₂ m hX g
  induction n generalizing h with
  | zero => simp [iterStep]
  | succ n ih =>
    rw [iterStep_succ', iterStep_succ']
    calc oneStep k₁ (iterStep k₁ n X) h
        ≤ oneStep k₁ (fun g => c ^ n * iterStep k₂ n X g) h := oneStep_mono hk₁ ih h
      _ = c ^ n * oneStep k₁ (iterStep k₂ n X) h := oneStep_mul_left _ _ _ _
      _ ≤ c ^ n * (c * oneStep k₂ (iterStep k₂ n X) h) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hc n)
          simp only [oneStep, Finset.mul_sum]
          exact Finset.sum_le_sum fun s _ => by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right (hle _ _) (hnn n _)
      _ = c ^ (n + 1) * oneStep k₂ (iterStep k₂ n X) h := by ring

/-! ## Euler equations: necessity and sufficiency -/

/-- The tangent-line inequality for a concave differentiable function on `(0, ∞)`: the
supporting-hyperplane step behind every sufficiency argument (O&R §8.7.1, p. 580). -/
theorem concave_tangent {u u' : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    u y ≤ u x + u' x * (y - x) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have h := hc.slope_le_of_hasDerivAt hx hy hxy (hd x hx)
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 hxy)] at h
    linarith
  · simp
  · have h := hc.le_slope_of_hasDerivAt hy hx hxy (hd x hx)
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 hxy)] at h
    linarith

/-- Lifetime utility, as a function of `δ`, when the agent gives up `c δ` units of
consumption at `t` to buy `δ` units of an asset with real payoff `R(s)` at `t+1`
(O&R (93), p. 580). Only the terms that change are kept. -/
def assetValue (u : ℝ → ℝ) (Ω : FinProb S) (β C c : ℝ) (C' R : S → ℝ) (δ : ℝ) : ℝ :=
  u (C - c * δ) + β * Ω.expect (fun s => u (C' s + δ * R s))

/-- The marginal value of the asset reallocation (O&R (93), p. 580). -/
theorem hasDerivAt_assetValue {u u' : ℝ → ℝ} (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    (Ω : FinProb S) (β : ℝ) {C : ℝ} (c : ℝ) {C' : S → ℝ} (R : S → ℝ) (hC : 0 < C)
    (hC' : ∀ s, 0 < C' s) :
    HasDerivAt (assetValue u Ω β C c C' R)
      (-(c * u' C) + β * Ω.expect (fun s => u' (C' s) * R s)) 0 := by
  have hg : HasDerivAt (fun δ : ℝ => C - c * δ) (-c) 0 := by
    simpa using HasDerivAt.const_sub C (HasDerivAt.const_mul c (hasDerivAt_id' (0 : ℝ)))
  have h1 : HasDerivAt (fun δ => u (C - c * δ)) (u' C * (-c)) 0 :=
    HasDerivAt.comp_of_eq 0 (hd C hC) hg (by simp)
  have h2 : HasDerivAt (fun δ => Ω.expect (fun s => u (C' s + δ * R s)))
      (Ω.expect fun s => u' (C' s) * R s) 0 := by
    unfold FinProb.expect
    apply HasDerivAt.fun_sum
    intro s _
    have hgs : HasDerivAt (fun δ : ℝ => C' s + δ * R s) (R s) 0 := by
      simpa using HasDerivAt.const_add (C' s) (HasDerivAt.mul_const (hasDerivAt_id' (0 : ℝ))
        (R s))
    have h3 := HasDerivAt.const_mul (Ω.prob s)
      (HasDerivAt.comp_of_eq 0 (hd (C' s) (hC' s)) hgs (by simp))
    exact h3
  have h4 := HasDerivAt.add h1 (HasDerivAt.const_mul β h2)
  unfold assetValue
  convert h4 using 1
  ring

/-- **Necessity of the asset Euler equation** (O&R (93), p. 580): if no small reallocation
into the asset raises utility, then `c u′(C_t) = β E_t[u′(C_{t+1}) R_{t+1}]`. -/
theorem asset_euler_of_isLocalMax {u u' : ℝ → ℝ} (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    {Ω : FinProb S} {β C c : ℝ} {C' R : S → ℝ} (hC : 0 < C) (hC' : ∀ s, 0 < C' s)
    (hmax : IsLocalMax (assetValue u Ω β C c C' R) 0) :
    c * u' C = β * Ω.expect (fun s => u' (C' s) * R s) := by
  have := hmax.hasDerivAt_eq_zero (hasDerivAt_assetValue hd Ω β c R hC hC')
  linarith

/-- **Sufficiency of the asset Euler equation** (O&R (93), p. 580): with concave utility, if
the Euler equation holds then NO feasible reallocation of any size raises utility. -/
theorem assetValue_le_of_euler {u u' : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) {Ω : FinProb S} {β C c : ℝ} {C' R : S → ℝ}
    (hβ : 0 ≤ β) (hC : 0 < C) (hC' : ∀ s, 0 < C' s)
    (heul : c * u' C = β * Ω.expect (fun s => u' (C' s) * R s)) {δ : ℝ}
    (h1 : 0 < C - c * δ) (h2 : ∀ s, 0 < C' s + δ * R s) :
    assetValue u Ω β C c C' R δ ≤ assetValue u Ω β C c C' R 0 := by
  have t1 := concave_tangent hc hd hC h1
  have t2 : Ω.expect (fun s => u (C' s + δ * R s))
      ≤ Ω.expect (fun s => u (C' s) + δ * (u' (C' s) * R s)) :=
    Ω.expect_mono fun s => by
      have := concave_tangent hc hd (hC' s) (h2 s)
      nlinarith [this]
  rw [Ω.expect_add, Ω.expect_mul_left] at t2
  have t3 := mul_le_mul_of_nonneg_left t2 hβ
  have h5 : c * u' C * δ = β * Ω.expect (fun s => u' (C' s) * R s) * δ := by rw [heul]
  simp only [assetValue, mul_zero, sub_zero, zero_mul, add_zero]
  nlinarith [t1, t3, h5]

/-- **The asset Euler equation is necessary and sufficient** for a local optimum of the
one-period reallocation, with concave utility (O&R (93), p. 580). -/
theorem isLocalMax_assetValue_iff {u u' : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) {Ω : FinProb S} {β C c : ℝ} {C' R : S → ℝ}
    (hβ : 0 ≤ β) (hC : 0 < C) (hC' : ∀ s, 0 < C' s) :
    IsLocalMax (assetValue u Ω β C c C' R) 0 ↔
      c * u' C = β * Ω.expect (fun s => u' (C' s) * R s) := by
  refine ⟨asset_euler_of_isLocalMax hd hC hC', fun heul => ?_⟩
  have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C - c * δ := by
    have hcont : Continuous fun δ : ℝ => C - c * δ := by fun_prop
    exact continuousAt_const.eventually_lt hcont.continuousAt (by simpa using hC)
  have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ s, 0 < C' s + δ * R s := by
    refine Filter.eventually_all.2 fun s => ?_
    have hcont : Continuous fun δ : ℝ => C' s + δ * R s := by fun_prop
    exact (continuousAt_const.eventually_lt hcont.continuousAt (by simpa using hC' s))
  filter_upwards [e1, e2] with δ h1 h2 using assetValue_le_of_euler hc hd hβ hC hC' heul h1 h2

/-- Lifetime utility, as a function of `δ`, when the agent holds `δ` extra dollars of money
at `t` (giving up `δ/P_t` of consumption, enjoying real balances `(M_t + δ)/P_t`) and spends
them at `t+1` (O&R (98), p. 581). -/
noncomputable def moneyValue (u v : ℝ → ℝ) (Ω : FinProb S) (β C M P : ℝ) (C' P' : S → ℝ)
    (δ : ℝ) : ℝ :=
  u (C - δ / P) + v ((M + δ) / P) + β * Ω.expect (fun s => u (C' s + δ / P' s))

/-- The marginal value of holding an extra dollar (O&R (98), p. 581). -/
theorem hasDerivAt_moneyValue {u u' v v' : ℝ → ℝ} (hdu : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    (hdv : ∀ x, 0 < x → HasDerivAt v (v' x) x) (Ω : FinProb S) (β : ℝ) {C M P : ℝ}
    {C' : S → ℝ} (P' : S → ℝ) (hC : 0 < C) (hM : 0 < M) (hP : 0 < P) (hC' : ∀ s, 0 < C' s) :
    HasDerivAt (moneyValue u v Ω β C M P C' P')
      (-(1 / P * u' C) + 1 / P * v' (M / P) + β * Ω.expect (fun s => 1 / P' s * u' (C' s)))
      0 := by
  have hg1 : HasDerivAt (fun δ : ℝ => C - δ / P) (-(1 / P)) 0 :=
    HasDerivAt.const_sub C (HasDerivAt.div_const (hasDerivAt_id' (0 : ℝ)) P)
  have hg2 : HasDerivAt (fun δ : ℝ => (M + δ) / P) (1 / P) 0 :=
    HasDerivAt.div_const (HasDerivAt.const_add M (hasDerivAt_id' (0 : ℝ))) P
  have h1 : HasDerivAt (fun δ => u (C - δ / P)) (u' C * (-(1 / P))) 0 :=
    HasDerivAt.comp_of_eq 0 (hdu C hC) hg1 (by simp)
  have h2 : HasDerivAt (fun δ => v ((M + δ) / P)) (v' (M / P) * (1 / P)) 0 :=
    HasDerivAt.comp_of_eq 0 (hdv (M / P) (div_pos hM hP)) hg2 (by simp)
  have h3 : HasDerivAt (fun δ => Ω.expect (fun s => u (C' s + δ / P' s)))
      (Ω.expect fun s => 1 / P' s * u' (C' s)) 0 := by
    unfold FinProb.expect
    apply HasDerivAt.fun_sum
    intro s _
    have hgs : HasDerivAt (fun δ : ℝ => C' s + δ / P' s) (1 / P' s) 0 :=
      HasDerivAt.const_add (C' s) (HasDerivAt.div_const (hasDerivAt_id' (0 : ℝ)) (P' s))
    have h4 := HasDerivAt.const_mul (Ω.prob s)
      (HasDerivAt.comp_of_eq 0 (hdu (C' s) (hC' s)) hgs (by simp))
    exact HasDerivAt.congr_deriv h4 (by ring)
  have h5 := HasDerivAt.add (HasDerivAt.add h1 h2) (HasDerivAt.const_mul β h3)
  unfold moneyValue
  convert h5 using 1
  ring

/-- **The money Euler equation (98) is necessary and sufficient** for a local optimum of the
money-holding decision, with concave `u` and `v` (O&R (98), p. 581). -/
theorem isLocalMax_moneyValue_iff {u u' v v' : ℝ → ℝ} (hcu : ConcaveOn ℝ (Set.Ioi 0) u)
    (hcv : ConcaveOn ℝ (Set.Ioi 0) v) (hdu : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    (hdv : ∀ x, 0 < x → HasDerivAt v (v' x) x) {Ω : FinProb S} {β C M P : ℝ}
    {C' P' : S → ℝ} (hβ : 0 ≤ β) (hC : 0 < C) (hM : 0 < M) (hP : 0 < P)
    (hC' : ∀ s, 0 < C' s) :
    IsLocalMax (moneyValue u v Ω β C M P C' P') 0 ↔
      1 / P * u' C = 1 / P * v' (M / P) + β * Ω.expect (fun s => 1 / P' s * u' (C' s)) := by
  constructor
  · intro hmax
    have := hmax.hasDerivAt_eq_zero (hasDerivAt_moneyValue hdu hdv Ω β P' hC hM hP hC')
    linarith
  · intro heul
    have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C - δ / P := by
      have hcont : Continuous fun δ : ℝ => C - δ / P := by fun_prop
      exact continuousAt_const.eventually_lt hcont.continuousAt (by simpa using hC)
    have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < (M + δ) / P := by
      have hcont : Continuous fun δ : ℝ => (M + δ) / P := by fun_prop
      exact continuousAt_const.eventually_lt hcont.continuousAt (by simpa using div_pos hM hP)
    have e3 : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ s, 0 < C' s + δ / P' s := by
      refine Filter.eventually_all.2 fun s => ?_
      have hcont : Continuous fun δ : ℝ => C' s + δ / P' s := by fun_prop
      exact continuousAt_const.eventually_lt hcont.continuousAt (by simpa using hC' s)
    filter_upwards [e1, e2, e3] with δ h1 h2 h3
    have t1 := concave_tangent hcu hdu hC h1
    have t2 := concave_tangent hcv hdv (div_pos hM hP) h2
    have t3 : Ω.expect (fun s => u (C' s + δ / P' s))
        ≤ Ω.expect (fun s => u (C' s) + δ * (1 / P' s * u' (C' s))) :=
      Ω.expect_mono fun s => by
        have := concave_tangent hcu hdu (hC' s) (h3 s)
        have e : u' (C' s) * (C' s + δ / P' s - C' s) = δ * (1 / P' s * u' (C' s)) := by
          ring
        linarith
    rw [Ω.expect_add, Ω.expect_mul_left] at t3
    have t4 := mul_le_mul_of_nonneg_left t3 hβ
    have e1' : u' C * (C - δ / P - C) = -(δ * (1 / P * u' C)) := by ring
    have e2' : v' (M / P) * ((M + δ) / P - M / P) = δ * (1 / P * v' (M / P)) := by
      ring
    have h6 : δ * (1 / P * u' C) = δ * (1 / P * v' (M / P))
        + δ * (β * Ω.expect (fun s => 1 / P' s * u' (C' s))) := by rw [heul]; ring
    simp only [moneyValue, zero_div, sub_zero, add_zero]
    nlinarith [t1, t2, t4, e1', e2', h6]

/-- **The nominal-bond Euler equation (95)** (O&R (95), p. 581): buying `δ` dollars of a
one-period dollar bond is a reallocation with cost `1/P_t` and payoff `(1+i)/P_{t+1}`; the
first-order condition is necessary and sufficient and reads
`u′(C_t) = β E_t[(1+i) (P_t/P_{t+1}) u′(C_{t+1})]`. -/
theorem nominal_bond_euler_iff {u u' : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) {Ω : FinProb S} {β C P i : ℝ}
    {C' P' : S → ℝ} (hβ : 0 ≤ β) (hC : 0 < C) (hP : 0 < P) (hC' : ∀ s, 0 < C' s) :
    IsLocalMax (assetValue u Ω β C (1 / P) C' (fun s => (1 + i) / P' s)) 0 ↔
      u' C = β * Ω.expect (fun s => (1 + i) * (P / P' s) * u' (C' s)) := by
  rw [isLocalMax_assetValue_iff hc hd hβ hC hC']
  have e : Ω.expect (fun s => (1 + i) * (P / P' s) * u' (C' s))
      = P * Ω.expect (fun s => u' (C' s) * ((1 + i) / P' s)) := by
    rw [← Ω.expect_mul_left]
    congr 1; funext s; ring
  rw [e]
  constructor
  · intro h
    have hP' : u' C = P * (1 / P * u' C) := by field_simp
    rw [hP', h]; ring
  · intro h
    rw [h, show ∀ z : ℝ, 1 / P * (β * (P * z)) = β * z from fun z => by field_simp]

/-- **The real-bond Euler equation (96)** (O&R (96), p. 581):
`u′(C_t) = (1+r) β E_t[u′(C_{t+1})]`, necessary and sufficient. -/
theorem real_bond_euler_iff {u u' : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) {Ω : FinProb S} {β C r : ℝ} {C' : S → ℝ}
    (hβ : 0 ≤ β) (hC : 0 < C) (hC' : ∀ s, 0 < C' s) :
    IsLocalMax (assetValue u Ω β C 1 C' (fun _ => 1 + r)) 0 ↔
      u' C = (1 + r) * β * Ω.expect (fun s => u' (C' s)) := by
  rw [isLocalMax_assetValue_iff hc hd hβ hC hC', one_mul,
    show (fun s => u' (C' s) * (1 + r)) = fun s => (1 + r) * u' (C' s) from
      funext fun s => by ring, Ω.expect_mul_left]
  constructor <;> intro h <;> linarith

/-! ## Nominal bonds, real bonds and money (§8.7.2) -/

/-- **(97) holds if and only if inflation and marginal utility are uncorrelated**
(O&R (95)–(97), p. 581; the book states only "only if"). Here `π = P_t/P_{t+1}` and
`m = u′(C_{t+1})`. -/
theorem fisher_iff_cov_zero {Ω : FinProb S} {uC β i r : ℝ} {π m : S → ℝ} (hβ : 0 < β)
    (hi : 0 < 1 + i) (hm : 0 < Ω.expect m)
    (h95 : uC = β * Ω.expect (fun s => (1 + i) * π s * m s))
    (h96 : uC = (1 + r) * β * Ω.expect m) :
    1 + r = (1 + i) * Ω.expect π ↔ Ω.cov π m = 0 := by
  have e : Ω.expect (fun s => (1 + i) * π s * m s) = (1 + i) * Ω.expect (fun s => π s * m s) :=
    by rw [← Ω.expect_mul_left]; congr 1; funext s; ring
  rw [e, Ω.expect_mul_eq] at h95
  have key : (1 + r) * Ω.expect m = (1 + i) * (Ω.expect π * Ω.expect m + Ω.cov π m) := by
    have := h95.symm.trans h96
    have hb : β * ((1 + r) * Ω.expect m) = β * ((1 + i) * (Ω.expect π * Ω.expect m
        + Ω.cov π m)) := by linarith
    exact (mul_left_cancel₀ hβ.ne' hb)
  constructor
  · intro h
    rw [h] at key
    have : (1 + i) * Ω.cov π m = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact h1
  · intro h
    rw [h, add_zero] at key
    have : ((1 + r) - (1 + i) * Ω.expect π) * Ω.expect m = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · linarith

/-- With deterministic consumption the certainty-equivalence Fisher equation (97) holds
(O&R p. 581: "unless consumption ... is deterministic"). -/
theorem fisher_of_deterministic_consumption {Ω : FinProb S} {uC β i r mbar : ℝ}
    {π : S → ℝ} (hβ : 0 < β) (hi : 0 < 1 + i) (hm : 0 < mbar)
    (h95 : uC = β * Ω.expect (fun s => (1 + i) * π s * mbar))
    (h96 : uC = (1 + r) * β * Ω.expect (fun _ => mbar)) :
    1 + r = (1 + i) * Ω.expect π := by
  refine (fisher_iff_cov_zero (m := fun _ => mbar) hβ hi (by rwa [Ω.expect_const]) h95
    h96).2 ?_
  rw [Ω.cov_comm, Ω.cov_const_left]

/-- **The money-demand condition** `v′(M/P)/u′(C) = i/(1+i)` from (95) and (98)
(O&R p. 582; identical to (37)). Here `A = E_t[u′(C_{t+1})/P_{t+1}]`. -/
theorem money_demand_of_euler {uC vM P β i A : ℝ} (huC : 0 < uC) (hP : 0 < P)
    (hi : 0 < 1 + i) (h98 : 1 / P * uC = 1 / P * vM + β * A)
    (h95 : 1 / P * uC = (1 + i) * β * A) : vM / uC = i / (1 + i) := by
  have hA : β * A = uC / (P * (1 + i)) := by
    field_simp; field_simp at h95; linarith
  rw [hA] at h98
  field_simp at h98 ⊢
  linarith

/-! ## Consumption allocations (94) -/

/-- **Complete risk sharing with CRRA utility gives constant consumption shares** (O&R (94),
p. 580): if every country's marginal utility `C^{−ρ}` is a country-specific constant times a
common state price, and consumption exhausts world output, then `Cⁿ = xⁿ Y^W` with
time- and state-invariant shares `xⁿ > 0`, `Σ xⁿ = 1`. -/
theorem consumption_shares {ι T : Type} [Fintype ι] [Nonempty ι] {ρ : ℝ} (hρ : ρ ≠ 0)
    {C : ι → T → ℝ} {Y : T → ℝ} {lam : ι → ℝ} {κ : T → ℝ} (hC : ∀ n t, 0 < C n t)
    (hlam : ∀ n, 0 < lam n) (hκ : ∀ t, 0 < κ t)
    (hfoc : ∀ n t, C n t ^ (-ρ) = lam n * κ t) (hY : ∀ t, ∑ n, C n t = Y t) :
    ∃ x : ι → ℝ, (∀ n, 0 < x n) ∧ ∑ n, x n = 1 ∧ ∀ n t, C n t = x n * Y t := by
  have hCeq : ∀ n t, C n t = lam n ^ (-1 / ρ) * κ t ^ (-1 / ρ) := by
    intro n t
    have h : (C n t ^ (-ρ)) ^ (-1 / ρ) = (lam n * κ t) ^ (-1 / ρ) := by rw [hfoc n t]
    rwa [← Real.rpow_mul (hC n t).le, show -ρ * (-1 / ρ) = 1 by field_simp, Real.rpow_one,
      Real.mul_rpow (hlam n).le (hκ t).le] at h
  set D := ∑ n, lam n ^ (-1 / ρ) with hD
  have hDpos : 0 < D := Finset.sum_pos (fun n _ => Real.rpow_pos_of_pos (hlam n) _)
    Finset.univ_nonempty
  refine ⟨fun n => lam n ^ (-1 / ρ) / D, fun n => div_pos (Real.rpow_pos_of_pos (hlam n) _)
    hDpos, ?_, ?_⟩
  · rw [← Finset.sum_div, ← hD, div_self hDpos.ne']
  · intro n t
    rw [← hY t, hCeq n t]
    simp only [hCeq, ← Finset.sum_mul]
    rw [← hD]
    field_simp

/-- With constant shares, every country's consumption grows with world output, so the
Euler equation (93) is the same for every country (O&R p. 580, fn 64). -/
theorem consumption_growth_eq_world {x Y Y' ρ : ℝ} (hx : 0 < x) :
    (x * Y / (x * Y')) ^ ρ = (Y / Y') ^ ρ := by
  rw [mul_div_mul_left _ _ hx.ne']

/-! ## The money Euler equation with CRRA/log utility: exact linearity (99) -/

/-- `(Y/Y′)^ρ = (xY)^ρ/(xY′)^ρ` (O&R (99), p. 583: the share `x` cancels). -/
theorem rpow_ratio_eq {x Y Y' ρ : ℝ} (hx : 0 < x) (hY : 0 < Y) (hY' : 0 < Y') :
    (Y / Y') ^ ρ = (x * Y) ^ ρ / (x * Y') ^ ρ := by
  rw [Real.div_rpow hY.le hY'.le, Real.mul_rpow hx.le hY.le, Real.mul_rpow hx.le hY'.le]
  have : 0 < x ^ ρ := Real.rpow_pos_of_pos hx ρ
  field_simp

/-- **(98) with `u = C^{1−ρ}/(1−ρ)`, `v = log` and `C = xY^W` is (99)** (O&R (99), p. 583):
`u′(C) = C^{−ρ}`, `v′(m) = 1/m`. -/
theorem money_euler_crra_iff (Ω : FinProb S) {ρ x β M P Yw : ℝ} {P' Y' : S → ℝ}
    (hx : 0 < x) (hM : 0 < M) (hP : 0 < P) (hY : 0 < Yw) (hY' : ∀ s, 0 < Y' s) :
    1 / P * (x * Yw) ^ (-ρ) = 1 / P * (1 / (M / P))
        + β * Ω.expect (fun s => 1 / P' s * (x * Y' s) ^ (-ρ)) ↔
      1 = P * (x * Yw) ^ ρ / M + β * Ω.expect (fun s => P / P' s * (Yw / Y' s) ^ ρ) := by
  have hapos : 0 < (x * Yw) ^ ρ := Real.rpow_pos_of_pos (mul_pos hx hY) ρ
  have hE : Ω.expect (fun s => P / P' s * (Yw / Y' s) ^ ρ)
      = P * (x * Yw) ^ ρ * Ω.expect (fun s => 1 / P' s * (x * Y' s) ^ (-ρ)) := by
    rw [← Ω.expect_mul_left]
    congr 1; funext s
    rw [rpow_ratio_eq hx hY (hY' s), Real.rpow_neg (mul_pos hx (hY' s)).le]
    field_simp
  rw [hE, Real.rpow_neg (mul_pos hx hY).le]
  set a := (x * Yw) ^ ρ
  set E := Ω.expect (fun s => 1 / P' s * (x * Y' s) ^ (-ρ))
  have hk : P * a ≠ 0 := by positivity
  rw [← mul_right_inj' hk]
  have l1 : P * a * (1 / P * a⁻¹) = 1 := by field_simp
  have l2 : P * a * (1 / P * (1 / (M / P)) + β * E) = P * a / M + β * (P * a * E) := by
    field_simp
  rw [l1, l2]

/-- The key pointwise identity behind the exact linearity of (99): with
`w = M/(P (xY)^ρ)` and `M′ = M (1+μ) ε`,
`(P/P′)(Y/Y′)^ρ = (1/(1+μ)) (1/w) (w′/ε)` (O&R (99)–(100), p. 583). -/
theorem price_ratio_term_eq {ρ x μ M P Yw P' Y' e : ℝ} (hx : 0 < x) (hM : 0 < M) (hP : 0 < P)
    (hY : 0 < Yw) (hP' : 0 < P') (hY' : 0 < Y') (hμ : 0 < 1 + μ) (he : 0 < e) :
    P / P' * (Yw / Y') ^ ρ = 1 / (1 + μ) * (P * (x * Yw) ^ ρ / M)
      * (M * (1 + μ) * e / (P' * (x * Y') ^ ρ) / e) := by
  rw [rpow_ratio_eq hx hY hY']
  have : 0 < (x * Yw) ^ ρ := Real.rpow_pos_of_pos (mul_pos hx hY) ρ
  have : 0 < (x * Y') ^ ρ := Real.rpow_pos_of_pos (mul_pos hx hY') ρ
  field_simp

/-- **(99) is exactly linear in output-adjusted real balances** (O&R (99)–(100), p. 583):
with `w = M/(P (xY^W)^ρ)` and money growth `M′ = M(1+μ)ε`, equation (99) holds iff
`w_t = 1 + (β/(1+μ)) E_t[w_{t+1}/ε_{t+1}]`. -/
theorem eq99_iff_linear (Ω : FinProb S) {β μ ρ x M P Yw : ℝ} {P' Y' ε : S → ℝ}
    (hx : 0 < x) (hM : 0 < M) (hP : 0 < P) (hY : 0 < Yw) (hP' : ∀ s, 0 < P' s)
    (hY' : ∀ s, 0 < Y' s) (hμ : 0 < 1 + μ) (hε : ∀ s, 0 < ε s) :
    (1 = P * (x * Yw) ^ ρ / M + β * Ω.expect (fun s => P / P' s * (Yw / Y' s) ^ ρ)) ↔
      M / (P * (x * Yw) ^ ρ) = 1 + β / (1 + μ)
        * Ω.expect (fun s => M * (1 + μ) * ε s / (P' s * (x * Y' s) ^ ρ) / ε s) := by
  have hE : Ω.expect (fun s => P / P' s * (Yw / Y' s) ^ ρ) = 1 / (1 + μ)
      * (P * (x * Yw) ^ ρ / M)
      * Ω.expect (fun s => M * (1 + μ) * ε s / (P' s * (x * Y' s) ^ ρ) / ε s) := by
    rw [← Ω.expect_mul_left]
    congr 1; funext s
    exact price_ratio_term_eq hx hM hP hY (hP' s) (hY' s) hμ (hε s)
  rw [hE]
  have hapos : 0 < (x * Yw) ^ ρ := Real.rpow_pos_of_pos (mul_pos hx hY) ρ
  set E := Ω.expect (fun s => M * (1 + μ) * ε s / (P' s * (x * Y' s) ^ ρ) / ε s)
  set a := (x * Yw) ^ ρ
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    field_simp at h ⊢
    linarith

/-- Equation (99) at a node of the event tree (O&R (99), p. 583). -/
def Eq99 (K : Kernel S) (β ρ x : ℝ) (M P Y : Hist S → ℝ) (h : Hist S) : Prop :=
  1 = P h * (x * Y h) ^ ρ / M h
    + β * (K.row h.1).expect (fun s' => P h / P (next h s') * (Y h / Y (next h s')) ^ ρ)

/-- Output-adjusted real balances `w = M/(P (xY^W)^ρ)` (O&R (101), p. 583: the guess is
`w ≡ ω`). -/
noncomputable def realBal (ρ x : ℝ) (M P Y : Hist S → ℝ) : Hist S → ℝ :=
  fun h => M h / (P h * (x * Y h) ^ ρ)

/-- `u′(C) M/P = w`: marginal utility times real balances is the output-adjusted real
balance, so the individual transversality condition (O&R fn 31, p. 542) is a condition
on `w` (O&R (101), p. 583). -/
theorem marginal_utility_real_balances {ρ x M P Y : ℝ} (hx : 0 < x) (hY : 0 < Y) :
    (x * Y) ^ (-ρ) * (M / P) = M / (P * (x * Y) ^ ρ) := by
  rw [Real.rpow_neg (mul_pos hx hY).le]
  field_simp

/-- The risk-neutral-like kernel `P(s, s′)/ε(s′)` induced by money growth shocks
(O&R (100), p. 583). -/
noncomputable def tilt (K : Kernel S) (ε : S → ℝ) : S → S → ℝ :=
  fun s s' => K.trans s s' / ε s'

/-- The linear stochastic difference equation `w_t = 1 + γ E_t[w_{t+1}/ε_{t+1}]` at every
node (O&R (99)–(100), p. 583). -/
def LinearMoneyEq (K : Kernel S) (ε : S → ℝ) (γ : ℝ) (w : Hist S → ℝ) : Prop :=
  ∀ h, w h = 1 + γ * oneStep (tilt K ε) w h

/-- The tilted expectation is `E_t[w_{t+1}/ε_{t+1}]` (O&R (100), p. 583). -/
theorem oneStep_tilt_eq (K : Kernel S) (ε : S → ℝ) (w : Hist S → ℝ) (h : Hist S) :
    oneStep (tilt K ε) w h = (K.row h.1).expect (fun s' => w (next h s') / ε s') := by
  simp only [oneStep, tilt, Kernel.row, FinProb.expect]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **(99) at every node is the linear equation for `w`** (O&R (99)–(100), p. 583). -/
theorem eq99_iff_linearMoneyEq (K : Kernel S) {β μ ρ x : ℝ} {M P Y : Hist S → ℝ}
    {ε : S → ℝ} (hx : 0 < x) (hM : ∀ h, 0 < M h) (hP : ∀ h, 0 < P h) (hY : ∀ h, 0 < Y h)
    (hμ : 0 < 1 + μ) (hε : ∀ s, 0 < ε s)
    (hgrowth : ∀ h s', M (next h s') = M h * (1 + μ) * ε s') :
    (∀ h, Eq99 K β ρ x M P Y h) ↔ LinearMoneyEq K ε (β / (1 + μ)) (realBal ρ x M P Y) := by
  refine forall_congr' fun h => ?_
  rw [oneStep_tilt_eq]
  have e : (fun s' => realBal ρ x M P Y (next h s') / ε s') = fun s' => M h * (1 + μ) * ε s'
      / (P (next h s') * (x * Y (next h s')) ^ ρ) / ε s' := by
    funext s'; simp only [realBal, hgrowth]
  rw [e]
  exact eq99_iff_linear (K.row h.1) hx (hM h) (hP h) (hY h) (fun _ => hP _) (fun _ => hY _) hμ
    hε

/-! ## Existence, uniqueness and bubbles (100)–(101) -/

/-- The tilted kernel is nonnegative (O&R (100), p. 583). -/
theorem tilt_nonneg (K : Kernel S) {ε : S → ℝ} (hε : ∀ s, 0 < ε s) (s s' : S) :
    0 ≤ tilt K ε s s' :=
  div_nonneg (K.trans_nonneg s s') (hε s').le

/-- **`E_t[1/ε_{t+1}] = 1` makes the tilted kernel stochastic** (O&R (100), p. 583). -/
theorem tilt_sum (K : Kernel S) {ε : S → ℝ} (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1)
    (s : S) : ∑ s', tilt K ε s s' = 1 := by
  rw [← hE s]
  simp only [tilt, Kernel.row, FinProb.expect]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **The book's `ω`** (O&R (101), p. 583): `1/(1 − β/(1+μ)) = (1+μ)/(1+μ−β) > 0`. -/
theorem omega_eq {β μ : ℝ} (hμ : 0 < 1 + μ) (hβμ : β < 1 + μ) :
    1 / (1 - β / (1 + μ)) = (1 + μ) / (1 + μ - β) ∧ 0 < (1 + μ) / (1 + μ - β) := by
  refine ⟨?_, div_pos hμ (by linarith)⟩
  have : 1 + μ - β ≠ 0 := by linarith
  field_simp

namespace Solutions

variable (K : Kernel S) {ε : S → ℝ}

/-- **The constant `ω = 1/(1−γ)` solves the linear equation** (O&R (101), p. 583, "our
conjecture is now verified"). -/
theorem omega_solves (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) {γ : ℝ}
    (hγ : γ ≠ 1) : LinearMoneyEq K ε γ (fun _ => 1 / (1 - γ)) := by
  intro h
  rw [oneStep_const (tilt_sum K hE)]
  have : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  field_simp
  ring

/-- **Every solution is `ω` plus a bubble** `B_t = γ E_t[B_{t+1}/ε_{t+1}]`, and conversely
(O&R p. 582, "assuming no monetary bubbles"). -/
theorem linear_iff_bubble (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) {γ : ℝ}
    (hγ : γ ≠ 1) (w : Hist S → ℝ) :
    LinearMoneyEq K ε γ w ↔ ∀ h, w h - 1 / (1 - γ)
      = γ * oneStep (tilt K ε) (fun g => w g - 1 / (1 - γ)) h := by
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  refine forall_congr' fun h => ?_
  rw [oneStep_sub, oneStep_const (tilt_sum K hE)]
  constructor
  · intro hw
    rw [hw]; field_simp; ring
  · intro hw
    have : w h = 1 / (1 - γ) + γ * (oneStep (tilt K ε) w h - 1 / (1 - γ)) := by linarith
    rw [this]; field_simp; ring

/-- Iterating the bubble equation: `B_t = γⁿ Ẽ_t B_{t+n}` (O&R (100), p. 583). -/
theorem bubble_iterate {k : S → S → ℝ} {γ : ℝ} {B : Hist S → ℝ}
    (hB : ∀ h, B h = γ * oneStep k B h) (n : ℕ) (h : Hist S) :
    B h = γ ^ n * iterStep k n B h := by
  induction n generalizing h with
  | zero => simp [iterStep]
  | succ n ih =>
    have hBf : B = fun g => γ * oneStep k B g := funext hB
    rw [ih h]
    conv_lhs => rw [hBf]
    rw [iterStep_mul_left, iterStep_succ, pow_succ]
    ring

/-- **The unique bounded solution is `ω`** (O&R (101), p. 583: "existence and uniqueness
(assuming no monetary bubbles)"): along the whole event tree, a bounded solution of
`w_t = 1 + γ E_t[w_{t+1}/ε_{t+1}]` with `0 ≤ γ < 1` is the constant `1/(1−γ)`. -/
theorem unique_bounded (hε : ∀ s, 0 < ε s)
    (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) {w : Hist S → ℝ} (hw : LinearMoneyEq K ε γ w) {b : ℝ}
    (hb : ∀ h, |w h| ≤ b) (h : Hist S) : w h = 1 / (1 - γ) := by
  set ω := 1 / (1 - γ)
  have hB := (linear_iff_bubble K hE hγ1.ne w).1 hw
  have hbd : ∀ g, |w g - ω| ≤ b + |ω| := fun g =>
    (abs_sub _ _).trans (by linarith [hb g])
  have key : ∀ n : ℕ, |w h - ω| ≤ γ ^ n * (b + |ω|) := fun n => by
    rw [bubble_iterate hB n h, abs_mul, abs_of_nonneg (pow_nonneg hγ0 n)]
    exact mul_le_mul_of_nonneg_left
      (abs_iterStep_le (tilt_nonneg K hε) (tilt_sum K hE) n hbd h) (pow_nonneg hγ0 n)
  have ht : Tendsto (fun n : ℕ => γ ^ n * (b + |ω|)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const (b + |ω|)
  have := ge_of_tendsto' ht key
  have h0 : |w h - ω| = 0 := le_antisymm this (abs_nonneg _)
  linarith [abs_eq_zero.1 h0]

/-- **Every positive solution lies above `ω`: there are no negative bubbles** (O&R (101),
p. 583; derived from positivity of the price level alone). -/
theorem ge_omega_of_pos (hε : ∀ s, 0 < ε s)
    (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) {w : Hist S → ℝ} (hw : LinearMoneyEq K ε γ w) (hpos : ∀ h, 0 < w h)
    (h : Hist S) : 1 / (1 - γ) ≤ w h := by
  set ω := 1 / (1 - γ)
  have hB := (linear_iff_bubble K hE hγ1.ne w).1 hw
  have key : ∀ n : ℕ, -(γ ^ n * ω) ≤ w h - ω := fun n => by
    rw [bubble_iterate hB n h]
    have hlow := iterStep_mono (tilt_nonneg K hε) n (X := fun _ => -ω)
      (Y := fun g => w g - ω) (fun g => by linarith [hpos g]) h
    rw [iterStep_const (tilt_sum K hE)] at hlow
    nlinarith [pow_nonneg hγ0 n]
  have ht : Tendsto (fun n : ℕ => -(γ ^ n * ω)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const ω).neg
  have := le_of_tendsto' ht key
  linarith

/-- A bubble growing deterministically at rate `1/γ` (O&R p. 582, "monetary bubbles"). -/
noncomputable def depthBubble (γ c : ℝ) : Hist S → ℝ :=
  fun h => 1 / (1 - γ) + c * γ⁻¹ ^ depth h

/-- `E_t` moves the deterministic bubble forward in time (O&R (100), p. 583). -/
theorem iterStep_depthBubble {k : S → S → ℝ} (hk : ∀ s, ∑ s', k s s' = 1) (γ c : ℝ) (n : ℕ)
    (h : Hist S) :
    iterStep k n (depthBubble γ c) h = 1 / (1 - γ) + c * γ⁻¹ ^ (depth h + n) :=
  iterStep_depth hk n (fun d => 1 / (1 - γ) + c * γ⁻¹ ^ d) h

/-- **Bubbles exist**: `ω + c γ^{−t}` solves the linear equation for every `c`
(O&R p. 582). -/
theorem depthBubble_solves (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) {γ : ℝ}
    (hγ0 : γ ≠ 0) (hγ1 : γ ≠ 1) (c : ℝ) : LinearMoneyEq K ε γ (depthBubble γ c) := by
  intro h
  have e := iterStep_depthBubble (tilt_sum K hE) γ c 1 h
  rw [show iterStep (tilt K ε) 1 (depthBubble γ c) h = oneStep (tilt K ε) (depthBubble γ c) h
    from rfl] at e
  rw [e]
  have : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ1)
  simp only [depthBubble, pow_succ]
  field_simp
  ring

omit [Fintype S] in
/-- Positive bubbles give positive real balances (O&R p. 582). -/
theorem depthBubble_pos {γ c : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hc : 0 ≤ c) (h : Hist S) :
    0 < depthBubble γ c h := by
  have : 0 < 1 / (1 - γ) := div_pos one_pos (by linarith)
  have : 0 ≤ c * γ⁻¹ ^ depth h := mul_nonneg hc (pow_nonneg (inv_nonneg.2 hγ0.le) _)
  simp only [depthBubble]; linarith

/-- A node at every date (O&R §8.7). -/
def nodeAt (s : S) (n : ℕ) : Hist S := (s, List.replicate n s)

omit [Fintype S] in
/-- The node `nodeAt s n` is at date `n` (O&R §8.7). -/
theorem depth_nodeAt (s : S) (n : ℕ) : depth (nodeAt s n) = n := by
  simp [depth, nodeAt]

omit [Fintype S] in
/-- **Nonzero bubbles are unbounded**, so boundedness is exactly "no bubbles"
(O&R p. 582). -/
theorem depthBubble_unbounded [Nonempty S] {γ c : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hc : c ≠ 0) : ¬ ∃ b, ∀ h : Hist S, |depthBubble γ c h| ≤ b := by
  rintro ⟨b, hb⟩
  have hgt : 1 < γ⁻¹ := one_lt_inv_iff₀.2 ⟨hγ0, hγ1⟩
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop
    ((b + |1 / (1 - γ)|) / |c|)).exists
  have hcpos : 0 < |c| := abs_pos.2 hc
  have h1 := hb (nodeAt (Classical.arbitrary S) n)
  simp only [depthBubble, depth_nodeAt] at h1
  have h2 : |c * γ⁻¹ ^ n| ≤ b + |1 / (1 - γ)| := by
    have := abs_sub_abs_le_abs_sub (1 / (1 - γ) + c * γ⁻¹ ^ n) (1 / (1 - γ))
    simp only [add_sub_cancel_left] at this
    have := abs_add_le (1 / (1 - γ) + c * γ⁻¹ ^ n) (-(1 / (1 - γ)))
    rw [add_neg_cancel_comm, abs_neg] at this
    linarith
  rw [abs_mul, abs_of_pos (pow_pos (inv_pos.2 hγ0) n)] at h2
  rw [div_lt_iff₀ hcpos] at hn
  nlinarith

/-- **No monetary equilibrium when `1 + μ ≤ β`** (O&R (100), p. 583, where `1 + μ > β` is
assumed): if `γ ≥ 1` the linear equation has NO positive solution at all, bounded or not. -/
theorem no_positive_solution [Nonempty S] {γ : ℝ} (hγ : 1 ≤ γ)
    (hε : ∀ s, 0 < ε s) (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1)
    {w : Hist S → ℝ} (hw : LinearMoneyEq K ε γ w) : ¬ ∀ h, 0 < w h := by
  intro hpos
  have key : ∀ n : ℕ, ∀ h, (n : ℝ) ≤ w h := by
    intro n
    induction n with
    | zero => exact fun h => by simpa using (hpos h).le
    | succ n ih =>
      intro h
      have hQ : (n : ℝ) ≤ oneStep (tilt K ε) w h := by
        have := oneStep_mono (tilt_nonneg K hε) (X := fun _ => (n : ℝ)) (Y := w) ih h
        rwa [oneStep_const (tilt_sum K hE)] at this
      rw [hw h]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  let h0 : Hist S := (Classical.arbitrary S, [])
  obtain ⟨n, hn⟩ := exists_nat_gt (w h0)
  linarith [key n h0]

end Solutions

open Solutions

/-! ## Transversality -/

/-- The individual transversality condition `lim β^T E_t[u′(C_{t+T}) M_{t+T}/P_{t+T}] = 0`
(O&R fn 31, p. 542, carried to the stochastic model of §8.7), written in `w`
(`marginal_utility_real_balances`). -/
def TVC (K : Kernel S) (β : ℝ) (w : Hist S → ℝ) : Prop :=
  ∀ h, Tendsto (fun T : ℕ => β ^ T * iterStep K.trans T w h) atTop (𝓝 0)

/-- The fundamental solution `ω` satisfies the transversality condition (O&R (101)). -/
theorem omega_TVC (K : Kernel S) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ω : ℝ) :
    TVC K β (fun _ => ω) := by
  intro h
  simp only [iterStep_const K.trans_sum]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const ω

/-- **With nonnegative money growth, bubbles violate the transversality condition**
(O&R p. 582; the stochastic analogue of the deterministic argument of §8.3.5):
the deterministic bubble `ω + cγ^{−t}`, `c > 0`, fails the TVC when `μ ≥ 0`. -/
theorem depthBubble_not_TVC [Nonempty S] (K : Kernel S) {β μ c : ℝ} (hβ : 0 < β)
    (hμ : 0 ≤ μ) (hβμ : β < 1 + μ) (hc : 0 < c) :
    ¬ TVC K β (depthBubble (β / (1 + μ)) c) := by
  intro htvc
  set γ := β / (1 + μ)
  have hμ1 : 0 < 1 + μ := by linarith
  have hγ0 : 0 < γ := div_pos hβ hμ1
  have hγ1 : γ < 1 := (div_lt_one hμ1).2 hβμ
  let h0 : Hist S := (Classical.arbitrary S, [])
  have ht := htvc h0
  have hω : 0 < 1 / (1 - γ) := div_pos one_pos (by linarith)
  have key : ∀ T : ℕ, c ≤ β ^ T * iterStep K.trans T (depthBubble γ c) h0 := fun T => by
    rw [iterStep_depthBubble K.trans_sum]
    have hd : depth h0 = 0 := rfl
    rw [hd, zero_add]
    have e : β ^ T * (c * γ⁻¹ ^ T) = c * (1 + μ) ^ T := by
      rw [← mul_assoc, mul_comm (β ^ T) c, mul_assoc, ← mul_pow]
      congr 2
      simp only [γ]; field_simp
    have h1 : 1 ≤ (1 + μ) ^ T := one_le_pow₀ (by linarith)
    have h2 : 0 ≤ β ^ T * (1 / (1 - γ)) := mul_nonneg (pow_nonneg hβ.le T) hω.le
    rw [mul_add, e]
    nlinarith
  have := ge_of_tendsto' ht key
  linarith

/-- **With money SHRINKING (`μ < 0`), bubbles satisfy the transversality condition**
(O&R pp. 582–583: the book's uniqueness claim needs `μ ≥ 0`, as in the deterministic
case): the bubble `ω + cγ^{−t}` is then a second, bubbly, positive equilibrium. -/
theorem depthBubble_TVC_of_neg (K : Kernel S) {β μ c : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hμ : μ < 0) (hβμ : β < 1 + μ) : TVC K β (depthBubble (β / (1 + μ)) c) := by
  intro h
  set γ := β / (1 + μ)
  have hμ1 : 0 < 1 + μ := by linarith
  simp only [iterStep_depthBubble K.trans_sum]
  have e : ∀ T : ℕ, β ^ T * (1 / (1 - γ) + c * γ⁻¹ ^ (depth h + T))
      = β ^ T * (1 / (1 - γ)) + c * γ⁻¹ ^ depth h * (1 + μ) ^ T := fun T => by
    rw [mul_add, pow_add]
    have : β ^ T * γ⁻¹ ^ T = (1 + μ) ^ T := by
      rw [← mul_pow]; congr 1; simp only [γ]; field_simp
    rw [← this]; ring
  simp only [e]
  have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (1 / (1 - γ))
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hμ1.le (by linarith : 1 + μ < 1)).const_mul
    (c * γ⁻¹ ^ depth h)
  simpa using h1.add h2

/-- `E_t[1/ε_{t+1}] = 1` forces `min ε ≤ 1` (O&R (100), p. 583). -/
theorem min_eps_le_one (K : Kernel S) {ε : S → ℝ} {εm : ℝ} (hεm : 0 < εm)
    (hmin : ∀ s, εm ≤ ε s) (s : S) (hE : (K.row s).expect (fun s' => 1 / ε s') = 1) :
    εm ≤ 1 := by
  have h1 : (K.row s).expect (fun s' => 1 / ε s') ≤ (K.row s).expect (fun _ => 1 / εm) :=
    (K.row s).expect_mono fun s' => one_div_le_one_div_of_le hεm (hmin s')
  rw [hE, FinProb.expect_const] at h1
  rwa [le_div_iff₀ hεm, one_mul] at h1

/-- **Uniqueness of the monetary equilibrium from the transversality condition**
(O&R (101), p. 583, made precise): if `(1+μ) min ε ≥ 1`, every POSITIVE solution of (99)
that satisfies the transversality condition is `w ≡ ω`. (By `min_eps_le_one` this forces
`μ ≥ 0`; by `depthBubble_TVC_of_neg` uniqueness genuinely fails for `μ < 0`.) -/
theorem unique_of_TVC (K : Kernel S) {ε : S → ℝ} (hε : ∀ s, 0 < ε s)
    (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) {β μ εm : ℝ} (hβ : 0 < β)
    (hβμ : β < 1 + μ) (hεm : 0 < εm) (hmin : ∀ s, εm ≤ ε s) (hcond : 1 ≤ (1 + μ) * εm)
    {w : Hist S → ℝ} (hw : LinearMoneyEq K ε (β / (1 + μ)) w) (hpos : ∀ h, 0 < w h)
    (htvc : TVC K β w) (h : Hist S) : w h = 1 / (1 - β / (1 + μ)) := by
  set γ := β / (1 + μ)
  set ω := 1 / (1 - γ)
  have hμ1 : 0 < 1 + μ := by linarith
  have hγ0 : 0 < γ := div_pos hβ hμ1
  have hγ1 : γ < 1 := (div_lt_one hμ1).2 hβμ
  have hω : 0 < ω := div_pos one_pos (by linarith)
  set B : Hist S → ℝ := fun g => w g - ω
  have hB0 : ∀ g, 0 ≤ B g := fun g => by
    simp only [B]; linarith [ge_omega_of_pos K hε hE hγ0.le hγ1 hw hpos g]
  have hB := (linear_iff_bubble K hE hγ1.ne w).1 hw
  have hcmp : ∀ s s', tilt K ε s s' ≤ εm⁻¹ * K.trans s s' := fun s s' => by
    simp only [tilt]
    rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hεm (hmin s')) (K.trans_nonneg s s')
  have hwB : w = fun g => ω + B g := funext fun g => by simp [B]
  have key : ∀ T : ℕ, B h ≤ β ^ T * iterStep K.trans T w h := fun T => by
    have h1 := bubble_iterate hB T h
    have h2 := iterStep_le_pow_mul (inv_nonneg.2 hεm.le) (tilt_nonneg K hε) K.trans_nonneg
      hcmp T hB0 h
    have hX : 0 ≤ iterStep K.trans T B h := iterStep_nonneg K.trans_nonneg T hB0 h
    have h3 : β ^ T * iterStep K.trans T w h
        = β ^ T * ω + β ^ T * iterStep K.trans T B h := by
      rw [hwB, iterStep_add_fun, iterStep_const K.trans_sum, mul_add]
    have hβsplit : β = ((1 + μ) * εm) * (γ * εm⁻¹) := by
      simp only [γ]; field_simp
    have h4 : B h ≤ (γ * εm⁻¹) ^ T * iterStep K.trans T B h := by
      calc B h = γ ^ T * iterStep (tilt K ε) T B h := h1
        _ ≤ γ ^ T * (εm⁻¹ ^ T * iterStep K.trans T B h) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg hγ0.le T)
        _ = (γ * εm⁻¹) ^ T * iterStep K.trans T B h := by rw [mul_pow, mul_assoc]
    have h5 : 1 ≤ ((1 + μ) * εm) ^ T := one_le_pow₀ hcond
    have h6 : β ^ T * iterStep K.trans T B h
        = ((1 + μ) * εm) ^ T * ((γ * εm⁻¹) ^ T * iterStep K.trans T B h) := by
      rw [hβsplit, mul_pow, mul_assoc]
    have h7 : 0 ≤ β ^ T * ω := mul_nonneg (pow_nonneg hβ.le T) hω.le
    rw [h3, h6]
    nlinarith [hB0 h]
  have := ge_of_tendsto' (htvc h) key
  have : B h = 0 := le_antisymm this (hB0 h)
  simp only [B] at this
  linarith

/-- **Deterministic money growth** (`ε ≡ 1`): the transversality condition selects `ω`
exactly when `μ ≥ 0` (O&R (100)–(101), p. 583, with the book's §8.3.5 condition). -/
theorem unique_of_TVC_deterministic (K : Kernel S) {β μ : ℝ} (hβ : 0 < β) (hβμ : β < 1 + μ)
    (hμ : 0 ≤ μ) {w : Hist S → ℝ} (hw : LinearMoneyEq K (fun _ => 1) (β / (1 + μ)) w)
    (hpos : ∀ h, 0 < w h) (htvc : TVC K β w) (h : Hist S) :
    w h = 1 / (1 - β / (1 + μ)) :=
  unique_of_TVC K (fun _ => one_pos) (fun s => by simp [FinProb.expect_const]) hβ hβμ
    one_pos (fun _ => le_rfl) (by linarith) hw hpos htvc h

/-- **Stationary Markov equilibria**: a solution that depends only on the current state is
`ω` (finite state space, so automatically bounded) (O&R (101), p. 583). -/
theorem markov_unique (K : Kernel S) {ε : S → ℝ} (hε : ∀ s, 0 < ε s)
    (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) {v : S → ℝ} (hv : ∀ s, v s = 1 + γ * ∑ s', tilt K ε s s' * v s') (s : S) :
    v s = 1 / (1 - γ) := by
  have hw : LinearMoneyEq K ε γ (fun g => v g.1) := fun g => hv g.1
  have hb : ∀ g : Hist S, |v g.1| ≤ ∑ t, |v t| := fun g =>
    Finset.single_le_sum (f := fun t => |v t|) (fun t _ => abs_nonneg _) (Finset.mem_univ _)
  exact unique_bounded K hε hE hγ0 hγ1 hw hb (s, [])

/-! ## Consequences: the price level and the nominal interest rate -/

/-- **The equilibrium price level** `P_t = M_t (1 − β/(1+μ)) (xY^W_t)^{−ρ}` (O&R p. 583). -/
theorem price_level_formula {ρ x β μ M P Y : ℝ} (hx : 0 < x) (hP : 0 < P)
    (hY : 0 < Y) (hβμ : β < 1 + μ) (hμ : 0 < 1 + μ)
    (hw : M / (P * (x * Y) ^ ρ) = 1 / (1 - β / (1 + μ))) :
    P = M * (1 - β / (1 + μ)) * (x * Y) ^ (-ρ) := by
  have ha : 0 < (x * Y) ^ ρ := Real.rpow_pos_of_pos (mul_pos hx hY) ρ
  have h1 : 1 - β / (1 + μ) ≠ 0 := by
    have : β / (1 + μ) < 1 := (div_lt_one hμ).2 hβμ
    linarith
  rw [Real.rpow_neg (mul_pos hx hY).le]
  field_simp at hw ⊢
  rw [hw]
  have : 1 + μ - β ≠ 0 := by linarith
  field_simp

/-- **The price level does not depend on expected future output** (O&R p. 583): two
economies in the bubble-free equilibrium with the same current money and output have the
same current price level, whatever their output processes and kernels. -/
theorem price_level_independent_of_future_output {ρ x β μ : ℝ} {M₁ P₁ Y₁ M₂ P₂ Y₂ : ℝ}
    (hx : 0 < x) (hP₁ : 0 < P₁) (hY₁ : 0 < Y₁) (hP₂ : 0 < P₂) (hY₂ : 0 < Y₂)
    (hβμ : β < 1 + μ) (hμ : 0 < 1 + μ)
    (hw₁ : M₁ / (P₁ * (x * Y₁) ^ ρ) = 1 / (1 - β / (1 + μ)))
    (hw₂ : M₂ / (P₂ * (x * Y₂) ^ ρ) = 1 / (1 - β / (1 + μ))) (hM : M₁ = M₂)
    (hY : Y₁ = Y₂) : P₁ = P₂ := by
  rw [price_level_formula hx hP₁ hY₁ hβμ hμ hw₁,
    price_level_formula hx hP₂ hY₂ hβμ hμ hw₂, hM, hY]

/-- **Higher expected money growth lowers real-balance demand** (O&R p. 583): `ω` is
strictly decreasing in `μ` on `1 + μ > β`, `β > 0`. -/
theorem omega_strictAnti {β μ₁ μ₂ : ℝ} (hβ : 0 < β) (h₁ : β < 1 + μ₁) (h12 : μ₁ < μ₂) :
    (1 + μ₂) / (1 + μ₂ - β) < (1 + μ₁) / (1 + μ₁ - β) := by
  have a1 : 0 < 1 + μ₁ - β := by linarith
  have a2 : 0 < 1 + μ₂ - β := by linarith
  rw [div_lt_div_iff₀ a2 a1]
  nlinarith

/-- **Higher current income raises real-balance demand** (O&R p. 583): with `ρ > 0`,
`M/P = ω (xY^W)^ρ` is strictly increasing in `Y^W`. -/
theorem real_balances_strictMono {ω x ρ Y₁ Y₂ : ℝ} (hω : 0 < ω) (hx : 0 < x) (hρ : 0 < ρ)
    (hY : 0 < Y₁) (h12 : Y₁ < Y₂) : ω * (x * Y₁) ^ ρ < ω * (x * Y₂) ^ ρ :=
  mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (mul_pos hx hY).le
    (mul_lt_mul_of_pos_left h12 hx) hρ) hω

/-- **The nominal interest rate** `1 + i = (1+μ)/β` (O&R p. 583): in the bubble-free
equilibrium the CRRA nominal-bond Euler equation (95),
`1 = (1+i) β E_t[(P_t/P_{t+1})(Y^W_t/Y^W_{t+1})^ρ]`, pins `i` independently of the
distribution of future output. -/
theorem nominal_rate_eq (K : Kernel S) {β μ ρ x i : ℝ} {M P Y : Hist S → ℝ} {ε : S → ℝ}
    (hx : 0 < x) (hM : ∀ h, 0 < M h) (hP : ∀ h, 0 < P h) (hY : ∀ h, 0 < Y h)
    (hμ : 0 < 1 + μ) (hβ : 0 < β) (hβμ : β < 1 + μ) (hε : ∀ s, 0 < ε s)
    (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1)
    (hgrowth : ∀ h s', M (next h s') = M h * (1 + μ) * ε s')
    (hw : ∀ h, realBal ρ x M P Y h = 1 / (1 - β / (1 + μ))) (h : Hist S)
    (h95 : 1 = (1 + i) * β
      * (K.row h.1).expect (fun s' => P h / P (next h s') * (Y h / Y (next h s')) ^ ρ)) :
    1 + i = (1 + μ) / β := by
  set ω := 1 / (1 - β / (1 + μ))
  have hγ1 : β / (1 + μ) < 1 := (div_lt_one hμ).2 hβμ
  have hω : 0 < ω := div_pos one_pos (by linarith)
  have hE' : (K.row h.1).expect (fun s' => P h / P (next h s') * (Y h / Y (next h s')) ^ ρ)
      = 1 / (1 + μ) := by
    have e : (fun s' => P h / P (next h s') * (Y h / Y (next h s')) ^ ρ)
        = fun s' => 1 / (1 + μ) * (1 / ω) * (ω * (1 / ε s')) := by
      funext s'
      rw [price_ratio_term_eq hx (hM h) (hP h) (hY h) (hP _) (hY _) hμ (hε s')]
      have h1 : P h * (x * Y h) ^ ρ / M h = 1 / ω := by
        rw [← hw h]; simp only [realBal]; field_simp
      have h2 : M h * (1 + μ) * ε s' / (P (next h s') * (x * Y (next h s')) ^ ρ) / ε s'
          = ω * (1 / ε s') := by
        rw [← hw (next h s')]; simp only [realBal, hgrowth]; field_simp
      rw [h1, h2]
    rw [e, FinProb.expect_mul_left, FinProb.expect_mul_left, hE h.1]
    field_simp
  rw [hE'] at h95
  field_simp at h95 ⊢
  linarith

/-- The equilibrium nominal rate satisfies the money-demand condition
`v′/u′ = 1/ω = 1 − β/(1+μ) = i/(1+i)` (O&R p. 582–583). -/
theorem money_demand_at_equilibrium {β μ i : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hi : 1 + i = (1 + μ) / β) : i / (1 + i) = 1 - β / (1 + μ) := by
  have : i = (1 + μ) / β - 1 := by linarith
  rw [hi, this]
  field_simp

/-! ## The money-growth shock must be positive (100) -/

/-- Next period's money stock is positive iff the shock is (O&R (100), p. 583: the book's
"nonnegative" must be "positive"). -/
theorem next_money_pos_iff {M μ e : ℝ} (hM : 0 < M) (hμ : 0 < 1 + μ) :
    0 < M * (1 + μ) * e ↔ 0 < e := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have : M * (1 + μ) * e ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  · intro h; positivity

omit [Fintype S] in
/-- **A zero shock destroys the monetary equilibrium** (O&R (100), p. 583): if `ε(s′) = 0`
for some state then money vanishes at the successor node, so no equilibrium with positive
money (and finite `log(M/P)`) exists. Hence `ε > 0` is required, not `ε ≥ 0`. -/
theorem no_positive_money_of_eps_zero [Nonempty S] {M : Hist S → ℝ} {μ : ℝ} {ε : S → ℝ}
    (hgrowth : ∀ h s', M (next h s') = M h * (1 + μ) * ε s') {s' : S} (hz : ε s' = 0) :
    ¬ ∀ h, 0 < M h := by
  intro hpos
  have := hpos (next (Classical.arbitrary S, []) s')
  rw [hgrowth, hz, mul_zero] at this
  exact lt_irrefl 0 this

/-- **`E[1/ε] = 1` implies `E[ε] ≥ 1`** (O&R (100), p. 583): expected gross money growth is
at least `1 + μ`. -/
theorem one_le_expect_eps (Ω : FinProb S) {ε : S → ℝ} (hε : ∀ s, 0 < ε s)
    (hE : Ω.expect (fun s => 1 / ε s) = 1) : 1 ≤ Ω.expect ε := by
  have h2 : Ω.expect (fun _ => (2 : ℝ)) ≤ Ω.expect (fun s => ε s + 1 / ε s) :=
    Ω.expect_mono fun s => by
      have := hε s
      have e : ε s + 1 / ε s - 2 = (ε s - 1) ^ 2 / ε s := by field_simp; ring
      have : 0 ≤ (ε s - 1) ^ 2 / ε s := div_nonneg (sq_nonneg _) this.le
      linarith
  rw [Ω.expect_const, Ω.expect_add, hE] at h2
  linarith

/-- Expected gross money growth `E_t[M_{t+1}/M_t] = (1+μ) E_t ε ≥ 1 + μ` (O&R (100),
p. 583). -/
theorem expected_money_growth (Ω : FinProb S) {M μ : ℝ} {ε : S → ℝ} (hM : 0 < M)
    (hμ : 0 < 1 + μ) (hε : ∀ s, 0 < ε s) (hE : Ω.expect (fun s => 1 / ε s) = 1) :
    Ω.expect (fun s => M * (1 + μ) * ε s / M) = (1 + μ) * Ω.expect ε ∧
      1 + μ ≤ Ω.expect (fun s => M * (1 + μ) * ε s / M) := by
  have e : (fun s => M * (1 + μ) * ε s / M) = fun s => (1 + μ) * ε s := by
    funext s; field_simp
  rw [e, Ω.expect_mul_left]
  refine ⟨rfl, ?_⟩
  have := one_le_expect_eps Ω hε hE
  nlinarith

/-- An i.i.d. two-state kernel (O&R (100), p. 583: a concrete money-growth process). -/
noncomputable def exampleKernel : Kernel Bool :=
  ⟨fun _ _ => 1 / 2, fun _ _ => by norm_num, fun _ => by simp⟩

/-- The shocks `ε ∈ {2, 2/3}` (O&R (100), p. 583). -/
noncomputable def exampleEps : Bool → ℝ := fun b => if b then 2 else 2 / 3

/-- **The hypotheses of (100) are satisfiable with a nondegenerate shock**: `E[1/ε] = 1`
while `E[ε] = 4/3` (O&R (100), p. 583). -/
theorem example_eps_moments (s : Bool) :
    (exampleKernel.row s).expect (fun s' => 1 / exampleEps s') = 1 ∧
      (exampleKernel.row s).expect exampleEps = 4 / 3 := by
  simp [FinProb.expect, Kernel.row, exampleKernel, exampleEps]
  norm_num

/-! ## The log-linearised model (§8.7.3) -/

/-- The stochastic Cagan equation `m_t − q_t = −η (E_t q_{t+1} − q_t)` at every node
(O&R p. 584, "resembles the Cagan equation"). -/
def CaganTree (K : Kernel S) (η : ℝ) (m q : Hist S → ℝ) : Prop :=
  ∀ h, m h - q h = -η * (oneStep K.trans q h - q h)

/-- **The log-linear price equation is a Cagan equation in `q = p + ρ y^W`** with
`η = 1/ī` (O&R p. 584). -/
theorem logLinear_iff_cagan (K : Kernel S) {ibar ρ : ℝ} {m p y : Hist S → ℝ} :
    (∀ h, m h - p h = ρ * y h - 1 / ibar * (oneStep K.trans p h - p h)
        - ρ / ibar * (oneStep K.trans y h - y h)) ↔
      CaganTree K (1 / ibar) m (fun g => p g + ρ * y g) := by
  refine forall_congr' fun h => ?_
  rw [oneStep_add, oneStep_mul_left]
  beta_reduce
  constructor <;> intro H <;> linear_combination H

/-- The fundamental (no-bubble) solution
`q_t = (1/(1+η)) Σ_j (η/(1+η))^j E_t m_{t+j}` (O&R p. 584). -/
noncomputable def fundamental (K : Kernel S) (η : ℝ) (m : Hist S → ℝ) : Hist S → ℝ :=
  fun h => 1 / (1 + η) * ∑' j : ℕ, (η / (1 + η)) ^ j * iterStep K.trans j m h

/-- The stochastic no-bubble condition `lim (η/(1+η))ⁿ E_t q_{t+n} = 0` (O&R (8), p. 518,
carried to §8.7.3). -/
def NoBubble (K : Kernel S) (η : ℝ) (q : Hist S → ℝ) : Prop :=
  ∀ h, Tendsto (fun n : ℕ => (η / (1 + η)) ^ n * iterStep K.trans n q h) atTop (𝓝 0)

/-- `E_t` commutes with convergent sums (O&R p. 584). -/
theorem oneStep_tsum (k : S → S → ℝ) {a : ℕ → Hist S → ℝ}
    (ha : ∀ g, Summable fun j => a j g) (h : Hist S) :
    oneStep k (fun g => ∑' j, a j g) h = ∑' j, oneStep k (a j) h := by
  simp only [oneStep]
  rw [Summable.tsum_finsetSum fun s' _ => (ha _).mul_left _]
  exact Finset.sum_congr rfl fun s' _ => (tsum_mul_left).symm

/-- `E_t` preserves summability (O&R p. 584). -/
theorem oneStep_summable (k : S → S → ℝ) {a : ℕ → Hist S → ℝ}
    (ha : ∀ g, Summable fun j => a j g) (g : Hist S) :
    Summable fun j => oneStep k (a j) g := by
  simp only [oneStep]
  exact summable_sum fun s' _ => (ha _).mul_left _

/-- `E_t X_{t+n}` commutes with convergent sums (O&R p. 584). -/
theorem iterStep_tsum (k : S → S → ℝ) (n : ℕ) {a : ℕ → Hist S → ℝ}
    (ha : ∀ g, Summable fun j => a j g) (h : Hist S) :
    iterStep k n (fun g => ∑' j, a j g) h = ∑' j, iterStep k n (a j) h := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [iterStep_succ, show oneStep k (fun g => ∑' j, a j g)
      = fun g => ∑' j, oneStep k (a j) g from funext fun g => oneStep_tsum k ha g,
      ih (oneStep_summable k ha)]
    simp only [iterStep_succ]

/-- **The fundamental solution solves the stochastic Cagan equation** (O&R p. 584), given
convergence of the discounted expected money path at every node. -/
theorem fundamental_solves (K : Kernel S) {η : ℝ} (hη : 0 < η) {m : Hist S → ℝ}
    (hsum : ∀ g, Summable fun j => (η / (1 + η)) ^ j * iterStep K.trans j m g) :
    CaganTree K η m (fundamental K η m) := by
  intro h
  set θ := η / (1 + η)
  have hE1 : oneStep K.trans (fundamental K η m) h
      = 1 / (1 + η) * ∑' j : ℕ, θ ^ j * iterStep K.trans (j + 1) m h := by
    rw [show fundamental K η m = fun g => 1 / (1 + η) * ∑' j : ℕ, θ ^ j * iterStep K.trans j m g
      from rfl, oneStep_mul_left, oneStep_tsum K.trans hsum]
    congr 2; funext j
    rw [oneStep_mul_left, ← iterStep_succ']
  have hsplit := (hsum h).tsum_eq_zero_add
  have hT : ∑' j : ℕ, θ ^ (j + 1) * iterStep K.trans (j + 1) m h
      = θ * ∑' j : ℕ, θ ^ j * iterStep K.trans (j + 1) m h := by
    rw [← tsum_mul_left]; congr 1; funext j; ring
  set T' := ∑' j : ℕ, θ ^ j * iterStep K.trans (j + 1) m h with hT'
  have hq : fundamental K η m h = 1 / (1 + η) * (m h + θ * T') := by
    change 1 / (1 + η) * ∑' j : ℕ, θ ^ j * iterStep K.trans j m h = _
    rw [hsplit, hT]
    simp only [pow_zero, one_mul]
    rfl
  rw [hE1, hq]
  simp only [θ]
  field_simp
  ring

/-- **The fundamental solution satisfies the no-bubble condition** (O&R p. 584). -/
theorem fundamental_noBubble (K : Kernel S) {η : ℝ} {m : Hist S → ℝ}
    (hsum : ∀ g, Summable fun j => (η / (1 + η)) ^ j * iterStep K.trans j m g) :
    NoBubble K η (fundamental K η m) := by
  intro h
  set θ := η / (1 + η)
  have e : ∀ n : ℕ, θ ^ n * iterStep K.trans n (fundamental K η m) h
      = 1 / (1 + η) * ∑' j : ℕ, θ ^ (j + n) * iterStep K.trans (j + n) m h := fun n => by
    rw [show fundamental K η m = fun g => 1 / (1 + η) * ∑' j : ℕ, θ ^ j * iterStep K.trans j m g
      from rfl, iterStep_mul_left, iterStep_tsum K.trans n hsum, ← mul_assoc, mul_comm (θ ^ n),
      mul_assoc, ← tsum_mul_left]
    congr 2; funext j
    rw [iterStep_mul_left, ← iterStep_add, pow_add, add_comm n j]
    ring
  simp only [e]
  simpa using (tendsto_sum_nat_add fun k => θ ^ k * iterStep K.trans k m h).const_mul
    (1 / (1 + η))

/-- **Uniqueness**: two solutions of the stochastic Cagan equation that both satisfy the
no-bubble condition coincide at every node (O&R p. 584). -/
theorem cagan_unique (K : Kernel S) {η : ℝ} (hη : 0 < η) {m q₁ q₂ : Hist S → ℝ}
    (h₁ : CaganTree K η m q₁) (h₂ : CaganTree K η m q₂) (hb₁ : NoBubble K η q₁)
    (hb₂ : NoBubble K η q₂) (h : Hist S) : q₁ h = q₂ h := by
  set θ := η / (1 + η)
  set d : Hist S → ℝ := fun g => q₁ g - q₂ g
  have hd : ∀ g, d g = θ * oneStep K.trans d g := fun g => by
    simp only [d, θ, oneStep_sub]
    have e1 := h₁ g
    have e2 := h₂ g
    field_simp
    linarith
  have key : ∀ n : ℕ, d h = θ ^ n * iterStep K.trans n q₁ h
      - θ ^ n * iterStep K.trans n q₂ h := fun n => by
    rw [bubble_iterate hd n h, iterStep_sub_fun]; ring
  have ht := (hb₁ h).sub (hb₂ h)
  rw [sub_zero] at ht
  have ht2 : Tendsto (fun _ : ℕ => d h) atTop (𝓝 0) := ht.congr fun n => (key n).symm
  have := tendsto_nhds_unique tendsto_const_nhds ht2
  simp only [d] at this
  linarith

/-- **The log-linear price level** (O&R p. 584):
`p_t = −ρ y^W_t + (ī/(1+ī)) Σ_{s≥t} (1+ī)^{−(s−t)} E_t m_s` is the unique solution of the
log-linearised equation for which `p + ρ y^W` has no bubble. -/
theorem logLinear_price_solution (K : Kernel S) {ibar ρ : ℝ} (hi : 0 < ibar)
    {m p y : Hist S → ℝ}
    (hsum : ∀ g, Summable fun j => (1 / (1 + ibar)) ^ j * iterStep K.trans j m g)
    (heq : ∀ h, m h - p h = ρ * y h - 1 / ibar * (oneStep K.trans p h - p h)
        - ρ / ibar * (oneStep K.trans y h - y h))
    (hnb : NoBubble K (1 / ibar) (fun g => p g + ρ * y g)) (h : Hist S) :
    p h = -ρ * y h + ibar / (1 + ibar)
      * ∑' j : ℕ, (1 / (1 + ibar)) ^ j * iterStep K.trans j m h := by
  have hθ : 1 / ibar / (1 + 1 / ibar) = 1 / (1 + ibar) := by field_simp; ring
  have hc : 1 / (1 + 1 / ibar) = ibar / (1 + ibar) := by field_simp; ring
  have hsum' : ∀ g, Summable fun j => (1 / ibar / (1 + 1 / ibar)) ^ j
      * iterStep K.trans j m g := by rw [hθ]; exact hsum
  have hq := cagan_unique K (one_div_pos.2 hi) ((logLinear_iff_cagan K).1 heq)
    (fundamental_solves K (one_div_pos.2 hi) hsum') hnb (fundamental_noBubble K hsum') h
  simp only [fundamental, hθ, hc] at hq
  linarith

/-! ## The stochastic cash-in-advance model (§8.7.4) -/

/-- **(103)**: a binding cash-in-advance constraint `M = P Y` gives `P = M/Y`
(O&R (103), p. 585). -/
theorem cia_price_level {M P Y : ℝ} (hY : 0 < Y) (hbind : M = P * Y) : P = M / Y := by
  rw [hbind]; field_simp

/-- Constant (unit) velocity under the cash-in-advance constraint (O&R p. 585: "a constant
velocity of money"). -/
theorem cia_velocity {M P Y : ℝ} (hM : 0 < M) (hbind : M = P * Y) : P * Y / M = 1 := by
  rw [← hbind]; exact div_self hM.ne'

/-- The cash-in-advance exchange rate from PPP (92) and (103):
`ℰ^{nm} = (Mⁿ/Yⁿ)/(M^m/Y^m)` (O&R (92), (103), pp. 580, 585). -/
theorem cia_exchange_rate {Mn Yn Mm Ym Pn Pm E : ℝ} (hYn : 0 < Yn) (hYm : 0 < Ym)
    (hPm : 0 < Pm) (hn : Mn = Pn * Yn) (hm : Mm = Pm * Ym) (hppp : Pn = E * Pm) :
    E = (Mn / Yn) / (Mm / Ym) := by
  rw [hn, hm, hppp]
  field_simp

/-- **The CIA nominal rate equals the MIU one with log utility** (O&R p. 585: "nominal
interest rates ... are determined just as in the preceding money-in-the-utility-function
model"): with `u = log`, `C = xY`, `P = M/Y` and `M′ = M(1+μ)ε`, `E[1/ε] = 1`,
`β E_t[(P_t/P_{t+1})(C_t/C_{t+1})] = β/(1+μ)`, so `1 + i = (1+μ)/β`. -/
theorem cia_bond_price_log (Ω : FinProb S) {β μ x M Y : ℝ} {Y' ε : S → ℝ} (hx : 0 < x)
    (hM : 0 < M) (hY : 0 < Y) (hY' : ∀ s, 0 < Y' s) (hμ : 0 < 1 + μ) (hε : ∀ s, 0 < ε s)
    (hE : Ω.expect (fun s => 1 / ε s) = 1) :
    β * Ω.expect (fun s => (M / Y) / (M * (1 + μ) * ε s / Y' s) * (x * Y / (x * Y' s)))
      = β / (1 + μ) := by
  have e : (fun s => (M / Y) / (M * (1 + μ) * ε s / Y' s) * (x * Y / (x * Y' s)))
      = fun s => 1 / (1 + μ) * (1 / ε s) := by
    funext s
    have := hY' s; have := hε s
    field_simp
  rw [e, Ω.expect_mul_left, hE]
  ring

/-! ## Currency substitution: dollarization (§8.3.8) -/

/-- **A positive home nominal interest rate is implied by the money Euler equation (65)**
(O&R (64)–(65), p. 552): with `(1+r)β = 1`, `u′(C_t) = u′(C_{t+1}) = U > 0` and a positive
marginal liquidity value `V = v′(·) > 0`, (65) forces `1 − βP_t/P_{t+1} > 0`, i.e. `i > 0`
(`1 + i = P_{t+1}/(βP_t)`). The book's (67) divides by this quantity. -/
theorem dollarization_home_rate_pos {U V β P P' : ℝ} (hU : 0 < U) (hV : 0 < V) (hP : 0 < P)
    (hP' : 0 < P') (h65 : 1 / P * U = 1 / P * V + 1 / P' * β * U) :
    0 < 1 - β * P / P' := by
  have : V = U * (1 - β * P / P') := by field_simp at h65 ⊢; linarith
  have h := hV
  rw [this] at h
  exact pos_of_mul_pos_right h hU.le

/-- **The foreign-currency first-order condition** (O&R (64)–(66) and the display before
(67), p. 552): `g′(M_F/P*) = (1 − βP*_t/P*_{t+1})/(1 − βP_t/P_{t+1})`. -/
theorem dollarization_foc {U V gp β P P' Ps Ps' : ℝ} (hU : 0 < U) (hV : 0 < V) (hP : 0 < P)
    (hP' : 0 < P') (hPs : 0 < Ps) (hPs' : 0 < Ps')
    (h65 : 1 / P * U = 1 / P * V + 1 / P' * β * U)
    (h66 : 1 / Ps * U = 1 / Ps * V * gp + 1 / Ps' * β * U) :
    gp = (1 - β * Ps / Ps') / (1 - β * P / P') := by
  have hpos := dollarization_home_rate_pos hU hV hP hP' h65
  have hV' : V = U * (1 - β * P / P') := by field_simp at h65 ⊢; linarith
  have hg : V * gp = U * (1 - β * Ps / Ps') := by field_simp at h66 ⊢; linarith
  rw [hV', mul_assoc] at hg
  have hg' : (1 - β * P / P') * gp = 1 - β * Ps / Ps' := mul_left_cancel₀ hU.ne' hg
  rw [eq_div_iff hpos.ne']
  linarith [hg']

/-- **Foreign-currency demand (67)** (O&R (67), p. 553): with `g(x) = a₀x − (a₁/2)x²`,
`g′(x) = a₀ − a₁x`, the interior holdings are `M_F/P* = (a₀ − ratio)/a₁`, positive iff
`a₀ > ratio`. -/
theorem dollarization_demand {a0 a1 x ratio : ℝ} (ha1 : 0 < a1) (hfoc : a0 - a1 * x = ratio) :
    x = (a0 - ratio) / a1 ∧ (0 < x ↔ ratio < a0) := by
  have hx : x = (a0 - ratio) / a1 := by field_simp; linarith
  refine ⟨hx, ?_⟩
  rw [hx, div_pos_iff_of_pos_right ha1, sub_pos]

/-- **No dollarization when home inflation does not exceed foreign inflation** (O&R p. 552,
"there is no point to using foreign currency since `a₀ ≤ 1`"): if `π ≤ π*` (gross
inflation factors) and the home nominal rate is positive, the ratio in (67) is at least `1`,
so `a₀ ≤ 1` rules out positive interior holdings. -/
theorem no_dollarization_of_low_inflation {β π πs a0 : ℝ} (hβ : 0 < β) (hπ : 0 < π)
    (hhome : 0 < 1 - β / π) (hle : π ≤ πs) (ha0 : a0 ≤ 1) :
    a0 ≤ (1 - β / πs) / (1 - β / π) := by
  have : β / πs ≤ β / π := div_le_div_of_nonneg_left hβ.le hπ hle
  rw [le_div_iff₀ hhome]
  nlinarith

/-- **Foreign-currency holdings rise with home inflation** (O&R p. 553): the ratio in (67)
is strictly decreasing in home inflation `π` when both nominal rates are positive, so the
interior `M_F/P*` is strictly increasing in `π`. -/
theorem dollarization_ratio_strictAnti {β π₁ π₂ πs : ℝ} (hβ : 0 < β) (hπ₁ : 0 < π₁)
    (h12 : π₁ < π₂) (hfor : 0 < 1 - β / πs) (hhome : 0 < 1 - β / π₁) :
    (1 - β / πs) / (1 - β / π₂) < (1 - β / πs) / (1 - β / π₁) := by
  have hπ₂ : 0 < π₂ := by linarith
  have h : β / π₂ < β / π₁ := div_lt_div_of_pos_left hβ hπ₁ h12
  have hhome2 : 0 < 1 - β / π₂ := by linarith
  exact (div_lt_div_iff_of_pos_left hfor hhome2 hhome).2 (by linarith)

/-- **The role of `a₀ > 1 − β`** (O&R p. 552, with constant foreign prices `π* = 1`):
if `a₀ > 1 − β`, foreign currency is held at all sufficiently high home inflation rates;
if `a₀ ≤ 1 − β` it is never held (for any `π > β`). -/
theorem dollarization_threshold {β a0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (1 - β < a0 → ∃ πbar, ∀ π, πbar < π → (1 - β) / (1 - β / π) < a0) ∧
      (a0 ≤ 1 - β → ∀ π, β < π → a0 < (1 - β) / (1 - β / π)) := by
  constructor
  · intro ha
    have h1 : 0 < 1 - β := by linarith
    -- choose π̄ so that β/π < 1 − (1−β)/a0
    have ha0 : 0 < a0 := by linarith
    set δ := 1 - (1 - β) / a0
    have hδ : 0 < δ := by
      simp only [δ]; rw [sub_pos, div_lt_one ha0]; exact ha
    refine ⟨max β (β / δ), fun π hπ => ?_⟩
    have hπβ : β < π := lt_of_le_of_lt (le_max_left _ _) hπ
    have hπ0 : 0 < π := by linarith
    have hπδ : β / δ < π := lt_of_le_of_lt (le_max_right _ _) hπ
    have hden : 0 < 1 - β / π := by rw [sub_pos, div_lt_one hπ0]; exact hπβ
    have hsmall : β / π < δ := by
      rw [div_lt_iff₀ hπ0]; rw [div_lt_iff₀ hδ] at hπδ; linarith
    rw [div_lt_iff₀ hden]
    simp only [δ] at hsmall
    have : (1 - β) / a0 * a0 = 1 - β := by field_simp
    nlinarith
  · intro ha π hπ
    have hπ0 : 0 < π := by linarith
    have hden : 0 < 1 - β / π := by rw [sub_pos, div_lt_one hπ0]; exact hπ
    have hden1 : 1 - β / π < 1 := by have := div_pos hβ0 hπ0; linarith
    have : 1 - β < (1 - β) / (1 - β / π) := by
      rw [lt_div_iff₀ hden]; nlinarith
    linarith

/-! ## The household problem on the event tree: global optimality (§8.7.1–8.7.2) -/

/-- Extend a node by a list of future states, earliest first (O&R §8.7.1, p. 579: the
event tree of histories). -/
def extend : Hist S → List S → Hist S
  | h, [] => h
  | h, s :: l => extend (next h s) l

/-- `g` is a descendant of `h` (possibly `h` itself) (O&R §8.7.1). -/
def Desc (h g : Hist S) : Prop := ∃ l : List S, extend h l = g

omit [Fintype S] in
/-- Every node descends from itself (O&R §8.7.1). -/
theorem desc_refl (h : Hist S) : Desc h h := ⟨[], rfl⟩

omit [Fintype S] in
/-- Descendants of a child are descendants of the parent (O&R §8.7.1). -/
theorem desc_of_desc_next {h g : Hist S} (s : S) (hd : Desc (next h s) g) : Desc h g := by
  obtain ⟨l, hl⟩ := hd
  exact ⟨s :: l, hl⟩

omit [Fintype S] in
/-- Appending a state to the extension moves to a child (O&R §8.7.1). -/
theorem extend_append (h : Hist S) (l : List S) (s : S) :
    extend h (l ++ [s]) = next (extend h l) s := by
  induction l generalizing h with
  | nil => rfl
  | cons t l ih => exact ih (next h t)

omit [Fintype S] in
/-- Children of descendants are descendants (O&R §8.7.1). -/
theorem desc_next {h g : Hist S} (hd : Desc h g) (s : S) : Desc h (next g s) := by
  obtain ⟨l, rfl⟩ := hd
  exact ⟨l ++ [s], extend_append h l s⟩

omit [Fintype S] in
/-- Extension moves forward in time by the length of the list (O&R §8.7.1). -/
theorem depth_extend (h : Hist S) (l : List S) : depth (extend h l) = depth h + l.length := by
  induction l generalizing h with
  | nil => rfl
  | cons t l ih =>
    simp only [extend, ih, depth_next, List.length_cons]
    ring

/-- `E_t X_{t+n}` is monotone in the values of `X` on the subtree below the node
(O&R §8.7.1). -/
theorem iterStep_mono_desc {k : S → S → ℝ} (hk : ∀ s s', 0 ≤ k s s') (n : ℕ)
    {X Y : Hist S → ℝ} {h : Hist S} (hXY : ∀ g, Desc h g → X g ≤ Y g) :
    iterStep k n X h ≤ iterStep k n Y h := by
  induction n generalizing h with
  | zero => exact hXY h (desc_refl h)
  | succ n ih =>
    rw [iterStep_succ', iterStep_succ']
    exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
      (ih fun g hg => hXY g (desc_of_desc_next s hg)) (hk _ _)

/-- `E_t X_{t+n}` depends only on the values of `X` on the subtree below the node
(O&R §8.7.1). -/
theorem iterStep_congr_desc (k : S → S → ℝ) (n : ℕ) {X Y : Hist S → ℝ} {h : Hist S}
    (hXY : ∀ g, Desc h g → X g = Y g) : iterStep k n X h = iterStep k n Y h := by
  induction n generalizing h with
  | zero => exact hXY h (desc_refl h)
  | succ n ih =>
    rw [iterStep_succ', iterStep_succ']
    exact Finset.sum_congr rfl fun s _ => by
      rw [ih fun g hg => hXY g (desc_of_desc_next s hg)]

/-- `E_t X_{t+n}` depends only on the values of `X` at date `t + n` (O&R §8.7.1). -/
theorem iterStep_congr_depth (k : S → S → ℝ) (n : ℕ) {X Y : Hist S → ℝ} {h : Hist S}
    (hXY : ∀ g, depth g = depth h + n → X g = Y g) : iterStep k n X h = iterStep k n Y h := by
  induction n generalizing h with
  | zero => exact hXY h rfl
  | succ n ih =>
    rw [iterStep_succ', iterStep_succ']
    exact Finset.sum_congr rfl fun s _ => by
      rw [ih fun g hg => hXY g (by rw [hg, depth_next]; ring)]

namespace Household

variable {J : Type} [Fintype J]

/-- The asset menu faced by a household (O&R §8.7.1–8.7.2, pp. 579–581): for each asset `j`
its real price at a node, its real payoff at a node per unit bought at the parent node, and
its real liquidity services (money: price, payoff and services all `1/P`; nominal bond: price
`1/P_t`, payoff `(1+i_t)/P_{t+1}`; real bond: price `1`, payoff `1+r_t`; output claim: price
`q_t`, payoff `q_{t+1} + d_{t+1}`), plus the real endowment/transfer. -/
structure AssetMarket (S J : Type) [Fintype S] [Fintype J] where
  price : J → Hist S → ℝ
  payoff : J → Hist S → ℝ
  service : J → Hist S → ℝ
  endow : Hist S → ℝ

/-- Real liquidity services from holdings, the argument of `v` (O&R (91), p. 579:
`v(M/P)`). -/
def services (A : AssetMarket S J) (a : J → Hist S → ℝ) (g : Hist S) : ℝ :=
  ∑ j, A.service j g * a j g

/-- **The budget constraints** at the root (initial real wealth `W₀`) and at every later
node of the subtree (O&R §8.7.1, p. 580: "the budget constraint for a country n resident"):
`C + Σ_j p_j a_j = endowment + Σ_j R_j a_j(parent)`. -/
def Feasible (A : AssetMarket S J) (h₀ : Hist S) (W₀ : ℝ) (C : Hist S → ℝ)
    (a : J → Hist S → ℝ) : Prop :=
  (C h₀ + ∑ j, A.price j h₀ * a j h₀ = W₀) ∧
    ∀ g, Desc h₀ g → ∀ s, C (next g s) + ∑ j, A.price j (next g s) * a j (next g s)
      = A.endow (next g s) + ∑ j, A.payoff j (next g s) * a j g

/-- Consumption and real balances stay in the domain of `u` and `v` (O&R (91), p. 579). -/
def Positive (A : AssetMarket S J) (h₀ : Hist S) (C : Hist S → ℝ) (a : J → Hist S → ℝ) :
    Prop :=
  ∀ g, Desc h₀ g → 0 < C g ∧ 0 < services A a g

/-- The date-`t` term `βᵗ E₀[u(C_t) + v(m_t)]` of lifetime utility (O&R (91), p. 579). -/
def utilTerm (K : Kernel S) (β : ℝ) (u v : ℝ → ℝ) (A : AssetMarket S J) (h₀ : Hist S)
    (C : Hist S → ℝ) (a : J → Hist S → ℝ) (t : ℕ) : ℝ :=
  β ^ t * iterStep K.trans t (fun g => u (C g) + v (services A a g)) h₀

/-- **Lifetime expected utility** `E₀ Σ_t βᵗ [u(C_t) + v(M_t/P_t)]` over the whole
infinite event tree (O&R (91), p. 579). -/
noncomputable def lifetimeU (K : Kernel S) (β : ℝ) (u v : ℝ → ℝ) (A : AssetMarket S J)
    (h₀ : Hist S) (C : Hist S → ℝ) (a : J → Hist S → ℝ) : ℝ :=
  ∑' t, utilTerm K β u v A h₀ C a t

/-- **The Euler equations for every asset at every node** (O&R (93), (95), (96), (98),
pp. 580–581): `p_j u′(C) = s_j v′(m) + β E_t[u′(C_{t+1}) R_{j,t+1}]`. -/
def Euler (K : Kernel S) (β : ℝ) (u' v' : ℝ → ℝ) (A : AssetMarket S J) (h₀ : Hist S)
    (C : Hist S → ℝ) (a : J → Hist S → ℝ) : Prop :=
  ∀ g, Desc h₀ g → ∀ j, A.price j g * u' (C g)
    = A.service j g * v' (services A a g)
      + β * oneStep K.trans (fun g' => u' (C g') * A.payoff j g') g

/-- The marginal-utility value at date `T+1` of the portfolio `b` carried out of date `T`:
`β^{T+1} E₀[u′(C_{T+1}) Σ_j R_{j,T+1} b_{j,T}]` (O&R fn 31, p. 542, in the stochastic
model). -/
def contValue (K : Kernel S) (β : ℝ) (u' : ℝ → ℝ) (A : AssetMarket S J) (h₀ : Hist S)
    (C : Hist S → ℝ) (b : J → Hist S → ℝ) (T : ℕ) : ℝ :=
  β ^ (T + 1) * iterStep K.trans (T + 1)
    (fun g => u' (C g) * ∑ j, A.payoff j g * b j (anc g)) h₀

/-- **The no-Ponzi condition** for a rival portfolio, valued with the candidate's marginal
utilities: `liminf_T contValue ≥ 0` (O&R §8.7; fn 31, p. 542). -/
def NoPonzi (K : Kernel S) (β : ℝ) (u' : ℝ → ℝ) (A : AssetMarket S J) (h₀ : Hist S)
    (C : Hist S → ℝ) (b : J → Hist S → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop, -ε ≤ contValue K β u' A h₀ C b T

/-- **The stochastic transversality condition** for the candidate plan (O&R fn 31, p. 542,
in the stochastic model of §8.7). -/
def TVCHousehold (K : Kernel S) (β : ℝ) (u' : ℝ → ℝ) (A : AssetMarket S J) (h₀ : Hist S)
    (C : Hist S → ℝ) (a : J → Hist S → ℝ) : Prop :=
  Tendsto (contValue K β u' A h₀ C a) atTop (𝓝 0)

/-- Nonnegative financial wealth (no net debt) at every node implies the no-Ponzi
condition (O&R §8.7: a natural admissibility requirement). -/
theorem noPonzi_of_nonneg_wealth (K : Kernel S) {β : ℝ} (hβ : 0 ≤ β) {u' : ℝ → ℝ}
    (A : AssetMarket S J) (h₀ : Hist S) {C : Hist S → ℝ} {b : J → Hist S → ℝ}
    (hu' : ∀ g, Desc h₀ g → 0 ≤ u' (C g))
    (hw : ∀ g, Desc h₀ g → 0 ≤ ∑ j, A.payoff j g * b j (anc g)) :
    NoPonzi K β u' A h₀ C b := by
  intro ε hε
  refine Filter.Eventually.of_forall fun T => ?_
  have : 0 ≤ contValue K β u' A h₀ C b T := by
    unfold contValue
    have h0 := iterStep_mono_desc K.trans_nonneg (T + 1) (X := fun _ => (0 : ℝ))
      (Y := fun g => u' (C g) * ∑ j, A.payoff j g * b j (anc g)) (h := h₀)
      (fun g hg => mul_nonneg (hu' g hg) (hw g hg))
    rw [iterStep_const K.trans_sum] at h0
    exact mul_nonneg (pow_nonneg hβ _) h0
  linarith

/-- **Sufficiency: the Euler equations plus the transversality condition imply global
optimality over whole plans** (O&R §8.7.1–8.7.2, pp. 579–582; the stochastic version of
the supporting-hyperplane argument). If `(C, a)` is feasible, positive, satisfies the Euler
equations for every asset at every node and the transversality condition, then its lifetime
utility is at least that of EVERY feasible positive rival `(C′, a′)` satisfying the no-Ponzi
condition (both lifetime utilities summable). -/
theorem household_sufficiency (K : Kernel S) (A : AssetMarket S J) {β : ℝ} (hβ : 0 ≤ β)
    {u u' v v' : ℝ → ℝ} (hcu : ConcaveOn ℝ (Set.Ioi 0) u)
    (hdu : ∀ x, 0 < x → HasDerivAt u (u' x) x) (hcv : ConcaveOn ℝ (Set.Ioi 0) v)
    (hdv : ∀ x, 0 < x → HasDerivAt v (v' x) x) {h₀ : Hist S} {W₀ : ℝ}
    {C C' : Hist S → ℝ} {a a' : J → Hist S → ℝ}
    (hF : Feasible A h₀ W₀ C a) (hF' : Feasible A h₀ W₀ C' a')
    (hP : Positive A h₀ C a) (hP' : Positive A h₀ C' a')
    (hE : Euler K β u' v' A h₀ C a) (htvc : TVCHousehold K β u' A h₀ C a)
    (hnp : NoPonzi K β u' A h₀ C a')
    (hs : Summable (utilTerm K β u v A h₀ C a))
    (hs' : Summable (utilTerm K β u v A h₀ C' a')) :
    lifetimeU K β u v A h₀ C' a' ≤ lifetimeU K β u v A h₀ C a := by
  -- notation
  set x : J → Hist S → ℝ := fun j g => a' j g - a j g
  set dU : Hist S → ℝ := fun g =>
    (u (C' g) + v (services A a' g)) - (u (C g) + v (services A a g))
  set LI : Hist S → ℝ := fun g => u' (C g) * ∑ j, A.payoff j g * x j (anc g)
  set H : Hist S → ℝ := fun g =>
    ∑ j, x j g * (A.service j g * v' (services A a g) - A.price j g * u' (C g))
  -- the tangent inequality at a node
  have tang : ∀ g, Desc h₀ g → dU g ≤ u' (C g) * (C' g - C g)
      + v' (services A a g) * (services A a' g - services A a g) := fun g hg => by
    have t1 := concave_tangent hcu hdu (hP g hg).1 (hP' g hg).1
    have t2 := concave_tangent hcv hdv (hP g hg).2 (hP' g hg).2
    simp only [dU]; linarith
  have hserv : ∀ g, services A a' g - services A a g = ∑ j, A.service j g * x j g := fun g => by
    simp only [services, x, ← Finset.sum_sub_distrib, mul_sub]
  -- (P1) at the root
  have P1 : dU h₀ ≤ H h₀ := by
    have hb : C' h₀ - C h₀ = -∑ j, A.price j h₀ * x j h₀ := by
      simp only [x, mul_sub, Finset.sum_sub_distrib]; linarith [hF.1, hF'.1]
    have key : u' (C h₀) * (C' h₀ - C h₀)
        + v' (services A a h₀) * (services A a' h₀ - services A a h₀) = H h₀ := by
      rw [hb, hserv]
      simp only [H, Finset.mul_sum, ← Finset.sum_neg_distrib, mul_neg, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    linarith [tang h₀ (desc_refl h₀)]
  -- (P2) at a child of a descendant
  have P2 : ∀ g, Desc h₀ g → ∀ s, dU (next g s) ≤ LI (next g s) + H (next g s) := by
    intro g hg s
    have hg' := desc_next hg s
    have hb : C' (next g s) - C (next g s) = -∑ j, A.price j (next g s) * x j (next g s)
        + ∑ j, A.payoff j (next g s) * x j g := by
      simp only [x, mul_sub, Finset.sum_sub_distrib]
      linarith [hF.2 g hg s, hF'.2 g hg s]
    have key : u' (C (next g s)) * (C' (next g s) - C (next g s))
        + v' (services A a (next g s)) * (services A a' (next g s) - services A a (next g s))
        = LI (next g s) + H (next g s) := by
      rw [hb, hserv]
      simp only [LI, H, anc_next, mul_add, Finset.mul_sum, ← Finset.sum_neg_distrib, mul_neg,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    linarith [tang _ hg']
  -- (P3) the Euler equations turn `H` into a one-step-ahead expectation
  have P3 : ∀ g, Desc h₀ g → H g = -β * oneStep K.trans LI g := fun g hg => by
    have hEg := hE g hg
    have e : ∀ j, A.service j g * v' (services A a g) - A.price j g * u' (C g)
        = -β * oneStep K.trans (fun g' => u' (C g') * A.payoff j g') g := fun j => by
      rw [hEg j]; ring
    simp only [H, e, LI, oneStep, anc_next, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by ring
  -- the telescoping bound on partial sums
  have tele : ∀ T : ℕ, ∑ t ∈ Finset.range (T + 1), β ^ t * iterStep K.trans t dU h₀
      ≤ -(β ^ (T + 1) * iterStep K.trans (T + 1) LI h₀) := by
    intro T
    induction T with
    | zero =>
      simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, pow_one]
      have := P3 h₀ (desc_refl h₀)
      change dU h₀ ≤ -(β * oneStep K.trans LI h₀)
      linarith [P1]
    | succ T ih =>
      rw [Finset.sum_range_succ]
      have hstep : iterStep K.trans (T + 1) dU h₀
          ≤ iterStep K.trans (T + 1) LI h₀ - β * iterStep K.trans (T + 2) LI h₀ := by
        rw [iterStep_succ]
        have h1 : iterStep K.trans T (oneStep K.trans dU) h₀
            ≤ iterStep K.trans T (oneStep K.trans (fun g => LI g + H g)) h₀ :=
          iterStep_mono_desc K.trans_nonneg T fun g hg =>
            Finset.sum_le_sum fun s _ =>
              mul_le_mul_of_nonneg_left (P2 g hg s) (K.trans_nonneg _ _)
        have h2 : iterStep K.trans T (oneStep K.trans (fun g => LI g + H g)) h₀
            = iterStep K.trans (T + 1) LI h₀ + iterStep K.trans (T + 1) H h₀ := by
          rw [← iterStep_succ, iterStep_add_fun]
        have h3 : iterStep K.trans (T + 1) H h₀ = -β * iterStep K.trans (T + 2) LI h₀ := by
          rw [iterStep_congr_desc K.trans (T + 1)
            (Y := fun g => -β * oneStep K.trans LI g) fun g hg => P3 g hg,
            iterStep_mul_left, ← iterStep_succ]
        linarith
      have hβT : 0 ≤ β ^ (T + 1) := pow_nonneg hβ _
      have := mul_le_mul_of_nonneg_left hstep hβT
      calc ∑ t ∈ Finset.range (T + 1), β ^ t * iterStep K.trans t dU h₀
            + β ^ (T + 1) * iterStep K.trans (T + 1) dU h₀
          ≤ -(β ^ (T + 1) * iterStep K.trans (T + 1) LI h₀)
            + β ^ (T + 1) * (iterStep K.trans (T + 1) LI h₀
              - β * iterStep K.trans (T + 2) LI h₀) := add_le_add ih this
        _ = -(β ^ (T + 1 + 1) * iterStep K.trans (T + 1 + 1) LI h₀) := by ring
  -- the terminal term is the difference of continuation values
  have hLIc : ∀ T, β ^ (T + 1) * iterStep K.trans (T + 1) LI h₀
      = contValue K β u' A h₀ C a' T - contValue K β u' A h₀ C a T := fun T => by
    simp only [contValue, ← mul_sub]
    rw [← iterStep_sub_fun]
    congr 2; funext g
    simp only [LI, x, mul_sub, Finset.sum_sub_distrib]
  -- lifetime utility difference as a limit of partial sums
  have hdiff : ∀ t, utilTerm K β u v A h₀ C' a' t - utilTerm K β u v A h₀ C a t
      = β ^ t * iterStep K.trans t dU h₀ := fun t => by
    simp only [utilTerm, ← mul_sub, ← iterStep_sub_fun]
    rfl
  have hlim : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), β ^ t * iterStep K.trans t dU h₀)
      atTop (𝓝 (lifetimeU K β u v A h₀ C' a' - lifetimeU K β u v A h₀ C a)) := by
    have := ((hs'.sub hs).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    simp only [lifetimeU, ← (hs'.tsum_sub hs)]
    refine this.congr fun T => ?_
    simp only [Function.comp, hdiff]
  -- conclude
  by_contra hcon
  push Not at hcon
  set D := lifetimeU K β u v A h₀ C' a' - lifetimeU K β u v A h₀ C a with hD
  have hDpos : 0 < D := by simp only [hD]; linarith
  have e1 : ∀ᶠ T in atTop, D / 2 < ∑ t ∈ Finset.range (T + 1), β ^ t * iterStep K.trans t dU h₀ :=
    hlim.eventually (lt_mem_nhds (by linarith))
  have e2 : ∀ᶠ T in atTop, contValue K β u' A h₀ C a T < D / 4 :=
    htvc.eventually (gt_mem_nhds (by linarith))
  have e3 := hnp (D / 4) (by linarith)
  obtain ⟨T, h1, h2, h3⟩ := (e1.and (e2.and e3)).exists
  have := tele T
  rw [hLIc T] at this
  linarith

/-- **The transversality condition in holdings form** (O&R fn 31, p. 542): under the Euler
equations, `contValue_T(a) = βᵀ E₀[Σ_j a_{j,T} (p_j u′(C_T) − s_j v′(m_T))]`, the
marginal-utility value of the portfolio held at date `T`. -/
theorem contValue_eq_holdings (K : Kernel S) (A : AssetMarket S J) {β : ℝ} {u' v' : ℝ → ℝ}
    {h₀ : Hist S} {C : Hist S → ℝ} {a : J → Hist S → ℝ} (hE : Euler K β u' v' A h₀ C a)
    (T : ℕ) :
    contValue K β u' A h₀ C a T = β ^ T * iterStep K.trans T (fun g => ∑ j, a j g
      * (A.price j g * u' (C g) - A.service j g * v' (services A a g))) h₀ := by
  unfold contValue
  rw [iterStep_succ, pow_succ, mul_assoc, ← iterStep_mul_left]
  congr 1
  refine iterStep_congr_desc K.trans T fun g hg => ?_
  have e : ∀ j, A.price j g * u' (C g) - A.service j g * v' (services A a g)
      = β * oneStep K.trans (fun g' => u' (C g') * A.payoff j g') g := fun j => by
    rw [hE g hg j]; ring
  simp only [e, oneStep, anc_next, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by ring

omit [Fintype S] in
/-- A node whose parent is `g` but which is not `g` is one period later (O&R §8.7.1). -/
theorem depth_of_anc_eq {g g'' : Hist S} (ha : anc g'' = g) (hne : g'' ≠ g) :
    depth g'' = depth g + 1 := by
  obtain ⟨s, _ | ⟨t, past⟩⟩ := g''
  · exact absurd ha hne
  · subst ha; rfl

omit [Fintype S] in
/-- A node whose parent is `g` but which is not `g` is a child of `g` (O&R §8.7.1). -/
theorem eq_next_of_anc_eq {g g'' : Hist S} (ha : anc g'' = g) (hne : g'' ≠ g) :
    g'' = next g g''.1 := by
  obtain ⟨s, _ | ⟨t, past⟩⟩ := g''
  · exact absurd ha hne
  · subst ha; rfl

omit [Fintype S] in
/-- A child is never its parent (O&R §8.7.1). -/
theorem next_ne (g : Hist S) (s : S) : next g s ≠ g := fun h => by
  have := congrArg depth h
  rw [depth_next] at this
  omega

omit [Fintype S] in
/-- A non-root node is one period after its parent (O&R §8.7.1). -/
theorem depth_anc {g : Hist S} (hg : 1 ≤ depth g) : depth (anc g) + 1 = depth g := by
  obtain ⟨s, _ | ⟨t, past⟩⟩ := g
  · simp [depth] at hg
  · rfl

omit [Fintype S] in
/-- Descendants are weakly later (O&R §8.7.1). -/
theorem depth_le_of_desc {h g : Hist S} (hd : Desc h g) : depth h ≤ depth g := by
  obtain ⟨l, rfl⟩ := hd
  rw [depth_extend]; omega

variable [DecidableEq S] [DecidableEq J]

/-- The probability of reaching `g` from `h₀` (O&R §8.7.1). -/
def reachProb (K : Kernel S) (h₀ g : Hist S) : ℝ :=
  iterStep K.trans (depth g - depth h₀) (fun g'' => if g'' = g then 1 else 0) h₀

/-- The root is reached with probability one (O&R §8.7.1). -/
theorem reachProb_self (K : Kernel S) (h₀ : Hist S) : reachProb K h₀ h₀ = 1 := by
  simp [reachProb, iterStep]

/-- **Reach probabilities multiply along the tree** (O&R §8.7.1): the probability of the
child `next g s` is that of `g` times the transition probability. -/
theorem reachProb_next (K : Kernel S) {h₀ g : Hist S} (hg : Desc h₀ g) (s : S) :
    reachProb K h₀ (next g s) = reachProb K h₀ g * K.trans g.1 s := by
  have hd := depth_le_of_desc hg
  unfold reachProb
  rw [depth_next, show depth g + 1 - depth h₀ = (depth g - depth h₀) + 1 by omega,
    iterStep_succ]
  rw [iterStep_congr_depth K.trans _ (Y := fun g'' => K.trans g.1 s
    * (if g'' = g then 1 else 0)) fun g'' hg'' => ?_, iterStep_mul_left, mul_comm]
  simp only [oneStep]
  by_cases he : g'' = g
  · subst he
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      have : next g'' b ≠ next g'' s := fun h => hb (by simpa [next] using congrArg Prod.fst h)
      simp [this]
    · simp
  · simp only [he, ↓reduceIte, mul_zero]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : next g'' b ≠ next g s := fun h => he (by
      have := congrArg anc h; simpa [anc_next] using this)
    simp [this]

/-- The one-node perturbation of consumption: buy `δ` more units of asset `j` at node `g`,
paying from consumption at `g`, and consume the payoff at every child of `g`
(O&R (93), p. 580). -/
def perturbC (A : AssetMarket S J) (C : Hist S → ℝ) (g : Hist S) (j : J) (δ : ℝ) :
    Hist S → ℝ :=
  fun g'' => C g'' - (if g'' = g then A.price j g * δ else 0)
    + (if anc g'' = g ∧ g'' ≠ g then A.payoff j g'' * δ else 0)

/-- The one-node perturbation of the portfolio (O&R (93), p. 580). -/
def perturbA (a : J → Hist S → ℝ) (g : Hist S) (j : J) (δ : ℝ) : J → Hist S → ℝ :=
  fun j' g'' => a j' g'' + (if j' = j ∧ g'' = g then δ else 0)

/-- Liquidity services under the perturbation (O&R (98), p. 581). -/
theorem services_perturbA (A : AssetMarket S J) (a : J → Hist S → ℝ) (g : Hist S) (j : J)
    (δ : ℝ) (g'' : Hist S) :
    services A (perturbA a g j δ) g''
      = services A a g'' + (if g'' = g then A.service j g * δ else 0) := by
  by_cases hg : g'' = g
  · subst hg
    simp [services, perturbA, mul_add, Finset.sum_add_distrib]
  · simp [services, perturbA, hg]

/-- **The perturbed plan satisfies the budget constraints** (O&R (93), p. 580). -/
theorem feasible_perturb (A : AssetMarket S J) {h₀ : Hist S} {W₀ : ℝ} {C : Hist S → ℝ}
    {a : J → Hist S → ℝ} (hF : Feasible A h₀ W₀ C a) {g : Hist S} (hg : Desc h₀ g) (j : J)
    (δ : ℝ) : Feasible A h₀ W₀ (perturbC A C g j δ) (perturbA a g j δ) := by
  constructor
  · by_cases hr : h₀ = g
    · subst hr
      have := hF.1
      simp [perturbC, perturbA, mul_add, Finset.sum_add_distrib] at this ⊢
      linarith
    · have hnot : ¬ (anc h₀ = g ∧ h₀ ≠ g) := fun ⟨ha, hne⟩ => by
        have := depth_of_anc_eq ha hne
        have := depth_le_of_desc hg
        omega
      simp only [perturbC, perturbA, hr, hnot, and_false, ↓reduceIte, add_zero, sub_zero]
      exact hF.1
  · intro g'' hg'' s
    have hb := hF.2 g'' hg'' s
    have hn : g'' ≠ next g'' s := (next_ne g'' s).symm
    by_cases h1 : next g'' s = g
    · subst h1
      simp [perturbC, perturbA, hn, anc_next, mul_add, Finset.sum_add_distrib] at hb ⊢
      linarith
    · by_cases h2 : g'' = g
      · subst h2
        simp [perturbC, perturbA, h1, anc_next, mul_add, Finset.sum_add_distrib] at hb ⊢
        linarith
      · simp [perturbC, perturbA, h1, h2, anc_next] at hb ⊢
        linarith

/-- The one-period value of the perturbation at `g` (O&R (93), (98), pp. 580–581). -/
def localValue (K : Kernel S) (β : ℝ) (u v : ℝ → ℝ) (A : AssetMarket S J)
    (C : Hist S → ℝ) (a : J → Hist S → ℝ) (g : Hist S) (j : J) (δ : ℝ) : ℝ :=
  u (C g - A.price j g * δ) + v (services A a g + A.service j g * δ)
    + β * ∑ s, K.trans g.1 s * u (C (next g s) + A.payoff j (next g s) * δ)

/-- **The lifetime-utility effect of a one-node perturbation**
`U(δ) − U(0) = β^d ρ(g) [φ(δ) − φ(0)]`, with `d` the date and `ρ(g)` the reach probability of
the node (O&R (93), p. 580). -/
theorem lifetimeU_perturb (K : Kernel S) (A : AssetMarket S J) (β : ℝ) (u v : ℝ → ℝ)
    {h₀ : Hist S} {C : Hist S → ℝ} {a : J → Hist S → ℝ} {g : Hist S} (hg : Desc h₀ g) (j : J)
    (δ : ℝ) (hs : Summable (utilTerm K β u v A h₀ C a)) :
    Summable (utilTerm K β u v A h₀ (perturbC A C g j δ) (perturbA a g j δ)) ∧
      lifetimeU K β u v A h₀ (perturbC A C g j δ) (perturbA a g j δ)
        - lifetimeU K β u v A h₀ C a
      = β ^ (depth g - depth h₀) * reachProb K h₀ g
        * (localValue K β u v A C a g j δ - localValue K β u v A C a g j 0) := by
  set d := depth g - depth h₀
  have hdg : depth g = depth h₀ + d := by have := depth_le_of_desc hg; omega
  set dU : Hist S → ℝ := fun g'' =>
    (u (perturbC A C g j δ g'') + v (services A (perturbA a g j δ) g''))
      - (u (C g'') + v (services A a g''))
  have hzero : ∀ g'', g'' ≠ g → ¬ (anc g'' = g ∧ g'' ≠ g) → dU g'' = 0 := fun g'' h1 h2 => by
    simp only [dU, perturbC, services_perturbA, h1, h2, ↓reduceIte, sub_zero, add_zero]
    ring
  have hterm : utilTerm K β u v A h₀ (perturbC A C g j δ) (perturbA a g j δ)
      = fun t => utilTerm K β u v A h₀ C a t + β ^ t * iterStep K.trans t dU h₀ := by
    funext t
    simp only [utilTerm, ← mul_add, ← iterStep_add_fun]
    congr 2; funext g''; simp only [dU]; ring
  have hat_d : iterStep K.trans d dU h₀ = reachProb K h₀ g * dU g := by
    rw [iterStep_congr_depth K.trans d (Y := fun g'' => dU g * (if g'' = g then 1 else 0))
      (fun g'' hg'' => by
        by_cases he : g'' = g
        · subst he; simp
        · simp only [he, ↓reduceIte, mul_zero]
          refine hzero g'' he fun ⟨ha, hne⟩ => ?_
          have := depth_of_anc_eq ha hne
          omega), iterStep_mul_left, mul_comm]
    rfl
  have hat_d1 : iterStep K.trans (d + 1) dU h₀ = reachProb K h₀ g * oneStep K.trans dU g := by
    rw [iterStep_succ, iterStep_congr_depth K.trans d
      (Y := fun g'' => oneStep K.trans dU g * (if g'' = g then 1 else 0))
      (fun g'' hg'' => by
        by_cases he : g'' = g
        · subst he; simp
        · simp only [he, ↓reduceIte, mul_zero]
          refine Finset.sum_eq_zero fun b _ => ?_
          have h1 : next g'' b ≠ g := fun h => by
            have := congrArg depth h; rw [depth_next] at this; omega
          have h2 : ¬ (anc (next g'' b) = g ∧ next g'' b ≠ g) := fun ⟨ha, _⟩ =>
            he (by rwa [anc_next] at ha)
          rw [hzero _ h1 h2, mul_zero]), iterStep_mul_left, mul_comm]
    rfl
  have hat_o : ∀ t, t ≠ d → t ≠ d + 1 → iterStep K.trans t dU h₀ = 0 := fun t ht ht1 => by
    rw [iterStep_congr_depth K.trans t (Y := fun _ => 0) (fun g'' hg'' => by
      refine hzero g'' (fun h => ht (by subst h; omega)) fun ⟨ha, hne⟩ => ?_
      have := depth_of_anc_eq ha hne
      exact ht1 (by omega)), iterStep_const K.trans_sum]
  have hsupp : ∀ t ∉ ({d, d + 1} : Finset ℕ), β ^ t * iterStep K.trans t dU h₀ = 0 := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    rw [hat_o t ht.1 ht.2, mul_zero]
  have hsum2 : Summable fun t => β ^ t * iterStep K.trans t dU h₀ :=
    summable_of_ne_finset_zero hsupp
  refine ⟨?_, ?_⟩
  · rw [hterm]; exact hs.add hsum2
  · unfold lifetimeU
    rw [hterm, hs.tsum_add hsum2, add_sub_cancel_left, tsum_eq_sum hsupp,
      Finset.sum_pair (by omega : d ≠ d + 1), hat_d, hat_d1]
    have hg1 : dU g = u (C g - A.price j g * δ) + v (services A a g + A.service j g * δ)
        - (u (C g) + v (services A a g)) := by
      have : ¬ (anc g = g ∧ g ≠ g) := fun ⟨_, h⟩ => h rfl
      simp only [dU, perturbC, services_perturbA, this, ↓reduceIte, add_zero]
    have hg2 : oneStep K.trans dU g = ∑ s, K.trans g.1 s
        * u (C (next g s) + A.payoff j (next g s) * δ)
        - ∑ s, K.trans g.1 s * u (C (next g s)) := by
      simp only [oneStep, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      have h1 : next g s ≠ g := next_ne g s
      have h2 : anc (next g s) = g ∧ next g s ≠ g := ⟨anc_next g s, h1⟩
      simp only [dU, perturbC, services_perturbA, h1, ↓reduceIte, sub_zero, add_zero]
      rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
      ring
    rw [hg1, hg2]
    simp only [localValue, mul_zero, sub_zero, add_zero]
    rw [pow_succ]
    ring

omit [DecidableEq J] in
/-- **Necessity of the Euler equations** (O&R (93), (95), (96), (98), pp. 580–581): if a
feasible, positive plan satisfying the transversality condition is optimal against every
admissible rival (feasible, positive, no-Ponzi, summable utility), then the Euler equation
holds for every asset at every node reached with positive probability. -/
theorem household_euler_necessary (K : Kernel S) (A : AssetMarket S J) {β : ℝ} (hβ : 0 < β)
    {u u' v v' : ℝ → ℝ} (hdu : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    (hdv : ∀ x, 0 < x → HasDerivAt v (v' x) x) {h₀ : Hist S} {W₀ : ℝ} {C : Hist S → ℝ}
    {a : J → Hist S → ℝ} (hF : Feasible A h₀ W₀ C a) (hP : Positive A h₀ C a)
    (htvc : TVCHousehold K β u' A h₀ C a) (hs : Summable (utilTerm K β u v A h₀ C a))
    (hopt : ∀ C' a', Feasible A h₀ W₀ C' a' → Positive A h₀ C' a' →
      NoPonzi K β u' A h₀ C a' → Summable (utilTerm K β u v A h₀ C' a') →
      lifetimeU K β u v A h₀ C' a' ≤ lifetimeU K β u v A h₀ C a)
    {g : Hist S} (hg : Desc h₀ g) (hρ : 0 < reachProb K h₀ g) (j : J) :
    A.price j g * u' (C g) = A.service j g * v' (services A a g)
      + β * oneStep K.trans (fun g' => u' (C g') * A.payoff j g') g := by
  classical
  set d := depth g - depth h₀
  have hdg : depth g = depth h₀ + d := by have := depth_le_of_desc hg; omega
  -- positivity of the perturbed plan near `δ = 0`
  have ev1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C g - A.price j g * δ := by
    have hc : Continuous fun δ : ℝ => C g - A.price j g * δ := by fun_prop
    exact continuousAt_const.eventually_lt hc.continuousAt (by simpa using (hP g hg).1)
  have ev2 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < services A a g + A.service j g * δ := by
    have hc : Continuous fun δ : ℝ => services A a g + A.service j g * δ := by fun_prop
    exact continuousAt_const.eventually_lt hc.continuousAt (by simpa using (hP g hg).2)
  have ev3 : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ s, 0 < C (next g s) + A.payoff j (next g s) * δ := by
    refine Filter.eventually_all.2 fun s => ?_
    have hc : Continuous fun δ : ℝ => C (next g s) + A.payoff j (next g s) * δ := by fun_prop
    exact continuousAt_const.eventually_lt hc.continuousAt
      (by simpa using (hP _ (desc_next hg s)).1)
  have hloc : IsLocalMax (localValue K β u v A C a g j) 0 := by
    filter_upwards [ev1, ev2, ev3] with δ h1 h2 h3
    have hPos : Positive A h₀ (perturbC A C g j δ) (perturbA a g j δ) := by
      intro g'' hg''
      rw [services_perturbA]
      by_cases he : g'' = g
      · subst he
        have : ¬ (anc g'' = g'' ∧ g'' ≠ g'') := fun ⟨_, h⟩ => h rfl
        simp only [perturbC, this, ↓reduceIte, add_zero]
        exact ⟨h1, h2⟩
      · simp only [he, ↓reduceIte, add_zero]
        refine ⟨?_, (hP g'' hg'').2⟩
        by_cases hc : anc g'' = g ∧ g'' ≠ g
        · have hval : perturbC A C g j δ g'' = C g'' + A.payoff j g'' * δ := by
            simp only [perturbC, he, ↓reduceIte, sub_zero]
            rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
          have := eq_next_of_anc_eq hc.1 hc.2
          rw [hval, this]; exact h3 _
        · simp only [perturbC, he, hc, ↓reduceIte, sub_zero, add_zero]
          exact (hP g'' hg'').1
    have hNP : NoPonzi K β u' A h₀ C (perturbA a g j δ) := by
      intro ε hε
      have hev := htvc.eventually (lt_mem_nhds (show -ε < 0 by linarith))
      filter_upwards [hev, Filter.eventually_gt_atTop d] with T hT hTd
      have heq : contValue K β u' A h₀ C (perturbA a g j δ) T = contValue K β u' A h₀ C a T := by
        unfold contValue
        congr 1
        refine iterStep_congr_depth K.trans _ fun g'' hg'' => ?_
        have hne : anc g'' ≠ g := fun h => by
          have h1 := depth_anc (g := g'') (by omega)
          rw [h] at h1; omega
        simp only [perturbA, hne, and_false, ↓reduceIte, add_zero]
      rw [heq]; exact hT.le
    have hper := lifetimeU_perturb K A β u v hg j δ hs
    have := hopt _ _ (feasible_perturb A hF hg j δ) hPos hNP hper.1
    have hpos : 0 < β ^ d * reachProb K h₀ g := mul_pos (pow_pos hβ _) hρ
    have h4 : β ^ d * reachProb K h₀ g * (localValue K β u v A C a g j δ
        - localValue K β u v A C a g j 0) ≤ 0 := by rw [← hper.2]; linarith
    have := (mul_nonpos_iff_pos_imp_nonpos.1 h4).1 hpos
    linarith
  -- the derivative of the local value
  have hderiv : HasDerivAt (localValue K β u v A C a g j)
      (-(A.price j g * u' (C g)) + A.service j g * v' (services A a g)
        + β * ∑ s, K.trans g.1 s * (u' (C (next g s)) * A.payoff j (next g s))) 0 := by
    have hc1 : HasDerivAt (fun δ : ℝ => C g - A.price j g * δ) (-A.price j g) 0 := by
      simpa using HasDerivAt.const_sub (C g) (HasDerivAt.const_mul (A.price j g)
        (hasDerivAt_id' (0 : ℝ)))
    have hc2 : HasDerivAt (fun δ : ℝ => services A a g + A.service j g * δ)
        (A.service j g) 0 := by
      simpa using HasDerivAt.const_add (services A a g) (HasDerivAt.const_mul (A.service j g)
        (hasDerivAt_id' (0 : ℝ)))
    have d1 := HasDerivAt.comp_of_eq 0 (hdu (C g) (hP g hg).1) hc1 (by simp)
    have d2 := HasDerivAt.comp_of_eq 0 (hdv _ (hP g hg).2) hc2 (by simp)
    have d3 : HasDerivAt (fun δ => ∑ s, K.trans g.1 s * u (C (next g s)
        + A.payoff j (next g s) * δ))
        (∑ s, K.trans g.1 s * (u' (C (next g s)) * A.payoff j (next g s))) 0 := by
      apply HasDerivAt.fun_sum
      intro s _
      have hcs : HasDerivAt (fun δ : ℝ => C (next g s) + A.payoff j (next g s) * δ)
          (A.payoff j (next g s)) 0 := by
        simpa using HasDerivAt.const_add (C (next g s))
          (HasDerivAt.const_mul (A.payoff j (next g s)) (hasDerivAt_id' (0 : ℝ)))
      exact HasDerivAt.const_mul _ (HasDerivAt.comp_of_eq 0
        (hdu _ (hP _ (desc_next hg s)).1) hcs (by simp))
    have := HasDerivAt.add (HasDerivAt.add d1 d2) (HasDerivAt.const_mul β d3)
    exact HasDerivAt.congr_deriv this (by ring)
  have h0 := hloc.hasDerivAt_eq_zero hderiv
  simp only [oneStep]
  linarith

end Household


/-! ## The §8.7 equilibrium plan is optimal for each household -/

namespace Equilibrium87

/-- **CRRA utility is concave**: `u′(C) = C^{−ρ}` with `ρ > 0` (O&R §8.7.3, p. 582). -/
theorem crra_concave {u : ℝ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hdu : ∀ z, 0 < z → HasDerivAt u (z ^ (-ρ)) z) : ConcaveOn ℝ (Set.Ioi 0) u := by
  have hd : ∀ z ∈ Set.Ioi (0 : ℝ), deriv u z = z ^ (-ρ) := fun z hz => (hdu z hz).deriv
  refine AntitoneOn.concaveOn_of_deriv (convex_Ioi 0) ?_ ?_ ?_
  · exact fun z hz => (hdu z hz).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; exact fun z hz => (hdu z hz).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro a ha b hb hab
    rw [hd a ha, hd b hb]
    exact Real.rpow_le_rpow_of_nonpos ha hab (by linarith)

variable {S : Type} [Fintype S]

/-- Equilibrium consumption `C = x Y^W` (O&R (94), p. 580). -/
def cons (x : ℝ) (y : S → ℝ) (h : Hist S) : ℝ := x * y h.1

/-- Marginal utility `u′(C) = (xY^W)^{−ρ}` (O&R §8.7.3). -/
noncomputable def lam (ρ x : ℝ) (y : S → ℝ) (h : Hist S) : ℝ := (x * y h.1) ^ (-ρ)

/-- The equilibrium price level `P = M(1 − β/(1+μ))(xY^W)^{−ρ}` (O&R p. 583). -/
noncomputable def price (β μ ρ x : ℝ) (y : S → ℝ) (M : Hist S → ℝ) (h : Hist S) : ℝ :=
  M h * (1 - β / (1 + μ)) * (x * y h.1) ^ (-ρ)

/-- The gross real interest rate that clears the real-bond market (O&R (96), p. 581):
`1 + r_t = u′(C_t)/(β E_t u′(C_{t+1}))`. -/
noncomputable def realRate (K : Kernel S) (β ρ x : ℝ) (y : S → ℝ) (g : Hist S) : ℝ :=
  lam ρ x y g / (β * oneStep K.trans (lam ρ x y) g)

/-- The dividend of the world output fund in marginal-utility units `u′(C) Y^W`
(O&R fn 64, p. 580). -/
noncomputable def divU (ρ x : ℝ) (y : S → ℝ) (h : Hist S) : ℝ := lam ρ x y h * y h.1

/-- The marginal-utility value of the output fund
`Σ_{n≥1} βⁿ E_t[u′(C_{t+n}) Y^W_{t+n}]` (O&R fn 64, p. 580). -/
noncomputable def fundU (K : Kernel S) (β ρ x : ℝ) (y : S → ℝ) (g : Hist S) : ℝ :=
  ∑' n : ℕ, β ^ (n + 1) * iterStep K.trans (n + 1) (divU ρ x y) g

/-- The output-fund price `q = fundU/u′(C)` (O&R fn 64, p. 580). -/
noncomputable def fundPrice (K : Kernel S) (β ρ x : ℝ) (y : S → ℝ) (g : Hist S) : ℝ :=
  fundU K β ρ x y g / lam ρ x y g

/-- **The §8.7 asset menu**: money (price, payoff and services `1/P`), the nominal bond
(`1 + i = (1+μ)/β`), the real bond (gross return `1 + r` set at the parent node) and the
world output fund (price `q`, payoff `q + Y^W`); endowment = the money transfer
`(M_t − M_{t−1})/P_t` (O&R §8.7.1–8.7.3, pp. 579–583). -/
noncomputable def market (K : Kernel S) (β μ ρ x : ℝ) (y : S → ℝ) (M : Hist S → ℝ) :
    Household.AssetMarket S (Fin 4) :=
  ⟨fun j h => ![1 / price β μ ρ x y M h, 1 / price β μ ρ x y M h, 1,
      fundPrice K β ρ x y h] j,
    fun j h => ![1 / price β μ ρ x y M h, ((1 + μ) / β) / price β μ ρ x y M h,
      realRate K β ρ x y (anc h), fundPrice K β ρ x y h + y h.1] j,
    fun j h => ![1 / price β μ ρ x y M h, 0, 0, 0] j,
    fun h => (M h - M (anc h)) / price β μ ρ x y M h⟩

/-- The equilibrium portfolio: the money stock, no bonds, and the constant share `x` of the
world output fund (O&R (94), p. 580). -/
def holdings (M : Hist S → ℝ) (x : ℝ) : Fin 4 → Hist S → ℝ := fun j h => ![M h, 0, 0, x] j

/-- The household's initial real wealth (O&R §8.7.1). -/
noncomputable def wealth0 (K : Kernel S) (β μ ρ x : ℝ) (y : S → ℝ) (M : Hist S → ℝ)
    (h₀ : Hist S) : ℝ :=
  cons x y h₀ + M h₀ / price β μ ρ x y M h₀ + fundPrice K β ρ x y h₀ * x

namespace Lemmas

variable {K : Kernel S} {y ε : S → ℝ} {β μ ρ x : ℝ} {M : Hist S → ℝ}

omit [Fintype S] in
/-- `u′(C)/P = 1/(M(1 − β/(1+μ)))` (O&R p. 583). -/
theorem lam_div_price (hy : ∀ s, 0 < y s) (hx : 0 < x) (h : Hist S) :
    lam ρ x y h * (1 / price β μ ρ x y M h) = 1 / (M h * (1 - β / (1 + μ))) := by
  have : 0 < (x * y h.1) ^ (-ρ) := Real.rpow_pos_of_pos (mul_pos hx (hy _)) _
  simp only [lam, price]
  field_simp

/-- `E_t[u′(C_{t+1})/P_{t+1}] = 1/(M_t(1+μ)(1 − β/(1+μ)))` (O&R (99)–(100), p. 583). -/
theorem oneStep_lam_div_price (hy : ∀ s, 0 < y s) (hx : 0 < x) (hε : ∀ s, 0 < ε s)
    (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) (hM : ∀ h, 0 < M h)
    (hμ : 0 < 1 + μ) (hγ : β / (1 + μ) < 1)
    (hgrowth : ∀ h s', M (next h s') = M h * (1 + μ) * ε s') (g : Hist S) :
    oneStep K.trans (fun g' => lam ρ x y g' * (1 / price β μ ρ x y M g')) g
      = 1 / (M g * (1 + μ) * (1 - β / (1 + μ))) := by
  have h1 : 0 < 1 - β / (1 + μ) := by linarith
  simp only [oneStep, lam_div_price hy hx, hgrowth]
  have e : ∀ s', K.trans g.1 s' * (1 / (M g * (1 + μ) * ε s' * (1 - β / (1 + μ))))
      = 1 / (M g * (1 + μ) * (1 - β / (1 + μ))) * (K.trans g.1 s' * (1 / ε s')) := fun s' => by
    have := hM g; have := hε s'
    field_simp
  simp only [e, ← Finset.mul_sum]
  have := hE g.1
  simp only [FinProb.expect, Kernel.row] at this
  rw [this, mul_one]

/-- The dividend in marginal-utility units is bounded (finite state space)
(O&R fn 64, p. 580). -/
theorem divU_bound (hy : ∀ s, 0 < y s) (hx : 0 < x) (h : Hist S) :
    0 ≤ divU ρ x y h ∧ divU ρ x y h ≤ ∑ s, (x * y s) ^ (-ρ) * y s := by
  have hpos : ∀ s, 0 ≤ (x * y s) ^ (-ρ) * y s := fun s =>
    mul_nonneg (Real.rpow_pos_of_pos (mul_pos hx (hy s)) _).le (hy s).le
  exact ⟨hpos h.1, Finset.single_le_sum (f := fun s => (x * y s) ^ (-ρ) * y s)
    (fun s _ => hpos s) (Finset.mem_univ _)⟩

/-- The terms of the fund value are summable and bounded (O&R fn 64, p. 580). -/
theorem fundU_terms (hy : ∀ s, 0 < y s) (hx : 0 < x) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (g : Hist S) :
    Summable (fun n : ℕ => β ^ (n + 1) * iterStep K.trans (n + 1) (divU ρ x y) g) ∧
      0 ≤ fundU K β ρ x y g ∧
      fundU K β ρ x y g ≤ (∑ s, (x * y s) ^ (-ρ) * y s) * (β / (1 - β)) := by
  set B := ∑ s, (x * y s) ^ (-ρ) * y s
  have hb : ∀ n, 0 ≤ iterStep K.trans n (divU ρ x y) g ∧ iterStep K.trans n (divU ρ x y) g ≤ B :=
    fun n => ⟨iterStep_nonneg K.trans_nonneg n (fun h => (divU_bound hy hx h).1) g, by
      have := iterStep_mono K.trans_nonneg n (X := divU ρ x y) (Y := fun _ => B)
        (fun h => (divU_bound hy hx h).2) g
      rwa [iterStep_const K.trans_sum] at this⟩
  have hgeo : Summable (fun n : ℕ => B * β * β ^ n) :=
    (summable_geometric_of_lt_one hβ0 hβ1).mul_left _
  have hle : ∀ n : ℕ, β ^ (n + 1) * iterStep K.trans (n + 1) (divU ρ x y) g ≤ B * β * β ^ n :=
    fun n => by
      rw [pow_succ]
      have := mul_le_mul_of_nonneg_left (hb (n + 1)).2 (pow_nonneg hβ0 n)
      nlinarith [pow_nonneg hβ0 n]
  have hnn : ∀ n : ℕ, 0 ≤ β ^ (n + 1) * iterStep K.trans (n + 1) (divU ρ x y) g :=
    fun n => mul_nonneg (pow_nonneg hβ0 _) (hb (n + 1)).1
  have hsum := Summable.of_nonneg_of_le hnn hle hgeo
  refine ⟨hsum, tsum_nonneg hnn, ?_⟩
  calc fundU K β ρ x y g ≤ ∑' n : ℕ, B * β * β ^ n := hsum.tsum_le_tsum hle hgeo
    _ = B * (β / (1 - β)) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1]; field_simp

/-- **The fund-pricing recursion** `fundU_t = β E_t[fundU_{t+1} + u′(C_{t+1})Y^W_{t+1}]`
(O&R (93) for the output fund, p. 580). -/
theorem fundU_recursion (hy : ∀ s, 0 < y s) (hx : 0 < x) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (g : Hist S) :
    fundU K β ρ x y g = β * oneStep K.trans (fun g' => fundU K β ρ x y g' + divU ρ x y g') g := by
  have hs := fun g' => (fundU_terms (K := K) (ρ := ρ) hy hx hβ0 hβ1 g').1
  have h1 : oneStep K.trans (fundU K β ρ x y) g
      = ∑' n : ℕ, β ^ (n + 1) * iterStep K.trans (n + 1 + 1) (divU ρ x y) g := by
    rw [show fundU K β ρ x y = fun g' => ∑' n : ℕ, β ^ (n + 1)
      * iterStep K.trans (n + 1) (divU ρ x y) g' from rfl, oneStep_tsum K.trans hs]
    congr 1; funext n; rw [oneStep_mul_left, ← iterStep_succ']
  have h2 : fundU K β ρ x y g = β * oneStep K.trans (divU ρ x y) g
      + ∑' n : ℕ, β ^ (n + 1 + 1) * iterStep K.trans (n + 1 + 1) (divU ρ x y) g := by
    rw [fundU, (hs g).tsum_eq_zero_add]
    simp only [zero_add, pow_one]
    rfl
  rw [oneStep_add, h1, h2, mul_add, ← tsum_mul_left, add_comm]
  congr 1
  congr 1; funext n; ring

end Lemmas

open Lemmas

variable {K : Kernel S} {y ε : S → ℝ} {β μ ρ x : ℝ} {M : Hist S → ℝ}

/-- **The equilibrium plan satisfies all four Euler equations** (O&R (93), (95), (96),
(98), pp. 580–583) with `u′(C) = C^{−ρ}` and `v = log`. -/
theorem euler_holds (hy : ∀ s, 0 < y s) (hx : 0 < x) (hε : ∀ s, 0 < ε s)
    (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) (hM : ∀ h, 0 < M h)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hβμ : β < 1 + μ)
    (hgrowth : ∀ h s', M (next h s') = M h * (1 + μ) * ε s') (h₀ : Hist S) :
    Household.Euler K β (fun z => z ^ (-ρ)) (fun z => z⁻¹) (market K β μ ρ x y M) h₀
      (cons x y) (holdings M x) := by
  intro g _ j
  have hμ : 0 < 1 + μ := by linarith
  have hγ : β / (1 + μ) < 1 := (div_lt_one hμ).2 hβμ
  have h1γ : 0 < 1 - β / (1 + μ) := by linarith
  have hMg := hM g
  have hlamg : 0 < lam ρ x y g := Real.rpow_pos_of_pos (mul_pos hx (hy _)) _
  have hPg : 0 < price β μ ρ x y M g :=
    mul_pos (mul_pos hMg h1γ) (Real.rpow_pos_of_pos (mul_pos hx (hy _)) _)
  have hserv : Household.services (market K β μ ρ x y M) (holdings M x) g
      = M g / price β μ ρ x y M g := by
    simp [Household.services, market, holdings, Fin.sum_univ_four]; ring
  have hcons : ∀ h, (cons x y h) ^ (-ρ) = lam ρ x y h := fun h => rfl
  have hos := oneStep_lam_div_price (K := K) (ρ := ρ) hy hx hε hE hM hμ hγ hgrowth g
  fin_cases j
  · -- money (98)
    rw [hserv]
    simp only [market, Fin.zero_eta, Matrix.cons_val_zero, hcons]
    rw [hos]
    have e1 : 1 / price β μ ρ x y M g * lam ρ x y g = 1 / (M g * (1 - β / (1 + μ))) := by
      rw [mul_comm]; exact lam_div_price hy hx g
    have e2 : 1 / price β μ ρ x y M g * (M g / price β μ ρ x y M g)⁻¹ = 1 / M g := by
      field_simp
    rw [e1, e2]
    have : 1 + μ - β ≠ 0 := by linarith
    field_simp
    ring
  · -- nominal bond (95)
    simp only [market, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, hcons,
      zero_mul, zero_add]
    have e : (fun g' => lam ρ x y g' * ((1 + μ) / β / price β μ ρ x y M g'))
        = fun g' => (1 + μ) / β * (lam ρ x y g' * (1 / price β μ ρ x y M g')) := by
      funext g'; ring
    rw [e, oneStep_mul_left, hos, mul_comm, lam_div_price hy hx]
    field_simp
  · -- real bond (96)
    simp only [market, Fin.reduceFinMk, Matrix.cons_val, hcons, zero_mul, zero_add,
      one_mul]
    have hpos : 0 < oneStep K.trans (lam ρ x y) g :=
      Finset.sum_pos' (fun s _ => mul_nonneg (K.trans_nonneg _ _)
        (Real.rpow_pos_of_pos (mul_pos hx (hy _)) _).le) (by
          obtain ⟨s, hs⟩ := (K.row g.1).exists_prob_pos
          exact ⟨s, Finset.mem_univ _,
            mul_pos hs (Real.rpow_pos_of_pos (mul_pos hx (hy _)) _)⟩)
    have e : (fun g' => lam ρ x y g' * realRate K β ρ x y (anc g'))
        = fun g' => realRate K β ρ x y (anc g') * lam ρ x y g' := by funext g'; ring
    rw [e, oneStep_pull, realRate]
    field_simp
  · -- output fund (93)
    simp only [market, Fin.reduceFinMk, Matrix.cons_val, hcons, zero_mul, zero_add]
    have e : (fun g' => lam ρ x y g' * (fundPrice K β ρ x y g' + y g'.1))
        = fun g' => fundU K β ρ x y g' + divU ρ x y g' := by
      funext g'
      have : 0 < lam ρ x y g' := Real.rpow_pos_of_pos (mul_pos hx (hy _)) _
      simp only [fundPrice, divU]; field_simp
    rw [e, ← fundU_recursion hy hx hβ0.le hβ1, fundPrice]
    field_simp

/-- **The equilibrium plan is feasible** (O&R §8.7.1): the budget constraint holds at the
root and at every node, with the money transfer as endowment. -/
theorem feasible (h₀ : Hist S) :
    Household.Feasible (market K β μ ρ x y M) h₀ (wealth0 K β μ ρ x y M h₀) (cons x y)
      (holdings M x) := by
  constructor
  · simp [market, holdings, wealth0, Fin.sum_univ_four]; ring
  · intro g _ s
    simp [market, holdings, Fin.sum_univ_four, anc_next, cons]
    ring

/-- **The equilibrium plan is positive** (O&R §8.7.1). -/
theorem positive (hy : ∀ s, 0 < y s) (hx : 0 < x) (hM : ∀ h, 0 < M h) (hβ0 : 0 < β)
    (hβμ : β < 1 + μ) (h₀ : Hist S) :
    Household.Positive (market K β μ ρ x y M) h₀ (cons x y) (holdings M x) := by
  intro g _
  have hμ : 0 < 1 + μ := by linarith
  have h1γ : 0 < 1 - β / (1 + μ) := by have := (div_lt_one hμ).2 hβμ; linarith
  have hPg : 0 < price β μ ρ x y M g :=
    mul_pos (mul_pos (hM g) h1γ) (Real.rpow_pos_of_pos (mul_pos hx (hy _)) _)
  refine ⟨mul_pos hx (hy _), ?_⟩
  simp only [Household.services, market, holdings, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, zero_mul, add_zero]
  exact mul_pos (one_div_pos.2 hPg) (hM g)

/-- **The transversality condition holds for the equilibrium plan** (O&R fn 31, p. 542):
derived from primitives: money contributes a bounded term (`u′(C)M/P = ω`), the output fund
the tail of a convergent series. -/
theorem tvc (hy : ∀ s, 0 < y s) (hx : 0 < x) (hε : ∀ s, 0 < ε s) (hM : ∀ h, 0 < M h)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hβμ : β < 1 + μ)
    (hgrowth : ∀ h s', M (next h s') = M h * (1 + μ) * ε s') (h₀ : Hist S) :
    Household.TVCHousehold K β (fun z => z ^ (-ρ)) (market K β μ ρ x y M) h₀ (cons x y)
      (holdings M x) := by
  have hμ : 0 < 1 + μ := by linarith
  have h1γ : 0 < 1 - β / (1 + μ) := by have := (div_lt_one hμ).2 hβμ; linarith
  set Bz := ∑ s, (x * y s) ^ (-ρ) * y s
  set B := ∑ s, 1 / ((1 + μ) * ε s * (1 - β / (1 + μ))) + x * (Bz * (β / (1 - β)) + Bz)
  set F : Hist S → ℝ := fun g => (cons x y g) ^ (-ρ)
    * ∑ j, (market K β μ ρ x y M).payoff j g * holdings M x j (anc g)
  have hF : ∀ g s, F (next g s) = 1 / ((1 + μ) * ε s * (1 - β / (1 + μ)))
      + x * (fundU K β ρ x y (next g s) + divU ρ x y (next g s)) := fun g s => by
    have hl : 0 < lam ρ x y (next g s) := Real.rpow_pos_of_pos (mul_pos hx (hy _)) _
    have hlp := lam_div_price (β := β) (μ := μ) (ρ := ρ) (M := M) hy hx (next g s)
    simp only [F, market, holdings, Fin.sum_univ_four, anc_next]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_zero,
      add_zero]
    change lam ρ x y (next g s) * (1 / price β μ ρ x y M (next g s) * M g
      + (fundPrice K β ρ x y (next g s) + y (next g s).1) * x) = _
    have e1 : lam ρ x y (next g s) * (1 / price β μ ρ x y M (next g s) * M g)
        = (lam ρ x y (next g s) * (1 / price β μ ρ x y M (next g s))) * M g := by ring
    rw [mul_add, e1, hlp, hgrowth]
    simp only [fundPrice, divU]
    have := hM g; have := hε s
    field_simp
  have hbF : ∀ g s, 0 ≤ F (next g s) ∧ F (next g s) ≤ B := fun g s => by
    rw [hF]
    have t := fundU_terms (K := K) (ρ := ρ) hy hx hβ0.le hβ1 (next g s)
    have d := divU_bound (ρ := ρ) hy hx (next g s)
    have hpos : ∀ s, 0 ≤ 1 / ((1 + μ) * ε s * (1 - β / (1 + μ))) := fun s =>
      (one_div_pos.2 (mul_pos (mul_pos hμ (hε s)) h1γ)).le
    have hle := Finset.single_le_sum (f := fun s => 1 / ((1 + μ) * ε s * (1 - β / (1 + μ))))
      (fun s _ => hpos s) (Finset.mem_univ s)
    constructor
    · have := hpos s; nlinarith [t.2.1, d.1]
    · simp only [B]; nlinarith [t.2.2, d.2]
  have hbo : ∀ g, 0 ≤ oneStep K.trans F g ∧ oneStep K.trans F g ≤ B := fun g => by
    constructor
    · exact Finset.sum_nonneg fun s _ => mul_nonneg (K.trans_nonneg _ _) (hbF g s).1
    · calc oneStep K.trans F g ≤ oneStep K.trans (fun _ => B) g :=
            Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hbF g s).2 (K.trans_nonneg _ _)
        _ = B := oneStep_const K.trans_sum B g
  have hcv : ∀ T, 0 ≤ Household.contValue K β (fun z => z ^ (-ρ)) (market K β μ ρ x y M) h₀
      (cons x y) (holdings M x) T ∧ Household.contValue K β (fun z => z ^ (-ρ))
      (market K β μ ρ x y M) h₀ (cons x y) (holdings M x) T ≤ β ^ (T + 1) * B := fun T => by
    have e : Household.contValue K β (fun z => z ^ (-ρ)) (market K β μ ρ x y M) h₀ (cons x y)
        (holdings M x) T = β ^ (T + 1) * iterStep K.trans T (oneStep K.trans F) h₀ := by
      simp only [Household.contValue]; rw [iterStep_succ]
    rw [e]
    have l := iterStep_nonneg K.trans_nonneg T (fun g => (hbo g).1) h₀
    have u := iterStep_mono K.trans_nonneg T (X := oneStep K.trans F) (Y := fun _ => B)
      (fun g => (hbo g).2) h₀
    rw [iterStep_const K.trans_sum] at u
    exact ⟨mul_nonneg (pow_nonneg hβ0.le _) l, mul_le_mul_of_nonneg_left u (pow_nonneg hβ0.le _)⟩
  have hup : Tendsto (fun T : ℕ => β ^ (T + 1) * B) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).comp
      (tendsto_add_atTop_nat 1)).mul_const B
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun T => (hcv T).1) (fun T => (hcv T).2)

/-- **The equilibrium lifetime utility is finite** (O&R (91), p. 579): consumption and real
balances depend only on the current state. -/
theorem util_summable {u : ℝ → ℝ} (hy : ∀ s, 0 < y s) (hx : 0 < x) (hM : ∀ h, 0 < M h)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hβμ : β < 1 + μ) (h₀ : Hist S) :
    Summable (Household.utilTerm K β u Real.log (market K β μ ρ x y M) h₀ (cons x y)
      (holdings M x)) := by
  have hμ : 0 < 1 + μ := by linarith
  have h1γ : 0 < 1 - β / (1 + μ) := by have := (div_lt_one hμ).2 hβμ; linarith
  set f : S → ℝ := fun s => u (x * y s) + Real.log (1 / ((1 - β / (1 + μ)) * (x * y s) ^ (-ρ)))
  have hfun : (fun g => u (cons x y g) + Real.log (Household.services (market K β μ ρ x y M)
      (holdings M x) g)) = fun g => f g.1 := by
    funext g
    have := hM g
    have : 0 < (x * y g.1) ^ (-ρ) := Real.rpow_pos_of_pos (mul_pos hx (hy _)) _
    simp only [f, cons, Household.services, market, holdings, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_zero, add_zero]
    congr 2
    simp only [price]; field_simp
    ring
  have hb : ∀ g : Hist S, |f g.1| ≤ ∑ s, |f s| := fun g =>
    Finset.single_le_sum (f := fun s => |f s|) (fun s _ => abs_nonneg _) (Finset.mem_univ _)
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right
    (∑ s, |f s|)) fun t => ?_
  simp only [Household.utilTerm, hfun, Real.norm_eq_abs, abs_mul, abs_of_nonneg
    (pow_nonneg hβ0.le t)]
  exact mul_le_mul_of_nonneg_left (abs_iterStep_le K.trans_nonneg K.trans_sum t hb h₀)
    (pow_nonneg hβ0.le t)

/-- **The §8.7 equilibrium allocation is optimal for each household** (O&R §8.7.1–8.7.3,
pp. 579–583): with CRRA utility `u′(C) = C^{−ρ}` and `v = log`, consumption `C = xY^W`,
money following `M_{t+1} = M_t(1+μ)ε_{t+1}` with `E_t[1/ε] = 1`, the price level
`P = M(1 − β/(1+μ))(xY^W)^{−ρ}` (so `M/P = ω(xY^W)^ρ`), `1 + i = (1+μ)/β`, the market-clearing
real rate and the output-fund price, the plan (money `M`, no bonds, fund share `x`) attains
at least the lifetime utility of EVERY feasible positive rival plan satisfying the no-Ponzi
condition with finite utility. -/
theorem equilibrium_optimal {u : ℝ → ℝ} (hρ : 0 < ρ)
    (hdu : ∀ z, 0 < z → HasDerivAt u (z ^ (-ρ)) z) (hy : ∀ s, 0 < y s) (hx : 0 < x)
    (hε : ∀ s, 0 < ε s) (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1)
    (hM : ∀ h, 0 < M h) (hβ0 : 0 < β) (hβ1 : β < 1) (hβμ : β < 1 + μ)
    (hgrowth : ∀ h s', M (next h s') = M h * (1 + μ) * ε s') (h₀ : Hist S)
    {C' : Hist S → ℝ} {a' : Fin 4 → Hist S → ℝ}
    (hF' : Household.Feasible (market K β μ ρ x y M) h₀ (wealth0 K β μ ρ x y M h₀) C' a')
    (hP' : Household.Positive (market K β μ ρ x y M) h₀ C' a')
    (hnp : Household.NoPonzi K β (fun z => z ^ (-ρ)) (market K β μ ρ x y M) h₀ (cons x y) a')
    (hs' : Summable (Household.utilTerm K β u Real.log (market K β μ ρ x y M) h₀ C' a')) :
    Household.lifetimeU K β u Real.log (market K β μ ρ x y M) h₀ C' a'
      ≤ Household.lifetimeU K β u Real.log (market K β μ ρ x y M) h₀ (cons x y)
        (holdings M x) :=
  Household.household_sufficiency K (market K β μ ρ x y M) hβ0.le (crra_concave hρ hdu) hdu
    strictConcaveOn_log_Ioi.concaveOn (fun _ hz => Real.hasDerivAt_log hz.ne')
    (feasible h₀) hF' (positive hy hx hM hβ0 hβμ h₀) hP'
    (euler_holds hy hx hε hE hM hβ0 hβ1 hβμ hgrowth h₀)
    (tvc hy hx hε hM hβ0 hβ1 hβμ hgrowth h₀) hnp (util_summable hy hx hM hβ0 hβ1 hβμ h₀) hs'

end Equilibrium87

end ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The forward foreign-exchange premium

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §8.7.5 and
Exercises 6–8, pp. 585–592, 601–603.

* Covered interest parity (104): state prices imply CIP; if CIP fails there is an explicit
  zero-cost portfolio with a strictly positive riskless payoff (an arbitrage), which no
  strictly positive state-price vector can price.
* Siegel's paradox (p. 586): `E[ℰ] E[1/ℰ] ≥ 1`, with equality iff `ℰ` is degenerate, so the
  dollar and yen versions of (105) hold together iff the exchange rate is nonrandom.
  (106) for a genuinely Gaussian log exchange rate (Mathlib's Gaussian law): the dollar and
  yen log forward rates are `m ± v/2`. The p. 587 number: `½ (0.1)² = 0.005`.
* Real speculative profits: (107) ⟺ (108) under relative PPP; the exact finite-state
  forward rate `F = E[ℰ/P]/E[1/P] = E[ℰ] + Cov(ℰ, 1/P)/E[1/P]`; (109) given the lognormal
  moment identity for the two relevant linear combinations (fn 75), and (109), (119) under
  genuine joint normality (Mathlib's `HasGaussianLaw` for `(e, p)` and `(e, p, c)`).
* The Fama decomposition (110)–(115) on a two-date finite event tree: the rational-
  expectations orthogonality is DERIVED (tower property); the population OLS slope
  minimises mean squared error; `a₁ < 0 ⇒ Cov(D, rp) < 0`, `a₁ < ½ ⇒ Var rp > Var D`.
* The forward rate in general equilibrium (116)–(119): the real-return differential
  identity, the forward-position Euler equation (necessary and sufficient), CRRA form,
  exact covariance form, and (119) given the lognormal moment identity.
* Exercise 6 (Engel 1992): `∂C/∂C_j = p_j/P` for homogeneous `Ω`; the multi-good
  forward Euler equations; the yen version and risk neutrality (no Siegel paradox in real
  terms); the two-good cash-in-advance spot rate and forward rate with independent money
  and output shocks; the "risk-neutral" forward equation (107) and its yen version.
* Exercises 7 and 8: time-averaged exchange rates are not random walks (autocorrelation
  1/6); point sampling is; overlapping forecast errors have correlation 1/2; every-other-
  observation errors are uncorrelated for ANY exchange-rate process (tower property).
-/

namespace ObstfeldRogoff.MoneyExchangeRates.ForwardPremium

open Finset Filter Topology
open ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing

variable {S : Type} [Fintype S]

/-! ## Covered interest parity (104) -/

/-- The dollar cost at `t` of `a` dollars in dollar bonds and `b` yen in yen bonds (the
forward position costs nothing) (O&R (104), p. 585). -/
def cipCost (E a b : ℝ) : ℝ := a + b * E

/-- The dollar payoff at `t+1` in state `s` of `a` dollars in dollar bonds, `b` yen in yen
bonds and `c` yen bought forward at `F` (O&R (104), p. 585). -/
def cipPayoff (i istar F : ℝ) (E' : S → ℝ) (a b c : ℝ) (s : S) : ℝ :=
  a * (1 + i) + b * (1 + istar) * E' s + c * (E' s - F)

omit [Fintype S] in
/-- **The covered-interest-arbitrage portfolio is riskless** (O&R p. 586): borrow one
dollar, buy `1/ℰ` yen, invest at `i*`, sell the proceeds forward. It costs nothing and pays
`(1+i*)F/ℰ − (1+i)` in EVERY state. -/
theorem cip_portfolio_riskless {i istar E F : ℝ} (hE : E ≠ 0) (E' : S → ℝ) (s : S) :
    cipCost E (-1) (1 / E) = 0 ∧
      cipPayoff i istar F E' (-1) (1 / E) (-((1 + istar) / E)) s
        = (1 + istar) * F / E - (1 + i) := by
  constructor
  · simp only [cipCost]; field_simp; ring
  · simp only [cipPayoff]; field_simp; ring

omit [Fintype S] in
/-- **If CIP fails there is an arbitrage** (O&R (104), p. 585): a zero-cost portfolio whose
payoff is strictly positive in every state. -/
theorem arbitrage_of_not_cip {i istar E F : ℝ} (hE : E ≠ 0) (E' : S → ℝ)
    (hcip : 1 + i ≠ (1 + istar) * F / E) :
    ∃ a b c : ℝ, cipCost E a b = 0 ∧ ∀ s, 0 < cipPayoff i istar F E' a b c s := by
  rcases lt_or_gt_of_ne hcip with h | h
  · refine ⟨-1, 1 / E, -((1 + istar) / E), ?_, fun s => ?_⟩
    · simp only [cipCost]; field_simp; ring
    · rw [(cip_portfolio_riskless hE E' s).2]; linarith
  · refine ⟨1, -(1 / E), (1 + istar) / E, ?_, fun s => ?_⟩
    · simp only [cipCost]; field_simp; ring
    · have := (cip_portfolio_riskless (i := i) (istar := istar) (F := F) hE E' s).2
      simp only [cipPayoff] at this ⊢
      linarith

/-- A strictly positive state-price vector values every portfolio (O&R p. 586, "no
arbitrage"): dollar bonds, yen bonds and forwards are priced by `q`. -/
structure StatePrices (S : Type) [Fintype S] where
  q : S → ℝ
  q_pos : ∀ s, 0 < q s

/-- The pricing conditions for the three instruments (O&R (104), p. 585). -/
def PricesInstruments (qs : StatePrices S) (i istar E F : ℝ) (E' : S → ℝ) : Prop :=
  (∑ s, qs.q s * (1 + i) = 1) ∧ (∑ s, qs.q s * ((1 + istar) * E' s) = E) ∧
    (∑ s, qs.q s * (E' s - F) = 0)

/-- **State prices imply covered interest parity** (O&R (104), p. 585):
`1 + i = (1 + i*) F/ℰ`. -/
theorem cip_of_statePrices [Nonempty S] {qs : StatePrices S} {i istar E F : ℝ}
    {E' : S → ℝ} (hE : 0 < E) (hp : PricesInstruments qs i istar E F E') :
    1 + i = (1 + istar) * F / E := by
  obtain ⟨h1, h2, h3⟩ := hp
  have hQ : 0 < ∑ s, qs.q s := Finset.sum_pos (fun s _ => qs.q_pos s) Finset.univ_nonempty
  have hb : (∑ s, qs.q s) * (1 + i) = 1 := by rw [Finset.sum_mul]; exact h1
  have hf : ∑ s, qs.q s * E' s = F * ∑ s, qs.q s := by
    have : ∑ s, (qs.q s * E' s - F * qs.q s) = 0 := by
      rw [← h3]; exact Finset.sum_congr rfl fun s _ => by ring
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at this
    linarith
  have hy : (1 + istar) * ∑ s, qs.q s * E' s = E := by
    rw [Finset.mul_sum, ← h2]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [hf] at hy
  field_simp
  nlinarith [hb, hy]

/-- **An arbitrage cannot be priced by strictly positive state prices** (O&R p. 586). -/
theorem no_statePrices_of_arbitrage [Nonempty S] (qs : StatePrices S) {i istar E F : ℝ}
    {E' : S → ℝ} (hp : PricesInstruments qs i istar E F E') {a b c : ℝ}
    (hcost : cipCost E a b = 0) (hpay : ∀ s, 0 < cipPayoff i istar F E' a b c s) :
    False := by
  obtain ⟨h1, h2, h3⟩ := hp
  have hval : ∑ s, qs.q s * cipPayoff i istar F E' a b c s = cipCost E a b := by
    have e : ∀ s, qs.q s * cipPayoff i istar F E' a b c s = a * (qs.q s * (1 + i))
        + b * (qs.q s * ((1 + istar) * E' s)) + c * (qs.q s * (E' s - F)) := fun s => by
      simp only [cipPayoff]; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, h3, cipCost]
    ring
  have hpos : 0 < ∑ s, qs.q s * cipPayoff i istar F E' a b c s :=
    Finset.sum_pos (fun s _ => mul_pos (qs.q_pos s) (hpay s)) Finset.univ_nonempty
  linarith

/-! ## Siegel's paradox (105)–(106) -/

/-- The symmetrised Jensen gap: `E[X]E[1/X] − 1 = ½ ΣΣ πᵢπⱼ (Xᵢ − Xⱼ)²/(XᵢXⱼ)`
(O&R p. 586, Jensen's inequality for `1/(·)` made exact on a finite space). -/
theorem expect_mul_expect_inv (Ω : FinProb S) {X : S → ℝ} (hX : ∀ s, 0 < X s) :
    2 * (Ω.expect X * Ω.expect (fun s => 1 / X s) - 1)
      = ∑ i, ∑ j, Ω.prob i * Ω.prob j * (X i - X j) ^ 2 / (X i * X j) := by
  have h1 : Ω.expect X * Ω.expect (fun s => 1 / X s)
      = ∑ i, ∑ j, Ω.prob i * Ω.prob j * (X i / X j) := by
    simp only [FinProb.expect, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsym : ∑ i, ∑ j, Ω.prob i * Ω.prob j * (X j / X i)
      = ∑ i, ∑ j, Ω.prob i * Ω.prob j * (X i / X j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e : ∀ i j, Ω.prob i * Ω.prob j * (X i - X j) ^ 2 / (X i * X j)
      = Ω.prob i * Ω.prob j * (X i / X j) + Ω.prob i * Ω.prob j * (X j / X i)
        - 2 * (Ω.prob i * Ω.prob j) := fun i j => by
    have := hX i; have := hX j
    field_simp; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsym, h1]
  simp only [Ω.prob_sum, mul_one]
  ring

/-- **Jensen for `1/ℰ`** (O&R p. 586): `E[1/ℰ] ≥ 1/E[ℰ]`, i.e. `E[ℰ]E[1/ℰ] ≥ 1`. -/
theorem one_le_expect_mul_expect_inv (Ω : FinProb S) {X : S → ℝ} (hX : ∀ s, 0 < X s) :
    1 ≤ Ω.expect X * Ω.expect (fun s => 1 / X s) := by
  have h := expect_mul_expect_inv Ω hX
  have : 0 ≤ ∑ i, ∑ j, Ω.prob i * Ω.prob j * (X i - X j) ^ 2 / (X i * X j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      div_nonneg (mul_nonneg (mul_nonneg (Ω.prob_nonneg i) (Ω.prob_nonneg j)) (sq_nonneg _))
        (mul_pos (hX i) (hX j)).le
  linarith

/-- A random variable is degenerate if it takes one value on the support (O&R p. 586,
"in general"). -/
def Degenerate (Ω : FinProb S) (X : S → ℝ) : Prop :=
  ∀ i j, 0 < Ω.prob i → 0 < Ω.prob j → X i = X j

/-- **Strict Jensen** (O&R p. 586): a nondegenerate positive exchange rate has
`E[1/ℰ] > 1/E[ℰ]`. -/
theorem one_lt_expect_mul_expect_inv (Ω : FinProb S) {X : S → ℝ} (hX : ∀ s, 0 < X s)
    (hnd : ¬ Degenerate Ω X) : 1 < Ω.expect X * Ω.expect (fun s => 1 / X s) := by
  simp only [Degenerate, not_forall] at hnd
  obtain ⟨i₀, j₀, hi, hj, hne⟩ := hnd
  have h := expect_mul_expect_inv Ω hX
  set g : S → S → ℝ := fun i j => Ω.prob i * Ω.prob j * (X i - X j) ^ 2 / (X i * X j)
  have hg : ∀ i j, 0 ≤ g i j := fun i j =>
    div_nonneg (mul_nonneg (mul_nonneg (Ω.prob_nonneg i) (Ω.prob_nonneg j)) (sq_nonneg _))
      (mul_pos (hX i) (hX j)).le
  have hsq : 0 < (X i₀ - X j₀) ^ 2 := by
    have : X i₀ - X j₀ ≠ 0 := sub_ne_zero.2 hne
    positivity
  have hpos : 0 < g i₀ j₀ := div_pos (mul_pos (mul_pos hi hj) hsq) (mul_pos (hX i₀) (hX j₀))
  have h1 : g i₀ j₀ ≤ ∑ j, g i₀ j :=
    Finset.single_le_sum (f := g i₀) (fun j _ => hg i₀ j) (Finset.mem_univ j₀)
  have h2 : ∑ j, g i₀ j ≤ ∑ i, ∑ j, g i j :=
    Finset.single_le_sum (f := fun i => ∑ j, g i j)
      (fun i _ => Finset.sum_nonneg fun j _ => hg i j) (Finset.mem_univ i₀)
  have : 0 < ∑ i, ∑ j, g i j := by linarith
  simp only [g] at this
  linarith

/-- The expectation of a degenerate variable is its common value (O&R p. 586). -/
theorem expect_of_degenerate (Ω : FinProb S) {X : S → ℝ} (hd : Degenerate Ω X) {s₀ : S}
    (hs₀ : 0 < Ω.prob s₀) : Ω.expect X = X s₀ := by
  have : ∀ s, Ω.prob s * X s = Ω.prob s * X s₀ := fun s => by
    rcases (Ω.prob_nonneg s).lt_or_eq with h | h
    · rw [hd s s₀ h hs₀]
    · rw [← h]; ring
  simp only [FinProb.expect, this, ← Finset.sum_mul, Ω.prob_sum, one_mul]

/-- **Siegel's paradox** (O&R (105), p. 586): the dollar version `F = E[ℰ]` and the yen
version `1/F = E[1/ℰ]` of the unbiasedness hypothesis hold simultaneously IFF the future
spot rate is degenerate. -/
theorem siegel_iff (Ω : FinProb S) {X : S → ℝ} (hX : ∀ s, 0 < X s) :
    (∃ F, F = Ω.expect X ∧ 1 / F = Ω.expect (fun s => 1 / X s)) ↔ Degenerate Ω X := by
  constructor
  · rintro ⟨F, hF1, hF2⟩
    by_contra hnd
    have h := one_lt_expect_mul_expect_inv Ω hX hnd
    have hFpos : 0 < F := hF1 ▸ Ω.expect_pos hX
    rw [← hF1, ← hF2, mul_one_div_cancel hFpos.ne'] at h
    exact lt_irrefl 1 h
  · intro hd
    obtain ⟨s₀, hs₀⟩ := Ω.exists_prob_pos
    refine ⟨X s₀, (expect_of_degenerate Ω hd hs₀).symm, ?_⟩
    have hd' : Degenerate Ω (fun s => 1 / X s) := fun i j hi hj => by
      simp only [hd i j hi hj]
    exact (expect_of_degenerate Ω hd' hs₀).symm

/-- The p. 587 number: a 10 percent standard deviation of the log exchange rate gives a
Jensen term `½ Var = 0.005` (O&R p. 587). -/
theorem jensen_term_number : (1 / 2 : ℝ) * (0.1 : ℝ) ^ 2 = (0.005 : ℝ) := by norm_num

namespace Gaussian

open MeasureTheory ProbabilityTheory

/-- **(106) for a Gaussian log exchange rate** (O&R (106), p. 587): if `e = log ℰ_{t+1}`
has the Gaussian law with mean `m` and variance `v` (Mathlib's `gaussianReal`), then
`E[ℰ] = exp(m + v/2)` and `E[1/ℰ] = exp(−m + v/2)`. -/
theorem expect_exp_gaussian {Ω' : Type*} {mΩ : MeasurableSpace Ω'} {P : Measure Ω'}
    {e : Ω' → ℝ} {m : ℝ} {v : NNReal} (he : HasLaw e (gaussianReal m v) P) :
    (∫ ω, Real.exp (e ω) ∂P) = Real.exp (m + v / 2) ∧
      (∫ ω, Real.exp (-e ω) ∂P) = Real.exp (-m + v / 2) := by
  have h1 := mgf_gaussianReal he 1
  have h2 := mgf_gaussianReal he (-1)
  simp only [mgf, one_mul, neg_one_mul] at h1 h2
  refine ⟨h1.trans (congrArg Real.exp (by ring)), h2.trans (congrArg Real.exp (by ring))⟩

/-- **The dollar and yen log forward rates under lognormality** (O&R (106), p. 587):
`F = E[ℰ]` gives `f = m + v/2`; the yen version `1/F* = E[1/ℰ]` gives `f* = m − v/2`; they
agree iff `v = 0`. -/
theorem log_forward_gaussian {Ω' : Type*} {mΩ : MeasurableSpace Ω'} {P : Measure Ω'}
    {e : Ω' → ℝ} {m : ℝ} {v : NNReal} (he : HasLaw e (gaussianReal m v) P) {F Fy : ℝ}
    (hF : F = ∫ ω, Real.exp (e ω) ∂P) (hFy : 1 / Fy = ∫ ω, Real.exp (-e ω) ∂P) :
    Real.log F = m + v / 2 ∧ Real.log Fy = m - v / 2 ∧ (Real.log F = Real.log Fy ↔ v = 0) := by
  obtain ⟨h1, h2⟩ := expect_exp_gaussian he
  have hlF : Real.log F = m + v / 2 := by rw [hF, h1, Real.log_exp]
  have hFy' : Fy = Real.exp (m - v / 2) := by
    rw [h2] at hFy
    have : Fy = 1 / Real.exp (-m + v / 2) := by
      rw [← hFy]; field_simp
    rw [this, one_div, ← Real.exp_neg]; congr 1; ring
  have hlFy : Real.log Fy = m - v / 2 := by rw [hFy', Real.log_exp]
  refine ⟨hlF, hlFy, ?_⟩
  rw [hlF, hlFy]
  constructor
  · intro h
    have : (v : ℝ) = 0 := by linarith
    exact_mod_cast this
  · intro h; rw [h]; simp

end Gaussian

/-! ## Real speculative profits (107)–(109) -/

/-- **(107) ⟺ (108) under relative PPP** (O&R (107)–(108), p. 587): with
`P_{t+1} = κ ℰ_{t+1} P*_{t+1}`, zero expected real dollar profits from a forward position is
equivalent to zero expected real yen profits. -/
theorem eq107_iff_eq108 (Ω : FinProb S) {F κ : ℝ} {E' P' Ps' : S → ℝ} (hF : 0 < F)
    (hκ : 0 < κ) (hE' : ∀ s, 0 < E' s) (hPs : ∀ s, 0 < Ps' s)
    (hppp : ∀ s, P' s = κ * E' s * Ps' s) :
    Ω.expect (fun s => (F - E' s) / P' s) = 0 ↔
      Ω.expect (fun s => (1 / F - 1 / E' s) / Ps' s) = 0 := by
  have e : (fun s => (F - E' s) / P' s) = fun s => -(F / κ) * ((1 / F - 1 / E' s) / Ps' s) := by
    funext s
    rw [hppp s]
    have := hE' s; have := hPs s
    field_simp; ring
  rw [e, Ω.expect_mul_left]
  have : -(F / κ) ≠ 0 := neg_ne_zero.2 (div_pos hF hκ).ne'
  constructor
  · intro h; exact (mul_eq_zero.1 h).resolve_left this
  · intro h; rw [h, mul_zero]

/-- **The forward rate from (107)** (O&R (107), p. 587; Exercise 6(f), p. 602):
`E[(F − ℰ)/P] = 0 ⟺ F = E[ℰ/P]/E[1/P]`. -/
theorem eq107_iff_ratio (Ω : FinProb S) {F : ℝ} {E' P' : S → ℝ} (hP' : ∀ s, 0 < P' s) :
    Ω.expect (fun s => (F - E' s) / P' s) = 0 ↔
      F = Ω.expect (fun s => E' s / P' s) / Ω.expect (fun s => 1 / P' s) := by
  have hpos : 0 < Ω.expect (fun s => 1 / P' s) := Ω.expect_pos fun s => one_div_pos.2 (hP' s)
  have e : (fun s => (F - E' s) / P' s) = fun s => F * (1 / P' s) - E' s / P' s := by
    funext s; ring
  rw [e, Ω.expect_sub, Ω.expect_mul_left, eq_div_iff hpos.ne']
  constructor <;> intro h <;> linarith

/-- **The exact finite-state analogue of (109)** (O&R (109), p. 588, without
lognormality): under (107), `F = E[ℰ] + Cov(ℰ, 1/P)/E[1/P]`, so the forward rate is
unbiased iff the future spot rate is uncorrelated with the purchasing power of money. -/
theorem forward_exact_decomposition (Ω : FinProb S) {F : ℝ} {E' P' : S → ℝ}
    (hP' : ∀ s, 0 < P' s) (h107 : Ω.expect (fun s => (F - E' s) / P' s) = 0) :
    F = Ω.expect E' + Ω.cov E' (fun s => 1 / P' s) / Ω.expect (fun s => 1 / P' s) := by
  have hpos : 0 < Ω.expect (fun s => 1 / P' s) := Ω.expect_pos fun s => one_div_pos.2 (hP' s)
  rw [(eq107_iff_ratio Ω hP').1 h107]
  have : Ω.expect (fun s => E' s / P' s) = Ω.expect (fun s => E' s * (1 / P' s)) := by
    congr 1; funext s; ring
  rw [this, Ω.expect_mul_eq]
  field_simp

/-- The lognormal moment identity `E[exp Z] = exp(E Z + ½ Var Z)` for a random variable
(O&R fn 41 of Ch. 5, used in fn 75, p. 588), stated as an explicit hypothesis. -/
def LognormalMGF (Ω : FinProb S) (Z : S → ℝ) : Prop :=
  Ω.expect (fun s => Real.exp (Z s)) = Real.exp (Ω.expect Z + Ω.var Z / 2)

/-- `Var(−X) = Var X` (O&R fn 75, p. 588). -/
theorem var_neg (Ω : FinProb S) (X : S → ℝ) : Ω.var (fun s => -X s) = Ω.var X := by
  have : (fun s => -X s) = fun s => (-1) * X s := funext fun s => by ring
  simp only [this, FinProb.var, FinProb.cov_mul_left, FinProb.cov_mul_right]; ring

/-- **(109)** (O&R (109) and fn 75, p. 588): if (107) holds and the lognormal moment
identity holds for `−p` and `e − p` (as under joint normality of the logs `e, p`), then
`f = E e + ½ Var e − Cov(e, p)`. -/
theorem eq109 (Ω : FinProb S) {F : ℝ} (hF : 0 < F) {e p : S → ℝ}
    (h107 : Ω.expect (fun s => (F - Real.exp (e s)) / Real.exp (p s)) = 0)
    (h1 : LognormalMGF Ω (fun s => -p s)) (h2 : LognormalMGF Ω (fun s => e s - p s)) :
    Real.log F = Ω.expect e + Ω.var e / 2 - Ω.cov e p := by
  have ex : (fun s => (F - Real.exp (e s)) / Real.exp (p s))
      = fun s => F * Real.exp (-p s) - Real.exp (e s - p s) := by
    funext s; rw [Real.exp_neg, Real.exp_sub]; field_simp
  rw [ex, Ω.expect_sub, Ω.expect_mul_left, h1, h2, sub_eq_zero] at h107
  have hl := congrArg Real.log h107
  rw [Real.log_mul hF.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at hl
  rw [var_neg, Ω.var_sub, Ω.expect_sub] at hl
  have : Ω.expect (fun s => -p s) = -Ω.expect p := by
    rw [show (fun s => -p s) = fun s => (-1) * p s from funext fun s => by ring,
      Ω.expect_mul_left]; ring
  rw [this] at hl
  linarith

/-- **(106) as the nonstochastic-price case of (109)** (O&R fn 75, p. 588): with a constant
price level `p ≡ p̄`, `f = E e + ½ Var e`. -/
theorem eq106_of_constant_price (Ω : FinProb S) {F pbar : ℝ} (hF : 0 < F) {e : S → ℝ}
    (h107 : Ω.expect (fun s => (F - Real.exp (e s)) / Real.exp pbar) = 0)
    (h2 : LognormalMGF Ω (fun s => e s - pbar)) :
    Real.log F = Ω.expect e + Ω.var e / 2 := by
  have h1 : LognormalMGF Ω (fun _ => -pbar) := by
    simp only [LognormalMGF, FinProb.expect_const, FinProb.var, FinProb.cov_const_left]
    ring_nf
  have := eq109 Ω hF (p := fun _ => pbar) h107 h1 h2
  rw [this, Ω.cov_comm, Ω.cov_const_left, sub_zero]

/-! ## The forward rate in general equilibrium (116)–(119) -/

/-- **The real-return differential identity** (O&R p. 591): with CIP (104) and PPP (92),
`(1+i)P_t/P_{t+1} − (1+i*)P*_t/P*_{t+1} = ((1+i)P_t/F_t)(F_t − ℰ_{t+1})/P_{t+1}`. -/
theorem real_return_differential {i istar P Ps F E E' P' Ps' : ℝ} (hF : 0 < F)
    (hE : 0 < E) (hE' : 0 < E') (hPs' : 0 < Ps') (hcip : 1 + i = (1 + istar) * F / E)
    (hppp : P = E * Ps) (hppp' : P' = E' * Ps') :
    (1 + i) * P / P' - (1 + istar) * Ps / Ps' = (1 + i) * P / F * ((F - E') / P') := by
  have hi : 1 + istar = (1 + i) * E / F := by
    rw [hcip]; field_simp
  rw [hi, hppp, hppp']
  field_simp

/-- **(116) from (93)** (O&R (116), p. 591): if both assets satisfy the Euler equation (93),
the return differential has zero marginal-utility-weighted expectation. -/
theorem eq116_of_euler (Ω : FinProb S) {β uC : ℝ} {rn rm m : S → ℝ} (huC : 0 < uC)
    (hn : uC = β * Ω.expect (fun s => (1 + rn s) * m s))
    (hm : uC = β * Ω.expect (fun s => (1 + rm s) * m s)) :
    Ω.expect (fun s => (rn s - rm s) * (m s / uC)) = 0 := by
  have e : (fun s => (rn s - rm s) * (m s / uC))
      = fun s => 1 / uC * ((1 + rn s) * m s - (1 + rm s) * m s) := by
    funext s; field_simp; ring
  rw [e, Ω.expect_mul_left, Ω.expect_sub]
  have : Ω.expect (fun s => (1 + rn s) * m s) = Ω.expect (fun s => (1 + rm s) * m s) := by
    by_cases hβ : β = 0
    · rw [hβ, zero_mul] at hn; linarith
    · exact mul_left_cancel₀ hβ (hn.symm.trans hm)
  rw [this, sub_self, mul_zero]

/-- **(117) from (116)** (O&R (117), p. 591): substituting the real-return differential of
the two nominal bonds and factoring out the date-`t` term `(1+i)P_t/F_t`. -/
theorem eq117_of_eq116 (Ω : FinProb S) {i P F uC : ℝ} {E' P' m d : S → ℝ} (hi : 0 < 1 + i)
    (hP : 0 < P) (hF : 0 < F)
    (hd : ∀ s, d s = (1 + i) * P / F * ((F - E' s) / P' s))
    (h116 : Ω.expect (fun s => d s * (m s / uC)) = 0) :
    Ω.expect (fun s => (F - E' s) / P' s * (m s / uC)) = 0 := by
  have e : (fun s => d s * (m s / uC))
      = fun s => (1 + i) * P / F * ((F - E' s) / P' s * (m s / uC)) := by
    funext s; rw [hd s]; ring
  rw [e, Ω.expect_mul_left] at h116
  exact (mul_eq_zero.1 h116).resolve_left (by positivity)

/-- **The forward-position Euler equation is necessary and sufficient** (O&R (117),
p. 591: "a forward position, which requires no money down in period t, must yield zero
expected utility in equilibrium"): buying `δ` yen forward costs nothing and pays
`δ(ℰ_{t+1} − F)/P_{t+1}` in real terms. -/
theorem forward_euler_iff {u u' : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) {Ω : FinProb S} {β C F : ℝ}
    {C' E' P' : S → ℝ} (hβ : 0 < β) (hC : 0 < C) (huC : 0 < u' C) (hC' : ∀ s, 0 < C' s) :
    IsLocalMax (assetValue u Ω β C 0 C' (fun s => (E' s - F) / P' s)) 0 ↔
      Ω.expect (fun s => (F - E' s) / P' s * (u' (C' s) / u' C)) = 0 := by
  rw [isLocalMax_assetValue_iff hc hd hβ.le hC hC', zero_mul]
  have e : (fun s => (F - E' s) / P' s * (u' (C' s) / u' C))
      = fun s => (-(1 / u' C)) * (u' (C' s) * ((E' s - F) / P' s)) := by
    funext s; field_simp; ring
  rw [e, Ω.expect_mul_left]
  constructor
  · intro h
    have : Ω.expect (fun s => u' (C' s) * ((E' s - F) / P' s)) = 0 := by
      rcases mul_eq_zero.1 h.symm with h1 | h1
      · linarith
      · exact h1
    rw [this, mul_zero]
  · intro h
    have hne : -(1 / u' C) ≠ 0 := neg_ne_zero.2 (one_div_pos.2 huC).ne'
    rw [(mul_eq_zero.1 h).resolve_left hne, mul_zero]

/-- **(118)**: with CRRA utility `u′(C) = C^{−ρ}`, `u′(C_{t+1})/u′(C_t) = (C_t/C_{t+1})^ρ`
(O&R (118), p. 591). -/
theorem crra_mrs {C C' ρ : ℝ} (hC : 0 < C) (hC' : 0 < C') :
    C' ^ (-ρ) / C ^ (-ρ) = (C / C') ^ ρ := by
  rw [Real.rpow_neg hC'.le, Real.rpow_neg hC.le, Real.div_rpow hC.le hC'.le]
  have := Real.rpow_pos_of_pos hC ρ; have := Real.rpow_pos_of_pos hC' ρ
  field_simp

/-- **The exact general-equilibrium forward rate** (O&R (117), p. 591, without
lognormality): with `m = u′(C_{t+1})/P_{t+1} > 0`, (117) holds iff
`F = E[ℰ m]/E[m] = E[ℰ] + Cov(ℰ, m)/E[m]`: the forward premium over the expected spot rate
is exactly the covariance risk premium. -/
theorem forward_rate_ge (Ω : FinProb S) {F uC : ℝ} {E' m : S → ℝ} (huC : 0 < uC)
    (hm : ∀ s, 0 < m s) :
    Ω.expect (fun s => (F - E' s) * (m s / uC)) = 0 ↔
      F = Ω.expect E' + Ω.cov E' m / Ω.expect m := by
  have hpos := Ω.expect_pos hm
  have e : (fun s => (F - E' s) * (m s / uC)) = fun s => 1 / uC * (F * m s - E' s * m s) := by
    funext s; field_simp
  rw [e, Ω.expect_mul_left, Ω.expect_sub, Ω.expect_mul_left, Ω.expect_mul_eq]
  have hu : 1 / uC ≠ 0 := (one_div_pos.2 huC).ne'
  constructor
  · intro h
    have := (mul_eq_zero.1 h).resolve_left hu
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- **(119)** (O&R (119), p. 592, with the hint of fn 79): if (118) holds and the lognormal
moment identity holds for `−(p + ρc)` and `e − (p + ρc)` (logs of `ℰ_{t+1}, P_{t+1},
C_{t+1}`; `C_t = exp c₀` known at `t`), then
`f − E e = ½ Var e − Cov(e, p) − ρ Cov(e, c)`. -/
theorem eq119 (Ω : FinProb S) {F ρ c₀ : ℝ} (hF : 0 < F) {e p c : S → ℝ}
    (h118 : Ω.expect (fun s => (F - Real.exp (e s)) / Real.exp (p s)
      * (Real.exp c₀ / Real.exp (c s)) ^ ρ) = 0)
    (h1 : LognormalMGF Ω (fun s => -(p s + ρ * c s)))
    (h2 : LognormalMGF Ω (fun s => e s + -(p s + ρ * c s))) :
    Real.log F - Ω.expect e = Ω.var e / 2 - Ω.cov e p - ρ * Ω.cov e c := by
  set Z : S → ℝ := fun s => -(p s + ρ * c s)
  have ex : (fun s => (F - Real.exp (e s)) / Real.exp (p s)
      * (Real.exp c₀ / Real.exp (c s)) ^ ρ)
      = fun s => Real.exp (ρ * c₀) * (F * Real.exp (Z s) - Real.exp (e s + Z s)) := by
    funext s
    rw [← Real.exp_sub, ← Real.exp_mul]
    simp only [Z, Real.exp_add, Real.exp_neg]
    rw [show (c₀ - c s) * ρ = ρ * c₀ + -(ρ * c s) by ring, Real.exp_add, Real.exp_neg]
    field_simp
  rw [ex, Ω.expect_mul_left, Ω.expect_sub, Ω.expect_mul_left] at h118
  have h3 := (mul_eq_zero.1 h118).resolve_left (Real.exp_pos _).ne'
  rw [h1, h2, sub_eq_zero] at h3
  have hl := congrArg Real.log h3
  rw [Real.log_mul hF.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp, Ω.expect_add,
    Ω.var_add] at hl
  have hcov : Ω.cov e Z = -(Ω.cov e p + ρ * Ω.cov e c) := by
    have : Z = fun s => (-1) * (p s + ρ * c s) := funext fun s => by simp [Z]
    rw [this, Ω.cov_mul_right, Ω.cov_add_right, Ω.cov_mul_right]; ring
  rw [hcov] at hl
  linarith

/-- With `ρ = 0` (risk-neutral investors who care about real returns) (119) reduces to
(109) (O&R p. 592). -/
theorem eq119_rho_zero (Ω : FinProb S) {F c₀ : ℝ} (hF : 0 < F) {e p c : S → ℝ}
    (h118 : Ω.expect (fun s => (F - Real.exp (e s)) / Real.exp (p s)
      * (Real.exp c₀ / Real.exp (c s)) ^ (0 : ℝ)) = 0)
    (h1 : LognormalMGF Ω (fun s => -(p s + 0 * c s)))
    (h2 : LognormalMGF Ω (fun s => e s + -(p s + 0 * c s))) :
    Real.log F = Ω.expect e + Ω.var e / 2 - Ω.cov e p := by
  have := eq119 Ω hF h118 h1 h2
  linarith

/-- **The world-output form of (119)** (O&R p. 592): with `C = xY^W`, `c = log x + y^W`, so
`Cov(e, c) = Cov(e, y^W)`. -/
theorem cov_consumption_eq_output (Ω : FinProb S) {e y : S → ℝ} (logx : ℝ) :
    Ω.cov e (fun s => logx + y s) = Ω.cov e y :=
  Ω.cov_add_const_right logx e y

/-! ## The Fama decomposition (110)–(115) -/

/-- The joint distribution of today's state (law `π`) and tomorrow's state (kernel `K`):
the two-date event tree behind the regression (110) (O&R p. 588). -/
def pairProb (π : FinProb S) (K : Kernel S) : FinProb (S × S) :=
  ⟨fun q => π.prob q.1 * K.trans q.1 q.2,
    fun q => mul_nonneg (π.prob_nonneg _) (K.trans_nonneg _ _), by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, K.trans_sum, mul_one, π.prob_sum]⟩

/-- The rational-expectations forecast `E_t Y_{t+1}` (O&R p. 590). -/
def condE (K : Kernel S) (Y : S → S → ℝ) (s : S) : ℝ := ∑ s', K.trans s s' * Y s s'

/-- **Rational expectations: forecast errors are orthogonal to date-`t` information**
(O&R p. 590, "must be uncorrelated with all variables observable on date t"), derived from
the tower property. -/
theorem forecast_error_orthogonal (π : FinProb S) (K : Kernel S) (g : S → ℝ)
    (Y : S → S → ℝ) :
    (pairProb π K).expect (fun q => g q.1 * (Y q.1 q.2 - condE K Y q.1)) = 0 := by
  simp only [FinProb.expect, pairProb, Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun s _ => ?_
  have e : ∑ s', π.prob s * K.trans s s' * (g s * (Y s s' - condE K Y s))
      = π.prob s * g s * (∑ s', K.trans s s' * Y s s' - condE K Y s * ∑ s', K.trans s s') := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s' _ => by ring
  rw [e, K.trans_sum, mul_one]
  simp [condE]

namespace Fama

variable (π : FinProb S) (K : Kernel S) (f e : S → ℝ) (e' : S → S → ℝ)

/-- The forward premium `f_t − e_t` (O&R (110), p. 588). -/
def fwdPrem : S × S → ℝ := fun q => f q.1 - e q.1

/-- Expected depreciation `D_t = E_t e_{t+1} − e_t` (O&R (112), p. 590). -/
def expDep : S × S → ℝ := fun q => condE K e' q.1 - e q.1

/-- The risk premium `rp_t = f_t − E_t e_{t+1}` (O&R p. 590). -/
def riskPrem : S × S → ℝ := fun q => f q.1 - condE K e' q.1

/-- Realised depreciation `e_{t+1} − e_t` (O&R (110), p. 588). -/
def realDep : S × S → ℝ := fun q => e' q.1 q.2 - e q.1

/-- **(112)**: `f_t − e_t = (E_t e_{t+1} − e_t) + rp_t` (O&R (112), p. 590). -/
theorem fwdPrem_eq : fwdPrem f e = fun q => expDep K e e' q + riskPrem K f e' q := by
  funext q; simp only [fwdPrem, expDep, riskPrem]; ring

/-- **(113)**: `Cov(f − e, e_{t+1} − e_t) = Cov(f − e, E_t e_{t+1} − e_t)`, because the
forecast error is orthogonal to the forward premium (O&R (113), p. 590). -/
theorem cov_fwdPrem_realDep :
    (pairProb π K).cov (fwdPrem f e) (realDep e e')
      = (pairProb π K).cov (fwdPrem f e) (expDep K e e') := by
  have hsplit : realDep e e' = fun q => expDep K e e' q + (e' q.1 q.2 - condE K e' q.1) := by
    funext q; simp only [realDep, expDep]; ring
  rw [hsplit, FinProb.cov_add_right]
  have h1 := forecast_error_orthogonal π K (fun s => f s - e s) e'
  have h2 := forecast_error_orthogonal π K (fun _ => 1) e'
  simp only [one_mul] at h2
  have h0 : (pairProb π K).cov (fwdPrem f e) (fun q => e' q.1 q.2 - condE K e' q.1) = 0 := by
    simp only [FinProb.cov, fwdPrem]
    rw [h1, h2, mul_zero, sub_zero]
  rw [h0, add_zero]

/-- **The population slope of (110)** (O&R (111), (113)–(114), p. 590):
`a₁ = [Var D + Cov(D, rp)]/[Var D + 2Cov(D, rp) + Var rp]` (the book's `plim` of the OLS
estimator is this population coefficient). -/
theorem fama_slope :
    (pairProb π K).cov (fwdPrem f e) (realDep e e') / (pairProb π K).var (fwdPrem f e)
      = ((pairProb π K).var (expDep K e e') + (pairProb π K).cov (expDep K e e')
          (riskPrem K f e'))
        / ((pairProb π K).var (expDep K e e') + 2 * (pairProb π K).cov (expDep K e e')
          (riskPrem K f e') + (pairProb π K).var (riskPrem K f e')) := by
  rw [cov_fwdPrem_realDep, fwdPrem_eq, FinProb.var_add, FinProb.cov_add_left,
    (pairProb π K).cov_comm (riskPrem K f e') (expDep K e e')]
  simp only [FinProb.var]
  ring_nf

/-- **Fama's first result** (O&R p. 590): a negative slope `a₁ < 0` forces
`Cov(D, rp) < −Var D ≤ 0`: the risk premium covaries negatively with expected
depreciation. -/
theorem fama_negative_slope (hvar : 0 < (pairProb π K).var (fwdPrem f e))
    (ha : (pairProb π K).cov (fwdPrem f e) (realDep e e')
      / (pairProb π K).var (fwdPrem f e) < 0) :
    (pairProb π K).cov (expDep K e e') (riskPrem K f e') < -(pairProb π K).var (expDep K e e')
      ∧ (pairProb π K).cov (expDep K e e') (riskPrem K f e') < 0 := by
  have hnum : (pairProb π K).cov (fwdPrem f e) (realDep e e') < 0 := by
    by_contra h
    push Not at h
    have := div_nonneg h hvar.le
    linarith
  rw [cov_fwdPrem_realDep, fwdPrem_eq, FinProb.cov_add_left,
    (pairProb π K).cov_comm (riskPrem K f e') (expDep K e e')] at hnum
  have hv := (pairProb π K).var_nonneg (expDep K e e')
  simp only [FinProb.var] at hv ⊢
  constructor <;> linarith

/-- **Fama's second result (115)** (O&R (114)–(115), p. 590): a slope `a₁ < ½` forces
`Var rp > Var D`: the risk premium is more variable than expected depreciation. -/
theorem fama_half_slope (hvar : 0 < (pairProb π K).var (fwdPrem f e))
    (ha : (pairProb π K).cov (fwdPrem f e) (realDep e e')
      / (pairProb π K).var (fwdPrem f e) < 1 / 2) :
    (pairProb π K).var (expDep K e e') < (pairProb π K).var (riskPrem K f e') := by
  rw [div_lt_iff₀ hvar] at ha
  rw [cov_fwdPrem_realDep, fwdPrem_eq, FinProb.cov_add_left,
    (pairProb π K).cov_comm (riskPrem K f e') (expDep K e e'), FinProb.var_add] at ha
  simp only [FinProb.var] at ha ⊢
  linarith

/-- Under the unbiasedness null `f_t = E_t e_{t+1}` (no risk premium) the population slope is
exactly `1` (O&R (110), p. 588: the null `a₁ = 1`). -/
theorem fama_slope_null (hnull : ∀ s, f s = condE K e' s)
    (hvar : 0 < (pairProb π K).var (expDep K e e')) :
    (pairProb π K).cov (fwdPrem f e) (realDep e e') / (pairProb π K).var (fwdPrem f e) = 1 := by
  have hrp : riskPrem K f e' = fun _ => 0 := by
    funext q; simp only [riskPrem, hnull, sub_self]
  rw [fama_slope, hrp]
  have h0 : (pairProb π K).var (fun _ : S × S => (0 : ℝ)) = 0 := by
    simp only [FinProb.var, FinProb.cov_const_left]
  have h1 : (pairProb π K).cov (expDep K e e') (fun _ => (0 : ℝ)) = 0 := by
    rw [FinProb.cov_comm, FinProb.cov_const_left]
  rw [h0, h1]
  field_simp
  ring

end Fama

/-- `E[Z²] = Var Z + (E Z)²` (O&R (111), p. 589). -/
theorem expect_sq_eq {T : Type} [Fintype T] (Ω : FinProb T) (Z : T → ℝ) :
    Ω.expect (fun t => Z t ^ 2) = Ω.var Z + Ω.expect Z ^ 2 := by
  simp only [FinProb.var, FinProb.cov, sq]; ring

/-- **The population OLS coefficients minimise mean squared error** (O&R (111), p. 589:
the probability limit of OLS is the population projection `a₁ = Cov(x, y)/Var(x)`,
`a₀ = E y − a₁ E x`). -/
theorem ols_minimises {T : Type} [Fintype T] (Ω : FinProb T) {X Y : T → ℝ}
    (hX : 0 < Ω.var X) (a₀ a₁ : ℝ) :
    Ω.expect (fun t => (Y t - (Ω.expect Y - Ω.cov X Y / Ω.var X * Ω.expect X)
        - Ω.cov X Y / Ω.var X * X t) ^ 2)
      ≤ Ω.expect (fun t => (Y t - a₀ - a₁ * X t) ^ 2) := by
  have hvar : ∀ b c : ℝ, Ω.var (fun t => Y t - b - c * X t)
      = Ω.var Y - 2 * c * Ω.cov X Y + c ^ 2 * Ω.var X := fun b c => by
    have e : (fun t => Y t - b - c * X t) = fun t => -b + (Y t + (-c) * X t) :=
      funext fun t => by ring
    rw [e, FinProb.var_const_add, FinProb.var_add]
    simp only [FinProb.var, FinProb.cov_mul_left, FinProb.cov_mul_right,
      Ω.cov_comm Y X]
    ring
  have hmean : ∀ b c : ℝ, Ω.expect (fun t => Y t - b - c * X t)
      = Ω.expect Y - b - c * Ω.expect X := fun b c => by
    rw [Ω.expect_sub, Ω.expect_sub, Ω.expect_const, Ω.expect_mul_left]
  rw [expect_sq_eq, expect_sq_eq, hvar, hvar, hmean, hmean]
  set a := Ω.cov X Y / Ω.var X
  have ha : Ω.cov X Y = a * Ω.var X := by simp only [a]; field_simp
  rw [ha]
  have : 0 ≤ Ω.var X * (a₁ - a) ^ 2 := mul_nonneg hX.le (sq_nonneg _)
  nlinarith [sq_nonneg (Ω.expect Y - a₀ - a₁ * Ω.expect X)]

/-! ## Exercise 6 (a): the consumption-based money price level -/

namespace Engel

variable {ι : Type} [Fintype ι]

/-- Money expenditure `Σ p_j C_j` (O&R Exercise 6, p. 601). -/
def expenditure (p c : ι → ℝ) : ℝ := ∑ j, p j * c j

/-- Bundles of positive goods reaching at least one unit of the index `Ω`, valued at
prices `p`; the money price level `P` is the least element (O&R Exercise 6, p. 601:
"the minimal expenditure of domestic money allowing `Ω = 1`"). -/
def costSet (Ω : (ι → ℝ) → ℝ) (p : ι → ℝ) : Set ℝ :=
  {e | ∃ c, (∀ j, 0 < c j) ∧ 1 ≤ Ω c ∧ e = expenditure p c}

/-- Scaling a bundle scales its cost (O&R Exercise 6). -/
theorem expenditure_smul (p c : ι → ℝ) (t : ℝ) :
    expenditure p (t • c) = t * expenditure p c := by
  simp only [expenditure, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Positive bundles at positive prices cost something (O&R Exercise 6). -/
theorem expenditure_pos [Nonempty ι] {p c : ι → ℝ} (hp : ∀ j, 0 < p j) (hc : ∀ j, 0 < c j) :
    0 < expenditure p c :=
  Finset.sum_pos (fun j _ => mul_pos (hp j) (hc j)) Finset.univ_nonempty

/-- **The budget binds at an optimum** when `Ω` is homogeneous of degree one
(O&R Exercise 6(a), p. 601). -/
theorem budget_binds [Nonempty ι] {Ω : (ι → ℝ) → ℝ} {p c : ι → ℝ} {X : ℝ}
    (hp : ∀ j, 0 < p j) (hc : ∀ j, 0 < c j) (hhom : ∀ t : ℝ, 0 < t → ∀ c, Ω (t • c) = t * Ω c)
    (hΩc : 0 < Ω c) (hfeas : expenditure p c ≤ X)
    (hopt : ∀ c', (∀ j, 0 < c' j) → expenditure p c' ≤ X → Ω c' ≤ Ω c) :
    expenditure p c = X := by
  by_contra hne
  have hlt : expenditure p c < X := lt_of_le_of_ne hfeas hne
  have he := expenditure_pos hp hc
  set t := X / expenditure p c
  have ht : 1 < t := (one_lt_div he).2 hlt
  have hfe : expenditure p (t • c) ≤ X := by
    rw [expenditure_smul]; simp only [t]; field_simp; exact le_rfl
  have := hopt (t • c) (fun j => by simp only [Pi.smul_apply, smul_eq_mul]; nlinarith [hc j])
    hfe
  rw [hhom t (by linarith)] at this
  nlinarith

/-- **The money price level is expenditure per unit of the index**: `P = X/Ω(c*)`
(O&R Exercise 6(a), p. 601). -/
theorem price_level_eq [Nonempty ι] {Ω : (ι → ℝ) → ℝ} {p c : ι → ℝ} {X P : ℝ}
    (hp : ∀ j, 0 < p j) (hc : ∀ j, 0 < c j) (hhom : ∀ t : ℝ, 0 < t → ∀ c, Ω (t • c) = t * Ω c)
    (hΩc : 0 < Ω c) (hfeas : expenditure p c ≤ X)
    (hopt : ∀ c', (∀ j, 0 < c' j) → expenditure p c' ≤ X → Ω c' ≤ Ω c)
    (hP : IsLeast (costSet Ω p) P) : P = X / Ω c := by
  have hb := budget_binds hp hc hhom hΩc hfeas hopt
  apply le_antisymm
  · apply hP.2
    refine ⟨(1 / Ω c) • c, fun j => ?_, ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos (one_div_pos.2 hΩc) (hc j)
    · rw [hhom _ (one_div_pos.2 hΩc)]; field_simp; exact le_rfl
    · rw [expenditure_smul, hb]; ring
  · obtain ⟨c', hc', h1, hPe⟩ := hP.1
    have he := expenditure_pos hp hc'
    set t := X / expenditure p c'
    have hX : 0 < X := hb ▸ expenditure_pos hp hc
    have htpos : 0 < t := div_pos hX he
    have hfe : expenditure p (t • c') ≤ X := by
      rw [expenditure_smul]; simp only [t]; field_simp; exact le_rfl
    have hle := hopt (t • c') (fun j => by
      simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos htpos (hc' j)) hfe
    rw [hhom t htpos] at hle
    have : t ≤ Ω c := by nlinarith
    rw [hPe, div_le_iff₀ hΩc]
    simp only [t] at this
    rwa [div_le_iff₀ he, mul_comm] at this

/-- Homogeneity of the minimal-expenditure price level in prices (O&R Exercise 6(f),
p. 602): if `P` is the least cost at prices `q`, then `t P` is the least cost at `t q`. -/
theorem least_cost_smul {Ω : (ι → ℝ) → ℝ} {q : ι → ℝ} {P t : ℝ} (ht : 0 < t)
    (hP : IsLeast (costSet Ω q) P) : IsLeast (costSet Ω (t • q)) (t * P) := by
  have hexp : ∀ c, expenditure (t • q) c = t * expenditure q c := fun c => by
    simp only [expenditure, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  constructor
  · obtain ⟨c, hc, h1, he⟩ := hP.1
    exact ⟨c, hc, h1, by rw [hexp, he]⟩
  · rintro e ⟨c, hc, h1, he⟩
    rw [he, hexp]
    exact mul_le_mul_of_nonneg_left (hP.2 ⟨c, hc, h1, rfl⟩) ht.le

/-- **The price level scales with money** (O&R Exercise 6(f), p. 602): if goods prices are
`M • q` then the minimal-expenditure price level is `M` times the one at prices `q`. -/
theorem price_level_scales {Ω : (ι → ℝ) → ℝ} {q : ι → ℝ} {M P φ : ℝ} (hM : 0 < M)
    (hP : IsLeast (costSet Ω (M • q)) P) (hφ : IsLeast (costSet Ω q) φ) : P = M * φ :=
  hP.unique (least_cost_smul hM hφ)

variable [DecidableEq ι]

/-- **Euler's theorem for a homogeneous index**: `Ω′(c)·c = Ω(c)` (O&R Exercise 6(a),
p. 601). -/
theorem euler_homogeneous {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {Ω : V → ℝ}
    {Ω' : V →L[ℝ] ℝ} {c : V} (hhom : ∀ t : ℝ, 0 < t → ∀ c, Ω (t • c) = t * Ω c)
    (hd : HasFDerivAt Ω Ω' c) :
    Ω' c = Ω c := by
  have hf : HasDerivAt (fun t : ℝ => t • c) c 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const c
  have hd1 : HasFDerivAt Ω Ω' ((fun t : ℝ => t • c) 1) := by simpa using hd
  have h1 : HasDerivAt (fun t : ℝ => Ω (t • c)) (Ω' c) 1 := hd1.comp_hasDerivAt 1 hf
  have h2 : HasDerivAt (fun t : ℝ => t * Ω c) (Ω c) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (Ω c)
  have heq : (fun t : ℝ => Ω (t • c)) =ᶠ[𝓝 1] fun t => t * Ω c := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hhom t ht c
  exact h1.unique (h2.congr_of_eventuallyEq heq)

/-- **Exercise 6(a)** (O&R p. 601): at an interior optimum of a homogeneous-of-degree-one
index `Ω` under a money budget, `∂Ω/∂C_j = p_j/P` for every good, where `P` is the minimal
money expenditure giving `Ω = 1`. -/
theorem marginal_index_eq_relative_price [Nonempty ι] {Ω : (ι → ℝ) → ℝ}
    {Ω' : (ι → ℝ) →L[ℝ] ℝ} {p c : ι → ℝ} {X P : ℝ} (hp : ∀ j, 0 < p j) (hc : ∀ j, 0 < c j)
    (hhom : ∀ t : ℝ, 0 < t → ∀ c, Ω (t • c) = t * Ω c) (hΩc : 0 < Ω c)
    (hfeas : expenditure p c ≤ X)
    (hopt : ∀ c', (∀ j, 0 < c' j) → expenditure p c' ≤ X → Ω c' ≤ Ω c)
    (hd : HasFDerivAt Ω Ω' c) (hP : IsLeast (costSet Ω p) P) (j : ι) :
    Ω' (Pi.single j 1) = p j / P := by
  have hb := budget_binds hp hc hhom hΩc hfeas hopt
  have hPeq := price_level_eq hp hc hhom hΩc hfeas hopt hP
  have hX : 0 < X := hb ▸ expenditure_pos hp hc
  -- Step 1: equal marginal utility per dollar across goods.
  have hratio : ∀ k l, Ω' (Pi.single k 1) / p k = Ω' (Pi.single l 1) / p l := by
    intro k l
    set d : ι → ℝ := (1 / p k) • Pi.single k 1 - (1 / p l) • Pi.single l 1
    have hed : expenditure p d = 0 := by
      simp only [d, expenditure, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
        mul_sub, Finset.sum_sub_distrib]
      simp [mul_inv_cancel₀ (hp k).ne', mul_inv_cancel₀ (hp l).ne']
    have hf : HasDerivAt (fun t : ℝ => c + t • d) d 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add c
    have hd0 : HasFDerivAt Ω Ω' ((fun t : ℝ => c + t • d) 0) := by simpa using hd
    have hg := hd0.comp_hasDerivAt 0 hf
    have hmax : IsLocalMax (Ω ∘ fun t : ℝ => c + t • d) 0 := by
      have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < c i + t * d i := by
        refine Filter.eventually_all.2 fun i => ?_
        have hcont : Continuous fun t : ℝ => c i + t * d i := by fun_prop
        exact continuousAt_const.eventually_lt hcont.continuousAt (by simpa using hc i)
      filter_upwards [hev] with t ht
      simp only [Function.comp, zero_smul, add_zero]
      apply hopt
      · intro i; simpa using ht i
      · have : expenditure p (c + t • d) = expenditure p c + t * expenditure p d := by
          simp only [expenditure, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
            Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [this, hed, mul_zero, add_zero]; exact hfeas
    have h0 := hmax.hasDerivAt_eq_zero hg
    simp only [d, map_sub, map_smul, smul_eq_mul] at h0
    have := hp k; have := hp l
    field_simp at h0 ⊢
    linarith
  -- Step 2: Euler's theorem and the budget.
  obtain ⟨j₀⟩ := (inferInstance : Nonempty ι)
  set lam := Ω' (Pi.single j₀ 1) / p j₀
  have hlam : ∀ k, Ω' (Pi.single k 1) = lam * p k := fun k => by
    rw [show lam = Ω' (Pi.single k 1) / p k from (hratio k j₀).symm,
      div_mul_cancel₀ _ (hp k).ne']
  have heul := euler_homogeneous hhom hd
  have hsum : Ω' c = lam * expenditure p c := by
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [map_sum]
    simp only [expenditure, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show Pi.single k (c k) = c k • Pi.single k (1 : ℝ) by
      ext i; simp [Pi.single_apply], map_smul, smul_eq_mul, hlam k]
    ring
  rw [heul, hb] at hsum
  rw [hlam j, hPeq]
  have : lam = Ω c / X := by field_simp; linarith
  rw [this]
  field_simp

end Engel

/-! ## Exercise 6 (b)–(d): multi-good forward Euler equations -/

/-- **Exercise 6(d) ⟺ 6(b)** (O&R Exercise 6, p. 601): given 6(a) at both dates
(`u_j = u′ ∂C/∂C_j = u′ p_j/P`), the forward-position Euler equation priced in any single
good `j` is equivalent to the one priced in the consumption-based price level. -/
theorem ex6d_iff_ex6b (Ω : FinProb S) {F uC pj P : ℝ} {E' uC' pj' P' : S → ℝ} (huC : 0 < uC)
    (hpj : 0 < pj) (hP : 0 < P) (hpj' : ∀ s, 0 < pj' s) (hP' : ∀ s, 0 < P' s) :
    Ω.expect (fun s => (F - E' s) / pj' s * ((uC' s * (pj' s / P' s)) / (uC * (pj / P)))) = 0
      ↔ Ω.expect (fun s => (F - E' s) / P' s * (uC' s / uC)) = 0 := by
  have e : (fun s => (F - E' s) / pj' s * ((uC' s * (pj' s / P' s)) / (uC * (pj / P))))
      = fun s => P / pj * ((F - E' s) / P' s * (uC' s / uC)) := by
    funext s
    have := hpj' s; have := hP' s
    field_simp
  rw [e, Ω.expect_mul_left]
  have : P / pj ≠ 0 := (div_pos hP hpj).ne'
  constructor
  · intro h; exact (mul_eq_zero.1 h).resolve_left this
  · intro h; rw [h, mul_zero]

/-- **Exercise 6(c)** (O&R p. 601): under PPP `P_{t+1} = ℰ_{t+1} P*_{t+1}`, the dollar
forward Euler equation is equivalent to the yen one,
`E_t[((1/F) − (1/ℰ_{t+1}))/P*_{t+1} · u′(C_{t+1})/u′(C_t)] = 0`. -/
theorem ex6c_iff (Ω : FinProb S) {F : ℝ} {E' P' Ps' w : S → ℝ} (hF : 0 < F)
    (hE' : ∀ s, 0 < E' s) (hPs : ∀ s, 0 < Ps' s) (hppp : ∀ s, P' s = E' s * Ps' s) :
    Ω.expect (fun s => (F - E' s) / P' s * w s) = 0 ↔
      Ω.expect (fun s => (1 / F - 1 / E' s) / Ps' s * w s) = 0 := by
  have e : (fun s => (F - E' s) / P' s * w s)
      = fun s => (-F) * ((1 / F - 1 / E' s) / Ps' s * w s) := by
    funext s
    rw [hppp s]
    have := hE' s; have := hPs s
    field_simp; ring
  rw [e, Ω.expect_mul_left]
  have : -F ≠ 0 := neg_ne_zero.2 hF.ne'
  constructor
  · intro h; exact (mul_eq_zero.1 h).resolve_left this
  · intro h; rw [h, mul_zero]

/-- **No Siegel paradox in real terms** (O&R Exercise 6(c), p. 601; p. 587–588): with
risk-neutral consumers (`u″ = 0`, so `u′(C_{t+1})/u′(C_t) ≡ 1`), the dollar condition (107)
and the yen condition (108) hold TOGETHER, and there is always a forward rate satisfying both,
`F = E[ℰ/P]/E[1/P]`, however random the exchange rate is. -/
theorem no_real_siegel (Ω : FinProb S) {E' P' Ps' : S → ℝ} (hE' : ∀ s, 0 < E' s)
    (hPs : ∀ s, 0 < Ps' s) (hppp : ∀ s, P' s = E' s * Ps' s) :
    ∃ F, 0 < F ∧ Ω.expect (fun s => (F - E' s) / P' s) = 0 ∧
      Ω.expect (fun s => (1 / F - 1 / E' s) / Ps' s) = 0 := by
  have hP' : ∀ s, 0 < P' s := fun s => by rw [hppp s]; exact mul_pos (hE' s) (hPs s)
  set F := Ω.expect (fun s => E' s / P' s) / Ω.expect (fun s => 1 / P' s)
  have hF : 0 < F := div_pos (Ω.expect_pos fun s => div_pos (hE' s) (hP' s))
    (Ω.expect_pos fun s => one_div_pos.2 (hP' s))
  have h107 : Ω.expect (fun s => (F - E' s) / P' s) = 0 := (eq107_iff_ratio Ω hP').2 rfl
  refine ⟨F, hF, h107, ?_⟩
  have := (ex6c_iff Ω (w := fun _ => 1) hF hE' hPs hppp).1 (by simpa using h107)
  simpa using this

/-! ## Exercise 6 (e)–(f): two-good cash-in-advance model -/

/-- **Cobb–Douglas spending shares** (O&R Exercise 6(e), p. 602): maximising
`γ log C_X + (1−γ) log C_Y` (the log of `C_X^γ C_Y^{1−γ}`) subject to
`p_X C_X + p_Y C_Y = Z` gives `p_X C_X = γ Z`, uniquely. -/
theorem cobb_douglas_share {γ pX pY Z cX : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hpX : 0 < pX)
    (hpY : 0 < pY) (hZ : 0 < Z) (hcX : 0 < cX) (hcX' : pX * cX < Z) :
    γ * Real.log cX + (1 - γ) * Real.log ((Z - pX * cX) / pY)
        ≤ γ * Real.log (γ * Z / pX) + (1 - γ) * Real.log ((1 - γ) * Z / pY) ∧
      (γ * Real.log cX + (1 - γ) * Real.log ((Z - pX * cX) / pY)
          = γ * Real.log (γ * Z / pX) + (1 - γ) * Real.log ((1 - γ) * Z / pY)
        ↔ cX = γ * Z / pX) := by
  have hs : 0 < γ * Z / pX := by positivity
  have hr : 0 < Z - pX * cX := by linarith
  have h1γ : 0 < 1 - γ := by linarith
  have hr' : 0 < (1 - γ) * Z := by positivity
  set a := cX / (γ * Z / pX)
  set b := (Z - pX * cX) / ((1 - γ) * Z)
  have ha : 0 < a := div_pos hcX hs
  have hb : 0 < b := div_pos hr hr'
  have hsum : γ * (a - 1) + (1 - γ) * (b - 1) = 0 := by
    simp only [a, b]; field_simp; ring
  have hla : Real.log cX = Real.log a + Real.log (γ * Z / pX) := by
    rw [← Real.log_mul ha.ne' hs.ne']; congr 1; simp only [a]; field_simp
  have hlb : Real.log ((Z - pX * cX) / pY) = Real.log b + Real.log ((1 - γ) * Z / pY) := by
    rw [← Real.log_mul hb.ne' (by positivity)]; congr 1; simp only [b]; field_simp
  rw [hla, hlb]
  have ta := Real.log_le_sub_one_of_pos ha
  have tb := Real.log_le_sub_one_of_pos hb
  constructor
  · nlinarith
  · constructor
    · intro h
      have h0 : γ * (Real.log a - (a - 1)) + (1 - γ) * (Real.log b - (b - 1)) = 0 := by
        linarith
      have hA : Real.log a - (a - 1) = 0 := by nlinarith
      have ha1 : a = 1 := by
        by_contra hne
        have := Real.log_lt_sub_one_of_pos ha hne
        linarith
      simp only [a] at ha1
      field_simp at ha1
      rw [← ha1]; field_simp
    · intro h
      have ha1 : a = 1 := by simp only [a, h]; field_simp
      have hb1 : b = 1 := by
        rw [ha1, sub_self, mul_zero, zero_add] at hsum
        rcases mul_eq_zero.1 hsum with h0 | h0
        · linarith
        · linarith
      rw [ha1, hb1, Real.log_one]
      ring

/-- **The two-good CIA spot rate** (O&R Exercise 6(e), p. 602): with pooled consumption
`(X/2, Y/2)` per country, Cobb–Douglas spending shares, cash-in-advance `p_X X = M`,
`p*_Y Y = M*`, and the law of one price `p_Y = ℰ p*_Y`, `ℰ = ((1−γ)/γ) M/M*`. -/
theorem ex6e_spot_rate {γ pX pY psY X Y Z M Ms E : ℝ} (hγ0 : 0 < γ)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (hpsY : 0 < psY)
    (hshareX : pX * (X / 2) = γ * Z) (hshareY : pY * (Y / 2) = (1 - γ) * Z)
    (hcia : M = pX * X) (hcias : Ms = psY * Y) (hloop : pY = E * psY) :
    E = (1 - γ) / γ * (M / Ms) := by
  have hpX : pX = 2 * γ * Z / X := by field_simp; linarith
  have hpY : pY = 2 * (1 - γ) * Z / Y := by field_simp; linarith
  have hE : E = pY / psY := by rw [hloop]; field_simp
  rw [hE, hpY, hcia, hcias, hpX]
  field_simp

/-- **The Cobb–Douglas marginal utility of good X** (O&R Exercise 6(e)): for
`C = C_X^γ C_Y^{1−γ}`, `∂C/∂C_X = γ C/C_X`. -/
theorem cobb_douglas_partial {γ cX cY : ℝ} (hcX : 0 < cX) :
    HasDerivAt (fun z => z ^ γ * cY ^ (1 - γ)) (γ * (cX ^ γ * cY ^ (1 - γ)) / cX) cX := by
  have h := (Real.hasDerivAt_rpow_const (p := γ) (Or.inl hcX.ne')).mul_const (cY ^ (1 - γ))
  convert h using 1
  rw [Real.rpow_sub_one hcX.ne']
  field_simp

/-- The product of two independent finite probability spaces (O&R Exercise 6(e), p. 602:
"money and output shocks are independently distributed"). -/
def prodProb {A B : Type} [Fintype A] [Fintype B] (Ωa : FinProb A) (Ωb : FinProb B) :
    FinProb (A × B) :=
  ⟨fun q => Ωa.prob q.1 * Ωb.prob q.2, fun q => mul_nonneg (Ωa.prob_nonneg _)
    (Ωb.prob_nonneg _), by
      rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, Ωa.prob_sum, Ωb.prob_sum, one_mul]⟩

/-- Under independence, the expectation of a product of a money-state function and an
output-state function factorises (O&R Exercise 6(e), p. 602). -/
theorem expect_prod_mul {A B : Type} [Fintype A] [Fintype B] (Ωa : FinProb A)
    (Ωb : FinProb B) (h : A → ℝ) (g : B → ℝ) :
    (prodProb Ωa Ωb).expect (fun q => h q.1 * g q.2) = Ωa.expect h * Ωb.expect g := by
  simp only [FinProb.expect, prodProb, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- **The two-good CIA forward rate** (O&R Exercise 6(e), p. 602): if money states `a` and
output states `b` are independent, `p_{X,t+1} = M_{t+1}/X_{t+1}`, `ℰ_{t+1} = κ M/M*`
(`κ = (1−γ)/γ`), and the good-`X` forward Euler equation 6(d) holds with a positive marginal
utility of good `X` that depends only on outputs (pooled consumption), then
`F = κ E[1/M*_{t+1}]/E[1/M_{t+1}]`, whatever the degree of risk aversion. -/
theorem ex6e_forward_rate {A B : Type} [Fintype A] [Fintype B] (Ωa : FinProb A)
    (Ωb : FinProb B) {F κ : ℝ} {M' Ms' : A → ℝ} {X' mu : B → ℝ} (hM' : ∀ a, 0 < M' a)
    (hX' : ∀ b, 0 < X' b) (hmu : ∀ b, 0 < mu b)
    (h6d : (prodProb Ωa Ωb).expect
      (fun q => (F - κ * M' q.1 / Ms' q.1) / (M' q.1 / X' q.2) * mu q.2) = 0) :
    F = κ * Ωa.expect (fun a => 1 / Ms' a) / Ωa.expect (fun a => 1 / M' a) := by
  have e : (fun q : A × B => (F - κ * M' q.1 / Ms' q.1) / (M' q.1 / X' q.2) * mu q.2)
      = fun q => (F * (1 / M' q.1) - κ * (1 / Ms' q.1)) * (X' q.2 * mu q.2) := by
    funext q
    have := hM' q.1; have := hX' q.2
    field_simp
  have hf := expect_prod_mul Ωa Ωb (fun a => F * (1 / M' a) - κ * (1 / Ms' a))
    (fun b => X' b * mu b)
  rw [e, hf] at h6d
  have hpos : 0 < Ωb.expect (fun b => X' b * mu b) :=
    Ωb.expect_pos fun b => mul_pos (hX' b) (hmu b)
  have h0 := (mul_eq_zero.1 h6d).resolve_right hpos.ne'
  rw [Ωa.expect_sub, Ωa.expect_mul_left, Ωa.expect_mul_left] at h0
  have hm : 0 < Ωa.expect (fun a => 1 / M' a) := Ωa.expect_pos fun a => one_div_pos.2 (hM' a)
  field_simp
  linarith

/-- **Exercise 6(f)**: the "risk-neutral" forward equation (107) holds in the two-good CIA
model (O&R p. 602). If the date-`t+1` price level is money times a positive function of
outputs, `P_{t+1} = M_{t+1} φ(X, Y)` (homogeneity of the price index, `least_cost_smul`;
`φ = 1/X` for `p_X`), then `E[ℰ/P]/E[1/P] = κ E[1/M*]/E[1/M]`, which is the forward rate of
6(e); the yen version `E[(1/ℰ)/P*]/E[1/P*]` equals its reciprocal. -/
theorem ex6f {A B : Type} [Fintype A] [Fintype B] (Ωa : FinProb A) (Ωb : FinProb B) {κ : ℝ}
    (hκ : 0 < κ) {M' Ms' : A → ℝ} {φ : B → ℝ} (hM' : ∀ a, 0 < M' a) (hMs' : ∀ a, 0 < Ms' a)
    (hφ : ∀ b, 0 < φ b) :
    (prodProb Ωa Ωb).expect (fun q => (κ * M' q.1 / Ms' q.1) / (M' q.1 * φ q.2))
        / (prodProb Ωa Ωb).expect (fun q => 1 / (M' q.1 * φ q.2))
      = κ * Ωa.expect (fun a => 1 / Ms' a) / Ωa.expect (fun a => 1 / M' a) ∧
    (prodProb Ωa Ωb).expect (fun q => (1 / (κ * M' q.1 / Ms' q.1))
          / ((M' q.1 * φ q.2) / (κ * M' q.1 / Ms' q.1)))
        / (prodProb Ωa Ωb).expect (fun q => 1 / ((M' q.1 * φ q.2) / (κ * M' q.1 / Ms' q.1)))
      = Ωa.expect (fun a => 1 / M' a) / (κ * Ωa.expect (fun a => 1 / Ms' a)) := by
  have e1 : (fun q : A × B => (κ * M' q.1 / Ms' q.1) / (M' q.1 * φ q.2))
      = fun q => (κ * (1 / Ms' q.1)) * (1 / φ q.2) := by
    funext q; have := hM' q.1; have := hMs' q.1; have := hφ q.2; field_simp
  have e2 : (fun q : A × B => 1 / (M' q.1 * φ q.2)) = fun q => (1 / M' q.1) * (1 / φ q.2) := by
    funext q; have := hM' q.1; have := hφ q.2; field_simp
  have e3 : (fun q : A × B => (1 / (κ * M' q.1 / Ms' q.1))
      / ((M' q.1 * φ q.2) / (κ * M' q.1 / Ms' q.1)))
      = fun q => (1 / M' q.1) * (1 / φ q.2) := by
    funext q; have := hM' q.1; have := hMs' q.1; have := hφ q.2; field_simp
  have e4 : (fun q : A × B => 1 / ((M' q.1 * φ q.2) / (κ * M' q.1 / Ms' q.1)))
      = fun q => (κ * (1 / Ms' q.1)) * (1 / φ q.2) := by
    funext q; have := hM' q.1; have := hMs' q.1; have := hφ q.2; field_simp
  have hb : 0 < Ωb.expect (fun b => 1 / φ b) := Ωb.expect_pos fun b => one_div_pos.2 (hφ b)
  have hm : 0 < Ωa.expect (fun a => 1 / M' a) := Ωa.expect_pos fun a => one_div_pos.2 (hM' a)
  have hms : 0 < Ωa.expect (fun a => 1 / Ms' a) :=
    Ωa.expect_pos fun a => one_div_pos.2 (hMs' a)
  have f1 := expect_prod_mul Ωa Ωb (fun a => κ * (1 / Ms' a)) (fun b => 1 / φ b)
  have f2 := expect_prod_mul Ωa Ωb (fun a => 1 / M' a) (fun b => 1 / φ b)
  rw [e1, e2, e3, e4, f1, f2, Ωa.expect_mul_left]
  constructor <;> field_simp

/-! ## Exercises 7 and 8: sampling, averaging and overlapping forecast errors -/

/-- Homoskedastic white noise `ε₀, …, ε_{n−1}`: mean zero, variance `σ²`, uncorrelated
(O&R Exercise 7, p. 602: "a serially uncorrelated white noise disturbance"). -/
structure WhiteNoise (Ω : FinProb S) (n : ℕ) where
  eps : Fin n → S → ℝ
  sigma2 : ℝ
  mean_zero : ∀ i, Ω.expect (eps i) = 0
  second : ∀ i j, Ω.expect (fun s => eps i s * eps j s) = if i = j then sigma2 else 0

/-- A linear combination `Σ aᵢ εᵢ` of the shocks (O&R Exercises 7–8). -/
def comb {Ω : FinProb S} {n : ℕ} (W : WhiteNoise Ω n) (a : Fin n → ℝ) : S → ℝ :=
  fun s => ∑ i, a i * W.eps i s

/-- Expectation of a finite sum (O&R Exercises 7–8). -/
theorem expect_finsum (Ω : FinProb S) {n : ℕ} (f : Fin n → S → ℝ) :
    Ω.expect (fun s => ∑ i, f i s) = ∑ i, Ω.expect (f i) := by
  simp only [FinProb.expect, Finset.mul_sum]
  exact Finset.sum_comm

/-- Linear combinations of white noise have mean zero (O&R Exercises 7–8). -/
theorem expect_comb {Ω : FinProb S} {n : ℕ} (W : WhiteNoise Ω n) (a : Fin n → ℝ) :
    Ω.expect (comb W a) = 0 := by
  unfold comb
  rw [expect_finsum]
  exact Finset.sum_eq_zero fun i _ => by rw [Ω.expect_mul_left, W.mean_zero, mul_zero]

/-- **Covariances of linear combinations of white noise**: `Cov(Σ aᵢεᵢ, Σ bᵢεᵢ) =
σ² Σ aᵢbᵢ` (O&R Exercises 7–8, "second-moment algebra"). -/
theorem cov_comb {Ω : FinProb S} {n : ℕ} (W : WhiteNoise Ω n) (a b : Fin n → ℝ) :
    Ω.cov (comb W a) (comb W b) = W.sigma2 * ∑ i, a i * b i := by
  have hpt : (fun s => comb W a s * comb W b s)
      = fun s => ∑ i, ∑ j, a i * b j * (W.eps i s * W.eps j s) := by
    funext s
    simp only [comb, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [FinProb.cov, expect_comb, mul_zero, sub_zero]
  rw [hpt, expect_finsum]
  simp only [expect_finsum, Ω.expect_mul_left, W.second, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The two-week average `ℰ̃_t = ½(ℰ_t + ℰ_{t−1})` of a random walk: sampled every other week,
`ℰ̃_{t+2} − ℰ̃_t = ½(ε_{t+2} + 2ε_{t+1} + ε_t)` (O&R Exercise 7(a), p. 602). -/
theorem timeavg_increment {E₀ ε₀ ε₁ ε₂ Em : ℝ} :
    (1 / 2 * ((E₀ + ε₁ + ε₂) + (E₀ + ε₁))) - 1 / 2 * (E₀ + Em)
      = 1 / 2 * (ε₂ + 2 * ε₁ + ε₀) ↔ Em = E₀ - ε₀ := by
  constructor <;> intro h <;> linarith

/-- **Exercise 7(a): the sampled average series is autocorrelated with coefficient 1/6**
(O&R p. 602): with shocks `ε_t, …, ε_{t+4}`, the consecutive biweekly changes
`½(ε_{t+2}+2ε_{t+1}+ε_t)` and `½(ε_{t+4}+2ε_{t+3}+ε_{t+2})` have equal variance `(3/2)σ²` and
covariance `σ²/4`, so their correlation is `1/6 ≠ 0`: not a random walk. -/
theorem ex7a_autocorrelation {Ω : FinProb S} (W : WhiteNoise Ω 5) (hσ : 0 < W.sigma2) :
    Ω.var (comb W ![1 / 2, 1, 1 / 2, 0, 0]) = 3 / 2 * W.sigma2 ∧
      Ω.var (comb W ![0, 0, 1 / 2, 1, 1 / 2]) = 3 / 2 * W.sigma2 ∧
      Ω.cov (comb W ![1 / 2, 1, 1 / 2, 0, 0]) (comb W ![0, 0, 1 / 2, 1, 1 / 2])
        = W.sigma2 / 4 ∧
      Ω.cov (comb W ![1 / 2, 1, 1 / 2, 0, 0]) (comb W ![0, 0, 1 / 2, 1, 1 / 2])
        / Ω.var (comb W ![1 / 2, 1, 1 / 2, 0, 0]) = 1 / 6 := by
  have h1 : Ω.var (comb W ![1 / 2, 1, 1 / 2, 0, 0]) = 3 / 2 * W.sigma2 := by
    simp only [FinProb.var, cov_comb, Fin.sum_univ_five]; simp; ring
  have h2 : Ω.var (comb W ![0, 0, 1 / 2, 1, 1 / 2]) = 3 / 2 * W.sigma2 := by
    simp only [FinProb.var, cov_comb, Fin.sum_univ_five]; simp; ring
  have h3 : Ω.cov (comb W ![1 / 2, 1, 1 / 2, 0, 0]) (comb W ![0, 0, 1 / 2, 1, 1 / 2])
      = W.sigma2 / 4 := by
    simp only [cov_comb, Fin.sum_univ_five]; simp; ring
  refine ⟨h1, h2, h3, ?_⟩
  rw [h1, h3]
  field_simp
  ring

/-- **Exercise 7(b): point sampling preserves the random walk** (O&R p. 602): the biweekly
changes `ε_{t+1}+ε_{t+2}` and `ε_{t+3}+ε_{t+4}` are uncorrelated. -/
theorem ex7b_point_sampling {Ω : FinProb S} (W : WhiteNoise Ω 5) :
    Ω.cov (comb W ![0, 1, 1, 0, 0]) (comb W ![0, 0, 0, 1, 1]) = 0 := by
  simp only [cov_comb, Fin.sum_univ_five]; simp

/-- **Exercise 7(a), conditional form** (O&R p. 602): on the event tree, if
`ℰ_{t+1} = ℰ_t + ε_{t+1}` with `E_t ε_{t+1} = 0`, then for the average
`ℰ̃_t = ℰ_t − ε_t/2 = ½(ℰ_t + ℰ_{t−1})`, `E_t ℰ̃_{t+2} = ℰ̃_t + ε_t/2 ≠ ℰ̃_t` (unless
`ε_t = 0`). -/
theorem ex7a_conditional (K : Kernel S) {g : S → ℝ} (hmds : ∀ s, ∑ s', K.trans s s' * g s' = 0)
    {Ex : Hist S → ℝ} (hrw : ∀ h s', Ex (next h s') = Ex h + g s') (h : Hist S) :
    iterStep K.trans 2 (fun h' => Ex h' - g h'.1 / 2) h = (Ex h - g h.1 / 2) + g h.1 / 2 := by
  have hn : ∀ (h : Hist S) s', (next h s').1 = s' := fun _ _ => rfl
  have h1 : ∀ h', oneStep K.trans (fun h'' => Ex h'' - g h''.1 / 2) h' = Ex h' := fun h' => by
    simp only [oneStep, hrw, hn]
    have e : ∀ s', K.trans h'.1 s' * (Ex h' + g s' - g s' / 2)
        = Ex h' * K.trans h'.1 s' + 1 / 2 * (K.trans h'.1 s' * g s') := fun s' => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, K.trans_sum, hmds]
    ring
  have h2 : oneStep K.trans Ex h = Ex h := by
    simp only [oneStep, hrw]
    have e : ∀ s', K.trans h.1 s' * (Ex h + g s') = Ex h * K.trans h.1 s' + K.trans h.1 s' * g s' :=
      fun s' => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, K.trans_sum, hmds]
    ring
  change oneStep K.trans (oneStep K.trans (fun h' => Ex h' - g h'.1 / 2)) h = _
  rw [show oneStep K.trans (fun h' => Ex h' - g h'.1 / 2) = Ex from funext h1, h2]
  ring

/-- **Exercise 7(b), conditional form** (O&R p. 602): point-sampled random walk,
`E_t ℰ_{t+2} = ℰ_t`. -/
theorem ex7b_conditional (K : Kernel S) {g : S → ℝ} (hmds : ∀ s, ∑ s', K.trans s s' * g s' = 0)
    {Ex : Hist S → ℝ} (hrw : ∀ h s', Ex (next h s') = Ex h + g s') (h : Hist S) :
    iterStep K.trans 2 Ex h = Ex h := by
  have h1 : ∀ h', oneStep K.trans Ex h' = Ex h' := fun h' => by
    simp only [oneStep, hrw]
    have e : ∀ s', K.trans h'.1 s' * (Ex h' + g s')
        = Ex h' * K.trans h'.1 s' + K.trans h'.1 s' * g s' := fun s' => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, K.trans_sum, hmds]
    ring
  change oneStep K.trans (oneStep K.trans Ex) h = _
  rw [show oneStep K.trans Ex = Ex from funext h1, h1]

/-- **Exercise 8(a): overlapping forecast errors are serially correlated** (O&R p. 603):
with a random walk, the two-week forecast errors `u_t = −(ε_{t+1}+ε_{t+2})` and
`u_{t+1} = −(ε_{t+2}+ε_{t+3})` have variance `2σ²` and covariance `σ²`, correlation `1/2`. -/
theorem ex8a_overlap {Ω : FinProb S} (W : WhiteNoise Ω 4) (hσ : 0 < W.sigma2) :
    Ω.var (comb W ![0, -1, -1, 0]) = 2 * W.sigma2 ∧
      Ω.cov (comb W ![0, -1, -1, 0]) (comb W ![0, 0, -1, -1]) = W.sigma2 ∧
      Ω.cov (comb W ![0, -1, -1, 0]) (comb W ![0, 0, -1, -1])
        / Ω.var (comb W ![0, -1, -1, 0]) = 1 / 2 := by
  have h1 : Ω.var (comb W ![0, -1, -1, 0]) = 2 * W.sigma2 := by
    simp only [FinProb.var, cov_comb, Fin.sum_univ_four]; simp; ring
  have h2 : Ω.cov (comb W ![0, -1, -1, 0]) (comb W ![0, 0, -1, -1]) = W.sigma2 := by
    simp only [cov_comb, Fin.sum_univ_four]; simp
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  field_simp

/-- The two-period forecast error `u = f_{t,2} − e_{t+2} = E_t e_{t+2} − e_{t+2}`, evaluated
at the date-`t+2` node (O&R Exercise 8, p. 603). -/
def forecastErr (K : Kernel S) (e : Hist S → ℝ) : Hist S → ℝ :=
  fun h₂ => iterStep K.trans 2 e (anc^[2] h₂) - e h₂

/-- The forecast error is unpredictable two periods ahead: `E_t u_t = 0` (O&R Exercise 8,
p. 603, "no risk premium"). -/
theorem forecastErr_unbiased (K : Kernel S) (e : Hist S → ℝ) (h : Hist S) :
    iterStep K.trans 2 (forecastErr K e) h = 0 := by
  unfold forecastErr
  rw [iterStep_sub_fun]
  have := iterStep_pull K.trans 2 (iterStep K.trans 2 e) (fun _ => 1) h
  simp only [mul_one, iterStep_const K.trans_sum] at this
  rw [this, sub_self]

/-- **Exercise 8(b): every-other-observation forecast errors are uncorrelated, for ANY
exchange-rate process** (O&R p. 603): `E_t[u_t u_{t+2}] = 0` and `E_t u_{t+2} = 0`,
because `u_t` is known at `t+2` and `u_{t+2}` is unpredictable at `t+2` (tower property). -/
theorem ex8b_nonoverlap (K : Kernel S) (e : Hist S → ℝ) (h : Hist S) :
    iterStep K.trans 4 (fun h₄ => forecastErr K e (anc^[2] h₄) * forecastErr K e h₄) h = 0 ∧
      iterStep K.trans 4 (forecastErr K e) h = 0 := by
  have inner : ∀ h₂, iterStep K.trans 2
      (fun h₄ => forecastErr K e (anc^[2] h₄) * forecastErr K e h₄) h₂ = 0 := fun h₂ => by
    rw [iterStep_pull, forecastErr_unbiased, mul_zero]
  constructor
  · rw [show (4 : ℕ) = 2 + 2 from rfl, iterStep_add, funext inner]
    exact iterStep_const K.trans_sum 2 0 h
  · rw [show (4 : ℕ) = 2 + 2 from rfl, iterStep_add,
      funext (forecastErr_unbiased K e)]
    exact iterStep_const K.trans_sum 2 0 h

/-! ## Sterilised and forward intervention (§8.7.6.1, Appendix 8B) -/

/-- A central-bank balance sheet in domestic currency (O&R Appendix 8B, p. 598): gold (at
price `P^g`), foreign-currency bonds and money (at the exchange rate `ℰ`), domestic bonds;
liabilities are the monetary base (currency plus reserves) and net worth. -/
structure CBBalanceSheet where
  gold : ℝ
  bondsF : ℝ
  bondsH : ℝ
  moneyF : ℝ
  base : ℝ
  netWorth : ℝ

/-- The balance-sheet identity `P^g Gold + ℰB_F + B_H + ℰM_F = M_H + RR + NW`
(O&R Appendix 8B, p. 598). -/
def CBBalanceSheet.Balanced (b : CBBalanceSheet) (Pg E : ℝ) : Prop :=
  Pg * b.gold + E * b.bondsF + b.bondsH + E * b.moneyF = b.base + b.netWorth

/-- A NONSTERILISED purchase of `δ` dollars' worth of foreign-currency bonds, paid for with
newly issued base money (O&R p. 598). -/
noncomputable def CBBalanceSheet.buyForeign (b : CBBalanceSheet) (E δ : ℝ) : CBBalanceSheet :=
  { b with bondsF := b.bondsF + δ / E, base := b.base + δ }

/-- An open-market SALE of `δ` of domestic bonds, withdrawing base money (O&R p. 599). -/
def CBBalanceSheet.sellHome (b : CBBalanceSheet) (δ : ℝ) : CBBalanceSheet :=
  { b with bondsH := b.bondsH - δ, base := b.base - δ }

/-- A nonsterilised foreign-exchange purchase preserves the balance-sheet identity
(O&R Appendix 8B, p. 598). -/
theorem buyForeign_balanced {b : CBBalanceSheet} {Pg E : ℝ} (hE : E ≠ 0) (δ : ℝ)
    (hb : b.Balanced Pg E) : (b.buyForeign E δ).Balanced Pg E := by
  simp only [CBBalanceSheet.Balanced, CBBalanceSheet.buyForeign] at hb ⊢
  have : E * (b.bondsF + δ / E) = E * b.bondsF + δ := by field_simp
  rw [this]
  linarith

/-- An open-market sale preserves the balance-sheet identity (O&R Appendix 8B, p. 599). -/
theorem sellHome_balanced {b : CBBalanceSheet} {Pg E : ℝ} (δ : ℝ) (hb : b.Balanced Pg E) :
    (b.sellHome δ).Balanced Pg E := by
  simp only [CBBalanceSheet.Balanced, CBBalanceSheet.sellHome] at hb ⊢
  linarith

/-- **A sterilised intervention is a swap of home for foreign bonds with no change in the
money supply** (O&R Appendix 8B, p. 599): nonsterilised purchase followed by an
open-market sale of the same amount. -/
theorem sterilised_is_swap (b : CBBalanceSheet) (E δ : ℝ) :
    ((b.buyForeign E δ).sellHome δ).base = b.base ∧
      ((b.buyForeign E δ).sellHome δ).bondsH = b.bondsH - δ ∧
      ((b.buyForeign E δ).sellHome δ).bondsF = b.bondsF + δ / E ∧
      ((b.buyForeign E δ).sellHome δ).gold = b.gold ∧
      ((b.buyForeign E δ).sellHome δ).moneyF = b.moneyF ∧
      ((b.buyForeign E δ).sellHome δ).netWorth = b.netWorth := by
  simp [CBBalanceSheet.buyForeign, CBBalanceSheet.sellHome]

/-- **Forward intervention is equivalent to sterilised intervention** (O&R §8.7.6.1,
p. 593): a forward purchase of `1+i` dollars for `(1+i)/F` yen at `t+1` lowers the present
value of dollar debt held by the market by `$1` and raises that of yen debt by
`(1+i)/((1+i*)F) = 1/ℰ` yen, also worth `$1`, by covered interest parity (104). -/
theorem forward_intervention_equiv {i istar E F : ℝ} (hi : 0 < 1 + i) (histar : 0 < 1 + istar)
    (hE : 0 < E) (hF : 0 < F) (hcip : 1 + i = (1 + istar) * F / E) :
    (1 + i) / (1 + i) = 1 ∧ 1 / (1 + istar) * ((1 + i) / F) = 1 / E ∧
      E * (1 / (1 + istar) * ((1 + i) / F)) = 1 := by
  refine ⟨div_self hi.ne', ?_, ?_⟩
  · rw [hcip]; field_simp
  · rw [hcip]; field_simp


/-! ## (109) and (119) under genuine joint normality -/

namespace JointGaussian

open MeasureTheory ProbabilityTheory

/-- **The lognormal moment identity for a Gaussian variable** (O&R fn 41 of Ch. 5, used in
fn 75, p. 588): if `Z` has a Gaussian law (Mathlib's `HasGaussianLaw`), then `exp Z` is
integrable and `E[exp Z] = exp(E Z + ½ Var Z)`. -/
theorem expect_exp {Ω' : Type*} {mΩ : MeasurableSpace Ω'} {P : Measure Ω'} {Z : Ω' → ℝ}
    (hZ : HasGaussianLaw Z P) :
    Integrable (fun ω => Real.exp (Z ω)) P ∧
      ∫ ω, Real.exp (Z ω) ∂P = Real.exp (P[Z] + Var[Z; P] / 2) := by
  have hL : HasLaw Z (gaussianReal P[Z] Var[Z; P].toNNReal) P :=
    { aemeasurable := hZ.aemeasurable, map_eq := hZ.map_eq_gaussianReal }
  have hv : ((Var[Z; P].toNNReal : NNReal) : ℝ) = Var[Z; P] :=
    Real.coe_toNNReal _ (variance_nonneg Z P)
  constructor
  · have := hL.integrable_comp (integrable_exp_mul_gaussianReal (μ := P[Z])
      (v := Var[Z; P].toNNReal) 1)
    simpa [Function.comp_def] using this
  · have := mgf_gaussianReal hL 1
    simp only [mgf, one_mul, hv, one_pow, mul_one] at this
    exact this

/-- **(109) under joint normality of `(e, p)`** (O&R (109) and fn 75, p. 588): if the log
exchange rate and the log price level `(e_{t+1}, p_{t+1})` are jointly Gaussian (Mathlib's
`HasGaussianLaw` for the pair) and (107) holds, then
`f = E e + ½ Var e − Cov(e, p)`, with Mathlib's expectation, variance and covariance. -/
theorem eq109_gaussian {Ω' : Type*} {mΩ : MeasurableSpace Ω'} {P : Measure Ω'}
    {e p : Ω' → ℝ} (hG : HasGaussianLaw (fun ω => (e ω, p ω)) P) {F : ℝ} (hF : 0 < F)
    (h107 : ∫ ω, (F - Real.exp (e ω)) / Real.exp (p ω) ∂P = 0) :
    Real.log F = P[e] + Var[e; P] / 2 - cov[e, p; P] := by
  have := hG.isProbabilityMeasure
  have he := hG.fst
  have hp := hG.snd
  have h1 := expect_exp hp.fun_neg
  have h2 := expect_exp hG.fun_sub
  have ex : (fun ω => (F - Real.exp (e ω)) / Real.exp (p ω))
      = fun ω => F * Real.exp (-p ω) - Real.exp (e ω - p ω) := by
    funext ω; rw [Real.exp_neg, Real.exp_sub]; field_simp
  rw [ex, integral_sub (h1.1.const_mul F) h2.1, integral_const_mul, h1.2, h2.2,
    sub_eq_zero] at h107
  have hl := congrArg Real.log h107
  rw [Real.log_mul hF.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at hl
  have m1 : P[fun ω => -p ω] = -P[p] := integral_neg _
  have m2 : P[fun ω => e ω - p ω] = P[e] - P[p] := integral_sub he.integrable hp.integrable
  rw [m1, m2, variance_fun_neg, variance_fun_sub he.memLp_two hp.memLp_two] at hl
  linarith

/-- **(119) under joint normality of `(e, p, c)`** (O&R (119) and fn 79, p. 592): if the
logs of the exchange rate, the price level and consumption at `t+1` are jointly Gaussian and
(118) holds (`C_t = exp c₀` known at `t`), then
`f − E e = ½ Var e − Cov(e, p) − ρ Cov(e, c)`. -/
theorem eq119_gaussian {Ω' : Type*} {mΩ : MeasurableSpace Ω'} {P : Measure Ω'}
    {e p c : Ω' → ℝ} (hG : HasGaussianLaw (fun ω => (e ω, p ω, c ω)) P) {F ρ c₀ : ℝ}
    (hF : 0 < F)
    (h118 : ∫ ω, (F - Real.exp (e ω)) / Real.exp (p ω)
      * (Real.exp c₀ / Real.exp (c ω)) ^ ρ ∂P = 0) :
    Real.log F - P[e] = Var[e; P] / 2 - cov[e, p; P] - ρ * cov[e, c; P] := by
  have := hG.isProbabilityMeasure
  have he := hG.fst
  have hpc := hG.snd
  have hp := hpc.fst
  have hc := hpc.snd
  set L : ℝ × ℝ →L[ℝ] ℝ := -(ContinuousLinearMap.fst ℝ ℝ ℝ + ρ • ContinuousLinearMap.snd ℝ ℝ ℝ)
  set Z : Ω' → ℝ := fun ω => -(p ω + ρ * c ω)
  have hZ : HasGaussianLaw Z P := by
    have := hpc.map_fun L
    have e1 : (fun ω => L (p ω, c ω)) = Z := by funext ω; simp [L, Z]
    rwa [e1] at this
  have hW : HasGaussianLaw (fun ω => e ω + Z ω) P := by
    have := hG.map_fun (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
      + L.comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
    have e1 : (fun ω => (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
        + L.comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) (e ω, p ω, c ω))
        = fun ω => e ω + Z ω := by funext ω; simp [L, Z]
    rwa [e1] at this
  have h1 := expect_exp hZ
  have h2 := expect_exp hW
  have ex : (fun ω => (F - Real.exp (e ω)) / Real.exp (p ω)
      * (Real.exp c₀ / Real.exp (c ω)) ^ ρ)
      = fun ω => Real.exp (ρ * c₀) * (F * Real.exp (Z ω) - Real.exp (e ω + Z ω)) := by
    funext ω
    rw [← Real.exp_sub, ← Real.exp_mul]
    simp only [Z, Real.exp_add, Real.exp_neg]
    rw [show (c₀ - c ω) * ρ = ρ * c₀ + -(ρ * c ω) by ring, Real.exp_add, Real.exp_neg]
    field_simp
  rw [ex, integral_const_mul, integral_sub (h1.1.const_mul F) h2.1, integral_const_mul]
    at h118
  have h3 := (mul_eq_zero.1 h118).resolve_left (Real.exp_pos _).ne'
  rw [h1.2, h2.2, sub_eq_zero] at h3
  have hl := congrArg Real.log h3
  rw [Real.log_mul hF.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at hl
  have m1 : P[fun ω => e ω + Z ω] = P[e] + P[Z] := integral_add he.integrable hZ.integrable
  have v1 : Var[fun ω => e ω + Z ω; P] = Var[e; P] + 2 * cov[e, Z; P] + Var[Z; P] :=
    variance_fun_add he.memLp_two hZ.memLp_two
  have c1 : cov[e, Z; P] = -(cov[e, p; P] + ρ * cov[e, c; P]) := by
    have hpc' : (fun ω => p ω + ρ * c ω) = p + fun ω => ρ * c ω := rfl
    simp only [Z]
    rw [covariance_fun_neg_right, hpc', covariance_add_right he.memLp_two hp.memLp_two
      (hc.memLp_two.const_mul ρ), covariance_const_mul_right]
  rw [m1, v1, c1] at hl
  linarith

/-- **The joint-normality hypothesis is satisfiable with correlated components** (O&R
p. 588): under a standard normal law, `(x, x/2)` is jointly Gaussian. -/
theorem jointGaussian_witness :
    HasGaussianLaw (fun x : ℝ => (x, x / 2)) (gaussianReal 0 1) := by
  have h := (IsGaussian.hasGaussianLaw_id (μ := gaussianReal 0 1)).map_fun
    ((ContinuousLinearMap.id ℝ ℝ).prod ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ))
  have e : (fun x : ℝ => ((ContinuousLinearMap.id ℝ ℝ).prod
      ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)) (id x)) = fun x : ℝ => (x, x / 2) := by
    funext x; simp; ring
  rwa [e] at h

end JointGaussian


/-! ## Non-vacuity of the white-noise hypotheses -/

/-- The uniform distribution on eight states (three fair coin flips) (O&R Exercise 7). -/
noncomputable def uniform8 : FinProb (Fin 8) :=
  ⟨fun _ => 1 / 8, fun _ => by norm_num, by simp⟩

/-- Five `±1` Walsh functions of three fair coin flips (O&R Exercise 7). -/
def walsh : Fin 5 → Fin 8 → ℝ :=
  ![![1, -1, 1, -1, 1, -1, 1, -1], ![1, 1, -1, -1, 1, 1, -1, -1],
    ![1, 1, 1, 1, -1, -1, -1, -1], ![1, -1, -1, 1, 1, -1, -1, 1],
    ![1, -1, 1, -1, -1, 1, -1, 1]]

/-- **The white-noise hypotheses of Exercises 7–8 are satisfiable**: the Walsh functions
of three fair coin flips are mean-zero, unit-variance and uncorrelated (O&R Exercise 7,
p. 602). -/
noncomputable def walshNoise : WhiteNoise uniform8 5 :=
  ⟨walsh, 1, fun i => by
    fin_cases i <;> simp [FinProb.expect, uniform8, walsh, Fin.sum_univ_eight],
    fun i j => by
      fin_cases i <;> fin_cases j <;>
        simp [FinProb.expect, uniform8, walsh, Fin.sum_univ_eight] <;> norm_num⟩

end ObstfeldRogoff.MoneyExchangeRates.ForwardPremium

set_option linter.style.longLine false
#print axioms ObstfeldRogoff.MoneyExchangeRates.caganResidual
#print axioms ObstfeldRogoff.MoneyExchangeRates.cagan_price_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.cagan_steady
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.disc
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.disc_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.disc_lt_one
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.one_sub_disc
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.inv_disc
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.one_lt_inv_disc
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.forward_iterate_generic
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.eq_tsum_of_forward_generic
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.summable_shift_generic
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.tendsto_tail_generic
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.IsCaganPath
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.isCaganPath_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.forward_iteration
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.CaganSummable
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.fundamental
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.caganSummable_of_growth
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.caganSummable_of_bounded
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.summable_shift
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.fundamental_recursion
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.fundamental_isCaganPath
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.fundamental_noBubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.noBubble_shift
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.eq_fundamental_of_noBubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.existsUnique_noBubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.bubble_isCaganPath
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.eq_fundamental_add_bubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.isCaganPath_iff_bubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.bubble_coeff_unique
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.disc_pow_mul_tendsto_bubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.noBubble_iff_bubble_zero
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.abs_tendsto_atTop_of_bubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.weights_sum_one
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.fundamental_const
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.fundamental_add_const
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.fundamental_add
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.fundamental_smul
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.fundamental_mono
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.tsum_nat_mul_disc_pow
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.caganSummable_linear
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.fundamental_linear
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.linear_isCaganPath
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.fundamental_eventually_const
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.stepMoney
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.caganSummable_stepMoney
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.fundamental_stepMoney_ge
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.fundamental_stepMoney_le
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.stepMoney_jump_at_zero
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.stepMoney_strictly_increasing
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.stepMoney_strictly_convex
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.MarkovKernel
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.MarkovKernel.mk
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.MarkovKernel.K
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.MarkovKernel.nonneg
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.MarkovKernel.rowSum
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.kernelApply
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.kernelPow
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.kernelApply_const
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.kernelApply_linear
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.kernelApply_mono
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.kernelApply_abs_le
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.kernelPow_abs_le
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.kernelPow_succ
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.kernelPow_succ'
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.kernelApply_tsum
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.abs_le_sum_abs
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.summable_markov
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.markovFundamental
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.IsMarkovEqm
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.markovFundamental_isMarkovEqm
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.bubble_eq_zero_of_bounded
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.isMarkovEqm_unique
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.existsUnique_markovEqm
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.markovFundamental_mono
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.markovFundamental_eigen
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.markovFundamental_eigen_one
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.one_le_eigen_denominator
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.twoStateKernel
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.twoState_price
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.TreeNode
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.treeExp
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.IsTreeEqm
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.treeExp_abs_le
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.treeExp_linear
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.treeExp_state
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.treeExp_const
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.markovFundamental_isTreeEqm
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.treeEqm_sub_isBubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.treeEqm_add_bubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.treeEqm_iff_bubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.treeEqm_unique_of_bounded
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.treeEqm_bounded_eq_fundamental
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.deterministic_bubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.treeEqm_with_deterministic_bubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.seignorage_decomposition
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.inflation_tax_identity
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.seignorage
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.seignorage_constant_growth
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.hasDerivAt_seignorage
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.continuousOn_seignorage
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.seignorage_strictMonoOn
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.seignorage_strictAntiOn
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.seignorage_lt_max
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.seignorage_foc
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.real_balances_at_max
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.seignorage_zero
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.seignorage_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.seignorage_tendsto_zero
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.continuous_seignorage_lt_max
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.exchangeFundamentals
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.monetary_model_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.exchange_rate_existsUnique
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.exchange_rate_comparative_statics
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.magnification
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.magnification_nonneg
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.magnification_strictMonoOn
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.magnification_one
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.treeExp_money
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.exchange_rate_persistent_growth
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.expected_depreciation_persistent_growth
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.exchange_rate_persistent_growth_unique
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.expected_depreciation_forward_sum
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.fixed_rate_money
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.fixed_money_rate
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.crawling_peg_money
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.crawling_peg_interest
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.IsInterestPegEqm
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.interestPeg_eqm_exists
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.interestPeg_eqm_form
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.interestPeg_indeterminate
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.interestPeg_pinned
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.IsTwoCountryEqm
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.twoCountry_fixed_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.twoCountry_fixed_implementable
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.truncMoney
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.IsFutureFixEqm
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.futureFix_rate
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.futureFix_existsUnique
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.futureFix_indeterminate_without_anchor
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.IsStochFutureFixEqm
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.stochFutureFix_rate_eq_money
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.stochFutureFix_unique
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.treeAncestor
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.treeAncestor_self
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.treeAncestor_child
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.futureFixValue
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.futureFixRate
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.stochFutureFix_exists
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.monthly_fifty_percent_annualised
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganModel.box_8_1_claims
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.AdmissibleMoney
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.AdmissibleMoney.mk
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.AdmissibleMoney.meas
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.AdmissibleMoney.locInt
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.AdmissibleMoney.growth
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.weighted
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.weighted_intervalIntegrable
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.weighted_measurable
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.weighted_integrableOn_Ioi_zero
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.weighted_integrableOn_Ioi
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.contFundamental
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.contFundamental_eq_exp_mul
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.integral_Ioi_weighted
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.contFundamental_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.contFundamental_continuous
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.contFundamental_hasDerivWithinAt
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.contFundamental_hasDerivAt
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.IsCaganSolOn
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.contFundamental_isSol
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.hasDerivAt_bubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.isCaganSolOn_add_bubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.isCaganSolOn_eq_fundamental_add_bubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.isCaganSolOn_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.bubble_coeff_unique
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.contFundamental_noBubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.isCaganSolOn_discounted_tendsto
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.noBubble_iff_eq_fundamental
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.existsUnique_noBubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.bubble_abs_tendsto_atTop
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.tendsto_exp_neg_mul_affine
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.admissible_affine
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.contFundamental_affine
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.affine_general_solution
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.contFundamental_const
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.weights_integrate_to_one
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.integrableOn_forward
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.contFundamental_add_const
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.contFundamental_mono
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.contFundamental_integration_by_parts
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.periodH_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.periodH_disc
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.periodH_scale
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.periodH_bubble_factor
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.periodHPrice
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.periodHPrice_eq_fundamental
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.periodH_solution_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.periodH_equation_limit
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.periodH_weight_limit
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.stepIndex
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.stepIndex_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.stepIndex_bounds
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.step_intervalIntegral
#print axioms ObstfeldRogoff.MoneyExchangeRates.CaganContinuous.periodHPrice_tendsto
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.log_domestic_credit
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.reserves_hasDerivAt
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.shadowRate
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.shadowRate_solves
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.shadowRate_eq_fundamental
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.isCaganSolOn_of_eqOn
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.float_eq_shadow_add_bubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.shadow_add_bubble_isSol
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.IsAttackEqm
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.attackTime
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.shadowRate_attackTime
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.eq_peg_of_continuousAt
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.attackEqm_characterisation
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.attackEqm_exists
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.attackEqm_unique
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.jump_at_other_date
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.depreciation_before_after
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.exhaustionTime
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.attackTime_eq_exhaustion_sub
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.reserves_zero_at_exhaustion
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.reserves_at_attack
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.reserves_at_attack_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.money_drop_at_attack
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.reserves_pos_before_attack
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.log_reserves_hasDerivAt
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.log_reserves_decline_accelerates
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.attackTime_corrected
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.printed_77_wrong
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.attackTime_pos_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.attackTime_strictMono_reserves
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.attackTime_strictAnti_growth
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.immediate_attack
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.IsBubbleAttackEqm
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.bubbleAttackEqm_characterisation
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.bubble_attackTime
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.bubbleAttackEqm_exists
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.bubble_attackTime_strictAnti
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.no_attack_without_growth
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.attack_without_growth_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.attack_without_growth_any_date
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.zero_growth_bubble_size
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.table_8_1_ratios
#print axioms ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack.table_8_1_italy
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.const_of_hasDerivAt_zero
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.zoneSolution
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.zoneSolution_solves
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.zone_ode_general
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.lambda_spec
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.zone_ode_no_drift
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.driftRoot
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.driftRoot_spec
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.driftRoot_props
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.driftRoot_no_drift
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.tendsto_atBot_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.symS
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.symS_eq_exp
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.hasDerivAt_symS
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.hasDerivAt_symS'
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.symS_solves_ode
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.symS_odd
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.edgeMap
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.hasDerivAt_edgeMap
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.continuous_edgeMap
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.edgeMap_strictMonoOn
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.edgeMap_bounds
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.existsUnique_edge
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.existsUnique_symmetric_zone
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.symS_deriv_formula
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.symS_deriv_props
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.symS_strictMonoOn
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.symS_maps_band
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.symS_curvature
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.honeymoon
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.edge_bounds
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.edge_tendsto
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.lambda_tendsto
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.IsLatticeEqm
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latticeEqm_unique
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.exists_theta
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latticeSol
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latticeCoeff
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.sinh_add_add_sinh_sub
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.sinh_add_sub_sinh_sub
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.sinh_step
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latticeCoeff_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latticeSol_isEqm
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latticeEqm_existsUnique
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latticeSol_odd
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latticeSol_increment
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latticeSol_increment_bounds
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latticeSol_smooth_pasting
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latticeSol_honeymoon
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.lattice_boundary_slope
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.freeFloat_solves
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.freeFloat_unique
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.oneS
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.oneSided_attack_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.oneSided_b_neg
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.oneSided_smooth_pasting_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.credible_zone_existsUnique
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.attack_impossible_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.credible_zone_deriv
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.credible_zone_below
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.small_reserves_locus
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.drift_band_smooth_pasting
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.band_interest_bounds
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.band_interest_state_prices
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.band_interest_numbers
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.regulated_second_moment
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.regulated_mean
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.notHitProb
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.notHitProb_mem
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.notHitProb_ceiling
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.notHitProb_antitone
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.notHitProb_block
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.notHitProb_blocks
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.ceiling_hit_almost_surely
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.bandUp
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.bandDown
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.bandKernel
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.bandKernel_apply
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.lattice_eq_markovFundamental
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.lattice_eq_80
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.intervProb
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.intervProb_succ
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.intervProb_mem
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.intervProb_mono_r
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.intervProb_antitone
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.intervProb_bound
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.intervProb_block
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.intervBound
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.intervProb_blocks
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.interventions_infinitely_often
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.reserves_exhausted_almost_surely
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.bandWidth
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.exp_sub_one_bounds
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.hasDerivAt_bandWidth
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.bandWidth_deriv_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.continuousOn_bandWidth
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.bandWidth_strictMonoOn
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.bandWidth_bounds
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.bandWidth_tendsto_zero
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.bandWidth_existsUnique
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.IsDriftBand
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.drift_band_XY
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.drift_band_width
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.driftX
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.driftY
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.driftXY_paste
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.driftBand_characterisation
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.driftBand_existsUnique
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latTheta
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.sinh_half_latTheta
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.cosh_latTheta
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latTheta_char
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latTheta_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latTheta_div_tendsto
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latRate
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.symS_eq_latRate
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latticeSol_eq_latRate
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.abs_sinh_le_cosh
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latRate_uniform_bound
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latRate_uniform_tendsto
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.lattice_converges
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.topValue
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.topValue_eq_latticeSol
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.continuous_topValue
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.topValue_bounds
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.cosh_ratio_antitone
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.topValue_eq_sum
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.topValue_strictMonoOn
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.existsUnique_lattice_spacing
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.latRate_near_edge
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.lattice_edge_tendsto
#print axioms ObstfeldRogoff.MoneyExchangeRates.TargetZone.lattice_edge_converges
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.userCost
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.wealth
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.wealth_succ
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.wealth_of_budget
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.wealth_pv_identity
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.wealth_congr_after
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.wealth_shift_date0
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.lifetimeUtility
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.NoPonzi
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.Transversality
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.Admissible
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.IsOptimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.grad
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.grad_apply
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.concave_le_tangent
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.hasDerivAt_line
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.hasDerivAt_fst
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.hasDerivAt_snd
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.strictMonoOn_of_uC_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.wealth_congr_before
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.wealth_congr_expenditure
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.noPonzi_congr
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.tsum_eq_add_of_eqOn_compl
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.discounted_marginal_utility
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.isOptimal_of_foc
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.euler_of_optimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.money_foc_of_optimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.transversality_of_optimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.isOptimal_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.userCost_eq_fisher
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.money_euler_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.transversality_of_tendsto
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.noPonzi_of_tendsto
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.intertemporal_budget
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.tendsto_wealth_of_budget
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.book_tvc_identity
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.seignorage_partial
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.government_pv
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.national_budget
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.transfers_of_zero_spending
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.aggregate_budget
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.national_budget_with_public_assets
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.national_pv
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.leisure_reduced_form
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.leisure_coefficients_pos_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.separable_concaveOn
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.separable_hasFDerivAt
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.logSeparable_isOptimal_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.steady_consumption_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.constant_consumption_isOptimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesIndex
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesDenom
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesPrice
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesDemandT
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesDemandN
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesDenom_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesPrice_eq_denom_rpow
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesPrice_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesPrice_rpow_one_sub
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesDemand_budget
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesDemand_ratio
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesDemandT_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesDemandN_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesIndex_demand
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesDemand_eq_price_form
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.ces_rpow_le_tangent
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.ces_tangent_le_rpow
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesDemand_foc
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesIndex_le_div_price
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesPrice_isLeast_cost
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesPrice_strictMonoOn
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesPrice_logDeriv_at_one
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.ces_powerMean_tendsto
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.ces_tendsto_one_sub_punctured
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesPrice_tendsto_cobbDouglas
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.eq_iff_rpow_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesInner
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesInner_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesIndex_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesUtility
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesMargC
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesMargM
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesUtility_hasFDerivAt
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.ces_money_demand_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesIndex_on_demand
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesIndex_on_demand'
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.expenditure_on_demand
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesMargC_on_demand
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.euler_growth
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.consumption_path
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.consumption_of_pv
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.pvWeight
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.prod_real_rate
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.pvWeight_eq_book
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dichotomy_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesUtility_separable
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesMarg_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.ces_optimal_foc
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.equilibrium_consumption
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.individual_consumption
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.ces_optimal_consumption
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.ces_equilibrium_consumption
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.logCD_isOptimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.logCD_optimal_consumption
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.logCD_equilibrium_consumption
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cdUtility
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cdMargC
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cdMargM
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cdUtility_hasFDerivAt
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cd_money_demand_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cd_money_demand_book
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cdMargC_on_demand
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cd_equilibrium_consumption
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.gDollar
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.gDollar_hasDerivAt
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.gDollar_increasing_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dollar_foc_ratio
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dollar_demand_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.substRatio
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dollar_zero_of_low_inflation
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.substRatio_strictAnti
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dollar_eventually_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.fiscal_fixing_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.fiscal_fixing_constant
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.fiscal_fixing_pos_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.exchange_rate_increasing_in_G
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.ces_money_demand_strictAnti
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.userCost_fisher_strictMono
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.steady_nominal_rate
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesIndex_eq_cost_div_price
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesIndex_concaveOn
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.isoelastic_hasDerivAt
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesUtility_concaveOn
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.ces_isOptimal_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.cesMargC_mul_expenditure
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.ces_isOptimal_of_closedForm
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dollar_wealth_of_budget
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dollarUtility
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.DollarAdmissible
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.DollarOptimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dollar_wealth_shift
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dollar_reduce
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dollar_euler_of_optimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dollar_money_foc_of_optimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dollar_tvc_of_optimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dollar_foreign_kkt_of_optimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dollar_isOptimal_of_foc
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dollar_optimal_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dollar_65_66_of_optimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dollar_demand_of_optimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility.dollar_67_of_optimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.userCost_of_beta
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.bubble_dynamics_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.BubbleTVC
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.candidate_wealth
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.equilibrium_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.mbar
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.log_dynamics_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.log_orbit
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.log_no_hyperinflation
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.log_discounted_balances
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.log_unique_of_nonneg_growth
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.log_deflation_tvc
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.log_dynamics_path
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.log_steady_state_equilibrium
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.log_equilibrium_unique
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.log_equilibria_multiple
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.steady_state_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.steady_state_unique
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.mbar_pos_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.iterated_money_euler
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.money_euler_limit_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.deflation_growth
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.discounted_product
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.prod_le_exp_neg_sum
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.exp_neg_sum_le_prod
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.tvc_iff_not_summable
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.concave_le_tangent'
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.summable_deriv_of_bounded
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.bounded_rules_out_deflation
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.log_rules_out_deflation
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.linlog_concaveOn
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.linlog_unbounded
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.affinePath
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.linlog_deflation_equilibrium
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.logIntDeriv
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.logIntUtility
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.one_le_log_add_exp
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.logIntDeriv_continuousOn
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.logIntUtility_hasDerivAt
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.logIntDeriv_mem
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.logIntDeriv_strictAntiOn
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.logIntUtility_props
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.deflOrbit
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.deflOrbit_succ
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.logInt_deflation_tvc
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.logIntUtility_unbounded
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.sum_inv_linear_ge
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.logInt_deflation_equilibrium
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.fn34_tendsto_atBot
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.fn34_sharpened
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.slowLog
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.slowLog_nonneg
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.slowLog_hasDerivAt
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.vSlow
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.vSlow_hasDerivAt
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.vSlow_counterexample
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.phiMap
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.phiMap_strictMonoOn
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.phiMap_preimage
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.phiPre
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.backOrbit
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.backOrbit_spec
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.backOrbit_iterate
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.backOrbit_unique
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.backOrbit_tendsto
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.hyperinflation_tendsto_zero
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.backing_rules_out_hyperinflation
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.hyperinflation_asymptotic
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.utility_summable_of_bounded
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.wealthE
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.AdmissibleE
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.IsOptimalE
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.localMax_of_optimalE
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.wealthE_congr_before
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.wealthE_congr_expenditure
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.wealthE_congr_after
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.ex2_money_foc
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.euler_of_optimalE
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.ex2c_money_foc
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.ex2_constant_consumption
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.ex2_dynamics_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.ex2_steady_state
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.ex2_no_deflation
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.ex2_hyperinflation_possible
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.equilibrium_iff_of_bounded
#print axioms ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles.equilibrium_iff_of_balances_bounded
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.ciaWealth
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.ciaDisc
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.ciaAssets
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.CIAAdmissible
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.CIAOptimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.CIATransversality
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.ciaWealth_succ
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.ciaDisc_succ
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.ciaDisc_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.ciaWealth_of_budget
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.cia_pv_identity
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.ciaAssets_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.ciaWealth_congr_before
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.ciaWealth_congr_after
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.cia_perturb_le
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.cia_binds
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.hasDerivAt_affine
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.cia_euler_of_optimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.deriv_nonpos_of_right_max
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.cia_date0_of_optimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.cia_tvc_of_optimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.cia_reindex
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.cia_isOptimal_of_foc
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.cia_optimal_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.budget_59
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.constant_velocity
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.euler_60_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.euler_60_stationary
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.helpman_lucas_euler
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.twoGoodPrice
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.ppp_of_law_of_one_price
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.relative_demand_130
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.relative_price_131
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.steady_real_rate
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.appendix8A_taxes
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.appendix8A_printed_sign
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.BalanceSheet
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.nonsterilised_preserves
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.sterilised_is_swap
#print axioms ObstfeldRogoff.MoneyExchangeRates.CashInAdvance.forward_intervention_identity
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.tendsto_add_nhdsGT
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.slope_right_tendsto
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.right_cont_tendsto
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.period_one_focs
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.mrs_period_h
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.mrs_limit
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.costate_period_h
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.costate_limit
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.fisher_period_h
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.discount_limit
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.flow_budget_limit
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.wealth_flow_equiv
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.concave_le_tangent_gen
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.hamiltonian
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.mangasarian_finite
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.arrow_finite
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.mangasarian_infinite
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.boundary_of_tvc_noPonzi
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.costate_solution
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.monetary_hamiltonian_focs
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.monetary_hamiltonian_concave
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.monetary_sufficiency
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.monetary_boundary
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.integral_exp_neg_mul
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.ponzi_counterexample
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.halkin_rival
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.halkin_candidate
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.variation_of_constants
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.budget_16
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.tvc_iff_wealth
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.budget_17
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.seignorage_by_parts
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.government_18
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.consolidated_19
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.money_demand_22
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.marginal_utility_on_demand
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.consumption_of_marginal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.consumption_23
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.consumption_euler_ct
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.consumption_25
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.real_balances_power
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.inverse_rate_ode
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.rateKernel
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.xStar
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.xStar_eq_book
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.tail_integral_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.xStar_solves
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.xStar_unique
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.nominal_rate_constant_growth
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.priceIndex_cobbDouglas
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.ctWealth
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.CTAdmissible
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.CTOptimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.ctWealth_hasDerivAt
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.ct_foc_integral
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.tent
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.tent_continuous
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.tent_nonneg
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.tent_eq_zero
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.tent_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.integral_pos_of_pos_at
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.ct_money_foc
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.integral_eq_of_vanish
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.ct_costate_of_optimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.ct_tvc_of_optimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.MaximumPrinciple.monetary_optimal_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.mk
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.prob
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.prob_nonneg
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.prob_sum
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.expect
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.cov
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.var
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.expect_const
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.expect_add
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.expect_sub
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.expect_mul_left
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.expect_mono
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.exists_prob_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.expect_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.expect_mul_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.var_eq_expect_sq
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.var_nonneg
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.cov_add_left
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.cov_add_right
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.cov_mul_left
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.cov_mul_right
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.cov_comm
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.cov_const_left
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.cov_add_const_right
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.var_add
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.var_sub
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.FinProb.var_const_add
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Kernel
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Kernel.mk
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Kernel.trans
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Kernel.trans_nonneg
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Kernel.trans_sum
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Kernel.row
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Hist
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.next
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.anc
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.depth
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.anc_next
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.depth_next
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.oneStep
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.iterStep
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.oneStep_add
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.oneStep_sub
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.oneStep_mul_left
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.oneStep_const
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.oneStep_mono
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.oneStep_pull
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.iterStep_succ
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.iterStep_succ'
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.iterStep_add
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.iterStep_add_fun
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.iterStep_sub_fun
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.iterStep_mul_left
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.iterStep_const
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.iterStep_mono
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.iterStep_pull
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.iterStep_depth
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.abs_iterStep_le
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.iterStep_nonneg
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.iterStep_le_pow_mul
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.concave_tangent
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.assetValue
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.hasDerivAt_assetValue
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.asset_euler_of_isLocalMax
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.assetValue_le_of_euler
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.isLocalMax_assetValue_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.moneyValue
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.hasDerivAt_moneyValue
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.isLocalMax_moneyValue_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.nominal_bond_euler_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.real_bond_euler_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.fisher_iff_cov_zero
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.fisher_of_deterministic_consumption
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.money_demand_of_euler
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.consumption_shares
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.consumption_growth_eq_world
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.rpow_ratio_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.money_euler_crra_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.price_ratio_term_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.eq99_iff_linear
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Eq99
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.realBal
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.marginal_utility_real_balances
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.tilt
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.LinearMoneyEq
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.oneStep_tilt_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.eq99_iff_linearMoneyEq
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.tilt_nonneg
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.tilt_sum
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.omega_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Solutions.omega_solves
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Solutions.linear_iff_bubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Solutions.bubble_iterate
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Solutions.unique_bounded
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Solutions.ge_omega_of_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Solutions.depthBubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Solutions.iterStep_depthBubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Solutions.depthBubble_solves
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Solutions.depthBubble_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Solutions.nodeAt
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Solutions.depth_nodeAt
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Solutions.depthBubble_unbounded
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Solutions.no_positive_solution
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.TVC
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.omega_TVC
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.depthBubble_not_TVC
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.depthBubble_TVC_of_neg
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.min_eps_le_one
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.unique_of_TVC
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.unique_of_TVC_deterministic
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.markov_unique
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.price_level_formula
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.price_level_independent_of_future_output
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.omega_strictAnti
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.real_balances_strictMono
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.nominal_rate_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.money_demand_at_equilibrium
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.next_money_pos_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.no_positive_money_of_eps_zero
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.one_le_expect_eps
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.expected_money_growth
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.exampleKernel
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.exampleEps
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.example_eps_moments
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.CaganTree
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.logLinear_iff_cagan
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.fundamental
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.NoBubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.oneStep_tsum
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.oneStep_summable
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.iterStep_tsum
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.fundamental_solves
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.fundamental_noBubble
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.cagan_unique
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.logLinear_price_solution
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.cia_price_level
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.cia_velocity
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.cia_exchange_rate
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.cia_bond_price_log
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.dollarization_home_rate_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.dollarization_foc
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.dollarization_demand
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.no_dollarization_of_low_inflation
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.dollarization_ratio_strictAnti
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.dollarization_threshold
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.extend
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Desc
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.desc_refl
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.desc_of_desc_next
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.extend_append
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.desc_next
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.depth_extend
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.iterStep_mono_desc
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.iterStep_congr_desc
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.iterStep_congr_depth
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.AssetMarket
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.AssetMarket.mk
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.AssetMarket.price
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.AssetMarket.payoff
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.AssetMarket.service
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.AssetMarket.endow
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.services
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.Feasible
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.Positive
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.utilTerm
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.lifetimeU
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.Euler
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.contValue
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.NoPonzi
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.TVCHousehold
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.noPonzi_of_nonneg_wealth
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.household_sufficiency
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.contValue_eq_holdings
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.depth_of_anc_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.eq_next_of_anc_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.next_ne
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.depth_anc
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.depth_le_of_desc
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.reachProb
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.reachProb_self
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.reachProb_next
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.perturbC
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.perturbA
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.services_perturbA
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.feasible_perturb
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.localValue
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.lifetimeU_perturb
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Household.household_euler_necessary
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.crra_concave
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.cons
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.lam
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.price
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.realRate
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.divU
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.fundU
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.fundPrice
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.market
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.holdings
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.wealth0
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.Lemmas.lam_div_price
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.Lemmas.oneStep_lam_div_price
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.Lemmas.divU_bound
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.Lemmas.fundU_terms
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.Lemmas.fundU_recursion
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.euler_holds
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.feasible
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.positive
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.tvc
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.util_summable
#print axioms ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing.Equilibrium87.equilibrium_optimal
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.cipCost
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.cipPayoff
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.cip_portfolio_riskless
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.arbitrage_of_not_cip
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.StatePrices
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.StatePrices.mk
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.StatePrices.q
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.StatePrices.q_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.PricesInstruments
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.cip_of_statePrices
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.no_statePrices_of_arbitrage
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.expect_mul_expect_inv
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.one_le_expect_mul_expect_inv
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Degenerate
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.one_lt_expect_mul_expect_inv
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.expect_of_degenerate
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.siegel_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.jensen_term_number
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Gaussian.expect_exp_gaussian
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Gaussian.log_forward_gaussian
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.eq107_iff_eq108
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.eq107_iff_ratio
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.forward_exact_decomposition
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.LognormalMGF
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.var_neg
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.eq109
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.eq106_of_constant_price
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.real_return_differential
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.eq116_of_euler
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.eq117_of_eq116
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.forward_euler_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.crra_mrs
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.forward_rate_ge
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.eq119
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.eq119_rho_zero
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.cov_consumption_eq_output
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.pairProb
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.condE
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.forecast_error_orthogonal
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Fama.fwdPrem
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Fama.expDep
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Fama.riskPrem
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Fama.realDep
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Fama.fwdPrem_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Fama.cov_fwdPrem_realDep
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Fama.fama_slope
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Fama.fama_negative_slope
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Fama.fama_half_slope
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Fama.fama_slope_null
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.expect_sq_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.ols_minimises
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Engel.expenditure
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Engel.costSet
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Engel.expenditure_smul
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Engel.expenditure_pos
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Engel.budget_binds
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Engel.price_level_eq
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Engel.least_cost_smul
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Engel.price_level_scales
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Engel.euler_homogeneous
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.Engel.marginal_index_eq_relative_price
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.ex6d_iff_ex6b
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.ex6c_iff
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.no_real_siegel
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.cobb_douglas_share
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.ex6e_spot_rate
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.cobb_douglas_partial
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.prodProb
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.expect_prod_mul
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.ex6e_forward_rate
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.ex6f
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.WhiteNoise
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.WhiteNoise.mk
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.WhiteNoise.eps
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.WhiteNoise.sigma2
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.WhiteNoise.mean_zero
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.WhiteNoise.second
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.comb
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.expect_finsum
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.expect_comb
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.cov_comb
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.timeavg_increment
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.ex7a_autocorrelation
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.ex7b_point_sampling
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.ex7a_conditional
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.ex7b_conditional
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.ex8a_overlap
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.forecastErr
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.forecastErr_unbiased
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.ex8b_nonoverlap
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.CBBalanceSheet
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.CBBalanceSheet.mk
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.CBBalanceSheet.gold
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.CBBalanceSheet.bondsF
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.CBBalanceSheet.bondsH
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.CBBalanceSheet.moneyF
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.CBBalanceSheet.base
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.CBBalanceSheet.netWorth
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.CBBalanceSheet.Balanced
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.CBBalanceSheet.buyForeign
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.CBBalanceSheet.sellHome
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.buyForeign_balanced
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.sellHome_balanced
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.sterilised_is_swap
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.forward_intervention_equiv
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.JointGaussian.expect_exp
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.JointGaussian.eq109_gaussian
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.JointGaussian.eq119_gaussian
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.JointGaussian.jointGaussian_witness
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.uniform8
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.walsh
#print axioms ObstfeldRogoff.MoneyExchangeRates.ForwardPremium.walshNoise
