/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MoneyExchangeRates.Model
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp

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
