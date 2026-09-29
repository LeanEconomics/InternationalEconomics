/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GlobalGrowth.AKModel
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Endogenous innovation and growth: the Romer model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §7.3.3
(pp. 483–496), equations (79)–(102), footnotes 41–42, Exercise 3 (p. 512), the Kremer
application (pp. 492–495), growth accounting (p. 482) and the Grossman–Helpman example
(pp. 495–496).

* **Supply side (79)–(93).** The final-goods first-order condition (84) is sufficient (by
  the tangent inequality for `x^α`), and the problem (83) separates across goods. The
  monopoly quantity (86), markup (87) and profit (88) are proved globally optimal. The
  blueprint price (89) is a genuine present-value sum. Labour arbitrage (91) holds iff
  `L_Y = r/(θα)` (92), which gives the TT curve (93).
* **Balanced growth (94)–(96).** For every `σ > 0` there is at most one balanced-growth
  equilibrium; the book only exhibits the intersection. An interior one exists iff
  `θL > (1-β)/(αβ)`, for every `σ`. Household utility is finite iff `g < r`, which is
  automatic for `σ ≤ 1` and can fail for `σ > 1` (explicit counterexample). Also: the log
  case (95)–(96), and the scale and merging effects for general `σ` (§7.3.3.6).
* **Verification that the BGP is a competitive equilibrium.** Firms are optimal, blueprints
  are priced by free entry, the labour and goods markets clear, household wealth (the value
  of the firms) obeys the budget identity, and the household's consumption plan is optimal
  over the infinite horizon (supporting hyperplane; imported from `AKModel`).
* **Social planner (fn 42, (97), Exercise 3).** The closed-form value function
  `V(A, X) = κ + a log A + b log X` satisfies the Bellman equation *exactly*, with the slack
  split into a saving part and an R&D part. With a lower bound on continuation values (the
  unbounded-below log tail) this gives optimality among all feasible plans with convergent
  utility, and uniqueness of the optimal path. The planner's growth rate is (97). Capital
  per blueprint converges to `K^{PLAN}`, so the planner is on a balanced path only in the
  limit unless `K₀ = K^{PLAN}`. Planned growth exceeds market growth, and the subsidised
  rate lies strictly in between.
* **Kremer (98)–(102).** Equation (102) holds, population growth rises with population, and
  population diverges.
* **Grossman–Helpman, corrected.** With the same `F` in both sectors the PPF is linear, the
  autarky price is 1 whatever the preferences, and any other world price gives complete
  specialisation. The printed law `A' - A = θXA` makes growth explode; the corrected law
  gives constant growth. For a general technology set, a higher world price of `X` weakly
  raises `X` output and hence growth (strictly if production moves), and a lower price
  lowers it.
* **Round 2 additions.**
  - *Subsidised equilibrium:* verified in full, with lump-sum taxes (`SubsidyAllocation`). The
    subsidised balanced path is unique and exists iff `θL > (1-β)/β`.
  - *Planner's corner case:* when `βθL ≤ 1-β` there is no research and no growth; this is
    proved by the same Bellman verification.
  - *Market dynamics off the balanced path:* for any utility, the economy cannot reach a
    stationary allocation in finite time unless it starts there (`romer_no_finite_arrival`).
    With log utility the equilibrium exists and is unique for every `A₀, K₀`. It has `L_Y`
    and blueprint growth at their balanced values from date 0, while `K_t` and the interest
    rate converge only asymptotically (`K_{t+1} = cK_t^α`). So O&R's "jumps immediately to a
    steady state" is true for growth, but false for capital and interest rates unless
    `K₀ = K̄`.
* **Round 3.** For `σ ≠ 1`, even growth does not jump: a constant `L_Y` from date 0 forces `K₁ = K₀`
  (`romer_sigma_ne_one_no_jump`). In every log equilibrium the blueprint price is the present
  value of profits; the no-bubble property is derived from household optimality
  (`romer_log_blueprint_pv`).
-/

namespace ObstfeldRogoff.GlobalGrowth.RomerGrowth

open Filter Topology Finset ObstfeldRogoff.GlobalGrowth.AKModel

/-! ## Cobb–Douglas tangent inequality -/

/-- Concavity of `x ↦ x^α` (`0 < α < 1`) in tangent form: `x^α ≤ x₀^α + α x₀^{α-1}(x - x₀)`
for `x ≥ 0`, `x₀ > 0`; the inequality behind the firms' problems (83)–(85). -/
theorem rpow_le_tangent {α x₀ x : ℝ} (hα : 0 < α) (hα1 : α < 1) (hx₀ : 0 < x₀) (hx : 0 ≤ x) :
    x ^ α ≤ x₀ ^ α + α * x₀ ^ (α - 1) * (x - x₀) := by
  have hgm := Real.geom_mean_le_arith_mean2_weighted hα.le (by linarith : 0 ≤ 1 - α) hx
    hx₀.le (by ring)
  have h1 : x₀ ^ (α - 1) * x₀ ^ (1 - α) = 1 := by
    rw [← Real.rpow_add hx₀, show α - 1 + (1 - α) = 0 by ring, Real.rpow_zero]
  have h2 : x₀ ^ (α - 1) * x₀ = x₀ ^ α := by
    rw [show α = (α - 1) + 1 by ring, Real.rpow_add hx₀, Real.rpow_one]
    ring_nf
  have hpos : 0 < x₀ ^ (α - 1) := Real.rpow_pos_of_pos hx₀ _
  have key : x ^ α = x₀ ^ (α - 1) * (x ^ α * x₀ ^ (1 - α)) := by
    rw [mul_comm (x ^ α), ← mul_assoc, h1, one_mul]
  rw [key]
  have := mul_le_mul_of_nonneg_left hgm hpos.le
  nlinarith

/-! ## Final goods and intermediate goods (79)–(88) -/

/-- **Demand for capital goods** O&R (84), p. 487: the final-goods producer's first-order
condition for `K_j`, `∂/∂K (L_Y^{1-α} K^α - pK) = α L_Y^{1-α} K^{α-1} - p`. -/
theorem finalGoods_foc {α LY K p : ℝ} (hK : 0 < K) :
    HasDerivAt (fun x => LY ^ (1 - α) * x ^ α - p * x)
      (α * LY ^ (1 - α) * K ^ (α - 1) - p) K := by
  have h : HasDerivAt (fun x => LY ^ (1 - α) * x ^ α - p * x)
      (LY ^ (1 - α) * (α * K ^ (α - 1)) - p * 1) K :=
    ((Real.hasDerivAt_rpow_const (p := α) (Or.inl hK.ne')).const_mul
      (LY ^ (1 - α))).sub ((hasDerivAt_id K).const_mul p)
  convert h using 1
  ring

/-- **The final-goods problem (83) is solved by (84)** (O&R p. 487): at the price
`p = α L_Y^{1-α} K^{α-1}`, the quantity `K` maximises `L_Y^{1-α} x^α - p x` over `x ≥ 0`. -/
theorem finalGoods_optimal {α LY K x : ℝ} (hα : 0 < α) (hα1 : α < 1) (hLY : 0 < LY)
    (hK : 0 < K) (hx : 0 ≤ x) :
    LY ^ (1 - α) * x ^ α - α * LY ^ (1 - α) * K ^ (α - 1) * x ≤
      LY ^ (1 - α) * K ^ α - α * LY ^ (1 - α) * K ^ (α - 1) * K := by
  have ht := rpow_le_tangent hα hα1 hK hx
  have hL := Real.rpow_pos_of_pos hLY (1 - α)
  nlinarith [mul_le_mul_of_nonneg_left ht hL.le]

/-- **The marginal product of a new capital good is unbounded** O&R (80), p. 485:
`α L_Y^{1-α} K^{α-1} → ∞` as `K ↓ 0`. -/
theorem new_good_mpk_unbounded {α LY : ℝ} (hα : 0 < α) (hα1 : α < 1) (hLY : 0 < LY) :
    Tendsto (fun K : ℝ => α * LY ^ (1 - α) * K ^ (α - 1)) (𝓝[>] 0) atTop :=
  (tendsto_rpow_neg_nhdsGT_zero (by linarith : α - 1 < 0)).const_mul_atTop
    (by have := Real.rpow_pos_of_pos hLY (1 - α); positivity)

/-- **Separability of (83)** (O&R p. 487): if each `K_j` solves its own problem at price
`p_j`, the vector `(K_j)` maximises `L_Y^{1-α} ∑ K_j^α - ∑ p_j K_j`. -/
theorem finalGoods_separable {α LY : ℝ} (s : Finset ℕ) (p K : ℕ → ℝ)
    (hopt : ∀ j ∈ s, ∀ x, 0 ≤ x → LY ^ (1 - α) * x ^ α - p j * x ≤
      LY ^ (1 - α) * K j ^ α - p j * K j)
    (x : ℕ → ℝ) (hx : ∀ j ∈ s, 0 ≤ x j) :
    LY ^ (1 - α) * ∑ j ∈ s, x j ^ α - ∑ j ∈ s, p j * x j ≤
      LY ^ (1 - α) * ∑ j ∈ s, K j ^ α - ∑ j ∈ s, p j * K j := by
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  exact sum_le_sum fun j hj => hopt j hj (x j) (hx j hj)

/-- Present-value monopoly profit of an intermediate-goods producer, O&R (85), p. 487:
`Π(K) = α L_Y^{1-α} K^α/(1+r) - K` (the good is produced one period before it is sold). -/
noncomputable def monoProfit (α r LY K : ℝ) : ℝ := α * LY ^ (1 - α) * K ^ α / (1 + r) - K

/-- **Monopoly pricing: the first-order condition of (85) is sufficient** (O&R p. 487):
if `α² L_Y^{1-α} K^{α-1} = 1 + r`, then `K` maximises `Π` over all `x ≥ 0`. -/
theorem monoProfit_optimal {α r LY K x : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < 1 + r)
    (hLY : 0 < LY) (hK : 0 < K) (hfoc : α ^ 2 * LY ^ (1 - α) * K ^ (α - 1) = 1 + r)
    (hx : 0 ≤ x) : monoProfit α r LY x ≤ monoProfit α r LY K := by
  unfold monoProfit
  have ht := rpow_le_tangent hα hα1 hK hx
  have hL := Real.rpow_pos_of_pos hLY (1 - α)
  have h1 := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ α * LY ^ (1 - α))
  have e : α * LY ^ (1 - α) * (K ^ α + α * K ^ (α - 1) * (x - K)) =
      α * LY ^ (1 - α) * K ^ α + (1 + r) * (x - K) := by
    rw [← hfoc]
    ring
  have key : α * LY ^ (1 - α) * x ^ α - (1 + r) * x ≤
      α * LY ^ (1 - α) * K ^ α - (1 + r) * K := by linarith
  have e1 : α * LY ^ (1 - α) * x ^ α / (1 + r) - x =
      (α * LY ^ (1 - α) * x ^ α - (1 + r) * x) / (1 + r) := by field_simp
  have e2 : α * LY ^ (1 - α) * K ^ α / (1 + r) - K =
      (α * LY ^ (1 - α) * K ^ α - (1 + r) * K) / (1 + r) := by field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right key hr.le

/-- The scale factor of the monopoly quantity (86): `κ = (α²/(1+r))^{1/(1-α)}`. -/
noncomputable def kappa (α r : ℝ) : ℝ := (α ^ 2 / (1 + r)) ^ (1 / (1 - α))

/-- `κ > 0`. -/
theorem kappa_pos {α r : ℝ} (hα : 0 < α) (hr : 0 < 1 + r) : 0 < kappa α r :=
  Real.rpow_pos_of_pos (by positivity) _

/-- `κ^{1-α} = α²/(1+r)` (the defining property of (86)). -/
theorem kappa_rpow {α r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < 1 + r) :
    kappa α r ^ (1 - α) = α ^ 2 / (1 + r) := by
  unfold kappa
  rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (by linarith), Real.rpow_one]

/-- `κ^{α-1} = (1+r)/α²`. -/
theorem kappa_rpow_neg {α r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < 1 + r) :
    kappa α r ^ (α - 1) = (1 + r) / α ^ 2 := by
  rw [show α - 1 = -(1 - α) by ring, Real.rpow_neg (kappa_pos hα hr).le,
    kappa_rpow hα hα1 hr, inv_div]

/-- The key scalar identity `(1+r) κ = α² κ^α`. -/
theorem kappa_identity {α r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < 1 + r) :
    (1 + r) * kappa α r = α ^ 2 * kappa α r ^ α := by
  have hk := kappa_pos hα hr
  have h : kappa α r = kappa α r ^ α * kappa α r ^ (1 - α) := by
    rw [← Real.rpow_add hk, show α + (1 - α) = 1 by ring, Real.rpow_one]
  rw [kappa_rpow hα hα1 hr] at h
  have e : (1 + r) * kappa α r = (1 + r) * (kappa α r ^ α * (α ^ 2 / (1 + r))) := by
    rw [← h]
  rw [e]
  field_simp

/-- `L_Y^{1-α} (κ L_Y)^{α-1} = κ^{α-1}`: the capital intensity of the symmetric choice. -/
theorem scale_rpow {α κ LY : ℝ} (hκ : 0 < κ) (hLY : 0 < LY) :
    LY ^ (1 - α) * (κ * LY) ^ (α - 1) = κ ^ (α - 1) := by
  rw [Real.mul_rpow hκ.le hLY.le, mul_left_comm, ← Real.rpow_add hLY,
    show 1 - α + (α - 1) = 0 by ring, Real.rpow_zero, mul_one]

/-- `L_Y^{1-α} (κ L_Y)^α = κ^α L_Y` (fn 41: `Y = L_Y^{1-α} A K̄^α` per blueprint). -/
theorem scale_output {α κ LY : ℝ} (hκ : 0 < κ) (hLY : 0 < LY) :
    LY ^ (1 - α) * (κ * LY) ^ α = κ ^ α * LY := by
  rw [Real.mul_rpow hκ.le hLY.le, mul_left_comm, ← Real.rpow_add hLY,
    show 1 - α + α = 1 by ring, Real.rpow_one]

/-- **The monopoly quantity** O&R (86), p. 487: `K̄ = (α²/(1+r))^{1/(1-α)} L_Y` satisfies the
first-order condition of (85), hence (by `monoProfit_optimal`) maximises profit. -/
theorem monopoly_quantity {α r LY : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < 1 + r)
    (hLY : 0 < LY) :
    α ^ 2 * LY ^ (1 - α) * (kappa α r * LY) ^ (α - 1) = 1 + r := by
  rw [mul_assoc, scale_rpow (kappa_pos hα hr) hLY, kappa_rpow_neg hα hα1 hr]
  field_simp

/-- **Constant markup** O&R (87), p. 487: `p̄ = α L_Y^{1-α} K̄^{α-1} = (1+r)/α`. -/
theorem monopoly_price {α r LY : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < 1 + r)
    (hLY : 0 < LY) :
    α * LY ^ (1 - α) * (kappa α r * LY) ^ (α - 1) = (1 + r) / α := by
  rw [mul_assoc, scale_rpow (kappa_pos hα hr) hLY, kappa_rpow_neg hα hα1 hr]
  field_simp

/-- **Monopoly profit** O&R (88), p. 488:
`Π̄ = ((1-α)/α) K̄ = ((1-α)/α)(α²/(1+r))^{1/(1-α)} L_Y`. -/
theorem monopoly_profit {α r LY : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < 1 + r)
    (hLY : 0 < LY) :
    monoProfit α r LY (kappa α r * LY) = (1 - α) / α * (kappa α r * LY) := by
  unfold monoProfit
  have hk := kappa_pos hα hr
  rw [mul_assoc, scale_output hk hLY]
  have hid := kappa_identity hα hα1 hr
  field_simp
  nlinarith

/-- **The monopolist's optimum, in full** (O&R (85)–(88)): `K̄ = κ L_Y` maximises
`Π(K)` over `K ≥ 0` and the maximal profit is `((1-α)/α) K̄`. -/
theorem monopoly_optimal {α r LY x : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < 1 + r)
    (hLY : 0 < LY) (hx : 0 ≤ x) :
    monoProfit α r LY x ≤ (1 - α) / α * (kappa α r * LY) := by
  rw [← monopoly_profit hα hα1 hr hLY]
  exact monoProfit_optimal hα hα1 hr hLY (mul_pos (kappa_pos hα hr) hLY)
    (monopoly_quantity hα hα1 hr hLY) hx

/-- **The price of a blueprint** O&R (89), p. 488 (free entry): the present value of the
profit stream, `p_A = ∑_{s ≥ 0} Π̄/(1+r)^s = (1+r) Π̄ / r`, a genuine infinite sum (`r > 0`). -/
theorem blueprint_price {r prof : ℝ} (hr : 0 < r) :
    HasSum (fun s : ℕ => prof * ((1 + r) ^ s)⁻¹) ((1 + r) * prof / r) := by
  have hq : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h := (hasSum_geometric_of_lt_one (by positivity) hq).mul_left prof
  convert h using 1
  · funext s
    rw [inv_pow]
  · field_simp
    rw [show 1 + r - 1 = r by ring]
    field_simp

/-- The blueprint price obeys the no-arbitrage recursion `p_A = Π̄ + p_A/(1+r)` (O&R (89)). -/
theorem blueprint_recursion {r prof : ℝ} (hr : 0 < r) :
    (1 + r) * prof / r = prof + (1 + r) * prof / r / (1 + r) := by
  field_simp
  ring

/-- **Labour-market arbitrage** O&R (91)–(92), pp. 488–489: with `K̄ = κ L_Y`,
`Π̄ = ((1-α)/α) K̄` and `p_A = (1+r)Π̄/r`, the R&D wage per blueprint `θ p_A` equals the
final-goods wage per blueprint `(1-α) L_Y^{-α} K̄^α` iff `L_Y = r/(θα)`. -/
theorem labour_arbitrage_iff {α r θ LY : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r)
    (hθ : 0 < θ) (hLY : 0 < LY) :
    θ * ((1 + r) * ((1 - α) / α * (kappa α r * LY)) / r) =
        (1 - α) * (LY ^ (-α) * (kappa α r * LY) ^ α) ↔ LY = r / (θ * α) := by
  have hr1 : 0 < 1 + r := by linarith
  have hk := kappa_pos hα hr1
  have hid := kappa_identity hα hα1 hr1
  have hwage : LY ^ (-α) * (kappa α r * LY) ^ α = kappa α r ^ α := by
    rw [Real.mul_rpow hk.le hLY.le, mul_left_comm, ← Real.rpow_add hLY, neg_add_cancel,
      Real.rpow_zero, mul_one]
  rw [hwage]
  have hka : 0 < kappa α r ^ α := Real.rpow_pos_of_pos hk α
  have h1a : 0 < 1 - α := by linarith
  constructor
  · intro h
    have e1 : θ * LY * ((1 + r) * kappa α r) * (1 - α) = r * α * kappa α r ^ α * (1 - α) := by
      field_simp at h
      linear_combination (1 - α) * h
    rw [hid] at e1
    have e2 : θ * LY * α * (α * kappa α r ^ α * (1 - α)) = r * (α * kappa α r ^ α * (1 - α)) := by
      linear_combination e1
    have e3 := mul_right_cancel₀ (by positivity) e2
    field_simp
    linarith
  · intro h
    rw [h, show θ * ((1 + r) * ((1 - α) / α * (kappa α r * (r / (θ * α)))) / r) =
      (1 - α) * ((1 + r) * kappa α r) / α ^ 2 by field_simp, hid]
    field_simp

/-- Aggregation in the symmetric equilibrium (O&R fn 41): `∑_{j<A} K̄^α = A K̄^α`. -/
theorem symmetric_sum (A : ℕ) (K α : ℝ) : ∑ _j ∈ range A, K ^ α = A * K ^ α := by
  rw [sum_const, card_range, nsmul_eq_mul]

/-! ## Balanced growth equilibria (90)–(96) -/

/-- **The TT curve** O&R (90), (92)–(93), p. 489: with `g = θ L_A`, `L_A + L_Y = L` and
`L_Y = r/(θα)`, `g = θL - r/α`, equivalently `1 + g = θL + (1+α)/α - (1+r)/α`. -/
theorem tt_curve {α θ L r : ℝ} (hα : 0 < α) (hθ : 0 < θ) :
    θ * (L - r / (θ * α)) = θ * L - r / α ∧
      θ * L - r / α = θ * L + (1 + α) / α - (1 + r) / α - 1 := by
  constructor
  · field_simp
  · field_simp
    ring

/-- **The consumption Euler curve** O&R (94), p. 489: `1 + r = (1+g)^{1/σ}/β` iff
`1 + g = [β(1+r)]^σ` (for `1 + g > 0`, `1 + r > 0`). -/
theorem euler_curve_iff {σ β r g : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hr : 0 < 1 + r)
    (hg : 0 < 1 + g) :
    1 + r = (1 + g) ^ (1 / σ) / β ↔ 1 + g = (β * (1 + r)) ^ σ := by
  constructor
  · intro h
    have h2 : β * (1 + r) = (1 + g) ^ (1 / σ) := by
      rw [h]
      field_simp
    rw [h2, ← Real.rpow_mul hg.le, one_div_mul_cancel hσ.ne', Real.rpow_one]
  · intro h
    rw [h, growth_rpow_inv hσ (mul_pos hβ hr)]
    field_simp

/-- A **balanced-growth equilibrium** of the Romer model (O&R Fig. 7.14): the TT curve (93)
and the Euler curve (94) both hold at `(r, g)`. -/
structure IsBGP (α β σ θ L r g : ℝ) : Prop where
  tt : g = θ * L - r / α
  euler : 1 + g = (β * (1 + r)) ^ σ

/-- The Euler curve is strictly increasing: `r ↦ [β(1+r)]^σ`. -/
theorem euler_strictMono {σ β : ℝ} (hσ : 0 < σ) (hβ : 0 < β) {r₁ r₂ : ℝ}
    (h1 : 0 < 1 + r₁) (h : r₁ < r₂) : (β * (1 + r₁)) ^ σ < (β * (1 + r₂)) ^ σ :=
  Real.rpow_lt_rpow (by positivity) (by nlinarith) hσ

/-- **Uniqueness of the balanced-growth equilibrium** (O&R p. 490, which only exhibits the
intersection): the TT curve is strictly decreasing and the Euler curve strictly increasing,
so there is at most one balanced growth path, for every `σ > 0`. -/
theorem bgp_unique {α β σ θ L r₁ g₁ r₂ g₂ : ℝ} (hα : 0 < α) (hσ : 0 < σ) (hβ : 0 < β)
    (h1 : IsBGP α β σ θ L r₁ g₁) (h2 : IsBGP α β σ θ L r₂ g₂) (hr₁ : 0 < 1 + r₁)
    (hr₂ : 0 < 1 + r₂) : r₁ = r₂ ∧ g₁ = g₂ := by
  have hr : r₁ = r₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have he := euler_strictMono hσ hβ hr₁ hlt
      have : g₁ < g₂ := by linarith [h1.euler, h2.euler]
      have htt : g₂ < g₁ := by
        rw [h1.tt, h2.tt]
        have := div_lt_div_of_pos_right hlt hα
        linarith
      linarith
    · have he := euler_strictMono hσ hβ hr₂ hgt
      have : g₂ < g₁ := by linarith [h1.euler, h2.euler]
      have htt : g₁ < g₂ := by
        rw [h1.tt, h2.tt]
        have := div_lt_div_of_pos_right hgt hα
        linarith
      linarith
  exact ⟨hr, by rw [h1.tt, h2.tt, hr]⟩

/-- **Existence of an interior balanced-growth equilibrium** (O&R p. 490, stated there for
the log case only): for every `σ > 0` and `0 < β < 1`, there is a BGP with `g > 0` and
`r > 0` (so that `0 < L_Y < L`) iff `θL > (1-β)/(αβ)`. -/
theorem bgp_exists_iff {α β σ θ L : ℝ} (hα : 0 < α) (hσ : 0 < σ) (hβ : 0 < β) (hβ1 : β < 1) :
    (∃ r g, IsBGP α β σ θ L r g ∧ 0 < g ∧ 0 < r) ↔ (1 - β) / (α * β) < θ * L := by
  constructor
  · rintro ⟨r, g, h, hg, hr⟩
    have h1 : 1 < (β * (1 + r)) ^ σ := by linarith [h.euler]
    have h2 : 1 < β * (1 + r) := (one_lt_growth_iff hσ (by positivity)).mp h1
    have h3 : r < α * (θ * L) := by
      have := h.tt
      have : r / α < θ * L := by linarith
      rwa [div_lt_iff₀ hα, mul_comm] at this
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  · intro hcond
    set φ : ℝ → ℝ := fun r => (β * (1 + r)) ^ σ - 1 - (θ * L - r / α) with hφ
    set a := 1 / β - 1 with ha
    set b := α * (θ * L) with hb
    have hab : a < b := by
      rw [div_lt_iff₀ (by positivity)] at hcond
      rw [ha, hb, div_sub_one hβ.ne', div_lt_iff₀ hβ]
      nlinarith
    have hapos : 0 < a := by
      rw [ha, div_sub_one hβ.ne']
      exact div_pos (by linarith) hβ
    have hcont : ContinuousOn φ (Set.Icc a b) := by
      apply Continuous.continuousOn
      exact (((continuous_const.mul (continuous_const.add continuous_id)).rpow_const
        fun _ => Or.inr hσ.le).sub continuous_const).sub
        (continuous_const.sub (continuous_id.div_const α))
    have hφa : φ a < 0 := by
      simp only [hφ, ha]
      rw [show β * (1 + (1 / β - 1)) = 1 by field_simp; ring, Real.one_rpow]
      have : (1 / β - 1) / α < θ * L := by
        rw [div_lt_iff₀ hα]
        nlinarith
      linarith
    have hφb : 0 < φ b := by
      simp only [hφ, hb]
      have hc := (div_lt_iff₀ (by positivity : 0 < α * β)).mp hcond
      have h1 : 1 < β * (1 + α * (θ * L)) := by nlinarith
      have := (one_lt_growth_iff hσ (by positivity)).mpr h1
      rw [show α * (θ * L) / α = θ * L by field_simp]
      linarith
    obtain ⟨r, hr, hφr⟩ := intermediate_value_Icc hab.le hcont ⟨hφa.le, hφb.le⟩
    have hra : a < r := by
      rcases eq_or_lt_of_le hr.1 with h | h
      · rw [← h] at hφr
        linarith
      · exact h
    have hrb : r < b := by
      rcases eq_or_lt_of_le hr.2 with h | h
      · rw [h] at hφr
        linarith
      · exact h
    refine ⟨r, θ * L - r / α, ⟨rfl, ?_⟩, ?_, by linarith⟩
    · simp only [hφ] at hφr
      linarith
    · have : r / α < θ * L := by
        rw [div_lt_iff₀ hα]
        linarith
      linarith

/-- **Finite utility on the balanced path iff `g < r`** (O&R omit this for `σ > 1`): with
aggregate consumption `C_t = C₀(1+g)ᵗ` and `1 + g = [β(1+r)]^σ`, lifetime utility is finite
iff `g < r`, equivalently `β(1+g)^{1-1/σ} < 1`. -/
theorem bgp_finite_iff {α β σ θ L r g C₀ : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hβ1 : β < 1)
    (hr : 0 < 1 + r) (hC₀ : 0 < C₀) (h : IsBGP α β σ θ L r g) :
    Summable (fun t : ℕ => β ^ t * crra σ (C₀ * (1 + g) ^ t)) ↔ g < r := by
  rw [h.euler, summable_balanced_iff hσ hβ hβ1 hr hC₀, ← h.euler]
  constructor <;> intro <;> linarith

/-- For `σ ≤ 1` and `g ≥ 0` the finiteness condition `g < r` holds automatically (O&R's
log case, p. 490). -/
theorem bgp_finite_of_sigma_le_one {α β σ θ L r g : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hβ : 0 < β) (hβ1 : β < 1) (hr : 0 < 1 + r) (hg : 0 ≤ g) (h : IsBGP α β σ θ L r g) :
    g < r := by
  have he := h.euler
  have h1 : 1 ≤ β * (1 + r) := by
    by_contra hlt
    push Not at hlt
    have : (β * (1 + r)) ^ σ < 1 := Real.rpow_lt_one (by positivity) hlt hσ
    linarith
  have h2 : (β * (1 + r)) ^ σ ≤ (β * (1 + r)) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h1 hσ1
  rw [Real.rpow_one] at h2
  nlinarith

/-- **Counterexample for `σ > 1`** (the finiteness condition O&R omit): `σ = 2`,
`β = 9/10`, `α = 1/3`, `θL = 36/25` give the interior balanced path `r = 1/3`,
`g = 11/25 > r` (both curves hold exactly), so household utility along it is infinite and
there is no balanced-growth equilibrium. -/
theorem bgp_infinite_utility_example :
    IsBGP (1 / 3) (9 / 10) 2 1 (36 / 25) (1 / 3) (11 / 25) ∧ (1 / 3 : ℝ) < 11 / 25 := by
  refine ⟨⟨by norm_num, ?_⟩, by norm_num⟩
  rw [Real.rpow_two]
  norm_num

/-- **The log case** O&R (95)–(96), p. 490: with `σ = 1`,
`r̄ = α(1 + θL - β)/(1 + αβ)` and `ḡ = (αβθL - (1-β))/(1 + αβ)`. -/
theorem bgp_log {α β θ L r g : ℝ} (hα : 0 < α) (hβ : 0 < β) (h : IsBGP α β 1 θ L r g) :
    r = α * (1 + θ * L - β) / (1 + α * β) ∧
      g = (α * β * θ * L - (1 - β)) / (1 + α * β) := by
  have he := h.euler
  rw [Real.rpow_one] at he
  have ht := h.tt
  have hαβ : 0 < 1 + α * β := by positivity
  have hr : r = α * (1 + θ * L - β) / (1 + α * β) := by
    rw [eq_div_iff hαβ.ne']
    have : g * α = θ * L * α - r := by rw [ht]; field_simp
    nlinarith
  refine ⟨hr, ?_⟩
  rw [ht, hr]
  field_simp
  ring

/-- Utility is finite in the log case: `r̄ - ḡ = (1-β)(αθL + 1 + α)/(1 + αβ) > 0`
(O&R (95)–(96)). -/
theorem bgp_log_r_sub_g {α β θ L r g : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1)
    (hθL : 0 < θ * L) (h : IsBGP α β 1 θ L r g) :
    r - g = (1 - β) * (α * θ * L + 1 + α) / (1 + α * β) ∧ g < r := by
  obtain ⟨hr, hg⟩ := bgp_log hα hβ h
  have hαβ : 0 < 1 + α * β := by positivity
  have e : r - g = (1 - β) * (α * θ * L + 1 + α) / (1 + α * β) := by
    rw [hr, hg]
    field_simp
    ring
  refine ⟨e, ?_⟩
  have : 0 < (1 - β) * (α * θ * L + 1 + α) / (1 + α * β) := by
    apply div_pos _ hαβ
    apply mul_pos (by linarith)
    nlinarith
  linarith

/-- **Scale effect** (O&R p. 491 and §7.3.3.6): for every `σ > 0`, a larger labour force
raises both the balanced interest rate and growth rate (the TT curve shifts up). -/
theorem bgp_mono_L {α β σ θ L₁ L₂ r₁ g₁ r₂ g₂ : ℝ} (hα : 0 < α) (hσ : 0 < σ) (hβ : 0 < β)
    (hθ : 0 < θ) (hL : L₁ < L₂) (h1 : IsBGP α β σ θ L₁ r₁ g₁) (h2 : IsBGP α β σ θ L₂ r₂ g₂)
    (hr₁ : 0 < 1 + r₁) (hr₂ : 0 < 1 + r₂) : r₁ < r₂ ∧ g₁ < g₂ := by
  have hr : r₁ < r₂ := by
    by_contra hle
    push Not at hle
    have hg : g₂ ≤ g₁ := by
      have := Real.rpow_le_rpow (by positivity : 0 ≤ β * (1 + r₂))
        (by nlinarith : β * (1 + r₂) ≤ β * (1 + r₁)) hσ.le
      linarith [h1.euler, h2.euler]
    have htt : g₁ < g₂ := by
      rw [h1.tt, h2.tt]
      have := div_le_div_of_nonneg_right hle hα.le
      nlinarith
    linarith
  exact ⟨hr, by linarith [euler_strictMono hσ hβ hr₁ hr, h1.euler, h2.euler]⟩

/-- **Integration raises growth and the interest rate above both autarky levels**
(O&R §7.3.3.6, p. 495): merging economies with labour forces `L, L* > 0` gives a balanced
interest rate above both autarky rates, and likewise for growth. -/
theorem merge_raises_growth {α β σ θ L L' r g r' g' rW gW : ℝ} (hα : 0 < α) (hσ : 0 < σ)
    (hβ : 0 < β) (hθ : 0 < θ) (hL : 0 < L) (hL' : 0 < L')
    (h : IsBGP α β σ θ L r g) (h' : IsBGP α β σ θ L' r' g')
    (hW : IsBGP α β σ θ (L + L') rW gW) (hr : 0 < 1 + r) (hr' : 0 < 1 + r')
    (hrW : 0 < 1 + rW) : max r r' < rW ∧ max g g' < gW := by
  obtain ⟨a1, b1⟩ := bgp_mono_L hα hσ hβ hθ (by linarith) h hW hr hrW
  obtain ⟨a2, b2⟩ := bgp_mono_L hα hσ hβ hθ (by linarith) h' hW hr' hrW
  exact ⟨max_lt a1 a2, max_lt b1 b2⟩

/-! ## The balanced-growth path is a competitive equilibrium (verification) -/

/-- The allocation and prices along a balanced growth path at `(r, g)` (O&R §7.3.3.3–7.3.3.4):
`L_Y = r/(θα)` (92), `K̄ = κ L_Y` (86), `p̄ = (1+r)/α` (87), `Π̄ = ((1-α)/α)K̄` (88),
`p_A = (1+r)Π̄/r` (89), `A_t = A₀(1+g)ᵗ`, the wage `w_t = (1-α) L_Y^{-α} A_t K̄^α` (91),
output `Y_t = L_Y^{1-α} A_t K̄^α` (fn 41), consumption `C_t = Y_t - A_{t+1}K̄` (the resource
constraint of p. 491), and household wealth `a_t = A_t(p̄K̄ + p_A)` (the value of the
intermediate-goods firms, including the capital they are about to sell). -/
structure BGPAllocation (α θ r g A₀ LY K p prof pA : ℝ) (A w Y C a : ℕ → ℝ) : Prop where
  hLY : LY = r / (θ * α)
  hK : K = kappa α r * LY
  hp : p = (1 + r) / α
  hprof : prof = (1 - α) / α * K
  hpA : pA = (1 + r) * prof / r
  hA : ∀ t, A t = A₀ * (1 + g) ^ t
  hw : ∀ t, w t = (1 - α) * (LY ^ (-α) * A t * K ^ α)
  hY : ∀ t, Y t = LY ^ (1 - α) * A t * K ^ α
  hC : ∀ t, C t = Y t - A (t + 1) * K
  ha : ∀ t, a t = A t * (p * K + pA)

namespace BGPAllocation

variable {α θ r g A₀ LY K p prof pA : ℝ} {A w Y C a : ℕ → ℝ}

/-- Scalar facts about a balanced allocation: `L_Y > 0`, `K̄ > 0`, `Y_t = A_t κ^α L_Y`,
`w_t = (1-α) A_t κ^α`, `p̄K̄ = α κ^α L_Y` (capital share) and `θ p_A = (1-α) κ^α` (91). -/
theorem facts (h : BGPAllocation α θ r g A₀ LY K p prof pA A w Y C a) (hα : 0 < α)
    (hα1 : α < 1) (hθ : 0 < θ) (hr : 0 < r) :
    0 < LY ∧ 0 < K ∧ (∀ t, Y t = A t * (kappa α r ^ α * LY)) ∧
      (∀ t, w t = (1 - α) * A t * kappa α r ^ α) ∧ p * K = α * kappa α r ^ α * LY ∧
      θ * pA = (1 - α) * kappa α r ^ α := by
  have hr1 : 0 < 1 + r := by linarith
  have hk := kappa_pos hα hr1
  have hid := kappa_identity hα hα1 hr1
  have hLY : 0 < LY := by rw [h.hLY]; positivity
  have hK : 0 < K := by rw [h.hK]; positivity
  have hwage : LY ^ (-α) * K ^ α = kappa α r ^ α := by
    rw [h.hK, Real.mul_rpow hk.le hLY.le, mul_left_comm, ← Real.rpow_add hLY, neg_add_cancel,
      Real.rpow_zero, mul_one]
  refine ⟨hLY, hK, fun t => ?_, fun t => ?_, ?_, ?_⟩
  · rw [h.hY t, mul_comm (LY ^ (1 - α)), mul_assoc, h.hK, scale_output hk hLY]
  · rw [h.hw t, mul_comm (LY ^ (-α)) (A t), mul_assoc, hwage]
    ring
  · have e : p * K = (1 + r) * kappa α r * LY / α := by
      rw [h.hp, h.hK]
      ring
    rw [e, hid]
    field_simp
  · have e : θ * pA = (1 - α) * ((1 + r) * kappa α r) / α ^ 2 := by
      rw [h.hpA, h.hprof, h.hK, h.hLY]
      field_simp
    rw [e, hid]
    field_simp

/-- **Firms optimise and blueprints are priced by free entry** (O&R (84)–(89)): at the
price `p̄ = α L_Y^{1-α} K̄^{α-1} = (1+r)/α` the final-goods producers demand `K̄`; `K̄`
maximises the monopolist's profit (85), which equals `Π̄`; and `p_A` is the present value
of `Π̄` forever. -/
theorem firms_optimal (h : BGPAllocation α θ r g A₀ LY K p prof pA A w Y C a) (hα : 0 < α)
    (hα1 : α < 1) (hθ : 0 < θ) (hr : 0 < r) :
    p = α * LY ^ (1 - α) * K ^ (α - 1) ∧
      (∀ x, 0 ≤ x → LY ^ (1 - α) * x ^ α - p * x ≤ LY ^ (1 - α) * K ^ α - p * K) ∧
      (∀ x, 0 ≤ x → monoProfit α r LY x ≤ prof) ∧
      HasSum (fun s : ℕ => prof * ((1 + r) ^ s)⁻¹) pA := by
  have hr1 : 0 < 1 + r := by linarith
  obtain ⟨hLY, hK, -, -, -, -⟩ := h.facts hα hα1 hθ hr
  have hprice : p = α * LY ^ (1 - α) * K ^ (α - 1) := by
    rw [h.hp, h.hK, monopoly_price hα hα1 hr1 hLY]
  refine ⟨hprice, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · rw [hprice]
    exact finalGoods_optimal hα hα1 hLY hK hx
  · rw [h.hprof, h.hK]
    exact monopoly_optimal hα hα1 hr1 hLY hx
  · rw [h.hpA]
    exact blueprint_price hr

/-- **Labour market and blueprint production** (O&R (81), (82), (90)–(92)): along a BGP
with `g ≥ 0`, `0 < L_Y ≤ L`, the R&D sector (`L_A = L - L_Y`) produces exactly
`A_{t+1} - A_t = θ A_t L_A`, and the R&D wage `p_A θ A_t` equals the final-goods wage
`w_t`. -/
theorem labour_market (h : BGPAllocation α θ r g A₀ LY K p prof pA A w Y C a) {β σ L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hθ : 0 < θ) (hr : 0 < r) (hg : 0 ≤ g)
    (hbgp : IsBGP α β σ θ L r g) :
    0 < LY ∧ LY ≤ L ∧ (∀ t, A (t + 1) - A t = θ * A t * (L - LY)) ∧
      ∀ t, pA * θ * A t = w t := by
  obtain ⟨hLY, -, -, hw, -, hlab⟩ := h.facts hα hα1 hθ hr
  have hgt : g = θ * (L - LY) := by
    rw [hbgp.tt, h.hLY]
    field_simp
  refine ⟨hLY, ?_, fun t => ?_, fun t => ?_⟩
  · by_contra hlt
    push Not at hlt
    have : θ * (L - LY) < 0 := mul_neg_of_pos_of_neg hθ (by linarith)
    linarith
  · rw [h.hA, h.hA, pow_succ, hgt]
    ring
  · rw [hw t]
    linear_combination (A t) * hlab

/-- **Goods market** (O&R p. 491): `C_t + A_{t+1}K̄ = Y_t`, consumption grows at `g`,
`C_t = C₀(1+g)ᵗ`, and is positive when `g < r`. -/
theorem goods_market (h : BGPAllocation α θ r g A₀ LY K p prof pA A w Y C a) (hα : 0 < α)
    (hα1 : α < 1) (hθ : 0 < θ) (hr : 0 < r) (hA₀ : 0 < A₀) (hgr : g < r) :
    (∀ t, C t + A (t + 1) * K = Y t) ∧ (∀ t, C t = C 0 * (1 + g) ^ t) ∧ 0 < C 0 := by
  have hr1 : 0 < 1 + r := by linarith
  obtain ⟨hLY, hK, hY, -, -, -⟩ := h.facts hα hα1 hθ hr
  have hid := kappa_identity hα hα1 hr1
  have hk := kappa_pos hα hr1
  have hCt : ∀ t, C t = A₀ * (kappa α r ^ α * LY - (1 + g) * K) * (1 + g) ^ t := by
    intro t
    rw [h.hC, hY, h.hA, h.hA, pow_succ]
    ring
  refine ⟨fun t => by rw [h.hC]; ring, fun t => by rw [hCt t, hCt 0, pow_zero, mul_one], ?_⟩
  rw [hCt 0, pow_zero, mul_one]
  apply mul_pos hA₀
  have hα2 : α ^ 2 < 1 := by nlinarith
  have hka : kappa α r ^ α = (1 + r) * kappa α r / α ^ 2 := by
    rw [hid]
    field_simp
  rw [hka, h.hK]
  have : (1 + g) * α ^ 2 < 1 + r := by nlinarith
  have hα2p : 0 < α ^ 2 := by positivity
  rw [sub_pos, div_mul_eq_mul_div, lt_div_iff₀ hα2p]
  nlinarith [mul_pos hk hLY]

/-- **The household budget holds** (O&R §7.3.3): with all assets earning `r`, wealth
`a_t = A_t(p̄K̄ + p_A)` evolves as `a_{t+1} = (1+r)(a_t + w_t L - C_t)`. The proof uses the
capital share `p̄K̄ = αY/A`, the wage bill, the R&D arbitrage `w_t = p_A θ A_t`, and the
no-arbitrage value of a firm `(1+r)(K̄ + p_A) = p̄K̄ + p_A`. -/
theorem budget (h : BGPAllocation α θ r g A₀ LY K p prof pA A w Y C a) {β σ L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hθ : 0 < θ) (hr : 0 < r) (hbgp : IsBGP α β σ θ L r g) :
    ∀ t, a (t + 1) = (1 + r) * a t + (1 + r) * (w t * L) - (1 + r) * C t := by
  intro t
  obtain ⟨hLY, hK, hY, hw, hpK, hlab⟩ := h.facts hα hα1 hθ hr
  have hgt : g = θ * (L - LY) := by
    rw [hbgp.tt, h.hLY]
    field_simp
  have hnoarb : (1 + r) * (K + pA) = p * K + pA := by
    rw [h.hpA, h.hprof, h.hp]
    field_simp
    ring
  rw [h.ha, h.ha, h.hC, hY, hw, h.hA, h.hA, pow_succ]
  have e : (1 - α) * kappa α r ^ α * L =
      (1 - α) * kappa α r ^ α * LY + θ * pA * (L - LY) := by
    rw [hlab]
    ring
  linear_combination (A₀ * (1 + g) ^ t) * (-(1 + r) * e + (1 + r) * pA * hgt -
    (1 + r) * hpK - (1 + g) * hnoarb)

/-- **The household's plan is optimal** (O&R (94), with the genuine infinite horizon): along
a BGP with `g < r`, consumption `C_t = C₀(1+g)ᵗ` has finite utility and maximises
`∑ βᵗ u(C_t)` among all plans with nonnegative wealth that satisfy the budget
`a_{t+1} = (1+r)(a_t + w_t L - C_t)` from the same initial wealth. -/
theorem household_optimal (h : BGPAllocation α θ r g A₀ LY K p prof pA A w Y C a)
    {β σ L : ℝ} (hα : 0 < α) (hα1 : α < 1) (hθ : 0 < θ) (hr : 0 < r) (hσ : 0 < σ)
    (hβ : 0 < β) (hβ1 : β < 1) (hA₀ : 0 < A₀) (hgr : g < r) (hbgp : IsBGP α β σ θ L r g) :
    Summable (fun t => β ^ t * crra σ (C t)) ∧
      ∀ a' C' : ℕ → ℝ, a' 0 = a 0 → (∀ t, 0 ≤ a' t) → (∀ t, 0 < C' t) →
        Budget (1 + r) (1 + r) (fun t => (1 + r) * (w t * L)) C' a' →
        Summable (fun t => β ^ t * crra σ (C' t)) →
        ∑' t, β ^ t * crra σ (C' t) ≤ ∑' t, β ^ t * crra σ (C t) := by
  have hr1 : 0 < 1 + r := by linarith
  obtain ⟨-, hCg, hC0⟩ := h.goods_market hα hα1 hθ hr hA₀ hgr
  have hG : 0 < 1 + g := by rw [hbgp.euler]; exact Real.rpow_pos_of_pos (by positivity) σ
  have hCt : ∀ t, C t = C 0 * ((β * (1 + r)) ^ σ) ^ t := fun t => by rw [hCg t, hbgp.euler]
  have hfun : (fun t => β ^ t * crra σ (C t)) =
      fun t => β ^ t * crra σ (C 0 * ((β * (1 + r)) ^ σ) ^ t) := by
    funext t
    rw [hCt t]
  have hsum : Summable (fun t => β ^ t * crra σ (C t)) := by
    rw [hfun, summable_balanced_iff hσ hβ hβ1 hr1 hC0, ← hbgp.euler]
    linarith
  refine ⟨hsum, fun a' C' h0 ha' hC' hb' hs' => ?_⟩
  have hbud : Budget (1 + r) (1 + r) (fun t => (1 + r) * (w t * L)) C a :=
    fun t => h.budget hα hα1 hθ hr hbgp t
  have heuler : ∀ t, β ^ t * crraMU σ (C t) =
      crraMU σ (C 0) / (1 + r) * (1 + r) * ((1 + r) ^ t)⁻¹ := by
    intro t
    rw [div_mul_cancel₀ _ hr1.ne', hCt t]
    have := balanced_euler hσ hβ hr1 hC0 t
    rwa [mul_one] at this
  have hA : ∀ t, a t = A₀ * (p * K + pA) * (1 + g) ^ t := fun t => by
    rw [h.ha, h.hA]
    ring
  have htail := balanced_tail (lam := crraMU σ (C 0) / (1 + r)) (k₀ := A₀ * (p * K + pA))
    hr1 hG (by linarith)
  have htail' : Tendsto (fun T : ℕ => crraMU σ (C 0) / (1 + r) *
      ((1 + r) * (((1 + r) ^ T)⁻¹ * a T))) atTop (𝓝 0) := by
    refine htail.congr fun T => ?_
    rw [hA T]
  have := tsum_add_le_of_partial (δ := 0) (N := 0) hs' hsum htail' fun T _ => by
    rw [add_zero]
    exact welfare_partial_le hβ.le hr1 (div_nonneg (crraMU_pos σ hC0).le hr1.le)
      (fun t => crra_support hσ (hC' t) (by rw [hCg t]; positivity)) heuler hb' hbud h0 T
      (ha' T)
  rwa [add_zero] at this

end BGPAllocation

/-! ## The social planner: closed-form Bellman verification (fn 42, (97), Exercise 3) -/

/-- Planner's output with `X = A K` total capital, O&R p. 491: `Y = L_Y^{1-α} A K^α`
`= A^{1-α} X^α L_Y^{1-α}`. -/
noncomputable def plannerOutput (α A X ℓ : ℝ) : ℝ := A ^ (1 - α) * X ^ α * ℓ ^ (1 - α)

/-- The planner's production function in O&R's form: `L_Y^{1-α} A (X/A)^α` equals
`A^{1-α} X^α L_Y^{1-α}` (p. 491, `K = X/A` per blueprint). -/
theorem plannerOutput_eq_book {α A X ℓ : ℝ} (hA : 0 < A) (hX : 0 ≤ X) :
    ℓ ^ (1 - α) * A * (X / A) ^ α = plannerOutput α A X ℓ := by
  unfold plannerOutput
  rw [Real.div_rpow hX hA.le, Real.rpow_sub hA, Real.rpow_one]
  field_simp

/-- Output is positive. -/
theorem plannerOutput_pos {α A X ℓ : ℝ} (hA : 0 < A) (hX : 0 < X) (hℓ : 0 < ℓ) :
    0 < plannerOutput α A X ℓ := by
  unfold plannerOutput
  positivity

/-- Log output: `log Y = (1-α) log A + α log X + (1-α) log L_Y`. -/
theorem log_plannerOutput {α A X ℓ : ℝ} (hA : 0 < A) (hX : 0 < X) (hℓ : 0 < ℓ) :
    Real.log (plannerOutput α A X ℓ) =
      (1 - α) * Real.log A + α * Real.log X + (1 - α) * Real.log ℓ := by
  unfold plannerOutput
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_rpow hA, Real.log_rpow hX, Real.log_rpow hℓ]

/-- The planner's final-goods labour, O&R fn 42 / Exercise 3:
`L_Y^{PLAN} = (1-β)(1+θL)/θ`. -/
noncomputable def ellStar (β θ L : ℝ) : ℝ := (1 - β) * (1 + θ * L) / θ

/-- Coefficient on `log A` in the planner's value function. -/
noncomputable def coefA (α β : ℝ) : ℝ := (1 - α) / ((1 - β) * (1 - α * β))

/-- Coefficient on `log X` in the planner's value function. -/
noncomputable def coefX (α β : ℝ) : ℝ := α / (1 - α * β)

/-- Constant term of the planner's value function. -/
noncomputable def plannerConst (α β θ L : ℝ) : ℝ :=
  (Real.log (1 - α * β) + α * β / (1 - α * β) * Real.log (α * β) +
    (1 - α) / (1 - α * β) * Real.log (ellStar β θ L) +
    β * coefA α β * Real.log (β * (1 + θ * L))) / (1 - β)

/-- **The planner's value function** (closed form, log utility):
`V(A, X) = κ + a log A + b log X` with `a = (1-α)/((1-β)(1-αβ))` and `b = α/(1-αβ)`. -/
noncomputable def plannerValue (α β θ L A X : ℝ) : ℝ :=
  plannerConst α β θ L + coefA α β * Real.log A + coefX α β * Real.log X

/-- Slack of the saving choice `X' = x` out of output `Y`, relative to the optimum
`X' = αβY`. -/
noncomputable def savingSlack (α β Y x : ℝ) : ℝ :=
  Real.log ((1 - α * β) * Y) + α * β / (1 - α * β) * Real.log (α * β * Y) -
    (Real.log (Y - x) + α * β / (1 - α * β) * Real.log x)

/-- Slack of the labour allocation `L_Y = ℓ` relative to `ℓ* = (1-β)(1+θL)/θ`. -/
noncomputable def labourSlack (β θ L ℓ : ℝ) : ℝ :=
  Real.log (ellStar β θ L) + β / (1 - β) * Real.log (β * (1 + θ * L)) -
    (Real.log ℓ + β / (1 - β) * Real.log (1 + θ * (L - ℓ)))

/-- **Optimal saving** (planner, log utility): `savingSlack ≥ 0`, with equality only at
`X' = αβY`. -/
theorem savingSlack_nonneg {α β Y x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hab1 : α * β < 1)
    (hY : 0 < Y) (hx : 0 < x) (hxY : x < Y) :
    0 ≤ savingSlack α β Y x ∧ (x ≠ α * β * Y → 0 < savingSlack α β Y x) := by
  have hab : 0 < α * β := mul_pos hα hβ
  have h1a : 0 < 1 - α * β := by linarith
  have hy1 : 0 < (1 - α * β) * Y := by positivity
  have hy2 : 0 < α * β * Y := by positivity
  have hm : 0 < α * β / (1 - α * β) := by positivity
  have l1 := Real.log_le_sub_one_of_pos (div_pos (sub_pos.mpr hxY) hy1)
  rw [Real.log_div (sub_pos.mpr hxY).ne' hy1.ne'] at l1
  have hsum : ((Y - x) / ((1 - α * β) * Y) - 1) +
      α * β / (1 - α * β) * (x / (α * β * Y) - 1) = 0 := by
    field_simp
    ring
  unfold savingSlack
  constructor
  · have l2 := Real.log_le_sub_one_of_pos (div_pos hx hy2)
    rw [Real.log_div hx.ne' hy2.ne'] at l2
    nlinarith [mul_le_mul_of_nonneg_left l2 hm.le]
  · intro hne
    have hx1 : x / (α * β * Y) ≠ 1 := by
      intro h
      apply hne
      rw [div_eq_one_iff_eq hy2.ne'] at h
      exact h
    have l2 := Real.log_lt_sub_one_of_pos (div_pos hx hy2) hx1
    rw [Real.log_div hx.ne' hy2.ne'] at l2
    nlinarith [mul_lt_mul_of_pos_left l2 hm]

/-- **Optimal R&D allocation** (planner): `labourSlack ≥ 0` on `0 < ℓ ≤ L`, with equality
only at `ℓ = ℓ*`. -/
theorem labourSlack_nonneg {β θ L ℓ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ)
    (hL : 0 < L) (hℓ : 0 < ℓ) (hℓL : ℓ ≤ L) :
    0 ≤ labourSlack β θ L ℓ ∧ (ℓ ≠ ellStar β θ L → 0 < labourSlack β θ L ℓ) := by
  have hs : 0 < ellStar β θ L := by
    unfold ellStar
    exact div_pos (mul_pos (by linarith) (by positivity)) hθ
  have hm : 0 < 1 + θ * (L - ℓ) := by nlinarith
  have hms : 0 < β * (1 + θ * L) := by positivity
  have hq : 0 < β / (1 - β) := div_pos hβ (by linarith)
  have hsum : (ℓ / ellStar β θ L - 1) + β / (1 - β) * ((1 + θ * (L - ℓ)) /
      (β * (1 + θ * L)) - 1) = 0 := by
    have h1b : (1 - β) ≠ 0 := by linarith
    have h1t : (1 + θ * L) ≠ 0 := by positivity
    unfold ellStar
    field_simp
    ring
  have l1 := Real.log_le_sub_one_of_pos (div_pos hm hms)
  rw [Real.log_div hm.ne' hms.ne'] at l1
  unfold labourSlack
  constructor
  · have l2 := Real.log_le_sub_one_of_pos (div_pos hℓ hs)
    rw [Real.log_div hℓ.ne' hs.ne'] at l2
    nlinarith [mul_le_mul_of_nonneg_left l1 hq.le]
  · intro hne
    have hx1 : ℓ / ellStar β θ L ≠ 1 := by
      intro h
      apply hne
      rw [div_eq_one_iff_eq hs.ne'] at h
      exact h
    have l2 := Real.log_lt_sub_one_of_pos (div_pos hℓ hs) hx1
    rw [Real.log_div hℓ.ne' hs.ne'] at l2
    nlinarith [mul_le_mul_of_nonneg_left l1 hq.le]

/-- **The Bellman equation, exactly** (O&R fn 42 made rigorous): for `A, X > 0`,
`0 < ℓ ≤ L` and `0 < X' < Y = A^{1-α}X^αℓ^{1-α}`,
`V(A, X) - [log(Y - X') + β V(A(1+θ(L-ℓ)), X')] = savingSlack + ((1-α)/(1-αβ)) labourSlack`.
Hence `V` satisfies the Bellman equation with the policy `X' = αβY`, `L_Y = ℓ*`. -/
theorem bellman_gap {α β θ L A X ℓ x : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hA : 0 < A) (hX : 0 < X) (hℓ : 0 < ℓ) (hℓL : ℓ ≤ L) :
    plannerValue α β θ L A X - (Real.log (plannerOutput α A X ℓ - x) +
        β * plannerValue α β θ L (A * (1 + θ * (L - ℓ))) x) =
      savingSlack α β (plannerOutput α A X ℓ) x +
        (1 - α) / (1 - α * β) * labourSlack β θ L ℓ := by
  have hY := plannerOutput_pos (α := α) hA hX hℓ
  have hm : 0 < 1 + θ * (L - ℓ) := by nlinarith
  have hab : 0 < α * β := mul_pos hα hβ
  have hab1 : α * β < 1 := by nlinarith
  have h1a : 0 < 1 - α * β := by linarith
  have h1b : 0 < 1 - β := by linarith
  unfold plannerValue savingSlack labourSlack plannerConst coefA coefX
  rw [Real.log_mul hA.ne' hm.ne', Real.log_mul h1a.ne' hY.ne', Real.log_mul hab.ne' hY.ne',
    log_plannerOutput hA hX hℓ]
  field_simp
  ring

/-- A **feasible plan for the Romer planner** (O&R p. 491): capital `X_t = A_t K_t > 0`,
final-goods labour `0 < L_{Y,t} ≤ L`, consumption `C_t > 0`, the resource constraint
`C_t + X_{t+1} = Y_t` (100% depreciation, `A_{t+1}K_{t+1} = X_{t+1}`), and the R&D technology
(81) `A_{t+1} = A_t(1 + θ L_{A,t})` with `L_{A,t} = L - L_{Y,t}` (82). -/
structure PlannerFeasible (α θ L A₀ X₀ : ℝ) (A X ℓ C : ℕ → ℝ) : Prop where
  initA : A 0 = A₀
  initX : X 0 = X₀
  posX : ∀ t, 0 < X t
  labourPos : ∀ t, 0 < ℓ t
  labourLe : ∀ t, ℓ t ≤ L
  posC : ∀ t, 0 < C t
  resource : ∀ t, C t + X (t + 1) = plannerOutput α (A t) (X t) (ℓ t)
  research : ∀ t, A (t + 1) = A t * (1 + θ * (L - ℓ t))

/-- Blueprints never decline on a feasible plan: `A₀ ≤ A_t`, so `A_t > 0`. -/
theorem PlannerFeasible.A_ge {α θ L A₀ X₀ : ℝ} {A X ℓ C : ℕ → ℝ}
    (hf : PlannerFeasible α θ L A₀ X₀ A X ℓ C) (hA₀ : 0 < A₀) (hθ : 0 < θ) (t : ℕ) :
    A₀ ≤ A t := by
  induction t with
  | zero => rw [hf.initA]
  | succ t ih =>
    rw [hf.research t]
    have h1 : 1 ≤ 1 + θ * (L - ℓ t) := by
      have := hf.labourLe t
      nlinarith
    nlinarith

/-- The one-period Bellman slack of a plan at date `t`:
`V(A_t, X_t) - [log C_t + β V(A_{t+1}, X_{t+1})]`. -/
noncomputable def planGap (α β θ L : ℝ) (A X C : ℕ → ℝ) (t : ℕ) : ℝ :=
  plannerValue α β θ L (A t) (X t) -
    (Real.log (C t) + β * plannerValue α β θ L (A (t + 1)) (X (t + 1)))

/-- On a feasible plan the Bellman slack is the sum of the saving and labour slacks,
hence nonnegative, and zero only if `X_{t+1} = αβY_t` and `L_{Y,t} = ℓ*`. -/
theorem PlannerFeasible.gap_eq {α β θ L A₀ X₀ : ℝ} {A X ℓ C : ℕ → ℝ}
    (hf : PlannerFeasible α θ L A₀ X₀ A X ℓ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hA₀ : 0 < A₀) (t : ℕ) :
    planGap α β θ L A X C t = savingSlack α β (plannerOutput α (A t) (X t) (ℓ t)) (X (t + 1)) +
      (1 - α) / (1 - α * β) * labourSlack β θ L (ℓ t) := by
  have hA := lt_of_lt_of_le hA₀ (hf.A_ge hA₀ hθ t)
  unfold planGap
  rw [← bellman_gap hα hα1 hβ hβ1 hθ hA (hf.posX t) (hf.labourPos t) (hf.labourLe t),
    ← hf.research t, show C t = plannerOutput α (A t) (X t) (ℓ t) - X (t + 1) by
      linarith [hf.resource t]]

/-- The Bellman slack is nonnegative on a feasible plan; it is strictly positive whenever
the plan deviates from the policy `X_{t+1} = αβY_t`, `L_{Y,t} = ℓ*` at `t`. -/
theorem PlannerFeasible.gap_nonneg {α β θ L A₀ X₀ : ℝ} {A X ℓ C : ℕ → ℝ}
    (hf : PlannerFeasible α θ L A₀ X₀ A X ℓ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hL : 0 < L) (hA₀ : 0 < A₀) (t : ℕ) :
    0 ≤ planGap α β θ L A X C t ∧
      (planGap α β θ L A X C t = 0 →
        ℓ t = ellStar β θ L ∧ X (t + 1) = α * β * plannerOutput α (A t) (X t) (ℓ t)) := by
  have hA := lt_of_lt_of_le hA₀ (hf.A_ge hA₀ hθ t)
  have hY := plannerOutput_pos (α := α) hA (hf.posX t) (hf.labourPos t)
  have hxY : X (t + 1) < plannerOutput α (A t) (X t) (ℓ t) := by
    linarith [hf.resource t, hf.posC t]
  have hab1 : α * β < 1 := by nlinarith
  obtain ⟨s1, s1'⟩ := savingSlack_nonneg hα hβ hab1 hY (hf.posX (t + 1)) hxY
  obtain ⟨s2, s2'⟩ := labourSlack_nonneg hβ hβ1 hθ hL (hf.labourPos t) (hf.labourLe t)
  have hn : 0 < (1 - α) / (1 - α * β) := div_pos (by linarith) (by linarith)
  rw [hf.gap_eq hα hα1 hβ hβ1 hθ hA₀ t]
  refine ⟨by positivity, fun h0 => ⟨?_, ?_⟩⟩
  · by_contra hne
    have := s2' hne
    nlinarith [mul_pos hn this]
  · by_contra hne
    have := s1' hne
    nlinarith [mul_nonneg hn.le s2]

/-- Discounted telescoping of Bellman slacks: for any sequences,
`∑_{t<T} βᵗ u_t + βᵀ v_T + ∑_{t<T} βᵗ (v_t - u_t - β v_{t+1}) = v_0`. -/
theorem telescope_bellman (β : ℝ) (u v : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ range T, β ^ t * u t + β ^ T * v T +
      ∑ t ∈ range T, β ^ t * (v t - (u t + β * v (t + 1))) = v 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, sum_range_succ, ← ih, pow_succ]
    ring

/-- **Lower bound on continuation values** of any feasible plan (the unbounded-below tail):
`V(A_T, X_T) ≥ κ + c_A log A₀ + (log C_T - (1-α) log L)/(1-αβ)` with
`c_A = (1-α)β/((1-β)(1-αβ)) ≥ 0`, because `C_T < Y_T ≤ A_T^{1-α} X_T^α L^{1-α}`. -/
theorem PlannerFeasible.value_lower {α β θ L A₀ X₀ : ℝ} {A X ℓ C : ℕ → ℝ}
    (hf : PlannerFeasible α θ L A₀ X₀ A X ℓ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hA₀ : 0 < A₀) (T : ℕ) :
    plannerConst α β θ L + (1 - α) * β / ((1 - β) * (1 - α * β)) * Real.log A₀ +
        (Real.log (C T) - (1 - α) * Real.log L) / (1 - α * β) ≤
      plannerValue α β θ L (A T) (X T) := by
  have hAge := hf.A_ge hA₀ hθ T
  have hA := lt_of_lt_of_le hA₀ hAge
  have hX := hf.posX T
  have hℓ := hf.labourPos T
  have hab1 : α * β < 1 := by nlinarith
  have h1a : 0 < 1 - α * β := by linarith
  have h1b : 0 < 1 - β := by linarith
  have hCY : Real.log (C T) ≤ Real.log (plannerOutput α (A T) (X T) (ℓ T)) :=
    Real.log_le_log (hf.posC T) (by linarith [hf.resource T, hf.posX (T + 1)])
  rw [log_plannerOutput hA hX hℓ] at hCY
  have hlogℓ : Real.log (ℓ T) ≤ Real.log L := Real.log_le_log hℓ (hf.labourLe T)
  have hlogA : Real.log A₀ ≤ Real.log (A T) := Real.log_le_log hA₀ hAge
  have key : Real.log (C T) - (1 - α) * Real.log L ≤
      (1 - α) * Real.log (A T) + α * Real.log (X T) := by nlinarith
  have hcA : 0 ≤ (1 - α) * β / ((1 - β) * (1 - α * β)) := by
    apply div_nonneg _ (by positivity)
    nlinarith
  unfold plannerValue coefA coefX
  have e : (1 - α) / ((1 - β) * (1 - α * β)) * Real.log (A T) + α / (1 - α * β) *
      Real.log (X T) = (1 - α) * β / ((1 - β) * (1 - α * β)) * Real.log (A T) +
      ((1 - α) * Real.log (A T) + α * Real.log (X T)) / (1 - α * β) := by
    field_simp
    ring
  have h2 : (Real.log (C T) - (1 - α) * Real.log L) / (1 - α * β) ≤
      ((1 - α) * Real.log (A T) + α * Real.log (X T)) / (1 - α * β) :=
    div_le_div_of_nonneg_right key h1a.le
  have h3 := mul_le_mul_of_nonneg_left hlogA hcA
  linarith

/-- **Optimality of the policy, genuine infinite horizon** (O&R fn 42, (97), Exercise 3):
for every feasible plan with convergent utility and every date `t₀`,
`∑ βᵗ log C_t + β^{t₀}·(Bellman slack at t₀) ≤ V(A₀, X₀)`. In particular
`∑ βᵗ log C_t ≤ V(A₀, X₀)`. -/
theorem planner_tsum_le {α β θ L A₀ X₀ : ℝ} {A X ℓ C : ℕ → ℝ}
    (hf : PlannerFeasible α θ L A₀ X₀ A X ℓ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hL : 0 < L) (hA₀ : 0 < A₀)
    (hs : Summable (fun t => β ^ t * Real.log (C t))) (t₀ : ℕ) :
    ∑' t, β ^ t * Real.log (C t) + β ^ t₀ * planGap α β θ L A X C t₀ ≤
      plannerValue α β θ L A₀ X₀ := by
  set κ0 := plannerConst α β θ L + (1 - α) * β / ((1 - β) * (1 - α * β)) * Real.log A₀ -
    (1 - α) * Real.log L / (1 - α * β) with hκ0
  have hab1 : α * β < 1 := by nlinarith
  have h1a : 0 < 1 - α * β := by linarith
  set low : ℕ → ℝ := fun T => β ^ T * κ0 + (β ^ T * Real.log (C T)) / (1 - α * β) with hlow
  have hlowlim : Tendsto low atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℕ => β ^ T * κ0) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const κ0
    have h2 := (hs.tendsto_atTop_zero).div_const (1 - α * β)
    rw [zero_div] at h2
    simpa using h1.add h2
  have hpart : ∀ T, t₀ < T → ∑ t ∈ range T, β ^ t * Real.log (C t) +
      β ^ t₀ * planGap α β θ L A X C t₀ ≤ plannerValue α β θ L A₀ X₀ - low T := by
    intro T hT
    have htel := telescope_bellman β (fun t => Real.log (C t))
      (fun t => plannerValue α β θ L (A t) (X t)) T
    simp only [hf.initA, hf.initX] at htel
    have hsingle := single_le_sum (f := fun t => β ^ t * planGap α β θ L A X C t)
      (fun t _ => mul_nonneg (pow_nonneg hβ.le t)
        (hf.gap_nonneg hα hα1 hβ hβ1 hθ hL hA₀ t).1) (mem_range.mpr hT)
    have hlowT := hf.value_lower hα hα1 hβ hβ1 hθ hA₀ T
    have hlowT' : low T ≤ β ^ T * plannerValue α β θ L (A T) (X T) := by
      simp only [hlow, hκ0]
      have := mul_le_mul_of_nonneg_left hlowT (pow_nonneg hβ.le T)
      have e : β ^ T * (plannerConst α β θ L + (1 - α) * β / ((1 - β) * (1 - α * β)) *
          Real.log A₀ + (Real.log (C T) - (1 - α) * Real.log L) / (1 - α * β)) =
          β ^ T * (plannerConst α β θ L + (1 - α) * β / ((1 - β) * (1 - α * β)) *
          Real.log A₀ - (1 - α) * Real.log L / (1 - α * β)) +
          β ^ T * Real.log (C T) / (1 - α * β) := by ring
      linarith
    unfold planGap at hsingle ⊢
    linarith
  have h1 := (hs.hasSum.tendsto_sum_nat).add_const (β ^ t₀ * planGap α β θ L A X C t₀)
  have h2 := hlowlim.const_sub (plannerValue α β θ L A₀ X₀)
  rw [sub_zero] at h2
  exact le_of_tendsto_of_tendsto h1 h2 (eventually_atTop.2 ⟨t₀ + 1, fun T hT => hpart T hT⟩)

/-- **Uniqueness of the planner's optimum**: a feasible plan with convergent utility that
attains `V(A₀, X₀)` follows the policy at every date: `L_{Y,t} = ℓ*` and
`X_{t+1} = αβ Y_t`. -/
theorem planner_policy_of_optimal {α β θ L A₀ X₀ : ℝ} {A X ℓ C : ℕ → ℝ}
    (hf : PlannerFeasible α θ L A₀ X₀ A X ℓ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hL : 0 < L) (hA₀ : 0 < A₀)
    (hs : Summable (fun t => β ^ t * Real.log (C t)))
    (hopt : plannerValue α β θ L A₀ X₀ ≤ ∑' t, β ^ t * Real.log (C t)) (t : ℕ) :
    ℓ t = ellStar β θ L ∧ X (t + 1) = α * β * plannerOutput α (A t) (X t) (ℓ t) := by
  have h := planner_tsum_le hf hα hα1 hβ hβ1 hθ hL hA₀ hs t
  obtain ⟨hnn, himp⟩ := hf.gap_nonneg hα hα1 hβ hβ1 hθ hL hA₀ t
  apply himp
  have hβt : 0 < β ^ t := pow_pos hβ t
  by_contra hne
  have := mul_pos hβt (lt_of_le_of_ne hnn (Ne.symm hne))
  linarith

/-- The planner's blueprint path: `A_t = A₀ [β(1+θL)]ᵗ`. -/
noncomputable def plannerA (β θ L A₀ : ℝ) (t : ℕ) : ℝ := A₀ * (β * (1 + θ * L)) ^ t

/-- The planner's capital path: `X_0 = X₀`, `X_{t+1} = αβ Y_t` with `L_Y = ℓ*`. -/
noncomputable def plannerX (α β θ L A₀ X₀ : ℝ) : ℕ → ℝ
  | 0 => X₀
  | t + 1 => α * β * plannerOutput α (plannerA β θ L A₀ t) (plannerX α β θ L A₀ X₀ t)
      (ellStar β θ L)

/-- The planner's consumption path `C_t = (1 - αβ) Y_t`. -/
noncomputable def plannerC (α β θ L A₀ X₀ : ℝ) (t : ℕ) : ℝ :=
  (1 - α * β) * plannerOutput α (plannerA β θ L A₀ t) (plannerX α β θ L A₀ X₀ t)
    (ellStar β θ L)

/-- The planner's R&D is interior (`0 < ℓ* < L`) iff `βθL > 1 - β`, i.e. iff planned growth
(97) is positive. -/
theorem ellStar_lt_iff {β θ L : ℝ} (hθ : 0 < θ) :
    ellStar β θ L < L ↔ 1 - β < β * θ * L := by
  unfold ellStar
  rw [div_lt_iff₀ hθ]
  constructor <;> intro h <;> nlinarith

/-- `1 + θ(L - ℓ*) = β(1+θL)`: the planner's blueprint growth factor. -/
theorem research_factor {β θ L : ℝ} (hθ : 0 < θ) :
    1 + θ * (L - ellStar β θ L) = β * (1 + θ * L) := by
  unfold ellStar
  field_simp
  ring

/-- The planner's capital stays positive. -/
theorem plannerX_pos {α β θ L A₀ X₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hL : 0 < L) (hA₀ : 0 < A₀) (hX₀ : 0 < X₀) (t : ℕ) :
    0 < plannerX α β θ L A₀ X₀ t := by
  have hs : 0 < ellStar β θ L := by
    unfold ellStar
    exact div_pos (mul_pos (by linarith) (by positivity)) hθ
  induction t with
  | zero => exact hX₀
  | succ t ih =>
    simp only [plannerX]
    have : 0 < plannerA β θ L A₀ t := by unfold plannerA; positivity
    have := plannerOutput_pos (α := α) this ih hs
    positivity

/-- **The candidate plan is feasible** when the planner's R&D is interior. -/
theorem planner_candidate_feasible {α β θ L A₀ X₀ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ) (hL : 0 < L) (hA₀ : 0 < A₀) (hX₀ : 0 < X₀)
    (hint : 1 - β < β * θ * L) :
    PlannerFeasible α θ L A₀ X₀ (plannerA β θ L A₀) (plannerX α β θ L A₀ X₀)
      (fun _ => ellStar β θ L) (plannerC α β θ L A₀ X₀) := by
  have hs : 0 < ellStar β θ L := by
    unfold ellStar
    exact div_pos (mul_pos (by linarith) (by positivity)) hθ
  have hab1 : α * β < 1 := by nlinarith
  refine ⟨by simp [plannerA], rfl, plannerX_pos hα hβ hβ1 hθ hL hA₀ hX₀, fun _ => hs,
    fun _ => ((ellStar_lt_iff hθ).mpr hint).le, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · unfold plannerC
    have : 0 < plannerA β θ L A₀ t := by unfold plannerA; positivity
    have := plannerOutput_pos (α := α) this (plannerX_pos hα hβ hβ1 hθ hL hA₀ hX₀ t) hs
    have : 0 < 1 - α * β := by linarith
    positivity
  · simp only [plannerC, plannerX]
    ring
  · simp only [plannerA]
    rw [research_factor hθ, pow_succ]
    ring

/-- The candidate follows the policy, so every Bellman slack is zero. -/
theorem planner_candidate_gap {α β θ L A₀ X₀ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ) (hL : 0 < L) (hA₀ : 0 < A₀) (hX₀ : 0 < X₀)
    (hint : 1 - β < β * θ * L) (t : ℕ) :
    planGap α β θ L (plannerA β θ L A₀) (plannerX α β θ L A₀ X₀) (plannerC α β θ L A₀ X₀) t
      = 0 := by
  have hf := planner_candidate_feasible hα hα1 hβ hβ1 hθ hL hA₀ hX₀ hint
  rw [hf.gap_eq hα hα1 hβ hβ1 hθ hA₀ t]
  simp only [savingSlack, labourSlack, plannerX]
  rw [research_factor hθ, show plannerOutput α (plannerA β θ L A₀ t)
    (plannerX α β θ L A₀ X₀ t) (ellStar β θ L) - α * β * plannerOutput α (plannerA β θ L A₀ t)
    (plannerX α β θ L A₀ X₀ t) (ellStar β θ L) = (1 - α * β) * plannerOutput α
    (plannerA β θ L A₀ t) (plannerX α β θ L A₀ X₀ t) (ellStar β θ L) by ring]
  ring

/-- Capital per blueprint `K_t = X_t/A_t` on the planner's path. -/
noncomputable def plannerK (α β θ L A₀ X₀ : ℝ) (t : ℕ) : ℝ :=
  plannerX α β θ L A₀ X₀ t / plannerA β θ L A₀ t

/-- The constant of the planner's capital dynamics, `c = (α/(1+θL)) ℓ*^{1-α}`. -/
noncomputable def plannerKc (α β θ L : ℝ) : ℝ := α / (1 + θ * L) * ellStar β θ L ^ (1 - α)

/-- **Planner's capital dynamics**: `K_{t+1} = c K_t^α`. -/
theorem plannerK_succ {α β θ L A₀ X₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hL : 0 < L) (hA₀ : 0 < A₀) (hX₀ : 0 < X₀) (t : ℕ) :
    plannerK α β θ L A₀ X₀ (t + 1) = plannerKc α β θ L * plannerK α β θ L A₀ X₀ t ^ α := by
  have hA : 0 < plannerA β θ L A₀ t := by unfold plannerA; positivity
  have hX := plannerX_pos hα hβ hβ1 hθ hL hA₀ hX₀ t
  unfold plannerK plannerKc
  simp only [plannerX]
  rw [show plannerA β θ L A₀ (t + 1) = plannerA β θ L A₀ t * (β * (1 + θ * L)) by
    simp only [plannerA]; rw [pow_succ]; ring]
  unfold plannerOutput
  rw [Real.div_rpow hX.le hA.le, Real.rpow_sub hA, Real.rpow_one]
  field_simp

/-- **Closed form for log capital per blueprint**: `log K_t = ℓk + αᵗ(log K_0 - ℓk)` with
`ℓk = log c/(1-α)`. -/
theorem plannerK_log {α β θ L A₀ X₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hL : 0 < L) (hA₀ : 0 < A₀) (hX₀ : 0 < X₀) (t : ℕ) :
    Real.log (plannerK α β θ L A₀ X₀ t) = Real.log (plannerKc α β θ L) / (1 - α) +
      α ^ t * (Real.log (plannerK α β θ L A₀ X₀ 0) - Real.log (plannerKc α β θ L) / (1 - α)) := by
  have hs : 0 < ellStar β θ L := by
    unfold ellStar
    exact div_pos (mul_pos (by linarith) (by positivity)) hθ
  have hc : 0 < plannerKc α β θ L := by unfold plannerKc; positivity
  have hK : ∀ t, 0 < plannerK α β θ L A₀ X₀ t := fun t => by
    unfold plannerK plannerA
    have := plannerX_pos hα hβ hβ1 hθ hL hA₀ hX₀ t
    positivity
  induction t with
  | zero => simp
  | succ t ih =>
    have h1a : (1 - α) ≠ 0 := by linarith
    rw [plannerK_succ hα hβ hβ1 hθ hL hA₀ hX₀ t, Real.log_mul hc.ne'
      (Real.rpow_pos_of_pos (hK t) α).ne', Real.log_rpow (hK t), ih, pow_succ]
    field_simp
    ring

/-- The planner's steady-state capital per blueprint, O&R fn 42:
`K^{PLAN} = α^{1/(1-α)} ((1-β)/θ) (1+θL)^{α/(α-1)}`. -/
noncomputable def plannerKbar (α β θ L : ℝ) : ℝ :=
  α ^ (1 / (1 - α)) * ((1 - β) / θ) * (1 + θ * L) ^ (α / (α - 1))

/-- `c^{1/(1-α)} = K^{PLAN}` (the fixed point of `K ↦ c K^α` is O&R's fn 42 formula). -/
theorem plannerKc_rpow {α β θ L : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ1 : β < 1) (hθ : 0 < θ)
    (hL : 0 < L) :
    plannerKc α β θ L ^ (1 / (1 - α)) = plannerKbar α β θ L := by
  have h1a : (1 - α) ≠ 0 := by linarith
  have ht : 0 < 1 + θ * L := by positivity
  have hs : 0 < ellStar β θ L := by
    unfold ellStar
    exact div_pos (mul_pos (by linarith) ht) hθ
  unfold plannerKc plannerKbar
  rw [Real.mul_rpow (by positivity) (Real.rpow_pos_of_pos hs _).le,
    ← Real.rpow_mul hs.le, mul_one_div_cancel h1a, Real.rpow_one,
    Real.div_rpow hα.le ht.le]
  unfold ellStar
  have h2a : (α - 1) ≠ 0 := by linarith
  rw [show α / (α - 1) = 1 - 1 / (1 - α) by field_simp; ring, Real.rpow_sub ht,
    Real.rpow_one]
  field_simp

/-- **Convergence of the planner's capital per blueprint** (O&R fn 42: "the steady level of
`K` under the planner's problem"): from any `X₀ > 0`, `K_t → K^{PLAN}`. The planner is on its
balanced path only in the limit, although blueprints grow at the constant rate (97) from
date 0. -/
theorem plannerK_tendsto {α β θ L A₀ X₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hL : 0 < L) (hA₀ : 0 < A₀) (hX₀ : 0 < X₀) :
    Tendsto (plannerK α β θ L A₀ X₀) atTop (𝓝 (plannerKbar α β θ L)) := by
  have hs : 0 < ellStar β θ L := by
    unfold ellStar
    exact div_pos (mul_pos (by linarith) (by positivity)) hθ
  have hc : 0 < plannerKc α β θ L := by unfold plannerKc; positivity
  have hK : ∀ t, 0 < plannerK α β θ L A₀ X₀ t := fun t => by
    unfold plannerK plannerA
    have := plannerX_pos hα hβ hβ1 hθ hL hA₀ hX₀ t
    positivity
  set lk := Real.log (plannerKc α β θ L) / (1 - α)
  have hlog : Tendsto (fun t => Real.log (plannerK α β θ L A₀ X₀ t)) atTop (𝓝 lk) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hα.le hα1).mul_const
      (Real.log (plannerK α β θ L A₀ X₀ 0) - lk)).const_add lk
    rw [zero_mul, add_zero] at h
    exact h.congr fun t => (plannerK_log hα hα1 hβ hβ1 hθ hL hA₀ hX₀ t).symm
  have h2 := (Real.continuous_exp.tendsto lk).comp hlog
  have heq : (Real.exp ∘ fun t => Real.log (plannerK α β θ L A₀ X₀ t)) =
      plannerK α β θ L A₀ X₀ := by
    funext t
    simp [Real.exp_log (hK t)]
  rw [heq] at h2
  rw [← plannerKc_rpow hα hα1 hβ1 hθ hL, Real.rpow_def_of_pos hc]
  convert h2 using 2
  simp only [lk, mul_one_div]

/-- **The candidate's utility equals `V(A₀, X₀)`** (genuine infinite horizon): the utility
series converges and `∑ βᵗ log C*_t = V(A₀, X₀)`. -/
theorem planner_candidate_hasSum {α β θ L A₀ X₀ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ) (hL : 0 < L) (hA₀ : 0 < A₀) (hX₀ : 0 < X₀)
    (hint : 1 - β < β * θ * L) :
    HasSum (fun t => β ^ t * Real.log (plannerC α β θ L A₀ X₀ t))
      (plannerValue α β θ L A₀ X₀) := by
  have hG : 0 < β * (1 + θ * L) := by positivity
  have hA : ∀ t, 0 < plannerA β θ L A₀ t := fun t => by unfold plannerA; positivity
  have hX := plannerX_pos hα hβ hβ1 hθ hL hA₀ hX₀
  -- value along the path
  have hV : ∀ T, plannerValue α β θ L (plannerA β θ L A₀ T) (plannerX α β θ L A₀ X₀ T) =
      plannerConst α β θ L + (coefA α β + coefX α β) * (Real.log A₀ +
        T * Real.log (β * (1 + θ * L))) + coefX α β * Real.log (plannerK α β θ L A₀ X₀ T) := by
    intro T
    have hlogA : Real.log (plannerA β θ L A₀ T) = Real.log A₀ + T * Real.log (β * (1 + θ * L)) := by
      unfold plannerA
      rw [Real.log_mul hA₀.ne' (pow_ne_zero _ hG.ne'), Real.log_pow]
    have hlogK : Real.log (plannerK α β θ L A₀ X₀ T) =
        Real.log (plannerX α β θ L A₀ X₀ T) - Real.log (plannerA β θ L A₀ T) := by
      unfold plannerK
      rw [Real.log_div (hX T).ne' (hA T).ne']
    unfold plannerValue
    rw [hlogK, hlogA]
    ring
  have hKb : 0 < plannerKbar α β θ L := by
    unfold plannerKbar
    have : 0 < 1 - β := by linarith
    positivity
  have hlogK : Tendsto (fun T => Real.log (plannerK α β θ L A₀ X₀ T)) atTop
      (𝓝 (Real.log (plannerKbar α β θ L))) :=
    (Real.continuousAt_log hKb.ne').tendsto.comp (plannerK_tendsto hα hα1 hβ hβ1 hθ hL hA₀ hX₀)
  have htail : Tendsto (fun T : ℕ => β ^ T *
      plannerValue α β θ L (plannerA β θ L A₀ T) (plannerX α β θ L A₀ X₀ T)) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1
    have hTp := tendsto_self_mul_const_pow_of_lt_one hβ.le hβ1
    have h1 := hp.mul_const (plannerConst α β θ L + (coefA α β + coefX α β) * Real.log A₀)
    have h2 := hTp.mul_const ((coefA α β + coefX α β) * Real.log (β * (1 + θ * L)))
    have h3 := (hp.mul hlogK).const_mul (coefX α β)
    rw [zero_mul] at h1 h2
    rw [zero_mul, mul_zero] at h3
    have := (h1.add h2).add h3
    rw [add_zero, add_zero] at this
    refine this.congr fun T => ?_
    rw [hV T]
    ring
  have hpart : ∀ T, ∑ t ∈ range T, β ^ t * Real.log (plannerC α β θ L A₀ X₀ t) =
      plannerValue α β θ L A₀ X₀ - β ^ T *
        plannerValue α β θ L (plannerA β θ L A₀ T) (plannerX α β θ L A₀ X₀ T) := by
    intro T
    have htel := telescope_bellman β (fun t => Real.log (plannerC α β θ L A₀ X₀ t))
      (fun t => plannerValue α β θ L (plannerA β θ L A₀ t) (plannerX α β θ L A₀ X₀ t)) T
    have hz : ∑ t ∈ range T, β ^ t * (plannerValue α β θ L (plannerA β θ L A₀ t)
        (plannerX α β θ L A₀ X₀ t) - (Real.log (plannerC α β θ L A₀ X₀ t) +
        β * plannerValue α β θ L (plannerA β θ L A₀ (t + 1)) (plannerX α β θ L A₀ X₀ (t + 1))))
        = 0 := by
      apply sum_eq_zero
      intro t _
      have := planner_candidate_gap hα hα1 hβ hβ1 hθ hL hA₀ hX₀ hint t
      unfold planGap at this
      rw [this, mul_zero]
    rw [hz, add_zero] at htel
    simp only [plannerA, pow_zero, mul_one] at htel
    simp only [plannerX] at htel
    simp only [plannerA] at *
    linarith
  have hlim : Tendsto (fun T => ∑ t ∈ range T, β ^ t * Real.log (plannerC α β θ L A₀ X₀ t))
      atTop (𝓝 (plannerValue α β θ L A₀ X₀)) := by
    have := htail.const_sub (plannerValue α β θ L A₀ X₀)
    rw [sub_zero] at this
    exact this.congr fun T => (hpart T).symm
  have hs : 0 < ellStar β θ L := by
    unfold ellStar
    exact div_pos (mul_pos (by linarith) (by positivity)) hθ
  have hab1 : α * β < 1 := by nlinarith
  set lk := Real.log (plannerKc α β θ L) / (1 - α)
  set d := Real.log (plannerK α β θ L A₀ X₀ 0) - lk
  set e0 := Real.log (1 - α * β) + (1 - α) * Real.log (ellStar β θ L) + Real.log A₀ + α * lk
  have hform : ∀ t : ℕ, β ^ t * Real.log (plannerC α β θ L A₀ X₀ t) =
      e0 * β ^ t + Real.log (β * (1 + θ * L)) * ((t : ℝ) ^ 1 * β ^ t) + α * d * (α * β) ^ t := by
    intro t
    have hY := plannerOutput_pos (α := α) (hA t) (hX t) hs
    have hlogA : Real.log (plannerA β θ L A₀ t) = Real.log A₀ + t * Real.log (β * (1 + θ * L)) := by
      unfold plannerA
      rw [Real.log_mul hA₀.ne' (pow_ne_zero _ hG.ne'), Real.log_pow]
    have hlogK : Real.log (plannerX α β θ L A₀ X₀ t) =
        Real.log (plannerA β θ L A₀ t) + Real.log (plannerK α β θ L A₀ X₀ t) := by
      unfold plannerK
      rw [Real.log_div (hX t).ne' (hA t).ne']
      ring
    unfold plannerC
    rw [Real.log_mul (by linarith) hY.ne', log_plannerOutput (hA t) (hX t) hs, hlogK,
      plannerK_log hα hα1 hβ hβ1 hθ hL hA₀ hX₀ t, hlogA, mul_pow]
    ring
  have hsum : Summable (fun t => β ^ t * Real.log (plannerC α β θ L A₀ X₀ t)) := by
    have hn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ]; exact hβ1
    have h1 := (summable_geometric_of_lt_one hβ.le hβ1).mul_left e0
    have h2 := (summable_pow_mul_geometric_of_norm_lt_one 1 hn).mul_left
      (Real.log (β * (1 + θ * L)))
    have h3 := (summable_geometric_of_lt_one (by positivity) hab1).mul_left (α * d)
    exact ((h1.add h2).add h3).congr fun t => (hform t).symm
  have := tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim
  rw [← this]
  exact hsum.hasSum


/-! ## The planner's corner case `L_Y = L` (no research) -/

/-- Constant term of the planner's value function for a labour policy `ℓp` (the interior case
is `ℓp = ℓ*`, the corner case `ℓp = L`). -/
noncomputable def plannerConstP (α β θ L ℓp : ℝ) : ℝ :=
  (Real.log (1 - α * β) + α * β / (1 - α * β) * Real.log (α * β) +
    (1 - α) / (1 - α * β) * Real.log ℓp +
    β * coefA α β * Real.log (1 + θ * (L - ℓp))) / (1 - β)

/-- The planner's value function for labour policy `ℓp`:
`V(A, X) = κ(ℓp) + a log A + b log X`. -/
noncomputable def plannerValueP (α β θ L ℓp A X : ℝ) : ℝ :=
  plannerConstP α β θ L ℓp + coefA α β * Real.log A + coefX α β * Real.log X

/-- Slack of the labour allocation `ℓ` relative to the policy `ℓp`. -/
noncomputable def labourSlackP (β θ L ℓp ℓ : ℝ) : ℝ :=
  Real.log ℓp + β / (1 - β) * Real.log (1 + θ * (L - ℓp)) -
    (Real.log ℓ + β / (1 - β) * Real.log (1 + θ * (L - ℓ)))

/-- **At the corner, no research is optimal**: if `βθL ≤ 1 - β` (planned growth (97) is
non-positive), then for every `0 < ℓ ≤ L`, `labourSlackP` at `ℓp = L` is nonnegative, and
strictly positive for `ℓ ≠ L`. -/
theorem labourSlack_corner {β θ L ℓ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ)
    (hL : 0 < L) (hcorner : β * θ * L ≤ 1 - β) (hℓ : 0 < ℓ) (hℓL : ℓ ≤ L) :
    0 ≤ labourSlackP β θ L L ℓ ∧ (ℓ ≠ L → 0 < labourSlackP β θ L L ℓ) := by
  have hm : 0 < 1 + θ * (L - ℓ) := by nlinarith
  have hq : 0 < β / (1 - β) := div_pos hβ (by linarith)
  have l1 := Real.log_le_sub_one_of_pos hm
  have key : (ℓ / L - 1) + β / (1 - β) * (1 + θ * (L - ℓ) - 1) ≤ 0 := by
    have e : (ℓ / L - 1) + β / (1 - β) * (1 + θ * (L - ℓ) - 1) =
        (L - ℓ) * (β * θ * L - (1 - β)) / ((1 - β) * L) := by
      have : (1 - β) ≠ 0 := by linarith
      field_simp
      ring
    rw [e]
    apply div_nonpos_of_nonpos_of_nonneg _ (by nlinarith)
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  unfold labourSlackP
  rw [show L - L = 0 by ring, mul_zero, add_zero, Real.log_one, mul_zero, add_zero]
  constructor
  · have l2 := Real.log_le_sub_one_of_pos (div_pos hℓ hL)
    rw [Real.log_div hℓ.ne' hL.ne'] at l2
    nlinarith [mul_le_mul_of_nonneg_left l1 hq.le]
  · intro hne
    have hx : ℓ / L ≠ 1 := by
      rw [Ne, div_eq_one_iff_eq hL.ne']
      exact hne
    have l2 := Real.log_lt_sub_one_of_pos (div_pos hℓ hL) hx
    rw [Real.log_div hℓ.ne' hL.ne'] at l2
    nlinarith [mul_le_mul_of_nonneg_left l1 hq.le]

theorem bellman_gapP {α β θ L ℓp A X ℓ x : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hA : 0 < A) (hX : 0 < X) (hℓ : 0 < ℓ) (hℓL : ℓ ≤ L) :
    plannerValueP α β θ L ℓp A X - (Real.log (plannerOutput α A X ℓ - x) +
        β * plannerValueP α β θ L ℓp (A * (1 + θ * (L - ℓ))) x) =
      savingSlack α β (plannerOutput α A X ℓ) x +
        (1 - α) / (1 - α * β) * labourSlackP β θ L ℓp ℓ := by
  have hY := plannerOutput_pos (α := α) hA hX hℓ
  have hm : 0 < 1 + θ * (L - ℓ) := by nlinarith
  have hab : 0 < α * β := mul_pos hα hβ
  have hab1 : α * β < 1 := by nlinarith
  have h1a : 0 < 1 - α * β := by linarith
  have h1b : 0 < 1 - β := by linarith
  unfold plannerValueP savingSlack labourSlackP plannerConstP coefA coefX
  rw [Real.log_mul hA.ne' hm.ne', Real.log_mul h1a.ne' hY.ne', Real.log_mul hab.ne' hY.ne',
    log_plannerOutput hA hX hℓ]
  field_simp
  ring

/-- The one-period Bellman slack of a plan at date `t`:
`V(A_t, X_t) - [log C_t + β V(A_{t+1}, X_{t+1})]`. -/
noncomputable def planGapP (α β θ L ℓp : ℝ) (A X C : ℕ → ℝ) (t : ℕ) : ℝ :=
  plannerValueP α β θ L ℓp (A t) (X t) -
    (Real.log (C t) + β * plannerValueP α β θ L ℓp (A (t + 1)) (X (t + 1)))

/-- On a feasible plan the Bellman slack is the sum of the saving and labour slacks,
hence nonnegative, and zero only if `X_{t+1} = αβY_t` and `L_{Y,t} = ℓ*`. -/
theorem PlannerFeasible.gap_eqP {α β θ L ℓp A₀ X₀ : ℝ} {A X ℓ C : ℕ → ℝ}
    (hf : PlannerFeasible α θ L A₀ X₀ A X ℓ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hA₀ : 0 < A₀) (t : ℕ) :
    planGapP α β θ L ℓp A X C t = savingSlack α β (plannerOutput α (A t) (X t) (ℓ t)) (X (t + 1)) +
      (1 - α) / (1 - α * β) * labourSlackP β θ L ℓp (ℓ t) := by
  have hA := lt_of_lt_of_le hA₀ (hf.A_ge hA₀ hθ t)
  unfold planGapP
  rw [← bellman_gapP hα hα1 hβ hβ1 hθ hA (hf.posX t) (hf.labourPos t) (hf.labourLe t),
    ← hf.research t, show C t = plannerOutput α (A t) (X t) (ℓ t) - X (t + 1) by
      linarith [hf.resource t]]

/-- The Bellman slack is nonnegative on a feasible plan; it is strictly positive whenever
the plan deviates from the policy `X_{t+1} = αβY_t`, `L_{Y,t} = ℓ*` at `t`. -/
theorem PlannerFeasible.gap_nonnegP {α β θ L ℓp A₀ X₀ : ℝ} {A X ℓ C : ℕ → ℝ}
    (hf : PlannerFeasible α θ L A₀ X₀ A X ℓ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hA₀ : 0 < A₀)
    (hslack : ∀ l, 0 < l → l ≤ L → 0 ≤ labourSlackP β θ L ℓp l ∧
      (l ≠ ℓp → 0 < labourSlackP β θ L ℓp l)) (t : ℕ) :
    0 ≤ planGapP α β θ L ℓp A X C t ∧
      (planGapP α β θ L ℓp A X C t = 0 →
        ℓ t = ℓp ∧ X (t + 1) = α * β * plannerOutput α (A t) (X t) (ℓ t)) := by
  have hA := lt_of_lt_of_le hA₀ (hf.A_ge hA₀ hθ t)
  have hY := plannerOutput_pos (α := α) hA (hf.posX t) (hf.labourPos t)
  have hxY : X (t + 1) < plannerOutput α (A t) (X t) (ℓ t) := by
    linarith [hf.resource t, hf.posC t]
  have hab1 : α * β < 1 := by nlinarith
  obtain ⟨s1, s1'⟩ := savingSlack_nonneg hα hβ hab1 hY (hf.posX (t + 1)) hxY
  obtain ⟨s2, s2'⟩ := hslack (ℓ t) (hf.labourPos t) (hf.labourLe t)
  have hn : 0 < (1 - α) / (1 - α * β) := div_pos (by linarith) (by linarith)
  rw [hf.gap_eqP hα hα1 hβ hβ1 hθ hA₀ t]
  refine ⟨by positivity, fun h0 => ⟨?_, ?_⟩⟩
  · by_contra hne
    have := s2' hne
    nlinarith [mul_pos hn this]
  · by_contra hne
    have := s1' hne
    nlinarith [mul_nonneg hn.le s2]

/-- **Lower bound on continuation values** of any feasible plan (the unbounded-below tail):
`V(A_T, X_T) ≥ κ + c_A log A₀ + (log C_T - (1-α) log L)/(1-αβ)` with
`c_A = (1-α)β/((1-β)(1-αβ)) ≥ 0`, because `C_T < Y_T ≤ A_T^{1-α} X_T^α L^{1-α}`. -/
theorem PlannerFeasible.value_lowerP {α β θ L ℓp A₀ X₀ : ℝ} {A X ℓ C : ℕ → ℝ}
    (hf : PlannerFeasible α θ L A₀ X₀ A X ℓ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hA₀ : 0 < A₀) (T : ℕ) :
    plannerConstP α β θ L ℓp + (1 - α) * β / ((1 - β) * (1 - α * β)) * Real.log A₀ +
        (Real.log (C T) - (1 - α) * Real.log L) / (1 - α * β) ≤
      plannerValueP α β θ L ℓp (A T) (X T) := by
  have hAge := hf.A_ge hA₀ hθ T
  have hA := lt_of_lt_of_le hA₀ hAge
  have hX := hf.posX T
  have hℓ := hf.labourPos T
  have hab1 : α * β < 1 := by nlinarith
  have h1a : 0 < 1 - α * β := by linarith
  have h1b : 0 < 1 - β := by linarith
  have hCY : Real.log (C T) ≤ Real.log (plannerOutput α (A T) (X T) (ℓ T)) :=
    Real.log_le_log (hf.posC T) (by linarith [hf.resource T, hf.posX (T + 1)])
  rw [log_plannerOutput hA hX hℓ] at hCY
  have hlogℓ : Real.log (ℓ T) ≤ Real.log L := Real.log_le_log hℓ (hf.labourLe T)
  have hlogA : Real.log A₀ ≤ Real.log (A T) := Real.log_le_log hA₀ hAge
  have key : Real.log (C T) - (1 - α) * Real.log L ≤
      (1 - α) * Real.log (A T) + α * Real.log (X T) := by nlinarith
  have hcA : 0 ≤ (1 - α) * β / ((1 - β) * (1 - α * β)) := by
    apply div_nonneg _ (by positivity)
    nlinarith
  unfold plannerValueP coefA coefX
  have e : (1 - α) / ((1 - β) * (1 - α * β)) * Real.log (A T) + α / (1 - α * β) *
      Real.log (X T) = (1 - α) * β / ((1 - β) * (1 - α * β)) * Real.log (A T) +
      ((1 - α) * Real.log (A T) + α * Real.log (X T)) / (1 - α * β) := by
    field_simp
    ring
  have h2 : (Real.log (C T) - (1 - α) * Real.log L) / (1 - α * β) ≤
      ((1 - α) * Real.log (A T) + α * Real.log (X T)) / (1 - α * β) :=
    div_le_div_of_nonneg_right key h1a.le
  have h3 := mul_le_mul_of_nonneg_left hlogA hcA
  linarith

/-- **Optimality of the policy, genuine infinite horizon** (O&R fn 42, (97), Exercise 3):
for every feasible plan with convergent utility and every date `t₀`,
`∑ βᵗ log C_t + β^{t₀}·(Bellman slack at t₀) ≤ V(A₀, X₀)`. In particular
`∑ βᵗ log C_t ≤ V(A₀, X₀)`. -/
theorem planner_tsum_leP {α β θ L ℓp A₀ X₀ : ℝ} {A X ℓ C : ℕ → ℝ}
    (hf : PlannerFeasible α θ L A₀ X₀ A X ℓ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hA₀ : 0 < A₀)
    (hslack : ∀ l, 0 < l → l ≤ L → 0 ≤ labourSlackP β θ L ℓp l ∧
      (l ≠ ℓp → 0 < labourSlackP β θ L ℓp l))
    (hs : Summable (fun t => β ^ t * Real.log (C t))) (t₀ : ℕ) :
    ∑' t, β ^ t * Real.log (C t) + β ^ t₀ * planGapP α β θ L ℓp A X C t₀ ≤
      plannerValueP α β θ L ℓp A₀ X₀ := by
  set κ0 := plannerConstP α β θ L ℓp + (1 - α) * β / ((1 - β) * (1 - α * β)) * Real.log A₀ -
    (1 - α) * Real.log L / (1 - α * β) with hκ0
  have hab1 : α * β < 1 := by nlinarith
  have h1a : 0 < 1 - α * β := by linarith
  set low : ℕ → ℝ := fun T => β ^ T * κ0 + (β ^ T * Real.log (C T)) / (1 - α * β) with hlow
  have hlowlim : Tendsto low atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℕ => β ^ T * κ0) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const κ0
    have h2 := (hs.tendsto_atTop_zero).div_const (1 - α * β)
    rw [zero_div] at h2
    simpa using h1.add h2
  have hpart : ∀ T, t₀ < T → ∑ t ∈ range T, β ^ t * Real.log (C t) +
      β ^ t₀ * planGapP α β θ L ℓp A X C t₀ ≤ plannerValueP α β θ L ℓp A₀ X₀ - low T := by
    intro T hT
    have htel := telescope_bellman β (fun t => Real.log (C t))
      (fun t => plannerValueP α β θ L ℓp (A t) (X t)) T
    simp only [hf.initA, hf.initX] at htel
    have hsingle := single_le_sum (f := fun t => β ^ t * planGapP α β θ L ℓp A X C t)
      (fun t _ => mul_nonneg (pow_nonneg hβ.le t)
        (hf.gap_nonnegP hα hα1 hβ hβ1 hθ hA₀ hslack t).1) (mem_range.mpr hT)
    have hlowT := hf.value_lowerP (ℓp := ℓp) hα hα1 hβ hβ1 hθ hA₀ T
    have hlowT' : low T ≤ β ^ T * plannerValueP α β θ L ℓp (A T) (X T) := by
      simp only [hlow, hκ0]
      have := mul_le_mul_of_nonneg_left hlowT (pow_nonneg hβ.le T)
      have e : β ^ T * (plannerConstP α β θ L ℓp + (1 - α) * β / ((1 - β) * (1 - α * β)) *
          Real.log A₀ + (Real.log (C T) - (1 - α) * Real.log L) / (1 - α * β)) =
          β ^ T * (plannerConstP α β θ L ℓp + (1 - α) * β / ((1 - β) * (1 - α * β)) *
          Real.log A₀ - (1 - α) * Real.log L / (1 - α * β)) +
          β ^ T * Real.log (C T) / (1 - α * β) := by ring
      linarith
    unfold planGapP at hsingle ⊢
    linarith
  have h1 := (hs.hasSum.tendsto_sum_nat).add_const (β ^ t₀ * planGapP α β θ L ℓp A X C t₀)
  have h2 := hlowlim.const_sub (plannerValueP α β θ L ℓp A₀ X₀)
  rw [sub_zero] at h2
  exact le_of_tendsto_of_tendsto h1 h2 (eventually_atTop.2 ⟨t₀ + 1, fun T hT => hpart T hT⟩)

/-- **Uniqueness of the planner's optimum**: a feasible plan with convergent utility that
attains `V(A₀, X₀)` follows the policy at every date: `L_{Y,t} = ℓ*` and
`X_{t+1} = αβ Y_t`. -/
theorem planner_policy_of_optimalP {α β θ L ℓp A₀ X₀ : ℝ} {A X ℓ C : ℕ → ℝ}
    (hf : PlannerFeasible α θ L A₀ X₀ A X ℓ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hA₀ : 0 < A₀)
    (hslack : ∀ l, 0 < l → l ≤ L → 0 ≤ labourSlackP β θ L ℓp l ∧
      (l ≠ ℓp → 0 < labourSlackP β θ L ℓp l))
    (hs : Summable (fun t => β ^ t * Real.log (C t)))
    (hopt : plannerValueP α β θ L ℓp A₀ X₀ ≤ ∑' t, β ^ t * Real.log (C t)) (t : ℕ) :
    ℓ t = ℓp ∧ X (t + 1) = α * β * plannerOutput α (A t) (X t) (ℓ t) := by
  have h := planner_tsum_leP hf hα hα1 hβ hβ1 hθ hA₀ hslack hs t
  obtain ⟨hnn, himp⟩ := hf.gap_nonnegP hα hα1 hβ hβ1 hθ hA₀ hslack t
  apply himp
  have hβt : 0 < β ^ t := pow_pos hβ t
  by_contra hne
  have := mul_pos hβt (lt_of_le_of_ne hnn (Ne.symm hne))
  linarith


/-- The corner plan's capital: `X_0 = X₀`, `X_{t+1} = αβ A₀^{1-α} X_t^α L^{1-α}` (no research,
`A_t = A₀`). -/
noncomputable def plannerXc (α β L A₀ X₀ : ℝ) : ℕ → ℝ
  | 0 => X₀
  | t + 1 => α * β * plannerOutput α A₀ (plannerXc α β L A₀ X₀ t) L

/-- The corner plan's consumption `C_t = (1-αβ) Y_t`. -/
noncomputable def plannerCc (α β L A₀ X₀ : ℝ) (t : ℕ) : ℝ :=
  (1 - α * β) * plannerOutput α A₀ (plannerXc α β L A₀ X₀ t) L

/-- The corner plan's capital stays positive. -/
theorem plannerXc_pos {α β L A₀ X₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hL : 0 < L)
    (hA₀ : 0 < A₀) (hX₀ : 0 < X₀) (t : ℕ) : 0 < plannerXc α β L A₀ X₀ t := by
  induction t with
  | zero => exact hX₀
  | succ t ih =>
    simp only [plannerXc]
    have := plannerOutput_pos (α := α) hA₀ ih hL
    positivity

/-- The corner plan is feasible. -/
theorem corner_feasible {α β θ L A₀ X₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hL : 0 < L) (hA₀ : 0 < A₀) (hX₀ : 0 < X₀) :
    PlannerFeasible α θ L A₀ X₀ (fun _ => A₀) (plannerXc α β L A₀ X₀) (fun _ => L)
      (plannerCc α β L A₀ X₀) := by
  have hab1 : α * β < 1 := by nlinarith
  refine ⟨rfl, rfl, plannerXc_pos hα hβ hL hA₀ hX₀, fun _ => hL, fun _ => le_rfl,
    fun t => ?_, fun t => ?_, fun t => by ring⟩
  · unfold plannerCc
    have := plannerOutput_pos (α := α) hA₀ (plannerXc_pos hα hβ hL hA₀ hX₀ t) hL
    have : 0 < 1 - α * β := by linarith
    positivity
  · simp only [plannerCc, plannerXc]
    ring

/-- The corner plan follows its policy: every Bellman slack is zero. -/
theorem corner_gap {α β θ L A₀ X₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hL : 0 < L) (hA₀ : 0 < A₀) (hX₀ : 0 < X₀) (t : ℕ) :
    planGapP α β θ L L (fun _ => A₀) (plannerXc α β L A₀ X₀) (plannerCc α β L A₀ X₀) t = 0 := by
  have hf := corner_feasible (θ := θ) hα hα1 hβ hβ1 hL hA₀ hX₀
  rw [hf.gap_eqP hα hα1 hβ hβ1 hθ hA₀ t]
  simp only [savingSlack, labourSlackP, plannerXc]
  rw [show plannerOutput α A₀ (plannerXc α β L A₀ X₀ t) L - α * β * plannerOutput α A₀
    (plannerXc α β L A₀ X₀ t) L = (1 - α * β) * plannerOutput α A₀ (plannerXc α β L A₀ X₀ t) L
    by ring]
  ring

/-- Closed form of log capital on the corner plan:
`log X_t = x̄ + αᵗ (log X₀ - x̄)` with `x̄ = [log(αβ) + (1-α)(log A₀ + log L)]/(1-α)`. -/
theorem plannerXc_log {α β L A₀ X₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hL : 0 < L)
    (hA₀ : 0 < A₀) (hX₀ : 0 < X₀) (t : ℕ) :
    Real.log (plannerXc α β L A₀ X₀ t) =
      (Real.log (α * β) + (1 - α) * (Real.log A₀ + Real.log L)) / (1 - α) +
        α ^ t * (Real.log X₀ - (Real.log (α * β) + (1 - α) * (Real.log A₀ + Real.log L)) /
          (1 - α)) := by
  have h1a : (1 - α) ≠ 0 := by linarith
  induction t with
  | zero => simp [plannerXc]
  | succ t ih =>
    have hX := plannerXc_pos hα hβ hL hA₀ hX₀ t
    simp only [plannerXc]
    rw [Real.log_mul (by positivity) (plannerOutput_pos hA₀ hX hL).ne',
      log_plannerOutput hA₀ hX hL, ih, pow_succ]
    field_simp
    ring

/-- **The corner optimum** (the case O&R's (97) leaves out, `βθL ≤ 1 - β`): the plan with no
research (`L_Y = L`, `A_t = A₀`, zero growth) and saving `X_{t+1} = αβ Y_t` is feasible, its
utility converges to `V_L(A₀, X₀)`, and every feasible plan with convergent utility achieves
at most `V_L(A₀, X₀)`; any plan attaining it does no research and saves `αβY_t` at every
date. -/
theorem planner_corner_optimal {α β θ L A₀ X₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hL : 0 < L) (hA₀ : 0 < A₀) (hX₀ : 0 < X₀)
    (hcorner : β * θ * L ≤ 1 - β) :
    PlannerFeasible α θ L A₀ X₀ (fun _ => A₀) (plannerXc α β L A₀ X₀) (fun _ => L)
        (plannerCc α β L A₀ X₀) ∧
      HasSum (fun t => β ^ t * Real.log (plannerCc α β L A₀ X₀ t))
        (plannerValueP α β θ L L A₀ X₀) ∧
      (∀ A X ℓ C : ℕ → ℝ, PlannerFeasible α θ L A₀ X₀ A X ℓ C →
        Summable (fun t => β ^ t * Real.log (C t)) →
        ∑' t, β ^ t * Real.log (C t) ≤ plannerValueP α β θ L L A₀ X₀) ∧
      (∀ A X ℓ C : ℕ → ℝ, PlannerFeasible α θ L A₀ X₀ A X ℓ C →
        Summable (fun t => β ^ t * Real.log (C t)) →
        plannerValueP α β θ L L A₀ X₀ ≤ ∑' t, β ^ t * Real.log (C t) →
        ∀ t, ℓ t = L ∧ A (t + 1) = A t ∧
          X (t + 1) = α * β * plannerOutput α (A t) (X t) (ℓ t)) := by
  have hslack : ∀ l, 0 < l → l ≤ L → 0 ≤ labourSlackP β θ L L l ∧
      (l ≠ L → 0 < labourSlackP β θ L L l) :=
    fun l hl hlL => labourSlack_corner hβ hβ1 hθ hL hcorner hl hlL
  have hf := corner_feasible (θ := θ) hα hα1 hβ hβ1 hL hA₀ hX₀
  have hab1 : α * β < 1 := by nlinarith
  set xb := (Real.log (α * β) + (1 - α) * (Real.log A₀ + Real.log L)) / (1 - α)
  set dd := Real.log X₀ - xb
  have hlogX : ∀ t, Real.log (plannerXc α β L A₀ X₀ t) = xb + α ^ t * dd :=
    fun t => plannerXc_log hα hα1 hβ hL hA₀ hX₀ t
  -- partial sums
  have hpart : ∀ T, ∑ t ∈ range T, β ^ t * Real.log (plannerCc α β L A₀ X₀ t) =
      plannerValueP α β θ L L A₀ X₀ - β ^ T *
        plannerValueP α β θ L L A₀ (plannerXc α β L A₀ X₀ T) := by
    intro T
    have htel := telescope_bellman β (fun t => Real.log (plannerCc α β L A₀ X₀ t))
      (fun t => plannerValueP α β θ L L A₀ (plannerXc α β L A₀ X₀ t)) T
    have hz : ∑ t ∈ range T, β ^ t * (plannerValueP α β θ L L A₀ (plannerXc α β L A₀ X₀ t) -
        (Real.log (plannerCc α β L A₀ X₀ t) +
        β * plannerValueP α β θ L L A₀ (plannerXc α β L A₀ X₀ (t + 1)))) = 0 := by
      apply sum_eq_zero
      intro t _
      have := corner_gap (θ := θ) hα hα1 hβ hβ1 hθ hL hA₀ hX₀ t
      unfold planGapP at this
      rw [this, mul_zero]
    rw [hz, add_zero] at htel
    have h0 : plannerXc α β L A₀ X₀ 0 = X₀ := rfl
    rw [h0] at htel
    linarith
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1
  have htail : Tendsto (fun T : ℕ => β ^ T *
      plannerValueP α β θ L L A₀ (plannerXc α β L A₀ X₀ T)) atTop (𝓝 0) := by
    have hconv : Tendsto (fun T : ℕ => plannerValueP α β θ L L A₀ (plannerXc α β L A₀ X₀ T))
        atTop (𝓝 (plannerConstP α β θ L L + coefA α β * Real.log A₀ + coefX α β * xb)) := by
      have ha := ((tendsto_pow_atTop_nhds_zero_of_lt_one hα.le hα1).mul_const dd).const_add xb
      rw [zero_mul, add_zero] at ha
      have := (ha.const_mul (coefX α β)).const_add
        (plannerConstP α β θ L L + coefA α β * Real.log A₀)
      refine this.congr fun T => ?_
      unfold plannerValueP
      rw [hlogX T]
    have := hp.mul hconv
    rwa [zero_mul] at this
  have hlim : Tendsto (fun T => ∑ t ∈ range T, β ^ t * Real.log (plannerCc α β L A₀ X₀ t))
      atTop (𝓝 (plannerValueP α β θ L L A₀ X₀)) := by
    have := htail.const_sub (plannerValueP α β θ L L A₀ X₀)
    rw [sub_zero] at this
    exact this.congr fun T => (hpart T).symm
  have hsum : Summable (fun t => β ^ t * Real.log (plannerCc α β L A₀ X₀ t)) := by
    set e1 := Real.log (1 - α * β) + (1 - α) * Real.log A₀ + (1 - α) * Real.log L + α * xb
    have hform : ∀ t : ℕ, β ^ t * Real.log (plannerCc α β L A₀ X₀ t) =
        e1 * β ^ t + α * dd * (α * β) ^ t := by
      intro t
      have hX := plannerXc_pos hα hβ hL hA₀ hX₀ t
      unfold plannerCc
      rw [Real.log_mul (by linarith) (plannerOutput_pos hA₀ hX hL).ne',
        log_plannerOutput hA₀ hX hL, hlogX t, mul_pow]
      ring
    have h1 := (summable_geometric_of_lt_one hβ.le hβ1).mul_left e1
    have h3 := (summable_geometric_of_lt_one (by positivity) hab1).mul_left (α * dd)
    exact (h1.add h3).congr fun t => (hform t).symm
  have hHas : HasSum (fun t => β ^ t * Real.log (plannerCc α β L A₀ X₀ t))
      (plannerValueP α β θ L L A₀ X₀) := by
    have := tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim
    rw [← this]
    exact hsum.hasSum
  refine ⟨hf, hHas, fun A X ℓ C hf' hs => ?_, fun A X ℓ C hf' hs hopt t => ?_⟩
  · have h := planner_tsum_leP hf' hα hα1 hβ hβ1 hθ hA₀ hslack hs 0
    have := (hf'.gap_nonnegP hα hα1 hβ hβ1 hθ hA₀ hslack 0).1
    simp only [pow_zero, one_mul] at h
    linarith
  · obtain ⟨hl, hX⟩ := planner_policy_of_optimalP hf' hα hα1 hβ hβ1 hθ hA₀ hslack hs hopt t
    refine ⟨hl, ?_, hX⟩
    rw [hf'.research t, hl]
    ring

/-- On the corner plan capital converges: `log X_t → x̄`, so the economy settles at a
stationary level with zero growth (the Brock–Mirman dynamics). -/
theorem plannerXc_tendsto {α β L A₀ X₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hL : 0 < L) (hA₀ : 0 < A₀) (hX₀ : 0 < X₀) :
    Tendsto (fun t => Real.log (plannerXc α β L A₀ X₀ t)) atTop
      (𝓝 ((Real.log (α * β) + (1 - α) * (Real.log A₀ + Real.log L)) / (1 - α))) := by
  have ha := ((tendsto_pow_atTop_nhds_zero_of_lt_one hα.le hα1).mul_const
    (Real.log X₀ - (Real.log (α * β) + (1 - α) * (Real.log A₀ + Real.log L)) / (1 - α))).const_add
    ((Real.log (α * β) + (1 - α) * (Real.log A₀ + Real.log L)) / (1 - α))
  rw [zero_mul, add_zero] at ha
  exact ha.congr fun t => (plannerXc_log hα hα1 hβ hL hA₀ hX₀ t).symm

/-- **The planner's problem is solved, in full** (O&R fn 42, (97), Exercise 3; genuine
infinite horizon, log utility). If `βθL > 1 - β`, the plan `L_Y = ℓ*`, `X_{t+1} = αβY_t` is
feasible, its utility converges to `V(A₀, X₀)`, and every feasible plan with convergent
utility achieves at most `V(A₀, X₀)`. -/
theorem planner_optimal {α β θ L A₀ X₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hL : 0 < L) (hA₀ : 0 < A₀) (hX₀ : 0 < X₀)
    (hint : 1 - β < β * θ * L) :
    PlannerFeasible α θ L A₀ X₀ (plannerA β θ L A₀) (plannerX α β θ L A₀ X₀)
        (fun _ => ellStar β θ L) (plannerC α β θ L A₀ X₀) ∧
      HasSum (fun t => β ^ t * Real.log (plannerC α β θ L A₀ X₀ t))
        (plannerValue α β θ L A₀ X₀) ∧
      ∀ A X ℓ C : ℕ → ℝ, PlannerFeasible α θ L A₀ X₀ A X ℓ C →
        Summable (fun t => β ^ t * Real.log (C t)) →
        ∑' t, β ^ t * Real.log (C t) ≤ plannerValue α β θ L A₀ X₀ := by
  refine ⟨planner_candidate_feasible hα hα1 hβ hβ1 hθ hL hA₀ hX₀ hint,
    planner_candidate_hasSum hα hα1 hβ hβ1 hθ hL hA₀ hX₀ hint, fun A X ℓ C hf hs => ?_⟩
  have h := planner_tsum_le hf hα hα1 hβ hβ1 hθ hL hA₀ hs 0
  have := (hf.gap_nonneg hα hα1 hβ hβ1 hθ hL hA₀ 0).1
  simp only [pow_zero, one_mul] at h
  linarith

/-- **The planner's optimum is unique**: any feasible plan with convergent utility at least
`V(A₀, X₀)` coincides with the candidate path at every date. -/
theorem planner_unique {α β θ L A₀ X₀ : ℝ} {A X ℓ C : ℕ → ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ) (hL : 0 < L) (hA₀ : 0 < A₀)
    (hf : PlannerFeasible α θ L A₀ X₀ A X ℓ C)
    (hs : Summable (fun t => β ^ t * Real.log (C t)))
    (hopt : plannerValue α β θ L A₀ X₀ ≤ ∑' t, β ^ t * Real.log (C t)) (t : ℕ) :
    A t = plannerA β θ L A₀ t ∧ X t = plannerX α β θ L A₀ X₀ t ∧ ℓ t = ellStar β θ L ∧
      C t = plannerC α β θ L A₀ X₀ t := by
  have hpol := planner_policy_of_optimal hf hα hα1 hβ hβ1 hθ hL hA₀ hs hopt
  have hAX : ∀ t, A t = plannerA β θ L A₀ t ∧ X t = plannerX α β θ L A₀ X₀ t := by
    intro t
    induction t with
    | zero => exact ⟨by rw [hf.initA]; simp [plannerA], hf.initX⟩
    | succ t ih =>
      obtain ⟨hℓ, hX⟩ := hpol t
      refine ⟨?_, ?_⟩
      · rw [hf.research t, hℓ, research_factor hθ, ih.1]
        simp only [plannerA]
        rw [pow_succ]
        ring
      · rw [hX, ih.1, ih.2, hℓ]
        rfl
  obtain ⟨hA, hX⟩ := hAX t
  obtain ⟨hℓ, hX1⟩ := hpol t
  refine ⟨hA, hX, hℓ, ?_⟩
  have hres := hf.resource t
  rw [hX1, hA, hX, hℓ] at hres
  unfold plannerC
  linarith

/-- **The planner's growth rate** O&R (97), p. 492 (Exercise 3): blueprints grow at
`ḡ^{PLAN} = βθL - (1-β)` from date 0, with R&D labour `θL_A = βθL - (1-β)` and
`L_Y^{PLAN} = (1-β)(1+θL)/θ`. -/
theorem planner_growth {β θ L A₀ : ℝ} (hθ : 0 < θ) (t : ℕ) :
    plannerA β θ L A₀ (t + 1) = (1 + (β * θ * L - (1 - β))) * plannerA β θ L A₀ t ∧
      θ * (L - ellStar β θ L) = β * θ * L - (1 - β) := by
  constructor
  · simp only [plannerA]
    rw [pow_succ]
    ring
  · have := research_factor (β := β) (L := L) hθ
    linarith

/-- **The planner grows faster than the market** (O&R p. 492; log utility):
`ḡ^{PLAN} - ḡ = β[θL(1 - α(1-β)) - α(1-β)]/(1+αβ)`, which is positive whenever the market
equilibrium is interior (`θL > (1-β)/(αβ)`). -/
theorem planner_minus_market {α β θ L : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hmkt : (1 - β) / (α * β) < θ * L) :
    (β * θ * L - (1 - β)) - (α * β * θ * L - (1 - β)) / (1 + α * β) =
        β * (θ * L * (1 - α * (1 - β)) - α * (1 - β)) / (1 + α * β) ∧
      (α * β * θ * L - (1 - β)) / (1 + α * β) < β * θ * L - (1 - β) := by
  have hab : 0 < 1 + α * β := by positivity
  have e : (β * θ * L - (1 - β)) - (α * β * θ * L - (1 - β)) / (1 + α * β) =
      β * (θ * L * (1 - α * (1 - β)) - α * (1 - β)) / (1 + α * β) := by
    field_simp
    ring
  refine ⟨e, ?_⟩
  have hc := (div_lt_iff₀ (by positivity : 0 < α * β)).mp hmkt
  have : 0 < β * (θ * L * (1 - α * (1 - β)) - α * (1 - β)) / (1 + α * β) := by
    apply div_pos _ hab
    apply mul_pos hβ
    have h1 : 0 < 1 - α * (1 - β) := by nlinarith
    have h2 : θ * L * (1 - α * (1 - β)) * (α * β) > (1 - β) * (1 - α * (1 - β)) := by
      nlinarith
    have h3 : α ^ 2 * β * (1 - β) ≤ (1 - β) * (1 - α * (1 - β)) := by
      have : 0 ≤ (1 - α) * (1 + α * β) := mul_nonneg (by linarith) (by positivity)
      nlinarith
    have h4 : α * (1 - β) * (α * β) < θ * L * (1 - α * (1 - β)) * (α * β) := by nlinarith
    have := lt_of_mul_lt_mul_right h4 (by positivity)
    linarith
  linarith

/-- Subsidised monopoly (O&R p. 492): when the producer receives `1/α` per dollar of sales,
profit is `L_Y^{1-α}K^α/(1+r) - K`; at `α L_Y^{1-α} K^{α-1} = 1 + r` (price `p̄ = 1 + r`)
the quantity `K` is optimal and profit equals `((1-α)/α) K`. -/
theorem subsidy_monopoly_optimal {α r LY K x : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hr : 0 < 1 + r) (hLY : 0 < LY) (hK : 0 < K)
    (hfoc : α * LY ^ (1 - α) * K ^ (α - 1) = 1 + r) (hx : 0 ≤ x) :
    LY ^ (1 - α) * x ^ α / (1 + r) - x ≤ LY ^ (1 - α) * K ^ α / (1 + r) - K ∧
      LY ^ (1 - α) * K ^ α / (1 + r) - K = (1 - α) / α * K := by
  have ht := rpow_le_tangent hα hα1 hK hx
  have hL := Real.rpow_pos_of_pos hLY (1 - α)
  have hKK : K ^ (α - 1) * K = K ^ α := by
    rw [show α = (α - 1) + 1 by ring, Real.rpow_add hK, Real.rpow_one]
    ring_nf
  have hval : LY ^ (1 - α) * K ^ α = (1 + r) * K / α := by
    rw [← hKK, ← hfoc]
    field_simp
  constructor
  · have h1 := mul_le_mul_of_nonneg_left ht hL.le
    have e : LY ^ (1 - α) * (K ^ α + α * K ^ (α - 1) * (x - K)) =
        LY ^ (1 - α) * K ^ α + (1 + r) * (x - K) := by
      rw [← hfoc]
      ring
    rw [div_sub' hr.ne', div_sub' hr.ne']
    exact div_le_div_of_nonneg_right (by nlinarith) hr.le
  · rw [hval]
    field_simp

/-- **Subsidised TT curve** (O&R p. 492): with the static distortion removed, R&D arbitrage
gives `L_Y = r/θ` (`K̄ = (α/(1+r))^{1/(1-α)} L_Y`, `(1+r)κ_s = ακ_s^α`), so
`g = θ(L - L_Y) = θL - r`. -/
theorem subsidy_labour_arbitrage {α r θ LY κs : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r)
    (hθ : 0 < θ) (hκ : 0 < κs) (hid : (1 + r) * κs = α * κs ^ α) :
    θ * ((1 + r) * ((1 - α) / α * (κs * LY)) / r) = (1 - α) * κs ^ α ↔ LY = r / θ := by
  have hka := Real.rpow_pos_of_pos hκ α
  have h1a : 0 < 1 - α := by linarith
  have e : θ * ((1 + r) * ((1 - α) / α * (κs * LY)) / r) =
      θ * LY * ((1 - α) * κs ^ α) / r := by
    rw [show (1 + r) * ((1 - α) / α * (κs * LY)) = (1 - α) * LY * ((1 + r) * κs) / α by ring,
      hid]
    field_simp
  rw [e]
  constructor
  · intro h
    rw [div_eq_iff hr.ne'] at h
    have := mul_right_cancel₀ (by positivity : (1 - α) * κs ^ α ≠ 0)
      (show θ * LY * ((1 - α) * κs ^ α) = r * ((1 - α) * κs ^ α) by linarith)
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp

/-- **Growth with the subsidy lies strictly between market and planner** (O&R p. 492, log
utility): the subsidised balanced path `g = θL - r`, `1 + g = β(1+r)` has
`g = (βθL - (1-β))/(1+β)`, and `ḡ < g < ḡ^{PLAN}` whenever `ḡ^{PLAN} > 0`. -/
theorem subsidy_growth_between {α β θ L r g : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθL : 0 < θ * L) (htt : g = θ * L - r) (heu : 1 + g = β * (1 + r))
    (hplan : 0 < β * θ * L - (1 - β)) :
    g = (β * θ * L - (1 - β)) / (1 + β) ∧
      (α * β * θ * L - (1 - β)) / (1 + α * β) < g ∧ g < β * θ * L - (1 - β) := by
  have hg : g = (β * θ * L - (1 - β)) / (1 + β) := by
    rw [eq_div_iff (by linarith)]
    nlinarith
  refine ⟨hg, ?_, ?_⟩
  · rw [hg, div_lt_div_iff₀ (by positivity) (by linarith)]
    have : 0 < θ * L * β * (1 - α) := by
      have : 0 < 1 - α := by linarith
      positivity
    nlinarith
  · rw [hg, div_lt_iff₀ (by linarith)]
    nlinarith

/-! ## Population size and growth: Kremer (98)–(102) -/

/-- O&R (99)–(101), p. 493: with `Y = A L^{1-α}` and Malthusian subsistence
`c̄ = Y/L`, the level of technology is `A = c̄ L^α`. -/
theorem kremer_technology {A L α cbar : ℝ} (hL : 0 < L) (hsub : cbar = A * L ^ (1 - α) / L) :
    A = cbar * L ^ α := by
  rw [hsub, Real.rpow_sub hL, Real.rpow_one]
  field_simp

/-- **Kremer's fundamental equation** O&R (102), p. 493: from (98) and (101),
`L_{t+1}^α - L_t^α = θ L_t^{1+α}` and `L_{t+1}/L_t = (1 + θ L_t)^{1/α}`. -/
theorem kremer_equation {α θ cbar L L' A A' : ℝ} (hα : 0 < α) (hL : 0 < L) (hL' : 0 < L')
    (hc : 0 < cbar) (hA : A = cbar * L ^ α) (hA' : A' = cbar * L' ^ α)
    (h98 : A' - A = θ * A * L) :
    L' ^ α - L ^ α = θ * L ^ (1 + α) ∧ L' / L = (1 + θ * L) ^ (1 / α) := by
  have hLa := Real.rpow_pos_of_pos hL α
  have h1 : L' ^ α - L ^ α = θ * L ^ (1 + α) := by
    rw [Real.rpow_add hL, Real.rpow_one]
    rw [hA, hA'] at h98
    have : cbar * (L' ^ α - L ^ α) = cbar * (θ * (L * L ^ α)) := by linarith
    have := mul_left_cancel₀ hc.ne' this
    linarith
  refine ⟨h1, ?_⟩
  have h2 : (L' / L) ^ α = 1 + θ * L := by
    rw [Real.div_rpow hL'.le hL.le, div_eq_iff hLa.ne']
    rw [Real.rpow_add hL, Real.rpow_one] at h1
    nlinarith
  rw [← h2, ← Real.rpow_mul (div_pos hL' hL).le, mul_one_div_cancel hα.ne', Real.rpow_one]

/-- **A larger population grows faster** (O&R p. 494): `L ↦ (1 + θL)^{1/α}` is strictly
increasing on `L ≥ 0`. -/
theorem kremer_growth_strictMono {α θ : ℝ} (hα : 0 < α) (hθ : 0 < θ) :
    StrictMonoOn (fun L : ℝ => (1 + θ * L) ^ (1 / α)) (Set.Ici 0) := by
  intro a ha b _ hab
  exact Real.rpow_lt_rpow (by nlinarith [Set.mem_Ici.mp ha]) (by nlinarith) (by positivity)

/-- **Kremer dynamics** (O&R (102)): along `L_{t+1} = L_t(1 + θL_t)^{1/α}` from `L_0 > 0`,
population rises without bound and the growth factor itself rises every period. -/
theorem kremer_path {α θ : ℝ} {L : ℕ → ℝ} (hα : 0 < α) (hθ : 0 < θ) (h0 : 0 < L 0)
    (hstep : ∀ t, L (t + 1) = L t * (1 + θ * L t) ^ (1 / α)) :
    (∀ t, L t < L (t + 1)) ∧ Tendsto L atTop atTop ∧
      ∀ t, (1 + θ * L t) ^ (1 / α) < (1 + θ * L (t + 1)) ^ (1 / α) := by
  set q := (1 + θ * L 0) ^ (1 / α) with hq
  have hq1 : 1 < q := Real.one_lt_rpow (by nlinarith) (by positivity)
  have hpos : ∀ t, 0 < L t ∧ L 0 * q ^ t ≤ L t := by
    intro t
    induction t with
    | zero => exact ⟨h0, by simp⟩
    | succ t ih =>
      have hge : q ≤ (1 + θ * L t) ^ (1 / α) := by
        apply Real.rpow_le_rpow (by nlinarith) _ (by positivity)
        have : L 0 ≤ L t := le_trans (by nlinarith [one_le_pow₀ hq1.le (n := t)]) ih.2
        nlinarith
      rw [hstep t, pow_succ]
      constructor
      · have := ih.1
        positivity
      · have := mul_le_mul ih.2 hge (by positivity) ih.1.le
        linarith
  have hgrow : ∀ t, L t < L (t + 1) := by
    intro t
    rw [hstep t]
    have : 1 < (1 + θ * L t) ^ (1 / α) :=
      Real.one_lt_rpow (by nlinarith [(hpos t).1]) (by positivity)
    nlinarith [(hpos t).1]
  refine ⟨hgrow, ?_, fun t => ?_⟩
  · apply tendsto_atTop_mono (fun t => (hpos t).2)
    exact (tendsto_pow_atTop_atTop_of_one_lt hq1).const_mul_atTop h0
  · exact kremer_growth_strictMono hα hθ (Set.mem_Ici.mpr (hpos t).1.le)
      (Set.mem_Ici.mpr (hpos (t + 1)).1.le) (hgrow t)

/-- **Growth accounting** (O&R p. 482): for `Y = A K^α L^{1-α}`,
`y_t - y_{t-1} = (a_t - a_{t-1}) + α(k_t - k_{t-1}) + (1-α)(l_t - l_{t-1})` in logs, exactly. -/
theorem growth_accounting {α A K L A' K' L' : ℝ} (hA : 0 < A) (hK : 0 < K) (hL : 0 < L)
    (hA' : 0 < A') (hK' : 0 < K') (hL' : 0 < L') :
    Real.log (A * K ^ α * L ^ (1 - α)) - Real.log (A' * K' ^ α * L' ^ (1 - α)) =
      (Real.log A - Real.log A') + α * (Real.log K - Real.log K') +
        (1 - α) * (Real.log L - Real.log L') := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hK, Real.log_rpow hL,
    Real.log_rpow hK', Real.log_rpow hL']
  ring

/-! ## Openness can lower growth: the Grossman–Helpman example (pp. 495–496), corrected -/

/-- A constant-returns technology on the factor orthant is superadditive:
`F(v + w) ≥ F(v) + F(w)` (homogeneity of degree one plus concavity). -/
theorem crs_superadditive {F : ℝ × ℝ → ℝ}
    (hom : ∀ t : ℝ, 0 < t → ∀ v : ℝ × ℝ, 0 ≤ v.1 → 0 ≤ v.2 → F (t • v) = t * F v)
    (conc : ConcaveOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) F)
    {v w : ℝ × ℝ} (hv1 : 0 ≤ v.1) (hv2 : 0 ≤ v.2) (hw1 : 0 ≤ w.1) (hw2 : 0 ≤ w.2) :
    F v + F w ≤ F (v + w) := by
  have hvS : v ∈ Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ) := ⟨hv1, hv2⟩
  have hwS : w ∈ Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ) := ⟨hw1, hw2⟩
  have hmid := conc.2 hvS hwS (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hsum : v + w = (2 : ℝ) • ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w) := by
    rw [smul_add, smul_smul, smul_smul]
    norm_num
  have h2 := hom 2 (by norm_num) ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w)
    (by simp; linarith) (by simp; linarith)
  rw [hsum, h2]
  simp only [smul_eq_mul] at hmid
  linarith

/-- `F(0) = 0` under constant returns. -/
theorem crs_zero {F : ℝ × ℝ → ℝ}
    (hom : ∀ t : ℝ, 0 < t → ∀ v : ℝ × ℝ, 0 ≤ v.1 → 0 ≤ v.2 → F (t • v) = t * F v) :
    F 0 = 0 := by
  have := hom 2 (by norm_num) 0 le_rfl le_rfl
  rw [smul_zero] at this
  linarith

/-- **Flag, O&R pp. 495–496: with the same `F` in both sectors the PPF is linear.** For any
feasible factor allocation, `X + Y = A F(Z_X, L_X) + A F(Z_Y, L_Y) ≤ A F(Z̄, L̄)`, and every
point of the line `X + Y = A F(Z̄, L̄)` is attained by a proportional split. -/
theorem gh_linear_ppf {F : ℝ × ℝ → ℝ}
    (hom : ∀ t : ℝ, 0 < t → ∀ v : ℝ × ℝ, 0 ≤ v.1 → 0 ≤ v.2 → F (t • v) = t * F v)
    (conc : ConcaveOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) F) {A : ℝ} (hA : 0 ≤ A)
    {vX vY : ℝ × ℝ} (h1 : 0 ≤ vX.1) (h2 : 0 ≤ vX.2) (h3 : 0 ≤ vY.1) (h4 : 0 ≤ vY.2) :
    A * F vX + A * F vY ≤ A * F (vX + vY) ∧
      ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
        A * F (lam • (vX + vY)) + A * F ((1 - lam) • (vX + vY)) = A * F (vX + vY) := by
  have hsup : A * F vX + A * F vY ≤ A * F (vX + vY) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (crs_superadditive hom conc h1 h2 h3 h4) hA
  refine ⟨hsup, fun lam hl0 hl1 => ?_⟩
  have hs1 : 0 ≤ (vX + vY).1 := by simp; linarith
  have hs2 : 0 ≤ (vX + vY).2 := by simp; linarith
  have key : ∀ m : ℝ, 0 ≤ m → F (m • (vX + vY)) = m * F (vX + vY) := by
    intro m hm
    rcases eq_or_lt_of_le hm with h | h
    · rw [← h, zero_smul, zero_mul, crs_zero hom]
    · exact hom m h _ hs1 hs2
  rw [key lam hl0, key (1 - lam) (by linarith)]
  ring

/-- **Complete specialisation** (the correct statement behind O&R p. 496): on a linear PPF
`X + Y ≤ M` (`X, Y ≥ 0`), if the relative price of `X` is `p > 1` the unique revenue maximum
is `(M, 0)`; if `p < 1` it is `(0, M)`. Factors do not move at the margin: all of them move. -/
theorem gh_specialisation {p M X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hXY : X + Y ≤ M) :
    (1 < p → p * X + Y ≤ p * M ∧ (p * X + Y = p * M → X = M ∧ Y = 0)) ∧
      (p < 1 → 0 ≤ p → p * X + Y ≤ M ∧ (p * X + Y = M → X = 0 ∧ Y = M)) := by
  constructor
  · intro hp
    refine ⟨by nlinarith, fun h => ?_⟩
    have hY0 : Y = 0 := by nlinarith
    exact ⟨by nlinarith, hY0⟩
  · intro hp hp0
    refine ⟨by nlinarith, fun h => ?_⟩
    have hX0 : X = 0 := by nlinarith
    exact ⟨hX0, by nlinarith⟩

/-- **The autarky price is 1 whatever the preferences** (O&R p. 496, flagged): if both goods
are produced in positive amounts at a revenue maximum on the linear PPF, then `p = 1`. -/
theorem gh_autarky_price {p M X Y : ℝ} (hp : 0 ≤ p) (hX : 0 < X) (hY : 0 < Y)
    (hXY : X + Y = M)
    (hmax : ∀ X' Y', 0 ≤ X' → 0 ≤ Y' → X' + Y' ≤ M → p * X' + Y' ≤ p * X + Y) : p = 1 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := hmax 0 M le_rfl (by linarith) (by linarith)
    nlinarith
  · have := hmax M 0 (by linarith) le_rfl (by linarith)
    nlinarith

/-- **Flag: the book's law of motion explodes.** With `A_{t+1} - A_t = θ X_t A_t` and
`X_t = A_t F_X` for a constant allocation (`F_X > 0`), the growth rate `θ A_t F_X` rises
strictly every period, so growth is not "a rate that depends on the share of factors". -/
theorem gh_growth_explodes {θ FX : ℝ} {A : ℕ → ℝ} (hθ : 0 < θ) (hF : 0 < FX) (h0 : 0 < A 0)
    (hlaw : ∀ t, A (t + 1) - A t = θ * (A t * FX) * A t) (t : ℕ) :
    θ * A t * FX < θ * A (t + 1) * FX := by
  have hpos : ∀ t, 0 < A t := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih => have := hlaw t; nlinarith [mul_pos (mul_pos hθ (mul_pos ih hF)) ih]
  have := hlaw t
  have hlt : A t < A (t + 1) := by
    nlinarith [mul_pos (mul_pos hθ (mul_pos (hpos t) hF)) (hpos t)]
  nlinarith [mul_pos hθ hF]

/-- **Corrected law of motion** (O&R p. 496): with `A_{t+1} - A_t = θ F(Z_X, L_X) A_t`
(learning proportional to `X_t/A_t`), a constant allocation gives constant growth
`θ F(Z_X, L_X)`: `A_t = A_0 (1 + θ F_X)ᵗ`. -/
theorem gh_growth_corrected {θ FX : ℝ} {A : ℕ → ℝ}
    (hlaw : ∀ t, A (t + 1) - A t = θ * FX * A t) (t : ℕ) :
    A t = A 0 * (1 + θ * FX) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have := hlaw t
    rw [pow_succ]
    linear_combination this + (1 + θ * FX) * ih

/-- **Supply responds to the price in the corrected (non-linear PPF) example** — revealed
preference on any technology set `T` (e.g. different factor intensities): if `(X₁, Y₁)`
maximises `p₁X + Y` and `(X₂, Y₂)` maximises `p₂X + Y` on `T` with `p₁ < p₂`, then
`X₁ ≤ X₂`, and `X₁ = X₂` forces `Y₁ = Y₂`. -/
theorem gh_supply_monotone {T : Set (ℝ × ℝ)} {p₁ p₂ : ℝ} {v₁ v₂ : ℝ × ℝ} (hv₁ : v₁ ∈ T)
    (hv₂ : v₂ ∈ T) (hmax₁ : ∀ v ∈ T, p₁ * v.1 + v.2 ≤ p₁ * v₁.1 + v₁.2)
    (hmax₂ : ∀ v ∈ T, p₂ * v.1 + v.2 ≤ p₂ * v₂.1 + v₂.2) (hp : p₁ < p₂) :
    v₁.1 ≤ v₂.1 ∧ (v₁.1 = v₂.1 → v₁.2 = v₂.2) := by
  have a := hmax₁ v₂ hv₂
  have b := hmax₂ v₁ hv₁
  refine ⟨by nlinarith, fun h => ?_⟩
  rw [h] at a b
  linarith

/-- **Opening to trade changes growth in the direction of the price change** (O&R p. 496,
corrected): with growth `θ X/A` (the corrected law), if the world price of `X` exceeds the
autarky price, growth is weakly higher (strictly if production moves); if below, weakly
lower. -/
theorem gh_trade_growth {T : Set (ℝ × ℝ)} {pA pW θ A : ℝ} {vA vW : ℝ × ℝ} (hθ : 0 < θ)
    (hA : 0 < A) (hvA : vA ∈ T) (hvW : vW ∈ T)
    (hmaxA : ∀ v ∈ T, pA * v.1 + v.2 ≤ pA * vA.1 + vA.2)
    (hmaxW : ∀ v ∈ T, pW * v.1 + v.2 ≤ pW * vW.1 + vW.2) :
    (pA < pW → θ * vA.1 / A ≤ θ * vW.1 / A ∧ (vA ≠ vW → θ * vA.1 / A < θ * vW.1 / A)) ∧
      (pW < pA → θ * vW.1 / A ≤ θ * vA.1 / A) := by
  constructor
  · intro hp
    obtain ⟨h1, h2⟩ := gh_supply_monotone hvA hvW hmaxA hmaxW hp
    refine ⟨by gcongr, fun hne => ?_⟩
    have hlt : vA.1 < vW.1 := by
      rcases eq_or_lt_of_le h1 with h | h
      · exact absurd (Prod.ext h (h2 h)) hne
      · exact h
    gcongr
  · intro hp
    have := (gh_supply_monotone hvW hvA hmaxW hmaxA hp).1
    gcongr

/-- **The static allocation is independent of `A`** (O&R p. 496): since `A` scales both
sectors, an allocation maximises `p A F_X + A F_Y` iff it maximises `p F_X + F_Y`. -/
theorem gh_static_independent_A {S : Set (ℝ × ℝ)} {fX fY : ℝ × ℝ → ℝ} {p A : ℝ}
    (hA : 0 < A) (s : ℝ × ℝ) :
    (∀ s' ∈ S, p * (A * fX s') + A * fY s' ≤ p * (A * fX s) + A * fY s) ↔
      (∀ s' ∈ S, p * fX s' + fY s' ≤ p * fX s + fY s) := by
  constructor
  · intro h s' hs'
    have := h s' hs'
    have e1 : p * (A * fX s') + A * fY s' = A * (p * fX s' + fY s') := by ring
    have e2 : p * (A * fX s) + A * fY s = A * (p * fX s + fY s) := by ring
    rw [e1, e2] at this
    exact le_of_mul_le_mul_left this hA
  · intro h s' hs'
    have := mul_le_mul_of_nonneg_left (h s' hs') hA.le
    linarith

/-! ## The subsidised equilibrium, verified in full (O&R p. 492) -/

/-- Scale factor of the subsidised monopoly quantity: `κ_s = (α/(1+r))^{1/(1-α)}`. -/
noncomputable def kappaS (α r : ℝ) : ℝ := (α / (1 + r)) ^ (1 / (1 - α))

/-- `κ_s > 0`. -/
theorem kappaS_pos {α r : ℝ} (hα : 0 < α) (hr : 0 < 1 + r) : 0 < kappaS α r :=
  Real.rpow_pos_of_pos (by positivity) _

/-- `κ_s^{1-α} = α/(1+r)`. -/
theorem kappaS_rpow {α r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < 1 + r) :
    kappaS α r ^ (1 - α) = α / (1 + r) := by
  unfold kappaS
  rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (by linarith), Real.rpow_one]

/-- The subsidised scalar identity `(1+r) κ_s = α κ_s^α`. -/
theorem kappaS_identity {α r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < 1 + r) :
    (1 + r) * kappaS α r = α * kappaS α r ^ α := by
  have hk := kappaS_pos hα hr
  have h : kappaS α r = kappaS α r ^ α * kappaS α r ^ (1 - α) := by
    rw [← Real.rpow_add hk, show α + (1 - α) = 1 by ring, Real.rpow_one]
  rw [kappaS_rpow hα hα1 hr] at h
  have e : (1 + r) * kappaS α r = (1 + r) * (kappaS α r ^ α * (α / (1 + r))) := by
    rw [← h]
  rw [e]
  field_simp

/-- The allocation along a **subsidised** balanced path (O&R p. 492): intermediate producers
receive `1/α` per dollar of sales, financed by a lump-sum tax. `L_Y = r/θ`,
`K̄ = κ_s L_Y`, market price `p̄ = 1 + r`, producer receipt `p̄/α`, profit
`Π̄ = ((1-α)/α)K̄`, `p_A = (1+r)Π̄/r`, wage `w_t = (1-α)L_Y^{-α}A_tK̄^α`, output
`Y_t = L_Y^{1-α}A_tK̄^α`, consumption `C_t = Y_t - A_{t+1}K̄`, the lump-sum tax equal to the
subsidy `(p̄/α - p̄)A_tK̄`, and household wealth `a_t = A_t(p̄K̄/α + p_A)`. -/
structure SubsidyAllocation (α θ r g A₀ LY K p prof pA : ℝ) (A w Y C a tx : ℕ → ℝ) : Prop where
  hLY : LY = r / θ
  hK : K = kappaS α r * LY
  hp : p = 1 + r
  hprof : prof = (1 - α) / α * K
  hpA : pA = (1 + r) * prof / r
  hA : ∀ t, A t = A₀ * (1 + g) ^ t
  hw : ∀ t, w t = (1 - α) * (LY ^ (-α) * A t * K ^ α)
  hY : ∀ t, Y t = LY ^ (1 - α) * A t * K ^ α
  hC : ∀ t, C t = Y t - A (t + 1) * K
  ha : ∀ t, a t = A t * (p / α * K + pA)
  htax : ∀ t, tx t = (p / α - p) * (A t * K)

namespace SubsidyAllocation

variable {α θ r g A₀ LY K p prof pA : ℝ} {A w Y C a tax : ℕ → ℝ}

/-- Scalar facts: `L_Y, K̄ > 0`, `Y_t = A_t κ_s^α L_Y`, `w_t = (1-α)A_tκ_s^α`, the market
price is the marginal product `α L_Y^{1-α}K̄^{α-1} = 1 + r`, producer revenue per blueprint
`(p̄/α)K̄ = κ_s^α L_Y` (all of output), and `θ p_A = (1-α)κ_s^α` (R&D arbitrage). -/
theorem facts (h : SubsidyAllocation α θ r g A₀ LY K p prof pA A w Y C a tax) (hα : 0 < α)
    (hα1 : α < 1) (hθ : 0 < θ) (hr : 0 < r) :
    0 < LY ∧ 0 < K ∧ (∀ t, Y t = A t * (kappaS α r ^ α * LY)) ∧
      (∀ t, w t = (1 - α) * A t * kappaS α r ^ α) ∧
      α * LY ^ (1 - α) * K ^ (α - 1) = 1 + r ∧ p / α * K = kappaS α r ^ α * LY ∧
      θ * pA = (1 - α) * kappaS α r ^ α := by
  have hr1 : 0 < 1 + r := by linarith
  have hk := kappaS_pos hα hr1
  have hid := kappaS_identity hα hα1 hr1
  have hLY : 0 < LY := by rw [h.hLY]; positivity
  have hK : 0 < K := by rw [h.hK]; positivity
  have hwage : LY ^ (-α) * K ^ α = kappaS α r ^ α := by
    rw [h.hK, Real.mul_rpow hk.le hLY.le, mul_left_comm, ← Real.rpow_add hLY, neg_add_cancel,
      Real.rpow_zero, mul_one]
  have hneg : kappaS α r ^ (α - 1) = (1 + r) / α := by
    rw [show α - 1 = -(1 - α) by ring, Real.rpow_neg hk.le, kappaS_rpow hα hα1 hr1, inv_div]
  refine ⟨hLY, hK, fun t => ?_, fun t => ?_, ?_, ?_, ?_⟩
  · rw [h.hY t, mul_comm (LY ^ (1 - α)), mul_assoc, h.hK, scale_output hk hLY]
  · rw [h.hw t, mul_comm (LY ^ (-α)) (A t), mul_assoc, hwage]
    ring
  · rw [mul_assoc, h.hK, scale_rpow hk hLY, hneg]
    field_simp
  · rw [h.hp, h.hK]
    have e : (1 + r) / α * (kappaS α r * LY) = (1 + r) * kappaS α r * LY / α := by ring
    rw [e, hid]
    field_simp
  · have e : θ * pA = (1 - α) * ((1 + r) * kappaS α r) / α := by
      rw [h.hpA, h.hprof, h.hK, h.hLY]
      field_simp
    rw [e, hid]
    field_simp

/-- **Firms optimise** in the subsidised economy (O&R p. 492): the final-goods producer
demands `K̄` at the market price `p̄ = 1 + r` (84); `K̄` maximises the subsidised monopoly
profit `L_Y^{1-α}K^α/(1+r) - K`, which equals `Π̄`; and `p_A` is the present value of `Π̄`. -/
theorem firms_optimal (h : SubsidyAllocation α θ r g A₀ LY K p prof pA A w Y C a tax)
    (hα : 0 < α) (hα1 : α < 1) (hθ : 0 < θ) (hr : 0 < r) :
    p = α * LY ^ (1 - α) * K ^ (α - 1) ∧
      (∀ x, 0 ≤ x → LY ^ (1 - α) * x ^ α - p * x ≤ LY ^ (1 - α) * K ^ α - p * K) ∧
      (∀ x, 0 ≤ x → LY ^ (1 - α) * x ^ α / (1 + r) - x ≤ prof) ∧
      HasSum (fun s : ℕ => prof * ((1 + r) ^ s)⁻¹) pA := by
  have hr1 : 0 < 1 + r := by linarith
  obtain ⟨hLY, hK, -, -, hfoc, -, -⟩ := h.facts hα hα1 hθ hr
  have hprice : p = α * LY ^ (1 - α) * K ^ (α - 1) := by rw [h.hp, hfoc]
  refine ⟨hprice, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · rw [hprice]
    exact finalGoods_optimal hα hα1 hLY hK hx
  · obtain ⟨h1, h2⟩ := subsidy_monopoly_optimal hα hα1 hr1 hLY hK hfoc hx
    rw [h.hprof, ← h2]
    exact h1
  · rw [h.hpA]
    exact blueprint_price hr

/-- **The government budget balances and R&D arbitrage holds** (O&R p. 492): the lump-sum
tax equals the subsidy, which is `(1-α)Y_t`; the R&D wage `p_A θ A_t` equals the final-goods
wage; blueprints grow at `g = θ(L - L_Y)`. -/
theorem labour_and_government (h : SubsidyAllocation α θ r g A₀ LY K p prof pA A w Y C a tax)
    {L : ℝ} (hα : 0 < α) (hα1 : α < 1) (hθ : 0 < θ) (hr : 0 < r) (htt : g = θ * L - r) :
    (∀ t, tax t = (1 - α) * Y t) ∧ (∀ t, pA * θ * A t = w t) ∧
      (∀ t, A (t + 1) - A t = θ * A t * (L - LY)) := by
  obtain ⟨-, -, hY, hw, -, hpK, hlab⟩ := h.facts hα hα1 hθ hr
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · rw [h.htax, hY t]
    have e : (p / α - p) * (A t * K) = (1 - α) * (A t * (p / α * K)) := by
      field_simp
    rw [e, hpK]
  · rw [hw t]
    linear_combination (A t) * hlab
  · rw [h.hA, h.hA, pow_succ, htt, h.hLY]
    field_simp
    ring

/-- **Goods market** in the subsidised economy: `C_t + A_{t+1}K̄ = Y_t`, `C_t = C₀(1+g)ᵗ`,
and `C₀ > 0` when `g < r`. -/
theorem goods_market (h : SubsidyAllocation α θ r g A₀ LY K p prof pA A w Y C a tax)
    (hα : 0 < α) (hα1 : α < 1) (hθ : 0 < θ) (hr : 0 < r) (hA₀ : 0 < A₀) (hgr : g < r) :
    (∀ t, C t + A (t + 1) * K = Y t) ∧ (∀ t, C t = C 0 * (1 + g) ^ t) ∧ 0 < C 0 := by
  have hr1 : 0 < 1 + r := by linarith
  obtain ⟨hLY, hK, hY, -, -, -, -⟩ := h.facts hα hα1 hθ hr
  have hid := kappaS_identity hα hα1 hr1
  have hk := kappaS_pos hα hr1
  have hCt : ∀ t, C t = A₀ * (kappaS α r ^ α * LY - (1 + g) * K) * (1 + g) ^ t := by
    intro t
    rw [h.hC, hY, h.hA, h.hA, pow_succ]
    ring
  refine ⟨fun t => by rw [h.hC]; ring, fun t => by rw [hCt t, hCt 0, pow_zero, mul_one], ?_⟩
  rw [hCt 0, pow_zero, mul_one]
  apply mul_pos hA₀
  have hka : kappaS α r ^ α = (1 + r) * kappaS α r / α := by
    rw [hid]
    field_simp
  rw [hka, h.hK]
  have : (1 + g) * α < 1 + r := by nlinarith
  rw [sub_pos, div_mul_eq_mul_div, lt_div_iff₀ hα]
  nlinarith [mul_pos hk hLY]

/-- **The household budget with lump-sum taxes** (O&R p. 492):
`a_{t+1} = (1+r)(a_t + w_t L - T_t - C_t)`. -/
theorem budget (h : SubsidyAllocation α θ r g A₀ LY K p prof pA A w Y C a tax) {L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hθ : 0 < θ) (hr : 0 < r) (htt : g = θ * L - r) :
    ∀ t, a (t + 1) = (1 + r) * a t + (1 + r) * (w t * L - tax t) - (1 + r) * C t := by
  intro t
  obtain ⟨hLY, hK, hY, hw, hfoc, hpK, hlab⟩ := h.facts hα hα1 hθ hr
  obtain ⟨htaxY, -, -⟩ := h.labour_and_government hα hα1 hθ hr htt
  have hgt : g = θ * (L - LY) := by
    rw [htt, h.hLY]
    field_simp
  have hnoarb : (1 + r) * (K + pA) = p / α * K + pA := by
    rw [h.hpA, h.hprof, h.hp]
    field_simp
    ring
  rw [h.ha, h.ha, h.hC, htaxY, hY, hw, h.hA, h.hA, pow_succ]
  have e : (1 - α) * kappaS α r ^ α * L =
      (1 - α) * kappaS α r ^ α * LY + θ * pA * (L - LY) := by
    rw [hlab]
    ring
  linear_combination (A₀ * (1 + g) ^ t) * (-(1 + r) * e + (1 + r) * pA * hgt -
    (1 + g) * hnoarb - (1 + r) * hpK)

/-- **The household's plan is optimal in the subsidised economy** (genuine infinite
horizon; lump-sum taxes enter as a reduction of labour income): with
`1 + g = [β(1+r)]^σ` and `g < r`, consumption `C_t` has finite utility and maximises utility
among all plans with nonnegative wealth satisfying the after-tax budget. -/
theorem household_optimal (h : SubsidyAllocation α θ r g A₀ LY K p prof pA A w Y C a tax)
    {β σ L : ℝ} (hα : 0 < α) (hα1 : α < 1) (hθ : 0 < θ) (hr : 0 < r) (hσ : 0 < σ)
    (hβ : 0 < β) (hβ1 : β < 1) (hA₀ : 0 < A₀) (hgr : g < r) (htt : g = θ * L - r)
    (heu : 1 + g = (β * (1 + r)) ^ σ) :
    Summable (fun t => β ^ t * crra σ (C t)) ∧
      ∀ a' C' : ℕ → ℝ, a' 0 = a 0 → (∀ t, 0 ≤ a' t) → (∀ t, 0 < C' t) →
        Budget (1 + r) (1 + r) (fun t => (1 + r) * (w t * L - tax t)) C' a' →
        Summable (fun t => β ^ t * crra σ (C' t)) →
        ∑' t, β ^ t * crra σ (C' t) ≤ ∑' t, β ^ t * crra σ (C t) := by
  have hr1 : 0 < 1 + r := by linarith
  obtain ⟨-, hCg, hC0⟩ := h.goods_market hα hα1 hθ hr hA₀ hgr
  have hG : 0 < 1 + g := by rw [heu]; exact Real.rpow_pos_of_pos (by positivity) σ
  have hCt : ∀ t, C t = C 0 * ((β * (1 + r)) ^ σ) ^ t := fun t => by rw [hCg t, heu]
  have hfun : (fun t => β ^ t * crra σ (C t)) =
      fun t => β ^ t * crra σ (C 0 * ((β * (1 + r)) ^ σ) ^ t) := by
    funext t
    rw [hCt t]
  have hsum : Summable (fun t => β ^ t * crra σ (C t)) := by
    rw [hfun, summable_balanced_iff hσ hβ hβ1 hr1 hC0, ← heu]
    linarith
  refine ⟨hsum, fun a' C' h0 ha' hC' hb' hs' => ?_⟩
  have hbud : Budget (1 + r) (1 + r) (fun t => (1 + r) * (w t * L - tax t)) C a :=
    fun t => h.budget hα hα1 hθ hr htt t
  have heuler : ∀ t, β ^ t * crraMU σ (C t) =
      crraMU σ (C 0) / (1 + r) * (1 + r) * ((1 + r) ^ t)⁻¹ := by
    intro t
    rw [div_mul_cancel₀ _ hr1.ne', hCt t]
    have := balanced_euler hσ hβ hr1 hC0 t
    rwa [mul_one] at this
  have hA : ∀ t, a t = A₀ * (p / α * K + pA) * (1 + g) ^ t := fun t => by
    rw [h.ha, h.hA]
    ring
  have htail := balanced_tail (lam := crraMU σ (C 0) / (1 + r)) (k₀ := A₀ * (p / α * K + pA))
    hr1 hG (by linarith)
  have htail' : Tendsto (fun T : ℕ => crraMU σ (C 0) / (1 + r) *
      ((1 + r) * (((1 + r) ^ T)⁻¹ * a T))) atTop (𝓝 0) := by
    refine htail.congr fun T => ?_
    rw [hA T]
  have := tsum_add_le_of_partial (δ := 0) (N := 0) hs' hsum htail' fun T _ => by
    rw [add_zero]
    exact welfare_partial_le hβ.le hr1 (div_nonneg (crraMU_pos σ hC0).le hr1.le)
      (fun t => crra_support hσ (hC' t) (by rw [hCg t]; positivity)) heuler hb' hbud h0 T
      (ha' T)
  rwa [add_zero] at this

end SubsidyAllocation

/-- **The subsidised balanced path is unique** (general `σ`): the subsidised TT curve
`g = θL - r` is strictly decreasing and the Euler curve strictly increasing. -/
theorem subsidy_bgp_unique {β σ θ L r₁ g₁ r₂ g₂ : ℝ} (hσ : 0 < σ) (hβ : 0 < β)
    (ht₁ : g₁ = θ * L - r₁) (he₁ : 1 + g₁ = (β * (1 + r₁)) ^ σ)
    (ht₂ : g₂ = θ * L - r₂) (he₂ : 1 + g₂ = (β * (1 + r₂)) ^ σ)
    (hr₁ : 0 < 1 + r₁) (hr₂ : 0 < 1 + r₂) : r₁ = r₂ ∧ g₁ = g₂ := by
  have hr : r₁ = r₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := euler_strictMono hσ hβ hr₁ hlt
      linarith
    · have := euler_strictMono hσ hβ hr₂ hgt
      linarith
  exact ⟨hr, by rw [ht₁, ht₂, hr]⟩

/-- **Existence of an interior subsidised balanced path** (general `σ`, `0 < β < 1`): there
is `(r, g)` with `g = θL - r`, `1 + g = [β(1+r)]^σ`, `g > 0`, `r > 0` iff
`θL > (1-β)/β`, i.e. iff the planner's growth rate `βθL - (1-β)` is positive. -/
theorem subsidy_bgp_exists_iff {β σ θ L : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hβ1 : β < 1) :
    (∃ r g, g = θ * L - r ∧ 1 + g = (β * (1 + r)) ^ σ ∧ 0 < g ∧ 0 < r) ↔
      (1 - β) / β < θ * L := by
  constructor
  · rintro ⟨r, g, ht, he, hg, hr⟩
    have h1 : 1 < (β * (1 + r)) ^ σ := by linarith
    have h2 : 1 < β * (1 + r) := (one_lt_growth_iff hσ (by positivity)).mp h1
    rw [div_lt_iff₀ hβ]
    nlinarith
  · intro hcond
    have hc := (div_lt_iff₀ hβ).mp hcond
    set φ : ℝ → ℝ := fun r => (β * (1 + r)) ^ σ - 1 - (θ * L - r) with hφ
    set a := 1 / β - 1 with ha
    have hapos : 0 < a := by
      rw [ha, div_sub_one hβ.ne']
      exact div_pos (by linarith) hβ
    have hab : a < θ * L := by
      rw [ha, div_sub_one hβ.ne', div_lt_iff₀ hβ]
      nlinarith
    have hcont : ContinuousOn φ (Set.Icc a (θ * L)) := by
      apply Continuous.continuousOn
      exact (((continuous_const.mul (continuous_const.add continuous_id)).rpow_const
        fun _ => Or.inr hσ.le).sub continuous_const).sub (continuous_const.sub continuous_id)
    have hφa : φ a < 0 := by
      simp only [hφ, ha]
      rw [show β * (1 + (1 / β - 1)) = 1 by field_simp; ring, Real.one_rpow]
      linarith
    have hφb : 0 < φ (θ * L) := by
      simp only [hφ]
      have h1 : 1 < β * (1 + θ * L) := by nlinarith
      have := (one_lt_growth_iff hσ (by positivity)).mpr h1
      linarith
    obtain ⟨r, hr, hφr⟩ := intermediate_value_Icc hab.le hcont ⟨hφa.le, hφb.le⟩
    have hra : a < r := by
      rcases eq_or_lt_of_le hr.1 with h | h
      · rw [← h] at hφr
        linarith
      · exact h
    have hrb : r < θ * L := by
      rcases eq_or_lt_of_le hr.2 with h | h
      · rw [h] at hφr
        linarith
      · exact h
    refine ⟨r, θ * L - r, rfl, ?_, by linarith, by linarith⟩
    simp only [hφ] at hφr
    linarith

/-! ## Market dynamics off the balanced path (log utility)

O&R p. 490 claim that with 100% depreciation "the economy jumps immediately to a steady
state". Capital per blueprint `K₀` (produced before date 0) is a state variable. We prove:
in every equilibrium the labour allocation and blueprint growth are at their balanced values
from date 0 (so that part of the claim is true), but `K_t` and the interest rate follow
`K_{t+1} = c K_t^α` and converge only asymptotically, unless `K₀ = K̄`. -/

/-- Discount factors for gross returns `R_t` (between `t-1` and `t`):
`D_0 = 1`, `D_{t+1} = D_t / R_{t+1}`. -/
noncomputable def discR (R : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => discR R t / R (t + 1)

/-- Discount factors are positive. -/
theorem discR_pos {R : ℕ → ℝ} (hR : ∀ t, 0 < R (t + 1)) (t : ℕ) : 0 < discR R t := by
  induction t with
  | zero => simp [discR]
  | succ t ih => simp only [discR]; exact div_pos ih (hR t)

/-- An optimal plan of a log household facing gross returns `R_{t+1}` and income `y_t`,
with budget `a_{t+1} = R_{t+1}(a_t + y_t - C_t)` and no borrowing (`a ≥ 0`). -/
structure LogHouseholdOptimal (β : ℝ) (R y a C : ℕ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ a t
  pos : ∀ t, 0 < C t
  budget : ∀ t, a (t + 1) = R (t + 1) * (a t + y t - C t)
  summable : Summable (fun t => β ^ t * Real.log (C t))
  optimal : ∀ a' C' : ℕ → ℝ, a' 0 = a 0 → (∀ t, 0 ≤ a' t) → (∀ t, 0 < C' t) →
    (∀ t, a' (t + 1) = R (t + 1) * (a' t + y t - C' t)) →
    Summable (fun t => β ^ t * Real.log (C' t)) →
    ∑' t, β ^ t * Real.log (C' t) ≤ ∑' t, β ^ t * Real.log (C t)

/-- **The log Euler equation is necessary**: at a household optimum with positive wealth at
`t + 1`, `C_{t+1} = β R_{t+1} C_t` (one-period perturbation). -/
theorem LogHouseholdOptimal.euler {β : ℝ} {R y a C : ℕ → ℝ} (hβ : 0 < β)
    (h : LogHouseholdOptimal β R y a C) (t : ℕ) (hR : 0 < R (t + 1)) (ha : 0 < a (t + 1)) :
    C (t + 1) = β * R (t + 1) * C t := by
  set φ : ℝ → ℝ := fun ε =>
    Real.log (C t - ε) + β * Real.log (C (t + 1) + R (t + 1) * ε) with hφ
  have hct := h.pos t
  have hct1 := h.pos (t + 1)
  have hmax : IsLocalMax φ 0 := by
    have hδ : 0 < min (C t) (min (a (t + 1) / R (t + 1)) (C (t + 1) / R (t + 1))) :=
      lt_min hct (lt_min (div_pos ha hR) (div_pos hct1 hR))
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with ε hε
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hε
    have h1 : |ε| < C t := lt_of_lt_of_le hε (min_le_left _ _)
    have h2 : |ε| * R (t + 1) < a (t + 1) := (lt_div_iff₀ hR).mp
      (lt_of_lt_of_le hε ((min_le_right _ _).trans (min_le_left _ _)))
    have h3 : |ε| * R (t + 1) < C (t + 1) := (lt_div_iff₀ hR).mp
      (lt_of_lt_of_le hε ((min_le_right _ _).trans (min_le_right _ _)))
    have e1 := neg_abs_le ε
    have e2 := le_abs_self ε
    set C' : ℕ → ℝ := fun s =>
      if s = t then C t - ε else if s = t + 1 then C (t + 1) + R (t + 1) * ε else C s with hC'
    set a' : ℕ → ℝ := fun s => if s = t + 1 then a (t + 1) + R (t + 1) * ε else a s with ha'
    have hC'pos : ∀ s, 0 < C' s := by
      intro s
      simp only [hC']
      split_ifs
      · linarith
      · nlinarith
      · exact h.pos s
    have ha'nn : ∀ s, 0 ≤ a' s := by
      intro s
      simp only [ha']
      split_ifs
      · nlinarith
      · exact h.nonneg s
    have hb' : ∀ s, a' (s + 1) = R (s + 1) * (a' s + y s - C' s) := by
      intro s
      have hb := h.budget s
      rcases (by omega : s = t ∨ s = t + 1 ∨ (s ≠ t ∧ s ≠ t + 1)) with hs | hs | ⟨hs1, hs2⟩
      · subst hs
        simp [hC', ha']
        linear_combination hb
      · subst hs
        simp [hC', ha']
        linear_combination hb
      · simp [hC', ha', hs1, hs2]
        linear_combination hb
    have hdec : (fun s => β ^ s * Real.log (C' s)) = fun s => β ^ s * Real.log (C s) +
        ((if s = t then β ^ t * (Real.log (C t - ε) - Real.log (C t)) else 0) +
          if s = t + 1 then β ^ (t + 1) * (Real.log (C (t + 1) + R (t + 1) * ε) -
            Real.log (C (t + 1))) else 0) := by
      funext s
      rcases (by omega : s = t ∨ s = t + 1 ∨ (s ≠ t ∧ s ≠ t + 1)) with hs | hs | ⟨hs1, hs2⟩
      · subst hs
        simp [hC']
        ring
      · subst hs
        simp [hC']
        ring
      · simp [hC', hs1, hs2]
    obtain ⟨hsum', htsum'⟩ := tsum_update_two h.summable t (t + 1)
      (β ^ t * (Real.log (C t - ε) - Real.log (C t)))
      (β ^ (t + 1) * (Real.log (C (t + 1) + R (t + 1) * ε) - Real.log (C (t + 1))))
    rw [← hdec] at hsum' htsum'
    have hopt := h.optimal a' C' (by simp [ha']) ha'nn hC'pos hb' hsum'
    rw [htsum'] at hopt
    have hβt : 0 < β ^ t := pow_pos hβ t
    have key : β ^ t * (φ ε - φ 0) ≤ 0 := by
      simp only [hφ, sub_zero, mul_zero, add_zero]
      rw [pow_succ] at hopt
      nlinarith
    by_contra hcon
    push Not at hcon
    have := mul_pos hβt (sub_pos.mpr hcon)
    linarith
  have d1 : HasDerivAt (fun ε : ℝ => Real.log (C t - ε)) ((C t)⁻¹ * (-1)) 0 := by
    have hs : HasDerivAt (fun ε : ℝ => C t - ε) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub (C t)
    have hc0 : HasDerivAt Real.log (C t)⁻¹ (C t - 0) := by
      rw [sub_zero]
      exact Real.hasDerivAt_log hct.ne'
    exact hc0.comp 0 hs
  have d2 : HasDerivAt (fun ε : ℝ => Real.log (C (t + 1) + R (t + 1) * ε))
      ((C (t + 1))⁻¹ * R (t + 1)) 0 := by
    have hs : HasDerivAt (fun ε : ℝ => C (t + 1) + R (t + 1) * ε) (R (t + 1)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (R (t + 1))).const_add (C (t + 1))
    have hc0 : HasDerivAt Real.log (C (t + 1))⁻¹ (C (t + 1) + R (t + 1) * 0) := by
      rw [mul_zero, add_zero]
      exact Real.hasDerivAt_log hct1.ne'
    exact hc0.comp 0 hs
  have hd := d1.add (d2.const_mul β)
  have h0 := hmax.hasDerivAt_eq_zero hd
  field_simp at h0
  linarith

/-- **No wasted wealth** (the transversality condition derived from optimality): at a
household optimum, discounted wealth `D_t a_t` cannot stay above a positive constant — else
consuming that constant extra at date 0 is feasible and strictly better. -/
theorem LogHouseholdOptimal.no_waste {β : ℝ} {R y a C : ℕ → ℝ}
    (h : LogHouseholdOptimal β R y a C) (hR : ∀ t, 0 < R (t + 1)) :
    ¬ ∃ ε, 0 < ε ∧ ∀ t, ε ≤ discR R (t + 1) * a (t + 1) := by
  rintro ⟨ε, hε, hbd⟩
  have hD := discR_pos hR
  set C' : ℕ → ℝ := fun s => if s = 0 then C 0 + ε else C s with hC'
  set a' : ℕ → ℝ := fun s => if s = 0 then a 0 else a s - ε / discR R s with ha'
  have hC'pos : ∀ s, 0 < C' s := by
    intro s
    simp only [hC']
    split_ifs
    · linarith [h.pos 0]
    · exact h.pos s
  have ha'nn : ∀ s, 0 ≤ a' s := by
    intro s
    simp only [ha']
    split_ifs with hs
    · exact h.nonneg 0
    · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      have := hbd t
      rw [sub_nonneg, div_le_iff₀ (hD _)]
      linarith
  have hb' : ∀ s, a' (s + 1) = R (s + 1) * (a' s + y s - C' s) := by
    intro s
    have hb := h.budget s
    have hDs : discR R (s + 1) = discR R s / R (s + 1) := rfl
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      simp only [ha', hC', Nat.add_one_ne_zero, ↓reduceIte]
      rw [hb, hDs]
      simp only [discR]
      field_simp [(hR 0).ne']
      ring
    · have hs1 : s ≠ 0 := by omega
      simp only [ha', hC', hs1, Nat.add_one_ne_zero, ↓reduceIte]
      rw [hb, hDs]
      field_simp [(hR s).ne', (hD s).ne']
      ring
  have hdec : (fun s => β ^ s * Real.log (C' s)) = fun s => β ^ s * Real.log (C s) +
      if s = 0 then Real.log (C 0 + ε) - Real.log (C 0) else 0 := by
    funext s
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      simp [hC']
    · have hs1 : s ≠ 0 := by omega
      simp [hC', hs1]
  obtain ⟨hsum', htsum'⟩ := tsum_update_one h.summable 0
    (Real.log (C 0 + ε) - Real.log (C 0))
  rw [← hdec] at hsum' htsum'
  have hopt := h.optimal a' C' (by simp [ha']) ha'nn hC'pos hb' hsum'
  rw [htsum'] at hopt
  have := Real.log_lt_log (h.pos 0) (by linarith : C 0 < C 0 + ε)
  linarith

/-- The market relations of the Romer economy along an arbitrary path (O&R §7.3.3, dated):
blueprints (81)–(82) with interior research `0 < L_{Y,t} < L`; monopoly pricing of capital
sold at `t + 1` (86)–(87), `R_{t+1} = α² L_{Y,t+1}^{1-α} K_{t+1}^{α-1}` (the gross interest
rate); goods-market clearing `C_t = Y_t - A_{t+1}K_{t+1}`; R&D arbitrage (91) per blueprint,
`θ p_{A,t} = (1-α) L_{Y,t}^{-α} K_t^α`; and the blueprint-value recursion (89),
`p_{A,t} = Π_t + p_{A,t+1}/R_{t+1}` with `Π_t = ((1-α)/α)K_{t+1}`. `K₀` is given. -/
structure RomerRel (α θ L : ℝ) (A LY K R C pA : ℕ → ℝ) : Prop where
  posA : ∀ t, 0 < A t
  posK : ∀ t, 0 < K t
  posC : ∀ t, 0 < C t
  LYpos : ∀ t, 0 < LY t
  LYlt : ∀ t, LY t < L
  research : ∀ t, A (t + 1) = A t * (1 + θ * (L - LY t))
  pricing : ∀ t, R (t + 1) = α ^ 2 * LY (t + 1) ^ (1 - α) * K (t + 1) ^ (α - 1)
  goods : ∀ t, C t = LY t ^ (1 - α) * A t * K t ^ α - A (t + 1) * K (t + 1)
  arbitrage : ∀ t, θ * pA t = (1 - α) * (LY t ^ (-α) * K t ^ α)
  blueprint : ∀ t, pA t = (1 - α) / α * K (t + 1) + pA (t + 1) / R (t + 1)

/-- `x^{1-a} = x · x^{-a}`. -/
theorem rpow_one_sub_eq {x a : ℝ} (hx : 0 < x) : x ^ (1 - a) = x * x ^ (-a) := by
  rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]

/-- `x^{a-1} · x = x^a`. -/
theorem rpow_sub_one_mul {x a : ℝ} (hx : 0 < x) : x ^ (a - 1) * x = x ^ a := by
  rw [← Real.rpow_add_one hx.ne', sub_add_cancel]

namespace RomerRel

variable {α θ L : ℝ} {A LY K R C pA : ℕ → ℝ}

/-- Scalar forms: with `m_t = L_{Y,t}^{-α}K_t^α`, output is `Y_t = A_t L_{Y,t} m_t`, the
capital share gives `R_{t+1}K_{t+1} = α² L_{Y,t+1} m_{t+1}`, and R&D arbitrage plus the
blueprint recursion give `α² L_{Y,t+1} m_t = K_{t+1}(1 + αθ L_{Y,t+1})`. -/
theorem scalar (h : RomerRel α θ L A LY K R C pA) (hα : 0 < α) (hα1 : α < 1) (t : ℕ) :
    LY t ^ (1 - α) * A t * K t ^ α = A t * LY t * (LY t ^ (-α) * K t ^ α) ∧
      R (t + 1) * K (t + 1) = α ^ 2 * LY (t + 1) * (LY (t + 1) ^ (-α) * K (t + 1) ^ α) ∧
      α ^ 2 * LY (t + 1) * (LY t ^ (-α) * K t ^ α) =
        K (t + 1) * (1 + α * θ * LY (t + 1)) := by
  have hL1 := h.LYpos (t + 1)
  have hK1 := h.posK (t + 1)
  have hY : LY t ^ (1 - α) * A t * K t ^ α = A t * LY t * (LY t ^ (-α) * K t ^ α) := by
    rw [rpow_one_sub_eq (h.LYpos t)]
    ring
  have hRK : R (t + 1) * K (t + 1) =
      α ^ 2 * LY (t + 1) * (LY (t + 1) ^ (-α) * K (t + 1) ^ α) := by
    rw [h.pricing t, rpow_one_sub_eq hL1, ← rpow_sub_one_mul hK1 (a := α)]
    ring
  refine ⟨hY, hRK, ?_⟩
  have ha0 := h.arbitrage t
  have ha1 := h.arbitrage (t + 1)
  have hb := h.blueprint t
  have hRpos : 0 < R (t + 1) := by
    rw [h.pricing t]
    have := Real.rpow_pos_of_pos hL1 (1 - α)
    have := Real.rpow_pos_of_pos hK1 (α - 1)
    positivity
  have hm1 : 0 < LY (t + 1) ^ (-α) * K (t + 1) ^ α := by
    have := Real.rpow_pos_of_pos hL1 (-α)
    have := Real.rpow_pos_of_pos hK1 α
    positivity
  -- θ p_{A,t+1} / R_{t+1} = (1-α) K_{t+1} / (α² L_{Y,t+1})
  have e1 : θ * (pA (t + 1) / R (t + 1)) * (α ^ 2 * LY (t + 1)) = (1 - α) * K (t + 1) := by
    rw [mul_div_assoc', ha1, div_mul_eq_mul_div, div_eq_iff hRpos.ne']
    have := hRK
    nlinarith [this]
  have h1a : 0 < 1 - α := by linarith
  have e2 : (1 - α) * (LY t ^ (-α) * K t ^ α) * (α ^ 2 * LY (t + 1)) =
      (1 - α) * (K (t + 1) * (1 + α * θ * LY (t + 1))) := by
    rw [← ha0, hb]
    have : θ * ((1 - α) / α * K (t + 1) + pA (t + 1) / R (t + 1)) * (α ^ 2 * LY (t + 1)) =
        θ * ((1 - α) / α * K (t + 1)) * (α ^ 2 * LY (t + 1)) +
          θ * (pA (t + 1) / R (t + 1)) * (α ^ 2 * LY (t + 1)) := by ring
    rw [this, e1]
    field_simp
    ring
  have := mul_left_cancel₀ h1a.ne' (by linarith [e2] :
    (1 - α) * (α ^ 2 * LY (t + 1) * (LY t ^ (-α) * K t ^ α)) =
      (1 - α) * (K (t + 1) * (1 + α * θ * LY (t + 1))))
  exact this

end RomerRel

/-- **The economy does not reach the balanced path in finite time unless it starts there**
(any utility; refutes O&R p. 490 "jumps immediately" when `K₀ ≠ K̄`). Along any path
satisfying the market relations and an Euler equation `C_{t+1} = (βR_{t+1})^σ C_t`, if
`L_Y` and `K` are constant from some date `T` on, they are constant from date 0. -/
theorem romer_no_finite_arrival {α β σ θ L : ℝ} {A LY K R C pA : ℕ → ℝ} (hα : 0 < α)
    (hα1 : α < 1) (hθ : 0 < θ) (h : RomerRel α θ L A LY K R C pA)
    (heuler : ∀ t, C (t + 1) = (β * R (t + 1)) ^ σ * C t) {T : ℕ}
    (hstat : ∀ t, T ≤ t → LY t = LY T ∧ K t = K T) :
    ∀ t, LY t = LY T ∧ K t = K T := by
  set Lb := LY T
  set Kb := K T
  have hLb : 0 < Lb := h.LYpos T
  have hKb : 0 < Kb := h.posK T
  -- downward induction: stationary from s+1 implies stationary from s
  have step : ∀ s, (∀ t, s + 1 ≤ t → LY t = Lb ∧ K t = Kb) →
      (∀ t, s ≤ t → LY t = Lb ∧ K t = Kb) := by
    intro s hs t hst
    rcases eq_or_lt_of_le hst with heq | hlt
    swap
    · exact hs t hlt
    subst heq
    obtain ⟨hL1, hK1⟩ := hs (s + 1) le_rfl
    obtain ⟨hL2, hK2⟩ := hs (s + 2) (by omega)
    have hK3 : K (s + 3) = Kb := (hs (s + 3) (by omega)).2
    obtain ⟨hY0, -, hArb0⟩ := h.scalar hα hα1 s
    obtain ⟨hY1, -, hArb1⟩ := h.scalar hα hα1 (s + 1)
    have hY2 : LY (s + 2) ^ (1 - α) * A (s + 2) * K (s + 2) ^ α =
        A (s + 2) * LY (s + 2) * (LY (s + 2) ^ (-α) * K (s + 2) ^ α) :=
      (h.scalar hα hα1 (s + 2)).1
    have hArb1' : α ^ 2 * LY (s + 2) * (LY (s + 1) ^ (-α) * K (s + 1) ^ α) =
        K (s + 2) * (1 + α * θ * LY (s + 2)) := hArb1
    set mb := Lb ^ (-α) * Kb ^ α with hmb
    have hmb0 : 0 < mb := by
      have := Real.rpow_pos_of_pos hLb (-α)
      have := Real.rpow_pos_of_pos hKb α
      positivity
    rw [hL1, hK1, hL2, hK2] at hArb1'
    rw [hL1, hK1] at hArb0
    have hms : LY s ^ (-α) * K s ^ α = mb := by
      have hαL : 0 < α ^ 2 * Lb := by positivity
      have e : α ^ 2 * Lb * (LY s ^ (-α) * K s ^ α) = α ^ 2 * Lb * mb := by
        rw [hArb0, hArb1']
      exact mul_left_cancel₀ hαL.ne' e
    have hR : R (s + 1) = R (s + 2) := by
      have e1 := h.pricing s
      have e2 : R (s + 2) = α ^ 2 * LY (s + 2) ^ (1 - α) * K (s + 2) ^ (α - 1) :=
        h.pricing (s + 1)
      rw [e1, e2, hL1, hK1, hL2, hK2]
    have hE1 := heuler s
    have hE2 : C (s + 2) = (β * R (s + 2)) ^ σ * C (s + 1) := heuler (s + 1)
    rw [← hR] at hE2
    have hCs := h.posC s
    have hC1 := h.posC (s + 1)
    have hratio : C (s + 2) * C s = C (s + 1) * C (s + 1) := by
      rw [hE2, hE1]
      ring
    have hA1 := h.research s
    have hA2 : A (s + 2) = A (s + 1) * (1 + θ * (L - LY (s + 1))) := h.research (s + 1)
    have hA3 : A (s + 3) = A (s + 2) * (1 + θ * (L - LY (s + 2))) := h.research (s + 2)
    have hg1 : C (s + 1) = LY (s + 1) ^ (1 - α) * A (s + 1) * K (s + 1) ^ α -
        A (s + 2) * K (s + 2) := h.goods (s + 1)
    have hg2 : C (s + 2) = LY (s + 2) ^ (1 - α) * A (s + 2) * K (s + 2) ^ α -
        A (s + 3) * K (s + 3) := h.goods (s + 2)
    have hc1 : C (s + 1) = A (s + 1) * (Lb * mb - (1 + θ * (L - Lb)) * Kb) := by
      rw [hg1, hY1, hA2, hL1, hK1, hK2]
      ring
    have hc2 : C (s + 2) = A (s + 1) * (1 + θ * (L - Lb)) *
        (Lb * mb - (1 + θ * (L - Lb)) * Kb) := by
      rw [hg2, hY2, hA3, hA2, hL1, hL2, hK2, hK3]
      ring
    have hc0 : C s = A s * (LY s * mb - (1 + θ * (L - LY s)) * Kb) := by
      rw [h.goods s, hY0, hA1, hK1, hms]
      ring
    have hcb : 0 < Lb * mb - (1 + θ * (L - Lb)) * Kb := by
      have := h.posC (s + 1)
      rw [hc1] at this
      exact pos_of_mul_pos_right this (h.posA (s + 1)).le
    have hLs : LY s = Lb := by
      rw [hc0, hc1, hc2, hA1] at hratio
      have hAs := h.posA s
      have hg : 0 < 1 + θ * (L - LY s) := by
        have := mul_pos hθ (sub_pos.mpr (h.LYlt s))
        linarith
      have hL0 : 0 < 1 + θ * L := by
        have := mul_pos hθ (lt_trans (h.LYpos T) (h.LYlt T))
        linarith
      have hz : A s * (1 + θ * (L - LY s)) * (Lb * mb - (1 + θ * (L - Lb)) * Kb) * A s *
          ((1 + θ * L) * mb) * (LY s - Lb) = 0 := by
        linear_combination hratio
      have hpos : 0 < A s * (1 + θ * (L - LY s)) * (Lb * mb - (1 + θ * (L - Lb)) * Kb) *
          A s * ((1 + θ * L) * mb) := by positivity
      rcases mul_eq_zero.mp hz with h2 | h2
      · exact absurd h2 hpos.ne'
      · linarith
    refine ⟨hLs, ?_⟩
    rw [hLs, hmb] at hms
    have hLa := Real.rpow_pos_of_pos hLb (-α)
    have hKa : K s ^ α = Kb ^ α := mul_left_cancel₀ hLa.ne' hms
    have hKs := h.posK s
    exact le_antisymm ((Real.rpow_le_rpow_iff hKs.le hKb.le hα).mp hKa.le)
      ((Real.rpow_le_rpow_iff hKb.le hKs.le hα).mp hKa.ge)
  have hall : ∀ n, ∀ t, T - n ≤ t → LY t = Lb ∧ K t = Kb := by
    intro n
    induction n with
    | zero => simpa using hstat
    | succ n ih =>
      rcases Nat.lt_or_ge n T with hn | hn
      · have e : T - (n + 1) + 1 = T - n := by omega
        exact step (T - (n + 1)) (by rw [e]; exact ih)
      · intro t ht
        exact ih t (by omega)
  exact fun t => hall T t (by omega)

/-- Geometric bound from a one-step contraction after `T₀`: if `0 < x_t ≤ M` and
`x_{t+1} ≤ β x_t` for `t ≥ T₀` (`0 < β ≤ 1`), then `β^{T₀}/M ≤ βᵗ/x_t` for every `t`. -/
theorem pow_div_lower {x : ℕ → ℝ} {β M : ℝ} {T₀ : ℕ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hx : ∀ t, 0 < x t) (hM : ∀ t, x t ≤ M) (hc : ∀ t, T₀ ≤ t → x (t + 1) ≤ β * x t) :
    ∀ t, β ^ T₀ / M ≤ β ^ t / x t := by
  have hM0 : 0 < M := lt_of_lt_of_le (hx 0) (hM 0)
  have hgeo : ∀ n, x (T₀ + n) ≤ β ^ n * x T₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hc (T₀ + n) (by omega)
      rw [show T₀ + (n + 1) = T₀ + n + 1 by ring, pow_succ]
      nlinarith
  intro t
  rw [div_le_div_iff₀ hM0 (hx t)]
  rcases le_or_gt T₀ t with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, t = T₀ + n := ⟨t - T₀, by omega⟩
    have h1 := hgeo n
    have h2 := hM T₀
    rw [pow_add]
    have : 0 ≤ β ^ T₀ := by positivity
    have : 0 ≤ β ^ n := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ β ^ n)]
  · have h1 : β ^ T₀ ≤ β ^ t := pow_le_pow_of_le_one hβ.le hβ1 h.le
    have := hM t
    nlinarith [pow_pos hβ T₀, hx t]

/-- A **market equilibrium of the Romer economy with log utility** from given `A₀`, `K₀`:
the market relations, household wealth equal to the market value of the intermediate-goods
firms `a_t = A_t(p_tK_t + p_{A,t})` (with `p_t = α L_{Y,t}^{1-α}K_t^{α-1}`), and the household's
consumption plan optimal given interest rates and wages `w_t L`. -/
structure RomerEq (α β θ L : ℝ) (A LY K R C pA a : ℕ → ℝ) : Prop where
  rel : RomerRel α θ L A LY K R C pA
  wealth : ∀ t, a t = A t * (α * LY t ^ (1 - α) * K t ^ (α - 1) * K t + pA t)
  household : LogHouseholdOptimal β R
    (fun t => (1 - α) * (LY t ^ (-α) * A t * K t ^ α) * L) a C

/-- **The market value of firms obeys the household budget** along any path satisfying the
market relations: `a_{t+1} = R_{t+1}(a_t + w_t L - C_t)` (the accounting of O&R §7.3.3). -/
theorem RomerRel.market_budget {α θ L : ℝ} {A LY K R C pA : ℕ → ℝ} (hα : 0 < α)
    (hα1 : α < 1) (h : RomerRel α θ L A LY K R C pA) (t : ℕ) :
    A (t + 1) * (α * LY (t + 1) ^ (1 - α) * K (t + 1) ^ (α - 1) * K (t + 1) + pA (t + 1)) =
      R (t + 1) * (A t * (α * LY t ^ (1 - α) * K t ^ (α - 1) * K t + pA t) +
        (1 - α) * (LY t ^ (-α) * A t * K t ^ α) * L - C t) := by
  obtain ⟨hY, -, -⟩ := h.scalar hα hα1 t
  have hKt := h.posK t
  have hK1 := h.posK (t + 1)
  have hpK : α * LY t ^ (1 - α) * K t ^ (α - 1) * K t = α * (LY t * (LY t ^ (-α) * K t ^ α)) := by
    rw [mul_assoc (α * LY t ^ (1 - α)), rpow_sub_one_mul hKt, rpow_one_sub_eq (h.LYpos t)]
    ring
  have hpK1 : α * LY (t + 1) ^ (1 - α) * K (t + 1) ^ (α - 1) * K (t + 1) =
      R (t + 1) * K (t + 1) / α := by
    rw [h.pricing t]
    field_simp
  have hArb := h.arbitrage t
  have hb := h.blueprint t
  have hRpos : 0 < R (t + 1) := by
    rw [h.pricing t]
    have := Real.rpow_pos_of_pos (h.LYpos (t + 1)) (1 - α)
    have := Real.rpow_pos_of_pos hK1 (α - 1)
    positivity
  rw [hpK1, hpK, h.goods t, hY, h.research t]
  have hpA : α * pA t * R (t + 1) = (1 - α) * K (t + 1) * R (t + 1) + α * pA (t + 1) := by
    rw [hb]
    field_simp
  have hwLA : θ * pA t * (L - LY t) = (1 - α) * (LY t ^ (-α) * K t ^ α) * (L - LY t) := by
    rw [hArb]
  field_simp
  linear_combination (-(A t) * (1 + θ * (L - LY t))) * hpA + (α * A t * R (t + 1)) * hwLA

set_option maxHeartbeats 1000000 in
-- the proof is one long case analysis with many nonlinear arithmetic steps
/-- **The Romer market equilibrium with log utility: exact transition** (the correct form of
O&R p. 490). In every equilibrium, from any `A₀, K₀ > 0`:
* the saving rule is `A_{t+1}K_{t+1} = α²β Y_t` (consumption `C_t = (1-α²β)Y_t`);
* final-goods labour is at its balanced value `L̄_Y = (1-β+θL)/(θ(1+αβ))` from date 0, so
  blueprints grow at `1 + ḡ = β(1 + αθL̄_Y)` from date 0 (the book's (96)).

Both the Euler equation and the transversality property are derived from household
optimality. -/
theorem romer_log_equilibrium {α β θ L : ℝ} {A LY K R C pA a : ℕ → ℝ} (hα : 0 < α)
    (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ)
    (h : RomerEq α β θ L A LY K R C pA a) :
    ∀ t, A (t + 1) * K (t + 1) = α ^ 2 * β * (LY t ^ (1 - α) * A t * K t ^ α) ∧
      LY t = (1 - β + θ * L) / (θ * (1 + α * β)) ∧
      A (t + 1) = A t * (β * (1 + α * θ * ((1 - β + θ * L) / (θ * (1 + α * β))))) := by
  have hr := h.rel
  set Y : ℕ → ℝ := fun t => LY t ^ (1 - α) * A t * K t ^ α with hYdef
  set m : ℕ → ℝ := fun t => LY t ^ (-α) * K t ^ α with hmdef
  have hm : ∀ t, 0 < m t := fun t => by
    have := Real.rpow_pos_of_pos (hr.LYpos t) (-α)
    have := Real.rpow_pos_of_pos (hr.posK t) α
    simp only [hmdef]
    positivity
  have hYm : ∀ t, Y t = A t * LY t * m t := fun t => (hr.scalar hα hα1 t).1
  have hYpos : ∀ t, 0 < Y t := fun t => by
    rw [hYm]
    have := hr.posA t
    have := hr.LYpos t
    have := hm t
    positivity
  have hR : ∀ t, 0 < R (t + 1) := fun t => by
    rw [hr.pricing t]
    have := Real.rpow_pos_of_pos (hr.LYpos (t + 1)) (1 - α)
    have := Real.rpow_pos_of_pos (hr.posK (t + 1)) (α - 1)
    positivity
  set I : ℕ → ℝ := fun t => A (t + 1) * K (t + 1) with hIdef
  have hIpos : ∀ t, 0 < I t := fun t => mul_pos (hr.posA _) (hr.posK _)
  have hRI : ∀ t, R (t + 1) * I t = α ^ 2 * Y (t + 1) := by
    intro t
    have := (hr.scalar hα hα1 t).2.1
    simp only [hIdef]
    rw [hYm (t + 1)]
    linear_combination (A (t + 1)) * this
  have hCYI : ∀ t, C t = Y t - I t := fun t => hr.goods t
  -- wealth, pA, and discounted wealth
  have hpA : ∀ t, θ * pA t = (1 - α) * m t := fun t => hr.arbitrage t
  have hpApos : ∀ t, 0 < pA t := fun t => by
    have := hpA t
    have := hm t
    have h1a : 0 < 1 - α := by linarith
    nlinarith
  have hpK : ∀ t, A t * (α * LY t ^ (1 - α) * K t ^ (α - 1) * K t) = α * Y t := by
    intro t
    simp only [hYdef]
    rw [mul_assoc (α * LY t ^ (1 - α)), rpow_sub_one_mul (hr.posK t)]
    ring
  have ha : ∀ t, a t = α * Y t + A t * pA t := fun t => by
    rw [h.wealth, mul_add, hpK]
  have hapos : ∀ t, 0 < a t := fun t => by
    rw [ha]
    have := hr.posA t
    have := hpApos t
    have := hYpos t
    positivity
  have heuler : ∀ t, C (t + 1) = β * R (t + 1) * C t :=
    fun t => h.household.euler hβ t (hR t) (hapos (t + 1))
  have hdisc : ∀ t, discR R t * C t = β ^ t * C 0 := by
    intro t
    induction t with
    | zero => simp [discR]
    | succ t ih =>
      simp only [discR]
      rw [heuler t, pow_succ]
      field_simp [(hR t).ne']
      linear_combination ih
  have hDpos : ∀ t, 0 < discR R t := discR_pos hR
  have hC0 := hr.posC 0
  have nowaste := h.household.no_waste hR
  -- saving share
  set z : ℕ → ℝ := fun t => I t / Y t with hzdef
  have hz0 : ∀ t, 0 < z t := fun t => div_pos (hIpos t) (hYpos t)
  have hz1 : ∀ t, z t < 1 := fun t => by
    have := hr.posC t
    rw [hCYI] at this
    rw [hzdef, div_lt_one (hYpos t)]
    linarith
  have hzrec : ∀ t, (1 - z (t + 1)) * z t = β * α ^ 2 * (1 - z t) := by
    intro t
    have hE := heuler t
    rw [hCYI, hCYI] at hE
    have hY1 := hYpos (t + 1)
    have hY0 := hYpos t
    have hRIt := hRI t
    have e : (Y (t + 1) - I (t + 1)) * I t = β * α ^ 2 * Y (t + 1) * (Y t - I t) := by
      rw [hE]
      linear_combination β * (Y t - I t) * hRIt
    simp only [hzdef]
    field_simp
    linarith [e]
  have hzstep : ∀ t, z (t + 1) - β * α ^ 2 = (z t - β * α ^ 2) / z t := by
    intro t
    have := hzrec t
    have := hz0 t
    field_simp
    linarith
  -- discounted wealth bounds
  have hDa1 : ∀ t, α * C 0 * (β ^ t / (1 - z t)) ≤ discR R t * a t := by
    intro t
    have hC := hr.posC t
    have hY := (hYpos t).ne'
    have hCz : C t = (1 - z t) * Y t := by
      rw [hCYI]
      simp only [hzdef]
      field_simp
    have hd := hdisc t
    have hDt := hDpos t
    have e : discR R t * (α * Y t) = α * C 0 * (β ^ t / (1 - z t)) := by
      have h1z : 0 < 1 - z t := by linarith [hz1 t]
      rw [div_eq_mul_inv]
      have : discR R t = β ^ t * C 0 / C t := by field_simp; linarith
      rw [this, hCz]
      field_simp
    rw [ha, mul_add, ← e]
    have := mul_pos hDt (mul_pos (hr.posA t) (hpApos t))
    linarith
  have hzeq : z 0 = β * α ^ 2 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- deviation grows geometrically and drives `z` negative
      have hdev : ∀ t, z t - β * α ^ 2 ≤ (z 0 - β * α ^ 2) * (1 / z 0) ^ t ∧
          z t ≤ z 0 := by
        intro t
        induction t with
        | zero => simp
        | succ t ih =>
          obtain ⟨ih1, ih2⟩ := ih
          have hzt := hz0 t
          have hneg : z t - β * α ^ 2 < 0 := by
            have : (z 0 - β * α ^ 2) * (1 / z 0) ^ t < 0 :=
              mul_neg_of_neg_of_pos (by linarith) (by have := hz0 0; positivity)
            linarith
          have hs := hzstep t
          have hle : (z t - β * α ^ 2) / z t ≤ (z t - β * α ^ 2) / z 0 := by
            rw [div_le_div_iff₀ hzt (hz0 0)]
            nlinarith [hneg, ih2]
          refine ⟨?_, ?_⟩
          · rw [hs, pow_succ]
            calc (z t - β * α ^ 2) / z t ≤ (z t - β * α ^ 2) / z 0 := hle
              _ = (z t - β * α ^ 2) * (1 / z 0) := by ring
              _ ≤ (z 0 - β * α ^ 2) * (1 / z 0) ^ t * (1 / z 0) :=
                mul_le_mul_of_nonneg_right ih1 (by have := hz0 0; positivity)
              _ = (z 0 - β * α ^ 2) * ((1 / z 0) ^ t * (1 / z 0)) := by ring
          · have : (z t - β * α ^ 2) / z t < z t - β * α ^ 2 := by
              rw [div_lt_iff₀ hzt]
              nlinarith [hz1 t]
            linarith
      have hq : 1 < 1 / z 0 := by rw [lt_div_iff₀ (hz0 0)]; linarith [hz1 0]
      obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop
        (β * α ^ 2 / (β * α ^ 2 - z 0))).exists
      have h1 := (hdev t).1
      have h2 := hz0 t
      have hd : 0 < β * α ^ 2 - z 0 := by linarith
      rw [div_lt_iff₀ hd] at ht
      nlinarith
    · -- over-saving: discounted wealth stays bounded away from zero
      have hinc : ∀ t, z 0 ≤ z t := by
        intro t
        induction t with
        | zero => exact le_rfl
        | succ t ih =>
          have hs := hzstep t
          have hzt := hz0 t
          have : 0 < z t - β * α ^ 2 := by linarith
          have : z t - β * α ^ 2 ≤ (z t - β * α ^ 2) / z t := by
            rw [le_div_iff₀ hzt]
            nlinarith [hz1 t]
          linarith
      have hq : β * α ^ 2 / z 0 < 1 := by rw [div_lt_one (hz0 0)]; exact hgt
      have hcontr : ∀ t, 1 - z (t + 1) ≤ β * α ^ 2 / z 0 * (1 - z t) := by
        intro t
        have hr' := hzrec t
        have hzt := hz0 t
        have h1 : 1 - z (t + 1) = β * α ^ 2 * (1 - z t) / z t := by
          field_simp
          linarith
        rw [h1, div_le_iff₀ hzt]
        have hq' : 1 ≤ z t / z 0 := (one_le_div (hz0 0)).mpr (hinc t)
        have h1z : 0 ≤ 1 - z t := by linarith [hz1 t]
        have hnn : 0 ≤ β * α ^ 2 * (1 - z t) := by positivity
        have e : β * α ^ 2 / z 0 * (1 - z t) * z t = β * α ^ 2 * (1 - z t) * (z t / z 0) := by
          field_simp
        rw [e]
        nlinarith [mul_le_mul_of_nonneg_left hq' hnn]
      have hgeo : ∀ t, 1 - z t ≤ (β * α ^ 2 / z 0) ^ t * (1 - z 0) := by
        intro t
        induction t with
        | zero => simp
        | succ t ih =>
          rw [pow_succ]
          have := hcontr t
          nlinarith [div_pos (by positivity : (0 : ℝ) < β * α ^ 2) (hz0 0)]
      have hα2 : 0 < 1 - α ^ 2 := by nlinarith
      obtain ⟨T₀, hT₀⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one
        (div_pos (by positivity : (0 : ℝ) < β * α ^ 2) (hz0 0)).le hq).eventually
        (gt_mem_nhds (show (0 : ℝ) < (1 - α ^ 2) / (1 - z 0) from
          div_pos hα2 (by linarith [hz1 0])))).exists_forall_of_atTop
      have hbig : ∀ t, T₀ ≤ t → α ^ 2 ≤ z t := by
        intro t ht
        have h1 := hgeo t
        have h2 := hT₀ t ht
        have h1z : 0 < 1 - z 0 := by linarith [hz1 0]
        rw [lt_div_iff₀ h1z] at h2
        linarith
      have hstep : ∀ t, T₀ ≤ t → 1 - z (t + 1) ≤ β * (1 - z t) := by
        intro t ht
        have hr' := hzrec t
        have hzt := hz0 t
        have h1 : 1 - z (t + 1) = β * α ^ 2 * (1 - z t) / z t := by
          field_simp
          linarith
        rw [h1, div_le_iff₀ hzt]
        have := hbig t ht
        have h1z : 0 ≤ 1 - z t := by linarith [hz1 t]
        nlinarith [mul_nonneg hβ.le h1z]
      have hlow := pow_div_lower (x := fun t => 1 - z t) (M := 1) hβ hβ1.le
        (fun t => by linarith [hz1 t]) (fun t => by linarith [hz0 t]) hstep
      apply nowaste
      refine ⟨α * C 0 * (β ^ T₀ / 1), by positivity, fun t => ?_⟩
      have hαC : 0 ≤ α * C 0 := by positivity
      calc α * C 0 * (β ^ T₀ / 1) ≤ α * C 0 * (β ^ (t + 1) / (1 - z (t + 1))) :=
            mul_le_mul_of_nonneg_left (hlow (t + 1)) hαC
        _ ≤ discR R (t + 1) * a (t + 1) := hDa1 (t + 1)
  have hzall : ∀ t, z t = β * α ^ 2 := by
    intro t
    induction t with
    | zero => exact hzeq
    | succ t ih =>
      have := hzstep t
      rw [ih, sub_self, zero_div] at this
      linarith
  have hIeq : ∀ t, I t = α ^ 2 * β * Y t := fun t => by
    have := hzall t
    simp only [hzdef] at this
    rw [div_eq_iff (hYpos t).ne'] at this
    linarith
  -- labour recursion
  have hLrec : ∀ t, LY (t + 1) * (1 + θ * L - θ * (1 + α * β) * LY t) = β * LY t := by
    intro t
    have harb := (hr.scalar hα hα1 t).2.2
    have hI := hIeq t
    simp only [hIdef] at hI
    rw [hr.research t, hYm t] at hI
    have hmt := hm t
    have hA := hr.posA t
    have e1 : (1 + θ * (L - LY t)) * K (t + 1) = α ^ 2 * β * (LY t * m t) := by
      have := mul_left_cancel₀ hA.ne' (show A t * ((1 + θ * (L - LY t)) * K (t + 1)) =
        A t * (α ^ 2 * β * (LY t * m t)) by linear_combination hI)
      exact this
    have e2 : α ^ 2 * m t * (LY (t + 1) * (1 + θ * (L - LY t))) =
        α ^ 2 * m t * (β * LY t * (1 + α * θ * LY (t + 1))) := by
      simp only [hmdef] at e1 ⊢
      linear_combination (1 + θ * (L - LY t)) * harb + (1 + α * θ * LY (t + 1)) * e1
    have := mul_left_cancel₀ (by positivity : α ^ 2 * m t ≠ 0) e2
    linear_combination this
  set Lb := (1 - β + θ * L) / (θ * (1 + α * β)) with hLb
  have hdLb : 1 + θ * L - θ * (1 + α * β) * Lb = β := by
    rw [hLb]
    field_simp
    ring
  have hLpos := hr.LYpos
  have hLlt := hr.LYlt
  have hdpos : ∀ t, 0 < 1 + θ * L - θ * (1 + α * β) * LY t := by
    intro t
    have := hLrec t
    have h1 := hLpos (t + 1)
    have h2 := hLpos t
    by_contra hle
    push Not at hle
    nlinarith
  have hL0 : LY 0 = Lb := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- research share → L: blueprint wealth explodes relative to discounting
      have hq0 : β < 1 + θ * L - θ * (1 + α * β) * LY 0 := by
        have : θ * (1 + α * β) * LY 0 < θ * (1 + α * β) * Lb :=
          mul_lt_mul_of_pos_left hlt (by positivity)
        linarith
      have hdec : ∀ t, LY t ≤ LY 0 ∧ LY (t + 1) ≤ β / (1 + θ * L - θ * (1 + α * β) * LY 0) *
          LY t := by
        intro t
        induction t with
        | zero =>
          refine ⟨le_rfl, ?_⟩
          have := hLrec 0
          rw [div_mul_eq_mul_div, le_div_iff₀ (hdpos 0)]
          linarith
        | succ t ih =>
          have hq1 : β / (1 + θ * L - θ * (1 + α * β) * LY 0) < 1 := by
            rw [div_lt_one (hdpos 0)]; exact hq0
          have h1 : LY (t + 1) ≤ LY 0 := by
            have := ih.2
            have := hLpos t
            nlinarith [ih.1, div_pos hβ (hdpos 0)]
          refine ⟨h1, ?_⟩
          have hd : 1 + θ * L - θ * (1 + α * β) * LY 0 ≤
              1 + θ * L - θ * (1 + α * β) * LY (t + 1) := by
            have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ θ * (1 + α * β))
            linarith
          have := hLrec (t + 1)
          rw [div_mul_eq_mul_div, le_div_iff₀ (hdpos 0)]
          nlinarith [hLpos (t + 2), hLpos (t + 1)]
      set q := β / (1 + θ * L - θ * (1 + α * β) * LY 0) with hqdef
      have hq1 : q < 1 := by rw [hqdef, div_lt_one (hdpos 0)]; exact hq0
      have hq0' : 0 < q := div_pos hβ (hdpos 0)
      have hgeo : ∀ t, LY t ≤ q ^ t * LY 0 := by
        intro t
        induction t with
        | zero => simp
        | succ t ih =>
          rw [pow_succ]
          nlinarith [(hdec t).2]
      have hLpos0 : 0 < L := lt_trans (hLpos 0) (hLlt 0)
      obtain ⟨T₀, hT₀⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0'.le hq1).eventually
        (gt_mem_nhds (show (0 : ℝ) < L / (1 + α * β) / LY 0 from by
          have := hLpos 0
          positivity))).exists_forall_of_atTop
      have hsmall : ∀ t, T₀ ≤ t → LY t ≤ L / (1 + α * β) := by
        intro t ht
        have h1 := hgeo t
        have h2 := hT₀ t ht
        rw [lt_div_iff₀ (hLpos 0)] at h2
        linarith
      have hstep : ∀ t, T₀ ≤ t → LY (t + 1) ≤ β * LY t := by
        intro t ht
        have hs := hsmall t ht
        have hd1 : 1 ≤ 1 + θ * L - θ * (1 + α * β) * LY t := by
          rw [le_div_iff₀ (by positivity)] at hs
          nlinarith
        have := hLrec t
        nlinarith [hLpos (t + 1), hLpos t]
      have hlow := pow_div_lower (x := LY) (M := L) hβ hβ1.le hLpos (fun t => (hLlt t).le)
        hstep
      -- discounted blueprint wealth ≥ const · βᵗ / L_{Y,t}
      have hz := hzall
      have h1z : 0 < 1 - β * α ^ 2 := by nlinarith
      apply nowaste
      refine ⟨C 0 * (1 - α) / (θ * (1 - β * α ^ 2)) * (β ^ T₀ / L), by
        have : 0 < 1 - α := by linarith
        have := hLpos0
        positivity, fun t => ?_⟩
      have hC : C (t + 1) = (1 - β * α ^ 2) * (A (t + 1) * LY (t + 1) * m (t + 1)) := by
        rw [hCYI, hIeq, hYm]
        ring
      have hd := hdisc (t + 1)
      have hDt := hDpos (t + 1)
      have hAt := hr.posA (t + 1)
      have hmt := hm (t + 1)
      have hLt := hLpos (t + 1)
      have hApA : A (t + 1) * pA (t + 1) = A (t + 1) * ((1 - α) * m (t + 1) / θ) := by
        rw [← hpA (t + 1)]
        field_simp
      have hkey : discR R (t + 1) * (A (t + 1) * pA (t + 1)) =
          C 0 * (1 - α) / (θ * (1 - β * α ^ 2)) * (β ^ (t + 1) / LY (t + 1)) := by
        have hD : discR R (t + 1) = β ^ (t + 1) * C 0 / C (t + 1) := by
          have := hr.posC (t + 1)
          field_simp
          linarith
        rw [hD, hApA, hC]
        field_simp
      have hle := hlow (t + 1)
      have hc0 : 0 ≤ C 0 * (1 - α) / (θ * (1 - β * α ^ 2)) := by
        have : 0 < 1 - α := by linarith
        positivity
      have hwa : discR R (t + 1) * (A (t + 1) * pA (t + 1)) ≤ discR R (t + 1) * a (t + 1) := by
        rw [ha, mul_add]
        have := mul_pos hDt (mul_pos hα (hYpos (t + 1)))
        linarith
      calc C 0 * (1 - α) / (θ * (1 - β * α ^ 2)) * (β ^ T₀ / L)
          ≤ C 0 * (1 - α) / (θ * (1 - β * α ^ 2)) * (β ^ (t + 1) / LY (t + 1)) :=
            mul_le_mul_of_nonneg_left hle hc0
        _ = discR R (t + 1) * (A (t + 1) * pA (t + 1)) := hkey.symm
        _ ≤ _ := hwa
    · -- final-goods labour would have to exceed `L`
      have hq0 : 1 + θ * L - θ * (1 + α * β) * LY 0 < β := by
        have : θ * (1 + α * β) * Lb < θ * (1 + α * β) * LY 0 :=
          mul_lt_mul_of_pos_left hgt (by positivity)
        linarith
      set q := β / (1 + θ * L - θ * (1 + α * β) * LY 0) with hqdef
      have hq1 : 1 < q := by rw [hqdef, one_lt_div (hdpos 0)]; exact hq0
      have hinc : ∀ t, LY 0 ≤ LY t ∧ q * LY t ≤ LY (t + 1) := by
        intro t
        induction t with
        | zero =>
          refine ⟨le_rfl, ?_⟩
          have := hLrec 0
          rw [hqdef, div_mul_eq_mul_div, div_le_iff₀ (hdpos 0)]
          linarith
        | succ t ih =>
          have h1 : LY 0 ≤ LY (t + 1) := by nlinarith [ih.1, ih.2, hLpos t]
          refine ⟨h1, ?_⟩
          have hd : 1 + θ * L - θ * (1 + α * β) * LY (t + 1) ≤
              1 + θ * L - θ * (1 + α * β) * LY 0 := by
            have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ θ * (1 + α * β))
            linarith
          have := hLrec (t + 1)
          rw [hqdef, div_mul_eq_mul_div, div_le_iff₀ (hdpos 0)]
          nlinarith [hLpos (t + 2), hLpos (t + 1), hdpos (t + 1)]
      have hgeo : ∀ t, q ^ t * LY 0 ≤ LY t := by
        intro t
        induction t with
        | zero => simp
        | succ t ih =>
          rw [pow_succ]
          nlinarith [(hinc t).2, lt_trans one_pos hq1]
      obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq1).eventually_gt_atTop
        (L / LY 0)).exists
      have := hgeo t
      have := hLlt t
      rw [div_lt_iff₀ (hLpos 0)] at ht
      linarith
  have hLall : ∀ t, LY t = Lb := by
    intro t
    induction t with
    | zero => exact hL0
    | succ t ih =>
      have := hLrec t
      rw [ih, hdLb] at this
      have := mul_right_cancel₀ hβ.ne' (show LY (t + 1) * β = Lb * β by linarith)
      exact this
  intro t
  refine ⟨hIeq t, hLall t, ?_⟩
  rw [hr.research t, hLall t]
  congr 1
  rw [hLb]
  field_simp
  ring

/-- **Sufficiency for the log household** (supporting hyperplane with time-varying returns):
a feasible plan with `D_t C_t = βᵗ C₀` (the Euler equation) and `D_T a_T → 0` (transversality)
is optimal. -/
theorem logHousehold_sufficient {β : ℝ} {R y a C : ℕ → ℝ} (hβ : 0 < β)
    (hR : ∀ t, 0 < R (t + 1)) (ha : ∀ t, 0 ≤ a t) (hC : ∀ t, 0 < C t)
    (hb : ∀ t, a (t + 1) = R (t + 1) * (a t + y t - C t))
    (hs : Summable (fun t => β ^ t * Real.log (C t)))
    (heu : ∀ t, discR R t * C t = β ^ t * C 0)
    (htvc : Tendsto (fun T => discR R T * a T) atTop (𝓝 0)) :
    LogHouseholdOptimal β R y a C := by
  have hD := discR_pos hR
  have hC0 := hC 0
  have hpv : ∀ (a' C' : ℕ → ℝ), (∀ t, a' (t + 1) = R (t + 1) * (a' t + y t - C' t)) →
      ∀ T, ∑ t ∈ range T, discR R t * C' t =
        a' 0 + ∑ t ∈ range T, discR R t * y t - discR R T * a' T := by
    intro a' C' hb' T
    induction T with
    | zero => simp [discR]
    | succ T ih =>
      rw [sum_range_succ, sum_range_succ, ih, hb' T]
      simp only [discR]
      field_simp [(hR T).ne']
      ring
  refine ⟨ha, hC, hb, hs, fun a' C' h0 ha' hC' hb' hs' => ?_⟩
  have hpart : ∀ T, ∑ t ∈ range T, β ^ t * Real.log (C' t) ≤
      ∑ t ∈ range T, β ^ t * Real.log (C t) + discR R T * a T / C 0 := by
    intro T
    have hsupp : ∀ t, β ^ t * Real.log (C' t) ≤ β ^ t * Real.log (C t) +
        (discR R t * C' t - discR R t * C t) / C 0 := by
      intro t
      have hl := Real.log_le_sub_one_of_pos (div_pos (hC' t) (hC t))
      rw [Real.log_div (hC' t).ne' (hC t).ne'] at hl
      have e : β ^ t * (C' t / C t - 1) = (discR R t * C' t - discR R t * C t) / C 0 := by
        have h1 := heu t
        have hCt := hC t
        field_simp
        linear_combination (C t - C' t) * h1
      nlinarith [pow_pos hβ t]
    have h1 := sum_le_sum fun t (_ : t ∈ range T) => hsupp t
    rw [sum_add_distrib, ← sum_div, sum_sub_distrib, hpv a' C' hb' T, hpv a C hb T, h0] at h1
    have : 0 ≤ discR R T * a' T / C 0 := div_nonneg (mul_nonneg (hD T).le (ha' T)) hC0.le
    have e : (a 0 + ∑ t ∈ range T, discR R t * y t - discR R T * a' T -
        (a 0 + ∑ t ∈ range T, discR R t * y t - discR R T * a T)) / C 0 =
        discR R T * a T / C 0 - discR R T * a' T / C 0 := by ring
    linarith
  have htail : Tendsto (fun T => discR R T * a T / C 0) atTop (𝓝 0) := by
    simpa using htvc.div_const (C 0)
  have h2 := hs.hasSum.tendsto_sum_nat.add htail
  rw [add_zero] at h2
  exact le_of_tendsto_of_tendsto hs'.hasSum.tendsto_sum_nat h2 (Eventually.of_forall hpart)

/-- The balanced final-goods labour of the log economy, `L̄_Y = (1-β+θL)/(θ(1+αβ))` (O&R (92),
(95)). -/
noncomputable def romerLbar (α β θ L : ℝ) : ℝ := (1 - β + θ * L) / (θ * (1 + α * β))

/-- Capital per blueprint on the equilibrium path: `K_{t+1} = (α²β L̄^{1-α}/G) K_t^α` with
`G = β(1 + αθL̄)`. -/
noncomputable def romerK (α β θ L K₀ : ℝ) : ℕ → ℝ
  | 0 => K₀
  | t + 1 => α ^ 2 * β * romerLbar α β θ L ^ (1 - α) * romerK α β θ L K₀ t ^ α /
      (β * (1 + α * θ * romerLbar α β θ L))

/-- `romerK` stays positive. -/
theorem romerK_pos {α β θ L K₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hθ : 0 < θ)
    (hLb : 0 < romerLbar α β θ L) (hK₀ : 0 < K₀) (t : ℕ) : 0 < romerK α β θ L K₀ t := by
  induction t with
  | zero => exact hK₀
  | succ t ih =>
    simp only [romerK]
    have := Real.rpow_pos_of_pos hLb (1 - α)
    have := Real.rpow_pos_of_pos ih α
    positivity

/-- **Existence: the explicit transition path is a market equilibrium** (log utility, any
`A₀, K₀ > 0`, interior research `θL > (1-β)/(αβ)`): `L_{Y,t} = L̄_Y`, `A_t = A₀Gᵗ`, `K_t` as in
`romerK`, the monopoly interest rate, `C_t = (1-α²β)Y_t`, blueprint value from arbitrage, and
market wealth satisfy every equilibrium condition, including household optimality. -/
theorem romer_log_exists {α β θ L A₀ K₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hA₀ : 0 < A₀) (hK₀ : 0 < K₀)
    (hint : (1 - β) / (α * β) < θ * L) :
    RomerEq α β θ L
      (fun t => A₀ * (β * (1 + α * θ * romerLbar α β θ L)) ^ t)
      (fun _ => romerLbar α β θ L) (romerK α β θ L K₀)
      (fun t => α ^ 2 * romerLbar α β θ L ^ (1 - α) * romerK α β θ L K₀ t ^ (α - 1))
      (fun t => (1 - α ^ 2 * β) * (romerLbar α β θ L ^ (1 - α) *
        (A₀ * (β * (1 + α * θ * romerLbar α β θ L)) ^ t) * romerK α β θ L K₀ t ^ α))
      (fun t => (1 - α) * (romerLbar α β θ L ^ (-α) * romerK α β θ L K₀ t ^ α) / θ)
      (fun t => A₀ * (β * (1 + α * θ * romerLbar α β θ L)) ^ t *
        (α * romerLbar α β θ L ^ (1 - α) * romerK α β θ L K₀ t ^ (α - 1) * romerK α β θ L K₀ t +
          (1 - α) * (romerLbar α β θ L ^ (-α) * romerK α β θ L K₀ t ^ α) / θ)) := by
  set Lb := romerLbar α β θ L with hLbdef
  set G := β * (1 + α * θ * Lb) with hG
  set K := romerK α β θ L K₀ with hK
  have hc := (div_lt_iff₀ (by positivity : 0 < α * β)).mp hint
  have hθL : 0 < θ * L := by
    by_contra hn
    push Not at hn
    nlinarith [mul_pos hα hβ]
  have hLb : 0 < Lb := by
    rw [hLbdef, romerLbar]
    apply div_pos _ (by positivity)
    linarith
  have hLbL : Lb < L := by
    rw [hLbdef, romerLbar, div_lt_iff₀ (by positivity)]
    nlinarith
  have hGeq : G = 1 + θ * (L - Lb) := by
    rw [hG, hLbdef, romerLbar]
    field_simp
    ring
  have hGpos : 0 < G := by positivity
  have hKpos : ∀ t, 0 < K t := romerK_pos hα hβ hθ hLb hK₀
  have hKs : ∀ t, K (t + 1) = α ^ 2 * β * Lb ^ (1 - α) * K t ^ α / G := fun t => rfl
  have hab : 0 < 1 - α ^ 2 * β := by nlinarith
  have hLa := Real.rpow_pos_of_pos hLb (1 - α)
  have hLn := Real.rpow_pos_of_pos hLb (-α)
  have hLsplit : Lb ^ (1 - α) = Lb * Lb ^ (-α) := rpow_one_sub_eq hLb
  have hKK : ∀ t, K t ^ (α - 1) * K t = K t ^ α := fun t => rpow_sub_one_mul (hKpos t)
  set A : ℕ → ℝ := fun t => A₀ * G ^ t with hAdef
  have hApos : ∀ t, 0 < A t := fun t => by simp only [hAdef]; positivity
  have hAK : ∀ t, A (t + 1) * K (t + 1) = α ^ 2 * β * (Lb ^ (1 - α) * A t * K t ^ α) := by
    intro t
    simp only [hAdef]
    rw [hKs, pow_succ]
    field_simp
  have hrel : RomerRel α θ L A (fun _ => Lb) K
      (fun t => α ^ 2 * Lb ^ (1 - α) * K t ^ (α - 1))
      (fun t => (1 - α ^ 2 * β) * (Lb ^ (1 - α) * A t * K t ^ α))
      (fun t => (1 - α) * (Lb ^ (-α) * K t ^ α) / θ) := by
    refine ⟨hApos, hKpos, fun t => ?_, fun _ => hLb, fun _ => hLbL, fun t => ?_, fun t => rfl,
      fun t => ?_, fun t => ?_, fun t => ?_⟩
    · have := hApos t
      have := Real.rpow_pos_of_pos (hKpos t) α
      positivity
    · simp only [hAdef]
      rw [pow_succ, ← hGeq]
      ring
    · rw [hAK t]
      ring
    · field_simp
    · have hK1 := hKpos (t + 1)
      have hk1 : K (t + 1) ^ (α - 1) * K (t + 1) = K (t + 1) ^ α := hKK (t + 1)
      have e1 : (1 - α) * (Lb ^ (-α) * K (t + 1) ^ α) / θ /
          (α ^ 2 * Lb ^ (1 - α) * K (t + 1) ^ (α - 1)) =
          (1 - α) * K (t + 1) / (θ * α ^ 2 * Lb) := by
        rw [hLsplit, ← hk1]
        have := Real.rpow_pos_of_pos hK1 (α - 1)
        field_simp
      rw [e1, hKs t, hG]
      have hGne : (1 + α * θ * Lb) ≠ 0 := by positivity
      rw [hLsplit]
      field_simp
      ring
  set Rf : ℕ → ℝ := fun t => α ^ 2 * Lb ^ (1 - α) * K t ^ (α - 1) with hRf
  set Cf : ℕ → ℝ := fun t => (1 - α ^ 2 * β) * (Lb ^ (1 - α) * A t * K t ^ α) with hCf
  have hRpos : ∀ t, 0 < Rf (t + 1) := fun t => by
    have := Real.rpow_pos_of_pos (hKpos (t + 1)) (α - 1)
    simp only [hRf]
    positivity
  have hCpos : ∀ t, 0 < Cf t := hrel.posC
  -- summability of log consumption
  have hsum : Summable (fun t => β ^ t * Real.log (Cf t)) := by
    set cc := α ^ 2 * β * Lb ^ (1 - α) / G with hcc
    set kb := Real.log cc / (1 - α)
    have hc0 : 0 < cc := by positivity
    have hkb : kb * (1 - α) = Real.log cc := by
      have h1a : (1 - α) ≠ 0 := by linarith
      simp only [kb]
      field_simp
    have hlogK : ∀ t, Real.log (K t) = kb + α ^ t * (Real.log K₀ - kb) := by
      intro t
      induction t with
      | zero => simp [hK, romerK]
      | succ t ih =>
        rw [hKs t, show α ^ 2 * β * Lb ^ (1 - α) * K t ^ α / G = cc * K t ^ α by
          rw [hcc]; ring,
          Real.log_mul hc0.ne' (Real.rpow_pos_of_pos (hKpos t) α).ne',
          Real.log_rpow (hKpos t), ih, pow_succ]
        linear_combination (-1 : ℝ) * hkb
    set e0 := Real.log (1 - α ^ 2 * β) + Real.log (Lb ^ (1 - α)) + Real.log A₀ + α * kb
    have hform : ∀ t : ℕ, β ^ t * Real.log (Cf t) = e0 * β ^ t +
        Real.log G * ((t : ℝ) ^ 1 * β ^ t) + α * (Real.log K₀ - kb) * (α * β) ^ t := by
      intro t
      have hKt := hKpos t
      simp only [hCf, hAdef]
      rw [Real.log_mul hab.ne' (by positivity), Real.log_mul (by positivity)
        (Real.rpow_pos_of_pos hKt α).ne', Real.log_mul hLa.ne' (by positivity),
        Real.log_mul hA₀.ne' (pow_ne_zero _ hGpos.ne'), Real.log_pow, Real.log_rpow hKt,
        hlogK t, mul_pow]
      ring
    have hab1 : α * β < 1 := by nlinarith
    have hn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ]; exact hβ1
    have h1 := (summable_geometric_of_lt_one hβ.le hβ1).mul_left e0
    have h2 := (summable_pow_mul_geometric_of_norm_lt_one 1 hn).mul_left (Real.log G)
    have h3 := (summable_geometric_of_lt_one (by positivity) hab1).mul_left
      (α * (Real.log K₀ - kb))
    exact ((h1.add h2).add h3).congr fun t => (hform t).symm
  -- the Euler equation in discounted form
  have hC1 : ∀ t, Cf (t + 1) = β * Rf (t + 1) * Cf t := by
    intro t
    have e := hAK t
    have hk1 := hKK (t + 1)
    simp only [hCf, hRf]
    rw [← hk1]
    linear_combination ((1 - α ^ 2 * β) * Lb ^ (1 - α) * K (t + 1) ^ (α - 1)) * e
  have heu : ∀ t, discR Rf t * Cf t = β ^ t * Cf 0 := by
    intro t
    induction t with
    | zero => simp [discR]
    | succ t ih =>
      have e : discR Rf (t + 1) * Cf (t + 1) = β * (discR Rf t * Cf t) := by
        rw [hC1 t]
        simp only [discR]
        field_simp [(hRpos t).ne']
      rw [e, ih, pow_succ]
      ring
  -- transversality: discounted wealth is a constant times βᵗ
  have hratio : ∀ t, A t * (α * Lb ^ (1 - α) * K t ^ (α - 1) * K t +
      (1 - α) * (Lb ^ (-α) * K t ^ α) / θ) = (α + (1 - α) / (θ * Lb)) / (1 - α ^ 2 * β) *
      Cf t := by
    intro t
    simp only [hCf]
    rw [mul_assoc (α * Lb ^ (1 - α)), hKK t, hLsplit]
    field_simp
  have htvc : Tendsto (fun T => discR Rf T * (A T * (α * Lb ^ (1 - α) * K T ^ (α - 1) * K T +
      (1 - α) * (Lb ^ (-α) * K T ^ α) / θ))) atTop (𝓝 0) := by
    have h0 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const
      ((α + (1 - α) / (θ * Lb)) / (1 - α ^ 2 * β) * Cf 0)
    rw [zero_mul] at h0
    refine h0.congr fun T => ?_
    rw [hratio T, mul_left_comm (discR Rf T), heu T]
    ring
  refine ⟨hrel, fun t => rfl, logHousehold_sufficient hβ hRpos (fun t => ?_) hCpos
    (fun t => hrel.market_budget hα hα1 t) hsum heu htvc⟩
  have h1 := Real.rpow_pos_of_pos (hKpos t) (α - 1)
  have h2 := Real.rpow_pos_of_pos (hKpos t) α
  have h1a : 0 < 1 - α := by linarith
  exact mul_nonneg (hApos t).le (add_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg hα.le hLa.le) h1.le) (hKpos t).le)
    (div_nonneg (mul_nonneg h1a.le (mul_nonneg hLn.le h2.le)) hθ.le))

/-- **Capital per blueprint in any log equilibrium** follows
`K_{t+1} = c K_t^α`, `c = α²β L̄_Y^{1-α}/(β(1+αθL̄_Y))`: the same law as `romerK`. -/
theorem romer_log_capital {α β θ L : ℝ} {A LY K R C pA a : ℕ → ℝ} (hα : 0 < α)
    (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ)
    (h : RomerEq α β θ L A LY K R C pA a) (t : ℕ) :
    K (t + 1) = α ^ 2 * β * romerLbar α β θ L ^ (1 - α) * K t ^ α /
      (β * (1 + α * θ * romerLbar α β θ L)) := by
  obtain ⟨hI, hL, hA⟩ := romer_log_equilibrium hα hα1 hβ hβ1 hθ h t
  have hAt := h.rel.posA t
  have hG : 0 < β * (1 + α * θ * romerLbar α β θ L) := by
    have := h.rel.posA (t + 1)
    rw [hA] at this
    exact pos_of_mul_pos_right this hAt.le
  rw [hA, hL] at hI
  unfold romerLbar at hG ⊢
  rw [eq_div_iff hG.ne']
  have := mul_left_cancel₀ hAt.ne' (show A t * (K (t + 1) *
    (β * (1 + α * θ * ((1 - β + θ * L) / (θ * (1 + α * β)))))) =
    A t * (α ^ 2 * β * ((1 - β + θ * L) / (θ * (1 + α * β))) ^ (1 - α) * K t ^ α) by
    linear_combination hI)
  exact this

/-- **Convergence, not a jump** (the corrected O&R p. 490): in every log equilibrium capital
per blueprint converges to `K̄ = c^{1/(1-α)}` (so the interest rate converges to its balanced
value), and the economy is on its balanced path from date 0 iff `K₀ = K̄`. -/
theorem romer_log_convergence {α β θ L : ℝ} {A LY K R C pA a : ℕ → ℝ} (hα : 0 < α)
    (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ)
    (h : RomerEq α β θ L A LY K R C pA a) :
    Tendsto K atTop (𝓝 ((α ^ 2 * β * romerLbar α β θ L ^ (1 - α) /
      (β * (1 + α * θ * romerLbar α β θ L))) ^ (1 / (1 - α)))) ∧
    ((∀ t, K t = K 0) ↔ K 0 = (α ^ 2 * β * romerLbar α β θ L ^ (1 - α) /
      (β * (1 + α * θ * romerLbar α β θ L))) ^ (1 / (1 - α))) := by
  set cc := α ^ 2 * β * romerLbar α β θ L ^ (1 - α) / (β * (1 + α * θ * romerLbar α β θ L))
    with hcc
  have hK := h.rel.posK
  have hstep : ∀ t, K (t + 1) = cc * K t ^ α := fun t => by
    rw [romer_log_capital hα hα1 hβ hβ1 hθ h t, hcc]
    ring
  have hc0 : 0 < cc := by
    have := hstep 0
    have := hK 1
    have := Real.rpow_pos_of_pos (hK 0) α
    by_contra hn
    push Not at hn
    nlinarith
  have h1a : (1 - α) ≠ 0 := by linarith
  set kb := Real.log cc / (1 - α)
  have hkb : kb * (1 - α) = Real.log cc := by simp only [kb]; field_simp
  have hlog : ∀ t, Real.log (K t) = kb + α ^ t * (Real.log (K 0) - kb) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hstep t, Real.log_mul hc0.ne' (Real.rpow_pos_of_pos (hK t) α).ne',
        Real.log_rpow (hK t), ih, pow_succ]
      linear_combination (-1 : ℝ) * hkb
  have hbar : cc ^ (1 / (1 - α)) = Real.exp kb := by
    rw [Real.rpow_def_of_pos hc0]
    congr 1
    simp only [kb]
    ring
  have hlim : Tendsto (fun t => Real.log (K t)) atTop (𝓝 kb) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hα.le hα1).mul_const
      (Real.log (K 0) - kb)).const_add kb
    rw [zero_mul, add_zero] at this
    exact this.congr fun t => (hlog t).symm
  refine ⟨?_, ⟨fun hconst => ?_, fun h0 t => ?_⟩⟩
  · rw [hbar]
    have := (Real.continuous_exp.tendsto kb).comp hlim
    refine this.congr fun t => ?_
    simp [Real.exp_log (hK t)]
  · have e := hstep 0
    rw [hconst 1] at e
    have hK0 := hK 0
    have h2 : K 0 ^ (1 - α) = cc := by
      have : K 0 = K 0 ^ α * K 0 ^ (1 - α) := by
        rw [← Real.rpow_add hK0, show α + (1 - α) = 1 by ring, Real.rpow_one]
      have hka := Real.rpow_pos_of_pos hK0 α
      have := mul_left_cancel₀ hka.ne' (show K 0 ^ α * K 0 ^ (1 - α) = K 0 ^ α * cc by
        rw [← this]; linear_combination e)
      exact this
    rw [← h2, ← Real.rpow_mul hK0.le, mul_one_div_cancel h1a, Real.rpow_one]
  · have hK0kb : Real.log (K 0) = kb := by
      rw [h0, hbar, Real.log_exp]
    have := hlog t
    rw [hK0kb, sub_self, mul_zero, add_zero, ← hK0kb] at this
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (hK t)) (Set.mem_Ioi.mpr (hK 0)) this

/-- **For `σ ≠ 1` even growth does not jump** (O&R p. 490 fails beyond log utility): along any
path satisfying the market relations and the isoelastic Euler equation
`C_{t+1} = (βR_{t+1})^σ C_t` with `σ ≠ 1`, if final-goods labour is constant from date 0 then
`K₁ = K₀`, i.e. capital per blueprint is already stationary. Hence when `K₀` differs from its
stationary value, `L_Y` and blueprint growth cannot be at constant (balanced) values from
date 0. The reason is that with `L_Y` constant the saving share is constant, so the Euler
equation forces output to grow at a constant rate, whereas capital per blueprint follows
`K_{t+1} = cK_t^α`. -/
theorem romer_sigma_ne_one_no_jump {α β σ θ L : ℝ} {A LY K R C pA : ℕ → ℝ} (hα : 0 < α)
    (hα1 : α < 1) (hβ : 0 < β) (hσ : σ ≠ 1) (h : RomerRel α θ L A LY K R C pA)
    (heuler : ∀ t, C (t + 1) = (β * R (t + 1)) ^ σ * C t) (hconst : ∀ t, LY t = LY 0) :
    K 1 = K 0 := by
  set Lb := LY 0
  have hLb : 0 < Lb := h.LYpos 0
  set g := θ * (L - Lb)
  have hA : ∀ t, A (t + 1) = A t * (1 + g) := fun t => by rw [h.research t, hconst t]
  have hg : 0 < 1 + g := by
    have := h.research 0
    have h1 := h.posA 1
    have h0 := h.posA 0
    rw [this] at h1
    exact pos_of_mul_pos_right h1 h0.le
  set d := 1 + α * θ * Lb
  have hd : 0 < d := by
    have := (h.scalar hα hα1 0).2.2
    rw [hconst 1] at this
    have hK1 := h.posK 1
    have hm : 0 < α ^ 2 * Lb * (LY 0 ^ (-α) * K 0 ^ α) := by
      have := Real.rpow_pos_of_pos hLb (-α)
      have := Real.rpow_pos_of_pos (h.posK 0) α
      positivity
    rw [this] at hm
    exact pos_of_mul_pos_right hm hK1.le
  -- capital law and output
  set m : ℕ → ℝ := fun t => Lb ^ (-α) * K t ^ α
  have hm : ∀ t, 0 < m t := fun t => by
    have := Real.rpow_pos_of_pos hLb (-α)
    have := Real.rpow_pos_of_pos (h.posK t) α
    simp only [m]
    positivity
  have hKlaw : ∀ t, K (t + 1) * d = α ^ 2 * Lb * m t := by
    intro t
    have := (h.scalar hα hα1 t).2.2
    rw [hconst (t + 1), hconst t] at this
    linarith
  set Y : ℕ → ℝ := fun t => A t * Lb * m t
  have hY : ∀ t, LY t ^ (1 - α) * A t * K t ^ α = Y t := fun t => by
    rw [(h.scalar hα hα1 t).1, hconst t]
  have hYpos : ∀ t, 0 < Y t := fun t => by
    have := h.posA t
    have := hm t
    simp only [Y]
    positivity
  set z := (1 + g) * α ^ 2 / d
  have hI : ∀ t, A (t + 1) * K (t + 1) = z * Y t := by
    intro t
    have := hKlaw t
    simp only [Y, z]
    rw [hA t, div_mul_eq_mul_div, eq_div_iff hd.ne']
    linear_combination A t * (1 + g) * this
  have hC : ∀ t, C t = (1 - z) * Y t := fun t => by rw [h.goods t, hY t, hI t]; ring
  have hCpos := h.posC
  have hz1 : 0 < 1 - z := by
    have := hCpos 0
    rw [hC 0] at this
    exact pos_of_mul_pos_left this (hYpos 0).le
  have hzpos : 0 < z := by simp only [z]; positivity
  have hRI : ∀ t, R (t + 1) = α ^ 2 * Y (t + 1) / (z * Y t) := by
    intro t
    have := (h.scalar hα hα1 t).2.1
    rw [hconst (t + 1)] at this
    have hK := h.posK (t + 1)
    rw [eq_div_iff (by have := hYpos t; positivity), ← hI t]
    simp only [Y]
    linear_combination A (t + 1) * this
  -- Euler forces constant output growth
  have hgrowth : ∀ t, Y (t + 1) ^ (1 - σ) = (β * α ^ 2 / z) ^ σ * Y t ^ (1 - σ) := by
    intro t
    have hE := heuler t
    rw [hC, hC, hRI t] at hE
    have hYt := hYpos t
    have hYt1 := hYpos (t + 1)
    have e1 : β * (α ^ 2 * Y (t + 1) / (z * Y t)) = (β * α ^ 2 / z) * (Y (t + 1) / Y t) := by
      field_simp
    rw [e1, Real.mul_rpow (by positivity) (by positivity),
      Real.div_rpow hYt1.le hYt.le] at hE
    have hE' : Y (t + 1) = (β * α ^ 2 / z) ^ σ * (Y (t + 1) ^ σ / Y t ^ σ) * Y t := by
      have := mul_left_cancel₀ hz1.ne' (show (1 - z) * Y (t + 1) = (1 - z) *
        ((β * α ^ 2 / z) ^ σ * (Y (t + 1) ^ σ / Y t ^ σ) * Y t) by linear_combination hE)
      exact this
    have hp1 := Real.rpow_pos_of_pos hYt1 σ
    have hp0 := Real.rpow_pos_of_pos hYt σ
    have a1 : Y (t + 1) ^ σ * Y (t + 1) ^ (1 - σ) = Y (t + 1) := by
      rw [← Real.rpow_add hYt1, show σ + (1 - σ) = 1 by ring, Real.rpow_one]
    have a0 : Y t ^ σ * Y t ^ (1 - σ) = Y t := by
      rw [← Real.rpow_add hYt, show σ + (1 - σ) = 1 by ring, Real.rpow_one]
    have e2 : Y (t + 1) * Y t ^ σ = (β * α ^ 2 / z) ^ σ * Y (t + 1) ^ σ * Y t := by
      have := congrArg (· * Y t ^ σ) hE'
      rw [this]
      field_simp
    apply mul_left_cancel₀ (mul_pos hp1 hp0).ne'
    linear_combination Y t ^ σ * a1 - (β * α ^ 2 / z) ^ σ * Y (t + 1) ^ σ * a0 + e2
  -- equal growth factors at dates 0 and 1
  have hratio : Y 1 / Y 0 = Y 2 / Y 1 := by
    have e0 := hgrowth 0
    have e1 := hgrowth 1
    have h1s : (1 - σ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
    have hq : (Y 1 / Y 0) ^ (1 - σ) = (Y 2 / Y 1) ^ (1 - σ) := by
      rw [Real.div_rpow (hYpos 1).le (hYpos 0).le, Real.div_rpow (hYpos 2).le (hYpos 1).le, e0, e1]
      have := Real.rpow_pos_of_pos (hYpos 0) (1 - σ)
      have := Real.rpow_pos_of_pos (hYpos 1) (1 - σ)
      field_simp
      linarith [e0]
    have := congrArg (fun x => x ^ (1 / (1 - σ))) hq
    rwa [← Real.rpow_mul (div_pos (hYpos 1) (hYpos 0)).le,
      ← Real.rpow_mul (div_pos (hYpos 2) (hYpos 1)).le, mul_one_div_cancel h1s,
      Real.rpow_one, Real.rpow_one] at this
  -- translate into capital
  have hK := h.posK
  have hYK : ∀ t, Y (t + 1) / Y t = (1 + g) * (K (t + 1) / K t) ^ α := by
    intro t
    simp only [Y, m]
    rw [hA t, Real.div_rpow (hK (t + 1)).le (hK t).le]
    have := h.posA t
    have := Real.rpow_pos_of_pos hLb (-α)
    have := Real.rpow_pos_of_pos (hK t) α
    field_simp
  rw [hYK 0, hYK 1] at hratio
  have hr : (K 1 / K 0) ^ α = (K 2 / K 1) ^ α := mul_left_cancel₀ hg.ne' hratio
  have hr' : K 1 / K 0 = K 2 / K 1 := by
    have h1 := div_pos (hK 1) (hK 0)
    have h2 := div_pos (hK 2) (hK 1)
    exact le_antisymm ((Real.rpow_le_rpow_iff h1.le h2.le hα).mp hr.le)
      ((Real.rpow_le_rpow_iff h2.le h1.le hα).mp hr.ge)
  -- capital law: K_{t+1} = c K_t^α with c = α² Lb^{1-α}/d, so K₁/K₀ = K₂/K₁ forces K₀ = K₁
  have hlaw : ∀ t, K (t + 1) / K t = α ^ 2 * Lb * Lb ^ (-α) / d * K t ^ (α - 1) := by
    intro t
    have := hKlaw t
    simp only [m] at this
    have e' : K t ^ (α - 1) * K t = K t ^ α := rpow_sub_one_mul (hK t)
    rw [div_eq_iff (hK t).ne']
    calc K (t + 1) = α ^ 2 * Lb * Lb ^ (-α) * K t ^ α / d := by
          rw [eq_div_iff hd.ne']
          linear_combination this
      _ = α ^ 2 * Lb * Lb ^ (-α) / d * K t ^ (α - 1) * K t := by
          rw [← e']
          ring
  rw [hlaw 0, hlaw 1] at hr'
  have hc : 0 < α ^ 2 * Lb * Lb ^ (-α) / d := by
    have := Real.rpow_pos_of_pos hLb (-α)
    positivity
  have hpow : K 0 ^ (α - 1) = K 1 ^ (α - 1) := mul_left_cancel₀ hc.ne' hr'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := Real.rpow_lt_rpow_of_neg (hK 1) hlt (by linarith : α - 1 < 0)
    linarith
  · have := Real.rpow_lt_rpow_of_neg (hK 0) hgt (by linarith : α - 1 < 0)
    linarith

/-- **The blueprint price is the present value of profits — no bubble** (O&R (89), derived
in every log equilibrium): `p_{A,t} = ∑_{s ≥ 0} (D_{t+s}/D_t) Π_{t+s}` with
`Π_u = ((1-α)/α)K_{u+1}` and `D` the market discount factors. The bubble term
`D_T p_{A,T}` vanishes because household optimality ties `D_T` to `βᵀ C₀/C_T`. -/
theorem romer_log_blueprint_pv {α β θ L : ℝ} {A LY K R C pA a : ℕ → ℝ} (hα : 0 < α)
    (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ)
    (h : RomerEq α β θ L A LY K R C pA a) (t : ℕ) :
    HasSum (fun s => discR R (t + s) / discR R t * ((1 - α) / α * K (t + s + 1))) (pA t) := by
  have hr := h.rel
  have hR : ∀ t, 0 < R (t + 1) := fun t => by
    rw [hr.pricing t]
    have := Real.rpow_pos_of_pos (hr.LYpos (t + 1)) (1 - α)
    have := Real.rpow_pos_of_pos (hr.posK (t + 1)) (α - 1)
    positivity
  have hD := discR_pos hR
  have h1a : 0 < 1 - α := by linarith
  have hm : ∀ t, 0 < LY t ^ (-α) * K t ^ α := fun t => by
    have := Real.rpow_pos_of_pos (hr.LYpos t) (-α)
    have := Real.rpow_pos_of_pos (hr.posK t) α
    positivity
  have hpA : ∀ t, 0 < pA t := fun t => by
    have := hr.arbitrage t
    have := hm t
    nlinarith
  -- wealth positive, hence the Euler equation, hence D_T C_T = βᵀ C₀
  have hapos : ∀ t, 0 < a t := fun t => by
    rw [h.wealth]
    have := hr.posA t
    have := Real.rpow_pos_of_pos (hr.LYpos t) (1 - α)
    have := Real.rpow_pos_of_pos (hr.posK t) (α - 1)
    have := hr.posK t
    have := hpA t
    positivity
  have heuler : ∀ t, C (t + 1) = β * R (t + 1) * C t :=
    fun t => h.household.euler hβ t (hR t) (hapos (t + 1))
  have hdisc : ∀ t, discR R t * C t = β ^ t * C 0 := by
    intro t
    induction t with
    | zero => simp [discR]
    | succ t ih =>
      simp only [discR]
      rw [heuler t, pow_succ]
      field_simp [(hR t).ne']
      linear_combination ih
  -- consumption and blueprint wealth in terms of output
  have heq := romer_log_equilibrium hα hα1 hβ hβ1 hθ h
  set Lb := (1 - β + θ * L) / (θ * (1 + α * β))
  have hLb : ∀ t, LY t = Lb := fun t => (heq t).2.1
  have hCY : ∀ t, C t = (1 - α ^ 2 * β) * (A t * Lb * (LY t ^ (-α) * K t ^ α)) := by
    intro t
    rw [hr.goods t, (heq t).1, (hr.scalar hα hα1 t).1, hLb t]
    ring
  have hLbpos : 0 < Lb := by rw [← hLb 0]; exact hr.LYpos 0
  have hab : 0 < 1 - α ^ 2 * β := by nlinarith
  have hAge : ∀ t, A 0 ≤ A t := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ t ih =>
      rw [hr.research t]
      have := hr.LYlt t
      have := hr.posA t
      nlinarith [mul_pos hθ (sub_pos.mpr (hr.LYlt t))]
  -- the bubble term vanishes
  have hbubble : Tendsto (fun T => discR R T * pA T) atTop (𝓝 0) := by
    have hform : ∀ T, discR R T * pA T =
        β ^ T * (C 0 * (1 - α) / (θ * (1 - α ^ 2 * β) * Lb * A T)) := by
      intro T
      have hDT : discR R T = β ^ T * C 0 / C T := by
        have := hr.posC T
        field_simp
        linarith [hdisc T]
      have hpAT : pA T = (1 - α) * (LY T ^ (-α) * K T ^ α) / θ := by
        rw [← hr.arbitrage T]
        field_simp
      rw [hDT, hpAT, hCY T]
      have := hr.posA T
      have := Real.rpow_pos_of_pos (hr.LYpos T) (-α)
      have := Real.rpow_pos_of_pos (hr.posK T) α
      field_simp
    have hb : ∀ T, 0 ≤ discR R T * pA T := fun T => (mul_pos (hD T) (hpA T)).le
    have hub : ∀ T, discR R T * pA T ≤
        β ^ T * (C 0 * (1 - α) / (θ * (1 - α ^ 2 * β) * Lb * A 0)) := by
      intro T
      rw [hform T]
      apply mul_le_mul_of_nonneg_left _ (pow_pos hβ T).le
      have := hr.posC 0
      have := hr.posA 0
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have := hAge T
      apply mul_le_mul_of_nonneg_left this (by positivity)
    have h0 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const
      (C 0 * (1 - α) / (θ * (1 - α ^ 2 * β) * Lb * A 0))
    rw [zero_mul] at h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 hb hub
  -- telescoping of the blueprint recursion
  have hstep : ∀ u, discR R u * pA u =
      discR R u * ((1 - α) / α * K (u + 1)) + discR R (u + 1) * pA (u + 1) := by
    intro u
    rw [hr.blueprint u]
    simp only [discR]
    field_simp [(hR u).ne']
  have hpart : ∀ n, ∑ s ∈ range n, discR R (t + s) * ((1 - α) / α * K (t + s + 1)) =
      discR R t * pA t - discR R (t + n) * pA (t + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih, hstep (t + n), show t + (n + 1) = t + n + 1 by ring]
      ring
  have hnn : ∀ s, 0 ≤ discR R (t + s) * ((1 - α) / α * K (t + s + 1)) := fun s =>
    mul_nonneg (hD _).le (mul_nonneg (div_nonneg h1a.le hα.le) (hr.posK _).le)
  have hlim : Tendsto (fun n => ∑ s ∈ range n, discR R (t + s) * ((1 - α) / α * K (t + s + 1)))
      atTop (𝓝 (discR R t * pA t)) := by
    have hb2 : Tendsto (fun n => discR R (t + n) * pA (t + n)) atTop (𝓝 0) :=
      (hbubble.comp (tendsto_add_atTop_nat t)).congr fun n => by
        simp only [Function.comp, add_comm]
    have := hb2.const_sub (discR R t * pA t)
    rw [sub_zero] at this
    exact this.congr fun n => (hpart n).symm
  have hS := (hasSum_iff_tendsto_nat_of_nonneg hnn _).mpr hlim
  have := hS.div_const (discR R t)
  rw [mul_div_cancel_left₀ _ (hD t).ne'] at this
  convert this using 1
  funext s
  ring

end ObstfeldRogoff.GlobalGrowth.RomerGrowth
