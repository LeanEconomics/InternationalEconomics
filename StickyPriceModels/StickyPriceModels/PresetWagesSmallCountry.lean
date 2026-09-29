/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceModels.NontradablesOvershooting
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Preset nominal wages in the small country (§10.4.1)

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.4.1,
pp. 706–709. A single nontraded good is produced competitively from differentiated labour
types with the CES technology (131), `Y_N = [∫ ℓ(z)^{(φ−1)/φ} dz]^{φ/(φ−1)}`, `φ > 1`; each worker
is a monopoly supplier of its labour type, with utility (132) and budget (133); the firm's
problem (134) gives the labour demands (135).

This file proves:

* The competitive firm (131), (134)–(135), on finitely many labour types with positive weights
  (the continuum `[0,1]` of the book is the equal-weight limit; the argument is identical):
  the wage index `W` is the minimum cost of a unit of labour, the labour demands (135) are the
  UNIQUE cost-minimising inputs, profits are `(P_N − W)Y_N` at best, so an equilibrium with
  positive output requires the zero-profit condition `P_N = W`; under symmetric wages
  `W = w`, (138), and `Y_N = ℓ`, (137).
* The worker's problem (132)–(133) with labour demand (135) IS the household problem of
  `NontradablesModel` with `θ` replaced by `φ` and aggregate demand `C^A_N` replaced by `Y_N`:
  labour income `wℓ = P_N ℓ^{(φ−1)/φ} Y_N^{1/φ}`. Hence (136) and (87)–(89) are necessary and
  sufficient for the worker's optimum (genuine infinite horizon), and (140) is the unique
  steady-state labour supply.
* Preset wages (§10.4.1.3): with `w_1 = w_0` preset, zero profits force `P_{N,1} = w_1 = P_{N,0}`
  although `P_N` is flexible, so the short-run system is IDENTICAL to §10.2: the impact response,
  (99), exact overshooting iff `ε > 1`, the equilibrium characterisation (with `φ` in the
  demand-determination bound `x² ≤ φ/(φ−1)`) and the strict welfare gain all transfer (p. 709).
-/

namespace ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry

open Real Filter Topology Finset
open ObstfeldRogoff.StickyPriceModels.NontradablesModel
open ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting

/-! ## The competitive firm (131), (134)–(135) -/

/-- Strict tangent inequality for `y ↦ y^s`, `0 < s < 1`, `b ≠ a` (strict concavity of the CES
aggregator (131), O&R p. 706–707): `b^s < a^s + s a^{s−1}(b − a)`. -/
theorem rpow_lt_tangent {s a b : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 < a) (hb : 0 < b)
    (hne : b ≠ a) : b ^ s < a ^ s + s * (a ^ (s - 1) * (b - a)) := by
  have hq : 0 < b / a := div_pos hb ha
  have hq1 : b / a - 1 ≠ 0 := by
    intro h; apply hne; field_simp at h; linarith
  have h1 : (1 + (b / a - 1)) ^ s < 1 + s * (b / a - 1) :=
    rpow_one_add_lt_one_add_mul_self (by linarith) hq1 hs0 hs1
  rw [show 1 + (b / a - 1) = b / a by ring] at h1
  have has : 0 < a ^ s := rpow_pos_of_pos ha s
  have key : b ^ s = a ^ s * (b / a) ^ s := by rw [div_rpow hb.le ha.le]; field_simp
  have hsplit : a ^ (s - 1) * (b - a) = a ^ s * (b / a - 1) := by
    rw [rpow_sub_one ha.ne']; field_simp
  rw [key, hsplit]
  nlinarith [mul_lt_mul_of_pos_left h1 has]

variable {ι : Type*} [Fintype ι]

/-- The CES labour aggregate (131), p. 706, on finitely many labour types with weights `ω`:
`Y_N = [Σ ω_i ℓ_i^{(φ−1)/φ}]^{φ/(φ−1)}`. -/
noncomputable def laborAggregate (ω : ι → ℝ) (φ : ℝ) (ℓ : ι → ℝ) : ℝ :=
  (∑ i, ω i * ℓ i ^ ((φ - 1) / φ)) ^ (φ / (φ - 1))

/-- The wage index `W = [Σ ω_i w_i^{1−φ}]^{1/(1−φ)}` (dual of (131); O&R p. 707). -/
noncomputable def wageIndex (ω : ι → ℝ) (φ : ℝ) (w : ι → ℝ) : ℝ :=
  (∑ i, ω i * w i ^ (1 - φ)) ^ (1 / (1 - φ))

/-- The labour demands (135), p. 707: `ℓ_i = (w_i/W)^{−φ} Y_N`. -/
noncomputable def laborDemand (ω : ι → ℝ) (φ : ℝ) (w : ι → ℝ) (Y : ℝ) (i : ι) : ℝ :=
  (w i / wageIndex ω φ w) ^ (-φ) * Y

/-- The wage index is positive (O&R p. 707). -/
theorem wageIndex_pos [Nonempty ι] {ω w : ι → ℝ} {φ : ℝ} (hω : ∀ i, 0 < ω i)
    (hw : ∀ i, 0 < w i) : 0 < wageIndex ω φ w := by
  unfold wageIndex
  apply rpow_pos_of_pos
  exact Finset.sum_pos (fun i _ => mul_pos (hω i) (rpow_pos_of_pos (hw i) _)) univ_nonempty

/-- `W^{1−φ} = Σ ω_i w_i^{1−φ}` (O&R p. 707). -/
theorem wageIndex_rpow [Nonempty ι] {ω w : ι → ℝ} {φ : ℝ} (hφ : 1 < φ) (hω : ∀ i, 0 < ω i)
    (hw : ∀ i, 0 < w i) : wageIndex ω φ w ^ (1 - φ) = ∑ i, ω i * w i ^ (1 - φ) := by
  unfold wageIndex
  have hS : 0 < ∑ i, ω i * w i ^ (1 - φ) :=
    Finset.sum_pos (fun i _ => mul_pos (hω i) (rpow_pos_of_pos (hw i) _)) univ_nonempty
  rw [← rpow_mul hS.le, show 1 / (1 - φ) * (1 - φ) = 1 by
    have : (1 : ℝ) - φ ≠ 0 := by linarith
    field_simp, rpow_one]

/-- The labour demands (135) cost exactly `W Y_N` (O&R (134)–(135)). -/
theorem laborDemand_cost [Nonempty ι] {ω w : ι → ℝ} {φ Y : ℝ} (hφ : 1 < φ)
    (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) :
    ∑ i, ω i * (w i * laborDemand ω φ w Y i) = wageIndex ω φ w * Y := by
  have hW := wageIndex_pos (φ := φ) hω hw
  have hWr := wageIndex_rpow hφ hω hw
  have e : ∀ i, ω i * (w i * laborDemand ω φ w Y i)
      = (ω i * w i ^ (1 - φ)) * (wageIndex ω φ w ^ φ * Y) := by
    intro i
    unfold laborDemand
    rw [div_rpow (hw i).le hW.le, rpow_neg (hw i).le, rpow_neg hW.le, rpow_sub (hw i),
      rpow_one]
    have : 0 < w i ^ φ := rpow_pos_of_pos (hw i) φ
    field_simp
  simp_rw [e]
  rw [← Finset.sum_mul, ← hWr, ← mul_assoc, ← rpow_add hW, show 1 - φ + φ = 1 by ring,
    rpow_one]

/-- The labour demands (135) produce exactly `Y_N` (O&R (131), (135)). -/
theorem laborDemand_output [Nonempty ι] {ω w : ι → ℝ} {φ Y : ℝ} (hφ : 1 < φ)
    (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) (hY : 0 < Y) :
    laborAggregate ω φ (laborDemand ω φ w Y) = Y := by
  have hW := wageIndex_pos (φ := φ) hω hw
  have hWr := wageIndex_rpow hφ hω hw
  have hφ0 : 0 < φ := by linarith
  have e : ∀ i, ω i * laborDemand ω φ w Y i ^ ((φ - 1) / φ)
      = (ω i * w i ^ (1 - φ)) * (Y ^ ((φ - 1) / φ) / wageIndex ω φ w ^ (1 - φ)) := by
    intro i
    unfold laborDemand
    rw [mul_rpow (rpow_pos_of_pos (div_pos (hw i) hW) _).le hY.le, ← rpow_mul (div_pos (hw i)
      hW).le, show -φ * ((φ - 1) / φ) = 1 - φ by field_simp; ring, div_rpow (hw i).le hW.le]
    have : 0 < wageIndex ω φ w ^ (1 - φ) := rpow_pos_of_pos hW _
    field_simp
  unfold laborAggregate
  simp_rw [e]
  rw [← Finset.sum_mul, ← hWr]
  have : 0 < wageIndex ω φ w ^ (1 - φ) := rpow_pos_of_pos hW _
  rw [mul_div_cancel₀ _ this.ne', ← rpow_mul hY.le,
    show (φ - 1) / φ * (φ / (φ - 1)) = 1 by
      have : φ - 1 ≠ 0 := by linarith
      field_simp, rpow_one]

/-- COST MINIMISATION (O&R (134)–(135), p. 707): any positive input vector producing at least
`Y_N` costs at least `W Y_N`, with equality ONLY at the labour demands (135) (existence and
uniqueness of the cost-minimising inputs; strict concavity of (131)). -/
theorem labor_cost_ge [Nonempty ι] {ω w ℓ : ι → ℝ} {φ Y : ℝ} (hφ : 1 < φ)
    (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) (hℓ : ∀ i, 0 < ℓ i) (hY : 0 < Y)
    (hout : Y ≤ laborAggregate ω φ ℓ) :
    wageIndex ω φ w * Y ≤ ∑ i, ω i * (w i * ℓ i) ∧
      (∑ i, ω i * (w i * ℓ i) = wageIndex ω φ w * Y → ℓ = laborDemand ω φ w Y) := by
  have hW := wageIndex_pos (φ := φ) hω hw
  have hWr := wageIndex_rpow hφ hω hw
  have hφ0 : 0 < φ := by linarith
  set s := (φ - 1) / φ with hs
  have hs0 : 0 < s := div_pos (by linarith) hφ0
  have hs1 : s < 1 := by rw [hs, div_lt_one hφ0]; linarith
  set ℓ0 := laborDemand ω φ w Y
  have hℓ0 : ∀ i, 0 < ℓ0 i := fun i =>
    mul_pos (rpow_pos_of_pos (div_pos (hw i) hW) _) hY
  -- the two powers of the demands
  have hpow1 : ∀ i, ℓ0 i ^ s = (w i / wageIndex ω φ w) ^ (1 - φ) * Y ^ s := by
    intro i
    simp only [ℓ0, laborDemand]
    rw [mul_rpow (rpow_pos_of_pos (div_pos (hw i) hW) _).le hY.le,
      ← rpow_mul (div_pos (hw i) hW).le, show -φ * s = 1 - φ by rw [hs]; field_simp; ring]
  have hpow2 : ∀ i, ℓ0 i ^ (s - 1) = (w i / wageIndex ω φ w) * Y ^ (s - 1) := by
    intro i
    simp only [ℓ0, laborDemand]
    rw [mul_rpow (rpow_pos_of_pos (div_pos (hw i) hW) _).le hY.le,
      ← rpow_mul (div_pos (hw i) hW).le, show -φ * (s - 1) = 1 by rw [hs]; field_simp; ring,
      rpow_one]
  have hsum0 : ∑ i, ω i * ℓ0 i ^ s = Y ^ s := by
    simp_rw [hpow1]
    have e : ∀ i, ω i * ((w i / wageIndex ω φ w) ^ (1 - φ) * Y ^ s)
        = (ω i * w i ^ (1 - φ)) * (Y ^ s / wageIndex ω φ w ^ (1 - φ)) := by
      intro i; rw [div_rpow (hw i).le hW.le]; ring
    simp_rw [e]
    rw [← Finset.sum_mul, ← hWr, mul_div_cancel₀ _ (rpow_pos_of_pos hW _).ne']
  have hcost0 := laborDemand_cost (Y := Y) hφ hω hw
  -- output requirement in power form
  have hS : 0 < ∑ i, ω i * ℓ i ^ s :=
    Finset.sum_pos (fun i _ => mul_pos (hω i) (rpow_pos_of_pos (hℓ i) _)) univ_nonempty
  have hreq : Y ^ s ≤ ∑ i, ω i * ℓ i ^ s := by
    have h1 := rpow_le_rpow hY.le hout hs0.le
    unfold laborAggregate at h1
    rw [← rpow_mul hS.le, show φ / (φ - 1) * s = 1 by
      rw [hs]; have : φ - 1 ≠ 0 := by linarith
      field_simp, rpow_one] at h1
    exact h1
  -- the tangent bound
  have htan : ∀ i, ω i * ℓ i ^ s ≤ ω i * ℓ0 i ^ s
      + s * Y ^ (s - 1) / wageIndex ω φ w * (ω i * (w i * ℓ i) - ω i * (w i * ℓ0 i)) := by
    intro i
    have h := rpow_le_tangent hs0 hs1.le (hℓ0 i) (hℓ i)
    rw [hpow2 i] at h
    have := mul_le_mul_of_nonneg_left h (hω i).le
    have e : ω i * ((w i / wageIndex ω φ w * Y ^ (s - 1)) * (ℓ i - ℓ0 i)) * s
        = s * Y ^ (s - 1) / wageIndex ω φ w * (ω i * (w i * ℓ i) - ω i * (w i * ℓ0 i)) := by
      field_simp
    nlinarith
  have hsumtan : ∑ i, ω i * ℓ i ^ s ≤ Y ^ s + s * Y ^ (s - 1) / wageIndex ω φ w
      * (∑ i, ω i * (w i * ℓ i) - wageIndex ω φ w * Y) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ univ) => htan i)
    rw [Finset.sum_add_distrib, hsum0, ← Finset.mul_sum, Finset.sum_sub_distrib, hcost0]
      at this
    exact this
  have hk : 0 < s * Y ^ (s - 1) / wageIndex ω φ w := by
    have := rpow_pos_of_pos hY (s - 1); positivity
  refine ⟨?_, fun heq => ?_⟩
  · by_contra hlt
    push Not at hlt
    have : s * Y ^ (s - 1) / wageIndex ω φ w
        * (∑ i, ω i * (w i * ℓ i) - wageIndex ω φ w * Y) < 0 :=
      mul_neg_of_pos_of_neg hk (by linarith)
    linarith
  · funext i
    by_contra hne
    have hstrict : ∑ i, ω i * ℓ i ^ s < ∑ i, (ω i * ℓ0 i ^ s
        + s * Y ^ (s - 1) / wageIndex ω φ w * (ω i * (w i * ℓ i) - ω i * (w i * ℓ0 i))) := by
      apply Finset.sum_lt_sum (fun j _ => htan j)
      refine ⟨i, mem_univ i, ?_⟩
      have h := rpow_lt_tangent hs0 hs1 (hℓ0 i) (hℓ i) hne
      rw [hpow2 i] at h
      have := mul_lt_mul_of_pos_left h (hω i)
      have e : ω i * ((w i / wageIndex ω φ w * Y ^ (s - 1)) * (ℓ i - ℓ0 i)) * s
          = s * Y ^ (s - 1) / wageIndex ω φ w * (ω i * (w i * ℓ i) - ω i * (w i * ℓ0 i)) := by
        field_simp
      nlinarith
    rw [Finset.sum_add_distrib, hsum0, ← Finset.mul_sum, Finset.sum_sub_distrib, hcost0, heq,
      sub_self, mul_zero, add_zero] at hstrict
    linarith

/-- THE FIRM'S PROFIT (O&R (134), p. 707): for any positive inputs, profit is at most
`(P_N − W) Y_N`, so with constant returns the competitive firm can have a positive-output
optimum only if `P_N = W` (zero profit); then every output level is optimal, with profit zero,
exactly at the labour demands (135). -/
theorem firm_profit_le [Nonempty ι] {ω w ℓ : ι → ℝ} {φ PN : ℝ} (hφ : 1 < φ)
    (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) (hℓ : ∀ i, 0 < ℓ i) :
    PN * laborAggregate ω φ ℓ - ∑ i, ω i * (w i * ℓ i)
      ≤ (PN - wageIndex ω φ w) * laborAggregate ω φ ℓ := by
  have hφ0 : 0 < φ := by linarith
  have hS : 0 < ∑ i, ω i * ℓ i ^ ((φ - 1) / φ) :=
    Finset.sum_pos (fun i _ => mul_pos (hω i) (rpow_pos_of_pos (hℓ i) _)) univ_nonempty
  have hY : 0 < laborAggregate ω φ ℓ := rpow_pos_of_pos hS _
  have := (labor_cost_ge hφ hω hw hℓ hY le_rfl).1
  nlinarith

/-- Zero profit is attained by (135) when `P_N = W` (O&R (134)–(135)). -/
theorem firm_zero_profit [Nonempty ι] {ω w : ι → ℝ} {φ Y : ℝ} (hφ : 1 < φ)
    (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) (hY : 0 < Y) :
    wageIndex ω φ w * laborAggregate ω φ (laborDemand ω φ w Y)
      - ∑ i, ω i * (w i * laborDemand ω φ w Y i) = 0 := by
  rw [laborDemand_output hφ hω hw hY, laborDemand_cost hφ hω hw]; ring

/-- If `P_N > W` profits are unbounded (no competitive equilibrium), and if `P_N < W` every
positive plan loses money: an equilibrium with positive output forces `P_N = W`
(O&R p. 708). -/
theorem firm_price_eq_wageIndex [Nonempty ι] {ω w : ι → ℝ} {φ PN : ℝ} (hφ : 1 < φ)
    (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) :
    (wageIndex ω φ w < PN → ∀ B : ℝ, ∃ Y > 0,
      B < PN * laborAggregate ω φ (laborDemand ω φ w Y)
        - ∑ i, ω i * (w i * laborDemand ω φ w Y i)) ∧
    (PN < wageIndex ω φ w → ∀ ℓ : ι → ℝ, (∀ i, 0 < ℓ i) →
      PN * laborAggregate ω φ ℓ - ∑ i, ω i * (w i * ℓ i) < 0) := by
  refine ⟨fun hgt B => ?_, fun hlt ℓ hℓ => ?_⟩
  · set d := PN - wageIndex ω φ w
    have hd : 0 < d := by simp only [d]; linarith
    refine ⟨(|B| + 1) / d, by positivity, ?_⟩
    rw [laborDemand_output hφ hω hw (by positivity), laborDemand_cost hφ hω hw]
    have e : PN * ((|B| + 1) / d) - wageIndex ω φ w * ((|B| + 1) / d) = |B| + 1 := by
      rw [← sub_mul]; exact mul_div_cancel₀ _ hd.ne'
    rw [e]; linarith [le_abs_self B]
  · have hφ0 : 0 < φ := by linarith
    have hS : 0 < ∑ i, ω i * ℓ i ^ ((φ - 1) / φ) :=
      Finset.sum_pos (fun i _ => mul_pos (hω i) (rpow_pos_of_pos (hℓ i) _)) univ_nonempty
    have hY : 0 < laborAggregate ω φ ℓ := rpow_pos_of_pos hS _
    have := firm_profit_le (PN := PN) hφ hω hw hℓ
    nlinarith

/-- SYMMETRY (137)–(138), p. 708: with a common wage `w` and weights summing to one, the wage
index is `W = w` (so zero profit gives `w = P_N`, (138)), each type's demand is `Y_N`, and
the aggregate of equal inputs `ℓ` is `ℓ`, so `Y_N = ℓ`, (137). -/
theorem symmetric_wages [Nonempty ι] {ω : ι → ℝ} {φ w Y : ℝ} (hφ : 1 < φ)
    (hω1 : ∑ i, ω i = 1) (hw : 0 < w) (hY : 0 < Y) :
    wageIndex ω φ (fun _ => w) = w ∧ (∀ i, laborDemand ω φ (fun _ => w) Y i = Y) ∧
      laborAggregate ω φ (fun _ => Y) = Y := by
  have hW : wageIndex ω φ (fun _ => w) = w := by
    unfold wageIndex
    rw [← Finset.sum_mul, hω1, one_mul, ← rpow_mul hw.le, show (1 - φ) * (1 / (1 - φ)) = 1 by
      have : (1 : ℝ) - φ ≠ 0 := by linarith
      field_simp, rpow_one]
  refine ⟨hW, fun i => by simp [laborDemand, hW, div_self hw.ne'], ?_⟩
  unfold laborAggregate
  rw [← Finset.sum_mul, hω1, one_mul, ← rpow_mul hY.le, show (φ - 1) / φ * (φ / (φ - 1)) = 1 by
    have : φ - 1 ≠ 0 := by linarith
    have : φ ≠ 0 := by linarith
    field_simp, rpow_one]


/-! ## The worker's problem (132)–(136) and the steady state (140) -/

/-- The §10.4.1 economy: the §10.2 economy with the labour-demand elasticity `φ` in the place of
the goods-demand elasticity `θ` (O&R (132)–(135), pp. 707–708). -/
def wageEconomy (E : Economy) (φ : ℝ) : Economy := ⟨E.β, E.r, E.γ, E.χ, E.ε, E.κ, φ, E.yT⟩

/-- The §10.4.1 parameter restrictions: those of §10.2 and `φ > 1` (O&R p. 707). -/
theorem wageEconomy_valid {E : Economy} (hE : E.Valid) {φ : ℝ} (hφ : 1 < φ) :
    (wageEconomy E φ).Valid := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _, h10⟩ := hE
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, hφ, h10⟩

/-- Labour demand (135) and labour income (133), p. 707: at the wage
`w = P_N (ℓ/Y_N)^{−1/φ}`, the demand `(w/P_N)^{−φ} Y_N` for type-`j` labour is exactly `ℓ`, and
real labour income is `wℓ/P_T = (P_N/P_T) ℓ^{(φ−1)/φ} Y_N^{1/φ}` — the §10.2 revenue with
`(θ, C^A_N)` replaced by `(φ, Y_N)`. (`Q.CA` is read as the path of `Y_N`.) -/
theorem laborIncome {E : Economy} {φ : ℝ} (hφ : 1 < φ) (Q : Prices) (t : ℕ) {ℓ : ℝ}
    (hT : 0 < Q.PT t) (hN : 0 < Q.PN t) (hY : 0 < Q.CA t) (hℓ : 0 < ℓ) :
    cesDemand φ (invDemand (wageEconomy E φ) Q t ℓ) (Q.PN t) (Q.CA t) = ℓ ∧
      invDemand (wageEconomy E φ) Q t ℓ * ℓ / Q.PT t = realRevenue (wageEconomy E φ) Q t ℓ :=
  ⟨cesDemand_invDemand (wageEconomy E φ) Q t (by simp [wageEconomy]; linarith) hN hY hℓ,
    invDemand_mul (wageEconomy E φ) Q t (by simp [wageEconomy]; linarith) hT hY hℓ⟩

/-- THE WORKER'S OPTIMUM (O&R (132)–(136)): a plan (tradables, nontradables, money, labour) is
optimal for the monopolistic worker IF AND ONLY IF (87), (89), the money condition (88), the
labour condition behind (136), no-Ponzi and the transversality condition hold (genuine infinite
horizon; specialisation of `NontradablesModel.householdOptimal_iff`). -/
theorem worker_optimal_iff {E : Economy} (hE : E.Valid) {φ : ℝ} (hφ : 1 < φ) {Q : Prices}
    (hQ : Q.Valid E.r) {B0 Mm1 : ℝ} {c : ℕ → Choice} :
    HouseholdOptimal (wageEconomy E φ) Q B0 Mm1 c ↔
      (∀ t, c t ∈ posChoice) ∧
      Summable (fun t => E.β ^ t * periodU (wageEconomy E φ) Q t (c t)) ∧
      EulerFOC (wageEconomy E φ) c ∧ IntraFOC (wageEconomy E φ) Q c ∧
      MoneyFOC (wageEconomy E φ) Q c ∧ LabourFOC (wageEconomy E φ) Q c ∧
      NoPonzi E.r (wealth E.r (initWealth (wageEconomy E φ) Q B0 Mm1)
        (netRes (wageEconomy E φ) Q) c) ∧
      LiminfNonpos E.r (wealth E.r (initWealth (wageEconomy E φ) Q B0 Mm1)
        (netRes (wageEconomy E φ) Q) c) :=
  householdOptimal_iff (wageEconomy_valid hE hφ) hQ

/-- (136), p. 708: at the worker's optimum,
`ℓ^{(φ+1)/φ} = [(φ−1)(1−γ)/(κφ)] Y_N^{1/φ} (1/C_N)` at every date. -/
theorem worker_136 {E : Economy} (hE : E.Valid) {φ : ℝ} (hφ : 1 < φ) {Q : Prices}
    {B0 Mm1 : ℝ} {c : ℕ → Choice}
    (hopt : HouseholdOptimal (wageEconomy E φ) Q B0 Mm1 c) (t : ℕ) :
    (c t).y ^ ((φ + 1) / φ) = (φ - 1) * (1 - E.γ) / (E.κ * φ) * Q.CA t ^ (1 / φ) / (c t).cN := by
  have hE' := wageEconomy_valid hE hφ
  exact labour_90 hE' hopt.1 (intraFOC_of_optimal hE' hopt) (labourFOC_of_optimal hE' hopt) t

/-- (140), p. 708: in any symmetric equilibrium (`ℓ = Y_N`, (137); `Y_N = C_N`, (139)) labour
supply equals `ℓ̄ = [(φ−1)(1−γ)/(κφ)]^{1/2} = ȳ_N` at every date (unique). -/
theorem laborSupply_140 {E : Economy} (hE : E.Valid) {φ : ℝ} (hφ : 1 < φ) {Q : Prices}
    {B0 Mm1 : ℝ} {M : ℕ → ℝ} {c : ℕ → Choice}
    (heq : IsEquilibrium (wageEconomy E φ) Q B0 Mm1 M c) (t : ℕ) :
    (c t).y = sqrt ((φ - 1) * (1 - E.γ) / (E.κ * φ)) ∧
      (c t).cN = sqrt ((φ - 1) * (1 - E.γ) / (E.κ * φ)) :=
  output_93 (wageEconomy_valid hE hφ) heq t

/-- EXISTENCE of the flexible-wage steady state (O&R p. 708, "steady-state prices ... are
determined as before"): for every `M̄ > 0` the §10.2 steady-state construction with `φ` in place
of `θ` is an equilibrium of the wage economy (specialisation of
`NontradablesModel.steadyState_isEquilibrium`). -/
theorem wage_steadyState_isEquilibrium {E : Economy} (hE : E.Valid)
    (hβr : E.β * (1 + E.r) = 1) {φ : ℝ} (hφ : 1 < φ) {Mbar : ℝ} (hM0 : 0 < Mbar) :
    (steadyPrices (wageEconomy E φ) Mbar).Valid E.r ∧
      IsEquilibrium (wageEconomy E φ) (steadyPrices (wageEconomy E φ) Mbar) 0 Mbar
        (fun _ => Mbar) (steadyChoice (wageEconomy E φ) Mbar) :=
  steadyState_isEquilibrium (wageEconomy_valid hE hφ) hβr hM0

/-! ## Preset wages (§10.4.1.3) -/

/-- Zero profits with PRESET wages (O&R p. 709): with symmetric wages the wage index equals the
wage, so the competitive firm's zero-profit condition `P_N = W` gives `P_{N,1} = w_1`; with
`w_1 = w_0` preset, `P_{N,1} = P_{N,0}` even though `P_N` is flexible. -/
theorem presetWage_price [Nonempty ι] {ω : ι → ℝ} {φ w0 w1 PN0 PN1 : ℝ} (hφ : 1 < φ)
    (hω1 : ∑ i, ω i = 1) (hw0 : 0 < w0) (hpre : w1 = w0)
    (hzp0 : PN0 = wageIndex ω φ (fun _ => w0)) (hzp1 : PN1 = wageIndex ω φ (fun _ => w1)) :
    PN1 = w1 ∧ PN1 = PN0 := by
  have h0 := (symmetric_wages (Y := 1) hφ hω1 hw0 one_pos).1
  have h1 := (symmetric_wages (Y := 1) hφ hω1 (hpre ▸ hw0) one_pos).1
  exact ⟨hzp1.trans h1, by rw [hzp1, h1, hzp0, h0, hpre]⟩

/-- THE PRESET-WAGE SHORT RUN IS IDENTICAL TO §10.2 (O&R p. 709): the preset-wage shock path
(`P_N` at its preset level `w_0`, labour demand-determined, rationing allowed) is an equilibrium
IF AND ONLY IF `x` solves the SAME impact equation as in §10.2 and `x² ≤ φ/(φ−1)` (the marginal
utility of the preset real wage is at least the marginal disutility of work). -/
theorem presetWage_equilibrium_iff {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {φ M0 μ x : ℝ} (hφ : 1 < φ) (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x) :
    ((shockPrices (wageEconomy E φ) M0 μ x).Valid E.r ∧
      IsStickyEquilibrium (wageEconomy E φ) (shockPrices (wageEconomy E φ) M0 μ x) 0 M0
        (fun _ => μ * M0) (shockChoice (wageEconomy E φ) M0 μ x)) ↔
      impactGap E.β E.γ E.ε μ x = 0 ∧ x ^ 2 ≤ φ / (φ - 1) :=
  shock_equilibrium_iff (wageEconomy_valid hE hφ) hβr hM0 hμ hx

/-- THE IDENTICAL IMPACT RESPONSE (O&R p. 709, "one arrives at the IDENTICAL expression (99)"):
the impact response of the preset-wage economy coincides with that of the preset-price economy
with the same `β, γ, ε`, whatever `θ` and `φ`. -/
theorem presetWage_same_impact {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {φ M0 μ x x' : ℝ} (hφ : 1 < φ) (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x) (hx' : 0 < x')
    (hprice : (shockPrices E M0 μ x).Valid E.r ∧
      IsStickyEquilibrium E (shockPrices E M0 μ x) 0 M0 (fun _ => μ * M0)
        (shockChoice E M0 μ x))
    (hwage : (shockPrices (wageEconomy E φ) M0 μ x').Valid E.r ∧
      IsStickyEquilibrium (wageEconomy E φ) (shockPrices (wageEconomy E φ) M0 μ x') 0 M0
        (fun _ => μ * M0) (shockChoice (wageEconomy E φ) M0 μ x')) :
    x' = x := by
  obtain ⟨hF, _⟩ := (shock_equilibrium_iff hE hβr hM0 hμ hx).mp hprice
  obtain ⟨hF', _⟩ := (presetWage_equilibrium_iff hE hβr hφ hM0 hμ hx').mp hwage
  obtain ⟨hβ, hβ1, _, hγ0, hγ1, _, hε, _, _, _⟩ := hE
  obtain ⟨z, _, _, _, huniq⟩ := impact_exists_unique hβ hβ1 hγ0 hγ1 hε hμ
  rw [huniq x' hx' hF', huniq x hx hF]

/-- (99) and exact overshooting with preset wages (O&R p. 709): on any preset-wage equilibrium
path after `μ > 1`, the exchange rate overshoots iff `ε > 1`. -/
theorem presetWage_overshoots_iff {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {φ M0 μ x PTstar : ℝ} (hφ : 1 < φ) (hM0 : 0 < M0) (hμ : 1 < μ) (hx : 0 < x)
    (hs : 0 < PTstar) (hQ : (shockPrices (wageEconomy E φ) M0 μ x).Valid E.r)
    (heq : IsStickyEquilibrium (wageEconomy E φ) (shockPrices (wageEconomy E φ) M0 μ x) 0 M0
      (fun _ => μ * M0) (shockChoice (wageEconomy E φ) M0 μ x)) :
    exchangeRate PTstar ((shockPrices (wageEconomy E φ) M0 μ x).PT 1)
        < exchangeRate PTstar ((shockPrices (wageEconomy E φ) M0 μ x).PT 0) ↔ 1 < E.ε :=
  exchangeRate_overshoots_iff (wageEconomy_valid hE hφ) hβr hM0 hμ hx hs hQ heq

/-- The essential welfare implication with preset wages (O&R p. 709, "the shock once again
coordinates an efficient increase in labor supply"): on the preset-wage path after `μ > 1` with
`x² ≤ φ/(φ−1)`, lifetime utility strictly rises; the real gain is
`(1−γ)[log x − ((φ−1)/(2φ))(x² − 1)] > 0`. -/
theorem presetWage_welfare_gain_pos {E : Economy} (hE : E.Valid) {φ M0 μ x : ℝ} (hφ : 1 < φ)
    (hM0 : 0 < M0) (hμ : 1 < μ) (hx : 0 < x) (hF : impactGap E.β E.γ E.ε μ x = 0)
    (hdd : x ^ 2 ≤ φ / (φ - 1)) :
    0 < realGain φ E.γ x ∧
      ∑' t, E.β ^ t * periodU (wageEconomy E φ) (steadyPrices (wageEconomy E φ) M0) t
          (steadyChoice (wageEconomy E φ) M0 t)
        < ∑' t, E.β ^ t * periodU (wageEconomy E φ) (shockPrices (wageEconomy E φ) M0 μ x) t
          (shockChoice (wageEconomy E φ) M0 μ x t) := by
  have hE' := wageEconomy_valid hE hφ
  obtain ⟨hβ, hβ1, _, hγ0, hγ1, _, hε, _, _, _⟩ := hE
  exact ⟨realGain_pos hφ hγ1 (one_lt_root hβ hβ1 hγ0 hγ1 hε hμ hx hF) hdd,
    welfare_gain_pos hE' hM0 hμ hx hF hdd⟩

end ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry
