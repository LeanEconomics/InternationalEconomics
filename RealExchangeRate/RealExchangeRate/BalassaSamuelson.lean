/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RealExchangeRate.CRSProduction
import RealExchangeRate.Model
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The price of nontraded goods and the Harrod–Balassa–Samuelson effect

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.2.1–4.2.3,
pp. 204–212, eqs. (2)–(9).

A small open economy produces tradables `Y_T = A_T F(K_T, L_T)` and nontradables
`Y_N = A_N G(K_N, L_N)` with constant returns, faces the world interest rate `r`, and has
labour mobile between sectors. Tradables are the numeraire and `p` is the relative price of
nontradables. The supply-side equilibrium is a solution `(k_T, w, k_N, p)` of (2)–(5).

Results:
* T1 (p. 206): for `r, A_T, A_N > 0` the equilibrium exists and is unique, so `p` depends only
  on `r`, the productivities and technology — never on demand;
* T2 (p. 208): a rise in `A_T` raises `p` and `k_N`; a rise in `A_N` leaves `k_N` and `pA_N`
  unchanged;
* Shephard's lemma for the nontraded unit cost `pA_N = c(r, w)` along any path (exact
  envelope theorem);
* T3 (pp. 208–209): the log-linearisations (8), (9) and the interest-rate formula, as EXACT
  derivatives of logs along arbitrary differentiable paths `(r(t), A_T(t), A_N(t))`, with the
  sector shares evaluated at the current equilibrium; `μ_KN − μ_KT = μ_LT − μ_LN`;
* T4 (p. 208): the Balassa–Samuelson sign claim is corrected — `μ_LN/μ_LT ≥ 1` and faster
  productivity growth in tradables raise `p` only if in addition `Â_T ≥ 0`; an explicit
  counterexample shows the book's version fails otherwise;
* T5 (p. 209): a rise in `r` lowers `p` iff `μ_LN > μ_LT` strictly (at `μ_LN = μ_LT`, `p̂ = 0`);
* T6 (pp. 211–212): with the Cobb–Douglas index `P = p^{1−γ}` (`CobbDouglasIndex`), the exact
  HBS relation `P̂ − P̂* = (1 − γ)(p̂ − p̂*)` with each country's own shares, and the book's
  formula under an explicit common-shares hypothesis (true for Cobb–Douglas technologies).
-/

namespace ObstfeldRogoff.RealExchangeRate.BalassaSamuelson

open Filter Topology Set CRSProduction

variable (F G : IntensiveTech)

/-- Supply-side equilibrium, O&R (2)–(5), p. 205: `k_T, k_N > 0`, `A_T f′(k_T) = r`,
`A_T(f − f′k_T) = w`, `pA_N g′(k_N) = r`, `pA_N(g − g′k_N) = w`. -/
def IsSupplyEqm (r AT AN kT w kN p : ℝ) : Prop :=
  0 < kT ∧ 0 < kN ∧ AT * F.fp kT = r ∧ AT * F.mpl kT = w ∧ p * AN * G.fp kN = r ∧
    p * AN * G.mpl kN = w

/-- Capital intensity of nontradables given factor prices, O&R (4)/(5), p. 206: the unique
`k_N > 0` with `g/g′ − k_N = w/r`. -/
noncomputable def kN (r w : ℝ) : ℝ := G.wrInv (w / r)

/-- Unit cost of nontradables at unit productivity, O&R (4), p. 206: `c(r, w) = r/g′(k_N)`,
which equals `pA_N` in equilibrium. -/
noncomputable def unitCost (r w : ℝ) : ℝ := r / G.fp (kN G r w)

/-- Equilibrium relative price of nontradables, O&R p. 206: `p(r, A_T, A_N) = c(r, w)/A_N`
with `w = w(r, A_T)` from the frontier (6). -/
noncomputable def eqmPrice (r AT AN : ℝ) : ℝ := unitCost G r (F.wage AT r) / AN

/-- Labour's share in tradables, O&R p. 208: `μ_LT = wL_T/Y_T = w/(A_T f(k_T))`. -/
noncomputable def muLT (r AT : ℝ) : ℝ := F.wage AT r / (AT * F.f (F.kstar AT r))

/-- Capital's share in tradables, O&R p. 209: `μ_KT = rK_T/Y_T = rk_T/(A_T f(k_T))`. -/
noncomputable def muKT (r AT : ℝ) : ℝ := r * F.kstar AT r / (AT * F.f (F.kstar AT r))

/-- Labour's share in nontradables, O&R p. 208: `μ_LN = wL_N/(pY_N) = w/(pA_N g(k_N))`
(independent of `A_N`). -/
noncomputable def muLN (r AT : ℝ) : ℝ :=
  F.wage AT r / (unitCost G r (F.wage AT r) * G.f (kN G r (F.wage AT r)))

/-- Capital's share in nontradables, O&R p. 209: `μ_KN = rK_N/(pY_N)`. -/
noncomputable def muKN (r AT : ℝ) : ℝ :=
  r * kN G r (F.wage AT r) / (unitCost G r (F.wage AT r) * G.f (kN G r (F.wage AT r)))

/-- Nontraded capital intensity solves the wage–rental condition, O&R (4)/(5), p. 206. -/
theorem kN_spec {r w : ℝ} (hr : 0 < r) (hw : 0 < w) :
    0 < kN G r w ∧ G.wageRental (kN G r w) = w / r :=
  G.wrInv_spec (div_pos hw hr)

/-- The nontraded unit cost satisfies the nontraded first-order conditions (4) and (5),
O&R p. 205, with `pA_N = c(r, w)`. -/
theorem unitCost_foc {r w : ℝ} (hr : 0 < r) (hw : 0 < w) :
    0 < unitCost G r w ∧ unitCost G r w * G.fp (kN G r w) = r ∧
      unitCost G r w * G.mpl (kN G r w) = w := by
  obtain ⟨hk, hω⟩ := kN_spec G hr hw
  have hfp := G.fp_pos _ hk
  refine ⟨div_pos hr hfp, div_mul_cancel₀ r hfp.ne', ?_⟩
  unfold IntensiveTech.wageRental at hω
  unfold unitCost
  rw [div_eq_div_iff hfp.ne' hr.ne'] at hω
  field_simp
  linarith

/-- Unit cost is the minimum cost of a unit of output, O&R (7) with fn. 19: for every
`k ≥ 0`, `c(r, w) g(k) ≤ rk + w`. -/
theorem unitCost_le {r w k : ℝ} (hr : 0 < r) (hw : 0 < w) (hk : 0 ≤ k) :
    unitCost G r w * G.f k ≤ r * k + w := by
  obtain ⟨h0, h1, h2⟩ := unitCost_foc G hr hw
  have := G.crs_profit_le h0 (kN_spec G hr hw).1 h1 h2 hk one_pos
  simpa using this

/-- Zero profit in nontradables, O&R (7), p. 208: `pA_N g(k_N) = rk_N + w`. -/
theorem unitCost_zero_profit {r w : ℝ} (hr : 0 < r) (hw : 0 < w) :
    unitCost G r w * G.f (kN G r w) = r * kN G r w + w := by
  obtain ⟨_, h1, h2⟩ := unitCost_foc G hr hw
  exact G.zero_profit h1 h2

/-- Shephard's lemma along a path, used for O&R (9) and p. 209: if `R(t)` and `W(t)` are
differentiable at `x` then `d c(R, W)/dt = (R′ k_N + W′)/g(k_N)` (exact envelope theorem;
`k_N/g` and `1/g` are the unit input requirements). -/
theorem unitCost_path_hasDerivAt {R W : ℝ → ℝ} {R' W' x : ℝ} (hR : HasDerivAt R R' x)
    (hW : HasDerivAt W W' x) (hR0 : 0 < R x) (hW0 : 0 < W x) :
    HasDerivAt (fun y => unitCost G (R y) (W y))
      ((R' * kN G (R x) (W x) + W') / G.f (kN G (R x) (W x))) x := by
  set k0 := kN G (R x) (W x) with hk0def
  have hk0 := (kN_spec G hR0 hW0).1
  have hg0 := G.f_pos hk0
  have hkc : ContinuousAt (fun y => kN G (R y) (W y)) x :=
    ContinuousAt.comp (f := fun y => W y / R y) (G.wrInv_continuousAt (div_pos hW0 hR0))
      (hW.continuousAt.div hR.continuousAt hR0.ne')
  have hgk : ContinuousAt (fun y => G.f (kN G (R y) (W y))) x :=
    ContinuousAt.comp (f := fun y => kN G (R y) (W y)) (G.hasDeriv _ hk0).continuousAt hkc
  have sR := hasDerivAt_iff_tendsto_slope.1 hR
  have sW := hasDerivAt_iff_tendsto_slope.1 hW
  have ha : Tendsto (fun y => (slope R x y * kN G (R y) (W y) + slope W x y) /
      G.f (kN G (R y) (W y))) (𝓝[≠] x) (𝓝 ((R' * k0 + W') / G.f k0)) :=
    ((sR.mul (hkc.tendsto.mono_left nhdsWithin_le_nhds)).add sW).div
      (hgk.tendsto.mono_left nhdsWithin_le_nhds) hg0.ne'
  have hb : Tendsto (fun y => (slope R x y * k0 + slope W x y) / G.f k0) (𝓝[≠] x)
      (𝓝 ((R' * k0 + W') / G.f k0)) :=
    ((sR.mul tendsto_const_nhds).add sW).div_const _
  refine hasDerivAt_of_between ha hb ?_
  have eR : ∀ᶠ y in 𝓝[≠] x, 0 < R y :=
    nhdsWithin_le_nhds (hR.continuousAt.eventually (Ioi_mem_nhds hR0))
  have eW : ∀ᶠ y in 𝓝[≠] x, 0 < W y :=
    nhdsWithin_le_nhds (hW.continuousAt.eventually (Ioi_mem_nhds hW0))
  filter_upwards [eR, eW, self_mem_nhdsWithin] with y hRy hWy hne
  have hyx : y - x ≠ 0 := sub_ne_zero.2 hne
  have dR : (y - x) * slope R x y = R y - R x := by
    rw [slope_def_field]; field_simp
  have dW : (y - x) * slope W x y = W y - W x := by
    rw [slope_def_field]; field_simp
  have hky := (kN_spec G hRy hWy).1
  have hgy := G.f_pos hky
  have z0 := unitCost_zero_profit G hR0 hW0
  have zy := unitCost_zero_profit G hRy hWy
  have i0 := unitCost_le G hR0 hW0 hky.le
  have iy := unitCost_le G hRy hWy hk0.le
  rw [← hk0def] at z0
  constructor
  · have e : (y - x) * ((slope R x y * kN G (R y) (W y) + slope W x y) /
        G.f (kN G (R y) (W y)))
        = ((R y - R x) * kN G (R y) (W y) + (W y - W x)) / G.f (kN G (R y) (W y)) := by
      rw [← dR, ← dW]; ring
    rw [e, div_le_iff₀ hgy]
    have : (unitCost G (R y) (W y) - unitCost G (R x) (W x)) * G.f (kN G (R y) (W y))
        = unitCost G (R y) (W y) * G.f (kN G (R y) (W y))
          - unitCost G (R x) (W x) * G.f (kN G (R y) (W y)) := by ring
    rw [this]; linarith
  · have e : (y - x) * ((slope R x y * k0 + slope W x y) / G.f k0)
        = ((R y - R x) * k0 + (W y - W x)) / G.f k0 := by
      rw [← dR, ← dW]; ring
    rw [e, le_div_iff₀ hg0]
    have : (unitCost G (R y) (W y) - unitCost G (R x) (W x)) * G.f k0
        = unitCost G (R y) (W y) * G.f k0 - unitCost G (R x) (W x) * G.f k0 := by ring
    rw [this]; linarith

/-- T1 existence, O&R p. 206: `(k_T(r, A_T), w(r, A_T), k_N, p(r, A_T, A_N))` solves the
supply-side system (2)–(5). -/
theorem supplyEqm_exists {r AT AN : ℝ} (hr : 0 < r) (hAT : 0 < AT) (hAN : 0 < AN) :
    IsSupplyEqm F G r AT AN (F.kstar AT r) (F.wage AT r) (kN G r (F.wage AT r))
      (eqmPrice F G r AT AN) := by
  obtain ⟨hkT, hfocT⟩ := F.kstar_foc hAT hr
  have hw := F.wage_pos hAT hr
  obtain ⟨hc, h1, h2⟩ := unitCost_foc G hr hw
  have hpA : eqmPrice F G r AT AN * AN = unitCost G r (F.wage AT r) := by
    unfold eqmPrice; field_simp
  exact ⟨hkT, (kN_spec G hr hw).1, hfocT, rfl, by rw [hpA]; exact h1, by rw [hpA]; exact h2⟩

/-- T1 uniqueness, O&R p. 206: every solution of (2)–(5) is the one above. In particular the
relative price `p` is pinned down by `r`, `A_T`, `A_N` and technology alone: demand plays no
role. -/
theorem supplyEqm_unique {r AT AN kT w k p : ℝ} (hr : 0 < r) (hAT : 0 < AT)
    (h : IsSupplyEqm F G r AT AN kT w k p) :
    kT = F.kstar AT r ∧ w = F.wage AT r ∧ k = kN G r w ∧ p = eqmPrice F G r AT AN := by
  obtain ⟨hkT, hk, h2, h3, h4, h5⟩ := h
  have ekT : kT = F.kstar AT r := F.kstar_unique hAT hr hkT h2
  have ew : w = F.wage AT r := by rw [← h3, ekT]; rfl
  have hw : 0 < w := ew ▸ F.wage_pos hAT hr
  have hfp := G.fp_pos k hk
  have hpA : p * AN ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h4; linarith
  have hω : G.wageRental k = w / r := by
    unfold IntensiveTech.wageRental
    rw [← h4, ← h5, mul_div_mul_left _ _ hpA]
  have ek : k = kN G r w := by
    obtain ⟨h1', h2'⟩ := kN_spec G hr hw
    exact (G.existsUnique_wageRental_eq (div_pos hw hr)).unique ⟨hk, hω⟩ ⟨h1', h2'⟩
  refine ⟨ekT, ew, ek, ?_⟩
  have hAN : AN ≠ 0 := by intro h0; apply hpA; rw [h0, mul_zero]
  unfold eqmPrice unitCost
  rw [← ew, ← ek]
  field_simp
  linarith

/-- T1, O&R p. 206: for `r, A_T, A_N > 0` the supply-side system (2)–(5) has exactly one
solution `(k_T, w, k_N, p)`. -/
theorem supplyEqm_existsUnique {r AT AN : ℝ} (hr : 0 < r) (hAT : 0 < AT) (hAN : 0 < AN) :
    ∃! x : ℝ × ℝ × ℝ × ℝ, IsSupplyEqm F G r AT AN x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  refine ⟨(F.kstar AT r, F.wage AT r, kN G r (F.wage AT r), eqmPrice F G r AT AN),
    supplyEqm_exists F G hr hAT hAN, ?_⟩
  rintro ⟨a, b, c, d⟩ hx
  obtain ⟨e1, e2, e3, e4⟩ := supplyEqm_unique F G hr hAT hx
  simp only at e1 e2 e3 e4
  subst e1 e2 e3 e4
  rfl

/-- The equilibrium price of nontradables is positive, O&R p. 206. -/
theorem eqmPrice_pos {r AT AN : ℝ} (hr : 0 < r) (hAT : 0 < AT) (hAN : 0 < AN) :
    0 < eqmPrice F G r AT AN :=
  div_pos (unitCost_foc G hr (F.wage_pos hAT hr)).1 hAN

/-- A higher wage raises the nontraded capital intensity, O&R p. 206 (MPL schedule). -/
theorem kN_strictMonoOn_w {r : ℝ} (hr : 0 < r) : StrictMonoOn (kN G r) (Ioi 0) := by
  intro w1 hw1 w2 hw2 h
  exact G.wrInv_strictMonoOn (div_pos (show (0 : ℝ) < w1 from hw1) hr)
    (div_pos (show (0 : ℝ) < w2 from hw2) hr) (div_lt_div_of_pos_right h hr)

/-- A higher wage raises the nontraded unit cost, O&R p. 208. -/
theorem unitCost_strictMonoOn_w {r : ℝ} (hr : 0 < r) : StrictMonoOn (unitCost G r) (Ioi 0) := by
  intro w1 hw1 w2 hw2 h
  have hk := kN_strictMonoOn_w G hr hw1 hw2 h
  have hk1 := (kN_spec G hr (show (0 : ℝ) < w1 from hw1)).1
  have hk2 := (kN_spec G hr (show (0 : ℝ) < w2 from hw2)).1
  have hfp := G.fp_strictAnti hk1 hk2 hk
  exact div_lt_div_of_pos_left hr (G.fp_pos _ hk2) hfp

/-- T2, O&R p. 208: a rise in tradables productivity `A_T` raises the equilibrium relative
price of nontradables. -/
theorem eqmPrice_strictMonoOn_AT {r AN : ℝ} (hr : 0 < r) (hAN : 0 < AN) :
    StrictMonoOn (fun a => eqmPrice F G r a AN) (Ioi 0) := by
  intro a1 ha1 a2 ha2 h
  have hw := F.wage_strictMonoOn_A hr ha1 ha2 h
  exact div_lt_div_of_pos_right (unitCost_strictMonoOn_w G hr
    (F.wage_pos (show (0 : ℝ) < a1 from ha1) hr) (F.wage_pos (show (0 : ℝ) < a2 from ha2) hr)
    hw) hAN

/-- T2, O&R p. 208: a rise in `A_T` raises the capital intensity of nontradables. -/
theorem eqm_kN_strictMonoOn_AT {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (fun a => kN G r (F.wage a r)) (Ioi 0) := by
  intro a1 ha1 a2 ha2 h
  exact kN_strictMonoOn_w G hr (F.wage_pos (show (0 : ℝ) < a1 from ha1) hr)
    (F.wage_pos (show (0 : ℝ) < a2 from ha2) hr) (F.wage_strictMonoOn_A hr ha1 ha2 h)

/-- T2, O&R p. 208: a change in nontradables productivity `A_N` leaves `k_N` unchanged and
moves `p` in exact inverse proportion (`pA_N` constant). -/
theorem eqm_AN_neutral {r AT AN AN' kT w k p kT' w' k' p' : ℝ} (hr : 0 < r) (hAT : 0 < AT)
    (h : IsSupplyEqm F G r AT AN kT w k p) (h' : IsSupplyEqm F G r AT AN' kT' w' k' p') :
    k = k' ∧ p * AN = p' * AN' := by
  obtain ⟨_, e2, e3, _⟩ := supplyEqm_unique F G hr hAT h
  obtain ⟨_, e2', e3', _⟩ := supplyEqm_unique F G hr hAT h'
  have ek : k = k' := by rw [e3, e3', e2, e2']
  refine ⟨ek, ?_⟩
  obtain ⟨_, hk, _, _, h4, _⟩ := h
  obtain ⟨_, _, _, _, h4', _⟩ := h'
  have hfp := G.fp_pos k hk
  rw [← ek] at h4'
  have : p * AN * G.fp k = p' * AN' * G.fp k := h4.trans h4'.symm
  exact mul_right_cancel₀ hfp.ne' this

/-- The factor shares in tradables sum to one, O&R p. 209: `μ_KT = 1 − μ_LT`. -/
theorem muKT_add_muLT {r AT : ℝ} (hr : 0 < r) (hAT : 0 < AT) :
    muKT F r AT + muLT F r AT = 1 := by
  obtain ⟨hk, h1⟩ := F.kstar_foc hAT hr
  have z := F.zero_profit h1 rfl
  have hY : 0 < AT * F.f (F.kstar AT r) := mul_pos hAT (F.f_pos hk)
  unfold muKT muLT
  rw [← add_div, div_eq_one_iff_eq hY.ne']
  unfold IntensiveTech.wage; linarith

/-- The factor shares in nontradables sum to one, O&R p. 209: `μ_KN = 1 − μ_LN`. -/
theorem muKN_add_muLN {r AT : ℝ} (hr : 0 < r) (hAT : 0 < AT) :
    muKN F G r AT + muLN F G r AT = 1 := by
  have hw := F.wage_pos hAT hr
  have z := unitCost_zero_profit G hr hw
  have hY : 0 < unitCost G r (F.wage AT r) * G.f (kN G r (F.wage AT r)) :=
    mul_pos (unitCost_foc G hr hw).1 (G.f_pos (kN_spec G hr hw).1)
  unfold muKN muLN
  rw [← add_div, div_eq_one_iff_eq hY.ne']
  linarith

/-- O&R p. 209: `μ_KN − μ_KT = μ_LT − μ_LN`. -/
theorem muKN_sub_muKT {r AT : ℝ} (hr : 0 < r) (hAT : 0 < AT) :
    muKN F G r AT - muKT F r AT = muLT F r AT - muLN F G r AT := by
  have h1 := muKT_add_muLT F hr hAT
  have h2 := muKN_add_muLN F G hr hAT
  linarith

/-- Labour's share in tradables is positive, O&R p. 208. -/
theorem muLT_pos {r AT : ℝ} (hr : 0 < r) (hAT : 0 < AT) : 0 < muLT F r AT :=
  div_pos (F.wage_pos hAT hr) (mul_pos hAT (F.f_pos (F.kstar_foc hAT hr).1))

/-- Labour's share in nontradables is positive, O&R p. 208. -/
theorem muLN_pos {r AT : ℝ} (hr : 0 < r) (hAT : 0 < AT) : 0 < muLN F G r AT := by
  have hw := F.wage_pos hAT hr
  exact div_pos hw (mul_pos (unitCost_foc G hr hw).1 (G.f_pos (kN_spec G hr hw).1))

/-- Ratio of labour shares, O&R p. 208: `μ_LN/μ_LT = Y_T/L_T ÷ pY_N/L_N`, i.e.
`A_T f(k_T)/(pA_N g(k_N))`. -/
theorem muLN_div_muLT {r AT : ℝ} (hr : 0 < r) (hAT : 0 < AT) :
    muLN F G r AT / muLT F r AT = AT * F.f (F.kstar AT r) /
      (unitCost G r (F.wage AT r) * G.f (kN G r (F.wage AT r))) := by
  have hw := F.wage_pos hAT hr
  have hf := F.f_pos (F.kstar_foc hAT hr).1
  have hc := (unitCost_foc G hr hw).1
  have hg := G.f_pos (kN_spec G hr hw).1
  unfold muLN muLT
  field_simp

/-- T3, O&R (8), p. 208, and its interest-rate analogue: along any differentiable path of
`(A_T(t), r(t))` the wage satisfies, exactly,
`ŵ = Â_T/μ_LT − (μ_KT/μ_LT) r̂` (hats are logarithmic derivatives). With `r` constant this is
(8), `Â_T = μ_LT ŵ`. -/
theorem logWage_path_hasDerivAt {AT R : ℝ → ℝ} {AT' R' t : ℝ} (hA : HasDerivAt AT AT' t)
    (hR : HasDerivAt R R' t) (hA0 : 0 < AT t) (hR0 : 0 < R t) :
    HasDerivAt (fun s => Real.log (F.wage (AT s) (R s)))
      (1 / muLT F (R t) (AT t) * (AT' / AT t)
        - muKT F (R t) (AT t) / muLT F (R t) (AT t) * (R' / R t)) t := by
  have hw := F.wage_pos hA0 hR0
  have hk := (F.kstar_foc hA0 hR0).1
  have hf := F.f_pos hk
  refine ((F.wage_path_hasDerivAt hA hR hA0 hR0).log hw.ne').congr_deriv ?_
  unfold muLT muKT
  field_simp

/-- T3, O&R (9) and p. 209 combined: along any differentiable path of `(r(t), A_T(t), A_N(t))`
the equilibrium relative price of nontradables satisfies, exactly,
`p̂ = (μ_LN/μ_LT) Â_T − Â_N + ((μ_LT − μ_LN)/μ_LT) r̂`. -/
theorem logPrice_path_hasDerivAt {R AT AN : ℝ → ℝ} {R' AT' AN' t : ℝ}
    (hR : HasDerivAt R R' t) (hA : HasDerivAt AT AT' t) (hN : HasDerivAt AN AN' t)
    (hR0 : 0 < R t) (hA0 : 0 < AT t) (hN0 : 0 < AN t) :
    HasDerivAt (fun s => Real.log (eqmPrice F G (R s) (AT s) (AN s)))
      (muLN F G (R t) (AT t) / muLT F (R t) (AT t) * (AT' / AT t) - AN' / AN t
        + (muLT F (R t) (AT t) - muLN F G (R t) (AT t)) / muLT F (R t) (AT t) * (R' / R t))
      t := by
  have hw := F.wage_pos hA0 hR0
  have hk := (F.kstar_foc hA0 hR0).1
  have hf := F.f_pos hk
  have hW := F.wage_path_hasDerivAt hA hR hA0 hR0
  have hC := unitCost_path_hasDerivAt G hR hW hR0 hw
  have hP := hC.div hN hN0.ne'
  have hp := eqmPrice_pos F G hR0 hA0 hN0
  refine (hP.log hp.ne').congr_deriv ?_
  obtain ⟨hc, _, _⟩ := unitCost_foc G hR0 hw
  have hkn := (kN_spec G hR0 hw).1
  have hg := G.f_pos hkn
  have hY := mul_pos hc hg
  have z1 := F.zero_profit (w := F.wage (AT t) (R t)) (F.kstar_foc hA0 hR0).2 rfl
  have z2 := unitCost_zero_profit G hR0 hw
  have hr1 := muLN_div_muLT F G hR0 hA0
  have hr2 : (muLT F (R t) (AT t) - muLN F G (R t) (AT t)) / muLT F (R t) (AT t)
      = R t * (kN G (R t) (F.wage (AT t) (R t)) - F.kstar (AT t) (R t))
        / (unitCost G (R t) (F.wage (AT t) (R t)) * G.f (kN G (R t) (F.wage (AT t) (R t)))) := by
    rw [sub_div, div_self (muLT_pos F hR0 hA0).ne', hr1, eq_div_iff hY.ne', sub_mul,
      div_mul_cancel₀ _ hY.ne']
    linarith
  rw [hr1, hr2]
  simp only [Pi.div_apply]
  field_simp
  ring

/-- T3 with the interest rate fixed, O&R (9), p. 208: `p̂ = (μ_LN/μ_LT) Â_T − Â_N`. -/
theorem logPrice_hat_eq9 {r : ℝ} {AT AN : ℝ → ℝ} {AT' AN' t : ℝ} (hA : HasDerivAt AT AT' t)
    (hN : HasDerivAt AN AN' t) (hr : 0 < r) (hA0 : 0 < AT t) (hN0 : 0 < AN t) :
    HasDerivAt (fun s => Real.log (eqmPrice F G r (AT s) (AN s)))
      (muLN F G r (AT t) / muLT F r (AT t) * (AT' / AT t) - AN' / AN t) t := by
  have := logPrice_path_hasDerivAt F G (hasDerivAt_const t r) hA hN hr hA0 hN0
  simpa using this

/-- T3 with productivities fixed, O&R p. 209: `p̂ = ((μ_LT − μ_LN)/μ_LT) r̂`. -/
theorem logPrice_hat_r {AT AN : ℝ} {R : ℝ → ℝ} {R' t : ℝ} (hR : HasDerivAt R R' t)
    (hR0 : 0 < R t) (hA0 : 0 < AT) (hN0 : 0 < AN) :
    HasDerivAt (fun s => Real.log (eqmPrice F G (R s) AT AN))
      ((muLT F (R t) AT - muLN F G (R t) AT) / muLT F (R t) AT * (R' / R t)) t := by
  have := logPrice_path_hasDerivAt F G hR (hasDerivAt_const t AT) (hasDerivAt_const t AN)
    hR0 hA0 hN0
  simpa using this

/-- T4, corrected Balassa–Samuelson inequality, O&R p. 208: if `μ_LN/μ_LT ≥ 1` AND `Â_T ≥ 0`,
then `p̂ = (μ_LN/μ_LT)Â_T − Â_N ≥ Â_T − Â_N`. -/
theorem bs_price_growth_ge {μLT μLN AT AN : ℝ} (hT : 0 < μLT) (hle : μLT ≤ μLN)
    (hA : 0 ≤ AT) : AT - AN ≤ μLN / μLT * AT - AN := by
  have : 1 ≤ μLN / μLT := (one_le_div hT).2 hle
  nlinarith

/-- T4, corrected Balassa–Samuelson theorem, O&R p. 208: with `μ_LN ≥ μ_LT`, `Â_T ≥ 0` and
faster productivity growth in tradables (`Â_T > Â_N`), the price of nontradables rises. -/
theorem bs_price_rises {μLT μLN AT AN : ℝ} (hT : 0 < μLT) (hle : μLT ≤ μLN) (hA : 0 ≤ AT)
    (hfaster : AN < AT) : 0 < μLN / μLT * AT - AN := by
  have := bs_price_growth_ge hT hle hA (AN := AN)
  linarith

/-- T4 counterexample, O&R p. 208: the book's claim (only `μ_LN/μ_LT ≥ 1` and `Â_T > Â_N`)
is false: with `μ_LT = 1/4`, `μ_LN = 1/2`, `Â_T = −1`, `Â_N = −3/2` the price falls,
`p̂ = −1/2`. -/
theorem bs_sign_counterexample :
    ∃ μLT μLN AT AN : ℝ, 0 < μLT ∧ μLT ≤ μLN ∧ μLN < 1 ∧ AN < AT ∧ μLN / μLT * AT - AN < 0 :=
  ⟨1 / 4, 1 / 2, -1, -3 / 2, by norm_num⟩

/-- T4 for the model's exact derivative, O&R (9), p. 208: at an equilibrium with
`μ_LN ≥ μ_LT`, non-negative tradables productivity growth and `Â_T > Â_N` (constant `r`),
the relative price of nontradables is strictly rising. -/
theorem eqm_logPrice_deriv_pos {r : ℝ} {AT AN : ℝ → ℝ} {AT' AN' t D : ℝ}
    (hA : HasDerivAt AT AT' t) (hN : HasDerivAt AN AN' t) (hr : 0 < r) (hA0 : 0 < AT t)
    (hN0 : 0 < AN t) (hle : muLT F r (AT t) ≤ muLN F G r (AT t)) (hA' : 0 ≤ AT')
    (hfaster : AN' / AN t < AT' / AT t)
    (hD : HasDerivAt (fun s => Real.log (eqmPrice F G r (AT s) (AN s))) D t) : 0 < D := by
  rw [hD.unique (logPrice_hat_eq9 F G hA hN hr hA0 hN0)]
  exact bs_price_rises (muLT_pos F hr hA0) hle (div_nonneg hA' hA0.le) hfaster

/-- T5, O&R p. 209: a rise in `r` lowers `p` when nontradables are STRICTLY more labour
intensive, `μ_LN > μ_LT`. -/
theorem price_falls_with_r {μLT μLN rhat : ℝ} (hT : 0 < μLT) (hlt : μLT < μLN)
    (hr : 0 < rhat) : (μLT - μLN) / μLT * rhat < 0 :=
  mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith) hT) hr

/-- T5 boundary case, O&R p. 209: at `μ_LN = μ_LT` (allowed by the book's `≥`) a rise in `r`
leaves `p` unchanged, so "lowers" needs the strict inequality. -/
theorem price_r_boundary {μ rhat : ℝ} : (μ - μ) / μ * rhat = 0 := by simp

/-- T5 as an equivalence, O&R p. 209: the interest-rate elasticity of `p` is negative iff
`μ_LN > μ_LT`. -/
theorem r_elasticity_neg_iff {μLT μLN : ℝ} (hT : 0 < μLT) :
    (μLT - μLN) / μLT < 0 ↔ μLT < μLN := by
  rw [div_neg_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, _⟩)
    · linarith
    · linarith
  · intro h; exact Or.inr ⟨by linarith, hT⟩

/-- Real exchange rate with a Cobb–Douglas index, O&R p. 211: with `P = p^{1−γ}`,
`log(P/P*) = (1 − γ)(log p − log p*)` (uses `CobbDouglasIndex.price_numeraire`). -/
theorem hbs_log_ratio (c : CobbDouglasIndex) {p ps : ℝ} (hp : 0 < p) (hps : 0 < ps) :
    Real.log (c.price 1 p / c.price 1 ps) = (1 - c.γ) * (Real.log p - Real.log ps) := by
  rw [c.price_numeraire, c.price_numeraire, Real.log_div (Real.rpow_pos_of_pos hp _).ne'
    (Real.rpow_pos_of_pos hps _).ne', Real.log_rpow hp, Real.log_rpow hps]
  ring

/-- T6, exact Harrod–Balassa–Samuelson relation, O&R p. 212: two countries with the same
technologies `F`, `G`, the same world interest rate and Cobb–Douglas price indices; along
differentiable productivity paths,
`P̂ − P̂* = (1 − γ)[(μ_LN/μ_LT)Â_T − Â_N − ((μ*_LN/μ*_LT)Â*_T − Â*_N)]`,
each country's shares evaluated at its own equilibrium. -/
theorem hbs_path_hasDerivAt (c : CobbDouglasIndex) {r : ℝ} {AT AN ATs ANs : ℝ → ℝ}
    {AT' AN' ATs' ANs' t : ℝ} (hA : HasDerivAt AT AT' t) (hN : HasDerivAt AN AN' t)
    (hAs : HasDerivAt ATs ATs' t) (hNs : HasDerivAt ANs ANs' t) (hr : 0 < r)
    (hA0 : 0 < AT t) (hN0 : 0 < AN t) (hAs0 : 0 < ATs t) (hNs0 : 0 < ANs t) :
    HasDerivAt (fun s => Real.log (c.price 1 (eqmPrice F G r (AT s) (AN s)) /
        c.price 1 (eqmPrice F G r (ATs s) (ANs s))))
      ((1 - c.γ) * ((muLN F G r (AT t) / muLT F r (AT t) * (AT' / AT t) - AN' / AN t)
        - (muLN F G r (ATs t) / muLT F r (ATs t) * (ATs' / ATs t) - ANs' / ANs t))) t := by
  have h := ((logPrice_hat_eq9 F G hA hN hr hA0 hN0).sub
    (logPrice_hat_eq9 F G hAs hNs hr hAs0 hNs0)).const_mul (1 - c.γ)
  refine h.congr_of_eventuallyEq ?_
  have e1 := hA.continuousAt.eventually (Ioi_mem_nhds hA0)
  have e2 := hN.continuousAt.eventually (Ioi_mem_nhds hN0)
  have e3 := hAs.continuousAt.eventually (Ioi_mem_nhds hAs0)
  have e4 := hNs.continuousAt.eventually (Ioi_mem_nhds hNs0)
  filter_upwards [e1, e2, e3, e4] with s h1 h2 h3 h4
  exact hbs_log_ratio c (eqmPrice_pos F G hr h1 h2) (eqmPrice_pos F G hr h3 h4)

/-- T6, the book's HBS formula, O&R p. 212, under the (implicit) hypothesis that both
countries have the same ratio `μ_LN/μ_LT = ρ`:
`P̂ − P̂* = (1 − γ)[ρ(Â_T − Â*_T) − (Â_N − Â*_N)]`. -/
theorem hbs_common_shares (c : CobbDouglasIndex) {r ρ : ℝ} {AT AN ATs ANs : ℝ → ℝ}
    {AT' AN' ATs' ANs' t : ℝ} (hA : HasDerivAt AT AT' t) (hN : HasDerivAt AN AN' t)
    (hAs : HasDerivAt ATs ATs' t) (hNs : HasDerivAt ANs ANs' t) (hr : 0 < r)
    (hA0 : 0 < AT t) (hN0 : 0 < AN t) (hAs0 : 0 < ATs t) (hNs0 : 0 < ANs t)
    (hρ : muLN F G r (AT t) / muLT F r (AT t) = ρ)
    (hρs : muLN F G r (ATs t) / muLT F r (ATs t) = ρ) :
    HasDerivAt (fun s => Real.log (c.price 1 (eqmPrice F G r (AT s) (AN s)) /
        c.price 1 (eqmPrice F G r (ATs s) (ANs s))))
      ((1 - c.γ) * (ρ * (AT' / AT t - ATs' / ATs t) - (AN' / AN t - ANs' / ANs t))) t := by
  refine (hbs_path_hasDerivAt F G c hA hN hAs hNs hr hA0 hN0 hAs0 hNs0).congr_deriv ?_
  rw [hρ, hρs]; ring

/-- T6 sign, O&R p. 212, corrected as in T4: with common ratio `ρ ≥ 1`, a non-negative
tradables growth advantage `Â_T − Â*_T ≥ 0` exceeding the nontradables advantage, Home's price
level rises relative to Foreign's (`P̂ − P̂* > 0`). The counterexample of
`bs_sign_counterexample` (with differences) shows `Â_T − Â*_T ≥ 0` cannot be dropped. -/
theorem hbs_sign (c : CobbDouglasIndex) {ρ dAT dAN : ℝ} (hρ : 1 ≤ ρ) (hdA : 0 ≤ dAT)
    (hfaster : dAN < dAT) : 0 < (1 - c.γ) * (ρ * dAT - dAN) := by
  have h1 : 0 < 1 - c.γ := by linarith [c.γ_lt_one]
  have h2 : 0 < ρ * dAT - dAN := by nlinarith
  exact mul_pos h1 h2

/-- Why common shares are natural, O&R p. 212: with a Cobb–Douglas intensive technology
`f(k) = k^α`, `f′(k) = αk^{α−1}`, labour's share `(f − f′k)/f` equals `1 − α` at every `k > 0`,
hence at every equilibrium, whatever the productivity levels. -/
theorem cobbDouglas_labourShare {α k : ℝ} (hk : 0 < k) :
    (k ^ α - α * k ^ (α - 1) * k) / k ^ α = 1 - α := by
  have hkα : 0 < k ^ α := Real.rpow_pos_of_pos hk α
  rw [Real.rpow_sub_one hk.ne']
  field_simp

end ObstfeldRogoff.RealExchangeRate.BalassaSamuelson
