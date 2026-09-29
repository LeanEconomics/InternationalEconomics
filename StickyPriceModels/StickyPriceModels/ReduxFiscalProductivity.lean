/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceModels.ReduxWelfare

/-!
# The redux model: productivity and government-spending shocks

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.3,
pp. 696–706.

The book treats productivity shocks (§10.3.1, `a = −(κ − κ̄₀)/κ̄₀`) and government-spending
shocks (§10.3.2, a CES government basket with the same `θ`, dissipative, financed by lump-sum taxes)
separately and notes that the effects are additive in the linear model (p. 698). We therefore
solve ONE linear system that carries money, productivity and government spending at once
(`FiscalSteadyLinear`, `FiscalShockEqm`) and read off every result of the section as a special
case.

* **Exact foundations.** The labour–leisure condition with a shocked `κ` is exact in logs and
  linearises to (100)–(101) (`labour_log_exact_kappa`, `linearise_100`); fn 24 (general exponent
  `μ`: `c̄ᵂ = ȳᵂ = āᵂ/μ`); government demand (109) aggregates exactly with private demand
  (`world_demand_with_gov`); (108) with (8) gives the budget with `G` (`gov_budget_combined`),
  whose steady state is (111)–(112); the level linearisations of (109), (118) and (120)
  (`linearise_113`, `linearise_118`, `linearise_121`).
* **The long run (102)–(104), (123)–(126).** `fiscalSteadyLinear_iff`: for every
  `b̄, m̄, m̄*, ā, ā*, ḡ, ḡ*` exactly one solution, with `c̄ᵂ = (āᵂ − ḡᵂ)/2`,
  `ȳᵂ = (āᵂ + ḡᵂ)/2` and the terms of trade `(δb̄/(1−n) − (ā−ā*) − (ḡ−ḡ*))/(2θ)`.
* **The short run (105)–(107), (127)–(130).** `fiscalShock_iff`: for every shock exactly one
  solution, `e = {[δ(1+θ)+2θ](m−m*) + (1+θ)[δ(g−g*) + (ḡ−ḡ*)] − (θ−1)(ā−ā*)}/D`,
  `b̄ = (1−n)(θe − (m−m*) − (g−g*))`, `cᵂ = mᵂ`, `yᵂ = mᵂ + gᵂ`,
  `r = ((1+δ)/δ)((āᵂ − ḡᵂ)/2 − mᵂ)`; the nominal interest rate is unchanged in each country
  (`fiscal_nominal_rate_unchanged`, p. 699).
* **Corollaries.** A permanent Home productivity rise appreciates the Home currency, produces a
  current-account DEFICIT and a long-run consumption differential that is tempered but not
  reversed; a temporary productivity shock changes nothing but leisure; a temporary relative rise
  in Home government spending produces a deficit and a permanent one a SURPLUS; a temporary rise in
  world spending raises world output one for one and leaves `cᵂ` and `r` unchanged (p. 705).
* **Welfare (T24, T26), closed forms the book leaves to the reader.** Permanent Home productivity
  rise: `dUᴿ_Home = (ā/(2θ))[(θ−1) + (n+θ−1)/δ] > 0`, `dUᴿ_Foreign = nā/(2θδ) > 0` (p. 700 "one
  can show"). Government spending, Home spends: flexible prices, per period, Home `−ḡ(1 − n/(2θ))`,
  Foreign `nḡ/(2θ)`; sticky prices, temporary `g`: Home `−g(1 − n/θ)`, Foreign `ng/θ`; a
  future-only `ḡ`: Home `−(ḡ/δ)(1 − n/(2θ))`, Foreign `nḡ/(2θδ)`; permanent = the sum; world
  welfare falls. Each is a derivative of lifetime utility (`fiscal_welfare_hasDerivAt`).
-/

namespace ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity

open Real Filter Topology ReduxPrimitives ReduxLogLinear ReduxSteadyState ReduxMoneyShocks
  ReduxWelfare

/-! ## Exact foundations of the productivity model (100)–(101), fn 24 -/

/-- **The labour–leisure condition with a productivity shock is exact in logs** (O&R p. 696,
(100)): if `y^{(θ+1)/θ} = ((θ−1)/(θκ)) X^{1/θ}/C` holds at `(κ₀, y₀, C₀, X₀)` and at
`(κ₁, y₁, C₁, X₁)`, then
`(θ+1)Δlog y = −θΔlog C + Δlog X − θΔlog κ`. -/
theorem labour_log_exact_kappa {θ κ0 κ1 y0 y1 C0 C1 X0 X1 : ℝ} (hθ : 1 < θ) (hκ0 : 0 < κ0)
    (hκ1 : 0 < κ1) (hy0 : 0 < y0) (hy1 : 0 < y1) (hC0 : 0 < C0) (hC1 : 0 < C1) (hX0 : 0 < X0)
    (hX1 : 0 < X1) (h0 : y0 ^ ((θ + 1) / θ) = (θ - 1) / (θ * κ0) * X0 ^ (1 / θ) / C0)
    (h1 : y1 ^ ((θ + 1) / θ) = (θ - 1) / (θ * κ1) * X1 ^ (1 / θ) / C1) :
    (θ + 1) * (Real.log y1 - Real.log y0) = -θ * (Real.log C1 - Real.log C0) +
      (Real.log X1 - Real.log X0) - θ * (Real.log κ1 - Real.log κ0) := by
  have hθ0 : θ ≠ 0 := by linarith
  have hθ1 : 0 < θ - 1 := by linarith
  have l0 := congrArg Real.log h0
  have l1 := congrArg Real.log h1
  have hA0 : 0 < (θ - 1) / (θ * κ0) := div_pos hθ1 (mul_pos (by linarith) hκ0)
  have hA1 : 0 < (θ - 1) / (θ * κ1) := div_pos hθ1 (mul_pos (by linarith) hκ1)
  rw [Real.log_rpow hy0, Real.log_div (mul_pos hA0 (rpow_pos_of_pos hX0 _)).ne' hC0.ne',
    Real.log_mul hA0.ne' (rpow_pos_of_pos hX0 _).ne', Real.log_rpow hX0,
    Real.log_div hθ1.ne' (mul_pos (by linarith) hκ0).ne',
    Real.log_mul (by linarith) hκ0.ne'] at l0
  rw [Real.log_rpow hy1, Real.log_div (mul_pos hA1 (rpow_pos_of_pos hX1 _)).ne' hC1.ne',
    Real.log_mul hA1.ne' (rpow_pos_of_pos hX1 _).ne', Real.log_rpow hX1,
    Real.log_div hθ1.ne' (mul_pos (by linarith) hκ1).ne',
    Real.log_mul (by linarith) hκ1.ne'] at l1
  have e := congrArg (fun z => θ * z) (show (θ + 1) / θ * Real.log y1 - (θ + 1) / θ *
    Real.log y0 = 1 / θ * Real.log X1 - Real.log C1 - Real.log κ1 -
      (1 / θ * Real.log X0 - Real.log C0 - Real.log κ0) by linarith)
  field_simp at e
  linarith

/-- **(100)–(101): the productivity term linearises to `θa`** (O&R p. 696): with
`κ = κ₀(1 − τa)` (so `a = −dκ/κ₀`), `d/dτ [−θ log κ] = θa` at `τ = 0`. -/
theorem linearise_100 {θ κ0 a : ℝ} (hκ0 : 0 < κ0) :
    HasDerivAt (fun τ => -θ * Real.log (κ0 * (1 - τ * a))) (θ * a) 0 := by
  have h1 : HasDerivAt (fun τ => κ0 * (1 - τ * a)) (κ0 * (-a)) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const a).const_sub 1).const_mul κ0
  have h2 := (h1.log (by simpa using hκ0.ne')).const_mul (-θ)
  convert h2 using 1
  simp
  field_simp

/-- **fn 24: with disutility `(κ/μ)y^μ`, `c̄ᵂ = ȳᵂ = āᵂ/μ`** (O&R p. 697, fn 24): the
population-weighted labour–leisure condition `(θ(μ−1)+1)ȳᵂ = −θc̄ᵂ + c̄ᵂ + θāᵂ` together with
`ȳᵂ = c̄ᵂ` gives `c̄ᵂ = āᵂ/μ` (for `μ = 2` this is (104)). -/
theorem fn24_world {θ μ aW yW cW : ℝ} (hθ : 0 < θ) (hμ : 0 < μ)
    (hlab : (θ * (μ - 1) + 1) * yW = -θ * cW + cW + θ * aW) (hy : yW = cW) :
    cW = aW / μ ∧ yW = aW / μ := by
  have h : θ * μ * cW = θ * aW := by rw [hy] at hlab; linarith
  have hc : cW = aW / μ := by
    field_simp
    have := mul_left_cancel₀ hθ.ne' (show θ * (cW * μ) = θ * aW by linarith)
    linarith
  exact ⟨hc, by rw [hy, hc]⟩

/-! ## Exact foundations of the government-spending model (108)–(112) -/

/-- **(109): government demand aggregates with private demand** (O&R pp. 700–701): if both
governments buy the CES basket with the same `θ` (demands `(p(z)/P)^{−θ}G`), then with PPP
`p/P = p*/P*` the world demand for a Home good is `(p/P)^{−θ}(Cᵂ + Gᵂ)`. -/
theorem world_demand_with_gov {θ n p P ps Ps C Cs G Gs : ℝ} (hrel : p / P = ps / Ps) :
    n * (cesDemand θ p P C + cesDemand θ p P G) +
      (1 - n) * (cesDemand θ ps Ps Cs + cesDemand θ ps Ps Gs) =
      cesDemand θ p P (worldConsumption n C Cs + worldConsumption n G Gs) := by
  unfold cesDemand worldConsumption
  rw [← hrel]
  ring

/-- **(108) with (8): the budget with government spending** (O&R p. 701): the household budget
`P B′ + M = P(1+r)B + M₋₁ + p y − P C − P τ` and the government budget (108)
`G = τ + (M − M₋₁)/P` combine to `P B′ = P(1+r)B + p y − P C − P G` (the analogue of (120)). -/
theorem gov_budget_combined {P B B1 M Mprev r py C τ G : ℝ} (hP : P ≠ 0)
    (h8 : P * B1 + M = P * (1 + r) * B + Mprev + py - P * C - P * τ)
    (h108 : G = τ + (M - Mprev) / P) :
    P * B1 = P * (1 + r) * B + py - P * C - P * G := by
  have h : P * G = P * τ + (M - Mprev) := by rw [h108]; field_simp
  linear_combination h8 + h

/-- **(111)–(112): steady-state income = expenditure with government spending** (O&R p. 701): with
constant `B` the combined budget gives `C = rB + p y/P − G` (with `r = δ`, (111)). -/
theorem gov_steady_budget {P B r py C G : ℝ} (hP : P ≠ 0)
    (h : P * B = P * (1 + r) * B + py - P * C - P * G) : C = r * B + py / P - G := by
  field_simp
  linear_combination h

/-- **(113): the level linearisation of world demand with government spending** (O&R p. 701): with
`G₀ = 0`, along `Cᵂ = X₀e^{τcᵂ}` and `Gᵂ = τ gᵂ X₀` (a LEVEL change `gᵂ = dGᵂ/C̄ᵂ₀`),
`d log(Cᵂ + Gᵂ) = cᵂ + gᵂ`. -/
theorem linearise_113 {X0 cW gW : ℝ} (hX0 : 0 < X0) :
    HasDerivAt (fun τ => Real.log (X0 * Real.exp (τ * cW) + τ * gW * X0)) (cW + gW) 0 := by
  have h1 : HasDerivAt (fun τ => X0 * Real.exp (τ * cW)) (X0 * cW) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const cW).exp.const_mul X0
  have h2 : HasDerivAt (fun τ : ℝ => τ * gW * X0) (gW * X0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const gW).mul_const X0
  have h := (h1.add h2).log (by simpa using hX0.ne')
  convert h using 1
  simp only [Pi.add_apply, zero_mul, Real.exp_zero, mul_one, add_zero]
  field_simp

/-- **(118): the level linearisation of the steady-state budget with government spending**
(O&R p. 702): around `B̄₀ = Ḡ₀ = 0`, along `B = τb̄C̄₀`, `π = e^{τu}`, `y = C̄₀e^{τŷ}`,
`G = τḡC̄₀`, `d log(δB + πy − G) = δb̄ + u + ŷ − ḡ`. -/
theorem linearise_118 {δ b u yh g C0 : ℝ} (hC0 : 0 < C0) :
    HasDerivAt (fun τ => Real.log (δ * (τ * b * C0) +
      Real.exp (τ * u) * (C0 * Real.exp (τ * yh)) - τ * g * C0)) (δ * b + u + yh - g) 0 := by
  have h1 : HasDerivAt (fun τ => δ * (τ * b * C0) + Real.exp (τ * u) * (C0 * Real.exp (τ * yh)))
      (C0 * (δ * b + u + yh)) 0 := by
    have hA : HasDerivAt (fun τ => δ * (τ * b * C0)) (δ * (b * C0)) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).mul_const b).mul_const C0).const_mul δ
    have hB : HasDerivAt (fun τ => Real.exp (τ * u)) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u).exp
    have hC : HasDerivAt (fun τ => C0 * Real.exp (τ * yh)) (C0 * yh) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const yh).exp.const_mul C0
    convert hA.add (hB.mul hC) using 1
    simp only [zero_mul, Real.exp_zero, mul_one, one_mul]
    ring
  have h2 : HasDerivAt (fun τ : ℝ => τ * g * C0) (g * C0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const g).mul_const C0
  have h := (h1.sub h2).log (by simpa using hC0.ne')
  convert h using 1
  simp only [Pi.sub_apply, zero_mul, Real.exp_zero, mul_one, mul_zero, sub_zero]
  field_simp
  ring

/-- **(121): the level linearisation of the short-run current account with government spending**
(O&R p. 702): with `B₁ = 0`, (120) gives `B₂ = πy − C − G`; along `π = e^{τu}`, `y = C̄₀e^{τŷ}`,
`C = C̄₀e^{τĉ}`, `G = τgC̄₀`, `d(B₂/C̄₀)/dτ = u + ŷ − ĉ − g`; with preset prices `u = −(1−n)e`. -/
theorem linearise_121 {u yh ch g C0 : ℝ} (hC0 : 0 < C0) :
    HasDerivAt (fun τ => (Real.exp (τ * u) * (C0 * Real.exp (τ * yh)) -
      C0 * Real.exp (τ * ch) - τ * g * C0) / C0) (u + yh - ch - g) 0 := by
  have h55 := linearise_55 (u := u) (yh := yh) (ch := ch) hC0
  have h2 : HasDerivAt (fun τ : ℝ => τ * g * C0 / C0) (g * C0 / C0) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const g).mul_const C0).div_const C0
  have h := h55.sub h2
  convert h using 1
  · funext τ; simp only [Pi.sub_apply]; ring
  · field_simp

/-! ## The long-run system with money, productivity and government spending -/

/-- The population-weighted world aggregate `xᵂ = n x + (1−n) x*` (O&R (11), (104), (115)). -/
def wavg (L : ReduxLinear) (x xs : ℝ) : ℝ := L.n * x + (1 - L.n) * xs

/-- **The long-run linear system with productivity and government spending**, O&R (102)–(104)
and (113)–(119), pp. 696–703: barred (27), (28); demand with government spending (113)–(114);
(32); the labour–leisure conditions with productivity and government spending
(100)–(101)/(116)–(117), `(θ+1)ȳ = −θc̄ + c̄ᵂ + ḡᵂ + θā`; the budgets with government spending
(118)–(119); and long-run money demand (50)–(51). For `ā = ā* = ḡ = ḡ* = 0` it is `SteadyLinear`. -/
structure FiscalSteadyLinear (L : ReduxLinear) (b m ms a as g gs : ℝ) (v : SteadyVars) : Prop where
  eq27 : v.p = L.n * v.ph + (1 - L.n) * (v.e + v.pf)
  eq28 : v.ps = L.n * (v.ph - v.e) + (1 - L.n) * v.pf
  eq113 : v.y = L.θ * (v.p - v.ph) + v.cW + wavg L g gs
  eq114 : v.ys = L.θ * (v.ps - v.pf) + v.cW + wavg L g gs
  eq32 : v.cW = L.n * v.c + (1 - L.n) * v.cs
  eq116 : (L.θ + 1) * v.y = -L.θ * v.c + v.cW + wavg L g gs + L.θ * a
  eq117 : (L.θ + 1) * v.ys = -L.θ * v.cs + v.cW + wavg L g gs + L.θ * as
  eq118 : v.c = L.δ * b + v.ph + v.y - v.p - g
  eq119 : v.cs = -(L.n / (1 - L.n)) * L.δ * b + v.pf + v.ys - v.ps - gs
  eq50 : v.p = m - v.c
  eq51 : v.ps = ms - v.cs

/-- The long-run terms of trade `p̄(h) − ē − p̄*(f) = (δb̄/(1−n) − (ā−ā*) − (ḡ−ḡ*))/(2θ)`, O&R
(46), (103), (126). -/
noncomputable def fiscalToT (L : ReduxLinear) (b a as g gs : ℝ) : ℝ :=
  (L.δ * b / (1 - L.n) - (a - as) - (g - gs)) / (2 * L.θ)

/-- The closed-form long-run solution with productivity and government spending, O&R
(102)–(104), (123)–(126): `c̄ᵂ = (āᵂ − ḡᵂ)/2`, `c̄ − c̄* = (θ+1)T + (ā − ā*)` with `T` the terms
of trade, and the levels. -/
noncomputable def fiscalSteadySolution (L : ReduxLinear) (b m ms a as g gs : ℝ) : SteadyVars where
  cW := (wavg L a as - wavg L g gs) / 2
  c := (wavg L a as - wavg L g gs) / 2 +
    (1 - L.n) * ((L.θ + 1) * fiscalToT L b a as g gs + (a - as))
  cs := (wavg L a as - wavg L g gs) / 2 - L.n * ((L.θ + 1) * fiscalToT L b a as g gs + (a - as))
  y := (wavg L a as + wavg L g gs) / 2 - L.θ * (1 - L.n) * fiscalToT L b a as g gs
  ys := (wavg L a as + wavg L g gs) / 2 + L.θ * L.n * fiscalToT L b a as g gs
  p := m - ((wavg L a as - wavg L g gs) / 2 +
    (1 - L.n) * ((L.θ + 1) * fiscalToT L b a as g gs + (a - as)))
  ps := ms - ((wavg L a as - wavg L g gs) / 2 -
    L.n * ((L.θ + 1) * fiscalToT L b a as g gs + (a - as)))
  e := m - ms - ((L.θ + 1) * fiscalToT L b a as g gs + (a - as))
  ph := m - ((wavg L a as - wavg L g gs) / 2 +
    (1 - L.n) * ((L.θ + 1) * fiscalToT L b a as g gs + (a - as))) +
    (1 - L.n) * fiscalToT L b a as g gs
  pf := ms - ((wavg L a as - wavg L g gs) / 2 -
    L.n * ((L.θ + 1) * fiscalToT L b a as g gs + (a - as))) - L.n * fiscalToT L b a as g gs

/-- **The long-run system has exactly one solution** (O&R (102)–(104), (123)–(126),
pp. 696–703): `FiscalSteadyLinear` holds IFF the unknowns equal `fiscalSteadySolution`. -/
theorem fiscalSteadyLinear_iff (L : ReduxLinear) (b m ms a as g gs : ℝ) (v : SteadyVars) :
    FiscalSteadyLinear L b m ms a as g gs v ↔ v = fiscalSteadySolution L b m ms a as g gs := by
  have hθ : L.θ ≠ 0 := by linarith [L.hθ]
  have hθ1 : L.θ + 1 ≠ 0 := by linarith [L.hθ]
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  constructor
  · intro h
    obtain ⟨h27, h28, h113, h114, h32, h116, h117, h118, h119, h50, h51⟩ := h
    rcases v with ⟨c, cs, y, ys, ph, pf, p, ps, e, cW⟩
    simp only at h27 h28 h113 h114 h32 h116 h117 h118 h119 h50 h51
    unfold wavg at h113 h114 h116 h117
    have s1 : p - ps = e := by linear_combination h27 - h28
    have s3 : L.n * y + (1 - L.n) * ys = cW + (L.n * g + (1 - L.n) * gs) := by
      rw [h113, h114, h27, h28]; ring
    have s4 : cW = ((L.n * a + (1 - L.n) * as) - (L.n * g + (1 - L.n) * gs)) / 2 := by
      have h2 : 2 * L.θ * cW = L.θ * ((L.n * a + (1 - L.n) * as) - (L.n * g + (1 - L.n) * gs)) := by
        linear_combination L.n * h116 + (1 - L.n) * h117 - (L.θ + 1) * s3 + L.θ * h32
      field_simp
      have := mul_left_cancel₀ hθ (show L.θ * (cW * 2) =
        L.θ * ((L.n * a + (1 - L.n) * as) - (L.n * g + (1 - L.n) * gs)) by linarith)
      linarith
    have s6 : y - ys = -L.θ * (ph - e - pf) := by linear_combination h113 - h114 + L.θ * s1
    have h119' : (1 - L.n) * cs = -(L.n * L.δ * b) + (1 - L.n) * (pf + ys - ps - gs) := by
      rw [h119]; field_simp; ring
    have s7 : (1 - L.n) * (c - cs) =
        L.δ * b + (1 - L.n) * ((ph - e - pf) + (y - ys) - (g - gs)) := by
      linear_combination (1 - L.n) * h118 - h119' - (1 - L.n) * s1
    have s8 : c - cs = (L.θ + 1) * (ph - e - pf) + (a - as) := by
      have h2 : L.θ * ((c - cs) - (L.θ + 1) * (ph - e - pf) - (a - as)) = 0 := by
        linear_combination h116 - h117 - (L.θ + 1) * s6
      have := (mul_eq_zero.1 h2).resolve_left hθ
      linarith
    have hT : ph - e - pf = fiscalToT L b a as g gs := by
      have h2 : (1 - L.n) * (2 * L.θ * (ph - e - pf)) =
          L.δ * b - (1 - L.n) * ((a - as) + (g - gs)) := by
        linear_combination s7 - (1 - L.n) * s8 + (1 - L.n) * s6
      unfold fiscalToT
      rw [eq_div_iff (mul_ne_zero two_ne_zero hθ)]
      field_simp
      linear_combination h2
    have hdc : c - cs = (L.θ + 1) * fiscalToT L b a as g gs + (a - as) := by rw [s8, hT]
    have hc : c = cW + (1 - L.n) * (c - cs) := by linear_combination -h32
    have hcs : cs = cW - L.n * (c - cs) := by linear_combination -h32
    have hy : y = -L.θ * (1 - L.n) * (ph - e - pf) + cW + (L.n * g + (1 - L.n) * gs) := by
      rw [h113, h27]; ring
    have hys : ys = L.θ * L.n * (ph - e - pf) + cW + (L.n * g + (1 - L.n) * gs) := by
      rw [h114, h28]; ring
    have hph : ph = p + (1 - L.n) * (ph - e - pf) := by linear_combination -h27
    have hpf : pf = ps - L.n * (ph - e - pf) := by linear_combination -h28
    have he : e = m - ms - (c - cs) := by linear_combination -s1 + h50 - h51
    simp only [fiscalSteadySolution, SteadyVars.mk.injEq]
    unfold wavg
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, s4⟩
    · rw [hc, s4, hdc]
    · rw [hcs, s4, hdc]
    · rw [hy, hT, s4]; ring
    · rw [hys, hT, s4]; ring
    · rw [hph, hT, h50, hc, s4, hdc]
    · rw [hpf, hT, h51, hcs, s4, hdc]
    · rw [h50, hc, s4, hdc]
    · rw [h51, hcs, s4, hdc]
    · rw [he, hdc]
  · rintro rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [fiscalSteadySolution, fiscalToT, wavg] <;> field_simp <;> ring

/-- **Consequences for the world and the terms of trade** (O&R (104), (123)–(124), (102), (103),
(125), (126)): any long-run solution has `c̄ᵂ = (āᵂ − ḡᵂ)/2`, `ȳᵂ = (āᵂ + ḡᵂ)/2`,
`p̄(h) − ē − p̄*(f) = (δb̄/(1−n) − (ā−ā*) − (ḡ−ḡ*))/(2θ)`,
`c̄ − c̄* = ((1+θ)/(2θ))(δb̄/(1−n) − (ḡ−ḡ*)) + ((θ−1)/(2θ))(ā−ā*)` and
`ȳ − ȳ* = −θ(p̄(h) − ē − p̄*(f))`. -/
theorem fiscalSteady_consequences {L : ReduxLinear} {b m ms a as g gs : ℝ} {v : SteadyVars}
    (h : FiscalSteadyLinear L b m ms a as g gs v) :
    v.cW = (wavg L a as - wavg L g gs) / 2 ∧
    L.n * v.y + (1 - L.n) * v.ys = (wavg L a as + wavg L g gs) / 2 ∧
    v.ph - v.e - v.pf = (L.δ * b / (1 - L.n) - (a - as) - (g - gs)) / (2 * L.θ) ∧
    v.c - v.cs = (1 + L.θ) / (2 * L.θ) * (L.δ * b / (1 - L.n) - (g - gs)) +
      (L.θ - 1) / (2 * L.θ) * (a - as) ∧
    v.y - v.ys = -L.θ * (v.ph - v.e - v.pf) := by
  have hv := (fiscalSteadyLinear_iff L b m ms a as g gs v).1 h
  have hθ : L.θ ≠ 0 := by linarith [L.hθ]
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  subst hv
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp only [fiscalSteadySolution, fiscalToT, wavg] <;>
    field_simp <;> ring

/-! ## The short run with money, productivity and government spending -/

variable (L : ReduxLinear) in
/-- **The short-run system with money, productivity and government spending**, O&R §10.3
(pp. 698–705): preset `p(h) = p*(f) = 0` in (27)–(28); short-run demand with government spending
(113)–(114); (32); the Euler equations (35)–(36) and date-1 money demands (37)–(38) (unchanged:
"government spending does not affect the money demand or the consumption Euler equations",
p. 703); the current account with government spending (121); and the long-run system at `b̄` with
permanent money `m, m*`, long-run productivity `ā, ā*` and long-run spending `ḡ, ḡ*`. Short-run
productivity does not enter: the labour–leisure conditions do not bind (p. 697). -/
structure FiscalShockEqm (m ms g gs ab abs gb gbs : ℝ) (u : ShortVars) (v : SteadyVars) : Prop where
  eq27 : u.p = L.n * 0 + (1 - L.n) * (u.e + 0)
  eq28 : u.ps = L.n * (0 - u.e) + (1 - L.n) * 0
  eq113 : u.y = L.θ * (u.p - 0) + u.cW + wavg L g gs
  eq114 : u.ys = L.θ * (u.ps - 0) + u.cW + wavg L g gs
  eq32 : u.cW = L.n * u.c + (1 - L.n) * u.cs
  eq35 : v.c = u.c + L.δ / (1 + L.δ) * u.r
  eq36 : v.cs = u.cs + L.δ / (1 + L.δ) * u.r
  eq37 : m - u.p = u.c - u.r / (1 + L.δ) - (v.p - u.p) / L.δ
  eq38 : ms - u.ps = u.cs - u.r / (1 + L.δ) - (v.ps - u.ps) / L.δ
  eq121 : u.b = u.y - u.c - (1 - L.n) * u.e - g
  longrun : FiscalSteadyLinear L u.b m ms ab abs gb gbs v

/-- The short-run exchange rate, O&R (106) and (128) combined (p. 698, p. 705):
`e = {[δ(1+θ)+2θ](m−m*) + (1+θ)[δ(g−g*) + (ḡ−ḡ*)] − (θ−1)(ā−ā*)}/D`. -/
noncomputable def fiscalE (L : ReduxLinear) (m ms g gs ab abs gb gbs : ℝ) : ℝ :=
  ((L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) + (1 + L.θ) * (L.δ * (g - gs) + (gb - gbs)) -
    (L.θ - 1) * (ab - abs)) / L.D

/-- The closed-form short-run solution, O&R (105)–(107), (127)–(130). -/
noncomputable def fiscalShortRunSolution (L : ReduxLinear) (m ms g gs ab abs gb gbs : ℝ) :
    ShortVars where
  e := fiscalE L m ms g gs ab abs gb gbs
  c := wavg L m ms + (1 - L.n) * ((m - ms) - fiscalE L m ms g gs ab abs gb gbs)
  cs := wavg L m ms - L.n * ((m - ms) - fiscalE L m ms g gs ab abs gb gbs)
  y := L.θ * (1 - L.n) * fiscalE L m ms g gs ab abs gb gbs + wavg L m ms + wavg L g gs
  ys := -(L.θ * L.n * fiscalE L m ms g gs ab abs gb gbs) + wavg L m ms + wavg L g gs
  p := (1 - L.n) * fiscalE L m ms g gs ab abs gb gbs
  ps := -(L.n * fiscalE L m ms g gs ab abs gb gbs)
  cW := wavg L m ms
  r := (1 + L.δ) / L.δ * ((wavg L ab abs - wavg L gb gbs) / 2 - wavg L m ms)
  b := (1 - L.n) * (L.θ * fiscalE L m ms g gs ab abs gb gbs - (m - ms) - (g - gs))

/-- The MM relation `m − p = c` (O&R (60); T15): the Euler equation (35), date-1 money demand
(37) and long-run money demand (50) imply that real balances move with consumption. -/
theorem mm_relation {δ m p pb c cb r : ℝ} (hδ : 0 < δ) (h35 : cb = c + δ / (1 + δ) * r)
    (h37 : m - p = c - r / (1 + δ) - (pb - p) / δ) (h50 : pb = m - cb) : m - p = c := by
  have hi := nominal_rate_unchanged hδ h35 h37 h50
  have hδ1 : (1 + δ) ≠ 0 := by linarith
  have : (pb - p) / δ = -(r / (1 + δ)) := by
    have e : pb - p = -(δ * r / (1 + δ)) := by linarith
    rw [e]; field_simp
  rw [this] at h37
  linarith

/-- **The short-run system has exactly one solution** (O&R (105)–(107), (127)–(130),
pp. 698–705): `FiscalShockEqm` holds IFF the short-run variables are `fiscalShortRunSolution`
and the long-run variables are `fiscalSteadySolution` at the implied `b̄`. -/
theorem fiscalShock_iff (L : ReduxLinear) (m ms g gs ab abs gb gbs : ℝ) (u : ShortVars)
    (v : SteadyVars) :
    FiscalShockEqm L m ms g gs ab abs gb gbs u v ↔
      u = fiscalShortRunSolution L m ms g gs ab abs gb gbs ∧
      v = fiscalSteadySolution L (fiscalShortRunSolution L m ms g gs ab abs gb gbs).b m ms ab
        abs gb gbs := by
  have hθ := L.hθ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hδ := L.hδ
  have hδ0 : L.δ ≠ 0 := hδ.ne'
  have hn1 : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hD := L.D_pos.ne'
  have hδ1 : (1 + L.δ) ≠ 0 := by linarith
  constructor
  · intro h
    have hv := (fiscalSteadyLinear_iff L u.b m ms ab abs gb gbs v).1 h.longrun
    obtain ⟨hcWlr, -, -, hdclr, -⟩ := fiscalSteady_consequences h.longrun
    have hmp := mm_relation hδ h.eq35 h.eq37 h.longrun.eq50
    have hmps := mm_relation hδ h.eq36 h.eq38 h.longrun.eq51
    have hwlr := h.longrun.eq32
    have h35 := h.eq35
    have h36 := h.eq36
    have h27 := h.eq27
    have h28 := h.eq28
    have h113 := h.eq113
    have h114 := h.eq114
    have h32 := h.eq32
    have h121 := h.eq121
    have hdiff : v.c - v.cs = u.c - u.cs := by rw [h35, h36]; ring
    rcases u with ⟨c, cs, y, ys, p, ps, e, cW, r, b⟩
    simp only at hmp hmps h35 h36 h27 h28 h113 h114 h32 h121 hdiff hdclr hv ⊢
    have hp : p = (1 - L.n) * e := by linarith
    have hps : ps = -(L.n * e) := by linarith
    have hcW : cW = wavg L m ms := by
      unfold wavg; rw [h32]; rw [hp] at hmp; rw [hps] at hmps
      linear_combination -L.n * hmp - (1 - L.n) * hmps
    have hr : r = (1 + L.δ) / L.δ * ((wavg L ab abs - wavg L gb gbs) / 2 - wavg L m ms) := by
      have hw : v.cW = cW + L.δ / (1 + L.δ) * r := by
        rw [hwlr, h35, h36, h32]; ring
      rw [hcWlr, hcW] at hw
      field_simp at hw ⊢
      linarith
    have hMM : e = (m - ms) - (c - cs) := by rw [hp] at hmp; rw [hps] at hmps; linarith
    have hb : b = (1 - L.n) * ((L.θ - 1) * e - (c - cs) - (g - gs)) := by
      rw [h121, h113, hp, h32]; unfold wavg; ring
    have hb' : b = (1 - L.n) * (L.θ * e - (m - ms) - (g - gs)) := by rw [hb, hMM]; ring
    have he : e = fiscalE L m ms g gs ab abs gb gbs := by
      rw [hdiff, hb'] at hdclr
      have h2 : (m - ms) - e = (1 + L.θ) / (2 * L.θ) *
          (L.δ * ((1 - L.n) * (L.θ * e - (m - ms) - (g - gs))) / (1 - L.n) - (gb - gbs)) +
          (L.θ - 1) / (2 * L.θ) * (ab - abs) := by rw [← hdclr]; linarith
      unfold fiscalE ReduxLinear.D
      rw [eq_div_iff (by have := L.D_pos; unfold ReduxLinear.D at this; linarith)]
      field_simp at h2
      linear_combination -h2
    refine ⟨?_, ?_⟩
    · simp only [fiscalShortRunSolution, ShortVars.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, he, hcW, hr, ?_⟩
      · rw [← he, ← hcW]; linear_combination -h32 + (1 - L.n) * hMM
      · rw [← he, ← hcW]; linear_combination -h32 - L.n * hMM
      · rw [← he, h113, hp, hcW]; ring
      · rw [← he, h114, hps, hcW]; ring
      · rw [hp, he]
      · rw [hps, he]
      · rw [hb', he]
    · rw [hv, hb', he]
      rfl
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      (fiscalSteadyLinear_iff L _ m ms ab abs gb gbs _).2 rfl⟩ <;>
      simp only [fiscalSteadySolution, fiscalShortRunSolution, fiscalE, fiscalToT, wavg,
        ReduxLinear.D] <;> field_simp <;> ring

/-- **Existence and uniqueness of the short-run equilibrium** (O&R §10.3): for every combination
of money, productivity and government-spending shocks. -/
theorem fiscalShock_existsUnique (L : ReduxLinear) (m ms g gs ab abs gb gbs : ℝ) :
    ∃! w : ShortVars × SteadyVars, FiscalShockEqm L m ms g gs ab abs gb gbs w.1 w.2 := by
  refine ⟨(fiscalShortRunSolution L m ms g gs ab abs gb gbs, fiscalSteadySolution L
    (fiscalShortRunSolution L m ms g gs ab abs gb gbs).b m ms ab abs gb gbs),
    (fiscalShock_iff L m ms g gs ab abs gb gbs _ _).2 ⟨rfl, rfl⟩, fun w hw => ?_⟩
  obtain ⟨h1, h2⟩ := (fiscalShock_iff L m ms g gs ab abs gb gbs w.1 w.2).1 hw
  exact Prod.ext h1 h2

/-- **The money-only case is the model of §10.1** (O&R p. 696: the linearised equations of
§10.1.5 are unchanged): with no productivity or government-spending shocks the system is
exactly `MoneyShockEqm`. Hence a TEMPORARY productivity shock (`ā = ā* = 0`), which enters no
short-run equation, has no effect on any variable except leisure (O&R p. 697). -/
theorem fiscal_zero_iff_money (L : ReduxLinear) (m ms : ℝ) (u : ShortVars) (v : SteadyVars) :
    FiscalShockEqm L m ms 0 0 0 0 0 0 u v ↔ MoneyShockEqm L m ms u v := by
  have hw : wavg L 0 0 = 0 := by simp [wavg]
  constructor
  · intro h
    obtain ⟨h27, h28, h113, h114, h32, h35, h36, h37, h38, h121, hl⟩ := h
    obtain ⟨l27, l28, l113, l114, l32, l116, l117, l118, l119, l50, l51⟩ := hl
    rw [hw] at h113 h114 l113 l114 l116 l117
    refine ⟨h27, h28, by linarith, by linarith, h32, h35, h36, h37, h38, by linarith,
      ⟨l27, l28, by linarith, by linarith, l32, by linarith, by linarith, by linarith,
        by linarith, l50, l51⟩⟩
  · intro h
    obtain ⟨h27, h28, h30, h31, h32, h35, h36, h37, h38, h55, hl⟩ := h
    obtain ⟨l27, l28, l30, l31, l32, l33, l34, l40, l41, l50, l51⟩ := hl
    refine ⟨h27, h28, by rw [hw]; linarith, by rw [hw]; linarith, h32, h35, h36, h37, h38,
      by linarith, ⟨l27, l28, by rw [hw]; linarith, by rw [hw]; linarith, l32,
        by rw [hw]; linarith, by rw [hw]; linarith, by linarith, by linarith, l50, l51⟩⟩

/-- **The GG schedule with productivity and government spending** (O&R (105), p. 698, and (127),
p. 704): `e = [δ(1+θ)+2θ](c−c*)/(δ(θ²−1)) + (1/(θ−1))[g − g* + (ḡ−ḡ*)/δ] − (ā−ā*)/(δ(1+θ))`. -/
theorem fiscal_gg {L : ReduxLinear} {m ms g gs ab abs gb gbs : ℝ} {u : ShortVars}
    {v : SteadyVars} (h : FiscalShockEqm L m ms g gs ab abs gb gbs u v) :
    u.e = (L.δ * (1 + L.θ) + 2 * L.θ) * (u.c - u.cs) / (L.δ * (L.θ ^ 2 - 1)) +
      1 / (L.θ - 1) * ((g - gs) + (gb - gbs) / L.δ) - (ab - abs) / (L.δ * (1 + L.θ)) := by
  obtain ⟨rfl, -⟩ := (fiscalShock_iff L m ms g gs ab abs gb gbs u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ.ne'
  have hθ1 : L.θ - 1 ≠ 0 := by linarith
  have hθ2 : 1 + L.θ ≠ 0 := by linarith
  have hsq : L.θ ^ 2 - 1 ≠ 0 := by nlinarith
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  have hθ0 : L.θ ≠ 0 := by linarith
  simp only [fiscalShortRunSolution, fiscalE, wavg, ReduxLinear.D]
  field_simp
  ring

/-- **World aggregates and the real interest rate** (O&R (104), (107), (123)–(124), (130)): in
every short-run equilibrium `cᵂ = mᵂ`, `yᵂ = mᵂ + gᵂ`, and
`r = ((1+δ)/δ)((āᵂ − ḡᵂ)/2 − mᵂ)`; in the long run `c̄ᵂ = (āᵂ − ḡᵂ)/2`, `ȳᵂ = (āᵂ + ḡᵂ)/2`. -/
theorem fiscal_world {L : ReduxLinear} {m ms g gs ab abs gb gbs : ℝ} {u : ShortVars}
    {v : SteadyVars} (h : FiscalShockEqm L m ms g gs ab abs gb gbs u v) :
    u.cW = wavg L m ms ∧ L.n * u.y + (1 - L.n) * u.ys = wavg L m ms + wavg L g gs ∧
    u.r = (1 + L.δ) / L.δ * ((wavg L ab abs - wavg L gb gbs) / 2 - wavg L m ms) ∧
    v.cW = (wavg L ab abs - wavg L gb gbs) / 2 ∧
    L.n * v.y + (1 - L.n) * v.ys = (wavg L ab abs + wavg L gb gbs) / 2 := by
  obtain ⟨h1, h2, -⟩ := fiscalSteady_consequences h.longrun
  obtain ⟨rfl, -⟩ := (fiscalShock_iff L m ms g gs ab abs gb gbs u v).1 h
  refine ⟨rfl, ?_, rfl, h1, h2⟩
  simp only [fiscalShortRunSolution]
  ring

/-- **The nominal interest rate does not change** (O&R p. 699, "the nominal interest rate doesn't
change: expected deflation exactly offsets the rise in the real interest rate"; T15): in each
country `î = δr/(1+δ) + (p̄ − p) = 0` after any combination of permanent money, productivity and
government-spending shocks. -/
theorem fiscal_nominal_rate_unchanged {L : ReduxLinear} {m ms g gs ab abs gb gbs : ℝ}
    {u : ShortVars} {v : SteadyVars} (h : FiscalShockEqm L m ms g gs ab abs gb gbs u v) :
    L.δ * u.r / (1 + L.δ) + (v.p - u.p) = 0 ∧ L.δ * u.r / (1 + L.δ) + (v.ps - u.ps) = 0 :=
  ⟨nominal_rate_unchanged L.hδ h.eq35 h.eq37 h.longrun.eq50,
    nominal_rate_unchanged L.hδ h.eq36 h.eq38 h.longrun.eq51⟩

/-! ## Productivity shocks: corollaries (105)–(107) -/

/-- **(106) and (107)** (O&R p. 698): with money and productivity shocks only,
`e = {[δ(1+θ)+2θ](m−m*) − (θ−1)(ā−ā*)}/(θδ(1+θ)+2θ)` and `r = ((1+δ)/δ)(āᵂ/2 − mᵂ)`. -/
theorem productivity_eq106_107 {L : ReduxLinear} {m ms ab abs : ℝ} {u : ShortVars}
    {v : SteadyVars} (h : FiscalShockEqm L m ms 0 0 ab abs 0 0 u v) :
    u.e = ((L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) - (L.θ - 1) * (ab - abs)) /
      (L.θ * L.δ * (1 + L.θ) + 2 * L.θ) ∧
    u.r = (1 + L.δ) / L.δ * (wavg L ab abs / 2 - wavg L m ms) := by
  obtain ⟨rfl, -⟩ := (fiscalShock_iff L m ms 0 0 ab abs 0 0 u v).1 h
  simp only [fiscalShortRunSolution, fiscalE, wavg, ReduxLinear.D]
  constructor <;> ring

/-- **A permanent rise in Home productivity** (O&R pp. 698–699; T23), no money or fiscal shock:
the exchange rate is `e = −(θ−1)ā/D < 0` (the Home currency APPRECIATES, (106)); Home runs a
current-account DEFICIT `b̄ = −(1−n)(θ−1)ā/(δ(1+θ)+2)`; the long-run consumption differential
`(θ−1)ā/D` is positive but below its flexible-price value `(θ−1)ā/(2θ)` ("tempered but not
reversed"); world consumption does not move on impact while the real interest rate rises,
`r = ((1+δ)/δ)nā/2` (107). -/
theorem productivity_corollaries {L : ReduxLinear} {a : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : FiscalShockEqm L 0 0 0 0 a 0 0 0 u v) (ha : 0 < a) :
    u.e = -((L.θ - 1) * a / L.D) ∧ u.e < 0 ∧
    u.b = -((1 - L.n) * (L.θ - 1) * a / L.E) ∧ u.b < 0 ∧
    v.c - v.cs = (L.θ - 1) * a / L.D ∧ 0 < v.c - v.cs ∧
    v.c - v.cs < (L.θ - 1) / (2 * L.θ) * a ∧ u.cW = 0 ∧
    u.r = (1 + L.δ) / L.δ * (L.n * a / 2) ∧ 0 < u.r := by
  have hdiff : v.c - v.cs = u.c - u.cs := by rw [h.eq35, h.eq36]; ring
  obtain ⟨rfl, -⟩ := (fiscalShock_iff L 0 0 0 0 a 0 0 0 u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hn0 := L.hn0
  have hn : 0 < 1 - L.n := by linarith [L.hn1]
  have hD := L.D_pos
  have hE := L.E_pos
  have hθ1 : 0 < L.θ - 1 := by linarith
  have he : (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).e = -((L.θ - 1) * a / L.D) := by
    simp only [fiscalShortRunSolution, fiscalE]; ring
  have hb : (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).b = -((1 - L.n) * (L.θ - 1) * a / L.E) := by
    simp only [fiscalShortRunSolution, fiscalE]
    rw [ReduxLinear.D_eq]
    have := hE.ne'
    have : L.θ ≠ 0 := by linarith
    field_simp; ring
  have hdc : v.c - v.cs = (L.θ - 1) * a / L.D := by
    rw [hdiff]; simp only [fiscalShortRunSolution, fiscalE, wavg]; ring
  have h1 : 0 < (L.θ - 1) * a / L.D := by positivity
  have h2 : 0 < (1 - L.n) * (L.θ - 1) * a / L.E := by positivity
  refine ⟨he, by rw [he]; linarith, hb, by rw [hb]; linarith, hdc, by rw [hdc]; positivity, ?_, ?_,
    ?_, ?_⟩
  · rw [hdc]
    have hE2 : 2 < L.E := by
      unfold ReduxLinear.E; nlinarith [mul_pos hδ (show (0 : ℝ) < 1 + L.θ by linarith)]
    rw [ReduxLinear.D_eq, div_lt_iff₀ (mul_pos (by linarith) hE)]
    have hpos : 0 < (L.θ - 1) * a := mul_pos hθ1 ha
    have e : (L.θ - 1) / (2 * L.θ) * a * (L.θ * L.E) = (L.θ - 1) * a * L.E / 2 := by
      field_simp
    have : (L.θ - 1) * a * 2 < (L.θ - 1) * a * L.E := by nlinarith
    linarith [e]
  · simp only [fiscalShortRunSolution, wavg]; ring
  · simp only [fiscalShortRunSolution, wavg]; ring
  · simp only [fiscalShortRunSolution, wavg]
    have : 0 < (1 + L.δ) / L.δ := by positivity
    have : 0 < L.n * a / 2 := by positivity
    nlinarith

/-! ## Government spending: corollaries (123)–(130) -/

/-- **(128)–(129) in the book's form** (O&R p. 705): with no money or productivity shocks,
`e = δ(1+θ)[g − g* + (ḡ−ḡ*)/δ]/D` and
`b̄ = (1−n)δ(1+θ)[g − g* + (ḡ−ḡ*)/δ]/(δ(1+θ)+2) − (1−n)(g − g*)`. -/
theorem gov_eq128_129 {L : ReduxLinear} {g gs gb gbs : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : FiscalShockEqm L 0 0 g gs 0 0 gb gbs u v) :
    u.e = L.δ * (1 + L.θ) * ((g - gs) + (gb - gbs) / L.δ) / L.D ∧
    u.b = (1 - L.n) * L.δ * (1 + L.θ) * ((g - gs) + (gb - gbs) / L.δ) / L.E -
      (1 - L.n) * (g - gs) := by
  obtain ⟨rfl, -⟩ := (fiscalShock_iff L 0 0 g gs 0 0 gb gbs u v).1 h
  have hδ := L.hδ.ne'
  have hE := L.E_pos.ne'
  have hθ0 : L.θ ≠ 0 := by linarith [L.hθ]
  simp only [fiscalShortRunSolution, fiscalE, ReduxLinear.D, ReduxLinear.E]
  refine ⟨?_, ?_⟩ <;> field_simp <;> ring

/-- **(122): the Foreign current account is implied** (O&R p. 702): in every short-run
equilibrium, `b̄* = −(n/(1−n)) b̄` (net foreign assets sum to zero, (17)) satisfies
`b̄* = y* − c* + ne − g*`. -/
theorem gov_eq122 {L : ReduxLinear} {m ms g gs ab abs gb gbs : ℝ} {u : ShortVars}
    {v : SteadyVars} (h : FiscalShockEqm L m ms g gs ab abs gb gbs u v) :
    -(L.n / (1 - L.n)) * u.b = u.ys - u.cs + L.n * u.e - gs := by
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have h121 := h.eq121
  have h113 := h.eq113
  have h114 := h.eq114
  have h27 := h.eq27
  have h28 := h.eq28
  have h32 := h.eq32
  unfold wavg at h113 h114
  have key : L.n * u.b + (1 - L.n) * (u.ys - u.cs + L.n * u.e - gs) = 0 := by
    rw [h121, h113, h114, h27, h28, h32]; ring
  field_simp
  linarith

/-- **Temporary versus permanent government spending and the current account** (O&R p. 705): a
TEMPORARY relative rise in Home spending (`ḡ = ḡ*`) gives a DEFICIT
`b̄ = −2(1−n)(g − g*)/(δ(1+θ)+2)`; a PERMANENT one (`ḡ − ḡ* = g − g*`) gives a SURPLUS
`b̄ = (1−n)(θ−1)(g − g*)/(δ(1+θ)+2)`. -/
theorem gov_current_account (L : ReduxLinear) {G : ℝ} (hG : 0 < G) :
    (fiscalShortRunSolution L 0 0 G 0 0 0 0 0).b = -(2 * (1 - L.n) * G / L.E) ∧
    (fiscalShortRunSolution L 0 0 G 0 0 0 0 0).b < 0 ∧
    (fiscalShortRunSolution L 0 0 G 0 0 0 G 0).b = (1 - L.n) * (L.θ - 1) * G / L.E ∧
    0 < (fiscalShortRunSolution L 0 0 G 0 0 0 G 0).b := by
  have hθ := L.hθ
  have hδ := L.hδ
  have hn : 0 < 1 - L.n := by linarith [L.hn1]
  have hE := L.E_pos
  have hθ0 : L.θ ≠ 0 := by linarith
  have h1 : (fiscalShortRunSolution L 0 0 G 0 0 0 0 0).b = -(2 * (1 - L.n) * G / L.E) := by
    simp only [fiscalShortRunSolution, fiscalE, ReduxLinear.D, ReduxLinear.E]
    have := hE.ne'; unfold ReduxLinear.E at this
    field_simp; ring
  have h2 : (fiscalShortRunSolution L 0 0 G 0 0 0 G 0).b = (1 - L.n) * (L.θ - 1) * G / L.E := by
    simp only [fiscalShortRunSolution, fiscalE, ReduxLinear.D, ReduxLinear.E]
    have := hE.ne'; unfold ReduxLinear.E at this
    field_simp; ring
  refine ⟨h1, ?_, h2, ?_⟩
  · rw [h1]; have : 0 < 2 * (1 - L.n) * G / L.E := by positivity
    linarith
  · rw [h2]; have : 0 < L.θ - 1 := by linarith
    positivity

/-- **A temporary rise in world government spending** (O&R p. 705): with no money, productivity
or future spending shocks, world consumption does not move, world output rises one for one,
`yᵂ = gᵂ`, and the real interest rate is unchanged, `r = 0`. -/
theorem temporary_world_spending {L : ReduxLinear} {g gs : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : FiscalShockEqm L 0 0 g gs 0 0 0 0 u v) :
    u.cW = 0 ∧ L.n * u.y + (1 - L.n) * u.ys = wavg L g gs ∧ u.r = 0 := by
  obtain ⟨h1, h2, h3, -, -⟩ := fiscal_world h
  refine ⟨by rw [h1]; simp [wavg], by rw [h2]; simp [wavg], by rw [h3]; simp [wavg]⟩

/-- **Permanent government spending under flexible prices** (O&R p. 703): in the long-run system
with `b̄ = 0` and a relative rise `ḡ > ḡ*` in Home spending, the terms of trade deteriorate,
`p̄(h) − ē − p̄*(f) = −(ḡ − ḡ*)/(2θ) < 0`, and relative Home output rises. -/
theorem gov_flex_terms_of_trade {L : ReduxLinear} {m ms gb gbs : ℝ} {v : SteadyVars}
    (h : FiscalSteadyLinear L 0 m ms 0 0 gb gbs v) (hg : gbs < gb) :
    v.ph - v.e - v.pf = -((gb - gbs) / (2 * L.θ)) ∧ v.ph - v.e - v.pf < 0 ∧
      0 < v.y - v.ys := by
  obtain ⟨-, -, hT, -, hy⟩ := fiscalSteady_consequences h
  have hθ : 0 < L.θ := by linarith [L.hθ]
  have hT' : v.ph - v.e - v.pf = -((gb - gbs) / (2 * L.θ)) := by rw [hT]; ring
  have hneg : v.ph - v.e - v.pf < 0 := by
    rw [hT']; have : 0 < (gb - gbs) / (2 * L.θ) := div_pos (by linarith) (by positivity)
    linarith
  refine ⟨hT', hneg, ?_⟩
  rw [hy]; nlinarith

/-! ## Welfare (T24, T26) -/

/-- The first-order change in real utility with a permanent productivity shock, O&R p. 700: (75)
plus the direct effect of lower `κ` on the disutility of effort in every period,
`((θ−1)/θ)(ā/2)(1 + 1/δ)`. -/
noncomputable def dURprod (L : ReduxLinear) (a c y cb yb : ℝ) : ℝ :=
  dUR L c y cb yb + (L.θ - 1) / L.θ * (a / 2) * (1 + 1 / L.δ)

/-- **The welfare derivative with a permanent productivity shock** (T24; O&R p. 700): along
`κ = κ₀(1 − τā)` in every period and log-deviations `c, ŷ, c̄, ȳ`, the derivative of `Uᴿ`
is `dURprod`. -/
theorem fiscal_welfare_hasDerivAt (M : ReduxParams) (a c y cb yb : ℝ) :
    HasDerivAt (fun τ => lifetimeWelfare M.β 0 (M.κ * (1 - τ * a))
      (twoRegime (M.ybar0 * Real.exp (τ * c)) (M.ybar0 * Real.exp (τ * cb)))
      (twoRegime (1 * Real.exp (τ * 0)) (1 * Real.exp (τ * 0)))
      (twoRegime (M.ybar0 * Real.exp (τ * y)) (M.ybar0 * Real.exp (τ * yb))))
      (dURprod (linearOf M) a c y cb yb) 0 := by
  have h := welfare_hasDerivAt M.hβ0.le M.hβ1 0 M.κ a M.ybar0 c cb 0 0 y yb M.ybar0_pos one_pos
    one_pos
  convert h using 1
  unfold dURprod dUR linearOf
  simp only
  rw [beta_div_one_sub M, M.κ_mul_ybar0_sq]
  ring

/-- **A permanent rise in Home productivity raises welfare in BOTH countries** (T24; O&R p. 700,
"one can show", left to the reader): with no money or fiscal shocks,
`dUᴿ_Home = (ā/(2θ))[(θ−1) + (n+θ−1)/δ]` (including the direct effect of lower `κ`) and
`dUᴿ_Foreign = nā/(2θδ)`, both positive for `ā > 0`. -/
theorem productivity_welfare {L : ReduxLinear} {a : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : FiscalShockEqm L 0 0 0 0 a 0 0 0 u v) :
    dURprod L a u.c u.y v.c v.y = a / (2 * L.θ) * ((L.θ - 1) + (L.n + L.θ - 1) / L.δ) ∧
    dUR L u.cs u.ys v.cs v.ys = L.n * a / (2 * L.θ * L.δ) ∧
    (0 < a → 0 < dURprod L a u.c u.y v.c v.y ∧ 0 < dUR L u.cs u.ys v.cs v.ys) := by
  obtain ⟨rfl, rfl⟩ := (fiscalShock_iff L 0 0 0 0 a 0 0 0 u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hn0 := L.hn0
  have hθ0 : L.θ ≠ 0 := by linarith
  have hδ0 : L.δ ≠ 0 := hδ.ne'
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  have hθ1 : L.θ + 1 ≠ 0 := by linarith
  have e1 : dURprod L a (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).c
      (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).y
      (fiscalSteadySolution L (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).b 0 0 a 0 0 0).c
      (fiscalSteadySolution L (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).b 0 0 a 0 0 0).y =
      a / (2 * L.θ) * ((L.θ - 1) + (L.n + L.θ - 1) / L.δ) := by
    simp only [dURprod, dUR, fiscalShortRunSolution, fiscalSteadySolution, fiscalE, fiscalToT,
      wavg, ReduxLinear.D]
    field_simp
    ring
  have e2 : dUR L (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).cs
      (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).ys
      (fiscalSteadySolution L (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).b 0 0 a 0 0 0).cs
      (fiscalSteadySolution L (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).b 0 0 a 0 0 0).ys =
      L.n * a / (2 * L.θ * L.δ) := by
    simp only [dUR, fiscalShortRunSolution, fiscalSteadySolution, fiscalE, fiscalToT,
      wavg, ReduxLinear.D]
    field_simp
    ring
  refine ⟨e1, e2, fun ha => ⟨?_, ?_⟩⟩
  · rw [e1]
    have : 0 < L.θ - 1 := by linarith
    have : 0 < L.n + L.θ - 1 := by linarith
    positivity
  · rw [e2]; positivity

/-- **fn 25: an anticipated permanent productivity rise** (O&R p. 699, fn 25): a change in `κ`
learned at date 1 but effective from date 2 leaves every short-run and long-run variable as in an
immediate permanent change (short-run productivity enters no equation of `FiscalShockEqm`); the
welfare derivative then lacks only the date-1 leisure term, which is `((θ−1)/θ)ā/2`. -/
theorem fn25_welfare_hasDerivAt (M : ReduxParams) (a c y cb yb : ℝ) :
    HasDerivAt (fun τ => ∑' s, M.β ^ s * twoRegime
      (periodWelfare 0 M.κ (M.ybar0 * Real.exp (τ * c)) 1 (M.ybar0 * Real.exp (τ * y)))
      (periodWelfare 0 (M.κ * (1 - τ * a)) (M.ybar0 * Real.exp (τ * cb)) 1
        (M.ybar0 * Real.exp (τ * yb))) s)
      (dURprod (linearOf M) a c y cb yb - (M.θ - 1) / M.θ * (a / 2)) 0 := by
  have e : (fun τ => ∑' s, M.β ^ s * twoRegime
      (periodWelfare 0 M.κ (M.ybar0 * Real.exp (τ * c)) 1 (M.ybar0 * Real.exp (τ * y)))
      (periodWelfare 0 (M.κ * (1 - τ * a)) (M.ybar0 * Real.exp (τ * cb)) 1
        (M.ybar0 * Real.exp (τ * yb))) s) = fun τ =>
      periodWelfare 0 (M.κ * (1 - τ * 0)) (M.ybar0 * Real.exp (τ * c)) (1 * Real.exp (τ * 0))
        (M.ybar0 * Real.exp (τ * y)) + M.β / (1 - M.β) *
      periodWelfare 0 (M.κ * (1 - τ * a)) (M.ybar0 * Real.exp (τ * cb)) (1 * Real.exp (τ * 0))
        (M.ybar0 * Real.exp (τ * yb)) := by
    funext τ
    rw [(hasSum_twoRegime M.hβ0.le M.hβ1 _ _).tsum_eq]
    simp
  rw [e]
  have h1 := hasDerivAt_periodWelfare 0 M.κ 0 M.ybar0 c 0 y M.ybar0_pos one_pos
  have h2 := (hasDerivAt_periodWelfare 0 M.κ a M.ybar0 cb 0 yb M.ybar0_pos one_pos).const_mul
    (M.β / (1 - M.β))
  convert h1.add h2 using 1
  unfold dURprod dUR linearOf
  simp only
  rw [beta_div_one_sub M, M.κ_mul_ybar0_sq]
  ring

/-- **Government spending under flexible prices** (T26; O&R p. 703, "a rise in Home government
spending would lower Home welfare … but raise welfare abroad"): in the long-run system with
`b̄ = 0` and a permanent rise `ḡ` in Home spending only, the per-period real-utility changes are
`c̄ − ((θ−1)/θ)ȳ = −ḡ(1 − n/(2θ)) < 0` for Home and `nḡ/(2θ) > 0` for Foreign; Home
consumption falls and output rises, Foreign consumption rises and output is unchanged. -/
theorem gov_flex_welfare {L : ReduxLinear} {m ms gb : ℝ} {v : SteadyVars}
    (h : FiscalSteadyLinear L 0 m ms 0 0 gb 0 v) :
    v.c - (L.θ - 1) / L.θ * v.y = -(gb * (1 - L.n / (2 * L.θ))) ∧
    v.cs - (L.θ - 1) / L.θ * v.ys = L.n * gb / (2 * L.θ) ∧
    (0 < gb → v.c < 0 ∧ 0 < v.y ∧ 0 < v.cs ∧ v.ys = 0) := by
  have hv := (fiscalSteadyLinear_iff L 0 m ms 0 0 gb 0 v).1 h
  subst hv
  have hθ := L.hθ
  have hn0 := L.hn0
  have hn1 := L.hn1
  have hθ0 : L.θ ≠ 0 := by linarith
  have hn : 1 - L.n ≠ 0 := by linarith
  have hc : (fiscalSteadySolution L 0 m ms 0 0 gb 0).c =
      -(gb * (L.n + (1 - L.n) * (L.θ + 1) / L.θ) / 2) := by
    simp only [fiscalSteadySolution, fiscalToT, wavg]; field_simp; ring
  have hy : (fiscalSteadySolution L 0 m ms 0 0 gb 0).y = gb / 2 := by
    simp only [fiscalSteadySolution, fiscalToT, wavg]; field_simp; ring
  have hcs : (fiscalSteadySolution L 0 m ms 0 0 gb 0).cs = L.n * gb / (2 * L.θ) := by
    simp only [fiscalSteadySolution, fiscalToT, wavg]; field_simp; ring
  have hys : (fiscalSteadySolution L 0 m ms 0 0 gb 0).ys = 0 := by
    simp only [fiscalSteadySolution, fiscalToT, wavg]; field_simp; ring
  have hθp : 0 < L.θ := by linarith
  refine ⟨?_, ?_, fun hg => ⟨?_, by rw [hy]; positivity, by rw [hcs]; positivity, hys⟩⟩
  · rw [hc, hy]; field_simp; ring
  · rw [hcs, hys]; ring
  · rw [hc]
    have : 0 < 1 - L.n := by linarith
    have : 0 < gb * (L.n + (1 - L.n) * (L.θ + 1) / L.θ) / 2 := by positivity
    linarith

/-- **Temporary government spending with sticky prices** (T26; O&R p. 706): a temporary rise `g`
in Home spending (no future spending, no money or productivity shock) changes real utility by
`dUᴿ_Home = −g(1 − n/θ) < 0` and `dUᴿ_Foreign = ng/θ > 0`; world welfare falls,
`n dUᴿ_Home + (1−n) dUᴿ_Foreign = ng(1/θ − 1) < 0`. -/
theorem gov_temporary_welfare {L : ReduxLinear} {g : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : FiscalShockEqm L 0 0 g 0 0 0 0 0 u v) :
    dUR L u.c u.y v.c v.y = -(g * (1 - L.n / L.θ)) ∧ dUR L u.cs u.ys v.cs v.ys = L.n * g / L.θ ∧
    L.n * dUR L u.c u.y v.c v.y + (1 - L.n) * dUR L u.cs u.ys v.cs v.ys =
      L.n * g * (1 / L.θ - 1) := by
  obtain ⟨rfl, rfl⟩ := (fiscalShock_iff L 0 0 g 0 0 0 0 0 u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ.ne'
  have hθ0 : L.θ ≠ 0 := by linarith
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [dUR, fiscalShortRunSolution, fiscalSteadySolution, fiscalE, fiscalToT, wavg,
      ReduxLinear.D] <;> field_simp <;> ring

/-- **Future government spending with sticky prices** (T26; O&R pp. 704–706): a rise `ḡ` in Home
spending from date 2 on (announced at date 1, no current spending) changes real utility by
`dUᴿ_Home = −(ḡ/δ)(1 − n/(2θ))` and `dUᴿ_Foreign = nḡ/(2θδ)`: exactly the flexible-price
per-period effects summed over dates `≥ 2`; every date-1 effect cancels. -/
theorem gov_future_welfare {L : ReduxLinear} {gb : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : FiscalShockEqm L 0 0 0 0 0 0 gb 0 u v) :
    dUR L u.c u.y v.c v.y = -(gb / L.δ * (1 - L.n / (2 * L.θ))) ∧
    dUR L u.cs u.ys v.cs v.ys = L.n * gb / (2 * L.θ * L.δ) := by
  obtain ⟨rfl, rfl⟩ := (fiscalShock_iff L 0 0 0 0 0 0 gb 0 u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ.ne'
  have hθ0 : L.θ ≠ 0 := by linarith
  have hθ1 : L.θ + 1 ≠ 0 := by linarith
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  refine ⟨?_, ?_⟩ <;>
    simp only [dUR, fiscalShortRunSolution, fiscalSteadySolution, fiscalE, fiscalToT, wavg,
      ReduxLinear.D] <;> field_simp <;> ring

/-- **Permanent government spending with sticky prices** (T26; O&R p. 706, "overall Foreign
benefits and Home loses when Home's government spends more"): a permanent rise `g = ḡ` in Home
spending changes real utility by the sum of the temporary and future effects,
`dUᴿ_Home = −g(1 − n/θ) − (g/δ)(1 − n/(2θ)) < 0` and `dUᴿ_Foreign = ng/θ + ng/(2θδ) > 0`. -/
theorem gov_permanent_welfare {L : ReduxLinear} {g : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : FiscalShockEqm L 0 0 g 0 0 0 g 0 u v) (hg : 0 < g) :
    dUR L u.c u.y v.c v.y = -(g * (1 - L.n / L.θ)) - g / L.δ * (1 - L.n / (2 * L.θ)) ∧
    dUR L u.cs u.ys v.cs v.ys = L.n * g / L.θ + L.n * g / (2 * L.θ * L.δ) ∧
    dUR L u.c u.y v.c v.y < 0 ∧ 0 < dUR L u.cs u.ys v.cs v.ys := by
  obtain ⟨rfl, rfl⟩ := (fiscalShock_iff L 0 0 g 0 0 0 g 0 u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hn0 := L.hn0
  have hn1 := L.hn1
  have hθ0 : L.θ ≠ 0 := by linarith
  have hθ1 : L.θ + 1 ≠ 0 := by linarith
  have hn : 1 - L.n ≠ 0 := by linarith
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  have e1 : dUR L (fiscalShortRunSolution L 0 0 g 0 0 0 g 0).c
      (fiscalShortRunSolution L 0 0 g 0 0 0 g 0).y
      (fiscalSteadySolution L (fiscalShortRunSolution L 0 0 g 0 0 0 g 0).b 0 0 0 0 g 0).c
      (fiscalSteadySolution L (fiscalShortRunSolution L 0 0 g 0 0 0 g 0).b 0 0 0 0 g 0).y =
      -(g * (1 - L.n / L.θ)) - g / L.δ * (1 - L.n / (2 * L.θ)) := by
    simp only [dUR, fiscalShortRunSolution, fiscalSteadySolution, fiscalE, fiscalToT, wavg,
      ReduxLinear.D]
    field_simp; ring
  have e2 : dUR L (fiscalShortRunSolution L 0 0 g 0 0 0 g 0).cs
      (fiscalShortRunSolution L 0 0 g 0 0 0 g 0).ys
      (fiscalSteadySolution L (fiscalShortRunSolution L 0 0 g 0 0 0 g 0).b 0 0 0 0 g 0).cs
      (fiscalSteadySolution L (fiscalShortRunSolution L 0 0 g 0 0 0 g 0).b 0 0 0 0 g 0).ys =
      L.n * g / L.θ + L.n * g / (2 * L.θ * L.δ) := by
    simp only [dUR, fiscalShortRunSolution, fiscalSteadySolution, fiscalE, fiscalToT, wavg,
      ReduxLinear.D]
    field_simp; ring
  have hθp : 0 < L.θ := by linarith
  refine ⟨e1, e2, ?_, ?_⟩
  · rw [e1]
    have h1 : 0 < 1 - L.n / L.θ := by rw [sub_pos, div_lt_one hθp]; linarith
    have h2 : 0 < 1 - L.n / (2 * L.θ) := by rw [sub_pos, div_lt_one (by positivity)]; linarith
    have : 0 < g * (1 - L.n / L.θ) := mul_pos hg h1
    have : 0 < g / L.δ * (1 - L.n / (2 * L.θ)) := by positivity
    linarith
  · rw [e2]; positivity

end ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity
