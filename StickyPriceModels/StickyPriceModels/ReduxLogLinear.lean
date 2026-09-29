/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceModels.ReduxPrimitives
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The redux model: the log-linear system

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.1.5–§10.1.6
(pp. 669–673) and the short-run current account of §10.1.7.2–§10.1.7.3 (pp. 675–677).

**Log-linearisation as differentiation (T10).** Each of the book's linear equations is the
derivative, at the symmetric steady state, of the corresponding exact equation written in
the logarithms of the variables. We state each one as a `HasDerivAt` along an arbitrary
direction of log-deviations (a directional derivative in every direction, i.e. the full
linearisation): the price indexes (27)–(28) (`hasDerivAt_log_bloc`), PPP (29), world demand
(30)–(31), world consumption (32), the labour–leisure conditions (33)–(34) (exactly linear in
logs), the Euler equations (35)–(36), money demand (37)–(38), (39), and the steady-state budgets
(40)–(41) (with `b̄ = dB̄/Cᵂ₀` a LEVEL change, since `B̄₀ = 0`).

**The steady-state linear system solved exactly (T11).** The long-run system (27)–(34), (40),
(41), (50), (51) has exactly one solution for every `b̄, m̄, m̄*`, namely (45)–(52) together with
the output levels `ȳ = −δb̄/2`, `ȳ* = nδb̄/(2(1−n))` (not given in the book) and the individual
prices (`steadyLinear_iff`). The wealth effect on relative consumption is dampened,
`(1+θ)/(2θ) < 1`, exactly when `θ > 1` (p. 672).

**The short-run current account (T12).** With preset prices, (27)–(28) give `p = (1−n)e` and
`p* = −ne`; (55) and (56) are derivatives of (54); `b̄ − b̄* = b̄/(1−n)`; and (57) holds EXACTLY
in the nonlinear model because both countries face the same real rate
(`consumption_ratio_exact`).
-/

namespace ObstfeldRogoff.StickyPriceModels.ReduxLogLinear

open Real Filter Topology ReduxPrimitives

/-! ## Log-linearisation of the price indexes (27)–(29) -/

/-- The derivative of `τ ↦ (A e^{τα})^{1−θ}` at `0` (used for (27)–(28)). -/
theorem hasDerivAt_rpow_exp {A α θ : ℝ} (hA : 0 < A) :
    HasDerivAt (fun τ => (A * Real.exp (τ * α)) ^ (1 - θ)) (A ^ (1 - θ) * ((1 - θ) * α)) 0 := by
  have e : (fun τ => (A * Real.exp (τ * α)) ^ (1 - θ)) =
      fun τ => A ^ (1 - θ) * Real.exp (τ * ((1 - θ) * α)) := by
    funext τ
    rw [mul_rpow hA.le (Real.exp_pos _).le, ← Real.exp_mul]
    ring_nf
  rw [e]
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const ((1 - θ) * α)).exp.const_mul (A ^ (1 - θ))
  simpa using h

/-- **Log-linearising a two-bloc CES price index** (O&R (27)–(28), p. 669; T10): if the two bloc
prices are equal at the base point, `A e^{τα}` and `A e^{τβ}`, then
`d/dτ log [n a^{1−θ} + (1−n) b^{1−θ}]^{1/(1−θ)}` at `τ = 0` is `n α + (1−n) β`. -/
theorem hasDerivAt_log_bloc {θ n A α β : ℝ} (hθ : θ ≠ 1) (hn0 : 0 < n) (hn1 : n < 1)
    (hA : 0 < A) :
    HasDerivAt (fun τ => Real.log (blocPriceIndex θ n (A * Real.exp (τ * α))
      (A * Real.exp (τ * β)))) (n * α + (1 - n) * β) 0 := by
  have hθ' : 1 - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  set S : ℝ → ℝ := fun τ => n * (A * Real.exp (τ * α)) ^ (1 - θ) +
    (1 - n) * (A * Real.exp (τ * β)) ^ (1 - θ) with hS
  have hSpos : ∀ τ, 0 < S τ := fun τ => by
    have h1 := rpow_pos_of_pos (mul_pos hA (Real.exp_pos (τ * α))) (1 - θ)
    have h2 := rpow_pos_of_pos (mul_pos hA (Real.exp_pos (τ * β))) (1 - θ)
    have : 0 < 1 - n := by linarith
    simp only [hS]; positivity
  have e : (fun τ => Real.log (blocPriceIndex θ n (A * Real.exp (τ * α))
      (A * Real.exp (τ * β)))) = fun τ => 1 / (1 - θ) * Real.log (S τ) := by
    funext τ
    unfold blocPriceIndex
    rw [Real.log_rpow (hSpos τ)]
  rw [e]
  have hSd : HasDerivAt S (n * (A ^ (1 - θ) * ((1 - θ) * α)) +
      (1 - n) * (A ^ (1 - θ) * ((1 - θ) * β))) 0 :=
    ((hasDerivAt_rpow_exp (θ := θ) (α := α) hA).const_mul n).add
      ((hasDerivAt_rpow_exp (θ := θ) (α := β) hA).const_mul (1 - n))
  have hS0 : S 0 = A ^ (1 - θ) := by
    simp only [hS, zero_mul, Real.exp_zero, mul_one]; ring
  have hlog := (hSd.log (by rw [hS0]; exact (rpow_pos_of_pos hA _).ne')).const_mul (1 / (1 - θ))
  convert hlog using 1
  rw [hS0]
  have := (rpow_pos_of_pos hA (1 - θ)).ne'
  field_simp

/-- **(27)**, O&R p. 669 (T10): around `p̄₀(h) = 𝓔₀ p̄₀*(f)`, with log-deviations `a` of `p(h)`,
`e` of `𝓔` and `b` of `p*(f)`, the Home price index moves by `p = n a + (1−n)(e + b)`. -/
theorem linearise_27 {θ n ph0 E0 pfs0 a e b : ℝ} (hθ : θ ≠ 1) (hn0 : 0 < n) (hn1 : n < 1)
    (hph0 : 0 < ph0) (hbase : ph0 = E0 * pfs0) :
    HasDerivAt (fun τ => Real.log (blocPriceIndex θ n (ph0 * Real.exp (τ * a))
      ((E0 * Real.exp (τ * e)) * (pfs0 * Real.exp (τ * b)))))
      (n * a + (1 - n) * (e + b)) 0 := by
  have h := hasDerivAt_log_bloc (α := a) (β := e + b) hθ hn0 hn1 hph0
  convert h using 3 with τ
  rw [hbase, mul_add, Real.exp_add]
  ring_nf

/-- **(28)**, O&R p. 669 (T10): the Foreign price index moves by `p* = n(a − e) + (1−n) b`. -/
theorem linearise_28 {θ n ph0 E0 pfs0 a e b : ℝ} (hθ : θ ≠ 1) (hn0 : 0 < n) (hn1 : n < 1)
    (hpfs0 : 0 < pfs0) (hE0 : 0 < E0) (hbase : ph0 = E0 * pfs0) :
    HasDerivAt (fun τ => Real.log (blocPriceIndex θ n
      ((ph0 * Real.exp (τ * a)) / (E0 * Real.exp (τ * e))) (pfs0 * Real.exp (τ * b))))
      (n * (a - e) + (1 - n) * b) 0 := by
  have h := hasDerivAt_log_bloc (α := a - e) (β := b) hθ hn0 hn1 hpfs0
  convert h using 3 with τ
  rw [hbase, mul_sub, Real.exp_sub]
  have := (Real.exp_pos (τ * e)).ne'
  have := hE0.ne'
  field_simp

/-- **(29) requires no approximation**, O&R p. 670: PPP (7) holds exactly, so in logs
`log P − log P* = log 𝓔` at every point; hence `e = p − p*` for deviations. -/
theorem ppp_log_exact {θ n ph pfs E : ℝ} (hθ : θ ≠ 1) (hn0 : 0 < n) (hn1 : n < 1)
    (hph : 0 < ph) (hpfs : 0 < pfs) (hE : 0 < E) :
    Real.log (blocPriceIndex θ n ph (E * pfs)) - Real.log (blocPriceIndex θ n (ph / E) pfs) =
      Real.log E := by
  rw [bloc_ppp hθ hn0 hn1 hph hpfs hE, Real.log_mul hE.ne'
    (blocPriceIndex_pos hn0 hn1 (div_pos hph hE) hpfs).ne']
  ring

/-- The linear PPP identity (29) follows from the linear (27) and (28) (O&R p. 670). -/
theorem eq29_of_27_28 {n p ps ph pf e : ℝ} (h27 : p = n * ph + (1 - n) * (e + pf))
    (h28 : ps = n * (ph - e) + (1 - n) * pf) : e = p - ps := by
  rw [h27, h28]; ring

/-! ## Demand, world aggregates and labour supply (30)–(34) -/

/-- **(30)–(31) are exact in logs**, O&R p. 670 (T10): world demand (10) gives
`log y = −θ(log p(h) − log P) + log Cᵂ` at every point, so `y = θ(p − p(h)) + cᵂ` for
deviations. -/
theorem log_demand_exact {θ ph P X : ℝ} (hph : 0 < ph) (hP : 0 < P) (hX : 0 < X) :
    Real.log (cesDemand θ ph P X) = -θ * (Real.log ph - Real.log P) + Real.log X := by
  unfold cesDemand
  rw [Real.log_mul (rpow_pos_of_pos (div_pos hph hP) _).ne' hX.ne',
    Real.log_rpow (div_pos hph hP), Real.log_div hph.ne' hP.ne']

/-- **World consumption (32)** (the linearisation of (11)), O&R p. 670 (T10): around
`C̄ = C̄* = C₀`, `d log(nC + (1−n)C*) = n c + (1−n) c*`. -/
theorem linearise_world {n C0 c cs : ℝ} (hC0 : 0 < C0) :
    HasDerivAt (fun τ => Real.log (worldConsumption n (C0 * Real.exp (τ * c))
      (C0 * Real.exp (τ * cs)))) (n * c + (1 - n) * cs) 0 := by
  unfold worldConsumption
  have h1 : HasDerivAt (fun τ => C0 * Real.exp (τ * c)) (C0 * c) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).exp.const_mul C0
  have h2 : HasDerivAt (fun τ => C0 * Real.exp (τ * cs)) (C0 * cs) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const cs).exp.const_mul C0
  have hsum : n * (C0 * Real.exp (0 * c)) + (1 - n) * (C0 * Real.exp (0 * cs)) = C0 := by
    simp only [zero_mul, Real.exp_zero, mul_one]; ring
  have h := ((h1.const_mul n).add (h2.const_mul (1 - n))).log
    (by simp only [Pi.add_apply]; rw [hsum]; exact hC0.ne')
  convert h using 1
  simp
  field_simp
  ring

/-- **(32) from (27), (28), (30), (31)**, O&R p. 670: the population-weighted sum of the demand
equations gives `cᵂ = yᵂ` because `n p(h) + (1−n)p*(f) = n p + (1−n) p*`. -/
theorem eq32_of_demands {n θ p ps ph pf e y ys cW : ℝ} (h27 : p = n * ph + (1 - n) * (e + pf))
    (h28 : ps = n * (ph - e) + (1 - n) * pf) (h30 : y = θ * (p - ph) + cW)
    (h31 : ys = θ * (ps - pf) + cW) : n * y + (1 - n) * ys = cW := by
  rw [h30, h31, h27, h28]; ring

/-- **(33)–(34) are exact in logs**, O&R p. 670 (T10): if the labour–leisure condition (15)
`y^{(θ+1)/θ} = K (Cᵂ)^{1/θ}/C` holds at a base point and at a new point, then the log
changes satisfy `(θ+1) Δlog y = −θ Δlog C + Δlog Cᵂ` exactly. -/
theorem labour_log_exact {θ K y0 y1 C0 C1 X0 X1 : ℝ} (hθ : θ ≠ 0) (hK : 0 < K)
    (hy0 : 0 < y0) (hy1 : 0 < y1) (hC0 : 0 < C0) (hC1 : 0 < C1) (hX0 : 0 < X0) (hX1 : 0 < X1)
    (h0 : y0 ^ ((θ + 1) / θ) = K * X0 ^ (1 / θ) / C0)
    (h1 : y1 ^ ((θ + 1) / θ) = K * X1 ^ (1 / θ) / C1) :
    (θ + 1) * (Real.log y1 - Real.log y0) =
      -θ * (Real.log C1 - Real.log C0) + (Real.log X1 - Real.log X0) := by
  have l0 := congrArg Real.log h0
  have l1 := congrArg Real.log h1
  rw [Real.log_rpow hy0, Real.log_div (mul_pos hK (rpow_pos_of_pos hX0 _)).ne' hC0.ne',
    Real.log_mul hK.ne' (rpow_pos_of_pos hX0 _).ne', Real.log_rpow hX0] at l0
  rw [Real.log_rpow hy1, Real.log_div (mul_pos hK (rpow_pos_of_pos hX1 _)).ne' hC1.ne',
    Real.log_mul hK.ne' (rpow_pos_of_pos hX1 _).ne', Real.log_rpow hX1] at l1
  have e := congrArg (fun z => θ * z) (show (θ + 1) / θ * Real.log y1 - (θ + 1) / θ *
    Real.log y0 = 1 / θ * Real.log X1 - Real.log C1 - (1 / θ * Real.log X0 - Real.log C0) by
      linarith)
  field_simp at e
  linarith

/-! ## The Euler equation (35)–(36) and money demand (37)–(39) -/

/-- **(35)–(36)**, O&R p. 670 (T10): with `C_{t+1}/C_t = β(1 + r_{t+1})` and `β(1+δ) = 1`, the
log growth of consumption at `r = δ(1 + τ r̂)` has derivative `δ r̂/(1 + δ)` at `τ = 0`
(`r̂ = dr/r̄`, `r̄ = δ`), and is `0` at the steady state. -/
theorem linearise_35 {β δ rh : ℝ} (hδ : 0 < δ) (hβ : β * (1 + δ) = 1) :
    HasDerivAt (fun τ => Real.log (β * (1 + δ * (1 + τ * rh)))) (δ * rh / (1 + δ)) 0 ∧
      Real.log (β * (1 + δ * (1 + 0 * rh))) = 0 := by
  constructor
  · have h1 : HasDerivAt (fun τ => β * (1 + δ * (1 + τ * rh))) (β * (δ * rh)) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).mul_const rh).const_add 1).const_mul δ
      simpa using (this.const_add 1).const_mul β
    have h0 : β * (1 + δ * (1 + 0 * rh)) = 1 := by rw [zero_mul, add_zero, mul_one, hβ]
    have h2 := h1.log (by rw [h0]; norm_num)
    convert h2 using 1
    simp only [zero_mul, add_zero, mul_one]
    rw [hβ]
    have : (1 + δ) ≠ 0 := by linarith
    field_simp
    have hb : β = 1 / (1 + δ) := by field_simp; linarith
    rw [hb]
    field_simp
  · simp [hβ]

/-- **(37)–(38)**, O&R p. 670 (T10): write money demand (14) as
`log(M/P) = log χ + log C + log((1+i)/i)` with `1 + i_{t+1} = (P_{t+1}/P_t)(1 + r_{t+1})`.
Around `P_{t+1} = P_t`, `r = δ` (so `i = δ`), along `P_{t+1}/P_t = e^{τ Δp}`,
`r = δ(1 + τ r̂)`, the term `log((1+i)/i)` has derivative `−r̂/(1+δ) − Δp/δ`. -/
theorem linearise_37 {δ dp rh : ℝ} (hδ : 0 < δ) :
    HasDerivAt (fun τ => Real.log ((Real.exp (τ * dp) * (1 + δ * (1 + τ * rh))) /
      (Real.exp (τ * dp) * (1 + δ * (1 + τ * rh)) - 1)))
      (-(rh / (1 + δ)) - dp / δ) 0 := by
  set g : ℝ → ℝ := fun τ => Real.exp (τ * dp) * (1 + δ * (1 + τ * rh)) with hg
  have hgd : HasDerivAt g (dp * (1 + δ) + δ * rh) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const dp).exp
    have h2 : HasDerivAt (fun τ => 1 + δ * (1 + τ * rh)) (δ * rh) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).mul_const rh).const_add 1).const_mul δ
      simpa using this.const_add 1
    have h3 := h1.mul h2
    have e : g = (fun x => Real.exp (id x * dp)) * (fun τ => 1 + δ * (1 + τ * rh)) := by
      funext τ; simp [hg]
    rw [e]
    convert h3 using 1
    simp
  have hg0 : g 0 = 1 + δ := by simp [hg]
  have hnum := hgd.log (by rw [hg0]; linarith)
  have hden := (hgd.sub_const 1).log (by rw [hg0]; simp; linarith)
  have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), 1 < g τ :=
    hgd.continuousAt.eventually (lt_mem_nhds (by rw [hg0]; linarith))
  have hsum := hnum.sub hden
  have hcongr : (fun τ => Real.log (g τ / (g τ - 1))) =ᶠ[𝓝 0]
      fun τ => Real.log (g τ) - Real.log (g τ - 1) := by
    filter_upwards [hev] with τ hτ
    rw [Real.log_div (by linarith) (by linarith)]
  have hfin := hsum.congr_of_eventuallyEq hcongr
  convert hfin using 1
  rw [hg0]
  simp only [add_sub_cancel_left]
  have : (1 + δ) ≠ 0 := by linarith
  have := hδ.ne'
  field_simp
  ring

/-- **(39) = (37) − (38) with (29)**, O&R p. 671. -/
theorem eq39_of_37_38 {δ m ms p ps p1 ps1 c cs r e e1 : ℝ}
    (h37 : m - p = c - r / (1 + δ) - (p1 - p) / δ)
    (h38 : ms - ps = cs - r / (1 + δ) - (ps1 - ps) / δ)
    (h29 : e = p - ps) (h29' : e1 = p1 - ps1) :
    m - ms - e = c - cs - (e1 - e) / δ := by
  rw [h29, h29']
  have : (p1 - ps1 - (p - ps)) / δ = (p1 - p) / δ - (ps1 - ps) / δ := by ring
  rw [this]
  linarith

/-! ## The steady-state budgets (40)–(41) -/

/-- **(40)**, O&R p. 671 (T10): steady-state income = expenditure (20), `C = δB + π y`, around
`B̄₀ = 0`, `π̄₀ = 1`, `ȳ₀ = C̄₀`: along `B = τ b̄ C̄₀` (a LEVEL change, since `B̄₀ = 0`),
`π = e^{τ u}` (`u = p̄(h) − p̄`) and `y = C̄₀ e^{τ ŷ}`, `d log C = δ b̄ + u + ŷ`. -/
theorem linearise_40 {δ b u yh C0 : ℝ} (hC0 : 0 < C0) :
    HasDerivAt (fun τ => Real.log (δ * (τ * b * C0) + Real.exp (τ * u) * (C0 * Real.exp (τ * yh))))
      (δ * b + u + yh) 0 := by
  have h1 : HasDerivAt (fun τ => δ * (τ * b * C0)) (δ * (b * C0)) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const b).mul_const C0
    simpa using this.const_mul δ
  have h2 : HasDerivAt (fun τ => Real.exp (τ * u)) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u).exp
  have h3 : HasDerivAt (fun τ => C0 * Real.exp (τ * yh)) (C0 * yh) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const yh).exp.const_mul C0
  have h4 := h1.add (h2.mul h3)
  have hval : δ * (0 * b * C0) + Real.exp (0 * u) * (C0 * Real.exp (0 * yh)) = C0 := by simp
  have h5 := h4.log (by simp only [Pi.add_apply, Pi.mul_apply]; rw [hval]; exact hC0.ne')
  have e : (fun τ => Real.log (δ * (τ * b * C0) + Real.exp (τ * u) * (C0 * Real.exp (τ * yh)))) =
      fun τ => Real.log ((fun τ => δ * (τ * b * C0)) τ +
        ((fun τ => Real.exp (τ * u)) * fun τ => C0 * Real.exp (τ * yh)) τ) := by
    funext τ; simp
  rw [e]
  convert h5 using 1
  simp only [Pi.add_apply, Pi.mul_apply]
  rw [hval]
  simp only [zero_mul, Real.exp_zero, one_mul]
  field_simp
  ring

/-- **(41)**, O&R p. 671 (T10): Foreign's steady-state budget (21), `C* = −(n/(1−n))δB + π* y*`,
linearises to `c̄* = −(n/(1−n))δ b̄ + p̄*(f) + ȳ* − p̄*`. -/
theorem linearise_41 {n δ b u yh C0 : ℝ} (hC0 : 0 < C0) :
    HasDerivAt (fun τ => Real.log (-(n / (1 - n)) * δ * (τ * b * C0) +
      Real.exp (τ * u) * (C0 * Real.exp (τ * yh))))
      (-(n / (1 - n)) * δ * b + u + yh) 0 := by
  have h := linearise_40 (δ := -(n / (1 - n)) * δ) (b := b) (u := u) (yh := yh) hC0
  convert h using 2 with τ

/-! ## The steady-state linear system (42)–(52) (T11) -/

/-- The unknowns of the long-run linear system, O&R §10.1.6 (pp. 671–673): log changes of
consumption `c̄, c̄*`, output `ȳ, ȳ*`, prices `p̄(h), p̄*(f), p̄, p̄*`, the exchange rate `ē`
and world consumption `c̄ᵂ`. -/
structure SteadyVars where
  c : ℝ
  cs : ℝ
  y : ℝ
  ys : ℝ
  ph : ℝ
  pf : ℝ
  p : ℝ
  ps : ℝ
  e : ℝ
  cW : ℝ

/-- **The long-run linear system**, O&R p. 671: barred (27), (28), (30), (31), (11)/(32), (33),
(34), the budgets (40), (41) and the long-run money demands (50), (51) (steady-state (37)–(38)
with constant prices, `m̄ − p̄ = c̄`), for given `b̄`, `m̄`, `m̄*`. -/
structure SteadyLinear (L : ReduxLinear) (b m ms : ℝ) (v : SteadyVars) : Prop where
  eq27 : v.p = L.n * v.ph + (1 - L.n) * (v.e + v.pf)
  eq28 : v.ps = L.n * (v.ph - v.e) + (1 - L.n) * v.pf
  eq30 : v.y = L.θ * (v.p - v.ph) + v.cW
  eq31 : v.ys = L.θ * (v.ps - v.pf) + v.cW
  eq32 : v.cW = L.n * v.c + (1 - L.n) * v.cs
  eq33 : (L.θ + 1) * v.y = -L.θ * v.c + v.cW
  eq34 : (L.θ + 1) * v.ys = -L.θ * v.cs + v.cW
  eq40 : v.c = L.δ * b + v.ph + v.y - v.p
  eq41 : v.cs = -(L.n / (1 - L.n)) * L.δ * b + v.pf + v.ys - v.ps
  eq50 : v.p = m - v.c
  eq51 : v.ps = ms - v.cs

/-- The closed-form long-run solution, O&R (45)–(52), p. 672–673, with the output levels
`ȳ = −δb̄/2`, `ȳ* = nδb̄/(2(1−n))` and the individual goods prices. -/
noncomputable def steadySolution (L : ReduxLinear) (b m ms : ℝ) : SteadyVars where
  c := (1 + L.θ) * L.δ * b / (2 * L.θ)
  cs := -(L.n / (1 - L.n)) * ((1 + L.θ) * L.δ * b / (2 * L.θ))
  y := -(L.δ * b) / 2
  ys := L.n * L.δ * b / (2 * (1 - L.n))
  p := m - (1 + L.θ) * L.δ * b / (2 * L.θ)
  ps := ms + (L.n / (1 - L.n)) * ((1 + L.θ) * L.δ * b / (2 * L.θ))
  e := m - ms - (1 + L.θ) * L.δ * b / (2 * L.θ * (1 - L.n))
  ph := m - (1 + L.θ) * L.δ * b / (2 * L.θ) + L.δ * b / (2 * L.θ)
  pf := ms + (L.n / (1 - L.n)) * ((1 + L.θ) * L.δ * b / (2 * L.θ)) -
    L.n * L.δ * b / (2 * L.θ * (1 - L.n))
  cW := 0

/-- **The long-run linear system has exactly one solution** (T11; O&R (42)–(52),
pp. 672–673): `SteadyLinear` holds IF AND ONLY IF the unknowns equal `steadySolution`. -/
theorem steadyLinear_iff (L : ReduxLinear) (b m ms : ℝ) (v : SteadyVars) :
    SteadyLinear L b m ms v ↔ v = steadySolution L b m ms := by
  have hθ : L.θ ≠ 0 := by linarith [L.hθ]
  have hθ1 : L.θ + 1 ≠ 0 := by linarith [L.hθ]
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  constructor
  · intro h
    obtain ⟨h27, h28, h30, h31, h32, h33, h34, h40, h41, h50, h51⟩ := h
    rcases v with ⟨c, cs, y, ys, ph, pf, p, ps, e, cW⟩
    simp only at h27 h28 h30 h31 h32 h33 h34 h40 h41 h50 h51
    -- world aggregates (47)
    have s1 : p - ps = e := by linear_combination h27 - h28
    have s3 : L.n * y + (1 - L.n) * ys = cW := by
      have := eq32_of_demands h27 h28 h30 h31; linarith
    have s4 : cW = 0 := by
      have h2 : 2 * L.θ * cW = 0 := by
        linear_combination L.n * h33 + (1 - L.n) * h34 - (L.θ + 1) * s3 + L.θ * h32
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd h (mul_ne_zero two_ne_zero hθ)
      · exact h
    subst s4
    -- differences (42)–(45)
    have s6 : y - ys = -L.θ * (ph - e - pf) := by linear_combination h30 - h31 + L.θ * s1
    have h41' : (1 - L.n) * cs = -(L.n * L.δ * b) + (1 - L.n) * (pf + ys - ps) := by
      rw [h41]; field_simp; ring
    have s7 : (1 - L.n) * (c - cs) = L.δ * b + (1 - L.n) * ((ph - e - pf) + (y - ys)) := by
      linear_combination (1 - L.n) * h40 - h41' - (1 - L.n) * s1
    have s8 : (L.θ + 1) * (ph - e - pf) = c - cs := by
      have h2 : L.θ * ((L.θ + 1) * (ph - e - pf) - (c - cs)) = 0 := by
        linear_combination h34 - h33 + (L.θ + 1) * s6
      have := (mul_eq_zero.1 h2).resolve_left hθ
      linarith
    have s9 : c - cs = (1 + L.θ) * L.δ * b / (2 * L.θ * (1 - L.n)) := by
      have h2 : 2 * L.θ * (1 - L.n) * (c - cs) = (1 + L.θ) * L.δ * b := by
        linear_combination (L.θ + 1) * s7 + (1 - L.n) * (1 - L.θ) * s8 +
          (1 - L.n) * (L.θ + 1) * s6
      field_simp
      linarith
    -- levels (48)–(49)
    have hc : c = (1 + L.θ) * L.δ * b / (2 * L.θ) := by
      have : c = (1 - L.n) * (c - cs) := by linear_combination -h32
      rw [this, s9]; field_simp
    have hcs : cs = -(L.n / (1 - L.n)) * ((1 + L.θ) * L.δ * b / (2 * L.θ)) := by
      have : cs = c - (c - cs) := by ring
      rw [this, s9, hc]; field_simp; ring
    have hy : y = -(L.δ * b) / 2 := by
      have : y = -L.θ * c / (L.θ + 1) := by field_simp; linarith
      rw [this, hc]; field_simp; ring
    have hys : ys = L.n * L.δ * b / (2 * (1 - L.n)) := by
      have : ys = -L.θ * cs / (L.θ + 1) := by field_simp; linarith
      rw [this, hcs]; field_simp; ring
    have hT : ph - e - pf = L.δ * b / (2 * L.θ * (1 - L.n)) := by
      have : ph - e - pf = (c - cs) / (L.θ + 1) := by field_simp; linarith
      rw [this, s9]; field_simp; ring
    have hp : p = m - (1 + L.θ) * L.δ * b / (2 * L.θ) := by rw [h50, hc]
    have hps : ps = ms + (L.n / (1 - L.n)) * ((1 + L.θ) * L.δ * b / (2 * L.θ)) := by
      rw [h51, hcs]; ring
    have he : e = m - ms - (1 + L.θ) * L.δ * b / (2 * L.θ * (1 - L.n)) := by
      rw [← s1, hp, hps]; field_simp; ring
    have hph : ph = m - (1 + L.θ) * L.δ * b / (2 * L.θ) + L.δ * b / (2 * L.θ) := by
      have : ph = p + (1 - L.n) * (ph - e - pf) := by linear_combination -h27
      rw [this, hp, hT]; field_simp
    have hpf : pf = ms + (L.n / (1 - L.n)) * ((1 + L.θ) * L.δ * b / (2 * L.θ)) -
        L.n * L.δ * b / (2 * L.θ * (1 - L.n)) := by
      have : pf = ps - L.n * (ph - e - pf) := by linear_combination -h28
      rw [this, hps, hT]; ring
    simp only [steadySolution, SteadyVars.mk.injEq]
    exact ⟨hc, hcs, hy, hys, hph, hpf, hp, hps, he, trivial⟩
  · intro h
    subst h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [steadySolution] <;> field_simp <;> ring

/-- **Existence and uniqueness of the long-run linear solution** (T11): for every `b̄, m̄, m̄*`
the system has exactly one solution. -/
theorem steadyLinear_existsUnique (L : ReduxLinear) (b m ms : ℝ) :
    ∃! v, SteadyLinear L b m ms v :=
  ⟨steadySolution L b m ms, (steadyLinear_iff L b m ms _).2 rfl,
    fun v hv => (steadyLinear_iff L b m ms v).1 hv⟩

/-- **(45)–(47), (52) and the output levels**, O&R pp. 672–673 (T11): any solution of the
long-run system has `c̄ − c̄* = (1+θ)δb̄/(2θ(1−n))` (45), `p̄(h) − ē − p̄*(f) = δb̄/(2θ(1−n))`
(46), `ȳᵂ = c̄ᵂ = 0` (47), `ȳ − ȳ* = −δb̄/(2(1−n))`, `ȳ = −δb̄/2`, `ȳ* = nδb̄/(2(1−n))`, and
`ē = m̄ − m̄* − (c̄ − c̄*)` (52). -/
theorem steadyLinear_consequences {L : ReduxLinear} {b m ms : ℝ} {v : SteadyVars}
    (h : SteadyLinear L b m ms v) :
    v.c - v.cs = (1 + L.θ) * L.δ * b / (2 * L.θ * (1 - L.n)) ∧
    v.ph - v.e - v.pf = L.δ * b / (2 * L.θ * (1 - L.n)) ∧
    L.n * v.y + (1 - L.n) * v.ys = 0 ∧ v.cW = 0 ∧
    v.y - v.ys = -(L.δ * b) / (2 * (1 - L.n)) ∧ v.y = -(L.δ * b) / 2 ∧
    v.ys = L.n * L.δ * b / (2 * (1 - L.n)) ∧ v.e = m - ms - (v.c - v.cs) := by
  have hv := (steadyLinear_iff L b m ms v).1 h
  have hθ : L.θ ≠ 0 := by linarith [L.hθ]
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  subst hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [steadySolution] <;> (try field_simp) <;>
    (try ring)

/-- **The wealth effect on relative consumption is dampened exactly when `θ > 1`** (O&R p. 672,
"the impact of wealth transfers on consumption differentials is less (recall `θ > 1`)"): for
`θ > 0`, `(1+θ)/(2θ) < 1 ⟺ θ > 1`. -/
theorem dampening_iff {θ : ℝ} (hθ : 0 < θ) : (1 + θ) / (2 * θ) < 1 ↔ 1 < θ := by
  rw [div_lt_one (by positivity)]
  constructor <;> intro h <;> linarith

/-! ## The short-run current account (54)–(57) (T12) -/

/-- **Short-run price levels with preset prices**, O&R p. 677 (T12): with `p(h) = p*(f) = 0`
in (27)–(28), `p = (1−n)e` and `p* = −ne`. -/
theorem shortRun_prices {n p ps e : ℝ} (h27 : p = n * 0 + (1 - n) * (e + 0))
    (h28 : ps = n * (0 - e) + (1 - n) * 0) : p = (1 - n) * e ∧ ps = -(n * e) := by
  constructor <;> [rw [h27]; rw [h28]] <;> ring

/-- **(55)–(56) as derivatives of (54)**, O&R pp. 675–677 (T10/T12): with `B₁ = 0`, (54) gives
`B₂ = π₁ y₁ − C₁`. Along `π₁ = e^{τu}`, `y₁ = C̄₀e^{τŷ}`, `C₁ = C̄₀e^{τĉ}`, the normalised
level `B₂/C̄₀` has derivative `u + ŷ − ĉ`. With preset prices `u = p(h) − p = −(1−n)e` this is
(55), `b̄ = y − c − (1−n)e`; for Foreign `u = p*(f) − p* = ne` gives (56). -/
theorem linearise_55 {u yh ch C0 : ℝ} (hC0 : 0 < C0) :
    HasDerivAt (fun τ => (Real.exp (τ * u) * (C0 * Real.exp (τ * yh)) -
      C0 * Real.exp (τ * ch)) / C0) (u + yh - ch) 0 := by
  have h2 : HasDerivAt (fun τ => Real.exp (τ * u)) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u).exp
  have h3 : HasDerivAt (fun τ => C0 * Real.exp (τ * yh)) (C0 * yh) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const yh).exp.const_mul C0
  have h4 : HasDerivAt (fun τ => C0 * Real.exp (τ * ch)) (C0 * ch) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ch).exp.const_mul C0
  have h := ((h2.mul h3).sub h4).div_const C0
  convert h using 1
  simp only [zero_mul, Real.exp_zero, one_mul, mul_one]
  field_simp

/-- **(55)–(56) and the per-capita differential** (T12; O&R p. 677 and the p. 688 correction):
if `b̄ = y − c − (1−n)e`, `b̄* = y* − c* + ne` and net foreign assets sum to zero,
`n b̄ + (1−n) b̄* = 0` (17), then `b̄* = −(n/(1−n)) b̄`, `b̄ − b̄* = b̄/(1−n)` and
`b̄/(1−n) = (y − y*) − (c − c*) − e` (62). -/
theorem shortRun_ca {n y ys c cs e b bs : ℝ} (hn1 : n < 1) (h55 : b = y - c - (1 - n) * e)
    (h56 : bs = ys - cs + n * e) (h17 : n * b + (1 - n) * bs = 0) :
    bs = -(n / (1 - n)) * b ∧ b - bs = b / (1 - n) ∧
      b / (1 - n) = (y - ys) - (c - cs) - e := by
  have hn : 1 - n ≠ 0 := by linarith
  have hbs : bs = -(n / (1 - n)) * b := by field_simp; linarith
  refine ⟨hbs, ?_, ?_⟩
  · rw [hbs]; field_simp; ring
  · have : b - bs = (y - ys) - (c - cs) - e := by rw [h55, h56]; ring
    rw [← this, hbs]; field_simp; ring

/-- **(57) holds exactly in the nonlinear model** (T12; O&R p. 677): if both countries' Euler
equations (13) hold at the common real rate, `C₂ = β(1+r)C₁` and `C₂* = β(1+r)C₁*`, then
`C₂/C₂* = C₁/C₁*`; in logs, relative consumption changes are permanent,
`(log C₂ − log C₂*) = (log C₁ − log C₁*)`. -/
theorem consumption_ratio_exact {β r C1 C2 Cs1 Cs2 : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    (hC1 : 0 < C1) (hCs1 : 0 < Cs1) (he : C2 = β * (1 + r) * C1)
    (hes : Cs2 = β * (1 + r) * Cs1) :
    C2 * Cs1 = Cs2 * C1 ∧ Real.log C2 - Real.log Cs2 = Real.log C1 - Real.log Cs1 := by
  refine ⟨by rw [he, hes]; ring, ?_⟩
  have hk : 0 < β * (1 + r) := mul_pos hβ hr
  rw [he, hes, Real.log_mul hk.ne' hC1.ne', Real.log_mul hk.ne' hCs1.ne']
  ring

/-- **(57) in log-deviation form**, O&R p. 677: measured from a symmetric base `C̄₀ = C̄₀*`,
`c̄ − c̄* = c − c*` exactly. -/
theorem eq57_exact {β r C0 C1 C2 Cs1 Cs2 : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    (hC1 : 0 < C1) (hCs1 : 0 < Cs1) (he : C2 = β * (1 + r) * C1)
    (hes : Cs2 = β * (1 + r) * Cs1) :
    (Real.log C2 - Real.log C0) - (Real.log Cs2 - Real.log C0) =
      (Real.log C1 - Real.log C0) - (Real.log Cs1 - Real.log C0) := by
  have := (consumption_ratio_exact hβ hr hC1 hCs1 he hes).2
  linarith

end ObstfeldRogoff.StickyPriceModels.ReduxLogLinear
