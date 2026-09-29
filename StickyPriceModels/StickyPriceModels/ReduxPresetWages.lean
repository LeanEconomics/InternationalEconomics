/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceModels.ReduxWelfare

/-!
# The two-country model with preset wages (§10.4.2)

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.4.2,
pp. 709–711. Each country has a continuum of differentiated final goods and of differentiated
labour inputs; the representative Home firm produces with the CES technology (142),
`y(j) = ½[2∫₀^{1/2} ℓ(z)^{(φ−1)/φ}dz]^{φ/(φ−1)}`, `φ > 1`, and each worker is the monopoly supplier
of its labour type, with utility (141).

* **The firm (142).** On finitely many labour types with positive weights summing to one (the
  normalised measure `2dz` on `[0, ½]`), the minimum cost of output `y` is `W y`, with `W` the CES
  wage index, attained exactly by the CES labour demands (`firm_min_cost`, `firm_cost_eq_iff`); so
  marginal cost is the constant `W`, and under symmetric wages `W = w` and `y = ℓ/2`.
* **Markup pricing.** Facing constant-elasticity demand, the profit `(p − W)(p/P)^{−θ}Y` has the
  UNIQUE maximiser `p = θW/(θ−1)` (`markup_isGreatest`; Bernoulli's inequality).
* **The worker.** On its labour-demand curve, real labour income is
  `(W/P) h^{(φ−1)/φ} H^{1/φ}` (`labour_income_on_demand`): the worker's problem IS the household
  problem (12) of `ReduxPrimitives` with `θ` replaced by `φ` and the demand shifter
  `Z = (W/P) H^{1/φ}` (profits enter as lump-sum income), so `HouseholdEnv.isOptimal_iff` gives
  necessity and sufficiency of its first-order conditions over a genuine infinite horizon; under
  symmetry the labour condition is `w/P = (φ/(φ−1)) κ h C` (`wage_foc_symmetric`).
* **Equivalence with §10.1.** Markup + wage condition + demand give EXACTLY (15) with `κ`
  replaced by `κφ/(φ−1)` (`presetWage_labour_iff`), so the flexible-price model is the redux model
  with parameters `wageParams`: its steady state exists and is unique for every `B̄`, the
  symmetric steady state is (143) (`wageParams_ybar0`), below the §10.1 level, the log-linear
  labour condition is (33) exactly, and income = wages + profits gives (40) unchanged. With
  nominal wages preset, the markup rule presets goods prices EXACTLY even though they are
  flexible (`markup_log_exact`), so the short-run linear system is `MoneyShockEqm` and all the
  results of §10.1.7–§10.1.8 transfer (`presetWage_iff_money`). Workers meet labour demand at the
  preset wage iff the real wage covers the marginal disutility, which holds strictly at the steady
  state (markup `φ/(φ−1)`).
* **Pricing to market (144).** With linear technology the two markets separate; the unique optimum
  is `p(h) = θ_H w/(θ_H−1)` at home and `𝓔p*(h) = θ_F w/(θ_F−1)` abroad; with equal elasticities
  the law of one price holds endogenously, `p(h) = 𝓔p*(h)`, and pass-through is complete (the
  foreign-currency price has elasticity `−1` with respect to `𝓔`) even when the elasticities
  differ (`ptm_optimal`, `ptm_pass_through`).
* **The normalisation of (141)–(142)** (survey flag): (143) requires `ℓ` in (141) to be the
  worker's TOTAL hours (`= y`); with the per-firm reading the effective `κ` is `4κ` and output
  halves (`normalisation_flag`).
-/

namespace ObstfeldRogoff.StickyPriceModels.ReduxPresetWages

open Real Filter Topology ReduxPrimitives ReduxLogLinear ReduxSteadyState ReduxMoneyShocks
  ReduxWelfare

/-! ## The firm (142): cost minimisation -/

/-- The Home firm's output (142), O&R p. 710: `y = ½ · [Σ ωᵢ ℓᵢ^{(φ−1)/φ}]^{φ/(φ−1)}` on finitely
many labour types with weights `ω` (the normalised measure `2dz` on `[0, ½]`). -/
noncomputable def firmOutput {ι : Type*} [Fintype ι] (φ : ℝ) (ω ℓ : ι → ℝ) : ℝ :=
  cesQuantityIndex φ ω ℓ / 2

/-- The firm's wage bill `∫₀^{1/2} w(z) ℓ(z) dz = ½ Σ ωᵢ wᵢ ℓᵢ`, O&R p. 710. -/
noncomputable def wageBill {ι : Type*} [Fintype ι] (ω w ℓ : ι → ℝ) : ℝ :=
  cesExpenditure ω w ℓ / 2

/-- **The cost of output is at least `W y`** (O&R p. 710; CES duality, T1): for positive wages
and inputs, the wage bill is at least the wage index `W = [Σ ωᵢ wᵢ^{1−φ}]^{1/(1−φ)}` times
output. -/
theorem firm_cost_ge {ι : Type*} [Fintype ι] [Nonempty ι] {φ : ℝ} (hφ : 1 < φ) {ω w ℓ : ι → ℝ}
    (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) (hℓ : ∀ i, 0 < ℓ i) :
    cesPriceIndex φ ω w * firmOutput φ ω ℓ ≤ wageBill ω w ℓ := by
  have h := ces_expenditure_ge hφ hω hw hℓ
  unfold firmOutput wageBill
  linarith

/-- **The cost-minimising inputs are exactly the CES labour demands** (O&R (135) analogue,
p. 710): the wage bill equals `W y` IFF `ℓᵢ = (wᵢ/W)^{−φ} · 2y`. -/
theorem firm_cost_eq_iff {ι : Type*} [Fintype ι] [Nonempty ι] {φ : ℝ} (hφ : 1 < φ)
    {ω w ℓ : ι → ℝ} (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) (hℓ : ∀ i, 0 < ℓ i) :
    wageBill ω w ℓ = cesPriceIndex φ ω w * firmOutput φ ω ℓ ↔
      ℓ = cesDemandBundle φ ω w (2 * firmOutput φ ω ℓ) := by
  have h := ces_expenditure_eq_iff hφ hω hw hℓ
  unfold wageBill firmOutput at *
  have e : 2 * (cesQuantityIndex φ ω ℓ / 2) = cesQuantityIndex φ ω ℓ := by ring
  rw [e]
  constructor
  · intro h1; exact h.1 (by linarith)
  · intro h1; have := h.2 h1; linarith

/-- **Marginal cost is the wage index** (O&R p. 710): for every `y > 0` the minimum wage bill
over positive inputs producing `y` is exactly `W y`. -/
theorem firm_min_cost {ι : Type*} [Fintype ι] [Nonempty ι] {φ : ℝ} (hφ : 1 < φ) {ω w : ι → ℝ}
    (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) {y : ℝ} (hy : 0 < y) :
    IsLeast {Z | ∃ ℓ : ι → ℝ, (∀ i, 0 < ℓ i) ∧ firmOutput φ ω ℓ = y ∧ Z = wageBill ω w ℓ}
      (cesPriceIndex φ ω w * y) := by
  have hW := cesPriceIndex_pos (θ := φ) hω hw
  refine ⟨⟨cesDemandBundle φ ω w (2 * y), fun i => cesDemand_pos φ (hw i) hW (by linarith),
    ?_, ?_⟩, ?_⟩
  · unfold firmOutput
    rw [cesQuantityIndex_demandBundle hφ hω hw (by linarith)]
    ring
  · unfold wageBill
    rw [cesExpenditure_demandBundle hφ.ne' hω hw]
    ring
  · rintro Z ⟨ℓ, hℓ, hy', rfl⟩
    have := firm_cost_ge hφ hω hw hℓ
    rw [hy'] at this
    exact this

/-- **Symmetric wages and inputs** (O&R p. 710, "when all domestic labor inputs are used
symmetrically at level `ℓ`, `y = ℓ/2`"): with weights summing to one, the wage index of equal
wages `w` is `w`, and equal inputs `ℓ` produce `ℓ/2`. -/
theorem symmetric_firm {ι : Type*} [Fintype ι] [Nonempty ι] {φ : ℝ} (hφ : 1 < φ) {ω : ι → ℝ}
    (hsum : ∑ i, ω i = 1) {w ℓ : ℝ} (hw : 0 < w) (hℓ : 0 < ℓ) :
    cesPriceIndex φ ω (fun _ => w) = w ∧ firmOutput φ ω (fun _ => ℓ) = ℓ / 2 := by
  have hφ1 : 1 - φ ≠ 0 := by linarith
  have hφ2 : φ - 1 ≠ 0 := by linarith
  have hφ0 : φ ≠ 0 := by linarith
  constructor
  · unfold cesPriceIndex
    rw [← Finset.sum_mul, hsum, one_mul, ← rpow_mul hw.le]
    rw [show (1 - φ) * (1 / (1 - φ)) = 1 by field_simp, rpow_one]
  · unfold firmOutput cesQuantityIndex
    rw [← Finset.sum_mul, hsum, one_mul, ← rpow_mul hℓ.le]
    rw [show (φ - 1) / φ * (φ / (φ - 1)) = 1 by field_simp, rpow_one]

/-! ## Markup pricing -/

/-- **Markup pricing is the unique optimum** (O&R p. 710, `p = θw/(θ−1)`): for `θ > 1`, marginal
cost `W > 0`, price index `P > 0` and demand level `Y > 0`, the profit
`(p − W)(p/P)^{−θ}Y` is maximised over `p > 0` exactly at `p* = θW/(θ−1)`: it is at most the
profit at `p*`, strictly unless `p = p*`. -/
theorem markup_isGreatest {θ W P Y : ℝ} (hθ : 1 < θ) (hW : 0 < W) (hP : 0 < P) (hY : 0 < Y)
    {p : ℝ} (hp : 0 < p) :
    (p - W) * cesDemand θ p P Y ≤ (θ * W / (θ - 1) - W) * cesDemand θ (θ * W / (θ - 1)) P Y ∧
    (p ≠ θ * W / (θ - 1) →
      (p - W) * cesDemand θ p P Y < (θ * W / (θ - 1) - W) * cesDemand θ (θ * W / (θ - 1)) P Y) := by
  have hθ1 : 0 < θ - 1 := by linarith
  have hθ0 : 0 < θ := by linarith
  set ps := θ * W / (θ - 1) with hps
  have hpspos : 0 < ps := by positivity
  set x := p / ps with hx
  have hxpos : 0 < x := div_pos hp hpspos
  have hpx : p = ps * x := by rw [hx]; field_simp
  have hWps : W = ps * ((θ - 1) / θ) := by rw [hps]; field_simp
  set A := (ps / P) ^ (-θ) * Y with hA
  have hApos : 0 < A := mul_pos (rpow_pos_of_pos (div_pos hpspos hP) _) hY
  have hd : cesDemand θ p P Y = x ^ (-θ) * A := by
    unfold cesDemand
    rw [hA, hpx, show ps * x / P = x * (ps / P) by ring,
      mul_rpow hxpos.le (div_pos hpspos hP).le]
    ring
  have hds : cesDemand θ ps P Y = A := by unfold cesDemand; rw [hA]
  rw [hd, hds]
  have hxθ : 0 < x ^ θ := rpow_pos_of_pos hxpos θ
  have hinv : x ^ (-θ) = 1 / x ^ θ := by rw [rpow_neg hxpos.le, one_div]
  -- Bernoulli: `x^θ ≥ 1 + θ(x − 1)`
  have key : ∀ strict : Bool, (strict = true → x ≠ 1) →
      (if strict then θ * x - (θ - 1) < x ^ θ else θ * x - (θ - 1) ≤ x ^ θ) := by
    intro strict hs
    cases strict with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases eq_or_ne x 1 with h1 | h1
      · rw [h1, one_rpow]; linarith
      · have := one_add_mul_self_lt_rpow_one_add (s := x - 1) (by linarith) (sub_ne_zero.2 h1) hθ
        rw [show 1 + (x - 1) = x by ring] at this
        linarith
    | true =>
      simp only [↓reduceIte]
      have h1 := hs rfl
      have := one_add_mul_self_lt_rpow_one_add (s := x - 1) (by linarith) (sub_ne_zero.2 h1) hθ
      rw [show 1 + (x - 1) = x by ring] at this
      linarith
  have e1 : (p - W) * (x ^ (-θ) * A) = ps / θ * A * ((θ * x - (θ - 1)) / x ^ θ) := by
    rw [hinv, hpx, hWps]; field_simp
  have e2 : (ps - W) * A = ps / θ * A * 1 := by rw [hWps]; field_simp; ring
  have hc : 0 < ps / θ * A := by positivity
  constructor
  · rw [e1, e2]
    apply mul_le_mul_of_nonneg_left _ hc.le
    rw [div_le_one hxθ]
    simpa using key false (by simp)
  · intro hne
    have hx1 : x ≠ 1 := by
      intro h; apply hne; rw [hpx, h, mul_one]
    rw [e1, e2]
    apply mul_lt_mul_of_pos_left _ hc
    rw [div_lt_one hxθ]
    simpa using key true (fun _ => hx1)

/-! ## The worker -/

/-- **Labour income on the labour-demand curve** (O&R p. 710 and (135)–(136)): if the worker's
hours are `h = (w/W)^{−φ} H`, its real labour income is
`(w/P) h = (W/P) h^{(φ−1)/φ} H^{1/φ}`. Hence the worker's budget is the household budget (8) of
§10.1 with `θ` replaced by `φ` and demand shifter `Z = (W/P)H^{1/φ}`. -/
theorem labour_income_on_demand {φ w W P h H : ℝ} (hφ : φ ≠ 0) (hw : 0 < w) (hW : 0 < W)
    (hh : 0 < h) (hH : 0 < H) (hd : h = cesDemand φ w W H) :
    w / P * h = W / P * (h ^ ((φ - 1) / φ) * H ^ (1 / φ)) := by
  have hq : 0 < w / W := div_pos hw hW
  have hd' : h = cesDemand φ (w / W) 1 H := by
    rw [hd]; unfold cesDemand; rw [div_one]
  have h1 := revenue_on_demand hφ hq hh hH hd'
  have e : w / P * h = W / P * (w / W * h) := by field_simp
  rw [e, h1]

/-- **The worker's problem is the household problem of §10.1 with `θ → φ`** (O&R p. 710:
"the first-order condition governing the individual's labor-leisure decision is analogous to
eq. (136)"): for the environment with elasticity `φ`, demand shifter `Z_t = (W_t/P_t)H_t^{1/φ}`
and lump-sum income (profits) netted into `τ`, an admissible plan is optimal IFF it satisfies the
Euler equation, money demand, the labour condition and the transversality condition (genuine
infinite horizon; `HouseholdEnv.isOptimal_iff`). -/
theorem worker_isOptimal_iff {E : HouseholdEnv} {q : HouseholdPlan} (hreg : E.Regular) :
    E.IsOptimal q ↔ E.Admissible q ∧ E.EulerCond q ∧ E.MoneyCond q ∧ E.LabourCond q ∧
      E.Transversality (E.wealthPath q) :=
  HouseholdEnv.isOptimal_iff hreg

/-- **The symmetric wage condition** (O&R p. 710; survey T32): with `Z = (W/P)H^{1/φ}` and
symmetry `h = H`, the worker's labour condition `h^{(φ+1)/φ} = ((φ−1)/(φκ)) Z/C`
(`labourCond_iff_book`) holds IFF `W/P = (φ/(φ−1)) κ h C`. -/
theorem wage_foc_symmetric {φ κ h C WP : ℝ} (hφ : 1 < φ) (hκ : 0 < κ) (hh : 0 < h)
    (hC : 0 < C) :
    h ^ ((φ + 1) / φ) = (φ - 1) / (φ * κ) * (WP * h ^ (1 / φ)) / C ↔
      WP = φ / (φ - 1) * κ * h * C := by
  have hφ0 : φ ≠ 0 := by linarith
  have hφ1 : φ - 1 ≠ 0 := by linarith
  rw [rpow_succ_div hφ0 hh]
  have hr := (rpow_pos_of_pos hh (1 / φ)).ne'
  constructor
  · intro h1
    field_simp at h1
    field_simp
    linarith
  · intro h1
    rw [h1]
    field_simp

/-! ## Equivalence with the model of §10.1 -/

/-- **Markup + wage condition + demand give (15) with `κ → κφ/(φ−1)`** (O&R pp. 710–711; survey
T32): if the relative price is the markup over the real wage, `q = (θ/(θ−1)) ω`, the real wage
satisfies the symmetric wage condition `ω = (φ/(φ−1)) κ y C` (hours `= y`), and output is on the
demand curve `y = q^{−θ}Cᵂ`, then `y^{(θ+1)/θ} = ((θ−1)/(θκ′))(Cᵂ)^{1/θ}/C` with
`κ′ = κφ/(φ−1)` — exactly the labour–leisure condition (15) of §10.1 with `κ′` in place of `κ`. -/
theorem presetWage_labour_iff {θ φ κ q ω y C X : ℝ} (hθ : 1 < θ) (hφ : 1 < φ) (hκ : 0 < κ)
    (hq : 0 < q) (hy : 0 < y) (hC : 0 < C) (hX : 0 < X) (hmarkup : q = θ / (θ - 1) * ω)
    (hdem : y = cesDemand θ q 1 X) :
    ω = φ / (φ - 1) * κ * y * C ↔
      y ^ ((θ + 1) / θ) = (θ - 1) / (θ * (κ * φ / (φ - 1))) * X ^ (1 / θ) / C := by
  have hθ0 : θ ≠ 0 := by linarith
  have hθ1 : θ - 1 ≠ 0 := by linarith
  have hφ1 : φ - 1 ≠ 0 := by linarith
  have hφ0 : φ ≠ 0 := by linarith
  have hXr : X ^ (1 / θ) = q * y ^ (1 / θ) := by
    have hX' : X = q ^ θ * y := by
      rw [hdem]; unfold cesDemand
      rw [div_one, rpow_neg hq.le]
      have := (rpow_pos_of_pos hq θ).ne'
      field_simp
    rw [hX', mul_rpow (rpow_nonneg hq.le _) hy.le, ← rpow_mul hq.le, mul_one_div_cancel hθ0,
      rpow_one]
  rw [rpow_succ_div hθ0 hy, hXr]
  have hr := (rpow_pos_of_pos hy (1 / θ)).ne'
  rw [hmarkup]
  constructor
  · intro h; rw [h]; field_simp
  · intro h
    field_simp at h
    field_simp
    linarith

/-- The parameters of §10.1 that reproduce the preset-wage economy (O&R p. 710): the same
`β, χ, θ, n`, and effort weight `κ′ = κφ/(φ−1)`. -/
noncomputable def wageParams (M : ReduxParams) {φ : ℝ} (hφ : 1 < φ) : ReduxParams :=
  ⟨M.β, M.χ, M.κ * φ / (φ - 1), M.θ, M.n, M.hβ0, M.hβ1, M.hχ,
    div_pos (mul_pos M.hκ (by linarith)) (by linarith), M.hθ, M.hn0, M.hn1⟩

/-- **(143): the symmetric steady state with preset wages**, O&R p. 710: the steady state of the
flexible-price preset-wage economy (which is the §10.1 steady state for `wageParams`, existing
and unique for every `B̄` by `exists_unique_steady`) has
`ȳ₀ = ȳ₀* = [((φ−1)/φ)((θ−1)/θ)/κ]^{1/2}`, strictly below the §10.1 level `[(θ−1)/(θκ)]^{1/2}`
("output is lower due to monopoly distortions in both the labor market and the output
market"). -/
theorem wageParams_ybar0 (M : ReduxParams) {φ : ℝ} (hφ : 1 < φ) :
    (wageParams M hφ).ybar0 = Real.sqrt ((φ - 1) / φ * ((M.θ - 1) / M.θ) / M.κ) ∧
    (wageParams M hφ).ybar0 < M.ybar0 ∧
    IsSteadyState (wageParams M hφ) 0 (symmetricSteady (wageParams M hφ)) := by
  have hθ := M.hθ
  have hκ := M.hκ
  have hφ0 : φ ≠ 0 := by linarith
  have hφ1 : φ - 1 ≠ 0 := by linarith
  have hθ0 : M.θ ≠ 0 := by linarith
  have e : (wageParams M hφ).K = (φ - 1) / φ * ((M.θ - 1) / M.θ) / M.κ := by
    simp only [ReduxParams.K, wageParams]
    field_simp
  refine ⟨by rw [ReduxParams.ybar0, e], ?_, (isSteadyState_zero_iff _ _).2 rfl⟩
  unfold ReduxParams.ybar0
  apply Real.sqrt_lt_sqrt (wageParams M hφ).K_pos.le
  rw [e]
  unfold ReduxParams.K
  have h1 : (φ - 1) / φ < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h2 : 0 < (M.θ - 1) / M.θ / M.κ := div_pos (div_pos (by linarith) (by linarith)) hκ
  have : (φ - 1) / φ * ((M.θ - 1) / M.θ) / M.κ = (φ - 1) / φ * ((M.θ - 1) / M.θ / M.κ) := by
    ring
  rw [this, show (M.θ - 1) / (M.θ * M.κ) = (M.θ - 1) / M.θ / M.κ by field_simp]
  nlinarith

/-- **The log-linear labour condition is (33), exactly** (O&R p. 710; survey T32): since the
preset-wage labour condition is (15) with `K′ = (θ−1)/(θκ′)`, log changes satisfy
`(θ+1)Δlog y = −θΔlog C + Δlog Cᵂ` exactly. -/
theorem presetWage_labour_log_exact {θ φ κ y0 y1 C0 C1 X0 X1 : ℝ} (hθ : 1 < θ) (hφ : 1 < φ)
    (hκ : 0 < κ) (hy0 : 0 < y0) (hy1 : 0 < y1) (hC0 : 0 < C0) (hC1 : 0 < C1) (hX0 : 0 < X0)
    (hX1 : 0 < X1)
    (h0 : y0 ^ ((θ + 1) / θ) = (θ - 1) / (θ * (κ * φ / (φ - 1))) * X0 ^ (1 / θ) / C0)
    (h1 : y1 ^ ((θ + 1) / θ) = (θ - 1) / (θ * (κ * φ / (φ - 1))) * X1 ^ (1 / θ) / C1) :
    (θ + 1) * (Real.log y1 - Real.log y0) =
      -θ * (Real.log C1 - Real.log C0) + (Real.log X1 - Real.log X0) := by
  have hK : 0 < (θ - 1) / (θ * (κ * φ / (φ - 1))) :=
    div_pos (by linarith) (mul_pos (by linarith) (div_pos (mul_pos hκ (by linarith))
      (by linarith)))
  exact labour_log_exact (by linarith) hK hy0 hy1 hC0 hC1 hX0 hX1 h0 h1

/-- **Income = wages + profits, so (40) is unchanged** (O&R p. 710: "Home agents each hold equal
shares of a portfolio of all Home firms"): with hours equal to output, `w y + (p − w) y = p y`,
so the steady-state budget is `C = δB + p(h)y/P` as in (20). -/
theorem wage_profit_income {w p y P : ℝ} : (w * y + (p - w) * y) / P = p * y / P := by ring

/-- **Preset wages preset goods prices, exactly** (O&R p. 710: "if final-goods prices are flexible,
wages are preset …"): with the markup rule `p = θw/(θ−1)` at both dates, the log change of the
goods price equals the log change of the wage; with the wage preset, `p₁ = p₀` exactly although
the goods price is flexible. -/
theorem markup_log_exact {θ w0 w1 : ℝ} (hθ : 1 < θ) (hw0 : 0 < w0) (hw1 : 0 < w1) :
    Real.log (θ * w1 / (θ - 1)) - Real.log (θ * w0 / (θ - 1)) = Real.log w1 - Real.log w0 ∧
      (w1 = w0 → θ * w1 / (θ - 1) = θ * w0 / (θ - 1)) := by
  have hθ0 : 0 < θ := by linarith
  have hθ1 : 0 < θ - 1 := by linarith
  refine ⟨?_, fun h => by rw [h]⟩
  rw [mul_div_assoc, mul_div_assoc, Real.log_mul hθ0.ne' (div_pos hw1 hθ1).ne',
    Real.log_mul hθ0.ne' (div_pos hw0 hθ1).ne', Real.log_div hw1.ne' hθ1.ne',
    Real.log_div hw0.ne' hθ1.ne']
  ring

variable (L : ReduxLinear) in
/-- **The short-run system with preset wages** (O&R p. 710): wages are preset (log deviations
`w = w* = 0`), goods prices follow the markup exactly (`p(h) = w`, `p*(f) = w*`,
`markup_log_exact`), and otherwise the date-1 equations and the long run are those of §10.1.7. -/
structure PresetWageEqm (m ms wh wf ph pf : ℝ) (u : ShortVars) (v : SteadyVars) : Prop where
  preset : wh = 0
  preset_star : wf = 0
  markup : ph = wh
  markup_star : pf = wf
  eq27 : u.p = L.n * ph + (1 - L.n) * (u.e + pf)
  eq28 : u.ps = L.n * (ph - u.e) + (1 - L.n) * pf
  eq30 : u.y = L.θ * (u.p - ph) + u.cW
  eq31 : u.ys = L.θ * (u.ps - pf) + u.cW
  eq32 : u.cW = L.n * u.c + (1 - L.n) * u.cs
  eq35 : v.c = u.c + L.δ / (1 + L.δ) * u.r
  eq36 : v.cs = u.cs + L.δ / (1 + L.δ) * u.r
  eq37 : m - u.p = u.c - u.r / (1 + L.δ) - (v.p - u.p) / L.δ
  eq38 : ms - u.ps = u.cs - u.r / (1 + L.δ) - (v.ps - u.ps) / L.δ
  eq55 : u.b = u.y - u.c + (ph - u.p)
  longrun : SteadyLinear L u.b m ms v

/-- **With preset wages the effects of money shocks are exactly those of §10.1** (O&R p. 710:
"the effects of a surprise permanent money increase on both consumption differentials and the
exchange rate are the same as in section 10.1"): `PresetWageEqm` holds IFF wages and goods prices
are unchanged and `MoneyShockEqm` holds; hence (by `moneyShock_iff`) the equilibrium exists, is
unique, and is given by (65)–(74). -/
theorem presetWage_iff_money (L : ReduxLinear) (m ms wh wf ph pf : ℝ) (u : ShortVars)
    (v : SteadyVars) :
    PresetWageEqm L m ms wh wf ph pf u v ↔
      wh = 0 ∧ wf = 0 ∧ ph = 0 ∧ pf = 0 ∧ MoneyShockEqm L m ms u v := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h27, h28, h30, h31, h32, h35, h36, h37, h38, h55, hl⟩
    subst h1 h2
    subst h3 h4
    refine ⟨rfl, rfl, rfl, rfl, h27, h28, h30, h31, h32, h35, h36, h37, h38, ?_, hl⟩
    rw [h55, h27]; ring
  · rintro ⟨rfl, rfl, rfl, rfl, h⟩
    exact ⟨rfl, rfl, rfl, rfl, h.eq27, h.eq28, h.eq30, h.eq31, h.eq32, h.eq35, h.eq36, h.eq37,
      h.eq38, by rw [h.eq55, h.eq27]; ring, h.longrun⟩

/-- **Workers meet labour demand at the preset wage iff the real wage covers the marginal
disutility** (O&R p. 709 for §10.4.1, and p. 710): a worker with a fixed real wage `ω > 0`
facing demand `h_d` prefers supplying `h_d` to any `h ∈ [0, h_d]` IFF `κ h_d ≤ ω/C`
(`meet_demand_iff`). At the steady state the real wage exceeds the marginal disutility by the
markup `φ/(φ−1) > 1`: `ω/C = (φ/(φ−1))κh > κh`. -/
theorem worker_meets_demand {ω C κ hd : ℝ} (hω : 0 < ω) (hC : 0 < C) (hκ : 0 < κ) :
    (∀ h, 0 ≤ h → h ≤ hd → ω * h / C - κ / 2 * h ^ 2 ≤ ω * hd / C - κ / 2 * hd ^ 2) ↔
      κ * hd ≤ ω / C :=
  meet_demand_iff hω hC hκ

/-- **At the steady state the real wage strictly exceeds the marginal disutility of work**
(O&R p. 709, "the marginal utility of the initial real wage exceeds the marginal disutility from
labor"): if `ω = (φ/(φ−1))κhC` with `φ > 1`, `κ, h, C > 0`, then `κh < ω/C`. -/
theorem steady_wage_exceeds_mrs {φ κ h C ω : ℝ} (hφ : 1 < φ) (hκ : 0 < κ) (hh : 0 < h)
    (hC : 0 < C) (hω : ω = φ / (φ - 1) * κ * h * C) : κ * h < ω / C := by
  rw [hω]
  have hφ1 : 0 < φ - 1 := by linarith
  have e : φ / (φ - 1) * κ * h * C / C = φ / (φ - 1) * (κ * h) := by field_simp
  rw [e]
  have : 1 < φ / (φ - 1) := by rw [one_lt_div hφ1]; linarith
  have : 0 < κ * h := mul_pos hκ hh
  nlinarith

/-! ## Pricing to market (144) -/

/-- **(144): pricing to market with linear technology** (O&R p. 711): a Home firm with constant
marginal cost `w` sells at `p` in the Home market (demand `(p/P)^{−θ_H}X_H`) and at the
foreign-currency price `p*` abroad (demand `(p*/P*)^{−θ_F}X_F`, revenue `𝓔p*` per unit in Home
currency). Its profit separates across markets, and at every `(p, p*)` it is at most the profit
at `p = θ_H w/(θ_H−1)`, `𝓔p* = θ_F w/(θ_F−1)`, strictly unless both prices are these. -/
theorem ptm_optimal {θH θF w P Ps XH XF E : ℝ} (hθH : 1 < θH) (hθF : 1 < θF) (hw : 0 < w)
    (hP : 0 < P) (hPs : 0 < Ps) (hXH : 0 < XH) (hXF : 0 < XF) (hE : 0 < E) {p ps : ℝ}
    (hp : 0 < p) (hps : 0 < ps) :
    (p - w) * cesDemand θH p P XH + (E * ps - w) * cesDemand θF ps Ps XF ≤
      (θH * w / (θH - 1) - w) * cesDemand θH (θH * w / (θH - 1)) P XH +
      (θF * w / (θF - 1) - w) * cesDemand θF (θF * w / (θF - 1) / E) Ps XF ∧
    ((p ≠ θH * w / (θH - 1) ∨ E * ps ≠ θF * w / (θF - 1)) →
      (p - w) * cesDemand θH p P XH + (E * ps - w) * cesDemand θF ps Ps XF <
      (θH * w / (θH - 1) - w) * cesDemand θH (θH * w / (θH - 1)) P XH +
      (θF * w / (θF - 1) - w) * cesDemand θF (θF * w / (θF - 1) / E) Ps XF) := by
  -- the Foreign market in Home-currency prices `p′ = 𝓔p*`, with index `𝓔P*`
  have hconv : ∀ q, cesDemand θF q Ps XF = cesDemand θF (E * q) (E * Ps) XF := by
    intro q; unfold cesDemand; congr 2; field_simp
  have hH := markup_isGreatest hθH hw hP hXH hp
  have hF := markup_isGreatest hθF hw (mul_pos hE hPs) hXF (mul_pos hE hps)
  have hopt : cesDemand θF (θF * w / (θF - 1) / E) Ps XF =
      cesDemand θF (θF * w / (θF - 1)) (E * Ps) XF := by
    rw [hconv]; congr 1; field_simp
  rw [hconv ps, hopt]
  refine ⟨by linarith [hH.1, hF.1], fun hne => ?_⟩
  rcases hne with h1 | h1
  · linarith [hH.2 h1, hF.1]
  · linarith [hH.1, hF.2 h1]

/-- **The law of one price and complete pass-through under pricing to market** (O&R p. 711): with
equal elasticities `θ_H = θ_F = θ` the optimal prices satisfy `p(h) = 𝓔p*(h) = θw/(θ−1)` (LOOP
holds although arbitrage is precluded); for any elasticities the optimal foreign-currency price is
`p* = θ_F w/((θ_F−1)𝓔)`, whose elasticity with respect to `𝓔` is exactly `−1` (complete
pass-through): `d log p*/d log 𝓔 = −1`. -/
theorem ptm_pass_through {θ θF w E0 : ℝ} (hθF : 1 < θF) (hw : 0 < w) (hE0 : 0 < E0) :
    θ * w / (θ - 1) = E0 * (θ * w / (θ - 1) / E0) ∧
    HasDerivAt (fun τ => Real.log (θF * w / (θF - 1) / (E0 * Real.exp τ))) (-1) 0 := by
  refine ⟨by field_simp, ?_⟩
  have hk : 0 < θF * w / (θF - 1) := div_pos (mul_pos (by linarith) hw) (by linarith)
  have e : (fun τ => Real.log (θF * w / (θF - 1) / (E0 * Real.exp τ))) =
      fun τ => Real.log (θF * w / (θF - 1)) - Real.log E0 - τ := by
    funext τ
    rw [Real.log_div hk.ne' (mul_pos hE0 (Real.exp_pos τ)).ne',
      Real.log_mul hE0.ne' (Real.exp_pos τ).ne', Real.log_exp]
    ring
  rw [e]
  simpa using (hasDerivAt_id (0 : ℝ)).const_sub (Real.log (θF * w / (θF - 1)) - Real.log E0)

/-- **Different elasticities give different price levels, not incomplete pass-through** (O&R
p. 711: "if the constant elasticity of demand is different in the two markets, the levels of
prices will differ"): for `θ_H ≠ θ_F` (both `> 1`) the optimal `p(h) ≠ 𝓔p*(h)`, while `𝓔p*(h)`
does not depend on `𝓔`. -/
theorem ptm_different_elasticities {θH θF w : ℝ} (hθH : 1 < θH) (hθF : 1 < θF) (hw : 0 < w)
    (hne : θH ≠ θF) : θH * w / (θH - 1) ≠ θF * w / (θF - 1) := by
  intro h
  have h1 : θH - 1 ≠ 0 := by linarith
  have h2 : θF - 1 ≠ 0 := by linarith
  field_simp at h
  exact hne (by linarith)

/-! ## The normalisation of (141)–(142) -/

/-- **(143) requires `ℓ` in (141) to be TOTAL hours** (survey flag on O&R pp. 709–710): if instead
the disutility were `(κ/2)ℓ²` with `ℓ = 2y` (hours per firm-type with `y = ℓ/2`), then
`(κ/2)(2y)² = (4κ/2)y²`, the effective weight is `4κ`, and the symmetric steady-state output is
exactly half of (143). -/
theorem normalisation_flag {θ φ κ y : ℝ} (hθ : 1 < θ) (hφ : 1 < φ) (hκ : 0 < κ) :
    κ / 2 * (2 * y) ^ 2 = 4 * κ / 2 * y ^ 2 ∧
    Real.sqrt ((φ - 1) / φ * ((θ - 1) / θ) / (4 * κ)) =
      Real.sqrt ((φ - 1) / φ * ((θ - 1) / θ) / κ) / 2 := by
  refine ⟨by ring, ?_⟩
  have hA : 0 ≤ (φ - 1) / φ * ((θ - 1) / θ) / κ :=
    div_nonneg (mul_nonneg (div_nonneg (by linarith) (by linarith))
      (div_nonneg (by linarith) (by linarith))) hκ.le
  have e : (φ - 1) / φ * ((θ - 1) / θ) / (4 * κ) = (φ - 1) / φ * ((θ - 1) / θ) / κ / 2 ^ 2 := by
    field_simp; ring
  rw [e, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num)]

end ObstfeldRogoff.StickyPriceModels.ReduxPresetWages
