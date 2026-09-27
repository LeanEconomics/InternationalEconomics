/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SmallOpenEconomyDynamics.PresentValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Firms, the labour market, and financial and human wealth

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §2.5.1,
pp. 99–105, footnotes 35–38, and Appendix 2B.1, pp. 121–123. Date 0 stands for the
book's date `t`; sequences are indexed from date 0.

* The consumer holds bonds `B` and firm shares `x`. The bond and share Euler equations give
  the arbitrage condition (2.53), `1 + r = (d_{s+1} + V_{s+1})/V_s`: `share_arbitrage_iff`.
  With it the finance constraint (2.52) becomes the financial-wealth accumulation equation
  `Q_{s+1} − Q_s = rQ_s + w_sL − C_s − G_s` for any share holdings, not only `x = 1`
  (`wealth_accumulation`), and the intertemporal budget constraint (2.55) is equivalent to
  the transversality condition on `Q` (`ibc_iff_transversality`).
* (2.56)–(2.57): the share price is the present value of dividends iff there is no bubble
  (`share_price_eq_pv_dividends_iff`, reusing `PresentValue.forward_solution_iff`).
* (2.58): the firm's first-order conditions `A_sF_L = w_s` (`labor_foc`) and
  `A_{s+1}F_K = r` (`capital_foc`), derived from optimality against one-date perturbations
  of the plan. Euler's theorem `F = K F_K + L F_L` is proved from degree-one homogeneity and
  differentiability (`euler_homogeneous`).
* (2.59): the firm's value equals next period's capital. The present value of dividends is
  `K_{t+1}` (`tendsto_pv_capital_dividends`), and more precisely
  `(1 + r)^{-n}V_n → V_0 − K_1`, so `V_0 = K_1` iff there is no bubble
  (`firm_value_eq_capital_iff`); then `V_s = K_{s+1}` at every date.
* (2.60)–(2.61) and the saving and current-account equations of pp. 104–105.
* Footnote 36 (Modigliani–Miller): firm borrowing leaves equity plus debt, and the consumer's
  wealth, unchanged (`modigliani_miller`, `modigliani_miller_consumer_wealth`).
* Appendix 2B.1: the iterated asset Euler equation (2.78) and the equivalence of its limit
  condition with (2.57). The book's argument that a positive limit cannot be an equilibrium
  is informal; we prove only that a positive limit means the price exceeds fundamentals and
  that nonnegative prices (free disposal, footnote 54) exclude a negative limit.
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth

open PresentValue Filter Topology Finset

/-! ## The consumer: arbitrage and financial wealth -/

/-- **Arbitrage between bonds and shares**, O&R (2.53), p. 101: given the bond Euler equation
`u'(C_s) = β(1 + r)u'(C_{s+1})` with `β > 0` and `u'(C_{s+1}) > 0`, the share Euler equation
`V_s u'(C_s) = (V_{s+1} + d_{s+1})βu'(C_{s+1})` holds iff `(1 + r)V_s = d_{s+1} + V_{s+1}`. -/
theorem share_arbitrage_iff {r β u u' V V' d' : ℝ} (hβ : 0 < β) (hu' : 0 < u')
    (hbond : u = β * (1 + r) * u') :
    V * u = (V' + d') * β * u' ↔ (1 + r) * V = d' + V' := by
  have hne : β * u' ≠ 0 := (mul_pos hβ hu').ne'
  rw [hbond]
  constructor
  · intro h
    apply mul_left_cancel₀ hne
    linear_combination h
  · intro h
    linear_combination β * u' * h

/-- The ex post return identity O&R (2.54), p. 101: under the arbitrage condition (2.53)
dated `s − 1`, dividends plus capital gains on `x_s` shares equal `rV_{s−1}x_s`. -/
theorem dividend_capital_gain_eq {r Vp Vs ds xs : ℝ} (harb : (1 + r) * Vp = ds + Vs) :
    ds * xs + (Vs - Vp) * xs = r * Vp * xs := by
  linear_combination -xs * harb

/-- **Financial-wealth accumulation**, O&R p. 101: if the finance constraint (2.52) holds at
date `s` and the arbitrage condition (2.53) held between `s − 1` and `s`, then financial wealth
`Q_{s+1} = B_{s+1} + V_s x_{s+1}` obeys `Q_{s+1} − Q_s = rQ_s + w_sL − C_s − G_s`, for arbitrary
share holdings `x_s, x_{s+1}`. -/
theorem wealth_accumulation {r Bs Bs1 Vp Vs xs xs1 ds wLs Cs Gs : ℝ}
    (h52 : Bs1 - Bs + Vs * xs1 - Vp * xs =
      r * Bs + ds * xs + (Vs - Vp) * xs + wLs - Cs - Gs)
    (harb : (1 + r) * Vp = ds + Vs) :
    (Bs1 + Vs * xs1) - (Bs + Vp * xs) = r * (Bs + Vp * xs) + wLs - Cs - Gs := by
  linear_combination h52 - xs * harb

/-- Initial financial wealth, O&R p. 101: at the initial date the finance constraint (2.52)
reads `Q_{t+1} = (1 + r)B_t + d_t x_t + V_t x_t + w_tL − C_t − G_t`; no arbitrage condition is
used, since an unanticipated shock may have occurred between `t − 1` and `t`. -/
theorem initial_financial_wealth {r B0 B1 Vm V0 x0 x1 d0 wL0 C0 G0 : ℝ}
    (h52 : B1 - B0 + V0 * x1 - Vm * x0 =
      r * B0 + d0 * x0 + (V0 - Vm) * x0 + wL0 - C0 - G0) :
    B1 + V0 * x1 = (1 + r) * B0 + d0 * x0 + V0 * x0 + wL0 - C0 - G0 := by
  linear_combination h52

/-- **The consumer's intertemporal budget constraint**, O&R (2.55), pp. 101–102. Let `Q (s+1)`
be financial wealth at the end of date `s`, `H_s = w_sL − G_s` after-tax labour income and
`W₀ = (1 + r)B_t + d_t x_t + V_t x_t`. If `Q_1 = W₀ + H_0 − C_0` and
`Q_{s+2} = (1 + r)Q_{s+1} + H_{s+1} − C_{s+1}`, then the transversality condition
`(1 + r)^{-T} Q_{T+1} → 0` holds iff `PV(C) = W₀ + PV(H)`. -/
theorem ibc_iff_transversality {r W0 : ℝ} (hr : 0 < 1 + r) {Q C H : ℕ → ℝ}
    (hQ1 : Q 1 = W0 + (H 0 - C 0))
    (hQ : ∀ s, Q (s + 2) = (1 + r) * Q (s + 1) + (H (s + 1) - C (s + 1)))
    (hC : Summable fun s => disc r ^ s * C s) (hH : Summable fun s => disc r ^ s * H s) :
    Tendsto (fun T => disc r ^ T * Q (T + 1)) atTop (𝓝 0) ↔ pv r C = W0 + pv r H := by
  have hHC : Summable fun s => disc r ^ s * (H s - C s) := by
    simpa [mul_sub] using hH.sub hC
  have hs : Summable fun s => disc r ^ (s + 1) * (H (s + 1) - C (s + 1)) :=
    (summable_nat_add_iff 1).mpr hHC
  rw [discounted_tendsto_zero_iff hr (A := fun s => Q (s + 1))
    (N := fun s => H (s + 1) - C (s + 1)) hQ hs]
  have hsplit : ∑' s, disc r ^ s * (H s - C s) =
      (H 0 - C 0) + ∑' s, disc r ^ (s + 1) * (H (s + 1) - C (s + 1)) := by
    rw [hHC.tsum_eq_zero_add]
    simp
  have hpv : ∑' s, disc r ^ s * (H s - C s) = pv r H - pv r C := by
    have := pv_sub hH hC
    unfold pv at this ⊢
    exact this
  rw [hQ1]
  constructor <;> intro e <;> linarith

/-- **The share price is the present value of dividends iff there is no bubble**,
O&R (2.56)–(2.57), p. 102, stated from the consumer's two Euler equations: with the bond Euler
equation `u'(C_s) = β(1 + r)u'(C_{s+1})` and the share Euler equation at every date,
`V_0 = Σ_{s≥1} (1 + r)^{-s} d_s` iff `(1 + r)^{-T} V_T → 0`. -/
theorem share_price_eq_pv_dividends_iff {r β : ℝ} (hr : 0 < 1 + r) (hβ : 0 < β)
    {u V d : ℕ → ℝ} (hu : ∀ s, 0 < u s)
    (hbond : ∀ s, u s = β * (1 + r) * u (s + 1))
    (hshare : ∀ s, V s * u s = (V (s + 1) + d (s + 1)) * β * u (s + 1))
    (hsum : Summable fun s => disc r ^ (s + 1) * d (s + 1)) :
    V 0 = ∑' s, disc r ^ (s + 1) * d (s + 1) ↔
      Tendsto (fun n => disc r ^ n * V n) atTop (𝓝 0) :=
  forward_solution_iff hr
    (fun s => (share_arbitrage_iff hβ (hu (s + 1)) (hbond s)).1 (hshare s)) hsum

/-! ## The firm -/

/-- The firm's dividend at date `s`, O&R p. 102: output less wages less investment,
`d_s = A_sF(K_s, L_s) − w_sL_s − (K_{s+1} − K_s)`. -/
def firmDividend (A w : ℕ → ℝ) (F : ℝ × ℝ → ℝ) (K L : ℕ → ℝ) (s : ℕ) : ℝ :=
  A s * F (K s, L s) - w s * L s - (K (s + 1) - K s)

/-- The firm's cum-dividend value `d_t + V_t = Σ_{s≥t} (1 + r)^{-(s-t)} d_s`, O&R p. 103, the
objective of the firm's hiring and investment decisions. -/
noncomputable def firmValue (r : ℝ) (A w : ℕ → ℝ) (F : ℝ × ℝ → ℝ) (K L : ℕ → ℝ) : ℝ :=
  ∑' s, disc r ^ s * firmDividend A w F K L s

/-- **The labour first-order condition** `A_sF_L(K_s, L_s) = w_s`, O&R p. 103, for every date
`s ≥ t`. Hypotheses: the plan's discounted dividends are summable, `F` has partial derivative
`F_L` in labour at `(K_s, L_s)`, and no change in date-`s` hiring raises the firm's value. -/
theorem labor_foc {r : ℝ} (hr : 0 < 1 + r) {A w K L : ℕ → ℝ} {F : ℝ × ℝ → ℝ}
    (hsum : Summable fun n => disc r ^ n * firmDividend A w F K L n) (s : ℕ) {FL : ℝ}
    (hFL : HasDerivAt (fun l => F (K s, l)) FL (L s))
    (hopt : ∀ l, firmValue r A w F K (Function.update L s l) ≤ firmValue r A w F K L) :
    A s * FL = w s := by
  set φ : ℝ → ℝ := fun l =>
    disc r ^ s * (A s * (F (K s, l) - F (K s, L s)) - w s * (l - L s)) with hφdef
  have hval : ∀ l, firmValue r A w F K (Function.update L s l) =
      firmValue r A w F K L + φ l := by
    intro l
    have hpt : (fun n => disc r ^ n * firmDividend A w F K (Function.update L s l) n) =
        fun n => disc r ^ n * firmDividend A w F K L n + if n = s then φ l else 0 := by
      funext n
      by_cases hn : n = s
      · subst hn
        simp [firmDividend, hφdef]
        ring
      · simp [firmDividend, hn]
    unfold firmValue
    rw [hpt, hsum.tsum_add (hasSum_ite_eq s (φ l)).summable, tsum_ite_eq]
  have hmax : IsLocalMax φ (L s) := by
    refine Filter.Eventually.of_forall fun l => ?_
    have h1 := hopt l
    rw [hval l] at h1
    simp [hφdef]
    linarith
  have hderiv : HasDerivAt φ (disc r ^ s * (A s * FL - w s * 1)) (L s) := by
    have h1 : HasDerivAt (fun l => A s * (F (K s, l) - F (K s, L s))) (A s * FL) (L s) :=
      HasDerivAt.const_mul (A s) (HasDerivAt.sub_const (F (K s, L s)) hFL)
    have h2 : HasDerivAt (fun l : ℝ => w s * (l - L s)) (w s * 1) (L s) :=
      HasDerivAt.const_mul (w s) (HasDerivAt.sub_const (L s) (hasDerivAt_id (L s)))
    exact HasDerivAt.const_mul (disc r ^ s) (HasDerivAt.sub h1 h2)
  have h0 := hmax.hasDerivAt_eq_zero hderiv
  have hd : disc r ^ s ≠ 0 := pow_ne_zero _ (disc_pos hr).ne'
  have := (mul_eq_zero.1 h0).resolve_left hd
  linarith

/-- **The capital first-order condition** `A_{s+1}F_K(K_{s+1}, L_{s+1}) = r`, O&R p. 103, for
every date after the first (capital `K_t` is predetermined). Hypotheses: the plan's
discounted dividends are summable, `F` has partial derivative `F_K` in capital at
`(K_{s+1}, L_{s+1})`, and no change in the capital stock chosen for date `s + 1` raises the
firm's value. -/
theorem capital_foc {r : ℝ} (hr : 0 < 1 + r) {A w K L : ℕ → ℝ} {F : ℝ × ℝ → ℝ}
    (hsum : Summable fun n => disc r ^ n * firmDividend A w F K L n) (s : ℕ) {FK : ℝ}
    (hFK : HasDerivAt (fun k => F (k, L (s + 1))) FK (K (s + 1)))
    (hopt : ∀ k, firmValue r A w F (Function.update K (s + 1) k) L ≤ firmValue r A w F K L) :
    A (s + 1) * FK = r := by
  set a : ℝ → ℝ := fun k => disc r ^ s * (-(k - K (s + 1))) with hadef
  set b : ℝ → ℝ := fun k => disc r ^ (s + 1) *
    (A (s + 1) * (F (k, L (s + 1)) - F (K (s + 1), L (s + 1))) + (k - K (s + 1))) with hbdef
  have hval : ∀ k, firmValue r A w F (Function.update K (s + 1) k) L =
      firmValue r A w F K L + a k + b k := by
    intro k
    have hpt : (fun n => disc r ^ n * firmDividend A w F (Function.update K (s + 1) k) L n) =
        fun n => (disc r ^ n * firmDividend A w F K L n + if n = s then a k else 0) +
          if n = s + 1 then b k else 0 := by
      funext n
      simp only [firmDividend, Function.update_apply, hadef, hbdef]
      by_cases h1 : n = s
      · subst h1
        simp
        ring
      · by_cases h2 : n = s + 1
        · subst h2
          simp
          ring
        · have h3 : n + 1 ≠ s + 1 := fun h => h1 (by omega)
          simp [h1, h2]
    unfold firmValue
    rw [hpt, (hsum.add (hasSum_ite_eq s (a k)).summable).tsum_add
      (hasSum_ite_eq (s + 1) (b k)).summable, hsum.tsum_add (hasSum_ite_eq s (a k)).summable,
      tsum_ite_eq, tsum_ite_eq]
  have hmax : IsLocalMax (fun k => a k + b k) (K (s + 1)) := by
    refine Filter.Eventually.of_forall fun k => ?_
    have h1 := hopt k
    rw [hval k] at h1
    simp [hadef, hbdef]
    linarith
  have hderiv : HasDerivAt (fun k => a k + b k)
      (disc r ^ s * (-1) + disc r ^ (s + 1) * (A (s + 1) * FK + 1)) (K (s + 1)) := by
    have ha : HasDerivAt a (disc r ^ s * (-1)) (K (s + 1)) :=
      HasDerivAt.const_mul (disc r ^ s)
        (HasDerivAt.neg (HasDerivAt.sub_const (K (s + 1)) (hasDerivAt_id (K (s + 1)))))
    have hb : HasDerivAt b (disc r ^ (s + 1) * (A (s + 1) * FK + 1)) (K (s + 1)) :=
      HasDerivAt.const_mul (disc r ^ (s + 1))
        (HasDerivAt.add
          (HasDerivAt.const_mul (A (s + 1))
            (HasDerivAt.sub_const (F (K (s + 1), L (s + 1))) hFK))
          (HasDerivAt.sub_const (K (s + 1)) (hasDerivAt_id (K (s + 1)))))
    exact HasDerivAt.add ha hb
  have h0 := hmax.hasDerivAt_eq_zero hderiv
  have hd : disc r ^ s ≠ 0 := pow_ne_zero _ (disc_pos hr).ne'
  have h1 : disc r * (A (s + 1) * FK + 1) = 1 := by
    have : disc r ^ s * (disc r * (A (s + 1) * FK + 1) - 1) = 0 := by
      rw [pow_succ] at h0
      linear_combination h0
    have := (mul_eq_zero.1 this).resolve_left hd
    linarith
  have h2 := one_add_mul_disc hr
  have : A (s + 1) * FK + 1 = 1 + r := by
    linear_combination (1 + r) * h1 - (A (s + 1) * FK + 1) * h2
  linarith

/-- **Euler's theorem for constant returns**, O&R p. 103 (via §1.5.1): if `F` is homogeneous
of degree one, `F(λK, λL) = λF(K, L)` for `λ > 0`, and differentiable at `(K, L)` with
derivative `D`, then `F(K, L) = K F_K + L F_L`, where `F_K = D(1, 0)` and `F_L = D(0, 1)`. -/
theorem euler_homogeneous {F : ℝ × ℝ → ℝ} {D : ℝ × ℝ →L[ℝ] ℝ} {K L : ℝ}
    (hF : HasFDerivAt F D (K, L))
    (hhom : ∀ c : ℝ, 0 < c → F (c * K, c * L) = c * F (K, L)) :
    F (K, L) = K * D (1, 0) + L * D (0, 1) := by
  have hγ : HasDerivAt (fun c : ℝ => c • ((K, L) : ℝ × ℝ)) ((1 : ℝ) • ((K, L) : ℝ × ℝ)) 1 :=
    HasDerivAt.smul_const (hasDerivAt_id (1 : ℝ)) ((K, L) : ℝ × ℝ)
  have hF' : HasFDerivAt F D ((fun c : ℝ => c • ((K, L) : ℝ × ℝ)) 1) := by
    simpa using hF
  have h1 := hF'.comp_hasDerivAt (1 : ℝ) hγ
  have h2 : HasDerivAt (fun c : ℝ => c * F (K, L)) (1 * F (K, L)) 1 :=
    HasDerivAt.mul_const (hasDerivAt_id (1 : ℝ)) (F (K, L))
  have hev : (fun c : ℝ => c * F (K, L)) =ᶠ[𝓝 1]
      (F ∘ fun c : ℝ => c • ((K, L) : ℝ × ℝ)) := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with c hc
    simp [hhom c hc]
  have h3 := h1.unique (h2.congr_of_eventuallyEq hev.symm)
  have hKL : ((K, L) : ℝ × ℝ) = K • ((1, 0) : ℝ × ℝ) + L • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  have hD : D (K, L) = K * D (1, 0) + L * D (0, 1) := by
    rw [hKL, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [one_smul] at h3
  linarith

/-- The Fréchet derivative's value `D(1, 0)` is the partial derivative `F_K` of O&R (2.58),
so `euler_homogeneous` and `capital_foc` refer to the same number. -/
theorem hasDerivAt_capital_partial {F : ℝ × ℝ → ℝ} {D : ℝ × ℝ →L[ℝ] ℝ} {K L : ℝ}
    (hF : HasFDerivAt F D (K, L)) : HasDerivAt (fun k => F (k, L)) (D (1, 0)) K := by
  have hc : HasDerivAt (fun k : ℝ => ((k, L) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) K :=
    HasDerivAt.prodMk (hasDerivAt_id K) (hasDerivAt_const K L)
  exact hF.comp_hasDerivAt K hc

/-- The Fréchet derivative's value `D(0, 1)` is the partial derivative `F_L` of O&R (2.58). -/
theorem hasDerivAt_labor_partial {F : ℝ × ℝ → ℝ} {D : ℝ × ℝ →L[ℝ] ℝ} {K L : ℝ}
    (hF : HasFDerivAt F D (K, L)) : HasDerivAt (fun l => F (K, l)) (D (0, 1)) L := by
  have hc : HasDerivAt (fun l : ℝ => ((K, l) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) L :=
    HasDerivAt.prodMk (hasDerivAt_const L K) (hasDerivAt_id L)
  exact hF.comp_hasDerivAt L hc

/-- **Dividends under the first-order conditions**, O&R p. 104: with Euler's theorem
`F = KF_K + LF_L` and `AF_K = r`, `AF_L = w`, the dividend is
`d_s = rK_s − (K_{s+1} − K_s) = (1 + r)K_s − K_{s+1}`. -/
theorem dividend_eq_of_foc {r A w F FK FL K L K' : ℝ} (heuler : F = K * FK + L * FL)
    (hK : A * FK = r) (hL : A * FL = w) :
    A * F - w * L - (K' - K) = (1 + r) * K - K' := by
  rw [heuler]
  linear_combination K * hK + L * hL

/-- **The present value of dividends is next period's capital**, O&R (2.59), p. 104: if
`d_{s+1} = (1 + r)K_{s+1} − K_{s+2}` and `(1 + r)^{-n}K_{n+1} → 0`, the partial sums of
`Σ_{s≥1} (1 + r)^{-s} d_s` converge to `K_1`. (The telescoping partial sums converge without
any summability hypothesis.) -/
theorem tendsto_pv_capital_dividends {r : ℝ} (hr : 0 < 1 + r) {K d : ℕ → ℝ}
    (hd : ∀ s, d (s + 1) = (1 + r) * K (s + 1) - K (s + 2))
    (hK : Tendsto (fun n => disc r ^ n * K (n + 1)) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ s ∈ range n, disc r ^ (s + 1) * d (s + 1)) atTop (𝓝 (K 1)) := by
  have hc := one_add_mul_disc hr
  have hpart : ∀ n, ∑ s ∈ range n, disc r ^ (s + 1) * d (s + 1) =
      K 1 - disc r ^ n * K (n + 1) := by
    intro n
    have : ∀ s ∈ range n, disc r ^ (s + 1) * d (s + 1) =
        disc r ^ s * K (s + 1) - disc r ^ (s + 1) * K (s + 1 + 1) := by
      intro s _
      rw [hd s, pow_succ]
      linear_combination disc r ^ s * K (s + 1) * hc
    rw [sum_congr rfl this, sum_range_sub' (fun s => disc r ^ s * K (s + 1))]
    simp
  simp_rw [hpart]
  simpa using tendsto_const_nhds.sub hK

/-- O&R (2.59) with an explicit summability hypothesis: the present value of dividends
`Σ_{s≥1} (1 + r)^{-s} d_s` equals `K_1`. -/
theorem pv_capital_dividends {r : ℝ} (hr : 0 < 1 + r) {K d : ℕ → ℝ}
    (hd : ∀ s, d (s + 1) = (1 + r) * K (s + 1) - K (s + 2))
    (hK : Tendsto (fun n => disc r ^ n * K (n + 1)) atTop (𝓝 0))
    (hsum : Summable fun s => disc r ^ (s + 1) * d (s + 1)) :
    ∑' s, disc r ^ (s + 1) * d (s + 1) = K 1 :=
  tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat (tendsto_pv_capital_dividends hr hd hK)

/-- **The firm's bubble term**, O&R pp. 102–104: under the arbitrage condition (2.53) and
dividends `d_{s+1} = (1 + r)K_{s+1} − K_{s+2}`, the gap `V_s − K_{s+1}` grows at exactly the
rate of interest: `V_s − K_{s+1} = (1 + r)^s (V_0 − K_1)`. -/
theorem firm_value_sub_capital {r : ℝ} {V K d : ℕ → ℝ}
    (harb : ∀ s, (1 + r) * V s = d (s + 1) + V (s + 1))
    (hd : ∀ s, d (s + 1) = (1 + r) * K (s + 1) - K (s + 2)) (s : ℕ) :
    V s - K (s + 1) = (1 + r) ^ s * (V 0 - K 1) := by
  induction s with
  | zero => simp
  | succ n ih =>
    have h1 := harb n
    rw [hd n] at h1
    rw [pow_succ]
    linear_combination -h1 + (1 + r) * ih

/-- The discounted firm value converges to the gap between price and capital:
`(1 + r)^{-n}V_n → V_0 − K_1`, given `(1 + r)^{-n}K_{n+1} → 0`. -/
theorem tendsto_firm_bubble {r : ℝ} (hr : 0 < 1 + r) {V K d : ℕ → ℝ}
    (harb : ∀ s, (1 + r) * V s = d (s + 1) + V (s + 1))
    (hd : ∀ s, d (s + 1) = (1 + r) * K (s + 1) - K (s + 2))
    (hK : Tendsto (fun n => disc r ^ n * K (n + 1)) atTop (𝓝 0)) :
    Tendsto (fun n => disc r ^ n * V n) atTop (𝓝 (V 0 - K 1)) := by
  have hc := one_add_mul_disc hr
  have heq : ∀ n, disc r ^ n * V n = (V 0 - K 1) + disc r ^ n * K (n + 1) := by
    intro n
    have h := firm_value_sub_capital harb hd n
    have hp : disc r ^ n * (1 + r) ^ n = 1 := by rw [← mul_pow, mul_comm, hc, one_pow]
    linear_combination disc r ^ n * h + (V 0 - K 1) * hp
  simp_rw [heq]
  simpa using tendsto_const_nhds.add hK

/-- **The firm's value equals its capital**, O&R (2.59), p. 104: given (2.53), the dividend
formula implied by the first-order conditions, and `(1 + r)^{-n}K_{n+1} → 0`, the firm's
ex-dividend value is `V_0 = K_1` iff the no-bubble condition (2.57) holds. -/
theorem firm_value_eq_capital_iff {r : ℝ} (hr : 0 < 1 + r) {V K d : ℕ → ℝ}
    (harb : ∀ s, (1 + r) * V s = d (s + 1) + V (s + 1))
    (hd : ∀ s, d (s + 1) = (1 + r) * K (s + 1) - K (s + 2))
    (hK : Tendsto (fun n => disc r ^ n * K (n + 1)) atTop (𝓝 0)) :
    V 0 = K 1 ↔ Tendsto (fun n => disc r ^ n * V n) atTop (𝓝 0) := by
  have h := tendsto_firm_bubble hr harb hd hK
  constructor
  · intro e
    simpa [e] using h
  · intro e
    have := tendsto_nhds_unique h e
    linarith

/-- O&R (2.59) at every date: without a bubble, `V_s = K_{s+1}` for all `s`. -/
theorem firm_value_eq_capital {r : ℝ} (hr : 0 < 1 + r) {V K d : ℕ → ℝ}
    (harb : ∀ s, (1 + r) * V s = d (s + 1) + V (s + 1))
    (hd : ∀ s, d (s + 1) = (1 + r) * K (s + 1) - K (s + 2))
    (hK : Tendsto (fun n => disc r ^ n * K (n + 1)) atTop (𝓝 0))
    (hnb : Tendsto (fun n => disc r ^ n * V n) atTop (𝓝 0)) (s : ℕ) :
    V s = K (s + 1) := by
  have h0 := (firm_value_eq_capital_iff hr harb hd hK).2 hnb
  have := firm_value_sub_capital harb hd s
  rw [h0, sub_self, mul_zero] at this
  linarith

/-! ## Financial and human wealth -/

/-- **Financial wealth is net foreign assets plus capital**, O&R p. 104: with `x = 1` and
`V_s = K_{s+1}`, `Q_{s+1} = B_{s+1} + V_s x_{s+1} = B_{s+1} + K_{s+1}`. -/
theorem financial_wealth_eq_bonds_add_capital {B1 V0 K1 : ℝ} (hV : V0 = K1) :
    B1 + V0 * 1 = B1 + K1 := by
  rw [hV, mul_one]

/-- **The budget constraint in financial and human wealth**, O&R (2.60) with footnote 38,
p. 104: if `PV(C) = (1 + r)B_t + d_t + V_t + PV(wL − G)` (the constraint (2.55) with `x = 1`),
`d_t = Y_t − w_tL − (K_{t+1} − K_t)` and `V_t = K_{t+1}`, then
`PV(C) = (1 + r)B_t + K_t + (Y_t − w_tL) + PV(wL − G)`. -/
theorem ibc_financial_human_wealth {r B0 K0 K1 Y0 wL0 d0 V0 : ℝ} {C H : ℕ → ℝ}
    (hibc : pv r C = (1 + r) * B0 + d0 + V0 + pv r H)
    (hd0 : d0 = Y0 - wL0 - (K1 - K0)) (hV0 : V0 = K1) :
    pv r C = (1 + r) * B0 + K0 + (Y0 - wL0) + pv r H := by
  rw [hibc, hd0, hV0]
  ring

/-- **O&R (2.60)**, p. 104: if in addition the ex post return to capital between `t − 1` and
`t` was `r`, i.e. `Y_t − w_tL = rK_t`, then `PV(C) = (1 + r)Q_t + PV(wL − G)` with
`Q_t = B_t + K_t`. -/
theorem ibc_financial_human_wealth_expost {r B0 K0 K1 Y0 wL0 d0 V0 : ℝ} {C H : ℕ → ℝ}
    (hibc : pv r C = (1 + r) * B0 + d0 + V0 + pv r H)
    (hd0 : d0 = Y0 - wL0 - (K1 - K0)) (hV0 : V0 = K1) (hY : Y0 - wL0 = r * K0) :
    pv r C = (1 + r) * (B0 + K0) + pv r H := by
  rw [ibc_financial_human_wealth hibc hd0 hV0, hY]
  ring

/-- **The consumption function in financial and human wealth**, O&R (2.61), p. 104: with
`β = 1/(1 + r)` consumption is flat; if the constant level `C̄` satisfies
`PV(C̄) = (1 + r)Q_t + PV(H)`, then
`C̄ = rQ_t + (r/(1 + r)) Σ (1 + r)^{-(s-t)} H_s = rQ_t + H̃`. -/
theorem consumption_financial_human {r Q0 Cbar : ℝ} (hr : 0 < r) {H : ℕ → ℝ}
    (hibc : pv r (fun _ => Cbar) = (1 + r) * Q0 + pv r H) :
    Cbar = r * Q0 + permanent r H := by
  rw [pv_const hr] at hibc
  unfold permanent
  have h1 : (1 : ℝ) + r ≠ 0 := by linarith
  have h2 : Cbar = r / (1 + r) * ((1 + r) / r * Cbar) := by field_simp
  rw [h2, hibc]
  field_simp

/-- National saving in financial wealth, O&R p. 104: with `Y_t = rK_t + w_tL` (from
Euler's theorem plus the first-order conditions), saving `S_t = Y_t + rB_t − C_t − G_t` equals
`rQ_t + w_tL − G_t − C_t` with `Q_t = B_t + K_t`. -/
theorem saving_eq_financial {r B0 K0 Y0 wL0 C0 G0 : ℝ} (hY : Y0 = r * K0 + wL0) :
    Y0 + r * B0 - C0 - G0 = r * (B0 + K0) + wL0 - G0 - C0 := by
  rw [hY]
  ring

/-- **The permanent-income saving function**, O&R p. 105: if `S_t = rQ_t + w_tL_t − G_t − C_t`
and consumption follows (2.61), `C_t = rQ_t + (wL − G)~`, then
`S_t = [w_tL_t − (wL)~_t] − (G_t − G̃_t)`. -/
theorem saving_permanent {r Q0 S0 C0 : ℝ} {wL G : ℕ → ℝ}
    (hwL : Summable fun s => disc r ^ s * wL s) (hG : Summable fun s => disc r ^ s * G s)
    (hS : S0 = r * Q0 + wL 0 - G 0 - C0)
    (hC : C0 = r * Q0 + permanent r (fun s => wL s - G s)) :
    S0 = (wL 0 - permanent r wL) - (G 0 - permanent r G) := by
  rw [hS, hC, permanent_sub hwL hG]
  ring

/-- **The current account in terms of labour income**, O&R p. 104: with `CA_t = S_t − I_t`
and the saving function above, `CA_t = [w_tL_t − (wL)~_t] − (G_t − G̃_t) − I_t`. -/
theorem current_account_permanent {r Q0 S0 C0 I0 : ℝ} {wL G : ℕ → ℝ}
    (hwL : Summable fun s => disc r ^ s * wL s) (hG : Summable fun s => disc r ^ s * G s)
    (hS : S0 = r * Q0 + wL 0 - G 0 - C0)
    (hC : C0 = r * Q0 + permanent r (fun s => wL s - G s)) :
    S0 - I0 = (wL 0 - permanent r wL) - (G 0 - permanent r G) - I0 := by
  rw [saving_permanent hwL hG hS hC]

/-! ## Modigliani–Miller (footnote 36) -/

/-- **Modigliani–Miller**, O&R footnote 36, p. 102. Let the firm issue one-period debt
`D_{s+1}` at the end of date `s`, repaying `(1 + r)D_s` at date `s`, so equity holders receive
`d'_s = d_s + D_{s+1} − (1 + r)D_s`. If the unlevered value `V` and the equity value `V'` both
satisfy the arbitrage condition (2.53) with their dividends and the no-bubble condition
(2.57), and the firm's debt satisfies `(1 + r)^{-n}D_{n+1} → 0`, then equity plus debt equals
the unlevered value at every date: `V'_s + D_{s+1} = V_s`. -/
theorem modigliani_miller {r : ℝ} (hr : 0 < 1 + r) {V V' d d' D : ℕ → ℝ}
    (harb : ∀ s, (1 + r) * V s = d (s + 1) + V (s + 1))
    (harb' : ∀ s, (1 + r) * V' s = d' (s + 1) + V' (s + 1))
    (hd' : ∀ s, d' s = d s + D (s + 1) - (1 + r) * D s)
    (hnb : Tendsto (fun n => disc r ^ n * V n) atTop (𝓝 0))
    (hnb' : Tendsto (fun n => disc r ^ n * V' n) atTop (𝓝 0))
    (hD : Tendsto (fun n => disc r ^ n * D (n + 1)) atTop (𝓝 0)) (s : ℕ) :
    V' s + D (s + 1) = V s := by
  have hc := one_add_mul_disc hr
  set Δ : ℕ → ℝ := fun n => V n - (V' n + D (n + 1)) with hΔ
  have hstep : ∀ n, Δ (n + 1) = (1 + r) * Δ n := by
    intro n
    simp only [hΔ]
    have h1 := harb n
    have h2 := harb' n
    rw [hd' (n + 1)] at h2
    linear_combination -h1 + h2
  have hconst : ∀ n, disc r ^ n * Δ n = Δ 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hstep n, pow_succ, ← ih]
      linear_combination disc r ^ n * Δ n * hc
  have hlim : Tendsto (fun n => disc r ^ n * Δ n) atTop (𝓝 0) := by
    have := hnb.sub (hnb'.add hD)
    simp only [sub_self, add_zero] at this
    refine this.congr fun n => ?_
    simp only [hΔ]
    ring
  simp_rw [hconst] at hlim
  have h0 : Δ 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  have hd : disc r ^ s ≠ 0 := pow_ne_zero _ (disc_pos hr).ne'
  have hs : Δ s = 0 := by
    have := hconst s
    rw [h0] at this
    exact (mul_eq_zero.1 this).resolve_left hd
  simp only [hΔ] at hs
  linarith

/-- **Modigliani–Miller for the consumer**, O&R footnote 36: a consumer holding all shares and
the firm's maturing debt receives `d'_t + V'_t + (1 + r)D_t = d_t + V_t` at date `t` when
`V'_t + D_{t+1} = V_t`, so the initial wealth in (2.55) is unchanged by the firm's financing. -/
theorem modigliani_miller_consumer_wealth {r d0 d0' V0 V0' D0 D1 : ℝ}
    (hd' : d0' = d0 + D1 - (1 + r) * D0) (hV : V0' + D1 = V0) :
    d0' + V0' + (1 + r) * D0 = d0 + V0 := by
  rw [hd']
  linarith

/-! ## Appendix 2B.1: ruling out asset-price bubbles -/

/-- **The iterated asset Euler equation**, O&R Appendix 2B.1, p. 122: iterating
`V_s u'(C_s) = β(d_{s+1} + V_{s+1})u'(C_{s+1})` gives
`V_0 u'(C_0) = Σ_{s<n} β^{s+1}u'(C_{s+1})d_{s+1} + β^n u'(C_n)V_n`. -/
theorem iterated_asset_euler {β : ℝ} {u V d : ℕ → ℝ}
    (h : ∀ s, V s * u s = β * (d (s + 1) + V (s + 1)) * u (s + 1)) (n : ℕ) :
    V 0 * u 0 = ∑ s ∈ range n, β ^ (s + 1) * u (s + 1) * d (s + 1) + β ^ n * u n * V n := by
  induction n with
  | zero => simp [mul_comm]
  | succ n ih =>
    rw [sum_range_succ, ih, pow_succ]
    linear_combination β ^ n * h n

/-- **O&R (2.78)**, p. 122: if the discounted utility value of dividends is summable, the
limit `lim β^T u'(C_T)V_T` exists and
`V_0 u'(C_0) = Σ_{s≥1} β^s u'(C_s)d_s + lim β^T u'(C_T)V_T`. -/
theorem tendsto_iterated_asset_euler {β : ℝ} {u V d : ℕ → ℝ}
    (h : ∀ s, V s * u s = β * (d (s + 1) + V (s + 1)) * u (s + 1))
    (hsum : Summable fun s => β ^ (s + 1) * u (s + 1) * d (s + 1)) :
    Tendsto (fun n => β ^ n * u n * V n) atTop
      (𝓝 (V 0 * u 0 - ∑' s, β ^ (s + 1) * u (s + 1) * d (s + 1))) := by
  have heq : ∀ n, β ^ n * u n * V n =
      V 0 * u 0 - ∑ s ∈ range n, β ^ (s + 1) * u (s + 1) * d (s + 1) := by
    intro n
    linarith [iterated_asset_euler h n]
  simp_rw [heq]
  exact tendsto_const_nhds.sub hsum.hasSum.tendsto_sum_nat

/-- Discounted marginal utility under the bond Euler equation, O&R p. 123:
`u'(C_s) = β(1 + r)u'(C_{s+1})` for all `s` implies `β^T u'(C_T) = u'(C_0)(1 + r)^{-T}`. -/
theorem discounted_marginal_utility {r β : ℝ} (hr : 0 < 1 + r) {u : ℕ → ℝ}
    (hbond : ∀ s, u s = β * (1 + r) * u (s + 1)) (n : ℕ) :
    β ^ n * u n = u 0 * disc r ^ n := by
  have hc := one_add_mul_disc hr
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : β * u (n + 1) = disc r * u n := by
      rw [hbond n]
      linear_combination -(β * u (n + 1)) * hc
    rw [pow_succ, pow_succ, mul_assoc, h1]
    linear_combination disc r * ih

/-- **The utility-weighted no-bubble condition is (2.57)**, O&R p. 123: under the bond Euler
equation and `u'(C_0) > 0`, `β^T u'(C_T)V_T → 0` iff `(1 + r)^{-T}V_T → 0`. -/
theorem utility_bubble_iff {r β : ℝ} (hr : 0 < 1 + r) {u V : ℕ → ℝ} (hu0 : 0 < u 0)
    (hbond : ∀ s, u s = β * (1 + r) * u (s + 1)) :
    Tendsto (fun n => β ^ n * u n * V n) atTop (𝓝 0) ↔
      Tendsto (fun n => disc r ^ n * V n) atTop (𝓝 0) := by
  have heq : (fun n => β ^ n * u n * V n) = fun n => u 0 * (disc r ^ n * V n) := by
    funext n
    rw [discounted_marginal_utility hr hbond n]
    ring
  rw [heq]
  constructor
  · intro h
    have := h.const_mul (u 0)⁻¹
    simp only [mul_zero, ← mul_assoc, inv_mul_cancel₀ hu0.ne', one_mul] at this
    exact this
  · intro h
    simpa using h.const_mul (u 0)

/-- A **positive bubble term means the price exceeds fundamentals**, O&R p. 123: under (2.53),
`lim (1 + r)^{-T}V_T > 0` iff `V_0 > Σ_{s≥1} (1 + r)^{-s} d_s`. This is the provable content of
the book's informal argument that such a path cannot be an equilibrium. -/
theorem bubble_pos_iff_price_gt_pv {r : ℝ} (hr : 0 < 1 + r) {V d : ℕ → ℝ}
    (harb : ∀ s, (1 + r) * V s = d (s + 1) + V (s + 1))
    (hsum : Summable fun s => disc r ^ (s + 1) * d (s + 1)) {b : ℝ}
    (hb : Tendsto (fun n => disc r ^ n * V n) atTop (𝓝 b)) :
    0 < b ↔ ∑' s, disc r ^ (s + 1) * d (s + 1) < V 0 := by
  have := tendsto_nhds_unique hb (tendsto_bubble hr harb hsum)
  rw [this, sub_pos]

/-- **Free disposal excludes a negative bubble**, O&R footnote 54, p. 123: if the asset price
is never negative, any limit of `(1 + r)^{-T}V_T` is nonnegative, so
`V_0 ≥ Σ_{s≥1} (1 + r)^{-s} d_s`. -/
theorem price_ge_pv_of_nonneg {r : ℝ} (hr : 0 < 1 + r) {V d : ℕ → ℝ}
    (harb : ∀ s, (1 + r) * V s = d (s + 1) + V (s + 1))
    (hsum : Summable fun s => disc r ^ (s + 1) * d (s + 1)) (hV : ∀ s, 0 ≤ V s) :
    ∑' s, disc r ^ (s + 1) * d (s + 1) ≤ V 0 := by
  have h := tendsto_bubble hr harb hsum
  have : 0 ≤ V 0 - ∑' s, disc r ^ (s + 1) * d (s + 1) :=
    ge_of_tendsto' h fun n => mul_nonneg (pow_nonneg (disc_pos hr).le n) (hV n)
  linarith

end ObstfeldRogoff.SmallOpenEconomyDynamics.FirmsAndWealth
