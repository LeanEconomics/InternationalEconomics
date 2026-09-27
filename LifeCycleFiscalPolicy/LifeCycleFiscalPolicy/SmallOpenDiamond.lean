/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LifeCycleFiscalPolicy.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Investment and growth in the small open OLG economy

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§3.4, "Investment and Growth", pp. 156–161 (the Feldstein–Horioka application,
pp. 161–164, is empirical and is not formalised).

Output is Cobb–Douglas, `Y = A K^α L^{1−α}` (O&R (3.34)); capital does not depreciate
and there are no adjustment costs; the young supply one unit of labour, the old none;
cohorts grow at rate `n` (O&R (3.35)); there is no government and the world rate `r`
is fixed.

* **Factor prices** (O&R (3.36)–(3.39)). The marginal-product condition `r = αAk^{α−1}`
  has the unique positive solution `k(r, A) = (αA/r)^{1/(1−α)}`, the wage is
  `w = (1 − α)A(αA/r)^{α/(1−α)}`, and the factor-price frontier satisfies `dw/dr = −k`.
* **Saving and foreign assets** (O&R (3.40)–(3.42)): `s^Y = (1 + n)(b + k)` and
  `b̄ = s̄^Y/(1 + n) − k̄`; steady-state net foreign assets grow at rate `n`, so the
  current account has the sign of `b̄`.
* **Per-capita saving and investment** (p. 159, footnotes 24–25), with their
  derivatives in `n`. The footnote-25 derivative `(n² + 4n + 2)k̄/(2 + n)²` is positive
  only for `n > √2 − 2`; we prove positivity exactly there.
* **Productivity growth** (O&R (3.43)–(3.44), footnote 27): `K/Y = α/r` at every date,
  `Y_t = N_t A_t^{1/(1−α)}(α/r)^{α/(1−α)}`, `Y_{t+1} = (1 + n)(1 + g)Y_t` and
  `I/Y = (n + g + ng)α/r`.
* **Log utility** (O&R (3.45)–(3.46), p. 161): `s^Y = βw/(1 + β)`, the old dissave
  exactly `s^Y`, `S/Y = β(1−α)/(1+β)·[1 − 1/((1+n)(1+g))]`,
  `B/Y = β(1−α)/((1+β)(1+n)(1+g)) − α/r` and `CA/Y = S/Y − I/Y = (n + g + ng)B/Y`,
  together with the comparative statics stated in the text.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond

/-! ## Factor prices -/

/-- The capital–labour ratio `k(r, A) = (αA/r)^{1/(1−α)}`, O&R (3.38), p. 157. -/
noncomputable def capLabour (α A r : ℝ) : ℝ := (α * A / r) ^ (1 / (1 - α))

/-- The real wage `w = (1 − α)A(αA/r)^{α/(1−α)}`, O&R (3.39), p. 157. -/
noncomputable def wageOf (α A r : ℝ) : ℝ := (1 - α) * A * (α * A / r) ^ (α / (1 - α))

/-- O&R (3.36), p. 157: `k(r, A)` satisfies the marginal-product condition
`αA k^{α−1} = r` (for `A, r > 0`, `0 < α < 1`). -/
theorem mpk_capLabour {α A r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hr : 0 < r) :
    α * A * capLabour α A r ^ (α - 1) = r := by
  have hx : 0 ≤ α * A / r := by positivity
  have h1 : (1 - α) ≠ 0 := by linarith
  unfold capLabour
  rw [← Real.rpow_mul hx, show 1 / (1 - α) * (α - 1) = -1 by field_simp; ring,
    Real.rpow_neg_one]
  field_simp

/-- O&R (3.36)–(3.38), p. 157: `k(r, A)` is the only positive capital–labour ratio at
which the marginal product of capital equals the world rate. -/
theorem capLabour_unique {α A r k : ℝ} (hα1 : α < 1) (hk : 0 < k) (hr : 0 < r)
    (hmpk : α * A * k ^ (α - 1) = r) : k = capLabour α A r := by
  have hkp : 0 < k ^ (α - 1) := Real.rpow_pos_of_pos hk _
  have h1 : (1 - α) ≠ 0 := by linarith
  have hαA : α * A ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmpk
    linarith
  have hx : α * A / r = k ^ (1 - α) := by
    rw [show (1 - α) = -(α - 1) by ring, Real.rpow_neg hk.le, ← hmpk]
    field_simp
    exact div_self hαA
  unfold capLabour
  rw [hx, ← Real.rpow_mul hk.le, show (1 - α) * (1 / (1 - α)) = 1 by field_simp,
    Real.rpow_one]

/-- O&R (3.37)/(3.39), p. 157: the wage equals the marginal product of labour at
`k(r, A)`, `(1 − α)A k(r, A)^α = (1 − α)A(αA/r)^{α/(1−α)}`. -/
theorem mpl_capLabour {α A r : ℝ} (hα1 : α < 1) (hA : 0 < A) (hr : 0 < r) (hα0 : 0 < α) :
    (1 - α) * A * capLabour α A r ^ α = wageOf α A r := by
  have hx : 0 ≤ α * A / r := by positivity
  have h1 : (1 - α) ≠ 0 := by linarith
  unfold capLabour wageOf
  rw [← Real.rpow_mul hx, show 1 / (1 - α) * α = α / (1 - α) by field_simp]

/-- Factor-price frontier, O&R (3.39), p. 157: along `w(r)` the wage falls with the world
rate at the rate `dw/dr = −k(r, A)` (for `A, r > 0`, `0 < α < 1`). -/
theorem wage_hasDerivAt {α A r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hr : 0 < r) :
    HasDerivAt (fun ρ => wageOf α A ρ) (-capLabour α A r) r := by
  have h1 : (1 - α) ≠ 0 := by linarith
  have hx : 0 < α * A / r := by positivity
  have hinv : HasDerivAt (fun ρ : ℝ => α * A / ρ) (α * A * (-(r ^ 2)⁻¹)) r := by
    have := (hasDerivAt_inv hr.ne').const_mul (α * A)
    simpa [div_eq_mul_inv] using this
  have hp := (hinv.rpow_const (p := α / (1 - α)) (Or.inl hx.ne')).const_mul ((1 - α) * A)
  refine hp.congr_deriv ?_
  unfold capLabour
  rw [show 1 / (1 - α) = (α / (1 - α) - 1) + 2 by field_simp; ring,
    Real.rpow_add hx, Real.rpow_two]
  generalize (α * A / r) ^ (α / (1 - α) - 1) = y
  field_simp

/-! ## Saving, investment and foreign assets with constant productivity -/

/-- O&R (3.40)–(3.41), p. 158: if aggregate saving of the young is `S^Y_t = B_{t+1} +
K_{t+1}` and `N_{t+1} = (1 + n)N_t`, then per young person
`s^Y_t = (1 + n)(b_{t+1} + k_{t+1})` with `b = B/N`, `k = K/N`. -/
theorem young_saving_per_capita {SY B' K' N N' n : ℝ} (hN : 0 < N) (hn : 0 < 1 + n)
    (hN' : N' = (1 + n) * N) (hS : SY = B' + K') :
    SY / N = (1 + n) * (B' / N' + K' / N') := by
  subst hN' hS
  field_simp

/-- O&R (3.42), p. 158: steady-state net foreign assets per worker,
`b̄ = s̄^Y/(1 + n) − k̄`. -/
theorem steady_foreign_assets {sY b k n : ℝ} (hn : 0 < 1 + n)
    (h : sY = (1 + n) * (b + k)) : b = sY / (1 + n) - k := by
  subst h
  field_simp
  ring

/-- O&R p. 159: in a steady state with `B_t = N_t b̄` and `N_{t+1} = (1 + n)N_t`, the
current account `B_{t+1} − B_t` equals `n N_t b̄`; for `n > 0` it is in surplus iff
`b̄ > 0` (and in deficit iff `b̄ < 0`). -/
theorem steady_current_account_sign {N n b : ℝ} (hN : 0 < N) (hn : 0 < n) :
    (1 + n) * N * b - N * b = n * N * b ∧ (0 < n * N * b ↔ 0 < b) ∧
      (n * N * b < 0 ↔ b < 0) := by
  have hnN : 0 < n * N := mul_pos hn hN
  refine ⟨by ring, ⟨fun h => ?_, fun h => mul_pos hnN h⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact pos_of_mul_pos_right h hnN.le
  · by_contra hb
    push Not at hb
    linarith [mul_nonneg hnN.le hb]
  · nlinarith

/-- Steady-state saving per member of the population, O&R p. 159:
`(S^Y_t + S^O_t)/(N_t + N_{t−1})` with `S^Y_t = N_t s^Y`, `S^O_t = N_{t−1}s^O`. -/
noncomputable def savingPerCapita (n sY sO : ℝ) : ℝ := (1 + n) / (2 + n) * sY + 1 / (2 + n) * sO

/-- O&R p. 159: with `N_t = (1 + n)N_{t−1}`, aggregate saving per capita is
`(1 + n)/(2 + n)·s^Y + 1/(2 + n)·s^O`. -/
theorem saving_per_capita_eq {N0 n sY sO : ℝ} (hN : 0 < N0) (hn : 0 < 1 + n) :
    ((1 + n) * N0 * sY + N0 * sO) / ((1 + n) * N0 + N0) = savingPerCapita n sY sO := by
  have h2 : 2 + n ≠ 0 := by linarith
  unfold savingPerCapita
  field_simp
  ring

/-- O&R footnote 24, p. 159: `d/dn` of steady-state saving per capita is
`(s^Y − s^O)/(2 + n)²` (holding the individual saving levels fixed, as they are
independent of `n`). -/
theorem savingPerCapita_hasDerivAt {n sY sO : ℝ} (hn : 0 < 2 + n) :
    HasDerivAt (fun m => savingPerCapita m sY sO) ((sY - sO) / (2 + n) ^ 2) n := by
  have hd : HasDerivAt (fun m : ℝ => 2 + m) 1 n := by
    simpa using (hasDerivAt_id n).const_add (2 : ℝ)
  have hn' : HasDerivAt (fun m : ℝ => 1 + m) 1 n := by
    simpa using (hasDerivAt_id n).const_add (1 : ℝ)
  have hq1 := ((hn'.div hd hn.ne').mul_const sY)
  have hq2 := (((hasDerivAt_const n (1 : ℝ)).div hd hn.ne').mul_const sO)
  refine (HasDerivAt.add hq1 hq2).congr_deriv ?_
  field_simp
  ring

/-- O&R p. 159 and footnote 24: since the old dissave (`s^O = −s^Y`), the derivative
`(s^Y − s^O)/(2 + n)²` is positive whenever the young save (`s^Y > 0`). -/
theorem savingPerCapita_deriv_pos {n sY : ℝ} (hsY : 0 < sY) (hn : 0 < 2 + n) :
    0 < (sY - -sY) / (2 + n) ^ 2 := by
  have : 0 < sY - -sY := by linarith
  positivity

/-- Steady-state investment per capita, O&R p. 159: `(1 + n)n k̄/(2 + n)`. -/
noncomputable def investPerCapita (n k : ℝ) : ℝ := (1 + n) * n * k / (2 + n)

/-- O&R p. 159: with `K_t = N_t k̄` and `N_{t+1} = (1 + n)N_t`, investment per member of
the population `(K_{t+1} − K_t)/(N_t + N_{t−1})` equals `(1 + n)n k̄/(2 + n)`. -/
theorem invest_per_capita_eq {N0 n k : ℝ} (hN : 0 < N0) (hn : 0 < 1 + n) :
    ((1 + n) * ((1 + n) * N0) * k - (1 + n) * N0 * k) / ((1 + n) * N0 + N0) =
      investPerCapita n k := by
  have h2 : 2 + n ≠ 0 := by linarith
  unfold investPerCapita
  field_simp
  ring

/-- O&R footnote 25, p. 159: `d/dn` of investment per capita is
`(n² + 4n + 2)k̄/(2 + n)²`. -/
theorem investPerCapita_hasDerivAt {n k : ℝ} (hn : 0 < 2 + n) :
    HasDerivAt (fun m => investPerCapita m k) ((n ^ 2 + 4 * n + 2) * k / (2 + n) ^ 2) n := by
  have hd : HasDerivAt (fun m : ℝ => 2 + m) 1 n := by
    simpa using (hasDerivAt_id n).const_add (2 : ℝ)
  have hn' : HasDerivAt (fun m : ℝ => 1 + m) 1 n := by
    simpa using (hasDerivAt_id n).const_add (1 : ℝ)
  have hnum := ((hn'.mul (hasDerivAt_id n)).mul_const k)
  refine (hnum.div hd hn.ne').congr_deriv ?_
  simp only [Pi.mul_apply, id]
  field_simp
  ring

/-- O&R footnote 25, p. 159, corrected: the derivative `(n² + 4n + 2)k̄/(2 + n)²` is
positive for `k̄ > 0` exactly when `n > √2 − 2` (the book says "`> 0`" without a
qualifier; it is negative for `−1 < n < √2 − 2`). -/
theorem investPerCapita_deriv_pos_iff {n k : ℝ} (hk : 0 < k) (hn : -1 < n) :
    0 < (n ^ 2 + 4 * n + 2) * k / (2 + n) ^ 2 ↔ Real.sqrt 2 - 2 < n := by
  have h2 : 0 < (2 + n) ^ 2 := by nlinarith
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [div_pos_iff_of_pos_right h2, mul_pos_iff_of_pos_right hk]
  have hfac : n ^ 2 + 4 * n + 2 = (n + 2 - Real.sqrt 2) * (n + 2 + Real.sqrt 2) := by
    nlinarith
  rw [hfac]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    have : 0 < n + 2 + Real.sqrt 2 := by linarith
    have : 0 < n + 2 - Real.sqrt 2 := by linarith
    positivity

/-! ## Productivity growth -/

namespace Growth

/-- Capital stock at date `t` when firms equate the marginal product of capital to `r`:
`K_t = N_t k(r, A_t)`, O&R (3.38), p. 157. -/
noncomputable def capital (α r : ℝ) (A N : ℕ → ℝ) (t : ℕ) : ℝ := N t * capLabour α (A t) r

/-- Output `Y_t = A_t K_t^α N_t^{1−α}` (labour force `L_t = N_t`), O&R (3.34), p. 156. -/
noncomputable def output (α r : ℝ) (A N : ℕ → ℝ) (t : ℕ) : ℝ :=
  A t * capital α r A N t ^ α * N t ^ (1 - α)

/-- O&R p. 160: under Cobb–Douglas technology, whenever `αA(K/N)^{α−1} = r` the
capital–output ratio is `K/(AK^αN^{1−α}) = α/r`. -/
theorem capital_output_ratio_of_mpk {α A K N r : ℝ} (hK : 0 < K) (hN : 0 < N)
    (hr : 0 < r) (hα0 : 0 < α) (hmpk : α * A * (K / N) ^ (α - 1) = r) :
    K / (A * K ^ α * N ^ (1 - α)) = α / r := by
  have hY : A * K ^ α * N ^ (1 - α) = A * (K / N) ^ (α - 1) * K := by
    rw [Real.div_rpow hK.le hN.le, Real.rpow_sub_one hK.ne',
      show α - 1 = -(1 - α) by ring, Real.rpow_neg hN.le]
    have : 0 < N ^ (1 - α) := Real.rpow_pos_of_pos hN _
    field_simp
  rw [hY, ← hmpk]
  have : 0 < (K / N) ^ (α - 1) := Real.rpow_pos_of_pos (div_pos hK hN) _
  have hA : A ≠ 0 := by
    rintro rfl
    simp at hmpk
    linarith
  field_simp

/-- O&R (3.43)–(3.44) text and footnote 27, p. 160: `Y_t = N_t A_t k(r,A_t)^α`. -/
theorem output_eq_labour_mul {α r : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hr : 0 < r) (hα0 : 0 < α) :
    output α r A N t = N t * A t * capLabour α (A t) r ^ α := by
  have hk : 0 ≤ capLabour α (A t) r := by unfold capLabour; positivity
  unfold output capital
  rw [Real.mul_rpow hN.le hk]
  have hNN : N t ^ α * N t ^ (1 - α) = N t := by
    rw [← Real.rpow_add hN, show α + (1 - α) = 1 by ring, Real.rpow_one]
  calc A t * (N t ^ α * capLabour α (A t) r ^ α) * N t ^ (1 - α)
      = (N t ^ α * N t ^ (1 - α)) * A t * capLabour α (A t) r ^ α := by ring
    _ = N t * A t * capLabour α (A t) r ^ α := by rw [hNN]

/-- O&R p. 160: `K_t/Y_t = α/r` at every date (not only in steady state), whatever the
path of productivity `A_t > 0` and labour force `N_t > 0`. -/
theorem capital_output_ratio {α r : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) :
    capital α r A N t / output α r A N t = α / r := by
  have hk : 0 < capLabour α (A t) r := by unfold capLabour; positivity
  unfold output
  refine capital_output_ratio_of_mpk (mul_pos hN hk) hN hr hα0 ?_
  unfold capital
  rw [show N t * capLabour α (A t) r / N t = capLabour α (A t) r by field_simp]
  exact mpk_capLabour hα0 hα1 hA hr

/-- O&R footnote 27, p. 160: `Y_t = N_t A_t^{1/(1−α)}(α/r)^{α/(1−α)}`. -/
theorem output_closed_form {α r : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) :
    output α r A N t = N t * A t ^ (1 / (1 - α)) * (α / r) ^ (α / (1 - α)) := by
  have h1 : (1 - α) ≠ 0 := by linarith
  have hx : 0 ≤ α * A t / r := by positivity
  rw [output_eq_labour_mul t hA hN hr hα0]
  unfold capLabour
  rw [← Real.rpow_mul hx, show 1 / (1 - α) * α = α / (1 - α) by field_simp,
    show α * A t / r = A t * (α / r) by ring, Real.mul_rpow hA.le (by positivity),
    show 1 / (1 - α) = 1 + α / (1 - α) by field_simp; ring, Real.rpow_add hA,
    Real.rpow_one]
  ring

/-- O&R (3.43) and footnote 27, p. 160: with `A_{t+1} = (1 + g)^{1−α}A_t` and
`N_{t+1} = (1 + n)N_t`, output grows at the gross rate `(1 + n)(1 + g)`. -/
theorem output_growth {α r n g : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) (hg : 0 < 1 + g) (hn : 0 < 1 + n)
    (hAg : A (t + 1) = (1 + g) ^ (1 - α) * A t) (hNn : N (t + 1) = (1 + n) * N t) :
    output α r A N (t + 1) = (1 + n) * (1 + g) * output α r A N t := by
  have h1 : (1 - α) ≠ 0 := by linarith
  have hA1 : 0 < A (t + 1) := by rw [hAg]; positivity
  have hN1 : 0 < N (t + 1) := by rw [hNn]; positivity
  rw [output_closed_form t hA hN hr hα0 hα1, output_closed_form (t + 1) hA1 hN1 hr hα0 hα1,
    hAg, hNn, Real.mul_rpow (by positivity) hA.le, ← Real.rpow_mul hg.le,
    show (1 - α) * (1 / (1 - α)) = 1 by field_simp, Real.rpow_one]
  ring

/-- O&R (3.44), p. 160: the investment share `I_t/Y_t = (K_{t+1} − K_t)/Y_t` equals
`(n + g + ng)α/r` at every date. -/
theorem investment_share {α r n g : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) (hg : 0 < 1 + g) (hn : 0 < 1 + n)
    (hAg : A (t + 1) = (1 + g) ^ (1 - α) * A t) (hNn : N (t + 1) = (1 + n) * N t) :
    (capital α r A N (t + 1) - capital α r A N t) / output α r A N t =
      (n + g + n * g) * (α / r) := by
  have hA1 : 0 < A (t + 1) := by rw [hAg]; positivity
  have hN1 : 0 < N (t + 1) := by rw [hNn]; positivity
  have hY : 0 < output α r A N t := by
    rw [output_closed_form t hA hN hr hα0 hα1]; positivity
  have hK0 := capital_output_ratio t hA hN hr hα0 hα1
  have hK1 := capital_output_ratio (t + 1) hA1 hN1 hr hα0 hα1
  rw [output_growth t hA hN hr hα0 hα1 hg hn hAg hNn] at hK1
  rw [div_eq_iff hY.ne'] at hK0
  rw [div_eq_iff (by positivity)] at hK1
  rw [hK0, hK1]
  field_simp
  ring

/-- Labour's share, O&R p. 160: total wages `N_t w_t` are the fraction `1 − α` of output. -/
theorem wage_bill_share {α r : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) :
    N t * wageOf α (A t) r = (1 - α) * output α r A N t := by
  rw [output_eq_labour_mul t hA hN hr hα0, ← mpl_capLabour hα1 hA hr hα0]
  ring

/-! ### Log utility -/

/-- O&R (3.45), p. 160: with log utility and wage income `w` only when young, the plan
is `c^Y = w/(1 + β)`, `c^O = (1 + r)βw/(1 + β)`, so saving of the young is
`s^Y = w − c^Y = βw/(1 + β)`. -/
theorem log_young_saving (m : LogOLG) (w : ℝ) :
    m.youngC w = w / (1 + m.β) ∧ m.oldC w = (1 + m.r) * m.β * w / (1 + m.β) ∧
      w - m.youngC w = m.β * w / (1 + m.β) := by
  have hb : 1 + m.β ≠ 0 := by linarith [m.β_pos]
  refine ⟨rfl, rfl, ?_⟩
  unfold LogOLG.youngC
  field_simp
  ring

/-- O&R p. 160 ("`s^O_t = −s^Y_{t−1}`"): the old, with no labour income, earn `r s^Y`
on their saving and consume `c^O = (1 + r)s^Y`, so their saving is exactly `−s^Y`. -/
theorem log_old_saving (m : LogOLG) (w : ℝ) :
    m.oldC w = (1 + m.r) * (w - m.youngC w) ∧
      m.r * (w - m.youngC w) - m.oldC w = -(w - m.youngC w) := by
  have hb : 1 + m.β ≠ 0 := by linarith [m.β_pos]
  have h : m.oldC w = (1 + m.r) * (w - m.youngC w) := by
    unfold LogOLG.oldC LogOLG.youngC
    field_simp
    ring
  exact ⟨h, by rw [h]; ring⟩

/-- O&R p. 160, saving of a date-`t` young person with log utility:
`s^Y_t = βw_t/(1 + β) = β(1 − α)A_t^{1/(1−α)}(α/r)^{α/(1−α)}/(1 + β)`. Neither `n` nor
`g` enters (O&R p. 161: "`g` doesn't even enter"). -/
theorem young_saving_closed_form {α β r A : ℝ} (hA : 0 < A) (hr : 0 < r) (hα0 : 0 < α)
    (hα1 : α < 1) :
    β / (1 + β) * wageOf α A r =
      β * (1 - α) * A ^ (1 / (1 - α)) * (α / r) ^ (α / (1 - α)) / (1 + β) := by
  have h1 : (1 - α) ≠ 0 := by linarith
  unfold wageOf
  rw [show α * A / r = A * (α / r) by ring, Real.mul_rpow hA.le (by positivity),
    show 1 / (1 - α) = 1 + α / (1 - α) by field_simp; ring, Real.rpow_add hA,
    Real.rpow_one]
  ring

/-- Aggregate young saving `N_t s^Y_t` with `s^Y_t = βw_t/(1 + β)`, O&R p. 160. -/
noncomputable def youngSaving (α β r : ℝ) (A N : ℕ → ℝ) (t : ℕ) : ℝ :=
  N t * (β / (1 + β) * wageOf α (A t) r)

/-- National saving `S_{t+1} = N_{t+1}s^Y_{t+1} + N_t s^O_{t+1}` with
`s^O_{t+1} = −s^Y_t`, O&R (3.46), p. 160. -/
noncomputable def saving (α β r : ℝ) (A N : ℕ → ℝ) (t : ℕ) : ℝ :=
  youngSaving α β r A N (t + 1) - youngSaving α β r A N t

/-- Net foreign assets `B_{t+1} = N_t s^Y_t − K_{t+1}`, O&R (3.40), p. 158. -/
noncomputable def foreignAssets (α β r : ℝ) (A N : ℕ → ℝ) (t : ℕ) : ℝ :=
  youngSaving α β r A N t - capital α r A N (t + 1)

/-- The steady-state saving rate `β(1−α)/(1+β)·[1 − 1/((1+n)(1+g))]`, O&R (3.46). -/
noncomputable def savingRate (α β n g : ℝ) : ℝ :=
  β * (1 - α) / (1 + β) * (1 - 1 / ((1 + n) * (1 + g)))

/-- The steady-state asset ratio `β(1−α)/((1+β)(1+n)(1+g)) − α/r`, O&R p. 161. -/
noncomputable def assetRatio (α β r n g : ℝ) : ℝ :=
  β * (1 - α) / ((1 + β) * (1 + n) * (1 + g)) - α / r

/-- O&R p. 160: young saving is the constant share `β(1 − α)/(1 + β)` of output. -/
theorem youngSaving_share {α β r : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) :
    youngSaving α β r A N t = β * (1 - α) / (1 + β) * output α r A N t := by
  have h := wage_bill_share t hA hN hr hα0 hα1
  unfold youngSaving
  calc N t * (β / (1 + β) * wageOf α (A t) r)
      = β / (1 + β) * (N t * wageOf α (A t) r) := by ring
    _ = β * (1 - α) / (1 + β) * output α r A N t := by rw [h]; ring

/-- O&R (3.46), p. 160: the national saving rate is
`S/Y = β(1−α)/(1+β)·[1 − 1/((1+n)(1+g))]` at every date. -/
theorem saving_share {α β r n g : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hβ : 0 < β) (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) (hg : 0 < 1 + g) (hn : 0 < 1 + n)
    (hAg : A (t + 1) = (1 + g) ^ (1 - α) * A t) (hNn : N (t + 1) = (1 + n) * N t) :
    saving α β r A N t / output α r A N (t + 1) = savingRate α β n g := by
  have hA1 : 0 < A (t + 1) := by rw [hAg]; positivity
  have hN1 : 0 < N (t + 1) := by rw [hNn]; positivity
  have hY : 0 < output α r A N t := by
    rw [output_closed_form t hA hN hr hα0 hα1]; positivity
  unfold saving savingRate
  rw [youngSaving_share t hA hN hr hα0 hα1, youngSaving_share (t + 1) hA1 hN1 hr hα0 hα1,
    output_growth t hA hN hr hα0 hα1 hg hn hAg hNn]
  have hb : 1 + β ≠ 0 := by linarith
  field_simp

/-- O&R p. 161: net foreign assets relative to output are
`B_{t+1}/Y_{t+1} = β(1−α)/((1+β)(1+n)(1+g)) − α/r` at every date. -/
theorem asset_share {α β r n g : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t) (hN : 0 < N t)
    (hβ : 0 < β) (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) (hg : 0 < 1 + g) (hn : 0 < 1 + n)
    (hAg : A (t + 1) = (1 + g) ^ (1 - α) * A t) (hNn : N (t + 1) = (1 + n) * N t) :
    foreignAssets α β r A N t / output α r A N (t + 1) = assetRatio α β r n g := by
  have hA1 : 0 < A (t + 1) := by rw [hAg]; positivity
  have hN1 : 0 < N (t + 1) := by rw [hNn]; positivity
  have hY : 0 < output α r A N t := by
    rw [output_closed_form t hA hN hr hα0 hα1]; positivity
  have hK1 := capital_output_ratio (t + 1) hA1 hN1 hr hα0 hα1
  have hY1 : 0 < output α r A N (t + 1) := by
    rw [output_closed_form (t + 1) hA1 hN1 hr hα0 hα1]; positivity
  rw [div_eq_iff hY1.ne'] at hK1
  unfold foreignAssets assetRatio
  rw [youngSaving_share t hA hN hr hα0 hα1, hK1,
    output_growth t hA hN hr hα0 hα1 hg hn hAg hNn]
  have hb : 1 + β ≠ 0 := by linarith
  field_simp

/-- O&R p. 161: the current account `CA_{t+1} = B_{t+2} − B_{t+1}` satisfies
`CA/Y = S/Y − I/Y = (n + g + ng)·B/Y` at every date, where `S_{t+1}` is `saving … t`
and `I_{t+1} = K_{t+2} − K_{t+1}`. -/
theorem current_account_share {α β r n g : ℝ} {A N : ℕ → ℝ} (t : ℕ) (hA : 0 < A t)
    (hN : 0 < N t) (hβ : 0 < β) (hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1) (hg : 0 < 1 + g)
    (hn : 0 < 1 + n) (hAg : ∀ s, A (s + 1) = (1 + g) ^ (1 - α) * A s)
    (hNn : ∀ s, N (s + 1) = (1 + n) * N s) :
    let Y := output α r A N (t + 1)
    (foreignAssets α β r A N (t + 1) - foreignAssets α β r A N t) / Y =
        saving α β r A N t / Y -
          (capital α r A N (t + 2) - capital α r A N (t + 1)) / Y ∧
      (foreignAssets α β r A N (t + 1) - foreignAssets α β r A N t) / Y =
        (n + g + n * g) * assetRatio α β r n g := by
  intro Y
  have hA1 : 0 < A (t + 1) := by rw [hAg]; positivity
  have hN1 : 0 < N (t + 1) := by rw [hNn]; positivity
  have hY1 : 0 < Y := by
    change 0 < output α r A N (t + 1)
    rw [output_closed_form (t + 1) hA1 hN1 hr hα0 hα1]; positivity
  refine ⟨?_, ?_⟩
  · unfold foreignAssets saving
    rw [show t + 1 + 1 = t + 2 from rfl]
    ring
  · have hB0 := asset_share t hA hN hβ hr hα0 hα1 hg hn (hAg t) (hNn t)
    have hB1 := asset_share (t + 1) hA1 hN1 hβ hr hα0 hα1 hg hn (hAg (t + 1))
      (hNn (t + 1))
    have hG := output_growth (t + 1) hA1 hN1 hr hα0 hα1 hg hn (hAg (t + 1)) (hNn (t + 1))
    rw [hG, div_eq_iff (by positivity)] at hB1
    rw [div_eq_iff hY1.ne'] at hB0
    rw [hB1, hB0]
    field_simp
    ring

/-! ### Comparative statics (O&R pp. 160–161) -/

/-- O&R p. 160: "net saving rises when `n` or `g` rises" — the steady-state saving
rate is strictly increasing in `n` (for `β > 0`, `α < 1`, `n, n' > −1`, `g > −1`). -/
theorem savingRate_strictMono_n {α β n n' g : ℝ} (hβ : 0 < β) (hα1 : α < 1)
    (hn : 0 < 1 + n) (hg : 0 < 1 + g) (hnn : n < n') :
    savingRate α β n g < savingRate α β n' g := by
  unfold savingRate
  have hc : 0 < β * (1 - α) / (1 + β) := by
    have : 0 < 1 - α := by linarith
    positivity
  have hlt : 1 / ((1 + n') * (1 + g)) < 1 / ((1 + n) * (1 + g)) :=
    one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  nlinarith

/-- O&R p. 160: the steady-state saving rate is strictly increasing in `g` as well
(`n` and `g` enter symmetrically). -/
theorem savingRate_strictMono_g {α β n g g' : ℝ} (hβ : 0 < β) (hα1 : α < 1)
    (hn : 0 < 1 + n) (hg : 0 < 1 + g) (hgg : g < g') :
    savingRate α β n g < savingRate α β n g' := by
  have h := savingRate_strictMono_n (α := α) (β := β) (g := n) hβ hα1 hg hn hgg
  unfold savingRate at h ⊢
  rwa [mul_comm (1 + g), mul_comm (1 + g')] at h

/-- O&R p. 160: "a rise in either obviously raises investment" — `(n + g + ng)α/r` is
strictly increasing in `n` (for `g > −1`) and in `g` (for `n > −1`), given `α, r > 0`. -/
theorem investShare_strictMono {α r n n' g g' : ℝ} (hα0 : 0 < α) (hr : 0 < r)
    (hn : 0 < 1 + n) (hg : 0 < 1 + g) :
    (n < n' → (n + g + n * g) * (α / r) < (n' + g + n' * g) * (α / r)) ∧
      (g < g' → (n + g + n * g) * (α / r) < (n + g' + n * g') * (α / r)) := by
  have hc : 0 < α / r := by positivity
  refine ⟨fun h => ?_, fun h => ?_⟩
  · apply mul_lt_mul_of_pos_right _ hc
    nlinarith
  · apply mul_lt_mul_of_pos_right _ hc
    nlinarith

/-- O&R p. 161: "more impatient countries (low `β`) tend to have bigger debt-output
ratios" — `B/Y` is strictly increasing in `β > 0`. -/
theorem assetRatio_strictMono_beta {α β β' r n g : ℝ} (hα1 : α < 1) (hβ : 0 < β)
    (hn : 0 < 1 + n) (hg : 0 < 1 + g) (hbb : β < β') :
    assetRatio α β r n g < assetRatio α β' r n g := by
  unfold assetRatio
  have hG : 0 < (1 + n) * (1 + g) := by positivity
  have h1 : 0 < 1 - α := by linarith
  have hβ' : 0 < β' := by linarith
  rw [show β * (1 - α) / ((1 + β) * (1 + n) * (1 + g)) =
      β / (1 + β) * ((1 - α) / ((1 + n) * (1 + g))) by field_simp,
    show β' * (1 - α) / ((1 + β') * (1 + n) * (1 + g)) =
      β' / (1 + β') * ((1 - α) / ((1 + n) * (1 + g))) by field_simp]
  have hq : β / (1 + β) < β' / (1 + β') := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have : 0 < (1 - α) / ((1 + n) * (1 + g)) := by positivity
  nlinarith

/-- O&R p. 161: "the debt-output ratio falls as the world interest rate `r` rises" —
`B/Y` is strictly increasing in `r > 0` (for `α > 0`). -/
theorem assetRatio_strictMono_r {α β r r' n g : ℝ} (hα0 : 0 < α) (hr : 0 < r)
    (hrr : r < r') : assetRatio α β r n g < assetRatio α β r' n g := by
  unfold assetRatio
  have : α / r' < α / r := div_lt_div_of_pos_left hα0 hr hrr
  linarith

/-- O&R p. 161: "the economy may be either debtor or creditor" — it is a debtor
(`B/Y < 0`) iff `β(1 − α)r < α(1 + β)(1 + n)(1 + g)`. -/
theorem assetRatio_neg_iff {α β r n g : ℝ} (hβ : 0 < β) (hr : 0 < r) (hn : 0 < 1 + n)
    (hg : 0 < 1 + g) :
    assetRatio α β r n g < 0 ↔ β * (1 - α) * r < α * ((1 + β) * (1 + n) * (1 + g)) := by
  unfold assetRatio
  have hD : 0 < (1 + β) * (1 + n) * (1 + g) := by
    have : 0 < 1 + β := by linarith
    positivity
  rw [sub_neg, div_lt_div_iff₀ hD hr]

end Growth

end ObstfeldRogoff.LifeCycleFiscalPolicy.SmallOpenDiamond
