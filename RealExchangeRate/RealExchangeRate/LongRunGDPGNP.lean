/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The long run: GDP and GNP with traded and nontraded goods

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.3.1,
pp. 216–220, footnotes 18–19. The world interest rate fixes the capital–labour
ratios `k_T`, `k_N` and the wage `w`, so each sector's output is its factor payments:
`Y_T = (rk_T + w)L_T` and `pY_N = (rk_N + w)L_N`. Labour is `L = L_T + L_N`, capital
is `K = k_T L_T + k_N L_N`, and national wealth is `Q = B + K`.

* **The GDP line** (O&R (4.10)): `Y_T = −[(rk_T + w)/(rk_N + w)] pY_N + (rk_T + w)L`. It is
  steeper than the GNP line iff tradables are capital-intensive, `k_T > k_N`.
* **The GNP line** (O&R (4.11)): in a steady state `C_T + pC_N = wL + rQ`, and with
  nontradables clearing, `Y_T − C_T = −rB` (footnote 18).
* **Wealth and the trade balance** (p. 220): with `k_T > k_N`, a rise in wealth that
  shifts labour into nontradables raises foreign assets by more than the rise in
  wealth, so the trade surplus falls by more than `r dQ`.
* **Gains from capital mobility** (footnote 19): any allocation of the economy's own
  capital `Q` and labour yields output worth at most `wL + rQ`, the GNP line. This
  follows from CRS profit maximisation in each sector.
-/

namespace ObstfeldRogoff.RealExchangeRate.LongRunGDPGNP

/-- **The GDP line**, O&R (4.10), p. 218: sectoral outputs equal factor payments and labour is fully
employed, so `Y_T = −[(rk_T + w)/(rk_N + w)] pY_N + (rk_T + w)L`. -/
theorem gdp_line {r w kT kN LT LN L YT pYN : ℝ} (hN : 0 < r * kN + w)
    (hT : YT = (r * kT + w) * LT) (hNp : pYN = (r * kN + w) * LN) (hL : LT + LN = L) :
    YT = -((r * kT + w) / (r * kN + w)) * pYN + (r * kT + w) * L := by
  rw [hT, hNp, ← hL]
  field_simp
  ring

/-- **Slope of the GDP line** (O&R p. 218): its slope magnitude `(rk_T + w)/(rk_N + w)` exceeds
one iff tradables are the capital-intensive sector. -/
theorem gdp_slope_gt_one_iff {r w kT kN : ℝ} (hr : 0 < r) (hN : 0 < r * kN + w) :
    1 < (r * kT + w) / (r * kN + w) ↔ kN < kT := by
  rw [one_lt_div hN]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **GDP equals factor income** (O&R p. 219): `Y_T + pY_N = rK + wL` with
`K = k_T L_T + k_N L_N`. -/
theorem gdp_eq_factor_income {r w kT kN LT LN YT pYN : ℝ}
    (hT : YT = (r * kT + w) * LT) (hNp : pYN = (r * kN + w) * LN) :
    YT + pYN = r * (kT * LT + kN * LN) + w * (LT + LN) := by
  rw [hT, hNp]; ring

/-- **The trade balance in the long run**, O&R footnote 18, p. 219: in a steady state with the GNP
line `C_T + pC_N = wL + rQ` (4.11), nontradables clearing `Y_N = C_N`, and `Q = B + K`, the trade
surplus pays the interest on foreign debt: `Y_T − C_T = −rB`. -/
theorem trade_balance_long_run {r w L Q B K YT pYN CT pCN : ℝ}
    (hgnp : CT + pCN = w * L + r * Q) (hgdp : YT + pYN = r * K + w * L) (hclear : pCN = pYN)
    (hQ : Q = B + K) : YT - CT = -(r * B) := by
  rw [hQ] at hgnp
  linarith

/-- **Foreign assets respond more than one-for-one to wealth**, O&R p. 220: capital is
`K = k_T L + (k_N − k_T)L_N` at fixed ratios, so with `Q = B + K` a change in wealth `dQ` and in
nontradables employment `dL_N` changes foreign assets by `dB = dQ − (k_N − k_T)dL_N`. -/
theorem foreign_asset_change {kT kN L dQ dLN : ℝ} :
    dQ - ((kT * L + (kN - kT) * dLN) - kT * L) = dQ - (kN - kT) * dLN := by ring

/-- **A rise in wealth raises foreign assets by more than itself** (O&R p. 220): if tradables are
capital-intensive (`k_T > k_N`) and the rise in wealth draws labour into nontradables (`dL_N > 0`),
then `dB > dQ`, and the trade surplus `Y_T − C_T = −rB` falls by more than `r dQ`. -/
theorem wealth_rise_trade_balance {r kT kN dQ dLN : ℝ} (hr : 0 < r) (hk : kN < kT)
    (hL : 0 < dLN) :
    dQ < dQ - (kN - kT) * dLN ∧ -(r * (dQ - (kN - kT) * dLN)) < -(r * dQ) := by
  have h : 0 < (kT - kN) * dLN := mul_pos (by linarith) hL
  constructor
  · nlinarith
  · nlinarith

/-- **Tradables output falls as labour moves to nontradables** (O&R p. 220):
`dY_T = −(rk_T + w)dL_N < 0` at fixed factor prices. -/
theorem tradables_output_falls {r w kT dLN : ℝ} (hT : 0 < r * kT + w) (hL : 0 < dLN) :
    -((r * kT + w) * dLN) < 0 := by
  have := mul_pos hT hL
  linarith

/-- **Gains from capital mobility**, O&R footnote 19, p. 219: if in each sector output never
exceeds factor payments at the world factor prices (CRS profit maximisation), then any use of the
economy's own capital `Q = K_T + K_N` and labour `L = L_T + L_N` yields output worth at most
`wL + rQ`: the autarky frontier lies weakly inside the GNP line. -/
theorem autarky_frontier_inside_gnp {r w KT KN LT LN YT pYN Q L : ℝ}
    (hT : YT ≤ r * KT + w * LT) (hN : pYN ≤ r * KN + w * LN) (hQ : KT + KN = Q)
    (hL : LT + LN = L) : YT + pYN ≤ w * L + r * Q := by
  rw [← hQ, ← hL]
  linarith

/-- **The frontiers touch only at the optimal ratios** (footnote 19): output equals `wL + rQ` iff
both sectors earn exactly their factor payments. -/
theorem autarky_frontier_eq_gnp_iff {r w KT KN LT LN YT pYN Q L : ℝ}
    (hT : YT ≤ r * KT + w * LT) (hN : pYN ≤ r * KN + w * LN) (hQ : KT + KN = Q)
    (hL : LT + LN = L) :
    YT + pYN = w * L + r * Q ↔ YT = r * KT + w * LT ∧ pYN = r * KN + w * LN := by
  rw [← hQ, ← hL]
  constructor
  · intro h; constructor <;> linarith
  · rintro ⟨h1, h2⟩; rw [h1, h2]; ring

end ObstfeldRogoff.RealExchangeRate.LongRunGDPGNP
