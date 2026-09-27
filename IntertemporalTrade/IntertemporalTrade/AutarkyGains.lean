/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalTrade.Consumer

/-!
# Autarky rates and the gains from intertemporal trade

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§1.1.4–1.1.5, pp. 8–11. The book argues these results from Figure 1.1. Here the
first group is proved by revealed preference, using only strict monotonicity
and strict concavity of `u`:
* gains from trade (p. 8, p. 10): `utility_endowment_le`, `utility_endowment_lt`;
* the saving-sign lemma behind the pattern of trade (pp. 9–10): a country lends
  when the world rate exceeds its autarky rate, `saving_nonneg_of_autarky_lt`;
* welfare rises with the distance between the world and autarky rates (p. 10):
  `utility_mono_of_autarky_le`, `utility_anti_of_le_autarky`.

With a derivative `u' > 0`, the autarky rate is characterised by O&R (1.7) and is
unique, the saving and welfare results become strict, and the autarky rate
has the comparative statics of p. 10.
-/

namespace ObstfeldRogoff.IntertemporalTrade.Consumer

open Set

namespace Household

variable (h : Household)

/-- `rA` is an autarky rate: at `rA` the household chooses to consume its endowment
(O&R p. 9). -/
def IsAutarkyRate (rA : ℝ) : Prop := h.IsOptimal rA h.Y1 h.Y2

/-- **Gains from trade** (O&R Figure 1.1, p. 8): the optimum is at least as good as autarky. -/
theorem utility_endowment_le {r c1 c2 : ℝ} (ho : h.IsOptimal r c1 c2) :
    h.utility h.Y1 h.Y2 ≤ h.utility c1 c2 :=
  ho.2 _ _ (h.endowment_feasible r)

/-- **Strict gains from trade** (O&R p. 10): if the household trades at all, it is strictly
better off than in autarky. -/
theorem utility_endowment_lt {r c1 c2 : ℝ} (ho : h.IsOptimal r c1 c2) (hne : c1 ≠ h.Y1) :
    h.utility h.Y1 h.Y2 < h.utility c1 c2 := by
  refine lt_of_le_of_ne (h.utility_endowment_le ho) fun heq => hne ?_
  have hY : h.IsOptimal r h.Y1 h.Y2 :=
    ⟨h.endowment_feasible r, fun d1 d2 hd => heq ▸ ho.2 d1 d2 hd⟩
  exact (h.optimal_unique ho hY).1

/-- A plan feasible at `r` that attains the maximal utility at `r` is optimal at `r`. -/
theorem isOptimal_of_utility_eq {r c1 c2 d1 d2 : ℝ} (hd : h.IsOptimal r d1 d2)
    (hc : h.Feasible r c1 c2) (heq : h.utility d1 d2 ≤ h.utility c1 c2) :
    h.IsOptimal r c1 c2 :=
  ⟨hc, fun e1 e2 he => (hd.2 e1 e2 he).trans heq⟩

/-- **Saving-sign lemma** (O&R pp. 9–10): at a world rate above the autarky rate the
household does not borrow, `C₁ ≤ Y₁`. Revealed preference; no derivatives. -/
theorem saving_nonneg_of_autarky_lt {rA r c1 c2 : ℝ} (hA : h.IsAutarkyRate rA)
    (hlt : rA < r) (ho : h.IsOptimal r c1 c2) : c1 ≤ h.Y1 := by
  by_contra hgt
  push Not at hgt
  have hb := h.optimal_binds ho
  have hslack : c2 < h.Y2 + (1 + rA) * (h.Y1 - c1) := by rw [hb]; nlinarith
  have hfA : h.Feasible rA c1 c2 := ⟨ho.1.1, ho.1.2.1, hslack.le⟩
  have hoA : h.IsOptimal rA c1 c2 :=
    h.isOptimal_of_utility_eq hA hfA (h.utility_endowment_le ho)
  exact absurd (h.optimal_binds hoA) hslack.ne

/-- **Saving-sign lemma**, borrowing side: at a world rate below the autarky rate the
household does not lend, `Y₁ ≤ C₁`. -/
theorem saving_nonpos_of_lt_autarky {rA r c1 c2 : ℝ} (hA : h.IsAutarkyRate rA)
    (hlt : r < rA) (ho : h.IsOptimal r c1 c2) : h.Y1 ≤ c1 := by
  by_contra hgt
  push Not at hgt
  have hb := h.optimal_binds ho
  have hslack : c2 < h.Y2 + (1 + rA) * (h.Y1 - c1) := by rw [hb]; nlinarith
  have hfA : h.Feasible rA c1 c2 := ⟨ho.1.1, ho.1.2.1, hslack.le⟩
  have hoA : h.IsOptimal rA c1 c2 :=
    h.isOptimal_of_utility_eq hA hfA (h.utility_endowment_le ho)
  exact absurd (h.optimal_binds hoA) hslack.ne

/-- At the autarky rate itself the household consumes its endowment. -/
theorem optimal_at_autarky {rA c1 c2 : ℝ} (hA : h.IsAutarkyRate rA)
    (ho : h.IsOptimal rA c1 c2) : c1 = h.Y1 ∧ c2 = h.Y2 :=
  h.optimal_unique ho hA

/-- **Welfare and the world rate, lenders** (O&R p. 10): above the autarky rate, utility is
nondecreasing in `r`. -/
theorem utility_mono_of_autarky_le {rA r r' c1 c2 d1 d2 : ℝ} (hA : h.IsAutarkyRate rA)
    (hr : rA ≤ r) (hrr : r ≤ r') (hc : h.IsOptimal r c1 c2) (hd : h.IsOptimal r' d1 d2) :
    h.utility c1 c2 ≤ h.utility d1 d2 := by
  have hs : c1 ≤ h.Y1 := by
    rcases hr.lt_or_eq with hlt | rfl
    · exact h.saving_nonneg_of_autarky_lt hA hlt hc
    · exact (h.optimal_at_autarky hA hc).1.le
  have hb := h.optimal_binds hc
  exact hd.2 c1 c2 ⟨hc.1.1, hc.1.2.1, by rw [hb]; nlinarith⟩

/-- **Welfare and the world rate, borrowers** (O&R p. 10): below the autarky rate, utility is
nonincreasing in `r`. -/
theorem utility_anti_of_le_autarky {rA r r' c1 c2 d1 d2 : ℝ} (hA : h.IsAutarkyRate rA)
    (hr : r' ≤ rA) (hrr : r ≤ r') (hc : h.IsOptimal r c1 c2) (hd : h.IsOptimal r' d1 d2) :
    h.utility d1 d2 ≤ h.utility c1 c2 := by
  have hs : h.Y1 ≤ d1 := by
    rcases hr.lt_or_eq with hlt | rfl
    · exact h.saving_nonpos_of_lt_autarky hA hlt hd
    · exact (h.optimal_at_autarky hA hd).1.ge
  have hb := h.optimal_binds hd
  exact hc.2 d1 d2 ⟨hd.1.1, hd.1.2.1, by rw [hb]; nlinarith⟩

/-- Strict welfare gain for a lender: if the household strictly lends at `r` (`C₁ < Y₁`), a
higher world rate makes it strictly better off. -/
theorem utility_lt_of_lends {r r' c1 c2 d1 d2 : ℝ} (hrr : r < r') (hc : h.IsOptimal r c1 c2)
    (hs : c1 < h.Y1) (hd : h.IsOptimal r' d1 d2) : h.utility c1 c2 < h.utility d1 d2 := by
  have hb := h.optimal_binds hc
  have hslack : c2 < h.Y2 + (1 + r') * (h.Y1 - c1) := by rw [hb]; nlinarith
  have hf : h.Feasible r' c1 c2 := ⟨hc.1.1, hc.1.2.1, hslack.le⟩
  refine lt_of_le_of_ne (hd.2 c1 c2 hf) fun heq => ?_
  have ho := h.isOptimal_of_utility_eq hd hf heq.ge
  exact absurd (h.optimal_binds ho) hslack.ne

/-- Strict welfare loss for a borrower: if the household strictly borrows at `r'`
(`Y₁ < C₁`), a lower world rate makes it strictly better off. -/
theorem utility_lt_of_borrows {r r' c1 c2 d1 d2 : ℝ} (hrr : r < r') (hc : h.IsOptimal r c1 c2)
    (hd : h.IsOptimal r' d1 d2) (hs : h.Y1 < d1) : h.utility d1 d2 < h.utility c1 c2 := by
  have hb := h.optimal_binds hd
  have hslack : d2 < h.Y2 + (1 + r) * (h.Y1 - d1) := by rw [hb]; nlinarith
  have hf : h.Feasible r d1 d2 := ⟨hd.1.1, hd.1.2.1, hslack.le⟩
  refine lt_of_le_of_ne (hc.2 d1 d2 hf) fun heq => ?_
  have ho := h.isOptimal_of_utility_eq hc hf heq.ge
  exact absurd (h.optimal_binds ho) hslack.ne

/-! ### Differentiable utility -/

variable {u' : ℝ → ℝ}

/-- **The autarky interest rate** O&R (1.7), p. 9: `rA` is an autarky rate iff
`β u'(Y₂)/u'(Y₁) = 1/(1 + rA)`. -/
theorem isAutarkyRate_iff (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c)
    (hpos : ∀ c, 0 < c → 0 < u' c) {rA : ℝ} (hr : 0 < 1 + rA) :
    h.IsAutarkyRate rA ↔ h.β * u' h.Y2 / u' h.Y1 = 1 / (1 + rA) := by
  have h1 := hpos _ h.Y1_pos
  have h2 := hpos _ h.Y2_pos
  unfold IsAutarkyRate
  rw [h.isOptimal_iff_euler hu hpos, div_eq_div_iff h1.ne' hr.ne']
  constructor
  · rintro ⟨-, -, -, he⟩
    linarith
  · intro he
    exact ⟨h.Y1_pos, h.Y2_pos, by ring, by linarith⟩

/-- The autarky rate is unique. -/
theorem autarkyRate_unique (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c)
    (hpos : ∀ c, 0 < c → 0 < u' c) {rA rB : ℝ} (hA : h.IsAutarkyRate rA)
    (hB : h.IsAutarkyRate rB) : rA = rB := by
  have eA := h.euler_of_optimal hu hA
  have eB := h.euler_of_optimal hu hB
  have := mul_pos h.β_pos (hpos _ h.Y2_pos)
  nlinarith

/-- **Strict saving sign** (O&R pp. 9–10): with differentiable utility, a world rate strictly
above the autarky rate makes the household a strict lender, `C₁ < Y₁`. -/
theorem saving_pos_of_autarky_lt (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c)
    (hpos : ∀ c, 0 < c → 0 < u' c) {rA r c1 c2 : ℝ} (hA : h.IsAutarkyRate rA)
    (hlt : rA < r) (ho : h.IsOptimal r c1 c2) : c1 < h.Y1 := by
  refine lt_of_le_of_ne (h.saving_nonneg_of_autarky_lt hA hlt ho) fun heq => ?_
  have hb := h.optimal_binds ho
  rw [heq, sub_self, mul_zero, add_zero] at hb
  rw [heq, hb] at ho
  exact hlt.ne (h.autarkyRate_unique hu hpos hA ho)

/-- **Strict saving sign**, borrowing side: below the autarky rate, `Y₁ < C₁`. -/
theorem saving_neg_of_lt_autarky (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c)
    (hpos : ∀ c, 0 < c → 0 < u' c) {rA r c1 c2 : ℝ} (hA : h.IsAutarkyRate rA)
    (hlt : r < rA) (ho : h.IsOptimal r c1 c2) : h.Y1 < c1 := by
  refine lt_of_le_of_ne (h.saving_nonpos_of_lt_autarky hA hlt ho) fun heq => ?_
  have hb := h.optimal_binds ho
  rw [← heq, sub_self, mul_zero, add_zero] at hb
  rw [← heq, hb] at ho
  exact hlt.ne (h.autarkyRate_unique hu hpos ho hA)

/-- **Welfare strictly increasing above the autarky rate** (O&R p. 10: "the greater the
difference, the greater the gain"). -/
theorem utility_strictMono_of_autarky_le (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c)
    (hpos : ∀ c, 0 < c → 0 < u' c) {rA r r' c1 c2 d1 d2 : ℝ} (hA : h.IsAutarkyRate rA)
    (hr : rA ≤ r) (hrr : r < r') (hc : h.IsOptimal r c1 c2) (hd : h.IsOptimal r' d1 d2) :
    h.utility c1 c2 < h.utility d1 d2 := by
  rcases hr.lt_or_eq with hlt | rfl
  · exact h.utility_lt_of_lends hrr hc (h.saving_pos_of_autarky_lt hu hpos hA hlt hc) hd
  · obtain ⟨e1, e2⟩ := h.optimal_at_autarky hA hc
    rw [e1, e2]
    exact h.utility_endowment_lt hd (h.saving_pos_of_autarky_lt hu hpos hA hrr hd).ne

/-- **Welfare strictly decreasing below the autarky rate** (O&R p. 10). -/
theorem utility_strictAnti_of_le_autarky (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c)
    (hpos : ∀ c, 0 < c → 0 < u' c) {rA r r' c1 c2 d1 d2 : ℝ} (hA : h.IsAutarkyRate rA)
    (hr : r' ≤ rA) (hrr : r < r') (hc : h.IsOptimal r c1 c2) (hd : h.IsOptimal r' d1 d2) :
    h.utility d1 d2 < h.utility c1 c2 := by
  rcases hr.lt_or_eq with hlt | rfl
  · exact h.utility_lt_of_borrows hrr hc hd (h.saving_neg_of_lt_autarky hu hpos hA hlt hd)
  · obtain ⟨e1, e2⟩ := h.optimal_at_autarky hA hd
    rw [e1, e2]
    exact h.utility_endowment_lt hc (h.saving_neg_of_lt_autarky hu hpos hA hrr hc).ne'

end Household

/-! ### Comparative statics of the autarky rate (O&R p. 10) -/

/-- The autarky gross rate `1 + rA = u'(Y₁)/(β u'(Y₂))`, from O&R (1.7). -/
noncomputable def autarkyGross (u' : ℝ → ℝ) (β Y1 Y2 : ℝ) : ℝ := u' Y1 / (β * u' Y2)

/-- The autarky rate falls when first-period output rises. -/
theorem autarkyGross_anti_Y1 {u' : ℝ → ℝ} (hanti : StrictAntiOn u' (Ioi 0))
    (hpos : ∀ c, 0 < c → 0 < u' c) {β Y1 Y1' Y2 : ℝ} (hβ : 0 < β) (hY1 : 0 < Y1)
    (hY2 : 0 < Y2) (hlt : Y1 < Y1') :
    autarkyGross u' β Y1' Y2 < autarkyGross u' β Y1 Y2 :=
  div_lt_div_of_pos_right (hanti (mem_Ioi.2 hY1) (mem_Ioi.2 (hY1.trans hlt)) hlt)
    (mul_pos hβ (hpos _ hY2))

/-- The autarky rate rises when second-period output rises. -/
theorem autarkyGross_mono_Y2 {u' : ℝ → ℝ} (hanti : StrictAntiOn u' (Ioi 0))
    (hpos : ∀ c, 0 < c → 0 < u' c) {β Y1 Y2 Y2' : ℝ} (hβ : 0 < β) (hY1 : 0 < Y1)
    (hY2 : 0 < Y2) (hlt : Y2 < Y2') :
    autarkyGross u' β Y1 Y2 < autarkyGross u' β Y1 Y2' := by
  unfold autarkyGross
  have h1 := hpos _ hY1
  have h2 := hpos _ (hY2.trans hlt)
  exact div_lt_div_of_pos_left h1 (mul_pos hβ h2)
    (mul_lt_mul_of_pos_left (hanti (mem_Ioi.2 hY2) (mem_Ioi.2 (hY2.trans hlt)) hlt) hβ)

/-- The autarky rate falls when the household becomes more patient (higher `β`). -/
theorem autarkyGross_anti_beta {u' : ℝ → ℝ} (hpos : ∀ c, 0 < c → 0 < u' c)
    {β β' Y1 Y2 : ℝ} (hβ : 0 < β) (hY1 : 0 < Y1) (hY2 : 0 < Y2) (hlt : β < β') :
    autarkyGross u' β' Y1 Y2 < autarkyGross u' β Y1 Y2 := by
  unfold autarkyGross
  have h2 := hpos _ hY2
  exact div_lt_div_of_pos_left (hpos _ hY1) (mul_pos hβ h2)
    (mul_lt_mul_of_pos_right hlt h2)

end ObstfeldRogoff.IntertemporalTrade.Consumer
