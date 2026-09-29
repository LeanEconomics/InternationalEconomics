/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MoneyExchangeRates.MonetaryBubbles

/-!
# Cash-in-advance models of money demand

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §8.3.6
(pp. 547–550), Appendix 8A (pp. 595–597), Appendix 8B and §8.7.6.1 (pp. 597–599, 594) and
Exercise 4 (p. 601).

The household maximises `Σβ^s u(C_s)` (57) subject to (34) and the cash-in-advance constraints
(58) `M_{s−1} ≥ P_sC_s`. We allow time-varying real rates (Exercise 4): the bond bought at `s`
pays `R_s = 1 + r_{s+1}`. With `n_s = M_s/P_s` and `ρ_s = P_s/P_{s+1}`, wealth
`A_s = (1+r_s)B_s + M_{s−1}/P_s` obeys `A_{s+1} = R_s(A_s + y_s − C_s − ι_s n_s)`,
`ι_s = 1 − ρ_s/R_s = i_{s+1}/(1+i_{s+1})`. We prove:

* **(a)** with `u` increasing and `i > 0` the constraint binds (`cia_binds`);
* the Euler equation `ρ_s u'(C_{s+1}) = R_s βρ_{s+1} u'(C_{s+2})` DERIVED from optimality, the
  date-0 condition (`C_t` is predetermined), and the necessity of the transversality condition;
* **sufficiency** of these conditions for concave `u` against every no-Ponzi rival, and hence
  an exact characterisation of the optimum (`cia_optimal_iff`);
* (59), constant velocity, **(60) and Exercise 4** (`euler_60_iff`: (60) holds with the
  time-varying `r_{s+1}`), the stationary case, and the undistorted Euler equation under the
  Helpman–Lucas timing;
* Appendix 8A: PPP from the law of one price, (130) (with the optimality of the CES demands),
  (131), `r = (1−β)/β`, and a **sign correction**: the government budget constraints must read
  `T_t = −(ΔM_H + ΔM^*_H)/P_t` (as in (43)); the printed `+` sign is inconsistent with the
  private budgets and market clearing unless total money is constant;
* Appendix 8B's balance-sheet mechanics (sterilised = nonsterilised + open-market sale) and the
  forward-intervention identity of §8.7.6.1 from covered interest parity.
-/

namespace ObstfeldRogoff.MoneyExchangeRates.CashInAdvance

open Real Filter Topology Set
open ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility

/-! ## The household's problem with a cash-in-advance constraint -/

/-- Wealth in the cash-in-advance model with (possibly time-varying) real interest rates
(O&R (34), p. 548, and Exercise 4): `A_s = (1 + r_s)B_s + M_{s−1}/P_s` evolves as
`A_{s+1} = R_s (A_s + y_s − C_s − ι_s n_s)`, where `R_s = 1 + r_{s+1}` is the gross return on a
bond bought at `s`, `n_s = M_s/P_s` the real balances acquired at `s` and
`ι_s = 1 − (P_s/P_{s+1})/R_s` their user cost. -/
noncomputable def ciaWealth (R : ℕ → ℝ) (A0 : ℝ) (y ι C n : ℕ → ℝ) : ℕ → ℝ
  | 0 => A0
  | s + 1 => R s * (ciaWealth R A0 y ι C n s + y s - C s - ι s * n s)

/-- The market discount factor `Π_{j<T} R_j^{−1}` (O&R p. 534, Exercise 4). -/
noncomputable def ciaDisc (R : ℕ → ℝ) (T : ℕ) : ℝ := ∏ j ∈ Finset.range T, (R j)⁻¹

/-- End-of-period financial assets in present value, `Π_{j<T}R_j^{−1}(B_{T+1} + M_T/P_T)`,
the object of the book's transversality condition (O&R p. 534) in the CIA model. -/
noncomputable def ciaAssets (R : ℕ → ℝ) (A0 : ℝ) (y ι C n : ℕ → ℝ) (T : ℕ) : ℝ :=
  ciaDisc R T * (ciaWealth R A0 y ι C n T + y T - C T)

/-- An admissible plan in the CIA model (O&R (57)–(58), p. 548): positive consumption,
nonnegative money, the cash-in-advance constraints `P_0C_0 ≤ M_{−1}` (`C_0 ≤ c₀`) and
`P_{s+1}C_{s+1} ≤ M_s` (`C_{s+1} ≤ ρ_s n_s`, `ρ_s = P_s/P_{s+1}`), summable utility and no Ponzi
scheme (`liminf` of `ciaAssets` at least zero). -/
def CIAAdmissible (u : ℝ → ℝ) (β : ℝ) (R : ℕ → ℝ) (A0 c0 : ℝ) (y ι ρ C n : ℕ → ℝ) : Prop :=
  (∀ s, 0 < C s) ∧ (∀ s, 0 ≤ n s) ∧ C 0 ≤ c0 ∧ (∀ s, C (s + 1) ≤ ρ s * n s) ∧
    Summable (fun s => β ^ s * u (C s)) ∧
    ∀ ε > 0, ∀ᶠ T in atTop, -ε < ciaAssets R A0 y ι C n T

/-- An optimal plan in the CIA model (O&R p. 548). -/
def CIAOptimal (u : ℝ → ℝ) (β : ℝ) (R : ℕ → ℝ) (A0 c0 : ℝ) (y ι ρ C n : ℕ → ℝ) : Prop :=
  CIAAdmissible u β R A0 c0 y ι ρ C n ∧ ∀ C' n', CIAAdmissible u β R A0 c0 y ι ρ C' n' →
    ∑' s, β ^ s * u (C' s) ≤ ∑' s, β ^ s * u (C s)

/-- The transversality condition of the CIA model, in its exact (`liminf ≤ 0`) form.
Context: O&R §8.3.6, pp. 547–550. -/
def CIATransversality (R : ℕ → ℝ) (A0 : ℝ) (y ι C n : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ᶠ T in atTop, ciaAssets R A0 y ι C n T < ε

/-- The law of motion of CIA wealth (O&R (34)). -/
theorem ciaWealth_succ (R : ℕ → ℝ) (A0 : ℝ) (y ι C n : ℕ → ℝ) (s : ℕ) :
    ciaWealth R A0 y ι C n (s + 1) = R s * (ciaWealth R A0 y ι C n s + y s - C s - ι s * n s) :=
  rfl

/-- `Π_{j<T+1} R_j^{−1} = (Π_{j<T} R_j^{−1}) R_T^{−1}`.
Context: O&R §8.3.6, pp. 547–550. -/
theorem ciaDisc_succ (R : ℕ → ℝ) (T : ℕ) : ciaDisc R (T + 1) = ciaDisc R T * (R T)⁻¹ := by
  simp only [ciaDisc, Finset.prod_range_succ]

/-- The discount factor is positive when gross returns are.
Context: O&R §8.3.6, pp. 547–550. -/
theorem ciaDisc_pos {R : ℕ → ℝ} (hR : ∀ s, 0 < R s) (T : ℕ) : 0 < ciaDisc R T :=
  Finset.prod_pos fun j _ => inv_pos.2 (hR j)

/-- **The budget constraint (34) in wealth form with time-varying rates** (O&R p. 548 and
Exercise 4): with `N_s` the money brought into `s` and the bond bought at `s` paying `R_s`,
`B_{s+1} + N_{s+1}/P_s = R_{s−1}B_s + N_s/P_s + Y_s − C_s − T_s` makes
`R_{s−1}B_s + N_s/P_s` equal to `ciaWealth`. -/
theorem ciaWealth_of_budget {R P B N Y T C : ℕ → ℝ} {Rm1 : ℝ} (hR : ∀ s, 0 < R s)
    (hP : ∀ s, 0 < P s)
    (hbud : ∀ s, B (s + 1) + N (s + 1) / P s =
      (if s = 0 then Rm1 else R (s - 1)) * B s + N s / P s + Y s - C s - T s) (s : ℕ) :
    (if s = 0 then Rm1 else R (s - 1)) * B s + N s / P s =
      ciaWealth R (Rm1 * B 0 + N 0 / P 0) (fun s => Y s - T s)
        (fun s => 1 - P s / P (s + 1) / R s) C (fun s => N (s + 1) / P s) s := by
  induction s with
  | zero => simp [ciaWealth]
  | succ s ih =>
    rw [ciaWealth_succ, ← ih]
    have h := hbud s
    have hPs := (hP s).ne'
    have hPs1 := (hP (s + 1)).ne'
    have hRs := (hR s).ne'
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    field_simp
    field_simp at h
    linear_combination R s * P (s + 1) * h

/-- **Finite-horizon present-value identity** in the CIA model:
`Σ_{s<T} D_s(C_s + ι_s n_s) + D_T A_T = A_0 + Σ_{s<T} D_s y_s` (O&R p. 534). -/
theorem cia_pv_identity {R : ℕ → ℝ} (hR : ∀ s, 0 < R s) (A0 : ℝ) (y ι C n : ℕ → ℝ) (T : ℕ) :
    ∑ s ∈ Finset.range T, ciaDisc R s * (C s + ι s * n s) +
        ciaDisc R T * ciaWealth R A0 y ι C n T =
      A0 + ∑ s ∈ Finset.range T, ciaDisc R s * y s := by
  induction T with
  | zero => simp [ciaDisc, ciaWealth]
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ciaWealth_succ, ciaDisc_succ]
    have h1 : (R T)⁻¹ * R T = 1 := inv_mul_cancel₀ (hR T).ne'
    linear_combination ih + ciaDisc R T *
      (ciaWealth R A0 y ι C n T + y T - C T - ι T * n T) * h1

/-- End-of-period assets in terms of next period's wealth:
`D_T(A_T + y_T − C_T) = D_{T+1}A_{T+1} + D_T ι_T n_T` (O&R p. 534). -/
theorem ciaAssets_eq {R : ℕ → ℝ} (hR : ∀ s, 0 < R s) (A0 : ℝ) (y ι C n : ℕ → ℝ) (T : ℕ) :
    ciaAssets R A0 y ι C n T = ciaDisc R (T + 1) * ciaWealth R A0 y ι C n (T + 1) +
      ciaDisc R T * (ι T * n T) := by
  unfold ciaAssets
  rw [ciaWealth_succ, ciaDisc_succ]
  have h1 : (R T)⁻¹ * R T = 1 := inv_mul_cancel₀ (hR T).ne'
  linear_combination (-(ciaDisc R T * (ciaWealth R A0 y ι C n T + y T - C T - ι T * n T))) * h1

/-- Plans agreeing before `k` have the same CIA wealth at `k`.
Context: O&R §8.3.6, pp. 547–550. -/
theorem ciaWealth_congr_before {R : ℕ → ℝ} {A0 : ℝ} {y ι C n C' n' : ℕ → ℝ} {k : ℕ}
    (hC : ∀ t, t < k → C t = C' t) (hn : ∀ t, t < k → n t = n' t) :
    ciaWealth R A0 y ι C n k = ciaWealth R A0 y ι C' n' k := by
  have key : ∀ j, j ≤ k → ciaWealth R A0 y ι C n j = ciaWealth R A0 y ι C' n' j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [ciaWealth_succ, ciaWealth_succ, ih (by omega), hC j (by omega), hn j (by omega)]
  exact key k le_rfl

/-- Plans agreeing from `k` on with equal wealth at `k` have equal wealth afterwards.
Context: O&R §8.3.6, pp. 547–550. -/
theorem ciaWealth_congr_after {R : ℕ → ℝ} {A0 : ℝ} {y ι C n C' n' : ℕ → ℝ} {k : ℕ}
    (hk : ciaWealth R A0 y ι C n k = ciaWealth R A0 y ι C' n' k)
    (hC : ∀ s, k ≤ s → C s = C' s) (hn : ∀ s, k ≤ s → n s = n' s) (j : ℕ) :
    ciaWealth R A0 y ι C n (k + j) = ciaWealth R A0 y ι C' n' (k + j) := by
  induction j with
  | zero => exact hk
  | succ j ih =>
    rw [← add_assoc, ciaWealth_succ, ciaWealth_succ, ih, hC _ (by omega), hn _ (by omega)]

/-- **Finite perturbations of a CIA optimum**: if a family of plans differs from the optimum only
on a finite set `S` of dates and is admissible (with the same assets eventually) for `ε` near
`0` along a filter `l`, then the utility of the perturbed dates does not exceed its value at the
optimum along `l`.
Context: O&R §8.3.6, pp. 547–550. -/
theorem cia_perturb_le {u : ℝ → ℝ} {β : ℝ} {R : ℕ → ℝ} {A0 c0 : ℝ} {y ι ρ C n : ℕ → ℝ}
    (hopt : CIAOptimal u β R A0 c0 y ι ρ C n) (S : Finset ℕ) (DC Dn : ℝ → ℕ → ℝ)
    (hoffC : ∀ ε t, t ∉ S → DC ε t = C t) {l : Filter ℝ}
    (hgood : ∀ᶠ ε in l, (∀ t, 0 < DC ε t) ∧ (∀ t, 0 ≤ Dn ε t) ∧ DC ε 0 ≤ c0 ∧
      (∀ t, DC ε (t + 1) ≤ ρ t * Dn ε t) ∧
      ∀ᶠ T in atTop, ciaAssets R A0 y ι (DC ε) (Dn ε) T = ciaAssets R A0 y ι C n T) :
    ∀ᶠ ε in l, ∑ t ∈ S, β ^ t * u (DC ε t) ≤ ∑ t ∈ S, β ^ t * u (C t) := by
  obtain ⟨⟨_, _, _, _, hsum, hnp⟩, hmax⟩ := hopt
  filter_upwards [hgood] with ε ⟨hC, hn, h0, hcia, hw⟩
  obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hsum S (g := fun t => β ^ t * u (DC ε t))
    fun t ht => by simp only [hoffC ε t ht]
  have hadm : CIAAdmissible u β R A0 c0 y ι ρ (DC ε) (Dn ε) := by
    refine ⟨hC, hn, h0, hcia, h1, fun e he => ?_⟩
    filter_upwards [hnp e he, hw] with T hT hT'
    rw [hT']; exact hT
  have hle := hmax _ _ hadm
  rw [h2, Finset.sum_sub_distrib] at hle
  linarith

/-- **(a) The cash-in-advance constraint binds when the nominal interest rate is positive**
(O&R p. 548: "people never hold money in excess of next period's consumption requirements when
they could instead earn a higher return by lending the money out"): at an optimum with
`u` strictly increasing and `ι_s > 0` (`i_{s+1} > 0`), `P_{s+1}C_{s+1} = M_s`. Proof: lend the
excess `δ` and consume the return `R_s ι_s δ` at `s + 1`. -/
theorem cia_binds {u : ℝ → ℝ} {β : ℝ} {R : ℕ → ℝ} {A0 c0 : ℝ} {y ι ρ C n : ℕ → ℝ}
    (hβ : 0 < β) (hR : ∀ s, 0 < R s) (hιdef : ∀ s, ι s = 1 - ρ s / R s)
    (hmono : StrictMonoOn u (Set.Ioi 0)) (hopt : CIAOptimal u β R A0 c0 y ι ρ C n) (s : ℕ)
    (hι : 0 < ι s) : C (s + 1) = ρ s * n s := by
  obtain ⟨⟨hC, hn, hC0, hcia, hsum, hnp⟩, hmax⟩ := hopt
  by_contra hne
  have hlt : C (s + 1) < ρ s * n s := lt_of_le_of_ne (hcia s) hne
  set σ := ρ s * n s - C (s + 1) with hσ
  have hσ0 : 0 < σ := by linarith
  set δ := σ / R s with hδ
  have hδ0 : 0 < δ := div_pos hσ0 (hR s)
  have hRι : R s * ι s + ρ s = R s := by rw [hιdef]; field_simp [(hR s).ne']; ring
  set C' : ℕ → ℝ := fun t => if t = s + 1 then C (s + 1) + R s * ι s * δ else C t with hC'
  set n' : ℕ → ℝ := fun t => if t = s then n s - δ else n t with hn'
  have hne1 : s + 1 ≠ s := Nat.succ_ne_self s
  have hwealth : ∀ j, ciaWealth R A0 y ι C' n' (s + 2 + j) =
      ciaWealth R A0 y ι C n (s + 2 + j) := by
    intro j
    refine ciaWealth_congr_after ?_ (fun t ht => by simp [hC']; omega)
      (fun t ht => by simp [hn']; omega) j
    have hbef : ciaWealth R A0 y ι C' n' s = ciaWealth R A0 y ι C n s :=
      ciaWealth_congr_before (fun t ht => by simp [hC']; omega) (fun t ht => by simp [hn']; omega)
    rw [show s + 2 = s + 1 + 1 by ring, ciaWealth_succ, ciaWealth_succ (C := C), ciaWealth_succ,
      ciaWealth_succ (C := C), hbef]
    have hne2 : s ≠ s + 1 := by omega
    simp only [hC', hn', ↓reduceIte, hne1, hne2]
    ring
  have hoff : ∀ t, t ∉ ({s + 1} : Finset ℕ) → C' t = C t := fun t ht => by
    simp only [Finset.mem_singleton] at ht; simp [hC', ht]
  obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hsum {s + 1} (g := fun t => β ^ t * u (C' t))
    fun t ht => by simp only [hoff t ht]
  have hgain : 0 < R s * ι s * δ := by have := hR s; positivity
  have hadm : CIAAdmissible u β R A0 c0 y ι ρ C' n' := by
    refine ⟨fun t => ?_, fun t => ?_, ?_, fun t => ?_, h1, fun e he => ?_⟩
    · by_cases ht : t = s + 1
      · subst ht; simp only [hC', ↓reduceIte]; linarith [hC (s + 1)]
      · simp only [hC', ht, ↓reduceIte]; exact hC t
    · by_cases ht : t = s
      · subst ht; simp only [hn', ↓reduceIte]
        have : δ ≤ n t := by
          rw [hδ, div_le_iff₀ (hR t)]
          have h3 : ρ t < R t := by
            have := hιdef t; rw [this] at hι
            rw [sub_pos, div_lt_one (hR t)] at hι; exact hι
          have := hC (t + 1)
          nlinarith [hn t]
        linarith
      · simp only [hn', ht, ↓reduceIte]; exact hn t
    · simp only [hC', show (0 : ℕ) ≠ s + 1 from (Nat.succ_ne_zero s).symm, ↓reduceIte]; exact hC0
    · by_cases ht : t = s
      · subst ht
        simp only [hC', hn', ↓reduceIte]
        have : ρ t * (n t - δ) = C (t + 1) + σ - ρ t * δ := by rw [hσ]; ring
        rw [this]
        have : σ = R t * δ := by rw [hδ]; field_simp [(hR t).ne']
        nlinarith [hRι]
      · by_cases ht1 : t + 1 = s + 1
        · omega
        · simp only [hC', hn', ht, ht1, ↓reduceIte]; exact hcia t
    · filter_upwards [hnp e he, eventually_ge_atTop (s + 2)] with T hT hT2
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hT2
      unfold ciaAssets at hT ⊢
      have hc : C' (s + 2 + j) = C (s + 2 + j) := by simp [hC']; omega
      rw [hwealth j, hc]
      exact hT
  have hle := hmax _ _ hadm
  rw [h2, Finset.sum_singleton] at hle
  have hu : u (C (s + 1)) < u (C' (s + 1)) := by
    simp only [hC', ↓reduceIte]
    exact hmono (hC (s + 1)) (by simp only [Set.mem_Ioi]; linarith [hC (s + 1)]) (by linarith)
  have hb := pow_pos hβ (s + 1)
  have := mul_lt_mul_of_pos_left hu hb
  linarith

/-- The derivative of `ε ↦ u(c + εa)` at `0` (used for the CIA first-order conditions).
Context: O&R §8.3.6, pp. 547–550. -/
theorem hasDerivAt_affine {u u' : ℝ → ℝ} {c a : ℝ} (hu : HasDerivAt u (u' c) c) :
    HasDerivAt (fun ε => u (c + ε * a)) (u' c * a) 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => c + ε * a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const a).const_add c
  have h2 : HasDerivAt u (u' c) (c + 0 * a) := by simpa using hu
  exact h2.comp (0 : ℝ) h1

/-- **The CIA consumption Euler equation, derived from optimality** (O&R pp. 548–549, and
Exercise 4 with time-varying rates): at an optimum,
`(P_s/P_{s+1}) u'(C_{s+1}) = R_s β (P_{s+1}/P_{s+2}) u'(C_{s+2})` for every `s`, i.e. the
book's `(P_{s−1}/P_s)u'(C_s) = (1 + r_s)(P_s/P_{s+1})βu'(C_{s+1})` for `s > t`. Proof: hold
`ε/ρ_s` less money at `s` (consume `ε` less at `s + 1`), lend it, and hold `R_s ε/ρ_s` more money
at `s + 1` (consume `ρ_{s+1}R_s ε/ρ_s` more at `s + 2`); wealth is unchanged from `s + 3` on. -/
theorem cia_euler_of_optimal {u u' : ℝ → ℝ} {β : ℝ} {R : ℕ → ℝ} {A0 c0 : ℝ}
    {y ι ρ C n : ℕ → ℝ} (hβ : 0 < β) (hR : ∀ s, 0 < R s) (hρ : ∀ s, 0 < ρ s)
    (hιdef : ∀ s, ι s = 1 - ρ s / R s) (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hopt : CIAOptimal u β R A0 c0 y ι ρ C n) (s : ℕ) :
    ρ s * u' (C (s + 1)) = R s * β * ρ (s + 1) * u' (C (s + 2)) := by
  have hC := hopt.1.1
  have hn := hopt.1.2.1
  have hcia := hopt.1.2.2.2.1
  have hC0 := hopt.1.2.2.1
  set k := R s / ρ s with hk
  set DC : ℝ → ℕ → ℝ := fun ε t => if t = s + 1 then C (s + 1) + ε * (-1) else
    if t = s + 2 then C (s + 2) + ε * (ρ (s + 1) * k) else C t with hDC
  set Dn : ℝ → ℕ → ℝ := fun ε t => if t = s then n s - ε / ρ s else
    if t = s + 1 then n (s + 1) + ε * k else n t with hDn
  have h12 : s + 1 ≠ s + 2 := by omega
  have hDs1 : ∀ ε, DC ε (s + 1) = C (s + 1) + ε * (-1) := fun ε => by simp [hDC]
  have hDs2 : ∀ ε, DC ε (s + 2) = C (s + 2) + ε * (ρ (s + 1) * k) := fun ε => by simp [hDC]
  have hoff : ∀ ε t, t ∉ ({s + 1, s + 2} : Finset ℕ) → DC ε t = C t := fun ε t ht => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    simp [hDC, ht.1, ht.2]
  have hnpos : ∀ t, 0 < n t := fun t => by
    have := hcia t; have := hC (t + 1); have := hρ t
    by_contra h; push Not at h; nlinarith [hn t]
  have hw : ∀ ε j, ciaWealth R A0 y ι (DC ε) (Dn ε) (s + 3 + j) =
      ciaWealth R A0 y ι C n (s + 3 + j) := by
    intro ε j
    refine ciaWealth_congr_after ?_ (fun t ht => hoff ε t (by simp; omega))
      (fun t ht => by
        have h1 : t ≠ s := by omega
        have h2 : t ≠ s + 1 := by omega
        simp [hDn, h1, h2]) j
    have hbef : ciaWealth R A0 y ι (DC ε) (Dn ε) s = ciaWealth R A0 y ι C n s :=
      ciaWealth_congr_before (fun t ht => hoff ε t (by simp; omega))
        (fun t ht => by
          have h1 : t ≠ s := by omega
          have h2 : t ≠ s + 1 := by omega
          simp [hDn, h1, h2])
    have hs0 : DC ε s = C s := hoff ε s (by simp)
    have hn2 : Dn ε (s + 2) = n (s + 2) := by simp [hDn]
    rw [show s + 3 = s + 2 + 1 by ring, ciaWealth_succ, ciaWealth_succ (C := C),
      show s + 2 = s + 1 + 1 by ring, ciaWealth_succ, ciaWealth_succ (C := C), ciaWealth_succ,
      ciaWealth_succ (C := C), hbef, hs0, show s + 1 + 1 = s + 2 by ring, hDs2, hDs1, hn2]
    have e1 : Dn ε s = n s - ε / ρ s := by simp [hDn]
    have e2 : Dn ε (s + 1) = n (s + 1) + ε * k := by simp [hDn]
    rw [e1, e2, hιdef s, hιdef (s + 1), hk]
    have := (hρ s).ne'
    have := (hR s).ne'
    have := (hR (s + 1)).ne'
    field_simp
    ring
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C (s + 1) + ε * (-1) ∧
      0 < C (s + 2) + ε * (ρ (s + 1) * k) ∧ 0 ≤ n s - ε / ρ s ∧ 0 ≤ n (s + 1) + ε * k := by
    have c1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C (s + 1) + ε * (-1) :=
      ((by fun_prop : Continuous fun ε : ℝ => C (s + 1) + ε * (-1)).tendsto 0).eventually
        (lt_mem_nhds (by simpa using hC (s + 1)))
    have c2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C (s + 2) + ε * (ρ (s + 1) * k) :=
      ((by fun_prop : Continuous fun ε : ℝ => C (s + 2) + ε * (ρ (s + 1) * k)).tendsto 0).eventually
        (lt_mem_nhds (by simpa using hC (s + 2)))
    have c3 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < n s - ε / ρ s :=
      ((by fun_prop : Continuous fun ε : ℝ => n s - ε / ρ s).tendsto 0).eventually
        (lt_mem_nhds (by simpa using hnpos s))
    have c4 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < n (s + 1) + ε * k :=
      ((by fun_prop : Continuous fun ε : ℝ => n (s + 1) + ε * k).tendsto 0).eventually
        (lt_mem_nhds (by simpa using hnpos (s + 1)))
    filter_upwards [c1, c2, c3, c4] with ε h1 h2 h3 h4 using ⟨h1, h2, h3.le, h4.le⟩
  have hle := cia_perturb_le hopt {s + 1, s + 2} DC Dn hoff (l := 𝓝 0) (by
    filter_upwards [hev] with ε ⟨h1, h2, h3, h4⟩
    refine ⟨fun t => ?_, fun t => ?_, ?_, fun t => ?_, ?_⟩
    · by_cases ht : t = s + 1
      · rw [ht, hDs1]; exact h1
      by_cases ht2 : t = s + 2
      · rw [ht2, hDs2]; exact h2
      rw [hoff ε t (by simp [ht, ht2])]; exact hC t
    · by_cases ht : t = s
      · subst ht; simpa [hDn] using h3
      by_cases ht1 : t = s + 1
      · subst ht1; simpa [hDn] using h4
      simpa [hDn, ht, ht1] using hn t
    · rw [hoff ε 0 (by simp)]; exact hC0
    · by_cases ht : t = s
      · subst ht
        have e2 : Dn ε t = n t - ε / ρ t := by simp [hDn]
        rw [hDs1, e2]
        have := hcia t
        have := (hρ t).ne'
        rw [mul_sub, mul_div_cancel₀ _ this]
        linarith
      by_cases ht1 : t = s + 1
      · subst ht1
        have e2 : Dn ε (s + 1) = n (s + 1) + ε * k := by simp [hDn]
        rw [show s + 1 + 1 = s + 2 by ring, hDs2, e2]
        have := hcia (s + 1)
        rw [show s + 1 + 1 = s + 2 by ring] at this
        nlinarith
      · have e1 : DC ε (t + 1) = C (t + 1) := hoff ε (t + 1) (by simp; omega)
        have e2 : Dn ε t = n t := by simp [hDn, ht, ht1]
        rw [e1, e2]; exact hcia t
    · filter_upwards [eventually_ge_atTop (s + 3)] with T hT
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hT
      unfold ciaAssets
      rw [hw ε j, hoff ε (s + 3 + j) (by simp; omega)])
  have hloc : IsLocalMax (fun ε => β ^ (s + 1) * u (C (s + 1) + ε * (-1)) +
      β ^ (s + 2) * u (C (s + 2) + ε * (ρ (s + 1) * k))) 0 := by
    filter_upwards [hle] with ε hε
    rw [Finset.sum_pair h12, hDs1, hDs2] at hε
    simpa using hε
  have hA := (hasDerivAt_affine (a := -1) (hu _ (hC (s + 1)))).const_mul (β ^ (s + 1))
  have hB := (hasDerivAt_affine (a := ρ (s + 1) * k) (hu _ (hC (s + 2)))).const_mul (β ^ (s + 2))
  have h0 := hloc.hasDerivAt_eq_zero (hA.add hB)
  have hb := pow_pos hβ (s + 1)
  rw [show s + 2 = s + 1 + 1 by ring] at h0
  have h3 : β ^ (s + 1) * (u' (C (s + 1)) - β * u' (C (s + 1 + 1)) * (ρ (s + 1) * k)) = 0 := by
    linear_combination -h0
  have h4 := (mul_eq_zero.1 h3).resolve_left hb.ne'
  have hkρ : k * ρ s = R s := by rw [hk]; field_simp [(hρ s).ne']
  rw [show s + 2 = s + 1 + 1 by ring]
  linear_combination ρ s * h4 + β * u' (C (s + 1 + 1)) * ρ (s + 1) * hkρ

/-- A one-sided first-order condition: if `f` has derivative `d` at `0` and `f ε ≤ f 0` for all
small `ε ≥ 0`, then `d ≤ 0`.
Context: O&R §8.3.6, pp. 547–550. -/
theorem deriv_nonpos_of_right_max {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0)
    (hmax : ∀ᶠ ε in 𝓝[≥] (0 : ℝ), f ε ≤ f 0) : d ≤ 0 := by
  have hs := hasDerivAt_iff_tendsto_slope.mp hf
  have hs' : Tendsto (slope f 0) (𝓝[>] 0) (𝓝 d) :=
    hs.mono_left (nhdsWithin_mono _ fun ε (hε : 0 < ε) => ne_of_gt hε)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), slope f 0 ε ≤ 0 := by
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε ≤ f 0 := nhdsWithin_mono _ Set.Ioi_subset_Ici_self hmax
    filter_upwards [h1, self_mem_nhdsWithin] with ε hε hpos
    rw [slope_def_field, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hpos)
  exact le_of_tendsto hs' hev

/-- **The date-0 condition** (O&R p. 549: `C_t` is predetermined by `M_{t−1}/P_t`): at a CIA
optimum `β(P_0/P_1)u'(C_1) ≤ u'(C_0)`, with equality if the date-0 cash constraint is slack.
Proof: consume `ε` less at date 0 and carry the cash into date 1. -/
theorem cia_date0_of_optimal {u u' : ℝ → ℝ} {β : ℝ} {R : ℕ → ℝ} {A0 c0 : ℝ}
    {y ι ρ C n : ℕ → ℝ} (hR : ∀ s, 0 < R s) (hιdef : ∀ s, ι s = 1 - ρ s / R s)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hopt : CIAOptimal u β R A0 c0 y ι ρ C n) :
    β * ρ 0 * u' (C 1) ≤ u' (C 0) ∧ (C 0 < c0 → u' (C 0) = β * ρ 0 * u' (C 1)) := by
  have hC := hopt.1.1
  have hn := hopt.1.2.1
  have hC0 := hopt.1.2.2.1
  have hcia := hopt.1.2.2.2.1
  set DC : ℝ → ℕ → ℝ := fun ε t => if t = 0 then C 0 + ε * (-1) else
    if t = 1 then C 1 + ε * ρ 0 else C t with hDC
  set Dn : ℝ → ℕ → ℝ := fun ε t => if t = 0 then n 0 + ε else n t with hDn
  have hD0 : ∀ ε, DC ε 0 = C 0 + ε * (-1) := fun ε => by simp [hDC]
  have hD1 : ∀ ε, DC ε 1 = C 1 + ε * ρ 0 := fun ε => by simp [hDC]
  have hoff : ∀ ε t, t ∉ ({0, 1} : Finset ℕ) → DC ε t = C t := fun ε t ht => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    simp [hDC, ht.1, ht.2]
  have hw : ∀ ε j, ciaWealth R A0 y ι (DC ε) (Dn ε) (2 + j) = ciaWealth R A0 y ι C n (2 + j) := by
    intro ε j
    refine ciaWealth_congr_after ?_ (fun t ht => hoff ε t (by simp; omega))
      (fun t ht => by have : t ≠ 0 := by omega
                      simp [hDn, this]) j
    rw [show (2 : ℕ) = 0 + 1 + 1 by rfl, ciaWealth_succ, ciaWealth_succ (C := C), ciaWealth_succ,
      ciaWealth_succ (C := C)]
    rw [hD0, hD1]
    have e1 : Dn ε 0 = n 0 + ε := by simp [hDn]
    have e2 : Dn ε 1 = n 1 := by simp [hDn]
    rw [e1, e2, hιdef 0]
    simp only [ciaWealth]
    have := (hR 0).ne'
    field_simp
    ring
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C 0 + ε * (-1) ∧ 0 < C 1 + ε * ρ 0 ∧ 0 ≤ n 0 + ε := by
    have hn0 : 0 < n 0 := by
      have := hcia 0; have := hC 1
      by_contra h; push Not at h
      have h2 : ρ 0 * n 0 ≤ 0 ∨ True := Or.inr trivial
      rcases le_or_gt (ρ 0) 0 with hr | hr
      · nlinarith [hn 0]
      · nlinarith [hn 0]
    have c1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C 0 + ε * (-1) :=
      ((by fun_prop : Continuous fun ε : ℝ => C 0 + ε * (-1)).tendsto 0).eventually
        (lt_mem_nhds (by simpa using hC 0))
    have c2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C 1 + ε * ρ 0 :=
      ((by fun_prop : Continuous fun ε : ℝ => C 1 + ε * ρ 0).tendsto 0).eventually
        (lt_mem_nhds (by simpa using hC 1))
    have c3 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < n 0 + ε :=
      ((by fun_prop : Continuous fun ε : ℝ => n 0 + ε).tendsto 0).eventually
        (lt_mem_nhds (by simpa using hn0))
    filter_upwards [c1, c2, c3] with ε h1 h2 h3 using ⟨h1, h2, h3.le⟩
  have hgood : ∀ ε, 0 < C 0 + ε * (-1) → 0 < C 1 + ε * ρ 0 → 0 ≤ n 0 + ε →
      C 0 + ε * (-1) ≤ c0 → (∀ t, 0 < DC ε t) ∧ (∀ t, 0 ≤ Dn ε t) ∧ DC ε 0 ≤ c0 ∧
      (∀ t, DC ε (t + 1) ≤ ρ t * Dn ε t) ∧
      ∀ᶠ T in atTop, ciaAssets R A0 y ι (DC ε) (Dn ε) T = ciaAssets R A0 y ι C n T := by
    intro ε h1 h2 h3 h4
    refine ⟨fun t => ?_, fun t => ?_, by rw [hD0]; exact h4, fun t => ?_, ?_⟩
    · by_cases ht : t = 0
      · rw [ht, hD0]; exact h1
      by_cases ht1 : t = 1
      · rw [ht1, hD1]; exact h2
      rw [hoff ε t (by simp [ht, ht1])]; exact hC t
    · by_cases ht : t = 0
      · subst ht; simpa [hDn] using h3
      simpa [hDn, ht] using hn t
    · by_cases ht : t = 0
      · subst ht
        rw [show (0 : ℕ) + 1 = 1 by rfl, hD1]
        simp only [hDn, ↓reduceIte]
        have := hcia 0
        linarith
      · rw [hoff ε (t + 1) (by simp; omega)]
        simp only [hDn, ht, ↓reduceIte]
        exact hcia t
    · filter_upwards [eventually_ge_atTop 2] with T hT
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hT
      unfold ciaAssets
      rw [hw ε j, hoff ε (2 + j) (by simp; omega)]
  have hf := ((hasDerivAt_affine (a := -1) (hu _ (hC 0))).const_mul (β ^ 0)).add
    ((hasDerivAt_affine (a := ρ 0) (hu _ (hC 1))).const_mul (β ^ 1))
  have hsum_eq : ∀ ε, ∑ t ∈ ({0, 1} : Finset ℕ), β ^ t * u (DC ε t) =
      β ^ 0 * u (C 0 + ε * (-1)) + β ^ 1 * u (C 1 + ε * ρ 0) := fun ε => by
    rw [Finset.sum_pair (by norm_num), hD0, hD1]
  refine ⟨?_, fun hlt => ?_⟩
  · have hle := cia_perturb_le hopt {0, 1} DC Dn hoff (l := 𝓝[≥] 0) (by
      filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with ε ⟨h1, h2, h3⟩ hε
      exact hgood ε h1 h2 h3 (by simp only [Set.mem_Ici] at hε; linarith))
    have hd := deriv_nonpos_of_right_max hf (by
      filter_upwards [hle] with ε hε
      rw [hsum_eq, Finset.sum_pair (by norm_num)] at hε
      simpa using hε)
    simp only [pow_zero, pow_one] at hd
    linarith
  · have hev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), C 0 + ε * (-1) ≤ c0 :=
      ((by fun_prop : Continuous fun ε : ℝ => C 0 + ε * (-1)).tendsto 0).eventually
        (ge_mem_nhds (by simpa using hlt))
    have hle := cia_perturb_le hopt {0, 1} DC Dn hoff (l := 𝓝 0) (by
      filter_upwards [hev, hev2] with ε ⟨h1, h2, h3⟩ h4
      exact hgood ε h1 h2 h3 h4)
    have hloc : IsLocalMax (fun ε => β ^ 0 * u (C 0 + ε * (-1)) + β ^ 1 * u (C 1 + ε * ρ 0)) 0 := by
      filter_upwards [hle] with ε hε
      rw [hsum_eq, Finset.sum_pair (by norm_num)] at hε
      simpa using hε
    have h0 := hloc.hasDerivAt_eq_zero hf
    simp only [pow_zero, pow_one] at h0
    linarith

/-- **Necessity of the transversality condition in the CIA model** (O&R p. 534): at an optimum
with `u` strictly increasing, `liminf` of end-of-period assets is at most zero; otherwise one
could consume more at date 1 (financed by holding more cash at date 0) without violating the
no-Ponzi condition. -/
theorem cia_tvc_of_optimal {u : ℝ → ℝ} {β : ℝ} {R : ℕ → ℝ} {A0 c0 : ℝ} {y ι ρ C n : ℕ → ℝ}
    (hβ : 0 < β) (hR : ∀ s, 0 < R s) (hρ : ∀ s, 0 < ρ s) (hιdef : ∀ s, ι s = 1 - ρ s / R s)
    (hmono : StrictMonoOn u (Set.Ioi 0)) (hopt : CIAOptimal u β R A0 c0 y ι ρ C n) :
    CIATransversality R A0 y ι C n := by
  obtain ⟨⟨hC, hn, hC0, hcia, hsum, hnp⟩, hmax⟩ := hopt
  intro ε hε
  by_contra hcon
  rw [not_frequently] at hcon
  set κ := ε * ρ 0 with hκ
  have hκ0 : 0 < κ := mul_pos hε (hρ 0)
  set C' : ℕ → ℝ := fun t => if t = 1 then C 1 + κ else C t with hC'
  set n' : ℕ → ℝ := fun t => if t = 0 then n 0 + ε else n t with hn'
  have hprop : ∀ j, ciaWealth R A0 y ι C' n' (2 + j) =
      ciaWealth R A0 y ι C n (2 + j) - ε * ∏ i ∈ Finset.range (2 + j), R i := by
    intro j
    induction j with
    | zero =>
      rw [show (2 : ℕ) + 0 = 0 + 1 + 1 by rfl, ciaWealth_succ, ciaWealth_succ (C := C),
        ciaWealth_succ, ciaWealth_succ (C := C)]
      simp only [show (0 : ℕ) + 1 = 1 by rfl, hC', hn', ↓reduceIte, ciaWealth,
        show (0 : ℕ) ≠ 1 by norm_num, show (1 : ℕ) ≠ 0 by norm_num]
      rw [hιdef 0, Finset.prod_range_succ, Finset.prod_range_one]
      have := (hR 0).ne'
      rw [hκ]
      field_simp
      ring
    | succ j ih =>
      rw [← add_assoc, ciaWealth_succ, ciaWealth_succ (C := C), ih, Finset.prod_range_succ]
      have h1 : C' (2 + j) = C (2 + j) := by simp [hC']; omega
      have h2 : n' (2 + j) = n (2 + j) := by simp [hn']
      rw [h1, h2]
      ring
  have hoff : ∀ t, t ∉ ({1} : Finset ℕ) → C' t = C t := fun t ht => by
    simp only [Finset.mem_singleton] at ht; simp [hC', ht]
  obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hsum {1} (g := fun t => β ^ t * u (C' t))
    fun t ht => by simp only [hoff t ht]
  have hadm : CIAAdmissible u β R A0 c0 y ι ρ C' n' := by
    refine ⟨fun t => ?_, fun t => ?_, ?_, fun t => ?_, h1, fun e he => ?_⟩
    · by_cases ht : t = 1
      · subst ht; simp only [hC', ↓reduceIte]; linarith [hC 1]
      · simp only [hC', ht, ↓reduceIte]; exact hC t
    · by_cases ht : t = 0
      · subst ht; simp only [hn', ↓reduceIte]; linarith [hn 0]
      · simp only [hn', ht, ↓reduceIte]; exact hn t
    · simp only [hC', show (0 : ℕ) ≠ 1 by norm_num, ↓reduceIte]; exact hC0
    · by_cases ht : t = 0
      · subst ht
        simp only [hC', hn', show (0 : ℕ) + 1 = 1 by rfl, ↓reduceIte]
        have := hcia 0
        rw [hκ]; nlinarith
      · have ht1 : t + 1 ≠ 1 := by omega
        simp only [hC', hn', ht, ht1, ↓reduceIte]; exact hcia t
    · filter_upwards [hcon, eventually_ge_atTop 2] with T hT hT2
      push Not at hT
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hT2
      unfold ciaAssets at hT ⊢
      have hc : C' (2 + j) = C (2 + j) := by simp [hC']; omega
      rw [hprop j, hc]
      have hD : ciaDisc R (2 + j) * ∏ i ∈ Finset.range (2 + j), R i = 1 := by
        unfold ciaDisc
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_eq_one fun i _ => inv_mul_cancel₀ (hR i).ne'
      have : ciaDisc R (2 + j) * (ciaWealth R A0 y ι C n (2 + j) -
          ε * ∏ i ∈ Finset.range (2 + j), R i + y (2 + j) - C (2 + j)) =
          ciaDisc R (2 + j) * (ciaWealth R A0 y ι C n (2 + j) + y (2 + j) - C (2 + j)) - ε := by
        linear_combination (-ε) * hD
      rw [this]
      linarith
  have hle := hmax _ _ hadm
  rw [h2, Finset.sum_singleton] at hle
  have hu : u (C 1) < u (C' 1) := by
    simp only [hC', ↓reduceIte]
    exact hmono (hC 1) (by simp only [Set.mem_Ioi]; linarith [hC 1]) (by linarith)
  have := mul_lt_mul_of_pos_left hu (pow_pos hβ 1)
  linarith

/-- Re-indexing the present value of expenditure so that each date's money purchase is paired
with next date's consumption: `Σ_{s≤T} D_s(C_s + ι_s n_s) =
C_0 + Σ_{s<T}(D_s ι_s n_s + D_{s+1}C_{s+1}) + D_T ι_T n_T` (O&R (59), p. 548). -/
theorem cia_reindex (R : ℕ → ℝ) (ι C n : ℕ → ℝ) (T : ℕ) :
    ∑ s ∈ Finset.range (T + 1), ciaDisc R s * (C s + ι s * n s) =
      C 0 + ∑ s ∈ Finset.range T, (ciaDisc R s * (ι s * n s) + ciaDisc R (s + 1) * C (s + 1)) +
        ciaDisc R T * (ι T * n T) := by
  induction T with
  | zero => simp [ciaDisc]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- **Sufficiency of the CIA first-order conditions** (O&R §8.3.6, made precise): with `u`
concave and differentiable, nonnegative nominal rates (`ι_s ≥ 0`), an admissible plan with
binding cash-in-advance constraints, the Euler equation (60) at every date, the date-0
condition, and the transversality condition is optimal. Proof: the supporting-line inequality,
the iterated Euler equation `β^{s+1}u'(C_{s+1}) = λ D_s/ρ_s` and the budget bound
`D_s ι_s n'_s + D_{s+1}C'_{s+1} ≥ D_s C'_{s+1}/ρ_s` (which uses `ι_s ≥ 0`). -/
theorem cia_isOptimal_of_foc {u u' : ℝ → ℝ} {β : ℝ} {R : ℕ → ℝ} {A0 c0 : ℝ}
    {y ι ρ C n : ℕ → ℝ} (hβ : 0 < β) (hR : ∀ s, 0 < R s) (hρ : ∀ s, 0 < ρ s)
    (hιdef : ∀ s, ι s = 1 - ρ s / R s) (hconc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hι0 : ∀ s, 0 ≤ ι s)
    (hadm : CIAAdmissible u β R A0 c0 y ι ρ C n) (hbind : ∀ s, C (s + 1) = ρ s * n s)
    (heuler : ∀ s, ρ s * u' (C (s + 1)) = R s * β * ρ (s + 1) * u' (C (s + 2)))
    (h0 : β * ρ 0 * u' (C 1) ≤ u' (C 0)) (h0' : C 0 = c0 ∨ u' (C 0) = β * ρ 0 * u' (C 1))
    (hpos : 0 ≤ u' (C 1)) (htvc : CIATransversality R A0 y ι C n) :
    CIAOptimal u β R A0 c0 y ι ρ C n := by
  refine ⟨hadm, fun C' n' hadm' => ?_⟩
  obtain ⟨hC, hn, hC0, hcia, hsum, hnp⟩ := hadm
  obtain ⟨hC', hn', hC0', hcia', hsum', hnp'⟩ := hadm'
  set lam := β * ρ 0 * u' (C 1) with hlam
  have hlam0 : 0 ≤ lam := by have := hρ 0; positivity
  have hdisc : ∀ s, β ^ (s + 1) * u' (C (s + 1)) = lam * ciaDisc R s / ρ s := by
    intro s
    induction s with
    | zero => simp [hlam, ciaDisc]; field_simp [(hρ 0).ne']
    | succ s ih =>
      rw [ciaDisc_succ, pow_succ]
      have he := heuler s
      have h1 := (hρ s).ne'
      have h2 := (hρ (s + 1)).ne'
      have h3 := (hR s).ne'
      have hb : β * u' (C (s + 1 + 1)) = ρ s * u' (C (s + 1)) / (R s * ρ (s + 1)) := by
        rw [show s + 1 + 1 = s + 2 by ring]; field_simp; linarith
      calc β ^ (s + 1) * β * u' (C (s + 1 + 1)) = β ^ (s + 1) * (β * u' (C (s + 1 + 1))) := by
            ring
        _ = β ^ (s + 1) * u' (C (s + 1)) * ρ s / (R s * ρ (s + 1)) := by rw [hb]; ring
        _ = _ := by rw [ih]; field_simp
  -- the supporting-line bounds
  have hterm : ∀ s, β ^ (s + 1) * u (C' (s + 1)) - β ^ (s + 1) * u (C (s + 1)) ≤
      lam * (ciaDisc R s * C' (s + 1) / ρ s - ciaDisc R s * C (s + 1) / ρ s) := by
    intro s
    have t := MonetaryBubbles.concave_le_tangent' hconc (hC (s + 1)) (hC' (s + 1))
      (hu _ (hC (s + 1)))
    have hb := pow_pos hβ (s + 1)
    have := mul_le_mul_of_nonneg_left t hb.le
    have key : β ^ (s + 1) * (u' (C (s + 1)) * (C' (s + 1) - C (s + 1))) =
        lam * (ciaDisc R s * C' (s + 1) / ρ s - ciaDisc R s * C (s + 1) / ρ s) := by
      rw [← mul_assoc, hdisc s]; ring
    linarith
  have hterm0 : u (C' 0) - u (C 0) ≤ lam * (C' 0 - C 0) := by
    have t := MonetaryBubbles.concave_le_tangent' hconc (hC 0) (hC' 0) (hu _ (hC 0))
    rcases h0' with heq | heq
    · have hd : C' 0 - C 0 ≤ 0 := by rw [heq]; linarith
      have : u' (C 0) * (C' 0 - C 0) ≤ lam * (C' 0 - C 0) :=
        mul_le_mul_of_nonpos_right h0 hd
      linarith
    · rw [heq] at t; linarith
  -- the budget bounds
  have hbudget : ∀ (C'' n'' : ℕ → ℝ), (∀ s, C'' (s + 1) ≤ ρ s * n'' s) → (∀ s, 0 ≤ n'' s) →
      ∀ T, C'' 0 + ∑ s ∈ Finset.range T, ciaDisc R s * C'' (s + 1) / ρ s ≤
        A0 + ∑ s ∈ Finset.range (T + 1), ciaDisc R s * y s - ciaAssets R A0 y ι C'' n'' T := by
    intro C'' n'' hc hnn T
    have h1 := cia_pv_identity hR A0 y ι C'' n'' (T + 1)
    rw [cia_reindex] at h1
    have h2 := ciaAssets_eq hR A0 y ι C'' n'' T
    have h3 : ∀ s, ciaDisc R s * C'' (s + 1) / ρ s ≤
        ciaDisc R s * (ι s * n'' s) + ciaDisc R (s + 1) * C'' (s + 1) := by
      intro s
      have hD := ciaDisc_pos hR s
      rw [ciaDisc_succ, hιdef s]
      have hr := (hR s).ne'
      have hρs := hρ s
      have hn2 : C'' (s + 1) / ρ s ≤ n'' s := by rw [div_le_iff₀ hρs]; linarith [hc s]
      have hι2 : 0 ≤ 1 - ρ s / R s := by rw [← hιdef s]; exact hι0 s
      have e : ciaDisc R s * C'' (s + 1) / ρ s = ciaDisc R s * ((1 - ρ s / R s) *
          (C'' (s + 1) / ρ s)) + ciaDisc R s * (R s)⁻¹ * C'' (s + 1) := by
        field_simp; ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hn2 hι2
      have := mul_le_mul_of_nonneg_left this hD.le
      linarith
    have h4 := Finset.sum_le_sum fun s (_ : s ∈ Finset.range T) => h3 s
    linarith
  have hbudgetC : ∀ T, C 0 + ∑ s ∈ Finset.range T, ciaDisc R s * C (s + 1) / ρ s =
      A0 + ∑ s ∈ Finset.range (T + 1), ciaDisc R s * y s - ciaAssets R A0 y ι C n T := by
    intro T
    have h1 := cia_pv_identity hR A0 y ι C n (T + 1)
    rw [cia_reindex] at h1
    have h2 := ciaAssets_eq hR A0 y ι C n T
    have h3 : ∀ s, ciaDisc R s * C (s + 1) / ρ s =
        ciaDisc R s * (ι s * n s) + ciaDisc R (s + 1) * C (s + 1) := by
      intro s
      rw [ciaDisc_succ, hιdef s, hbind s]
      have := (hR s).ne'
      have := (hρ s).ne'
      field_simp
      ring
    rw [Finset.sum_congr rfl fun s _ => h3 s]
    linarith
  have hpartial : ∀ T, ∑ s ∈ Finset.range (T + 1), (β ^ s * u (C' s) - β ^ s * u (C s)) ≤
      lam * (ciaAssets R A0 y ι C n T - ciaAssets R A0 y ι C' n' T) := by
    intro T
    rw [Finset.sum_range_succ']
    have hs := Finset.sum_le_sum fun s (_ : s ∈ Finset.range T) => hterm s
    have hb1 := hbudget C' n' hcia' hn' T
    have hb2 := hbudgetC T
    have hsplit : ∑ s ∈ Finset.range T, lam * (ciaDisc R s * C' (s + 1) / ρ s -
        ciaDisc R s * C (s + 1) / ρ s) = lam * (∑ s ∈ Finset.range T, ciaDisc R s * C' (s + 1) /
        ρ s - ∑ s ∈ Finset.range T, ciaDisc R s * C (s + 1) / ρ s) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hsplit] at hs
    simp only [pow_zero, one_mul]
    have : lam * (C' 0 - C 0) + lam * (∑ s ∈ Finset.range T, ciaDisc R s * C' (s + 1) / ρ s -
        ∑ s ∈ Finset.range T, ciaDisc R s * C (s + 1) / ρ s) ≤
        lam * (ciaAssets R A0 y ι C n T - ciaAssets R A0 y ι C' n' T) := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (by linarith) hlam0
    linarith
  have hlim : Tendsto (fun T => ∑ s ∈ Finset.range (T + 1), (β ^ s * u (C' s) -
      β ^ s * u (C s))) atTop (𝓝 (∑' s, β ^ s * u (C' s) - ∑' s, β ^ s * u (C s))) :=
    (tendsto_add_atTop_iff_nat 1).2 (hsum'.hasSum.sub hsum.hasSum).tendsto_sum_nat
  by_contra hlt
  push Not at hlt
  set δ := ∑' s, β ^ s * u (C' s) - ∑' s, β ^ s * u (C s) with hδ
  have hδ0 : 0 < δ := by linarith
  have hl1 : 0 < lam + 1 := by linarith
  set ε := δ / (4 * (lam + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hsmall : 2 * lam * ε < δ := by
    have h4 : ε * (4 * (lam + 1)) = δ := by rw [hεdef]; field_simp
    nlinarith
  obtain ⟨T, hT3, hT1, hT2⟩ :=
    ((htvc ε hε).and_eventually ((hlim.eventually (lt_mem_nhds hsmall)).and (hnp' ε hε))).exists
  have hP := hpartial T
  have hab : ciaAssets R A0 y ι C n T - ciaAssets R A0 y ι C' n' T ≤ 2 * ε := by linarith
  have := mul_le_mul_of_nonneg_left hab hlam0
  linarith

/-- **Exact characterisation of the CIA optimum** (O&R §8.3.6, made precise): with `u` concave,
differentiable and strictly increasing (`u' > 0`) and positive nominal interest rates
(`ι_s > 0`), an admissible plan is optimal IFF the cash-in-advance constraint binds at every
date after 0, the Euler equation holds at every date, the date-0 condition holds and the
transversality condition holds. -/
theorem cia_optimal_iff {u u' : ℝ → ℝ} {β : ℝ} {R : ℕ → ℝ} {A0 c0 : ℝ} {y ι ρ C n : ℕ → ℝ}
    (hβ : 0 < β) (hR : ∀ s, 0 < R s) (hρ : ∀ s, 0 < ρ s) (hιdef : ∀ s, ι s = 1 - ρ s / R s)
    (hconc : ConcaveOn ℝ (Set.Ioi 0) u) (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hu' : ∀ c, 0 < c → 0 < u' c) (hι : ∀ s, 0 < ι s) :
    CIAOptimal u β R A0 c0 y ι ρ C n ↔ CIAAdmissible u β R A0 c0 y ι ρ C n ∧
      (∀ s, C (s + 1) = ρ s * n s) ∧
      (∀ s, ρ s * u' (C (s + 1)) = R s * β * ρ (s + 1) * u' (C (s + 2))) ∧
      β * ρ 0 * u' (C 1) ≤ u' (C 0) ∧ (C 0 = c0 ∨ u' (C 0) = β * ρ 0 * u' (C 1)) ∧
      CIATransversality R A0 y ι C n := by
  have hmono : StrictMonoOn u (Set.Ioi 0) :=
    strictMonoOn_of_deriv_pos (convex_Ioi 0)
      (fun x hx => (hu x hx).continuousAt.continuousWithinAt)
      (fun x hx => by rw [interior_Ioi] at hx; rw [(hu x hx).deriv]; exact hu' x hx)
  constructor
  · intro hopt
    obtain ⟨h1, h2⟩ := cia_date0_of_optimal hR hιdef hu hopt
    refine ⟨hopt.1, fun s => cia_binds hβ hR hιdef hmono hopt s (hι s),
      cia_euler_of_optimal hβ hR hρ hιdef hu hopt, h1, ?_,
      cia_tvc_of_optimal hβ hR hρ hιdef hmono hopt⟩
    rcases hopt.1.2.2.1.lt_or_eq with hlt | heq
    · exact Or.inr (h2 hlt)
    · exact Or.inl heq
  · rintro ⟨hadm, hbind, he, h0, h0', htvc⟩
    exact cia_isOptimal_of_foc hβ hR hρ hιdef hconc hu (fun s => (hι s).le) hadm hbind he h0 h0'
      (hu' _ (hadm.1 1)).le htvc

/-! ## (59), (60), Exercise 4 and variants -/

/-- **(59)**, O&R p. 548: with the cash-in-advance constraint binding, `M_{s−1} = P_sC_s`, the
budget constraint (34) becomes `B_{s+1} = (1+r)B_s + Y_s − T_s − (P_{s+1}/P_s)C_{s+1}`. -/
theorem budget_59 {r : ℝ} {P B N Y T C : ℕ → ℝ} {s : ℕ} (hPs : P s ≠ 0)
    (hbud : B (s + 1) + N (s + 1) / P s = (1 + r) * B s + N s / P s + Y s - C s - T s)
    (hbind : ∀ t, N t = P t * C t) :
    B (s + 1) = (1 + r) * B s + Y s - T s - P (s + 1) / P s * C (s + 1) := by
  rw [hbind (s + 1), hbind s] at hbud
  field_simp at hbud ⊢
  linarith

/-- **Constant velocity** (O&R p. 549): with the constraint binding, `M_{t−1}/P_t = C_t`, so
money demand depends on consumption, not income or the nominal rate. -/
theorem constant_velocity {P N C : ℕ → ℝ} {t : ℕ} (hP : P t ≠ 0) (hbind : N t = P t * C t) :
    N t / P t = C t := by
  rw [hbind]; field_simp

/-- **(60) and Exercise 4**, O&R pp. 549 and 601: with Fisher parity
`1 + i_{s+1} = R_s P_{s+1}/P_s` (so `P_s/P_{s+1} = R_s/(1 + i_{s+1})`), the CIA Euler equation
is equivalent to `u'(C_{s+1})/(1 + i_{s+1}) = R_{s+1} β u'(C_{s+2})/(1 + i_{s+2})`: the book's
(60) holds with the time-varying real rate `1 + r_{s+2} = R_{s+1}` (Exercise 4). -/
theorem euler_60_iff {β : ℝ} {R ρ i : ℕ → ℝ} {u1 u2 : ℝ} (s : ℕ) (hR : 0 < R s)
    (hf1 : ρ s = R s / (1 + i (s + 1))) (hf2 : ρ (s + 1) = R (s + 1) / (1 + i (s + 2))) :
    ρ s * u1 = R s * β * ρ (s + 1) * u2 ↔
      u1 / (1 + i (s + 1)) = R (s + 1) * β * u2 / (1 + i (s + 2)) := by
  rw [hf1, hf2, show R s / (1 + i (s + 1)) * u1 = R s * (u1 / (1 + i (s + 1))) by ring,
    show R s * β * (R (s + 1) / (1 + i (s + 2))) * u2 =
      R s * (R (s + 1) * β * u2 / (1 + i (s + 2))) by ring]
  exact mul_right_inj' hR.ne'

/-- **(60) with a constant real rate**, O&R p. 549:
`u'(C_s)/(1+i_s) = (1+r)βu'(C_{s+1})/(1+i_{s+1})`, and in a stationary equilibrium with a
constant nominal rate it reduces to the usual Euler equation
`u'(C_s) = (1+r)βu'(C_{s+1})` (p. 549). -/
theorem euler_60_stationary {r β ibar u1 u2 : ℝ} (hi : 0 < 1 + ibar)
    (h : u1 / (1 + ibar) = (1 + r) * β * u2 / (1 + ibar)) : u1 = (1 + r) * β * u2 := by
  field_simp at h; linarith

/-- **The Helpman–Lucas timing** (O&R p. 550): if cash acquired in period `t` can be spent in `t`
(`M_t ≥ P_tC_t`), consumption is not taxed by inflation; the inflation tax falls on sellers'
receipts, so disposable income is `y_s = (1 − ι_s)Y_s − T_s` and period expenditure is just
`C_s`. The Euler equation derived from optimality is then the undistorted
`u'(C_s) = (1+r)βu'(C_{s+1})`. -/
theorem helpman_lucas_euler {u u' : ℝ → ℝ} {β r A0 : ℝ} {ι Y T C m : ℕ → ℝ} (hβ : 0 < β)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hopt : MonetaryBubbles.IsOptimalE u β r A0 (fun s => (1 - ι s) * Y s - T s)
      (fun _ c _ => c * 1 + 0) C m) (s : ℕ) :
    u' (C s) = (1 + r) * β * u' (C (s + 1)) := by
  have := MonetaryBubbles.euler_of_optimalE (w := fun _ _ => 1) (F := fun _ _ => 0) hβ hu
    (fun _ => one_pos) hopt s
  simpa using this

/-! ## Appendix 8A: a two-country cash-in-advance model -/

/-- The CES consumption price index (126), O&R p. 596:
`P = [γ p_H^{1−θ} + (1−γ) p_F^{1−θ}]^{1/(1−θ)}`. -/
noncomputable def twoGoodPrice (γ θ pH pF : ℝ) : ℝ :=
  (γ * pH ^ (1 - θ) + (1 - γ) * pF ^ (1 - θ)) ^ (1 / (1 - θ))

/-- **PPP from the law of one price and identical preferences** (O&R (122)–(127), p. 596): if
`p_H = ℰp^*_H` and `p_F = ℰp^*_F`, then `P = ℰP^*` (the price index is homogeneous of degree
one). -/
theorem ppp_of_law_of_one_price {γ θ E pHs pFs : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1)
    (hE : 0 < E) (hH : 0 < pHs) (hF : 0 < pFs) :
    twoGoodPrice γ θ (E * pHs) (E * pFs) = E * twoGoodPrice γ θ pHs pFs := by
  have h1γ : 0 < 1 - γ := by linarith
  have hθ' : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ1)
  unfold twoGoodPrice
  rw [mul_rpow hE.le hH.le, mul_rpow hE.le hF.le,
    show γ * (E ^ (1 - θ) * pHs ^ (1 - θ)) + (1 - γ) * (E ^ (1 - θ) * pFs ^ (1 - θ)) =
      E ^ (1 - θ) * (γ * pHs ^ (1 - θ) + (1 - γ) * pFs ^ (1 - θ)) by ring,
    mul_rpow (by positivity) (by positivity), ← rpow_mul hE.le, mul_one_div_cancel hθ', rpow_one]

/-- **(130), the intratemporal first-order condition**, O&R p. 597: for total spending `Z > 0`
(in units of the Home good) the CES demands at relative price `p_F/p_H` attain the maximal
value of the index among all bundles with the same cost, and they satisfy
`C_H = (γ/(1−γ))(p_F/p_H)^θ C_F`. -/
theorem relative_demand_130 {γ θ pH pF Z : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hH : 0 < pH) (hF : 0 < pF) (hZ : 0 < Z) :
    (∀ CH CF, 0 < CH → 0 < CF → CH + pF / pH * CF = Z →
      cesIndex γ θ CH CF ≤ cesIndex γ θ (cesDemandT γ θ (pF / pH) Z)
        (cesDemandN γ θ (pF / pH) Z)) ∧
    cesDemandT γ θ (pF / pH) Z =
      γ / (1 - γ) * (pF / pH) ^ θ * cesDemandN γ θ (pF / pH) Z := by
  have hp : 0 < pF / pH := div_pos hF hH
  have h1γ : 0 < 1 - γ := by linarith
  refine ⟨fun CH CF hCH hCF hcost => ?_, ?_⟩
  · rw [cesIndex_demand hγ0 hγ1 hθ hθ1 hp hZ]
    have := cesIndex_le_div_price hγ0 hγ1 hθ hθ1 hp hCH.le hCF.le (fun _ => ⟨hCH, hCF⟩)
      (by rw [hcost]; exact hZ)
    rwa [hcost] at this
  · have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
    rw [cesDemandT_eq, cesDemandN_eq]
    have e : (pF / pH) ^ θ * (pF / pH) ^ (-θ) = 1 := by
      rw [← rpow_add hp, add_neg_cancel, rpow_zero]
    field_simp
    linear_combination (-1 : ℝ) * e

/-- **(131), the equilibrium relative price**, O&R p. 597: if Home and Foreign residents both
choose `C_H = k C_F` with `k = (γ/(1−γ))(p_F/p_H)^θ` (identical preferences and the law of one
price) and goods markets clear, then `p_H/p_F = [γY_F/((1−γ)Y_H)]^{1/θ}`. -/
theorem relative_price_131 {γ θ pH pF YH YF CH CF CsH CsF : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hθ : 0 < θ) (hH : 0 < pH) (hF : 0 < pF) (hYF : 0 < YF)
    (hHome : CH = γ / (1 - γ) * (pF / pH) ^ θ * CF)
    (hFor : CsH = γ / (1 - γ) * (pF / pH) ^ θ * CsF) (hmH : CH + CsH = YH)
    (hmF : CF + CsF = YF) :
    pH / pF = (γ * YF / ((1 - γ) * YH)) ^ (1 / θ) := by
  have h1γ : 0 < 1 - γ := by linarith
  have hk : YH = γ / (1 - γ) * (pF / pH) ^ θ * YF := by
    rw [← hmH, ← hmF, hHome, hFor]; ring
  have hpow : (pH / pF) ^ θ = γ * YF / ((1 - γ) * YH) := by
    have hp : (pF / pH) ^ θ = ((pH / pF) ^ θ)⁻¹ := by
      rw [← inv_div, inv_rpow (div_pos hH hF).le]
    rw [hk, hp]
    have := rpow_pos_of_pos (div_pos hH hF) θ
    field_simp
  rw [← hpow, ← rpow_mul (div_pos hH hF).le, mul_one_div_cancel hθ.ne', rpow_one]

/-- **The steady-state real interest rate** (O&R p. 597): with constant consumption and constant
inflation, the Euler equation (129) gives `(1+r)β = 1`, i.e. `r = (1−β)/β`. -/
theorem steady_real_rate {β r ρ u1 : ℝ} (hβ : 0 < β) (hρ : 0 < ρ) (hu : 0 < u1)
    (h : ρ * u1 = (1 + r) * β * ρ * u1) : r = (1 - β) / β := by
  have h1 : (1 + r) * β = 1 := by
    have := mul_right_cancel₀ (mul_pos hρ hu).ne' (by linarith : (1 + r) * β * (ρ * u1) =
      1 * (ρ * u1))
    linarith
  field_simp
  linarith

/-- **The government budget constraints of Appendix 8A, with the sign corrected** (O&R p. 597):
summing the Home budget (128) and the Foreign budget (in Home currency) under PPP, the law of
one price, zero net bond supply and goods-market clearing gives
`P T + ℰP^*T^* = −(ΔM_H^{total} + ℰΔM_F^{total})`. So the corrected taxes
`T = −ΔM_H^{total}/P`, `T^* = −ΔM_F^{total}/P^*` (government spending zero, as in (43)) are
consistent, while the book's printed `T = +ΔM_H^{total}/P` would force total money to be
constant. -/
theorem appendix8A_taxes {P Ps E R pH pF pHs pFs Bh Bh' Bf Bf' MH MH' MF MF' MsH MsH' MsF MsF'
    YH YF CH CF CsH CsF T Ts : ℝ}
    (hHome : P * Bh' + MH' + E * MF' =
      P * R * Bh + MH + E * MF + pH * YH - pH * CH - pF * CF - P * T)
    (hFor : E * Ps * Bf' + MsH' + E * MsF' =
      E * Ps * R * Bf + MsH + E * MsF + E * pFs * YF - E * pHs * CsH - E * pFs * CsF -
        E * Ps * Ts)
    (hppp : P = E * Ps) (hlH : pH = E * pHs) (hlF : pF = E * pFs) (hb : Bh + Bf = 0)
    (hb' : Bh' + Bf' = 0) (hcH : CH + CsH = YH) (hcF : CF + CsF = YF) :
    P * T + E * Ps * Ts = -((MH' + MsH' - MH - MsH) + E * (MF' + MsF' - MF - MsF)) := by
  subst hppp hlH hlF
  have hBf : Bf = -Bh := by linarith
  have hBf' : Bf' = -Bh' := by linarith
  have hYH : YH = CH + CsH := hcH.symm
  have hYF : YF = CF + CsF := hcF.symm
  subst hBf hBf' hYH hYF
  linear_combination hHome + hFor

/-- The printed sign fails (O&R p. 597, a correction): with `T = +ΔM_H^{total}/P` and
`T^* = +ΔM_F^{total}/P^*`, the budgets and market clearing force
`ΔM_H^{total} + ℰΔM_F^{total} = 0`; with the corrected signs no such restriction arises. -/
theorem appendix8A_printed_sign {P Ps E ΔH ΔF T Ts : ℝ} (hP : P ≠ 0) (hPs : Ps ≠ 0)
    (hsum : P * T + E * Ps * Ts = -(ΔH + E * ΔF)) :
    ((T = ΔH / P ∧ Ts = ΔF / Ps) → ΔH + E * ΔF = 0) ∧
    (T = -ΔH / P → Ts = -ΔF / Ps → P * T + E * Ps * Ts = -(ΔH + E * ΔF)) := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [h1, h2] at hsum
    field_simp at hsum
    linarith
  · intro h1 h2
    rw [h1, h2]
    field_simp
    ring

/-! ## Appendix 8B and forward intervention (§8.7.6.1) -/

/-- The central bank's balance-sheet identity, O&R p. 598:
`P^g Gold + ℰB_F + B_H + ℰM_F = M_H + RR + NW` (with `base = M_H + RR`). -/
def BalanceSheet (Pg gold E bF bH mF base nw : ℝ) : Prop :=
  Pg * gold + E * bF + bH + E * mF = base + nw

/-- **Nonsterilised intervention** (O&R p. 598): buying one unit (of home currency) of foreign
bonds with newly issued base money preserves the balance-sheet identity. -/
theorem nonsterilised_preserves {Pg gold E bF bH mF base nw : ℝ} (hE : E ≠ 0)
    (h : BalanceSheet Pg gold E bF bH mF base nw) :
    BalanceSheet Pg gold E (bF + 1 / E) bH mF (base + 1) nw := by
  unfold BalanceSheet at h ⊢
  field_simp
  field_simp at h
  linarith

/-- **Sterilised intervention = nonsterilised purchase + open-market sale** (O&R pp. 598–599):
the combined operation preserves the identity, swaps one unit of home-currency bonds for
foreign-currency bonds and leaves the monetary base unchanged. -/
theorem sterilised_is_swap {Pg gold E bF bH mF base nw : ℝ} (hE : E ≠ 0)
    (h : BalanceSheet Pg gold E bF bH mF base nw) :
    BalanceSheet Pg gold E (bF + 1 / E) (bH - 1) mF base nw ∧
      (base + 1) - 1 = base := by
  refine ⟨?_, by ring⟩
  unfold BalanceSheet at h ⊢
  field_simp
  field_simp at h
  linarith

/-- **Forward intervention is equivalent to sterilised intervention** (O&R §8.7.6.1, p. 594):
covered interest parity (104) `F = ℰ(1+i)/(1+i^*)` gives
`(1 + i)/((1 + i^*)F) = 1/ℰ`, so fixing the forward rate and the interest differential pins the
spot rate exactly as a spot operation does. -/
theorem forward_intervention_identity {E F i is : ℝ} (hE : E ≠ 0) (hi : 1 + i ≠ 0)
    (his : 1 + is ≠ 0) (hcip : F = E * (1 + i) / (1 + is)) :
    (1 + i) / ((1 + is) * F) = 1 / E := by
  rw [hcip]
  field_simp

end ObstfeldRogoff.MoneyExchangeRates.CashInAdvance
