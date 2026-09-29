/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceModels.NontradablesOvershooting

/-!
# Cash in advance and the credibility of monetary policy (Exercise 4)

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, Chapter 10,
Exercise 4, pp. 713–714 (a cash-in-advance variant of the §10.2 model, pp. 689–694). Utility is
`γ log C_T + (1−γ) log C_N − (κ/2) y_N²` (no money in utility), with the contemporaneous
cash-in-advance constraint `M ≥ P_T C_T + P_N C_N`, holding with equality, and currency pays
the nominal interest rate (so the timing of the constraint introduces no wedge).

* (a) The CIA household problem is a genuine infinite-horizon problem; its first-order conditions
  (87), (89), (90) with no-Ponzi and the transversality condition are NECESSARY AND SUFFICIENT;
  in every symmetric flexible-price equilibrium `ȳ_N = C̄_N = [(θ−1)(1−γ)/(κθ)]^{1/2}` (unique),
  and the steady state exists.
* (b) The planner's output `ȳ_N^{PLAN} = ((1−γ)/κ)^{1/2}` is the unique maximiser, and
  `ȳ_N < ȳ_N^{PLAN}`.
* (c) EXACT (no linearisation): CIA with equality and (89) give `M = P_N C_N/(1−γ)`; with `P_N`
  preset at the level `(1−γ)M^e/ȳ_N` consistent with `M^e`, `y_N = C_N = (M/M^e) ȳ_N` and
  `P_T = γM/ȳ_T`. Finite-state version: with a random money supply on finitely many states and
  `M^e = E[M]`, the formula holds state by state and `E[y_N] = ȳ_N`.
* (d) The one-shot assumption spelled out: with expectations and the future real allocation
  held fixed, the authority's objective `U_t − (χ/2)(P_{T,t}/P_{T,t−1})²` differs across choices of
  `M_t` exactly by `(1−γ) log C_N − (κ/2) y_N² − (χ/2)(P_{T,t}/P_{T,t−1})²`; if next period's
  inflation penalty were counted with `M_{t+1}` fixed in levels, the extra term
  `−β(χ/2)(M_{t+1}/M_t)²` would appear — the one-shot game ignores it.
* (e) The best response is unique (strict concavity) and the one-shot equilibrium is UNIQUE:
  `μ = ((1−γ)/(χθ))^{1/2} = {κ[(ȳ_N^{PLAN})² − ȳ_N²]/χ}^{1/2}`. The penalty in the book is on the
  GROSS inflation factor (minimised at zero money): with the conventional `(π − 1)²` penalty the
  unique equilibrium is instead `μ = [1 + (1 + 4(1−γ)/(θχ))^{1/2}]/2 > 1`, an inflation bias
  relative to the commitment optimum `μ = 1`; under the literal gross penalty the commitment
  problem has no optimum at all.

The book's `χ` in (d) is the weight on the inflation penalty; here it is `E.χ` (the §10.2
real-balance parameter, which the CIA model does not otherwise use), and `E.ε` is unused.
-/

namespace ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility

open Real Filter Topology Finset
open ObstfeldRogoff.StickyPriceModels.NontradablesModel
open ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting

/-! ## (a) The cash-in-advance household problem -/

/-- Period utility of Exercise 4, p. 713: `γ log C_T + (1−γ) log C_N − (κ/2) y_N²`. -/
noncomputable def ciaU (E : Economy) (_t : ℕ) (c : Choice) : ℝ :=
  E.γ * log c.cT + (1 - E.γ) * log c.cN - E.κ / 2 * c.y ^ 2

/-- Net real resources in the CIA economy (O&R p. 714): currency pays the nominal interest
rate, so money and bonds earn the same return and money drops out of the wealth recursion;
`rev t y` is real revenue from selling `y` (the demand curve (86) under flexible prices, the
preset price times `y` otherwise). -/
noncomputable def ciaNetRes (E : Economy) (Q : Prices) (rev : ℕ → ℝ → ℝ) (t : ℕ) (c : Choice) :
    ℝ :=
  E.yT - Q.τ t + rev t c.y - relPrice Q t * c.cN - c.cT

/-- Admissible CIA choices: positive, the cash-in-advance constraint with equality
`M_t = P_{T,t} C_T + P_{N,t} C_N`, and output in the admissible set `Ys t` (O&R p. 713). -/
def ciaSet (Q : Prices) (Ys : ℕ → Set ℝ) (t : ℕ) : Set Choice :=
  {c | c ∈ posChoice ∧ c.money = Q.PT t * c.cT + Q.PN t * c.cN ∧ c.y ∈ Ys t}

/-- Optimality in the CIA economy from initial real wealth `A0` (O&R Ex. 4). -/
def CIAOptimal (E : Economy) (Q : Prices) (rev : ℕ → ℝ → ℝ) (Ys : ℕ → Set ℝ) (A0 : ℝ)
    (c : ℕ → Choice) : Prop :=
  IsOptimal E.β E.r A0 (ciaU E) (ciaNetRes E Q rev) (ciaSet Q Ys) c

/-- The flexible-price regime: revenue on the demand curve (86), any positive output. -/
noncomputable def flexRev (E : Economy) (Q : Prices) : ℕ → ℝ → ℝ := realRevenue E Q

/-- Any positive output is admissible under flexible prices (O&R Ex. 4(a)). -/
def flexYs : ℕ → Set ℝ := fun _ => Set.Ioi 0

/-- SUFFICIENCY in the CIA economy (O&R Ex. 4(a)): under flexible prices, an admissible plan with
summable utility satisfying (87), (89), (90), no-Ponzi and the transversality condition is
optimal. -/
theorem ciaOptimal_of_foc {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {A0 : ℝ} {c : ℕ → Choice} (hc : ∀ t, c t ∈ ciaSet Q flexYs t)
    (hsum : Summable fun t => E.β ^ t * ciaU E t (c t)) (heu : EulerFOC E c)
    (hN : IntraFOC E Q c) (hL : LabourFOC E Q c)
    (hnp : NoPonzi E.r (wealth E.r A0 (ciaNetRes E Q (flexRev E Q)) c))
    (htv : LiminfNonpos E.r (wealth E.r A0 (ciaNetRes E Q (flexRev E Q)) c)) :
    CIAOptimal E Q (flexRev E Q) flexYs A0 c := by
  have hE' := hE
  obtain ⟨hβ, _, hr, hγ0, hγ1, _, _, hκ, hθ, _⟩ := hE'
  have hpos : ∀ t, c t ∈ posChoice := fun t => (hc t).1
  refine isOptimal_of_saddle (μ0 := E.γ / (c 0).cT) hr (div_pos hγ0 (hpos 0).1).le hc hsum hnp
    htv ?_
  intro t y hy
  obtain ⟨ha, hb, _, hq⟩ := hpos t
  obtain ⟨⟨ha', hb', _, hq'⟩, _, _⟩ := hy
  obtain ⟨hT, hPN, hA, _⟩ := hQ t
  set lam := E.γ / (c t).cT with hlam
  set ρ := relPrice Q t
  set K := Q.CA t ^ (1 / E.θ)
  set s := (E.θ - 1) / E.θ with hs
  have hK : 0 < K := rpow_pos_of_pos hA _
  have hρ : 0 < ρ := div_pos hPN hT
  have hs0 : 0 < s := div_pos (by linarith) (by linarith)
  have hs1 : s ≤ 1 := by rw [hs, div_le_one (by linarith)]; linarith
  have hlam0 : 0 < lam := div_pos hγ0 ha
  have hA' := log_tangent hγ0.le ha' ha
  have hB' := log_tangent (k := 1 - E.γ) (by linarith) hb' hb
  have hBr : (1 - E.γ) / (c t).cN = lam * ρ := hN t
  have hD1 := rpow_le_tangent hs0 hs1 hq hq'
  have hD2 : lam * ρ * K * y.y ^ s ≤ lam * ρ * K * (c t).y ^ s
      + E.κ * (c t).y * (y.y - (c t).y) := by
    have hL' : E.κ * (c t).y = lam * ρ * K * (s * (c t).y ^ (s - 1)) := by rw [hL t]; ring
    have := mul_le_mul_of_nonneg_left hD1 (by positivity : 0 ≤ lam * ρ * K)
    rw [hL']; linarith
  have hD3 : -(E.κ / 2) * y.y ^ 2 ≤ -(E.κ / 2) * (c t).y ^ 2 - E.κ * (c t).y * (y.y - (c t).y) := by
    have := mul_nonneg (by linarith : 0 ≤ E.κ / 2) (sq_nonneg (y.y - (c t).y))
    nlinarith
  have hpt : ciaU E t y + lam * ciaNetRes E Q (flexRev E Q) t y
      ≤ ciaU E t (c t) + lam * ciaNetRes E Q (flexRev E Q) t (c t) := by
    simp only [ciaU, ciaNetRes, flexRev, realRevenue]
    rw [hBr] at hB'
    have e1 : (1 - E.γ) / (c t).cN * y.cN = lam * ρ * y.cN := by rw [hBr]
    have e2 : (1 - E.γ) / (c t).cN * (c t).cN = lam * ρ * (c t).cN := by rw [hBr]
    linarith [hA', hB', hD2, hD3, e1, e2]
  have hd := discounted_mu_of_euler hβ hr hpos heu hγ0 t
  have hβt : 0 ≤ E.β ^ t := pow_nonneg hβ.le t
  have key := mul_le_mul_of_nonneg_left hpt hβt
  have e : ∀ z : Choice, E.β ^ t * (ciaU E t z + lam * ciaNetRes E Q (flexRev E Q) t z)
      = E.β ^ t * ciaU E t z + E.γ / (c 0).cT * (disc E.r t * ciaNetRes E Q (flexRev E Q) t z) := by
    intro z
    have h2 : E.γ / (c 0).cT * (disc E.r t * ciaNetRes E Q (flexRev E Q) t z)
        = (E.β ^ t * (E.γ / (c t).cT)) * ciaNetRes E Q (flexRev E Q) t z := by rw [hd]; ring
    rw [h2]; ring
  rw [e, e] at key
  exact key

/-- NECESSITY of (89) in the CIA economy, in ANY pricing regime (O&R Ex. 4): reallocating
spending between tradables and nontradables (with money adjusting to keep the CIA constraint) is
always feasible. -/
theorem cia_intra_of_optimal {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {rev : ℕ → ℝ → ℝ} {Ys : ℕ → Set ℝ} {A0 : ℝ} {c : ℕ → Choice}
    (hopt : CIAOptimal E Q rev Ys A0 c) : IntraFOC E Q c := by
  obtain ⟨hβ, _, hr, hγ0, hγ1, _, _, _, _, _⟩ := hE
  intro t
  obtain ⟨⟨ha, hb, hn, hq⟩, _, hys⟩ := hopt.1 t
  obtain ⟨hT, hPN, _, _⟩ := hQ t
  set ρ := relPrice Q t
  set g : ℝ → Choice := fun η => ⟨(c t).cT - ρ * η, (c t).cN + η,
    Q.PT t * ((c t).cT - ρ * η) + Q.PN t * ((c t).cN + η), (c t).y⟩ with hg
  have hmax : IsLocalMax (fun η => ciaU E t (g η)) 0 := by
    have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cT - ρ * η :=
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually
        (lt_mem_nhds (by simpa using ha))
    have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cN + η :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (lt_mem_nhds (by simpa using hb))
    filter_upwards [h1, h2] with η e1 e2
    have hmem : g η ∈ ciaSet Q Ys t := ⟨⟨e1, e2, by positivity, hq⟩, rfl, hys⟩
    have hres : ciaNetRes E Q rev t (c t) ≤ ciaNetRes E Q rev t (g η) := by
      simp only [ciaNetRes, g]; linarith
    have h := perturb_le_gen hr hβ hopt t g hmem hres
    have hg0 : ciaU E t (g 0) = ciaU E t (c t) := by simp [g, ciaU]
    rw [hg0]; exact h
  have hfun : (fun η => ciaU E t (g η)) = fun η =>
      E.γ * log ((c t).cT - ρ * η) + (1 - E.γ) * log ((c t).cN + η)
        - E.κ / 2 * (c t).y ^ 2 := by
    funext η; simp only [ciaU, g]
  have hd1 : HasDerivAt (fun η => (c t).cT - ρ * η) (-ρ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul ρ).const_sub (c t).cT
  have hd2 : HasDerivAt (fun η => (c t).cN + η) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (c t).cN
  have hd : HasDerivAt (fun η => ciaU E t (g η))
      (E.γ * (-ρ / (c t).cT) + (1 - E.γ) * (1 / (c t).cN)) 0 := by
    rw [hfun]
    have e1 := (hd1.log (by simpa using ha.ne')).const_mul E.γ
    have e2 := (hd2.log (by simpa using hb.ne')).const_mul (1 - E.γ)
    simp only [mul_zero, sub_zero, add_zero] at e1 e2
    exact (e1.add e2).sub_const _
  have h0 := hmax.hasDerivAt_eq_zero hd
  field_simp at h0 ⊢
  linarith

/-- NECESSITY of the Euler equation (87) in the CIA economy, in ANY pricing regime
(O&R Ex. 4): shifting tradables consumption between `t` and `t+1` (money adjusting to keep the
CIA constraint) is always feasible. -/
theorem cia_euler_of_optimal {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {rev : ℕ → ℝ → ℝ} {Ys : ℕ → Set ℝ} {A0 : ℝ} {c : ℕ → Choice}
    (hopt : CIAOptimal E Q rev Ys A0 c) : EulerFOC E c := by
  obtain ⟨hβ, _, hr, hγ0, _, _, _, _, _, _⟩ := hE
  intro t
  obtain ⟨⟨ha, hb, _, hq⟩, _, hys⟩ := hopt.1 t
  obtain ⟨⟨ha', hb', _, hq'⟩, _, hys'⟩ := hopt.1 (t + 1)
  obtain ⟨hT, hN, _, _⟩ := hQ t
  obtain ⟨hT', hN', _, _⟩ := hQ (t + 1)
  have htt : t + 1 ≠ t := Nat.succ_ne_self t
  set x' : ℝ → ℕ → Choice := fun η s =>
    if s = t then ⟨(c t).cT + η, (c t).cN, Q.PT t * ((c t).cT + η) + Q.PN t * (c t).cN,
      (c t).y⟩
    else if s = t + 1 then
      ⟨(c (t + 1)).cT - (1 + E.r) * η, (c (t + 1)).cN,
        Q.PT (t + 1) * ((c (t + 1)).cT - (1 + E.r) * η) + Q.PN (t + 1) * (c (t + 1)).cN,
        (c (t + 1)).y⟩
    else c s with hx'
  set f : ℝ → ℝ := fun η => E.β ^ t * (E.γ * log ((c t).cT + η))
    + E.β ^ (t + 1) * (E.γ * log ((c (t + 1)).cT - (1 + E.r) * η)) with hf
  have hloc : IsLocalMax f 0 := by
    have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cT + η :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (lt_mem_nhds (by simpa using ha))
    have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c (t + 1)).cT - (1 + E.r) * η :=
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually
        (lt_mem_nhds (by simpa using ha'))
    filter_upwards [h1, h2] with η e1 e2
    have hS : ∀ s ∉ ({t, t + 1} : Finset ℕ), x' η s = c s := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
      simp [x', hs.1, hs.2]
    have hadm : ∀ s, x' η s ∈ ciaSet Q Ys s := by
      intro s
      by_cases hs1 : s = t
      · subst hs1; simp only [x', ↓reduceIte]
        exact ⟨⟨e1, hb, by positivity, hq⟩, rfl, hys⟩
      by_cases hs2 : s = t + 1
      · subst hs2; simp only [x', htt, ↓reduceIte]
        exact ⟨⟨e2, hb', by positivity, hq'⟩, rfl, hys'⟩
      rw [hS s (by simp [hs1, hs2])]; exact hopt.1 s
    have hpv : 0 ≤ ∑ s ∈ ({t, t + 1} : Finset ℕ),
        disc E.r s * (ciaNetRes E Q rev s (x' η s) - ciaNetRes E Q rev s (c s)) := by
      rw [Finset.sum_pair htt.symm]
      simp only [x', htt, ↓reduceIte, ciaNetRes]
      have := disc_succ_mul hr t
      nlinarith
    have h := perturb_utility_le_of_pv hr hopt hadm hS hpv
    rw [Finset.sum_pair htt.symm] at h
    simp only [x', htt, ↓reduceIte, ciaU] at h
    simp only [hf, add_zero, mul_zero, sub_zero]
    linarith
  have hd1 : HasDerivAt (fun η => (c t).cT + η) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (c t).cT
  have hd2 : HasDerivAt (fun η => (c (t + 1)).cT - (1 + E.r) * η) (-(1 + E.r)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 + E.r)).const_sub (c (t + 1)).cT
  have hd : HasDerivAt f (E.β ^ t * (E.γ * (1 / (c t).cT))
      + E.β ^ (t + 1) * (E.γ * (-(1 + E.r) / (c (t + 1)).cT))) 0 := by
    have e1 := ((hd1.log (by simpa using ha.ne')).const_mul E.γ).const_mul (E.β ^ t)
    have e2 := ((hd2.log (by simpa using ha'.ne')).const_mul E.γ).const_mul (E.β ^ (t + 1))
    simp only [add_zero, mul_zero, sub_zero] at e1 e2
    exact e1.add e2
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hβt : 0 < E.β ^ t := pow_pos hβ t
  rw [pow_succ] at h0
  have h3 : E.β ^ t * (E.γ / (c t).cT - E.β * (1 + E.r) * (E.γ / (c (t + 1)).cT)) = 0 := by
    rw [← h0]; field_simp; ring
  have := (mul_eq_zero.mp h3).resolve_left hβt.ne'
  linarith

/-- NECESSITY of the output condition behind (90) in the flexible-price CIA economy
(O&R Ex. 4(a)). -/
theorem cia_labour_of_optimal {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {A0 : ℝ} {c : ℕ → Choice} (hopt : CIAOptimal E Q (flexRev E Q) flexYs A0 c) :
    LabourFOC E Q c := by
  obtain ⟨hβ, _, hr, hγ0, hγ1, _, _, _, hθ, _⟩ := hE
  intro t
  obtain ⟨⟨ha, hb, _, hq⟩, _, _⟩ := hopt.1 t
  obtain ⟨hT, hN, _, _⟩ := hQ t
  set R := realRevenue E Q t
  set s := (E.θ - 1) / E.θ
  set K := Q.CA t ^ (1 / E.θ)
  set ρ := relPrice Q t
  have hRd : HasDerivAt R (ρ * (s * (c t).y ^ (s - 1) * K)) (c t).y := by
    have := ((hasDerivAt_rpow_const (p := s) (Or.inl hq.ne')).mul_const K).const_mul ρ
    exact this
  have hRc : HasDerivAt (fun η => R ((c t).y + η)) (ρ * (s * (c t).y ^ (s - 1) * K)) 0 := by
    have hR0 : HasDerivAt R (ρ * (s * (c t).y ^ (s - 1) * K)) ((c t).y + 0) := by
      simpa using hRd
    have := hR0.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add (c t).y)
    convert this using 1 <;> first | rfl | simp
  have hd1 : HasDerivAt (fun η => (c t).cT + (R ((c t).y + η) - R (c t).y))
      (ρ * (s * (c t).y ^ (s - 1) * K)) 0 := by
    simpa using (hRc.sub_const (R (c t).y)).const_add (c t).cT
  set g : ℝ → Choice := fun η => ⟨(c t).cT + (R ((c t).y + η) - R (c t).y), (c t).cN,
    Q.PT t * ((c t).cT + (R ((c t).y + η) - R (c t).y)) + Q.PN t * (c t).cN,
    (c t).y + η⟩ with hg
  have hmax : IsLocalMax (fun η => ciaU E t (g η)) 0 := by
    have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cT + (R ((c t).y + η) - R (c t).y) :=
      hd1.continuousAt.eventually (lt_mem_nhds (by simpa using ha))
    have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).y + η :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (lt_mem_nhds (by simpa using hq))
    filter_upwards [h1, h2] with η e1 e2
    have hmem : g η ∈ ciaSet Q flexYs t :=
      ⟨⟨e1, hb, by positivity, e2⟩, rfl, Set.mem_Ioi.mpr e2⟩
    have hres : ciaNetRes E Q (flexRev E Q) t (c t) ≤ ciaNetRes E Q (flexRev E Q) t (g η) := by
      simp only [ciaNetRes, flexRev, g, R]; linarith
    have h := perturb_le_gen hr hβ hopt t g hmem hres
    have hg0 : ciaU E t (g 0) = ciaU E t (c t) := by simp [g, ciaU]
    rw [hg0]; exact h
  have hfun : (fun η => ciaU E t (g η)) = fun η =>
      E.γ * log ((c t).cT + (R ((c t).y + η) - R (c t).y)) - E.κ / 2 * ((c t).y + η) ^ 2
        + (1 - E.γ) * log (c t).cN := by
    funext η; simp only [ciaU, g]; ring
  have hsq : HasDerivAt (fun η => ((c t).y + η) ^ 2) (2 * (c t).y) 0 := by
    have := (hasDerivAt_pow 2 ((c t).y + 0)).comp (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).const_add (c t).y)
    convert this using 1 <;> first | rfl | simp
  have hd : HasDerivAt (fun η => ciaU E t (g η))
      (E.γ * (ρ * (s * (c t).y ^ (s - 1) * K) / (c t).cT) - E.κ / 2 * (2 * (c t).y)) 0 := by
    rw [hfun]
    have e1 := (hd1.log (by simpa using ha.ne')).const_mul E.γ
    simp only [sub_self, add_zero] at e1
    exact ((e1.sub (hsq.const_mul (E.κ / 2)))).add_const _
  have h0 := hmax.hasDerivAt_eq_zero hd
  have : E.κ * (c t).y = E.γ / (c t).cT * ρ * (s * ((c t).y ^ (s - 1) * K)) := by
    field_simp at h0 ⊢; linarith
  exact this

/-- NECESSITY of the transversality condition (liminf form) in the CIA economy (O&R (16)). -/
theorem cia_liminfNonpos {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {rev : ℕ → ℝ → ℝ} {Ys : ℕ → Set ℝ} {A0 : ℝ} {c : ℕ → Choice}
    (hopt : CIAOptimal E Q rev Ys A0 c) :
    LiminfNonpos E.r (wealth E.r A0 (ciaNetRes E Q rev) c) := by
  obtain ⟨_, _, hr, hγ0, _, _, _, _, _, _⟩ := hE
  obtain ⟨hT, hN, _, _⟩ := hQ 0
  refine liminfNonpos_of_isOptimal hr hopt ?_
  intro η hη
  obtain ⟨⟨ha, hb, _, hq⟩, _, hys⟩ := hopt.1 0
  refine ⟨⟨(c 0).cT + η, (c 0).cN, Q.PT 0 * ((c 0).cT + η) + Q.PN 0 * (c 0).cN, (c 0).y⟩,
    ⟨⟨by linarith, hb, by positivity, hq⟩, rfl, hys⟩, ?_, ?_⟩
  · simp only [ciaNetRes]; linarith
  · simp only [ciaU]
    have := log_lt_log ha (by linarith : (c 0).cT < (c 0).cT + η)
    nlinarith

/-- EX. 4(a) MAIN THEOREM: under flexible prices a CIA plan is optimal IF AND ONLY IF it has
summable utility and satisfies (87), (89), (90), no-Ponzi and the transversality condition. -/
theorem ciaOptimal_iff {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {A0 : ℝ} {c : ℕ → Choice} :
    CIAOptimal E Q (flexRev E Q) flexYs A0 c ↔
      (∀ t, c t ∈ ciaSet Q flexYs t) ∧ Summable (fun t => E.β ^ t * ciaU E t (c t)) ∧
      EulerFOC E c ∧ IntraFOC E Q c ∧ LabourFOC E Q c ∧
      NoPonzi E.r (wealth E.r A0 (ciaNetRes E Q (flexRev E Q)) c) ∧
      LiminfNonpos E.r (wealth E.r A0 (ciaNetRes E Q (flexRev E Q)) c) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.2.1, cia_euler_of_optimal hE hQ h, cia_intra_of_optimal hE hQ h,
      cia_labour_of_optimal hE hQ h, h.2.1, cia_liminfNonpos hE hQ h⟩
  · rintro ⟨hc, hs, he, hn, hl, hnp, htv⟩
    exact ciaOptimal_of_foc hE hQ hc hs he hn hl hnp htv

/-- EX. 4(a), p. 714: in every symmetric flexible-price CIA equilibrium (`y_N = C_N = C^A_N`),
nontradables output and consumption equal `ȳ_N = [(θ−1)(1−γ)/(κθ)]^{1/2}` at every date. -/
theorem cia_flexible_output {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {A0 : ℝ} {c : ℕ → Choice} (hopt : CIAOptimal E Q (flexRev E Q) flexYs A0 c)
    (hsym : ∀ t, (c t).y = (c t).cN ∧ Q.CA t = (c t).cN) (t : ℕ) :
    (c t).y = ybarN E ∧ (c t).cN = ybarN E := by
  have hpos : ∀ t, c t ∈ posChoice := fun t => (hopt.1 t).1
  have h90 := labour_90 hE hpos (cia_intra_of_optimal hE hQ hopt)
    (cia_labour_of_optimal hE hQ hopt) t
  obtain ⟨_, _, _, _, hγ1, _, _, hκ, hθ, _⟩ := hE
  obtain ⟨hy, hA⟩ := hsym t
  rw [hA, ← hy] at h90
  have hq := (hpos t).2.2.2
  set x := (c t).y
  have hθ0 : 0 < E.θ := by linarith
  have e1 : x ^ ((E.θ + 1) / E.θ) = x * x ^ (1 / E.θ) := by
    rw [show (E.θ + 1) / E.θ = 1 + 1 / E.θ by field_simp, rpow_add hq, rpow_one]
  rw [e1] at h90
  have hx1 : 0 < x ^ (1 / E.θ) := rpow_pos_of_pos hq _
  have hsq : x ^ 2 = (E.θ - 1) * (1 - E.γ) / (E.κ * E.θ) := by
    field_simp at h90 ⊢
    nlinarith
  have hxy : x = ybarN E := by
    unfold ybarN; rw [← hsq, sqrt_sq hq.le]
  exact ⟨hxy, hy ▸ hxy⟩

/-- The CIA steady-state prices (O&R Ex. 4(a)): any `P_T > 0`, `P_N = (P_N/P_T)‾ P_T`,
aggregate demand `ȳ_N`, zero taxes. -/
noncomputable def ciaSteadyPrices (E : Economy) (pT : ℝ) : Prices :=
  ⟨fun _ => pT, fun _ => relPriceBar E * pT, fun _ => ybarN E, fun _ => 0⟩

/-- The CIA steady-state allocation `(ȳ_T, ȳ_N, M = P_T ȳ_T + P_N ȳ_N, ȳ_N)` (O&R Ex. 4(a)). -/
noncomputable def ciaSteadyChoice (E : Economy) (pT : ℝ) : ℕ → Choice :=
  fun _ => ⟨E.yT, ybarN E, pT * E.yT + relPriceBar E * pT * ybarN E, ybarN E⟩

/-- EXISTENCE in Ex. 4(a): the CIA steady state is a genuine infinite-horizon household optimum
(zero initial wealth) with `y_N = C_N = C^A_N = ȳ_N`. -/
theorem cia_steadyState_optimal {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {pT : ℝ} (hT : 0 < pT) :
    (ciaSteadyPrices E pT).Valid E.r ∧
      CIAOptimal E (ciaSteadyPrices E pT) (flexRev E (ciaSteadyPrices E pT)) flexYs 0
        (ciaSteadyChoice E pT) ∧
      ∀ t, (ciaSteadyChoice E pT t).y = (ciaSteadyChoice E pT t).cN ∧
        (ciaSteadyPrices E pT).CA t = (ciaSteadyChoice E pT t).cN := by
  have hE' := hE
  obtain ⟨hβ, hβ1, hr, hγ0, hγ1, _, _, hκ, hθ, hyT⟩ := hE'
  have hr0 : 0 < E.r := by nlinarith
  have hy := ybarN_pos hE
  have hrel := relPriceBar_pos hE
  set Q := ciaSteadyPrices E pT
  set c := ciaSteadyChoice E pT
  have hQ : Q.Valid E.r := by
    intro t
    refine ⟨hT, by simp only [Q, ciaSteadyPrices]; positivity, hy, ?_⟩
    simp only [userCost, Q, ciaSteadyPrices]
    rw [div_sub_div _ _ hT.ne' (mul_pos hr hT).ne']
    apply div_pos _ (mul_pos hT (mul_pos hr hT))
    nlinarith
  have hc : ∀ t, c t ∈ ciaSet Q flexYs t := fun t =>
    ⟨⟨hyT, hy, by simp only [c, ciaSteadyChoice]; positivity, hy⟩,
      by simp [c, Q, ciaSteadyChoice, ciaSteadyPrices],
      Set.mem_Ioi.mpr hy⟩
  have hw : ∀ t, wealth E.r 0 (ciaNetRes E Q (flexRev E Q)) c t = 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [wealth, ih]
      have hrev : flexRev E Q t (c t).y = relPrice Q t * (c t).cN :=
        realRevenue_symm E Q t (by linarith) hy rfl
      simp only [ciaNetRes, hrev]
      simp [c, Q, ciaSteadyChoice, ciaSteadyPrices]
  have hdw : Tendsto (fun T => disc E.r T * wealth E.r 0 (ciaNetRes E Q (flexRev E Q)) c T)
      atTop (𝓝 0) := by simp_rw [hw, mul_zero]; exact tendsto_const_nhds
  refine ⟨hQ, ciaOptimal_of_foc hE hQ hc ?_ ?_ ?_ ?_
    (fun δ hδ => (hdw.eventually (lt_mem_nhds (by linarith : -δ < 0))).mono fun _ h => h.le)
    (fun δ hδ => (hdw.eventually (gt_mem_nhds hδ)).frequently.mono fun _ h => h.le),
    fun t => ⟨rfl, rfl⟩⟩
  · exact (summable_geometric_of_lt_one hβ.le hβ1).mul_right (ciaU E 0 (c 0))
  · intro t; simp only [c, ciaSteadyChoice]; rw [hβr, one_mul]
  · intro t
    simp only [c, ciaSteadyChoice, relPrice, Q, ciaSteadyPrices]
    rw [mul_div_cancel_right₀ _ hT.ne']
    unfold relPriceBar; field_simp
  · intro t
    simp only [c, ciaSteadyChoice, relPrice, Q, ciaSteadyPrices]
    rw [mul_div_cancel_right₀ _ hT.ne', ← rpow_add hy,
      show (E.θ - 1) / E.θ - 1 + 1 / E.θ = 0 by field_simp; ring, rpow_zero, mul_one]
    have hk := kappa_mul_ybarN_sq hE
    unfold relPriceBar
    field_simp at hk ⊢
    linarith

/-! ## (b) The planner -/

/-- The planner's output (Ex. 4(b), p. 714): `ȳ_N^{PLAN} = ((1−γ)/κ)^{1/2}`. -/
noncomputable def yPlan (E : Economy) : ℝ := sqrt ((1 - E.γ) / E.κ)

/-- Ex. 4(b): the planner, choosing `y_N = C_N` to maximise `(1−γ) log C_N − (κ/2) y_N²`, has the
UNIQUE optimum `ȳ_N^{PLAN}` (strict concavity). -/
theorem planner_unique {E : Economy} (hE : E.Valid) {y : ℝ} (hy : 0 < y) :
    (1 - E.γ) * log y - E.κ / 2 * y ^ 2 ≤ (1 - E.γ) * log (yPlan E) - E.κ / 2 * yPlan E ^ 2 ∧
      (y ≠ yPlan E →
        (1 - E.γ) * log y - E.κ / 2 * y ^ 2 < (1 - E.γ) * log (yPlan E) - E.κ / 2 * yPlan E ^ 2) :=
  by
  obtain ⟨_, _, _, _, hγ1, _, _, hκ, _, _⟩ := hE
  have hq : 0 < (1 - E.γ) / E.κ := div_pos (by linarith) hκ
  have hp : 0 < yPlan E := sqrt_pos.mpr hq
  have hp2 : yPlan E ^ 2 = (1 - E.γ) / E.κ := sq_sqrt hq.le
  have hlog := log_tangent (k := 1 - E.γ) (by linarith) hy hp
  have hkey : (1 - E.γ) / yPlan E = E.κ * yPlan E := by
    field_simp; rw [hp2]; field_simp
  rw [hkey] at hlog
  have hsq : -(E.κ / 2) * y ^ 2 = -(E.κ / 2) * yPlan E ^ 2 - E.κ * yPlan E * (y - yPlan E)
      - E.κ / 2 * (y - yPlan E) ^ 2 := by ring
  refine ⟨?_, fun hne => ?_⟩
  · have := mul_nonneg (by linarith : 0 ≤ E.κ / 2) (sq_nonneg (y - yPlan E))
    nlinarith
  · have hpos : 0 < (y - yPlan E) ^ 2 := by
      have : y - yPlan E ≠ 0 := sub_ne_zero.mpr hne
      positivity
    have := mul_pos (by linarith : 0 < E.κ / 2) hpos
    nlinarith

/-- Monopoly depresses output below the planner's level: `ȳ_N < ȳ_N^{PLAN}` (O&R Ex. 4(b), cf.
(25)). -/
theorem ybarN_lt_yPlan {E : Economy} (hE : E.Valid) : ybarN E < yPlan E := by
  obtain ⟨_, _, _, _, hγ1, _, _, hκ, hθ, _⟩ := hE
  unfold ybarN yPlan
  apply sqrt_lt_sqrt (div_nonneg (mul_nonneg (by linarith) (by linarith))
    (mul_nonneg hκ.le (by linarith)))
  rw [div_lt_div_iff₀ (by positivity) hκ]
  have : 0 < 1 - E.γ := by linarith
  nlinarith

/-- The gap used in Ex. 4(e): `κ[(ȳ_N^{PLAN})² − ȳ_N²] = (1−γ)/θ`. -/
theorem kappa_gap {E : Economy} (hE : E.Valid) :
    E.κ * (yPlan E ^ 2 - ybarN E ^ 2) = (1 - E.γ) / E.θ := by
  have hk := kappa_mul_ybarN_sq hE
  obtain ⟨_, _, _, _, hγ1, _, _, hκ, hθ, _⟩ := hE
  have hq : 0 ≤ (1 - E.γ) / E.κ := div_nonneg (by linarith) hκ.le
  rw [mul_sub, hk]
  unfold yPlan
  rw [sq_sqrt hq]
  field_simp
  ring

/-! ## (c) Output with preset nontradables prices, exactly -/

/-- The preset nontradables price "consistent with `M^e`": `P_N = (1−γ)M^e/ȳ_N`
(O&R Ex. 4(c)). -/
noncomputable def presetPN (E : Economy) (Me : ℝ) : ℝ := (1 - E.γ) * Me / ybarN E

/-- The preset price is the flexible-price equilibrium price when `M = M^e` (O&R Ex. 4(c)):
with CIA equality, (89), `C_T = ȳ_T` and `C_N = ȳ_N`, `P_N = (1−γ)M^e/ȳ_N`. -/
theorem flexible_PN {E : Economy} (hE : E.Valid) {Me PT PN : ℝ} (hT : 0 < PT)
    (hcia : Me = PT * E.yT + PN * ybarN E)
    (h89 : (1 - E.γ) / ybarN E = E.γ / E.yT * (PN / PT)) : PN = presetPN E Me := by
  have hy := ybarN_pos hE
  obtain ⟨_, _, _, hγ0, hγ1, _, _, _, _, hyT⟩ := hE
  unfold presetPN
  rw [hcia]
  field_simp at h89 ⊢
  nlinarith

/-- EX. 4(c), EXACT: with CIA equality `M = P_T C_T + P_N C_N`, the Cobb–Douglas condition (89),
`C_T = ȳ_T`, and `P_N` preset at `(1−γ)M^e/ȳ_N`, nontradables consumption is
`C_N = (M/M^e) ȳ_N` (so `y_N = (M/M^e) ȳ_N` by demand determination) and `P_T = γM/ȳ_T`. -/
theorem preset_output {E : Economy} (hE : E.Valid) {M Me PT cN : ℝ} (hMe : 0 < Me)
    (hT : 0 < PT) (hcN : 0 < cN) (hcia : M = PT * E.yT + presetPN E Me * cN)
    (h89 : (1 - E.γ) / cN = E.γ / E.yT * (presetPN E Me / PT)) :
    cN = M / Me * ybarN E ∧ PT = E.γ * M / E.yT := by
  have hy := ybarN_pos hE
  obtain ⟨_, _, _, hγ0, hγ1, _, _, _, _, hyT⟩ := hE
  have h1g : 0 < 1 - E.γ := by linarith
  have hPN : 0 < presetPN E Me := by unfold presetPN; positivity
  -- (89): `P_T C_T = (γ/(1−γ)) P_N C_N`
  have hsplit : PT * E.yT * (1 - E.γ) = E.γ * (presetPN E Me * cN) := by
    field_simp at h89; linarith
  have hMsplit : M * (1 - E.γ) = presetPN E Me * cN := by
    rw [hcia]; nlinarith
  refine ⟨?_, ?_⟩
  · unfold presetPN at hMsplit
    field_simp at hMsplit ⊢
    have : 0 < 1 - E.γ := by linarith
    nlinarith
  · field_simp
    nlinarith

/-- Ex. 4(c) from OPTIMALITY: in any pricing regime (preset or not), at a CIA household optimum
with `C_T = ȳ_T` and `P_{N,t}` preset at `(1−γ)M^e_t/ȳ_N`, the household's nontradables demand is
`(M_t/M^e_t) ȳ_N` and `P_{T,t} = γM_t/ȳ_T` at every date. -/
theorem preset_output_of_optimal {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {rev : ℕ → ℝ → ℝ} {Ys : ℕ → Set ℝ} {A0 : ℝ} {c : ℕ → Choice}
    (hopt : CIAOptimal E Q rev Ys A0 c) {Me : ℕ → ℝ} (hMe : ∀ t, 0 < Me t)
    (hcT : ∀ t, (c t).cT = E.yT) (hPN : ∀ t, Q.PN t = presetPN E (Me t)) (t : ℕ) :
    (c t).cN = (c t).money / Me t * ybarN E ∧ Q.PT t = E.γ * (c t).money / E.yT := by
  have h89 := cia_intra_of_optimal hE hQ hopt t
  obtain ⟨⟨_, hb, hn, _⟩, hcia, _⟩ := hopt.1 t
  rw [hcT t, hPN t] at hcia
  simp only [relPrice] at h89
  rw [hcT t, hPN t] at h89
  exact preset_output hE (hMe t) (hQ t).1 hb hcia h89

/-- Ex. 4(c), FINITE-STATE VERSION: with a random money supply `M(s)` on finitely many states
`s` with probabilities `p_s`, and `P_N` preset at the level consistent with `M^e = E[M]`,
output is `(M(s)/M^e) ȳ_N` state by state, and expected output equals `ȳ_N`. -/
theorem preset_output_finite_state {S : Type*} [Fintype S] {E : Economy} (hE : E.Valid)
    {p M PT cN : S → ℝ}
    (hMe : 0 < ∑ s, p s * M s) (hT : ∀ s, 0 < PT s) (hcN : ∀ s, 0 < cN s)
    (hcia : ∀ s, M s = PT s * E.yT + presetPN E (∑ s', p s' * M s') * cN s)
    (h89 : ∀ s, (1 - E.γ) / cN s = E.γ / E.yT * (presetPN E (∑ s', p s' * M s') / PT s)) :
    (∀ s, cN s = M s / (∑ s', p s' * M s') * ybarN E) ∧ ∑ s, p s * cN s = ybarN E := by
  have hstate : ∀ s, cN s = M s / (∑ s', p s' * M s') * ybarN E := fun s =>
    (preset_output hE hMe (hT s) (hcN s) (hcia s) (h89 s)).1
  refine ⟨hstate, ?_⟩
  simp_rw [hstate]
  have e : ∀ s, p s * (M s / (∑ s', p s' * M s') * ybarN E)
      = (p s * M s) * (ybarN E / ∑ s', p s' * M s') := by intro s; ring
  simp_rw [e]
  rw [← Finset.sum_mul, mul_div_cancel₀ _ hMe.ne']

/-! ## (d) The authority's objective and the one-shot assumption -/

/-- Period utility along a money path under (c): `γ log ȳ_T + (1−γ) log C_N − (κ/2) y_N²` with
`C_N = y_N = (M/M^e) ȳ_N` (O&R Ex. 4(c)–(d)). -/
noncomputable def utilAt (E : Economy) (M Me : ℝ) : ℝ :=
  E.γ * log E.yT + (1 - E.γ) * log (M / Me * ybarN E) - E.κ / 2 * (M / Me * ybarN E) ^ 2

/-- Money carried into date `s`: `M_{−1}` at `s = 0` (O&R Ex. 4(d)). -/
def lagMoney (Mm1 : ℝ) (M : ℕ → ℝ) : ℕ → ℝ
  | 0 => Mm1
  | s + 1 => M s

/-- The authority's objective of Ex. 4(d), p. 714: `U_t − (χ/2)(P_{T,t}/P_{T,t−1})²`, with
`P_T ∝ M` by (c), from date `t` (Lean date 0). -/
noncomputable def authObj (E : Economy) (Mm1 : ℝ) (M Me : ℕ → ℝ) : ℝ :=
  ∑' s, E.β ^ s * utilAt E (M s) (Me s) - E.χ / 2 * (M 0 / Mm1) ^ 2

/-- The one-shot objective of Ex. 4(d): `(1−γ) log C_N − (κ/2) y_N² − (χ/2)(P_{T,t}/P_{T,t−1})²`. -/
noncomputable def oneShotObj (E : Economy) (Mm1 Me M : ℝ) : ℝ :=
  (1 - E.γ) * log (M / Me * ybarN E) - E.κ / 2 * (M / Me * ybarN E) ^ 2
    - E.χ / 2 * (M / Mm1) ^ 2

/-- Tradables inflation equals money growth: by (c), `P_{T,t}/P_{T,t−1} = M_t/M_{t−1}`
(O&R Ex. 4(d)). -/
theorem inflation_eq_money_growth {E : Economy} (hE : E.Valid) {M M' : ℝ} (hM' : 0 < M') :
    (E.γ * M / E.yT) / (E.γ * M' / E.yT) = M / M' := by
  obtain ⟨_, _, _, hγ0, _, _, _, _, _, hyT⟩ := hE
  field_simp

/-- EX. 4(d), THE ONE-SHOT REDUCTION: if the date-`t` money supply is changed while expectations
`M^e` and the future path `M_s`, `s > t`, are held fixed (one-shot play: future real allocations
do not respond), the authority's objective changes by exactly the change in the one-shot
objective `(1−γ) log C_N − (κ/2) y_N² − (χ/2)(P_{T,t}/P_{T,t−1})²`. -/
theorem authObj_sub {E : Economy} {Mm1 : ℝ} {M M' Me : ℕ → ℝ}
    (hsum : Summable fun s => E.β ^ s * utilAt E (M s) (Me s)) (hfut : ∀ s, s ≠ 0 → M' s = M s) :
    authObj E Mm1 M' Me - authObj E Mm1 M Me
      = oneShotObj E Mm1 (Me 0) (M' 0) - oneShotObj E Mm1 (Me 0) (M 0) := by
  have hoff : ∀ s ∉ ({0} : Finset ℕ),
      E.β ^ s * utilAt E (M' s) (Me s) = E.β ^ s * utilAt E (M s) (Me s) := by
    intro s hs; rw [hfut s (by simpa using hs)]
  obtain ⟨_, htsum⟩ := tsum_eq_add_of_eq_off hsum {0} hoff
  unfold authObj
  rw [htsum, Finset.sum_singleton, pow_zero, one_mul, one_mul]
  unfold oneShotObj utilAt
  ring

/-- The authority's objective INCLUDING every future inflation penalty
`Σ_s β^s (χ/2)(M_s/M_{s−1})²` (the dynamic objective that the one-shot game does not use). -/
noncomputable def fullObj (E : Economy) (Mm1 : ℝ) (M Me : ℕ → ℝ) : ℝ :=
  ∑' s, E.β ^ s * (utilAt E (M s) (Me s) - E.χ / 2 * (M s / lagMoney Mm1 M s) ^ 2)

/-- WHAT THE ONE-SHOT ASSUMPTION DROPS (O&R Ex. 4(d), made explicit): if the future money path is
held fixed IN LEVELS and the next-period inflation penalty is counted, a change in `M_t` changes
the objective by the one-shot change MINUS `β(χ/2)[(M_{t+1}/M_t')² − (M_{t+1}/M_t)²]`. The
one-shot game ignores exactly this channel (the effect of `M_t` on next period's inflation). -/
theorem fullObj_sub {E : Economy} {Mm1 : ℝ} {M M' Me : ℕ → ℝ}
    (hsum : Summable fun s => E.β ^ s *
      (utilAt E (M s) (Me s) - E.χ / 2 * (M s / lagMoney Mm1 M s) ^ 2))
    (hfut : ∀ s, s ≠ 0 → M' s = M s) :
    fullObj E Mm1 M' Me - fullObj E Mm1 M Me
      = (oneShotObj E Mm1 (Me 0) (M' 0) - oneShotObj E Mm1 (Me 0) (M 0))
        - E.β * (E.χ / 2) * ((M 1 / M' 0) ^ 2 - (M 1 / M 0) ^ 2) := by
  have hlag : ∀ s, 2 ≤ s → lagMoney Mm1 M' s = lagMoney Mm1 M s := by
    intro s hs
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    simp only [lagMoney]; exact hfut k (by omega)
  have hoff : ∀ s ∉ ({0, 1} : Finset ℕ),
      E.β ^ s * (utilAt E (M' s) (Me s) - E.χ / 2 * (M' s / lagMoney Mm1 M' s) ^ 2)
        = E.β ^ s * (utilAt E (M s) (Me s) - E.χ / 2 * (M s / lagMoney Mm1 M s) ^ 2) := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
    rw [hfut s hs.1, hlag s (by omega)]
  obtain ⟨_, htsum⟩ := tsum_eq_add_of_eq_off hsum {0, 1} hoff
  unfold fullObj
  rw [htsum, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  simp only [lagMoney, pow_zero, pow_one, one_mul, hfut 1 one_ne_zero]
  unfold oneShotObj utilAt
  ring

/-! ## (e) The one-shot game -/

/-- The one-shot objective in money-growth form with penalty `(χ/2)(μ − a)²`: `a = 0` is the
book's gross-inflation penalty, `a = 1` the conventional `(π − 1)²` one (O&R Ex. 4(d)–(e)).
Here `μ = M_t/M_{t−1}` and `μ^e = M^e_t/M_{t−1}`. -/
noncomputable def gameObj (E : Economy) (a μe μ : ℝ) : ℝ :=
  (1 - E.γ) * log (μ / μe * ybarN E) - E.κ / 2 * (μ / μe * ybarN E) ^ 2 - E.χ / 2 * (μ - a) ^ 2

/-- The book's one-shot objective in money-growth form: `oneShotObj` at `M_t = μM_{t−1}`,
`M^e_t = μ^e M_{t−1}` is `gameObj` with `a = 0` (O&R Ex. 4(e)). -/
theorem oneShotObj_eq_gameObj {E : Economy} {Mm1 μe μ : ℝ} (hM : 0 < Mm1) (hμe : 0 < μe) :
    oneShotObj E Mm1 (μe * Mm1) (μ * Mm1) = gameObj E 0 μe μ := by
  unfold oneShotObj gameObj
  rw [show μ * Mm1 / (μe * Mm1) = μ / μe by field_simp, show μ * Mm1 / Mm1 = μ by field_simp,
    sub_zero]

/-- The best-response condition: `(1−γ)/μ = (κȳ_N²/μ^{e2}) μ + χ(μ − a)` (O&R Ex. 4(e)). -/
def BestResponseFOC (E : Economy) (a μe μ : ℝ) : Prop :=
  (1 - E.γ) / μ = E.κ * ybarN E ^ 2 / μe ^ 2 * μ + E.χ * (μ - a)

/-- BEST RESPONSE (O&R Ex. 4(e)): for given expectations `μ^e > 0`, `μ > 0` maximises the
one-shot objective over all positive money growth IF AND ONLY IF the first-order condition holds
(strict concavity); moreover the maximiser is then strict. -/
theorem gameObj_max_iff {E : Economy} (hE : E.Valid) {a μe μ : ℝ} (hμe : 0 < μe) (hμ : 0 < μ) :
    (∀ ν, 0 < ν → gameObj E a μe ν ≤ gameObj E a μe μ) ↔ BestResponseFOC E a μe μ := by
  have hy := ybarN_pos hE
  obtain ⟨_, _, _, _, hγ1, hχ, _, hκ, _, _⟩ := hE
  set k := E.κ * ybarN E ^ 2 / μe ^ 2 with hk
  have hk0 : 0 < k := by positivity
  have hform : ∀ ν, 0 < ν → gameObj E a μe ν
      = (1 - E.γ) * log ν - (k + E.χ) / 2 * ν ^ 2 + E.χ * a * ν
        + ((1 - E.γ) * log (ybarN E / μe) - E.χ / 2 * a ^ 2) := by
    intro ν hν
    unfold gameObj
    rw [show ν / μe * ybarN E = ν * (ybarN E / μe) by ring, log_mul hν.ne' (by positivity), hk]
    field_simp
    ring
  constructor
  · intro hmax
    have hloc : IsLocalMax (fun ν => (1 - E.γ) * log ν - (k + E.χ) / 2 * ν ^ 2 + E.χ * a * ν) μ
        := by
      filter_upwards [Ioi_mem_nhds hμ] with ν hν
      have h1 := hmax ν hν
      rw [hform ν hν, hform μ hμ] at h1
      linarith
    have h1 := (hasDerivAt_log hμ.ne').const_mul (1 - E.γ)
    have h2 := (hasDerivAt_pow 2 μ).const_mul ((k + E.χ) / 2)
    have h3 := (hasDerivAt_id' μ).const_mul (E.χ * a)
    have hd := (h1.sub h2).add h3
    have h0 := hloc.hasDerivAt_eq_zero hd
    unfold BestResponseFOC
    rw [← hk]
    norm_num at h0
    field_simp at h0 ⊢
    linarith
  · intro hfoc ν hν
    unfold BestResponseFOC at hfoc
    rw [← hk] at hfoc
    rw [hform ν hν, hform μ hμ]
    have hlog := log_tangent (k := 1 - E.γ) (by linarith) hν hμ
    have hsq := mul_nonneg (by linarith : 0 ≤ (k + E.χ) / 2) (sq_nonneg (ν - μ))
    have e : (1 - E.γ) / μ * ν - (1 - E.γ) / μ * μ = (k * μ + E.χ * (μ - a)) * (ν - μ) := by
      rw [hfoc]; ring
    nlinarith

/-- EXISTENCE AND UNIQUENESS OF THE BEST RESPONSE (O&R Ex. 4(e)): for every `μ^e > 0` there is
exactly one `μ > 0` satisfying the best-response condition (a quadratic with one positive root).
-/
theorem bestResponse_exists_unique {E : Economy} (hE : E.Valid) {a μe : ℝ} (hμe : 0 < μe) :
    ∃ μ, 0 < μ ∧ BestResponseFOC E a μe μ ∧ ∀ ν, 0 < ν → BestResponseFOC E a μe ν → ν = μ := by
  have hy := ybarN_pos hE
  obtain ⟨_, _, _, _, hγ1, hχ, _, hκ, _, _⟩ := hE
  set K := E.κ * ybarN E ^ 2 / μe ^ 2 + E.χ with hK
  have hK0 : 0 < K := by positivity
  set D := (E.χ * a) ^ 2 + 4 * K * (1 - E.γ) with hD
  have hD0 : 0 < D := by have : 0 < 1 - E.γ := by linarith
                         positivity
  set μ := (E.χ * a + sqrt D) / (2 * K) with hμdef
  have hsD : sqrt D ^ 2 = D := sq_sqrt hD0.le
  have hsDgt : |E.χ * a| < sqrt D := by
    rw [← sqrt_sq_eq_abs]
    apply sqrt_lt_sqrt (sq_nonneg _)
    have : 0 < 1 - E.γ := by linarith
    rw [hD]; nlinarith
  have hμ0 : 0 < μ := by
    apply div_pos _ (by positivity)
    have := neg_abs_le (E.χ * a); linarith
  have hfoc_iff : ∀ ν, 0 < ν → (BestResponseFOC E a μe ν ↔ K * ν ^ 2 - E.χ * a * ν
      - (1 - E.γ) = 0) := by
    intro ν hν
    unfold BestResponseFOC
    rw [hK]
    constructor
    · intro h; rw [div_eq_iff hν.ne'] at h; linear_combination -h
    · intro h; rw [div_eq_iff hν.ne']; linear_combination -h
  have hroot : K * μ ^ 2 - E.χ * a * μ - (1 - E.γ) = 0 := by
    have e1 : K * μ ^ 2 - E.χ * a * μ = (sqrt D ^ 2 - (E.χ * a) ^ 2) / (4 * K) := by
      rw [hμdef]; field_simp; ring
    rw [e1, hsD, hD]; field_simp; ring
  refine ⟨μ, hμ0, (hfoc_iff μ hμ0).mpr hroot, fun ν hν hfν => ?_⟩
  have hν' := (hfoc_iff ν hν).mp hfν
  -- two positive roots of the same quadratic coincide
  have hfac : K * (ν - μ) * (ν + μ - E.χ * a / K) = 0 := by
    field_simp; nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hK0.ne'
    · linarith
  · -- `ν + μ = χa/K` contradicts `μ > (χa + |χa|)/(2K) ≥ χa/K` and `ν > 0`
    have hμbig : E.χ * a / K < μ := by
      rw [hμdef, div_lt_div_iff₀ hK0 (by positivity)]
      have := le_abs_self (E.χ * a)
      nlinarith
    linarith

/-- A one-shot (rational-expectations) equilibrium (O&R Ex. 4(e)): money growth `μ > 0` that is
the best response to the expectation `μ^e = μ`. -/
def IsOneShotEquilibrium (E : Economy) (a μ : ℝ) : Prop :=
  0 < μ ∧ ∀ ν, 0 < ν → gameObj E a μ ν ≤ gameObj E a μ μ

/-- THE ONE-SHOT EQUILIBRIUM IS UNIQUE (O&R Ex. 4(e)): with penalty `(χ/2)(μ − a)²`,
`μ` is an equilibrium IFF `μ = [a + (a² + 4(1−γ)/(θχ))^{1/2}]/2`. -/
theorem oneShotEquilibrium_iff {E : Economy} (hE : E.Valid) {a μ : ℝ} :
    IsOneShotEquilibrium E a μ ↔
      μ = (a + sqrt (a ^ 2 + 4 * (1 - E.γ) / (E.θ * E.χ))) / 2 := by
  have hk := kappa_mul_ybarN_sq hE
  have hE' := hE
  obtain ⟨_, _, _, _, hγ1, hχ, _, hκ, hθ, _⟩ := hE'
  set D := a ^ 2 + 4 * (1 - E.γ) / (E.θ * E.χ) with hD
  have hD0 : 0 < D := by
    have : 0 < 1 - E.γ := by linarith
    have : 0 < E.θ := by linarith
    positivity
  have hsD : sqrt D ^ 2 = D := sq_sqrt hD0.le
  have hsDgt : |a| < sqrt D := by
    rw [← sqrt_sq_eq_abs]
    apply sqrt_lt_sqrt (sq_nonneg _)
    have : 0 < 1 - E.γ := by linarith
    have : 0 < E.θ := by linarith
    rw [hD]; have : 0 < 4 * (1 - E.γ) / (E.θ * E.χ) := by positivity
    linarith
  set μs := (a + sqrt D) / 2 with hμs
  have hμs0 : 0 < μs := by have := neg_abs_le a; rw [hμs]; linarith
  -- the equilibrium condition in quadratic form
  have hquad : ∀ ν, 0 < ν → (BestResponseFOC E a ν ν ↔ ν ^ 2 - a * ν - (1 - E.γ) / (E.θ * E.χ)
      = 0) := by
    intro ν hν
    unfold BestResponseFOC
    have hθ0 : 0 < E.θ := by linarith
    have e : E.κ * ybarN E ^ 2 = (E.θ - 1) * (1 - E.γ) / E.θ := hk
    constructor
    · intro h
      rw [e] at h
      field_simp at h ⊢
      nlinarith
    · intro h
      rw [e]
      field_simp at h ⊢
      nlinarith
  have hroot : μs ^ 2 - a * μs - (1 - E.γ) / (E.θ * E.χ) = 0 := by
    have e1 : μs ^ 2 - a * μs = (sqrt D ^ 2 - a ^ 2) / 4 := by rw [hμs]; ring
    rw [e1, hsD, hD]; ring
  constructor
  · rintro ⟨hμ, hmax⟩
    have hfoc := (gameObj_max_iff hE hμ hμ).mp hmax
    have hq := (hquad μ hμ).mp hfoc
    have hfac : (μ - μs) * (μ + μs - a) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · have : a < μs := by have := le_abs_self a; rw [hμs]; linarith
      linarith
  · intro h
    rw [h]
    exact ⟨hμs0, (gameObj_max_iff hE hμs0 hμs0).mpr ((hquad μs hμs0).mpr hroot)⟩

/-- EX. 4(e), THE BOOK'S ANSWER (gross-inflation penalty, `a = 0`): the unique one-shot
equilibrium money growth is `M_t/M_{t−1} = P_{T,t}/P_{T,t−1} = ((1−γ)/(χθ))^{1/2}
= {κ[(ȳ_N^{PLAN})² − ȳ_N²]/χ}^{1/2}`. -/
theorem book_equilibrium {E : Economy} (hE : E.Valid) {μ : ℝ} :
    IsOneShotEquilibrium E 0 μ ↔ μ = sqrt ((1 - E.γ) / (E.χ * E.θ)) ∧
      sqrt ((1 - E.γ) / (E.χ * E.θ)) = sqrt (E.κ * (yPlan E ^ 2 - ybarN E ^ 2) / E.χ) := by
  have hgap := kappa_gap hE
  have hE' := hE
  obtain ⟨_, _, _, _, hγ1, hχ, _, _, hθ, _⟩ := hE'
  have hsame : sqrt ((1 - E.γ) / (E.χ * E.θ)) = sqrt (E.κ * (yPlan E ^ 2 - ybarN E ^ 2) / E.χ) := by
    rw [hgap]; congr 1; field_simp
  have hq : (0 + sqrt (0 ^ 2 + 4 * (1 - E.γ) / (E.θ * E.χ))) / 2
      = sqrt ((1 - E.γ) / (E.χ * E.θ)) := by
    have hpos : 0 ≤ (1 - E.γ) / (E.χ * E.θ) := by
      have : 0 < 1 - E.γ := by linarith
      have : 0 < E.θ := by linarith
      positivity
    rw [zero_add, show (0 : ℝ) ^ 2 + 4 * (1 - E.γ) / (E.θ * E.χ)
        = 2 ^ 2 * ((1 - E.γ) / (E.χ * E.θ)) by field_simp; ring,
      sqrt_mul (by norm_num), sqrt_sq (by norm_num)]
    ring
  rw [oneShotEquilibrium_iff hE, hq]
  exact ⟨fun h => ⟨h, hsame⟩, fun h => h.1⟩

/-- EX. 4(e) WITH THE CONVENTIONAL `(π − 1)²` PENALTY (`a = 1`, flagged): the unique one-shot
equilibrium is `μ = [1 + (1 + 4(1−γ)/(θχ))^{1/2}]/2`, which differs from the book's answer, and
exceeds one (an inflation bias). -/
theorem conventional_equilibrium {E : Economy} (hE : E.Valid) {μ : ℝ} :
    IsOneShotEquilibrium E 1 μ ↔ μ = (1 + sqrt (1 + 4 * (1 - E.γ) / (E.θ * E.χ))) / 2 := by
  rw [oneShotEquilibrium_iff hE, one_pow]

/-- The conventional-penalty equilibrium exhibits an inflation bias: `μ > 1` (O&R Ex. 4(e)). -/
theorem conventional_inflation_bias {E : Economy} (hE : E.Valid) {μ : ℝ}
    (h : IsOneShotEquilibrium E 1 μ) : 1 < μ := by
  rw [conventional_equilibrium hE] at h
  obtain ⟨_, _, _, _, hγ1, hχ, _, _, hθ, _⟩ := hE
  have hpos : 0 < 4 * (1 - E.γ) / (E.θ * E.χ) := by
    have : 0 < 1 - E.γ := by linarith
    have : 0 < E.θ := by linarith
    positivity
  have : 1 < sqrt (1 + 4 * (1 - E.γ) / (E.θ * E.χ)) := by
    rw [lt_sqrt zero_le_one]; linarith
  rw [h]; linarith

/-- Under commitment (expectations equal to the choice, so output is `ȳ_N` whatever `μ`), the
conventional penalty is minimised exactly at `μ = 1`: the discretionary equilibrium is
inflationary relative to commitment (O&R Ex. 4, cf. Chapter 9). -/
theorem commitment_conventional {E : Economy} (hE : E.Valid) {μ : ℝ} (hμ : 0 < μ) :
    gameObj E 1 μ μ ≤ gameObj E 1 1 1 ∧ (μ ≠ 1 → gameObj E 1 μ μ < gameObj E 1 1 1) := by
  have hχ := hE.2.2.2.2.2.1
  unfold gameObj
  rw [div_self hμ.ne', div_self one_ne_zero, sub_self]
  refine ⟨?_, fun hne => ?_⟩
  · have := mul_nonneg (by linarith : 0 ≤ E.χ / 2) (sq_nonneg (μ - 1)); linarith
  · have : 0 < (μ - 1) ^ 2 := by have : μ - 1 ≠ 0 := sub_ne_zero.mpr hne
                                 positivity
    have := mul_pos (by linarith : 0 < E.χ / 2) this; linarith

/-- The literal gross-inflation penalty has NO commitment optimum (flag on Ex. 4(d)): under
commitment every `μ > 0` is strictly beaten by `μ/2`, since the penalty `(χ/2)μ²` is minimised
only at zero money. -/
theorem commitment_gross_no_optimum {E : Economy} (hE : E.Valid) {μ : ℝ} (hμ : 0 < μ) :
    gameObj E 0 μ μ < gameObj E 0 (μ / 2) (μ / 2) := by
  have hχ := hE.2.2.2.2.2.1
  unfold gameObj
  rw [div_self hμ.ne', div_self (by positivity : μ / 2 ≠ 0), sub_zero, sub_zero]
  have h3 : E.χ / 2 * (μ / 2) ^ 2 < E.χ / 2 * μ ^ 2 := by
    have : (μ / 2) ^ 2 < μ ^ 2 := by nlinarith
    exact mul_lt_mul_of_pos_left this (by linarith)
  linarith

end ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility
