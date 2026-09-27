# Source map

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Chapter 1, “Intertemporal Trade and the Current Account Balance” (pp. 1–58).
Equation numbers are the book's; page numbers are book pages. Lean names are
relative to `ObstfeldRogoff.IntertemporalTrade`. Where the Lean statement adds
a hypothesis the book leaves implicit, or departs from the printed claim, see
[corrections](corrections.md).

## §1.1 A small two-period endowment economy (pp. 1–14)

| Book | Claim | Lean |
| --- | --- | --- |
| (1.1), p. 1 | Lifetime utility `u(C₁) + βu(C₂)` | `Consumer.Household`, `Consumer.Household.utility` |
| (1.2), p. 2 | Intertemporal budget constraint | `Economy.Budget`, `Consumer.Household.Feasible`, `Consumer.Household.feasible_iff_budget` |
| p. 7 | Budget line `C₂ = Y₂ − (1 + r)(C₁ − Y₁)` | `Economy.budget_iff`, `Consumer.Household.optimal_binds` |
| p. 3 | The optimum is unique (strict concavity) | `Consumer.Household.optimal_unique` |
| (1.3)–(1.4), p. 3 | Euler equation, necessary | `Consumer.Household.euler_of_optimal` |
| (1.3), p. 3 | Euler equation, sufficient | `Consumer.Household.optimal_of_euler`, `Consumer.Household.isOptimal_iff_euler` |
| (1.5), p. 3 | Flat consumption when `β(1 + r) = 1`, `C̄ = ((1 + r)Y₁ + Y₂)/(2 + r)` | `Consumer.Household.flat_of_beta_mul_eq_one`, `Consumer.Household.flat_level` |
| p. 4 | Consumption tilts up iff `β(1 + r) > 1` | `Consumer.Household.tilt_up`, `Consumer.Household.tilt_down` |
| fn 1, p. 2 | An optimum exists under the Inada condition | `Consumer.Household.exists_optimal` |
| (1.6), pp. 6–7 | Current account; GNP − GDP = rB | `Economy.ca1`, `Economy.ca2`, `CurrentAccount.gnp_sub_gdp` |
| p. 7 | `CA₁ + CA₂ = 0`, `CA₂ = −CA₁` | `Economy.ca1_add_ca2`, `CurrentAccount.ca2_eq_neg_ca1` |
| Fig. 1.1, p. 8; p. 10 | Gains from trade, strict when the country trades | `Consumer.Household.utility_endowment_le`, `Consumer.Household.utility_endowment_lt` |
| (1.7), p. 9 | Autarky rate `β u'(Y₂)/u'(Y₁) = 1/(1 + r^A)`; it is unique | `Consumer.Household.isAutarkyRate_iff`, `Consumer.Household.autarkyRate_unique` |
| pp. 9–10 | Trade pattern: `r > r^A` ⇒ lend, `r < r^A` ⇒ borrow (revealed preference; strict with `u'`) | `Consumer.Household.saving_nonneg_of_autarky_lt`, `saving_nonpos_of_lt_autarky`, `saving_pos_of_autarky_lt`, `saving_neg_of_lt_autarky` |
| p. 10 | Welfare rises with the distance between `r` and `r^A` | `Consumer.Household.utility_mono_of_autarky_le`, `utility_anti_of_le_autarky`, `utility_strictMono_of_autarky_le`, `utility_strictAnti_of_le_autarky`, `utility_lt_of_lends`, `utility_lt_of_borrows` |
| p. 10 | `r^A` falls with `Y₁`, rises with `Y₂`, falls with `β` | `Consumer.autarkyGross_anti_Y1`, `Consumer.autarkyGross_mono_Y2`, `Consumer.autarkyGross_anti_beta` |
| (1.8), p. 11 | Budget with government spending; current accounts sum to zero | `CurrentAccount.budgetG_iff`, `CurrentAccount.caG1_add_caG2` |
| p. 11 | Flat consumption: `CA₁ = (Y₁ − Y₂)/(2 + r)`; permanent shocks leave it unchanged, temporary ones move it | `CurrentAccount.ca1_of_optimal`, `CurrentAccount.caG1_of_flat`, `CurrentAccount.flatCA1_permanent`, `flatCA1_strictMono_Y1`, `flatCA1_strictAnti_Y2` |
| p. 12 | Temporary `G₁` gives `CA₁ = −G₁/(2 + r) < 0`; permanent `G` gives `CA = 0` | `CurrentAccount.temporary_government_deficit`, `CurrentAccount.permanent_government_balanced`, `CurrentAccount.flat_level_G` |

## §1.2 The role of investment (pp. 14–22)

| Book | Claim | Lean |
| --- | --- | --- |
| (1.11)–(1.13), p. 15 | `ΔB = CA` iff `Δ(B + K) = S`, given `K' = K + I` | `Investment.nfa_change_iff_wealth_change` |
| (1.12)–(1.14), pp. 15–16 | `CA = S − I` | `Investment.currentAccount_eq_saving_sub_investment`, `Investment.ca1_eq_currentAccount` |
| (1.15), p. 17 | The two period identities with `B₁ = B₃ = 0` ⇔ (1.15) | `Investment.intertemporal_budget_iff`, `Investment.consumption2_budget` |
| (1.16), p. 17 | The reduced problem | `Investment.budget_iff_consumption2`, `Investment.consumption2_eq_pv` |
| (1.17), p. 17 | `F'(K₂) = r`, and its converse under concavity | `Investment.capital_foc`, `Investment.profit_max_of_deriv_eq`, `Investment.optimal_capital_eq_of_deriv` |
| (1.3)/(1.16), p. 17 | Euler equation with investment | `Investment.consumption_foc` |
| p. 19 | **Fisher separation**: optimal `K₂` maximises `F(K) − rK` for any preferences and government spending; unique under strict concavity | `Investment.fisher_separation`, `Investment.profit_maximizer_unique`, `Investment.fisher_separation_independent` |
| p. 19 | Government spending does not crowd out investment | `Investment.no_crowding_out` |
| p. 21 | The production point maximises the PV of net output | `Investment.pvNetOutput_eq`, `Investment.fisher_separation_pv` |
| (1.18), p. 19 | The PPF | `Investment.ppf_no_government`, `Investment.consumption2_autarky` |
| p. 20; fn 13 | PPF intercepts | `Investment.ppf_horizontal_intercept`, `Investment.ppf_vertical_intercept` |
| p. 20; fn 12 | PPF slope `−[1 + F'(K₂)]`, curvature `F''(K₂)`, strict concavity | `Investment.ppf_hasDerivAt`, `Investment.ppf_slope_hasDerivAt`, `Investment.ppf_strictConcaveOn` |
| p. 21 | Government shifts the PPF left by `G₁`, down by `G₂` | `Investment.ppf_shift` |
| pp. 20–21 | Autarky tangency `r^A = F'(K₂)`; market clearing | `Investment.autarky_tangency`, `Investment.autarky_market_clearing` |
| p. 21 | Gains from trade with investment | `Investment.gains_from_trade`, `Investment.optimum_solves_wealth_problem` |
| p. 22, Fig. 1.4 | Temporary `G₁` ⇒ deficit, `G₂` ⇒ surplus (under normality) | `Investment.consumption_smoothing`, `Investment.ca1_strictAnti_G1`, `Investment.temporary_G1_deficit`, `Investment.ca1_strictMono_G2`, `Investment.future_G2_surplus` |

## §1.3 A two-region world economy (pp. 23–42)

| Book | Claim | Lean |
| --- | --- | --- |
| (1.19), p. 23 | World equilibrium; Walras's law | `WorldEquilibrium.IsEquilibrium`, `WorldEquilibrium.walras_law` |
| p. 23, Fig. 1.5 | `r^A < r < r^{A*}`; the low-`r^A` country lends | `WorldEquilibrium.rate_between_autarky`, `WorldEquilibrium.trade_pattern` |
| — | Existence of an equilibrium (continuity of optimal consumption + IVT) | `WorldEquilibrium.continuousAt_optimal_c1`, `WorldEquilibrium.exists_autarkyRate`, `WorldEquilibrium.exists_equilibrium` |
| p. 33 | The equilibrium is Pareto optimal | `WorldEquilibrium.first_welfare_theorem`, `WorldEquilibrium.cost_ge_of_utility_ge`, `WorldEquilibrium.cost_gt_of_utility_gt` |
| (1.20), p. 28 | `log(C₂/C₁) = σ log(1 + r) + σ log β` | `Isoelastic.log_growth_isoelastic` |
| (1.21), p. 28 | Elasticity of intertemporal substitution | `Isoelastic.eis` |
| (1.22), p. 28 | Isoelastic utility has constant EIS `σ`; conversely constant EIS ⇒ affine transform of isoelastic | `Isoelastic.isoU`, `Isoelastic.hasDerivAt_isoU`, `Isoelastic.deriv_deriv_isoU`, `Isoelastic.eis_isoU`, `Isoelastic.eq_affine_isoU_of_eis_const` |
| fn 14, p. 28 | `(C^{1−1/σ} − 1)/(1 − 1/σ) → log C` as `σ → 1` | `Isoelastic.tendsto_normalised_isoU_log` |
| (1.23), p. 29 | `dC₁/dr` for general `u` | `Isoelastic.dC1_dr_general`, `Isoelastic.general_formula_eq_isoelastic` |
| (1.24), p. 29 | `dC₁/dr` for isoelastic `u`; negative for a borrower | `Isoelastic.hasDerivAt_consC1`, `Isoelastic.deriv_consC1_neg_of_borrower` |
| (1.25)–(1.26), p. 30 | Isoelastic closed forms; log case, spending share `1/(1 + β)` | `Isoelastic.euler_iff_growth`, `Isoelastic.euler_budget_iff_closed_form`, `Isoelastic.consC1`, `Isoelastic.consC2`, `Isoelastic.consC1_log`, `Isoelastic.log_euler_budget_iff` |
| p. 34 | `dK₂/dA₂ = −F'(K₂)/(A₂F''(K₂)) > 0` at given `r` | `WorldEquilibrium.hasDerivAt_capital_productivity`, `WorldEquilibrium.capital_increasing_in_productivity` |
| pp. 36–38 | Blanchard–Summers: saving shift exceeds investment shift iff `α < 1` | `WorldEquilibrium.blanchard_summers` |
| p. 39 | Expenditure function and Hicksian demands | `Duality.ExpenditureSystem` |
| (1.27), p. 39; fn 18 | Shephard's lemma `E_R = C₂^H`; `C₁^H = E − R E_R` | `Duality.ExpenditureSystem.E_le_hicksian_cost`, `Duality.ExpenditureSystem.shephard`, `Duality.ExpenditureSystem.C1H_eq_E_sub`, `Duality.ExpenditureSystem.hasDerivAt_E_of_hicksian`, `Duality.ExpenditureSystem.hicksian_tangency` |
| (1.28), p. 40 | `E_U · dU₁/dR = Y₂ − C₂` | `Duality.ExpenditureSystem.welfare_effect`, `Duality.ExpenditureSystem.welfare_rises_iff` |
| (1.29)–(1.31), p. 41 | Duality identity, Slutsky equation, total effect | `Duality.ExpenditureSystem.slutsky`, `Duality.ExpenditureSystem.total_effect` |
| p. 42 | Isoelastic Hicksian demand, expenditure function, closed-form (1.27)–(1.31) | `Duality.Iso.system`, `Duality.Iso.le_cost`, `Duality.Iso.shephard_iso`, `Duality.Iso.duality_identity_iso`, `Duality.Iso.slutsky_iso`, `Duality.Iso.total_effect_iso` |
| p. 42 | `dC₁/dR` in two forms; equivalent to (1.24) | `Duality.Iso.hasDerivAt_C1_total`, `Duality.Iso.hasDerivAt_C1_total_euler`, `Duality.Iso.hasDerivAt_C1_r_eq24` |

## §1.4 Taxation of foreign borrowing and lending (pp. 42–45)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 42 | Foreign's saving `S₁*(r)` comes from log optimisation; Foreign lends iff `r > r^{A*}` | `OptimalTax.Foreign.household_optimal`, `OptimalTax.Foreign.saving`, `OptimalTax.Foreign.saving_pos_iff` |
| p. 43 | Market clearing ⇔ `1 + r = Y₂*/[(1 + β*)(Y₁ − C₁) + β*Y₁*]`; `r` rises with `C₁` | `OptimalTax.Foreign.market_clearing_iff`, `OptimalTax.Foreign.rate_strictMonoOn` |
| (1.32), p. 43 | Foreign offer curve TT, equal to Home's budget line at the induced rate | `OptimalTax.Foreign.offer`, `OptimalTax.Foreign.offer_eq_budget` |
| p. 43, Fig. 1.11 | TT passes through A with slope `−(1 + r^{A*})`; TT is strictly concave and decreasing | `OptimalTax.Foreign.offer_endowment`, `OptimalTax.Foreign.offer_slope_endowment`, `OptimalTax.Foreign.offer_strictConcaveOn`, `OptimalTax.Foreign.offer_strictAntiOn` |
| p. 43 | B lies on TT; part of TT lies strictly outside the laissez-faire budget line | `OptimalTax.laissezFaire_on_offer`, `OptimalTax.laissezFaire_borrows`, `OptimalTax.offer_above_laissezFaire_line` |
| p. 43 | The planner optimum C is characterised by tangency | `OptimalTax.planner_tangency`, `OptimalTax.plannerOptimal_of_tangency` |
| Fig. 1.11; p. 44 | `Y₁ < C₁^C < C₁^B` and `r^{A*} < r^τ < r^L` | `OptimalTax.planner_between`, `OptimalTax.rate_ordering` |
| pp. 43–44 | A positive tax on borrowing, rebated lump sum, decentralises C | `OptimalTax.optimalTax_eq`, `OptimalTax.optimalTax_pos`, `OptimalTax.tax_decentralises` |
| pp. 44–45 | Home gains, Foreign loses | `OptimalTax.home_gains`, `OptimalTax.foreign_loses` |
| p. 45 | The tax equilibrium is Pareto-inefficient: Foreign could bribe Home | `OptimalTax.exists_pareto_improvement`, `OptimalTax.tax_equilibrium_pareto_inefficient` |
| p. 45 | A small country's optimal tax is zero (exactly, and as a limit as Foreign grows) | `OptimalTax.small_country_zero_tax`, `OptimalTax.Foreign.tendsto_rate_scale`, `OptimalTax.Foreign.tendsto_optimalTax_scale` |
| fn 19, p. 44 | If `r^A < r^{A*}` the optimal policy taxes lending | `OptimalTax.laissezFaire_lends`, `OptimalTax.planner_between_lend`, `OptimalTax.optimalTax_neg` |

## §1.5 International labour movements (pp. 45–51)

| Book | Claim | Lean |
| --- | --- | --- |
| (1.33), p. 46 | Constant returns for `F(K, L) = L f(K/L)` | `LabourMobility.prod_homogeneous` |
| (1.34), p. 47; fn 21 | Euler's theorem from degree-one homogeneity | `LabourMobility.euler_of_homogeneous`, `LabourMobility.prod_eq_euler` |
| (1.35)–(1.36), p. 47 | `F_K = f'(k)`, `F_L = f(k) − f'(k)k` | `LabourMobility.hasDerivAt_prod_capital`, `LabourMobility.hasDerivAt_prod_labour` |
| (1.37)–(1.38), p. 48 | First-order conditions | `LabourMobility.euler_equation`, `LabourMobility.wage_eq_marginal_product` |
| p. 48 | Factor-price frontier: `k'(w) = −1/(kf''(k)) > 0`, `r'(w) = −1/k < 0` | `LabourMobility.Technology.hasDerivAt_wage`, `wage_strictMonoOn`, `kOf_wage`, `wage_kOf`, `hasDerivAt_kOf`, `kOf_slope_pos`, `hasDerivAt_rOf`, `rOf_strictAntiOn` |
| pp. 49–50 | `F(K, L) ≤ r(w)K + wL`, equality iff `K = k(w)L` | `LabourMobility.Technology.profit_nonpos`, `profit_eq_zero_iff`, `prod_le_factor_payments`, `prod_lt_factor_payments` |
| pp. 49–50 | GNP line weakly above the PPF, touching only at B (gains from labour trade) | `LabourMobility.Technology.ppf_le_gnpLine`, `ppf_eq_gnpLine_iff`, `ppf_tangent_at_B`, `consumption2_le_gnp` |
| p. 50 | GDP line; GDP > GNP above B | `LabourMobility.Technology.gdpLine_eq`, `gdpLine_sub_gnpLine`, `gnpLine_lt_gdpLine_iff` |
| p. 50 | `w^A > w` ⇒ labour imports; `w^A < w` ⇒ exports | `LabourMobility.Technology.labour_imports_of_autarkyWage_gt`, `labour_exports_of_autarkyWage_lt` |
| p. 50 | More labour lowers `w^A`; more saving raises it | `LabourMobility.Technology.autarkyWage_anti_labour`, `netLabourExports_lt_of_labour_lt`, `autarkyWage_lt_of_saving_lt`, `autarkyWage_lt_of_more_saving` |

## Appendix 1A Stability and the Marshall–Lerner condition (pp. 53–54)

| Book | Claim | Lean |
| --- | --- | --- |
| (1.39)–(1.40), pp. 53–54 | Walras stability in terms of imports | `Stability.worldExcessSaving_eq`, `Stability.hasDerivAt_netImports` |
| (1.41), p. 54 | Marshall–Lerner: stable iff `ζ + ζ* > 1` | `Stability.zeta`, `Stability.zetaStar`, `Stability.marshall_lerner`, `Stability.stable_iff_marshall_lerner` |
| p. 53 | Zero-current-account equilibria are stable | `Stability.dC1_neg_of_zero_ca`, `Stability.stable_of_saving_increasing` |

## Exercises (pp. 54–58)

| Book | Claim | Lean |
| --- | --- | --- |
| Ex 1(a) | Euler condition for general `U(C₁, C₂)` | `Consumer.euler_general` |
| Ex 1(b) | Envelope: `dU/dr = U₂(Y₁ − C₁)` | `Consumer.envelope_general` |
| Ex 1(d) | A rate change is equivalent to a wealth change `r̂(Y₁ − C₁)` | `Consumer.welfare_equivalent_wealth` |
| Ex 2(a) | Log demands | `Isoelastic.log_euler_budget_iff`, `Isoelastic.consC2_log_share`, `WorldEquilibrium.logC1` |
| Ex 2(b) | Log saving function | `WorldEquilibrium.log_saving` |
| Ex 2(c) | Closed-form world rate | `WorldEquilibrium.log_equilibrium_iff`, `WorldEquilibrium.logGrossRate` |
| Ex 2(d) | The world rate lies between the autarky rates (mediant) | `WorldEquilibrium.mediant_between`, `WorldEquilibrium.log_rate_between` |
| Ex 2(e) | Trade pattern | `WorldEquilibrium.trade_pattern` (general utility) |
| Ex 2(f) | `dU₁/dr = β(r − r^A)/[(1 + r)((1 + r) + β(1 + r^A))]` | `WorldEquilibrium.logWelfare`, `WorldEquilibrium.hasDerivAt_logWelfare` |
| Ex 3 | `K₂ = (αA₂/r)^{1/(1−α)}`; closed-form `C₁` | `Isoelastic.ex3_capital_iff`, `Isoelastic.ex3_consumption` |
| Ex 4 | `σ → 0` limits and derivative | `Isoelastic.ex4_growth_tendsto_one`, `ex4_consC1_tendsto`, `ex4_flat`, `ex4_hasDerivAt`, `ex4d_euler_iff`, `ex4d_ratio_tendsto` |
| Ex 5 | Comparative statics of the world rate (log utility) | `WorldEquilibrium.logGrossRate_anti_Y1`, `logGrossRate_mono_Y2`, `logGrossRate_anti_Y1s`, `logGrossRate_mono_Y2s`, `logGrossRate_comm` |
| Ex 7 | CARA utility | `Isoelastic.ex7_euler_iff`, `Isoelastic.caraC1`, `ex7_euler_budget_iff`, `ex7_hasDerivAt`, `ex7_eis`, `ex7_hasDerivAt_eis` |
| Ex 8(a) | Optimal ad valorem tax `τ = 1/(ζ* − 1)` | `OptimalTax.elasticity_sub_one`, `OptimalTax.ex8_optimal_tax` |
| Ex 8(b) | `ζ* > 1` at the optimum (under an added hypothesis, see corrections) | `OptimalTax.ex8_elasticity_gt_one`, `OptimalTax.ex8_elasticity_gt_one_of_supply` |
