# Paper D, Theorem 2.6 and Appendix A: map to the `T4_*` Lean modules

Supplement to `PaperD/MAP.md` (left unchanged, as are `PaperD.lean` and all other existing files).
Ten `T4_*` modules, plus `T4_All.lean`, which imports the root `PaperD` and all of them, so that
`lake build PaperD.T4_All` checks them against the whole library. All are in namespace
`Kagey131.PaperD`. There is no `sorry`, `admit`, new axiom or `native_decide`.
`#print axioms` (`axioms-t4.lean`, `axioms-t4.log`) gives `[propext, Classical.choice, Quot.sound]`
for 56 declarations and `[propext]` for `logTab_spec` and `logTab_least`.

| Paper statement | Lean | File | Status |
|---|---|---|---|
| Theorem 2.6(a), `C_N ≥ 4ε/(N+2)·(1-2ε)` | `thm_erw_bounds_a` (`center_lower` for `N = 2h`) | `T4_Bounds`, `T4_Lower` | faithful |
| Theorem 2.6(b), `C_N ≤ 4ε/(N+2)·N^{2ε}e^{5200ε}` | `thm_erw_bounds_b`; `center_upper_all` (every even `N ≥ 2`) | `T4_Main` | faithful; stronger |
| Theorem 2.6, "in particular" | `thm_erw_bounds_in_particular`; `log_center_lower`, `log_center_upper` | `T4_Bounds`, `T4_Main` | faithful (lower half stronger: every even `N ≥ 2`, `ε < 1/2`) |
| Proposition 2.5(a) | `center_first_flip` (fixed-start form `law_first_flip`) | `T4_Hitting` | faithful |
| Proposition 2.5(b) | `hitV_zero_eq_pi`, `sum_pi`, `center_deriv_eq_sum_hit` (with `center_hasDerivAt`) | `T4_Lower`, `T4_Polya` | faithful |
| Proposition 2.5(c) | `sum_w_mul` (`∑ w_t t = 3 - 6/(h+2)`), `sum_pi_moment`, `w_le`, `pi_le` | `T4_Lower`, `T4_Polya` | faithful |
| Lemma A.1(a) | `phiU_up` + `phiU_stay` (recursion); `hitV_zero_eq_phiU` (hitting probability, `c = 0` only) | `T4_Polya`, `T4_Lower` | recursion faithful; probabilistic reading only for `c = 0` |
| Lemma A.1(b) | `phiU_up` | `T4_Polya` | faithful |
| Lemma A.1(c) | `upProb_pseudocount` (existing) | `ElephantAlgebra` | faithful |
| Lemma A.1(d) | `hitV_ge_phiU`, `hitV_ge_pi`; sign step `phiU_sub_step`, `phiU_step_eq` | `T4_Lower` | faithful (`0 ≤ ε` allowed) |
| Lemma A.3(a) | `hitV_le_of_super` | `T4_Hitting` | faithful |
| Lemma A.3(b) | `hitV_ge_of_sub` | `T4_Lower` | faithful |
| Lemma A.5 | `logPhi_deriv_lt` (DLMF 5.9.15 proved: `binetDigammaBounds_holds`) | `T4_Digamma`, `T4_Binet` | faithful |
| Proposition A.4(a) | `prop_A4a`, `J_eq`, `step_eq_J` | `T4_Super` | faithful |
| Proposition A.4(b) | `super_step_Sg`, `delta_le`, `log_delta_le` (Steps 3-4: `exponent_le_Sg`; Step 1: `J_le`, `rho_sub_one`) | `T4_Super` | faithful |
| Proposition A.4(b), weakened to `s` | `super_step`, `exponent_le` | `T4_Super` | weaker (what A.4(c) uses) |
| Proposition A.4(c) | `prop_A4_c` (`π_t` as `piPaper`) | `A4_Full` | faithful (`0 < ε < 1/4`, every even `N ≥ 2`) |
| Proposition A.4(c), relaxed | `hitV_le_pi` | `T4_Upper` | weaker (exponent already relaxed as in Step 1 of 2.6(b)) |
| Proposition A.4(d) | `prop_A4_d`, `prop_A4_d'` (`U_N` as `UN`, with `cOne`, `wPaper`, `GA4`) | `A4_Full` | faithful (`0 < ε < 1/4`, every even `N ≥ 2`) |
| Proof of 2.6(b) | `center_upper` (premises `BinetDigammaBounds`, `SeriesBound`, both proved) | `T4_Upper` | faithful |
| Series bound `S < 102.59` | `seriesBound_holds` (partial sums `≤ 102.635`) | `T4_Series` | weaker, sufficient (`< 103.1`) |

Not formalized: the probabilistic reading of Lemma A.1(a) for `c > 0` (not needed) and the
duplication-formula route of Lemma A.5 (replaced by the Binet bounds). The sharper exponent of
A.4(c) is now proved in `A4_Full` (`prop_A4_c`).

## Proposed edits to existing files (not applied)

`PaperD.lean`: add `import PaperD.T4_Bounds` (it pulls in the other nine `T4_*` modules;
`T4_All` shows that this causes no name clash).

`PaperD/MAP.md`, coverage paragraph: replace "These are the bounds on the center (Theorem 2.6),
the crossing asymptotics, ..." by "These are the crossing asymptotics, ...", and add: "Theorem 2.6
(both parts and the logarithmic display) is formalized end to end in the `T4_*` modules:
`thm_erw_bounds_a`, `thm_erw_bounds_b`, `thm_erw_bounds_in_particular`; also Proposition 2.5(a)-(c)
(`center_first_flip`, `hitV_zero_eq_pi`, `center_deriv_eq_sum_hit`, `sum_w_mul`, `w_le`), Lemmas
A.1(b),(d), A.3(a),(b), A.5 and Proposition A.4(a)-(d); see `PaperD/T4_MAP.md`." Update the module
count accordingly (the root now imports 22 modules; with the 10 `T4_*` modules, 33 in all).
