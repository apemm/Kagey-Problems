# W-S4 progress log (coin-turning note, namespace `Kagey131.PaperD.S4`)

Files are in `kagey-problems/problem131/lean/PaperD/S4/` and the sub-root is
`kagey-problems/problem131/lean/PaperD/S4.lean`. Checked from `~/lean-work/w-s4` with
`lake env lean "$L/PaperD/S4/<File>.lean"`; `Note`, `Numbers`, `Expansion200`, `Crossing200`, `Feller` and the sub-root were
also compiled with `lake env lean -R "$L" -o .lake/build/lib/lean/PaperD/S4/<File>.olean ...` so
that the later files import the earlier ones. Axioms (checked with `#print axioms` over every
theorem of the five files): `propext`, `Classical.choice`, `Quot.sound` only (one helper uses
`propext` alone). No `sorry`, `admit`, `native_decide`, `axiom` or `opaque`. The two integer
checks of `Crossing200` use `decide +kernel`.

| Target | Status | File | Theorems | Deviation |
|---|---|---|---|---|
| S4-1 | done | Note.lean | see the table below | indexing by `N` steps (Lean's `t = N - 1`); states `1..d` are `Fin d` with state `1` as `0`; `N = 2h` is a hypothesis `N = 2 * h` instead of `Even N` |
| S4-2 | done | Note.lean | rem_aging_d_paths, rem_aging_d_expected_moves, rem_aging_d_expected_moves_isBigO (and rem_aging_d_two_states, rem_aging_d_two_states_chain, rem_aging_d_moves_indep, rem_aging_d_crp) | the `O(1)` is an explicit uniform bound |
| S4-3 | done | Numbers.lean | fig_corner_half (exact `703/73`), fig_center_half, fig_corner_two, fig_center_two, panel_a_flat, panel_a_ends, panel_a_center | roundings shown by brackets: `9.55 <= 9.63 < 9.65`, `0.425 <= 0.4303 < 0.435`, `0.0345 <= 0.0347 < 0.0355`, `2.05 <= 2.061 < 2.15`; panel (a) is proved from the one-step ratio `Q(m+1)/Q(m)` (`q2_step`), which gives the strict maximum at the ends or at the center, a stronger statement than the center/end ratio |
| S4-4 | done | Expansion200.lean | euler_bounds, expansion_value_200 | `0.8931 <= value <= 0.8933`; `gamma` is bracketed by `harmonic 128 - log 129 < gamma < harmonic 128 - log 128` (value of `harmonic 128` by `norm_num`) |
| S4-5 | done | Crossing200.lean | tableZ_spec, PA_eq, EN_eq, sum_lt_rho, rho_lt_sum, crossing_200_bounds | `0.89245 < c_200 < 0.89255` where `c_200 = FL4.cN 100`; exact integer tables for `c = 17849/20000` and `c = 17851/20000`; the whole file checks in about 20 s |
| S4-6 | done | Feller.lean | fail_prod, block_weight, runProb_closed, sum_ordL, orderingSum, esf_compact, spLaw_eq_esf, crpLaw_eq_esfC, crpLaw_eq_esf, feller_coupling, rem_aging_feller | the two laws are given as definitions (see the notes below): the spacing law by the run probabilities of independent trials, the restaurant law by the forward equation of the table-size chain; both are proved equal to the Ewens formula |

## Statements of the note under their labels (`Note.lean`)

Current numbers 2.1 to 2.7 and A.1 to A.3. "Lean" is the theorem in `Kagey131.PaperD.S4`.

| Label | Number | Lean | Existing theorems used |
|---|---|---|---|
| `prop:aging-urn` | 2.1 | prop_aging_urn_joint, prop_aging_urn_law, prop_aging_urn_ratio, prop_aging_urn_ratio_mono | `FL1.prop_aging_urn`, `urnLaw_eq`, `urn_ratio_formula`, `urn_prob_ratio_strictMonoOn`, `urn_prob_ratio_eq_one_iff` |
| `rem:aging-feller` | 2.2 | rem_aging_feller (= feller_coupling), in Feller.lean | `rpoch` and `rpoch_add` of `FL1_Urn` only |
| `prop:aging-two` | 2.3 | prop_aging_two_a_joint, prop_aging_two_a, prop_aging_two_b, prop_aging_two_ends | `FL1.prop_aging_two_a_of_thm`, `prop_aging_two_b_of_thm`, `plusBin_one`, `plus_top_strict_max`, `plus_top_strict_min` |
| `thm:aging-d` | 2.4 | thm_aging_d_a, thm_aging_d_a_uniform, thm_aging_d_b, thm_aging_d_corner | `FL1.thm_aging_d_a`, `thm_aging_d_b`, `corner_strict_max`, `corner_strict_min`, `mem_ageBins`, `card_ageBins` |
| `rem:aging-d` | 2.5 | rem_aging_d_two_states, rem_aging_d_two_states_chain, rem_aging_d_paths, rem_aging_d_moves_indep, rem_aging_d_crp, rem_aging_d_expected_moves, rem_aging_d_expected_moves_isBigO | `FL1.thm_aging_two_state`, `plusBin_eq_ageBin`, `chain_path_1122`, `urn_draws_122`, `movePat_law_one`, `crp_new_table`, `expected_moves_one`, `expected_moves_one_isBigO`; the coupling with the chain of Dietz and Sethuraman and the limits are not formalized |
| `prop:aging-fair` | 2.6 | prop_aging_fair_a, prop_aging_fair_b_ratio, prop_aging_fair_b, prop_aging_fair_sides | `agBin_one_interior`, `agBin_one_top`, `agBin_ratio_strictMonoOn`, `aging_crossing_exists_unique`, `aging_crossing_sides`, `continuous_agBin`, `agBin_zero_c` |
| `prop:aging-expansion` | 2.7 | prop_aging_expansion; the value at `N = 200`: expansion_value_200; the computed crossing: crossing_200_bounds | `FL4.aging_expansion` |
| `lem:D-average` | A.1 | lem_D_average (with `lam`, `hitT`, `rhoAB`, `qStay_eq_lam`) | `agBin_center_averaging`, `agBin_ge`, `agBin_le` |
| `prop:D-bracket` | A.2 | prop_D_bracket_mono, prop_D_bracket_expansion, prop_D_bracket_crossing, prop_D_bracket, prop_D_bracket_limit, prop_D_bracket_ge | `FL4.cM_strictMono`, `cM_expansion`, `cN_spec`, `bracket`, `crossing_log_limit`, `cN_ge_cM_three` |
| `prop:D-llt` | A.3 | prop_D_llt | `FL4.llt_rate` |

Notes on the statements.

* `PA c N s = agBin (agingP c) (N-1) s` is `P(A_N = s)` for the fair start, `EN` is `E_N`, and `PAp`,
  `PApEnd` are the fixed-start laws. They are definitions in `Note.lean`.
* `prop:D-bracket` and `prop:D-llt` are stated for `N = 2h`. The crossing `c_N` is `FL4.cN h`,
  and `prop_D_bracket_crossing` shows it is the only solution in `(0, 2)` of `C_N = E_N` and
  lies in `(0, 1)`. `c^{(M)}` is `FL4.cM M`.
* `prop:aging-expansion` and `prop:D-bracket` carry the `O(...)` as an explicit uniform constant
  `C`, which is the same statement for `N >= 4` where `log N > 0`.
* `lem:D-average` gives `P(T = r) = agEnd (agingP c) (r-1) h true`, the joint law
  `P(S_r = h, X_r = +1)`, and `lambda_{t,N} = (c/t) rho(t, N)` as `lam` with
  `rho(a, b) = prod_{k=a+1}^b (1 - c/k)` as `rhoAB`.
* Where an existing theorem is stronger than the note's statement (the strict maxima in
  `prop:aging-two`, the explicit constants), the note's form is proved and the stronger form is
  kept next to it.

## The Feller coupling (`Feller.lean`)

`rem:aging-feller` is stated for a fixed number `T` of trials or customers and `α = dθ`.

* Spacing side. `fT α t = α/(α+t-1)` is the success probability of trial `t` (`fT α 1 = 1`). The
  runs of the trials are a list `l` of positive lengths with sum `T`, and `runProb α s l` is the
  probability that independent trials `s, s+1, …` split into these runs: a success at the first
  trial of each run and failures at the others. `spLaw α m` sums `runProb α 1 l` over the
  distinct orderings `l` of the multiset `m` (`ordL m`). So the sum runs over the lists of run
  lengths, as the plan suggested, and the indicator vector of the trials is not used.
* Restaurant side. `crpLaw α T m` is the law of the multiset of table sizes after `T`
  customers, written as a forward equation over the predecessors of `m`: a new table with
  probability `α/(α+T)` from `m.erase 1`, and for each size `x ≥ 2` present in `m`, one of the
  `(m.erase x).count (x-1) + 1` tables of size `x - 1` in `(x-1) ::ₘ m.erase x` grows with
  probability `(x-1)/(α+T)` each. This is the standard seating rule seen through the sizes only;
  the seating of individual customers is not formalized.
* Proof. `runProb_closed` gives `runProb α s l · (α+s-1)^{(S)} · Dp s l · (s-1)! = α^k (s+S-1)!`
  with `Dp` the product of the partial sums, by induction on `l` (`block_weight`, `fail_prod`).
  `orderingSum` shows `∑ over orderings of 1/(product of partial sums) = 1/(∏ m · ∏ c_j!)` by
  removing the last element (`sum_ordL`). `spLaw_eq_esf` combines them. `crp_term` and
  `crpLaw_eq_esfC` prove the Ewens formula for the restaurant by induction on `T`: each
  predecessor contributes `ESF(m) · x c_x/(T+1)`, and `∑ x c_x = T + 1`.
* Both laws are stated for multisets of positive integers with sum `T` and `α > 0`
  (`feller_coupling`, `rem_aging_feller`). The Ewens formula `esf` is
  `T!/α^{(T)} ∏_{j=1}^T (α/j)^{c_j}/c_j!`, as in the note's argument for the coupling; its compact
  form is `esf_compact`.

## Files and commands

All under `kagey-problems/problem131/lean/PaperD/`, checked from `~/lean-work/w-s4`:
`S4/Note.lean`, `S4/Numbers.lean`, `S4/Expansion200.lean`, `S4/Crossing200.lean`,
`S4/Feller.lean`, and the sub-root `S4.lean` (imports the five). Command for each:
`lake env lean "$L/PaperD/S4/<File>.lean"` with
`L="C:/Users/arjun/OneDrive/Documents/GitHub/Kagey-Problems/kagey-problems/problem131/lean"`.
Imports: `Note` uses `PaperD.FL1_Bridge` and `PaperD.FL4_All`; `Numbers` and `Crossing200` use
`PaperD.S4.Note`; `Expansion200` uses Mathlib only; `Feller` uses `PaperD.FL1_Urn`. The module
list for `lean/PaperD/MAP.md` and `lean/README.md` is the five modules above (about 100
declarations, none with `sorry`).
