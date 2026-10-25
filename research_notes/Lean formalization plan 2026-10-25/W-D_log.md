# W-D progress log (Paper D)

Workspace `~/lean-work/w-d`, modules in `lean/PaperD/Modes/` (namespace `Kagey131.PaperD.Modes`),
sub-root `lean/PaperD/Modes.lean`. Each file is checked with
`lake env lean "$L/PaperD/Modes/<File>.lean"` from `~/lean-work/w-d`; the dependencies were
compiled in dependency order with `lake env lean -R "$L" -o .lake/build/lib/lean/PaperD/Modes/<File>.olean ...`.
All 22 modules and the sub-root compile with no error and no `sorry`; `#print axioms` for each
main theorem (scratch file `~/lean-work/w-d/scratch_axioms.lean`, not in the repository) gives
only `propext`, `Classical.choice`, `Quot.sound`.

Section 4 of the paper was being edited; the labels used here are `thm:two-modes`,
`thm:two-modes-near-one`, `lem:descartes`, `lem:sp-limit`, `lem:sp-derivative`, `cor:height-window`,
`thm:threshold`. `thm:threshold` (computer-assisted) is not formalized.

## Status by target

| Target | Status | File(s) | Main declarations | Deviation from the paper |
|---|---|---|---|---|
| D-1 | done | NearOneNumeric | `near_one_numeric` | uses gamma > 1/2 only (M < 80/79, V < 59/741 instead of 1.0107 and 0.0752); hypothesis `1 <= M` is not needed (named `_hM1`) |
| D-2 | done | SignTools | `signPattern_sublist_of_sublist`, `signPattern_mul_pos`, `signPattern_neg`, `signPattern_reverse`; defs `ValuesAtMost`, `IncrementsAtMost`, `piFour` | none |
| D-3 | done | SpLimit | `valuesAtMost_of_tendsto`, `incrementsAtMost_of_tendsto` (finite core `signPattern_le_of_tendsto`) | stated for an arbitrary sign list `P` (paper: alternating list) |
| D-4 | done | HeightWindow | `height_window`, `height_window_generic`, helpers `concave_chord`, `sum_ewBin`, `ewBin_pos` | none; hypotheses are the conclusion of `modal_intervals_at_crossing_all_even` |
| D-5 | done | NearOneProb | `cantelli`, `cdf_not_concave`, `not_concave_of_ratio`, `concave_cdf_of_antitone` | concavity step proved for `g` continuous and antitone on `[0,inf)` |
| D-6 | done | GammaMoments, NearOne | `gamma_mean_bounds`, `gamma_second_moment_bound`; `near_one_incompatible`, `near_one_not_concave` | the moment formulas are the named hypothesis `GLRMomentsHyp` (Guerin, Laulin, Raschel, Thm 1.4) |
| D-7 | done | SpDerivative | `sp_derivative` (via `incrementsAtMost_of_deriv`, `valuesAtMost_piFour_of_incr`) | none |
| D-8 | done | PolySigns, PolySigns2, PolyValues | `poly_values_pattern`, `expsum_valuesAtMost` | through Mathlib's rule of signs as planned |
| D-9 | done | Smoothing | `smoothedD_valuesAtMost`, defs `gaussKer`, `zPt`, `smoothedD` | none |
| D-10 | done | Dichotomy | `two_mode_dichotomy`, `two_mode_exclusive`, `two_mode_not_unimodal` (core `no_valley`) | none |
| D-11 | done | ExpSignsA, ExpDescartes, ExpValues | `descartes_values`, `zero_count`, `expSum_zeros_finite`, `expSum_sign_atBot` | exponent sums as lists of pairs `(lambda_k, b_k)`, `lambda` strictly increasing, some `b_k != 0` |
| D-12 | done modulo hypotheses | GaussDeriv, EdgeBounds, StepTwoA, StepTwoB, Mollify, TwoModes | `smoothedD_close`, `smoothedD_tendsto`, `mol_deriv`, `mol1_tendsto`, `mol0_tendsto_density`, `increments_density`, `two_modes`, `main_limit_near_one` | see below |

## D-12 hypotheses and what is not proved

* `DensityHyp g`: `g` continuous, even, nonnegative, integrable, bounded (Guerin, Laulin, Raschel,
  Theorem 1.3).
* `LawConvHyp eps a g`: for bounded continuous `f`, `sum_k P_N(k) f(z_k) -> int f g` with
  `z_k = (2k-N) N^(-a)`, i.e. convergence in law of `S_N/N^a` to the law with density `g`.
* `GLRMomentsHyp` and the identification `P(|X| <= t) = 2 int_0^t g` (the law of `|L_a|` is that of
  `|L°_a|`) for `main_limit_near_one`.
* Taylor estimate with constant `2 M4 eta^4` instead of the paper's `M4 eta^4/12` (only the order is used).
* Not formalized: `thm:threshold` (computer-assisted), the almost sure convergence and the density
  (cited from the literature), `cor:fixed-memory-bridge`.

## Rows for MAP.md (Paper D by statement label)

| Label | Lean | File |
|---|---|---|
| `cor:height-window` | `height_window` | `PaperD/Modes/HeightWindow.lean` |
| `lem:descartes` | `descartes_values`, `zero_count`, `expSum_zeros_finite` (arbitrary exponents); `poly_values_pattern`, `expsum_valuesAtMost` (equally spaced) | `ExpValues`, `ExpDescartes`, `PolyValues` |
| `lem:sp-limit` | `valuesAtMost_of_tendsto`, `incrementsAtMost_of_tendsto` | `SpLimit.lean` |
| `lem:sp-derivative` | `sp_derivative` | `SpDerivative.lean` |
| `thm:two-modes` | `two_modes` (hypotheses `DensityHyp`, `LawConvHyp`); steps: `smoothedD_valuesAtMost`, `smoothedD_tendsto`, `mol_deriv`, `mol1_tendsto`, `mol0_tendsto_density`, `two_mode_dichotomy`, `two_mode_exclusive`, `two_mode_not_unimodal` | `TwoModes`, `Smoothing`, `StepTwoB`, `Mollify`, `Dichotomy` |
| `thm:two-modes-near-one` | `near_one_numeric`, `cantelli`, `cdf_not_concave`, `not_concave_of_ratio`, `gamma_mean_bounds`, `gamma_second_moment_bound`, `near_one_incompatible`, `near_one_not_concave`, `main_limit_near_one` | `NearOneNumeric`, `NearOneProb`, `GammaMoments`, `NearOne`, `TwoModes` |
| `thm:main-limit` | `main_limit_near_one` (modulo hypotheses above) | `TwoModes.lean` |
