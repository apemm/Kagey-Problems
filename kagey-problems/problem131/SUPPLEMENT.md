# Verification supplement for the 4 papers on Problem 131

This supplement serves the papers on Kagey's Problem 131 by A. Pemmasani: Papers A and B (preprint, 2026) and the drafts of Papers C and D.

| Paper | Title | Source |
| --- | --- | --- |
| A | Uniform Bessel bounds for endpoint crossings in the persistent random walk | `paperA/problem131.tex` |
| B | Vertex crossings in a symmetric Markov multinomial model | `paperB/problem131_multistate.tex` |
| C | Face selection for slowly switching Markov chains and the planar persistent walk | `paperC/problem131_switching.tex` |
| D | Endpoint crossings for random walks with memory | `paperD/problem131_memory.tex` |

The proofs are in the papers. The scripts check the finite statements exactly and the asymptotic
ones numerically, and where possible each number is computed in 2 independent ways. For each paper
we first list the results whose proofs rest on a computation, with the script that checks them and
the 2 methods, and then say what each script checks.

Run `python -B verify_all.py --paper a` in this folder, or use `b`, `c`, `d` or `all`. Add `--full`
for the long runs and `--dry-run` to print the commands without running them. For each paper the
runner calls the paper's own runner, `paperA/verify_all.py` to `paperD/verify_all.py`, with
`--quick`, or with `--full`, and it skips a paper whose folder is missing. The scripts for Papers A
and B use only the standard library of Python 3. Those for Papers C and D need numpy, scipy and
mpmath, and Paper C also needs sympy. Before most computations we wrote a prediction and a
condition that would refute it in a ledger, and we recorded the outcome below it. `ledger.md`
indexes the ledgers of all 4 papers.

## Paper A: the two-state walk

`python -B verify_all.py --paper a` runs `paperA/verify_all.py`, which takes about 2 minutes. The
scripts below are in `paperA/`. Add `--full` to include `verify_every_n.py` and
`verify_every_n_sign.py` (about 21 minutes more), which run before `verify_every_n_guards.py`.

| Result that rests on computation | Script | The 2 methods |
| --- | --- | --- |
| The crossing at every N (theorem), for 2 <= N <= 174 | `verify_every_n.py`, rechecked by `verify_every_n_guards.py` | The certificate integers come from the run-count sum and from the recursion with integer weights. zeta_N comes from a Decimal Newton iteration and from a float Lambert W iteration. The Lean kernel also checks these certificates (`lean/PaperA/EveryN.lean`). |
| The crossing equation (proposition), for N <= 174 | the same 2 scripts | The same certificates. The guards also get the sign of R_N from the certificate integers for N <= 1000 and check z_2 = 2/3 < log 2. |
| Part (d) of the corollary on the crossing at every N | `verify_every_n_guards.py` | One evaluation with a proved bracket. f(zeta_2774) - 1 = 2.1e-4 and f(zeta_2773) - 1 < 0 in 60-digit decimal arithmetic, with zeta_N known to within 10^-45. The function increases in zeta, so the signs hold on the whole bracket. |
| The remark on the sign of z_N - zeta_N (computer-assisted throughout) | `verify_every_n.py` and `verify_every_n_sign.py` | Up to N = 1000 the certificate integers, and for 1001 <= N <= 2773 exact integers S_N(v) < 1 at a rational v just above zeta_N/(N - zeta_N). The run-count sum and the recursion agree at N = 401, 1000, 1008, 2000 and 2773, and 2 float methods agree up to N = 3000. |

The integer tests are exact, and every comparison with zeta_N is made in 60-digit decimal
arithmetic with zeta_N bracketed to within 10^-45. The margins are above 0.03 for the crossing and
the crossing equation. For the sign remark the smallest distance from zeta_N to a certified interval
is 1.66e-5 (at N = 218), and for 1001 <= N <= 2773 the test point exceeds zeta_N/(N - zeta_N) by at
least 1.2e-11. Every other high-precision check is not interval arithmetic, so it supports the
proofs but does not replace them.

| Script | What it checks |
| --- | --- |
| `verify.py` | Run-count probabilities against a dynamic program and against word enumeration, normalization, generating functions, the 2 lattice-path bijections, variance and normal approximation, and the table of central crossings by exact rational signs at the neighboring decimals. |
| `check_bessel.py` | The central Bessel bound at 1,400 points, and crossing comparisons at high precision up to N = 10^8. |
| `verify_adjacent.py` | Adjacent-bin ratio and global extrema in 474 exact distributions up to N = 80, exact adjacent thresholds, and the cubic gap between the central and adjacent polynomials by word enumeration up to N = 12. |
| `verify_allbin.py` | 5,476 exact coefficient comparisons, 264 all-bin Bessel inequalities, 28 Laguerre-Bessel inequalities, and the crossing and edge expansions at 80 digits. |
| `verify_periodic_window.py` | 66 cyclic run polynomials against enumeration, 120 relative-error inequalities, and root and critical-window samples up to N = 10^12. |
| `verify_every_n.py` | The crossing at every N (about 8 minutes, only with `--full`). The bounds on I_0 + I_1 at 2,000 points, with the Bessel values by power series and by quadrature, the certificates for 2 <= N <= 174 and as a cross-check up to N = 1000, the margins of the analytic proof, and a table of z_N by 2 bisections. Writes `paperA/data/every_n_certificates.csv` and `paperA/data/every_n_output.txt`. |
| `verify_every_n_sign.py` | The sign of z_N - zeta_N for 1001 <= N <= 2773 (about 13 minutes, only with `--full`). |
| `verify_every_n_guards.py` | The rounding guards of the 2 scripts above, the signs of z_N - zeta_N and of R_N for N <= 1000, and the checks at N = 2773 and 2774 (about 25 seconds). |
| `verify_uniform_llt.py` | The uniform local law in 3 runs. With no argument, the exact identity for P_N(k) in 3,900 cases and the errors of the tilted Bessel form over all bins. With `--run2`, the lemmas and the error bound at 217 sampled points. With `--run3`, the central crossing from the tilted form against p_N. |
| `verify_uniform_llt_cor5.py` | Where the proved central bound of the local law stops being vacuous (the smallest even N is 1454, found 2 ways), and the closed form for bins 1 and N - 1 in 390 exact cases (about 30 seconds). |

`verify.py` checks the exact law against enumeration for N <= 16 at 20 rational values of p. The
polynomials have degree less than N, so for those N this proves the polynomial identities. The last
4 scripts in the table report their checks in their output rather than through the exit code, so
the output has to be read. It is also saved in `paperA/data/`. The predictions are in `ledger.md`,
`paperA/data/ledger_every_n.md` and `paperA/data/ledger_llt.md`.

## Paper B: the complete graph

`python -B verify_all.py --paper b` runs `paperB/verify_all.py`, which takes about 2 minutes. The
scripts below are in `paperB/`. Add `--full` to include `verify_B_tie_repair.py` (about 3 minutes
more).

No proof in Paper B rests on computation. The statements that the paper marks as numerically
verified are checked as follows.

| Statement | Script | The 2 methods |
| --- | --- | --- |
| Proposition 4.3 (where a conditioned path starts) is proved. Its numerical check is the error -0.0020 quoted after it, for d = 2, alpha_1 = 0.6, z = L - (1/2) log L and N = 2000 | `verify_general_start.py` | The start weights from the run formula and from the refresh formula in double precision, against the limit sqrt(alpha_a)/A. |
| The three phases after Example 4.9 (the K_3 example with the start (1/2, 1/2, 0)) at N = 90, 300 and 1002 | `verify_general_start.py` (N = 90) and `verify_B_tie_repair.py` (N = 300 and 1002, with `--full`) | A dynamic program over all bins, against the lines of the example. |
| The widths of the K_3 window at finite N (Remark 4.10) | `verify_general_start.py` (N = 3000 to 300000) and `verify_B_tie_repair.py` (N = 300, with `--full`) | The lower end from the run formula and from Paper A's S_N = 1. The upper end from the run formula, with its sign change confirmed by a second method. |
| The numbers in Remark C.2 (the factor e^E of the crossover theorem) | `verify_crossover_factor.py` | S_(n,a) by the run formula, by a quadrature of the integral form (21) in double precision and by the positive sum (3) at 60 digits for N <= 2 * 10^6, and by the last two for larger N. They agree to about 10^-14 in log S. |

| Script | What it checks |
| --- | --- |
| `verify_geometry.py` | 6,733 exact bin probabilities in 237 distributions against a dynamic program, 158 of the distributions also by word enumeration, and normalization, moments and the values at p = 0, 1. |
| `verify_simplex_threshold.py` | The positive refresh formula, balancing transfers, the edge-mode example at N = 4, and the balanced-face crossings at high precision. |
| `verify_frontier_boundary.py` | The majorant for all count vectors, the mixed-face crossover, and the fixed rare-count formulas and crossings. |
| `verify_frontier_modes.py` | Spatial profiles, lattice-volume limits, exact finite-N mode comparisons, and the weak-field support hierarchy. |
| `verify_vertex_completion.py` | 462 exact identities for the near-vertex representation, 200 rational concavity checks, 16 uniform root brackets, and 4 examples with growing rare counts where the probabilities are not approximated although the roots are, each at 2 series cutoffs. |
| `verify_general_start.py` | The tie, the law with a start and the tree form of the constants (about 20 seconds). The weighted Cayley formula by the matrix-tree theorem and by listing all trees for k <= 7, the law with a start against word enumeration for 357 bins, the crossings with a start by 3 methods, and the K_3 window at finite N. Writes `paperB/data/general_start_output.txt`. |
| `verify_B_tie_repair.py` | The exact identity Hess I times Sigma_alpha = identity at rational points for k = 2 to 6, and dynamic programs over all bins at N = 300 and N = 1002 (about 3 minutes, only with `--full`). Writes `paperB/data/B_tie_repair_output.txt`. |
| `verify_crossover_factor.py` | The factor e^E of the crossover theorem (about 50 seconds). Exact S_n by the proper-run formula, a quadrature of the refresh integral and the positive refresh sum at 60 digits, checked against word enumeration for small N. With the argument `repair` (under 1 second) it computes psi by a series and by a continued fraction and checks 3 further examples. |

`verify_general_start.py` and `verify_B_tie_repair.py` report their checks in their output rather
than through the exit code. Some of their lines show failures on purpose, since they belong to the 2
registered predictions that failed (T1(e) and T4), so the output cannot be judged by searching for
"False". The predictions are in `paperB/data/ledger_B_tie.md` and
`paperB/data/ledger_B_crossover.md`.
`predict_general_start.py` and `verify_crossover_factor.py predict` only evaluate formulas for those
registrations and check nothing, so `paperB/verify_all.py` does not run them. The dated logs in
`early_runs/` are from earlier versions of the manuscripts, before they were split.

## Paper C: slowly switching Markov chains

`python -B verify_all.py --paper c` runs `paperC/verify_all.py`, which takes a few minutes, or up to
about half an hour with `--full`. Its output is in `paperC/data/verify_output.txt`, and the ledgers
are `paperC/data/ledger_C1.md` to `ledger_C5.md`. A script that finds a failed check lists it and
exits with an error.

| Result that rests on computation | Script | The 2 methods |
| --- | --- | --- |
| The moment lemma behind the Fisher theorem | `verify_sticky_fisher.py` | The 3 moments from the exact law with q as a symbol for N <= 12 against the closed forms, and exact rationals at N = 13, 15 and 17 for 3 values of q. The identity for Var X^2 is checked in sympy. |
| The row Theta_eps of the table of examples (2 triangles joined by a weak link) | `verify_examples.py` | 3 exact resultants in sympy, from characteristic polynomials recomputed from the matrices. The thresholds from their closed forms and from numerical roots, and the certificate at eps_0 in exact rational arithmetic. |
| The values of c_F on the 4-cycle | `verify_second_order.py` | The next Laplace term evaluated exactly in 2 forms, and a continuum check by Richardson extrapolation of the torus integral. |

| Script | What it checks |
| --- | --- |
| `verify_first_order.py` | The exact law and first-order face selection. The run expansion in exact rationals against all words and a dynamic program, the rate on a face by direct maximization and by a Legendre transform of the Perron root, and the winners from the convex hull and from a direct minimization over all faces. |
| `verify_second_order.py` | The local law, the constants K_F, the crossings and the directed 3-cycle. P_N(n) by the run expansion and by a discrete torus integral, and K_F from Perron vectors in double precision and from the Hessian of the Perron root at 30 digits. |
| `verify_examples.py` | The 4-cycle and the table of examples. Exit rates with numpy and with mpmath at 40 digits, the winners by the hull and on a grid, and the modes at finite N by a dynamic program of the whole chain and by the run expansion on each face. |
| `verify_planar.py` | The planar walk. The origin probability by the switch-count formula and by Fourier inversion, and for N <= 10 also by a dynamic program and all 4^N words. Paper A's crossing from the run formula and from the recurrence. |
| `verify_sticky_fisher.py` | Sticky priors and the Fisher information. The law of the counts by a dynamic program and by exact formulas, the direct-jump probability by Monte Carlo and 2 quadratures, and the information of the endpoint by the run formula and by a complex-step derivative of Paper A's recurrence. |

## Paper D: walks with memory

`python -B verify_all.py --paper d` runs `paperD/verify_all.py`, which takes about 5 minutes, or
about 45 minutes with `--full`. Its output is in `paperD/data/verify_output.txt` and
`verify_output_full.txt`, and `paperD/data/ledger.md` indexes the ledgers `ledger_D1.md` to
`ledger_D4.md`. Labels that say "research notes, not printed" check numbers that the paper no longer
prints.

The proofs do not use the computations, except that some constants are values of explicit series
and integrals and that the remark on the bulk uses a computed sign.

| Result that rests on computation | Script | The 2 methods |
| --- | --- | --- |
| The upper bound on C_N in the bounds theorem for the elephant walk (the constant 5200) | `verify_elephant_crossing.py` | The series sum over t of t^2 log(t+1) 2^(-t/2) = 102.59 by mpmath and by a direct sum, so 3 + 50.4 times it is below 5200. |
| The golden-ratio corollary, C(phi) = 0.7761317206 and the factor 1.2884 | `verify_heavy_runs.py` | The general formula for C(alpha) and the closed form at the golden ratio. |
| The remark on the bulk, f_L''(lambda_0) = -0.0789 (computed, not certified) | `verify_elephant_shape.py` | The Landau density by a real integral and by Fourier inversion. |
| The convexity conjecture, checked for 10 <= N <= 600 and N = 1600, 3200, ..., 25600 | `verify_elephant_shape.py` | The law from the minority-count chain and from the law of A_N directly. |
| The ranges after the dip corollary (x_N >= 2(1 - eps_N) for 8 <= N <= 600 and on the grid N = 50 * 2^k <= 51200) | `verify_elephant_shape.py` and `verify_elephant_crossing.py` | The crossing from the minority-count chain and from the full law of A_N. |
| The numbers in the remarks on the refined crossing, on other exponents and on crossover sizes | `verify_elephant_crossing.py` and `verify_heavy_runs.py` | For the elephant walk the 2 methods above. For heavy tails the two-renewal formula and a spectral method, and for small N a first-run recursion and a sum over all run compositions. |
| The aging remark | `verify_aging.py` | A forward recursion, transfer matrices at roots of unity, and the path-weight form in exact rationals. |

`verify_elephant_crossing.py` checks the crossing of the elephant walk, `verify_elephant_shape.py`
the shape of its law at the crossing, `verify_heavy_runs.py` the heavy-tailed runs and
`verify_aging.py` the aging walk. For the Markov walk of Paper A they use an exact run-count formula
and a dynamic program.

## Lean

The Lean 4 proofs are in `lean/`, one library for each paper (`lean/PaperA` to `lean/PaperD`), with
Lean 4.33.1 and Mathlib. `python -B lean/verify_lean.py` builds them with Lake and checks that every
theorem and lemma uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. The last run
checked 481 declarations for Paper A, 307 for Paper B, 346 for Paper C and 281 for Paper D. The
build output, source hashes and axioms are in `lean/build-log.txt` and
`lean/verification-manifest.json`.
`lean/README.md` says what each library covers and what is not in Lean, and `lean/PaperC/MAP.md`
and `lean/PaperD/MAP.md` match the statements of Papers C and D to their Lean theorems.
