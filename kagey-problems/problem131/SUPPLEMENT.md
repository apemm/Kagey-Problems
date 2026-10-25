# Verification supplement for the papers on Problem 131

This supplement serves the 6 papers on Kagey's Problem 131 by A. Pemmasani. Papers A (arXiv:2610.06935) and B (arXiv:2610.09258) are posted, and Papers C to F are in preparation. Since October 2026 Paper C incorporates Paper B.

| Paper | Title | Source |
| --- | --- | --- |
| A | Uniform Bessel bounds for magnetization crossings in finite Ising chains (arXiv v1: Uniform Bessel bounds for endpoint crossings in the persistent random walk) | `paperA/problem131.tex` |
| B | Vertex crossings in a symmetric Markov multinomial model | `archive/paperB/problem131_multistate.tex` |
| C | Face selection for slowly switching Markov chains | `paperC/problem131_switching.tex` |
| D | The center and the ends of the elephant random walk with rare reversals (before October 17, 2026: Endpoint crossings for the elephant random walk) | `paperD/problem131_memory.tex` |
| E | Endpoint crossings for the planar persistent walk | `paperE/problem131_planar.tex` |
| F | Endpoint crossings for random walks with heavy-tailed runs and for aging walks | `paperF/problem131_heavy_aging.tex` |

The Lean files and the older recorded outputs and ledgers use the statement numbers from before
Papers E and F were split off Papers C and D on October 13, 2026. The exception is
`lean/PaperD/MAP.md`, which gives the numbers of Paper D in its build of October 17, 2026.

The proofs are in the papers. The scripts check the finite statements exactly and the asymptotic
ones numerically, and where possible each number is computed in 2 independent ways. For each paper
we first list the results whose proofs rest on a computation, with the script that checks them and
the 2 methods, and then say what each script checks.

Run `python -B verify_all.py --paper a` in this folder, or use `b`, `c`, `d`, `e`, `f` or `all`.
Add `--full` for the long runs and `--dry-run` to print the commands without running them. For each
paper the runner calls the paper's own runner (with B in `archive/paperB/verify_all.py`),
with `--quick`, or with `--full`, and it skips a paper whose folder is missing. The scripts for
Papers A and B use only the standard library of Python 3. Those for Papers C, D and F need
numpy, scipy and mpmath. Paper C also needs sympy, and Paper D also needs python-flint.
Paper E needs numpy and scipy, and imports
code from `common/two_state.py`, so it also needs the folder `common`. Before most
computations we wrote a prediction and a condition that would refute it in a ledger, and we
recorded the outcome below it. The file `ledger.md` indexes the ledgers of all 6 papers, and each
ledger uses the statement numbers of its date.

## Paper A: the two-state walk

`python -B verify_all.py --paper a` runs `paperA/verify_all.py`, which takes about 2 minutes. The
scripts below are in `paperA/`. Add `--full` to include `verify_every_n.py` and
`verify_every_n_sign.py` (about 21 minutes more), which run before `verify_every_n_guards.py`.

| Result that rests on computation | Script | The 2 methods |
| --- | --- | --- |
| The crossing at every N (theorem), for 2 <= N <= 174 | `verify_certified_bounds.py`, also called by `verify_every_n_guards.py` | The certificate integers come from the run-count sum and the independent recursion with integer weights. Opposite interval signs certify zeta_N. The Lean kernel also checks the short-chain certificates (`lean/PaperA/EveryN.lean`). |
| The crossing equation (proposition), for N <= 174 | `verify_certified_bounds.py` | Outward intervals at the same rational endpoints certify the remainder and logarithm bounds. |
| Part (d) of the corollary on the crossing at every N | `lean/PaperA/EveryNSign.lean` and `verify_certified_bounds.py` | Lean checks rational Taylor bounds at N = 2774 and proves the inequality for every larger N. Independently, outward Python intervals give f(zeta_2774) - 1 > 0.0002124 and f(zeta_2773) - 1 < -0.000005210. |
| The remark on the sign of z_N - zeta_N (computer-assisted throughout) | `verify_certified_bounds.py`, with the original integer checks in `verify_every_n.py` and `verify_every_n_sign.py` | The replay encloses all polynomial comparisons through N = 2773 and all rational-grid separations. The original independent recursion agrees with run counts at N = 401, 1000, 1008, 2000 and 2773, and two float methods agree up to N = 3000. |

The integer tests are exact. Every comparison with zeta_N uses eighty-digit outward intervals,
including a proved pi enclosure and explicit widening of correctly rounded logarithms.
Newton iteration only proposes the bracket of half-width 10^-45. The short-chain margins exceed
0.03 for both the crossing and the crossing equation. For the sign remark the smallest distance
from zeta_N to a certified interval exceeds 1.65e-5 (at N = 218), and for 1001 <= N <= 2773 the
test point exceeds zeta_N/(N - zeta_N) by at least 1.2e-11. The replay bounds any omitted
positive polynomial tail by a geometric series. `paperA/README.md` explains the construction.
Other high-precision tables and sampled asymptotic checks remain numerical diagnostics.

| Script | What it checks |
| --- | --- |
| `verify.py` | Run-count probabilities against a dynamic program and against word enumeration, normalization, generating functions, the 2 lattice-path bijections, variance and normal approximation, and the table of central crossings by exact rational signs at the neighboring decimals. |
| `check_bessel.py` | The central Bessel bound at 1,400 points, and crossing comparisons at high precision up to N = 10^8. |
| `verify_adjacent.py` | Adjacent-bin ratio and global extrema in 474 exact distributions up to N = 80, exact adjacent thresholds, and the cubic gap between the central and adjacent polynomials by word enumeration up to N = 12. |
| `verify_allbin.py` | 5,476 exact coefficient comparisons, 264 all-bin Bessel inequalities, 28 Laguerre-Bessel inequalities, and the crossing and edge expansions at 80 digits. |
| `verify_periodic_window.py` | 66 cyclic run polynomials against enumeration, 120 relative-error inequalities, and root and critical-window samples up to N = 10^12. |
| `verify_ising_coupling.py` | Table 2 and Corollary 5.5. The couplings at the free and periodic central crossings for 10 <= N <= 10^6 from the exact run polynomials, against the main terms of the expansions and the two approximations of Stepanyan et al., the values of N/xi at both crossings, and the secant slopes of the periodic coupling. Asserts the 2 couplings already quoted in Section 5 to 6 decimals and the orderings stated in the text (a few seconds). |
| `verify_ising_coupling_tm.py` | Table 2, second method. Finds both central crossings again from the 2 x 2 transfer matrix of the Ising chain, with the coefficient of the middle bin extracted as a discrete Fourier sum over the N + 1 roots of unity, and asserts that every coupling of Table 2 agrees with the run polynomials within 1e-12 (the largest difference is about 2e-13). Needs NumPy (about 2 minutes). |
| `verify_walls.py` | Proposition 5.7 and Remark 5.8. The mean number of domain walls in the central bin at the free crossing for N = 10^3, 10^4, 10^5 from the exact run polynomial, against z_N + 1/2 + 1/(8 z_N) and the explicit bound of the proposition, the width 1/(2W) in the coupling, and the coupling at which the chain is fully ordered with probability 1/2. Asserts every value quoted in Section 5 (under a second). |
| `verify_field.py` | Theorem 5.9 (a fixed dimensionless magnetic field). Targeted outward interval checks at the four quoted fields certify each limiting and finite-chain minimum, its minimizing bin and its rounding. Full positive polynomials are evaluated without truncation. All bins beyond a certified cutoff are excluded with the uniform bound of the proof, including bins beyond N/2. The finite evaluators are checked against exact word enumeration for N = 2 through 9, and the threshold inequality and equality case against exact rational examples. No field-grid sweep is run. Output is stored in `paperA/data/field_verification.txt` (seconds). |
| `verify_every_n.py` | The crossing at every N (about 8 minutes, only with `--full`). The bounds on I_0 + I_1 at 2,000 points, with the Bessel values by power series and by quadrature, the certificates for 2 <= N <= 174 and as a cross-check up to N = 1000, the margins of the analytic proof, and a table of z_N by 2 bisections. Writes `paperA/data/every_n_certificates.csv` and `paperA/data/every_n_output.txt`. |
| `verify_every_n_sign.py` | The sign of z_N - zeta_N for 1001 <= N <= 2773 (about 13 minutes, only with `--full`). |
| `verify_certified_bounds.py` | Replays all finite certificates with outward intervals, including both integer methods for N <= 174. Writes bounds, margins and input hashes to `data/certified_bounds_output.txt` and `data/certified_bounds_manifest.json` (about ten seconds). |
| `test_certified_decimal.py` | Independent exact-rational tests of interval operations, logarithms, pi, root-grid separation and positive-tail bounds. |
| `verify_every_n_guards.py` | Runs the certified replay, then retains the older rounded diagnostic output and independent integer-DP spot checks. |
| `verify_uniform_llt.py` | The uniform local law in 3 runs. With no argument, the exact identity for P_N(k) in 3,900 cases and the errors of the tilted Bessel form over all bins. With `--run2`, the lemmas and the error bound at 217 sampled points. With `--run3`, the central crossing from the tilted form against p_N. |
| `verify_uniform_llt_cor5.py` | Where the proved central bound of the local law stops being vacuous (the smallest even N is 1454, found 2 ways), and the closed form for bins 1 and N - 1 in 390 exact cases (about 30 seconds). |

`verify.py` checks the exact law against enumeration for N <= 16 at 20 rational values of p. The
polynomials have degree less than N, so for those N this proves the polynomial identities. The last
two local-law scripts report their checks in their output rather than through the exit code, so
that output has to be read. It is also saved in `paperA/data/`. The predictions are in `ledger.md`,
`paperA/data/ledger_every_n.md` and `paperA/data/ledger_llt.md`.

## Paper B: the complete graph

`python -B verify_all.py --paper b` runs `archive/paperB/verify_all.py`, which takes about 2 minutes. The
scripts below are in `archive/paperB/`. Add `--full` to include `verify_B_tie_repair.py` (about 3 minutes
more).

Paper B is incorporated into Paper C since October 2026. These scripts also check the statements
of Sections 5 and 6 of Paper C that came from Paper B (Section 8 of Paper C says which), and the
numbers of Remark 5.13 and of the phases after Example 5.12 of Paper C are the ones in the rows
below for Remark 4.10 and Example 4.9 of Paper B.

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
| `verify_general_start.py` | The tie, the law with a start and the tree form of the constants (about 20 seconds). The weighted Cayley formula by the matrix-tree theorem and by listing all trees for k <= 7, the law with a start against word enumeration for 357 bins, the crossings with a start by 3 methods, and the K_3 window at finite N. Writes `archive/paperB/data/general_start_output.txt`. |
| `verify_B_tie_repair.py` | The exact identity Hess I times Sigma_alpha = identity at rational points for k = 2 to 6, and dynamic programs over all bins at N = 300 and N = 1002 (about 3 minutes, only with `--full`). Writes `archive/paperB/data/B_tie_repair_output.txt`. |
| `verify_crossover_factor.py` | The factor e^E of the crossover theorem (about 50 seconds). Exact S_n by the proper-run formula, a quadrature of the refresh integral and the positive refresh sum at 60 digits, checked against word enumeration for small N. With the argument `repair` (under 1 second) it computes psi by a series and by a continued fraction and checks 3 further examples. |

`verify_general_start.py` and `verify_B_tie_repair.py` report their checks in their output rather
than through the exit code. Some of their lines show failures on purpose, since they belong to the 2
registered predictions that failed (T1(e) and T4), so the output cannot be judged by searching for
"False". The predictions are in `archive/paperB/data/ledger_B_tie.md` and
`archive/paperB/data/ledger_B_crossover.md`.
`predict_general_start.py` and `verify_crossover_factor.py predict` only evaluate formulas for those
registrations and check nothing, so `archive/paperB/verify_all.py` does not run them. The dated logs in
`early_runs/` are from earlier versions of the manuscripts, before they were split.

## Paper C: slowly switching Markov chains

Since October 2026 Paper C incorporates Paper B (see `paperC/README.md`). The command
`python -B verify_all.py --paper c` runs `paperC/verify_all.py`, which runs 7 scripts
and takes about ten minutes (`verify_forest.py` alone takes about 5), or up to about half an hour
with `--full`. The statements that came from Paper B are also checked by the scripts of Paper B
(`--paper b`, above). A script that finds a failed check exits with an error (`verify_forest.py`,
`verify_rate_flows.py` and `verify_weak_field.py` stop at the first failed assertion), and then the
runner stops. The output of the merged version is `paperC/data/verify_output_2026-10-23.txt`. The 2
older stored outputs predate the split and the merge and use the old statement numbers. They are
`paperC/data/verify_output.txt`, a run of 5 scripts from September 26, 2026, and
`paperC/data/verify_output_2026-10-09.txt`, a run of 6 scripts from October 9, 2026. Both include
the planar checks that now belong to Paper E, and neither includes `verify_forest.py`,
`verify_rate_flows.py` or `verify_weak_field.py`. The ledgers are `paperC/data/ledger_C1.md`,
`ledger_C2.md`, `ledger_C4.md` and `ledger_C5.md`, indexed by `paperC/data/ledger.md`, and they also
use the old numbers. The check labels of the scripts use the numbers of the merged paper (build of
October 23, 2026), and those of the sticky checks use the numbers of the note `S3_sticky_note`.

No proof in Paper C rests on a floating-point computation. Exact computer algebra enters in the
first 2 rows below. The third row belongs to the note `S1_endpoint_information_note/`, which was
Section 8 and Appendix E of an earlier version of Paper C. The value c_F = -(k-1)/8 of the next term
on the complete graph (Proposition 4.15(iv)) is computed by hand in Appendix B, and
`verify_second_order.py` also evaluates it exactly for k = 3 and 4.

| Result that rests on computation | Script | The 2 methods |
| --- | --- | --- |
| Proposition S1.4 of the supplement, which proves the row Theta_eps of Table 2 (2 triangles joined by a link) | `verify_examples.py` | Two exact resultants in sympy, from characteristic polynomials recomputed from the matrices. The script also computes a third resultant, which the proof does not use. The thresholds from their closed forms and from numerical roots, and the certificate at eps_0 in exact rational arithmetic. |
| The values of c_F for the 3-arc and for C_4 after Corollary 7.1 | `verify_second_order.py` | The formula of Proposition 4.15(ii) evaluated exactly in sympy in 2 forms (an Euler form and an angle form), and a continuum check by Richardson extrapolation of the torus integral (for C_4 only with `--full`). |
| The moment lemma behind the Fisher theorem (Lemma A.1 of the note S1, no longer in Paper C) | `verify_sticky_fisher.py` | The 3 moments from the exact law with q as a symbol for N <= 12 against the closed forms, and exact rationals at N = 13, 15 and 17 for 3 values of q. The identity for Var X^2 is checked in sympy. |

| Script | What it checks |
| --- | --- |
| `verify_first_order.py` | The exact law and first-order face selection (Sections 2 and 3). The run expansion in exact rationals against all words and a dynamic program, the rate on a face by direct maximization and by a Legendre transform of the Perron root, and the winners from the convex hull and from a direct minimization over all faces. |
| `verify_second_order.py` | The local law, the constants K_F, the crossings, the directed 3-cycle, the next term and the K_3 window (Sections 4, 5 and 7, Appendices A and B). It computes P_N(n) by the run expansion and by a discrete torus integral, and K_F from Perron vectors in double precision and from the Hessian of the Perron root at 30 digits. |
| `verify_examples.py` | The 4-cycle and Table 2, with Section S1 of the supplement. Exit rates with numpy and with mpmath at 40 digits, the winners by the hull and on a grid, and the modes at finite N by a dynamic program of the whole chain and by the run expansion on each face. |
| `verify_sticky_fisher.py` | Sticky priors (the note `S3_sticky_note`, which was Section 6 and Appendix D of Paper C) and the Fisher information of the note S1. The law of the counts by a dynamic program and by exact formulas, the direct-jump probability by Monte Carlo and 2 quadratures, and the information of the endpoint by the run formula and by a complex-step derivative of Paper A's recurrence. It imports Paper A's polynomial S_N and recurrence from `common/two_state.py`, as does `paperE/verify_planar.py`. |
| `verify_forest.py` | The tree formula for the constant on every irreducible face (Proposition 4.9 and Lemma A.3, about 5 minutes). Lemma A.3 in exact rational arithmetic for 119 generators with 2 to 6 states, with the trees and arborescences listed one by one, and in sympy for a general 3-state generator and the directed 3-cycle. In floating point, K_F and C_F(alpha) against the constants of `verify_second_order.py` on random non-reversible faces, the reversible case against Proposition 4.2(b), the directed 3-cycle against Proposition 4.14, and det Sigma at 50 digits against the Hessian of the Perron root. Every part is an assertion, and the floating-point parts use a tolerance. |
| `verify_rate_flows.py` | The rate through flows (Remark 4.12, which was Proposition 4.16 with Example 4.18 before the merge; a few seconds). In floating point on 480 random faces with 2 to 5 states, the balance of the flow at the maximizer, the form as a minimum over balanced flows, the bound by the reversible formula with its gap, and the comparison of the Perron root with that of the geometric symmetrization. On random cycles, the one equation for the net flow and the form with the geometric mean. Also the numbers of the old Example 4.18. Every check is an assertion. |
| `verify_weak_field.py` | A weak field (Proposition 4.16, new in the merge; about a minute). Part (a) by listing all 3^8 words of a 3-state chain. Part (b) on 4 faces (a pair of the path 1-2-3, the 3-arc of the 4-cycle, a non-reversible 3-state face and the full face of K_3): the tilted and untilted face maxima of the continuum density by the torus integral, with the limit of T times their log ratio minus <xi, alpha*> and the shift of the maximizer against the values that completing the square predicts (Richardson in T = 20 to 160); and on the pair at N = 20000 by an exact dynamic program of the chain, against the continuum. Part (d) by the transfer matrix at N = 10^6. Every check is an assertion. |

## Paper D: the elephant random walk

The command `python -B verify_all.py --paper d` runs `paperD/verify_all.py`, which runs 5 scripts
(`verify_elephant_crossing.py`, `verify_elephant_shape.py`, `verify_elephant_odd.py`,
`certify_elephant.py` and, since October 25, 2026, `verify_elephant_modes.py`) and takes about 4
minutes. The quick run of October 25 is `paperD/data/verify_output_2026-10-25.txt`. With `--full` it runs larger cases in its first 2 scripts. A script that finds a failed
check exits with an error, and the runner then names it and exits with an error too. The runner
does not run `certify_convex.py` (about an hour for 10 <= N <= 2000) or `certify_center.py` (about
half an hour), so run them by hand as `python -B certify_convex.py 10 2000` and
`python -B certify_center.py 10 2000`. Their outputs of October 17, 2026 are
`paperD/data/certify_convex_output_2026-10-17.txt` and `paperD/data/certify_center_output_2026-10-17.txt`,
with per-N witnesses in `paperD/data/witnesses_convex_2026-10-17.jsonl` and
`paperD/data/witnesses_center_2026-10-17.jsonl`. The earlier outputs
`paperD/data/certify_convex_output.txt` (October 9) and `paperD/data/certify_center_output_2026-10-16.txt`
are kept as historical logs. The output of October 16 added the check that the enclosure of the
crossing lies above 2/(N+2). The earlier
`paperD/data/certify_center_output.txt`, from October 13, 2026, lacks that check. These outputs
cite no statement numbers. The output of `certify_elephant.py` from October 16, 2026, is
`paperD/data/certify_elephant_output.txt`, and its labels still use the numbers of October 15
(Lemma 3.7, Proposition 3.8 and Lemma 3.11 there are the removed rounding lemma, Proposition 3.7
and Lemma 3.10 now). The other stored outputs predate the split and use the old statement
numbers, and they include the checks of heavy-tailed runs and aging walks that now belong to Paper
F. They are `paperD/data/verify_output.txt` and `verify_output_full.txt`, a quick run and a full run
of 4 scripts from September 26, 2026 (before `verify_aging_urn.py`, `certify_elephant.py` and
`verify_elephant_odd.py`), and `paperD/data/verify_output_2026-10-09.txt`, a quick run of 6 scripts
from October 9, 2026 (still without `verify_elephant_odd.py`). The ledgers are
`paperD/data/ledger_D1.md` and `ledger_D2.md`, indexed by `paperD/data/ledger.md`. Labels that say
"research notes, not printed" check numbers that the paper no longer prints.

The statement numbers in this section are those of the build of October 17, 2026. That build
removed Lemma 3.7 (the rounding error of a double-precision computation) and Theorem 3.15 (the
window around the center), and `lean/PaperD/MAP.md` lists the numbers that moved. A later build of
the same day moved the second order, the tail and the proof of parts (b) to (d) of the proposition
on odd N to the further results of the arXiv version (`paperD/problem131_arxiv.tex`, Sections S1 to S5, with numbers S1.1 and so on). The
numbers here are those of that later build, and `lean/PaperD/MAP.md` lists them too. On October 25,
2026 the convexity window between the humps (the propositions called 3.24 and 3.26 below, the
conjecture 3.14 and the remark 3.27) moved to Section S5 of the arXiv version, and Section 4.2
gained Theorems 4.2 and 4.3 on the modes of the fixed-memory limit law. `lean/PaperD/MAP.md`
gives the numbers of October 25. The journal proofs now use computation only for Theorem 2.6(b),
Proposition 3.7 and Lemma 3.10. Theorems 4.2 and 4.3 use none.

The proofs use computation in 3 places, which take the first 5 rows below. Some constants are values
of explicit sums and integrals, Lemma 3.10 uses ball arithmetic, and the ball-arithmetic enclosure
of the crossing and of the law for 10 <= N <= 2000 proves Propositions 3.24 and 3.26 and, for even
10 <= N < 1688, Proposition 3.7. The other rows are numbers quoted outside the proofs.

| Result that rests on computation | Script | The 2 methods |
| --- | --- | --- |
| The upper bound on C_N in Theorem 2.6(b) (the constant 5200) | `certify_elephant.py` (Part 3, needs python-flint), and without certification `verify_elephant_crossing.py` | Ball arithmetic encloses the first 60 terms of the series sum over t of t^2 log(t+1) 2^(-t/2) in [102.586396, 102.586398], and with a geometric bound on the tail the series is below 102.59. So 3 + 50.4 times 102.59 is below 5200. The uncertified check sums the series by mpmath and directly. |
| Proposition 3.7 for 8 <= N < 1688 (C_N < E_N at eps = 2/(N+2)) | `certify_center.py` (needs python-flint), and `certify_elephant.py` for N = 2, 4, 6 and 8 | For even 10 <= N <= 2000, an exact rational comparison shows that the lower end of the ball-arithmetic enclosure of eps_N lies above 2/(N+2), with smallest margin 1.107 at N = 10. For N = 2, 4, 6 and 8 the ratio C_N/E_N in exact rational arithmetic. As a supplementary check, which the paper no longer uses, Part 1 of `certify_elephant.py` still runs the recursion in double precision with a rounding bound for the 840 even N, and in exact integer arithmetic for 20 values of N. |
| Lemma 3.10, the mode lambda_L of the Landau density and f_L'' near it | `certify_elephant.py` (needs python-flint), and without certification `verify_elephant_shape.py` | Ball arithmetic with rigorous error bounds, with enclosures of f_L' at 4 points and of f_L'' on 2 intervals. The uncertified check uses a real integral and Fourier inversion. Lean proves enclosures of the same quantities by an integration that its kernel checks (`lean/PaperD/U6_Cert.lean`), so the Arb run is an independent check. |
| Proposition 3.24, convexity between the humps for every 10 <= N <= 2000 | `certify_convex.py` (needs python-flint), and without certification `verify_elephant_shape.py` for N <= 600 | Ball arithmetic. For each N the crossing is enclosed and the law is run with that enclosure. For every possible mode the second difference is certified positive between the humps directly, and the 2 inequalities that Theorem 3.19 needs are certified as well. The uncertified check is in double precision. |
| Proposition 3.26, the center is the unique interior minimum for every even 10 <= N <= 2000 | `certify_center.py` (needs python-flint) | Ball arithmetic, with the enclosures of `certify_convex.py`. The hypothesis 2m*+1 <= N/2 of Lemma 3.22 holds for every possible mode, for all 996 even N, and with Proposition 3.24 the lemma applies. The direct test P_N(a) > C_N for every other interior a also succeeds for all of them. |
| Conjecture 3.14, checked for 10 <= N <= 600 and on the grid N = 50, 100, ..., 12800 (and 25600 with `--full`) | `verify_elephant_shape.py` | The law from the minority-count chain and from the law of A_N directly. |
| The numbers in Remarks 3.12 and 3.27, and in Remark S1.3 of the arXiv version | `verify_elephant_crossing.py`, `verify_elephant_shape.py` and `verify_elephant_odd.py` | For Remark S1.3 the Taylor coefficients from 2 dynamic programs (the second at N = 51200 only with `--full`), and the limit from its closed form and from a series. For Remark 3.12 the minority-count chain and the full law of A_N where a law is computed. For Remark 3.27 one method only, the Landau density by quadrature in mpmath. |

| Script | What it checks |
| --- | --- |
| `verify_elephant_crossing.py` | The crossing of the elephant walk (Section 2, Table 1 and Appendix A). The dynamic programs against exact rationals and 40-digit arithmetic, the constants in the proofs of Theorem 2.6(b), Proposition S1.1 of the arXiv version and the lemmas of Appendix A and of Section S1.A, the monotone ratio of Proposition 2.3 for N <= 12, the crossings of Table 1 by the minority-count chain on a window and by the full law of A_N, the comparison with Paper A's walk in Theorem 2.8, and the coefficients of Remark S1.3. For Paper A's walk it uses an exact run-count formula and a dynamic program. |
| `verify_elephant_shape.py` | The shape of the law at the crossing (Section 3 and Appendices B and C). Lemma 2.4 in exact arithmetic for N <= 30 and against all recursive trees for N <= 7, the inequalities in the proof of Proposition 3.7, the dip, the sign changes and convexity between the humps for 10 <= N <= 600 and on the grid, the bounds of Theorem 3.5, the tail of Theorem S2.1 of the arXiv version, the facts behind Theorem 3.9, Lemma 3.10 in double precision, and the numbers of Figure 2 and Remark 3.12. |
| `verify_elephant_odd.py` | Proposition 3.25, whose parts (b) to (d) are proved in Section S3 of the arXiv version, and Remark 3.27 (about 10 seconds). The identity of Proposition 3.25(a) in exact rational arithmetic for 6 odd N and in double precision for 4 more, the crossing for odd N against the root g_N, the constants of part (c) at eps = 2/N, and the half-maximum and inflection points of the Landau density quoted in Remark 3.27. |
| `certify_elephant.py` | Proposition 3.7 for N = 2, 4, 6 and 8, Lemma 3.10 and the series in Theorem 2.6(b) (about a minute). The exact ratios C_N/E_N at eps = 2/(N+2) for N = 2, 4, 6 and 8, the ball-arithmetic enclosures for the Landau density, and the ball-arithmetic enclosure of the series. As a supplementary check it also keeps the double-precision recursion for 8 <= N < 1688 with checks that its integers are exact and that nothing underflows, the same bits from plain Python floats, and exact integer arithmetic for 20 values of N (this was the proof through the rounding lemma, which the paper removed on October 17, 2026). |
| `certify_convex.py` | Proposition 3.24 in ball arithmetic for the range of N given on the command line (not run by `verify_all.py`). |
| `certify_center.py` | Proposition 3.26, and Proposition 3.7 for even 10 <= N < 1688, in ball arithmetic for the even N in the range given on the command line (not run by `verify_all.py`). It imports `certify_convex.py`. |
| `verify_elephant_modes.py` | Section 4.2 (new on October 25, 2026; about a minute). The constants in the proof of Theorem 4.3 at a = 39/40 in 50-digit arithmetic, and the exact mean and variance of the limit against their bounds on a grid of a in [39/40, 1). As an illustration of Step 1 of the proof of Theorem 4.2, the sign pattern of the Gaussian smoothing of the second differences at N = 2000. The numbers of Remark 4.4, which are not proof inputs: the value of a at which the second difference at the center of the exact finite law changes sign for N = 1000, 4000 and 8000 (double precision, bisection), and the sign of g_a''(0) for the limit law on the grid a = 0.55 to 0.85 and its change of sign a_c = 0.66881, from the moment recursion and the cosine series in ball arithmetic. Output in `paperD/data/verify_modes_output.txt`, with the sha256 of the script and the software versions in its first line. |

## Paper E: the planar persistent walk

The command `python -B verify_all.py --paper e` runs `paperE/verify_all.py`, which runs 2 scripts
and takes a few minutes. With `--full` it adds the crossings for N = 1280 to 10240, and the
top-level runner puts Papers C and E at up to about half an hour together. A failed check ends
either script with an error. The folder `paperE/data` holds no output of the checks. The planar
checks are in 2 outputs of Paper C, `paperC/data/verify_output.txt` (September 26, 2026, with
`verify_planar.py` only) and `paperC/data/verify_output_2026-10-09.txt` (October 9, 2026, with both
scripts), and they use the old numbers (6.x and C.x). The ledger is `paperE/data/ledger_C3.md`,
which keeps its name and its numbers from Paper C. The docstrings and check labels of both
scripts use the current numbers.

Paper E says that no proof rests on a floating-point computation. The rows below are numbers
computed at finite N, which illustrate the theorems.

| Result that rests on computation | Script | The 2 methods |
| --- | --- | --- |
| The planar crossings in Section 3 and Figure 2 | `verify_planar.py` | The three levels of Lemma 3.1, and Fourier inversion at the root for N <= 2560 (N <= 640 without `--full`). For larger N one method only. |
| The zero-turn shares at the crossings, and their limit 0.7749 at s = 2r (Corollary 3.6(b)) | `verify_planar.py` | Paper A's polynomial S_N and the three levels. The limit from its closed form. |

| Script | What it checks |
| --- | --- |
| `verify_planar.py` | The planar walk (Section 3 and Appendix A). The origin probability by the three levels of Lemma 3.1, by Fourier inversion, by a dynamic program and by all 4^N words (the first 3 for even N <= 10, all 4 for N <= 8), and Lemma 3.1 and the axis part of Proposition 3.2 exactly for N <= 6. Some bounds at finite N that are not statements of the paper, the increase of omega_N/c_N in h, the crossings and the zero-turn shares, and Paper A's crossing from the run formula and from the recurrence. The identity of Theorem 3.9(a) in exact rational arithmetic for even N <= 30 and 4 values of x. |
| `verify_planar_product.py` | The product curve and turns only. The product formula of Proposition 3.7 in exact rational arithmetic for N = 4, 6, 8. In floating point and only on grids, the inequality F(y/2) <= 2F(y) of Appendix A, the inequality x S_N'(x) <= (2z+2) S_N(x) of Lemma A.4 at N = 16, 64 and 256, and Delta_N >= 0 and the bound of Theorem 3.9(b) for N up to 96. It prints N(v*_N - u_N) against L^2/N without testing it. The proofs do not use these checks. |

## Paper F: heavy-tailed runs and aging walks

The command `python -B verify_all.py --paper f` runs `paperF/verify_all.py`, which runs 3 scripts
and takes a few minutes. With `--full` it adds the heavy cells. A script that finds a failed check exits with an error, and
the runner then names it and exits with an error too. The folder `paperF/data` holds no output of
the checks. The checks of `verify_heavy_runs.py` and `verify_aging.py` are in the outputs of Paper D
from September 26, 2026 (`paperD/data/verify_output.txt` and `verify_output_full.txt`), and those of
all 3 scripts are in `paperD/data/verify_output_2026-10-09.txt`. These outputs use the old numbers
(4.x, 5.x, D.x and E.x). The ledgers are `paperF/data/ledger_D3.md` and `ledger_D4.md`, which keep
their names and their numbers from Paper D. The check labels of the scripts use the current
numbers. In the outputs, Corollary 2.5, Remarks 2.7 and 2.10, Theorems 2.8, 2.9
and 3.4, Section 3 and Tables 1 and 2 appear there as Corollary 4.5, Remarks 4.6 and 4.9, Theorems
4.7, 4.8 and 5.2, Section 5 and Tables 2 and 3. Labels that say "research notes, not printed" check
numbers that the paper does not print.

No proof in Paper F rests on a computation. The rows below are numbers quoted outside the proofs,
and exact checks of 2 proved statements.

| Result that rests on computation | Script | The 2 methods |
| --- | --- | --- |
| Corollary 2.5, C(phi) = 0.7761317206 and the factor 1.2884 | `verify_heavy_runs.py` | The general formula for C(alpha) and the closed form at the golden ratio. |
| The values of R_N in Table 1, and the numbers in Remarks 2.7 and 2.10 and after Theorems 2.8 and 2.9 (crossover sizes, alpha = 1, ratios to the leading terms) | `verify_heavy_runs.py` | The two-renewal formula of Proposition 2.2 and a spectral method, and for small N a first-run recursion and a sum over all run compositions. Some of the largest cells use one method only. |
| The crossing c_200 = 0.8925 after Proposition 3.7, and the values of c_N in Appendix B | `verify_aging.py` | A forward recursion, transfer matrices at roots of unity, and the path-weight form, with an exact rational sign check at c_200 plus and minus 10^-6. |
| The exact checks of Theorem 3.4 and Proposition 3.1 for d = 2, 3, 4 | `verify_aging.py` and `verify_aging_urn.py` | For Theorem 3.4 a forward recursion in exact rationals and a sum over all paths. For Proposition 3.1 the law of the walk by a forward recursion in exact rationals against the Dirichlet-multinomial formula. |

| Script | What it checks |
| --- | --- |
| `verify_heavy_runs.py` | Heavy-tailed runs (Section 2, Tables 1 and 2, and Appendix A). The two-renewal formula against a first-run recursion and a sum over all run compositions for every bin with N <= 14, the end of Proposition 2.1, the constants C(alpha) and C_fr(alpha) by formula and by quadrature, the values of Table 1, the crossover sizes behind Remark 2.7, the Lamperti value (2/pi) tan(pi alpha/2) of Table 2, and the approach to the limits of Theorems 2.8 and 2.9. |
| `verify_aging.py` | The aging walk (Section 3 and Appendix B). The law at c = 1 with a fixed first step and the recursion against all 2^N paths for N <= 12, the ratios of Proposition 3.3 increasing in c, the d-state law of Theorem 3.4 against all paths, the bounds and the expansion of Appendix B, and c_N by 3 methods. |
| `verify_aging_urn.py` | Proposition 3.1 in exact rational arithmetic, with only the standard library. For d = 2, 3, 4, 4 values of theta and up to 7 steps (5 for d = 4), the law of the counts and the last state against the Dirichlet-multinomial formula. Also that the d-state chain of Theorem 3.4 at theta = 1 is the same walk after its first step. |

## Lean

The Lean 4 proofs are in `lean/`, one library for each of Papers A to D (`lean/PaperA` to
`lean/PaperD`), with Lean 4.33.1 and Mathlib. The library `lean/PaperC` also covers Paper E, and
`lean/PaperD` also covers Paper F, with the statement numbers from before the split. The command
`python -B lean/verify_lean.py` builds them with Lake and checks that every theorem and lemma uses
only the axioms `propext`, `Classical.choice` and `Quot.sound`. The recorded run on October 16, 2026,
checked 1257 declarations for Paper A, 307 for Paper B and 346 for Paper C (with Paper E). The run
on October 18, 2026, checked 22427 for Paper D (with Paper F), of which 20517 are steps of the
generated certificates for 101 <= N <= 2000 and 163 are for Paper F, and 4 for the library
`lean/PaperAD`, which joins the libraries of Papers A and D for Theorem 2.8 of Paper D. All
24341 declarations passed. The build output, source hashes and axioms are in `lean/build-log.txt` and
`lean/verification-manifest.json`. The Paper A library has 55 modules (including the root), with
22 linter warnings and no unexpected axioms. Every source hash matches the current Lean files.

The file `lean/README.md` summarizes coverage. The files `lean/PaperA/MAP.md` through
`lean/PaperD/MAP.md` map covered statements to Lean declarations and list partial coverage and
omissions. The C map uses the numbers of the merged Paper C from October 23, 2026, including the statements from Paper B, whose Lean files are in `lean/PaperB`. The D map uses the numbers of Paper D
from October 17, 2026, and for Paper F those from before the split. Both explain where the
statements of Papers E and F moved. For Paper D, Lean proves with no hypothesis Theorem 1.1 as
stated, Theorem 2.8, Lemmas 3.1 to 3.4, Proposition 3.7 for every even N >= 8, the sign chain of
Section 3.5, Propositions 3.24 and 3.26, Proposition 3.25 apart from part (d), Appendices A, B
and D, and Sections S2 and S3 of the arXiv version apart from Proposition 3.25(d), all checked by
the kernel with no `native_decide`. The bulk is proved from named classical results that Lean
states as hypotheses. Theorems 3.8 and 3.9 use Fourier inversion on Z, the characteristic function
of a compound Poisson sum and the Efron-Stein inequality, and the limit in law of Theorem 3.9
also Scheffe's lemma. Lemma 3.10 uses only the unimodality of class L laws (Yamazato 1978), since
Lean checks its numbers by its own integration. Corollary 3.11(b), Theorem 3.21, Corollary 3.23,
Proposition 3.25(d) and Theorem 1.3(c) use the first three and unimodality, and Theorem 1.2
uses these and Scheffe's lemma.
Propositions S1.1 and S1.2 and Lemma S1.6(c), (d) use Hoeffding's inequality for the
hypergeometric law. `lean/PaperD/MAP.md` gives the status of every statement and the source of
each classical result.

For Paper A, every numbered result is formalized in Lean except the Mehler-Heine limit for real
parameters in Remark 4.7, which the paper cites. Lean proves that limit for nonnegative integer
parameters. The results stated at every N, among them Theorem 3.4 and Proposition 3.8 for all
N >= 2, are proved as stated. Each asymptotic error term is replaced by a bound that holds from
some point on and is at least as strong as the paper's. Lean also checks that every value printed
in Tables 1 and 2 is the correct rounding of the quantity it names, and it bounds most decimals
quoted in the text and the captions. As Section 7 of the paper says, the following are not
formalized. These are the couplings J_N^(1) and J_N^(>=2) displayed after Theorem 5.9, the mean
number of domain walls at the periodic crossing stated after Proposition 5.7, the Lambert form of
zeta_N, and the numbers 0.755, 0.74 and 0.013 of Sections 5.4 and 4.5. `lean/PaperA/MAP.md` gives
the Lean theorem for each result, or says that there is none. The imported `Tables` module proves
recurrence identities for material moved to the tables note. The path interpretations and
bijections are not formalized.
