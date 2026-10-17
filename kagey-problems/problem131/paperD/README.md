# The center and the ends of the elephant random walk with rare reversals

Before October 17, 2026 the paper was titled "Endpoint crossings for the elephant random walk".

In the elephant random walk each step copies a uniformly chosen earlier step and reverses (flips) it
with probability eps. For an even number N of steps the paper studies the crossing, the value of eps
at which the walk is as likely to end at the origin (the middle bin, N/2 right steps) as at N (the
end bin, N right steps). The crossing is unique, and x_N = N eps_N = 2 log N - log log N - log 16 +
o(1), about twice the value for the persistent random walk, because a walk that ends in the middle
usually has a reversal among its first few steps. At the crossing the law has a hump near each end,
and for large even N, and for every even N from 10 to 2000, the middle is the lowest interior bin.

For the persistent (Markov) walk, which copies its last step instead, the question is part of
Problem 131 of Kagey's Open Problem Collection (https://peterkagey.com/problems/131/), posed for a
Galton board, which is why the values of the number of right steps are called bins. The paper uses
one result on the persistent walk, the crossing equation of A. Pemmasani, "Uniform Bessel bounds
for magnetization crossings in finite Ising chains", arXiv:2610.06935 (Proposition 3.8 there, with
its source in `../paperA`), and only to compare the two crossings (Theorem 2.8).

Conventions. The walk has N steps, L = log N, A_N is the number of right steps, and P_N(k) is the
probability of bin k. C_N = P_N(N/2) is the probability of the center bin and E_N = P_N(N) that of
the right end. For the persistent walk T = Nq is the expected number of switches and z_N is its
value at the crossing. For the elephant walk x = N eps plays the role of T and its crossing x_N plays
the role of z_N. The first step is fair unless we say otherwise. (Earlier versions of the paper, and
the check scripts and Lean files, write n for N.)

## What is proved

The statement numbers below are those of the build of October 17, 2026. Check them against the
current PDF if the paper has changed since then. That build removed the rounding lemma (Lemma 3.7
before) and the window theorem (Theorem 3.15 before), and `../lean/PaperD/MAP.md` lists the
numbers that moved. A later build of the same day moved the second order, the tail and the proof
of parts (b) to (d) of the proposition on odd N to Online Resource 1 (`online_resource.tex`, with
numbers S1.1 and so on), and the numbers below are those of that later build. The section
"Statement labels and old numbers" below gives the TeX label of each statement with its old
numbers. Theorems 1.1, 1.2 and 1.3 in the introduction collect the main results below.

The elephant walk (each step copies a uniformly chosen earlier step and flips it with probability
eps). Put x = N eps.

- For every even N the crossing eps_N is unique and eps_N < 1/2, because C_N/E_N increases in eps
  (Proposition 2.3).
- C_N'(0) = 4/(N+2) exactly (Proposition 2.5).
- C_N >= (4 eps/(N+2))(1 - 2 eps) for 0 < eps < 1/2, and C_N <= (4 eps/(N+2)) N^(2 eps) e^(5200 eps)
  for even N >= 64 and eps(1 + log N) <= 1/100 (Theorem 2.6). So
  log C_N = log(4 eps/(N+2)) + O(eps log N) there.
- x_N = N eps_N satisfies x_N + log x_N = 2 log N - log 8 + O((log N)^2/N), so
  x_N = 2 log N - log log N - log 16 + O(log log N/log N) (Theorem 2.7).
- With the crossing equation of the persistent walk (arXiv:2610.06935, Proposition 3.8) for its
  crossing z_N,
  x_N = 2 z_N - log(2 pi) + c_*/log N + O(log log N/(log N)^2), where
  c_* = (1/2) log(2 pi) - 1/4 (Theorem 2.8).
- The center to second order. In the range of Theorem 2.6(b),
  log C_N = log(4 eps/(N+2)) + 2 eps log N + O(eps), with explicit constants (Proposition S1.1 of Online Resource 1). So
  x_N = g_N - (2 g_N log N + g_N^2/2)/(N(1 + 1/g_N)) + O(log N/N), where g_N is the root of
  g + log g = 2 log N - log 8, and x_N < g_N for large N (Proposition S1.2).
- The end is strictly below its neighbor whenever x >= 2(1 - eps), with two-sided bounds on their
  ratio (Theorem 3.5). So the law at the crossing is not unimodal once x_N >= 2(1 - eps_N)
  (Corollary 3.6). This hypothesis holds for every even N >= 8 (Proposition 3.7). For N >= 1688
  the proof uses Theorem 2.6(b) at eps = 2/N. For 10 <= N < 1688 it uses the ball-arithmetic
  enclosure of eps_N from `certify_center.py`, whose lower end lies above 2/(N+2), and for N = 8 an
  exact computation. For N = 2, 4 and 6 the hypothesis fails.
- Given the first step, let M_N be the number of steps that differ from it. For N >= 2 and
  eps <= 1/4 its law is within an explicit delta_B of a compound Poisson law with jumps d at rates
  x/(d(d+1)), bin by bin (Theorem 3.8). The bulk (M_N - x log x)/x tends to the Landau law when
  x -> oo and x^3 (log N)^2/N -> 0, in particular at the crossing, with a bound for each bin
  (Theorem 3.9).
- The Landau density f_L has exactly one mode lambda_L, with -0.22278299 < lambda_L < -0.22278297,
  and -0.0792 <= f_L'' <= -0.0786 near it (Lemma 3.10, by ball arithmetic). So at the crossing every
  mode is at distance x log x + lambda_L x + O(sqrt(x log x)) from the nearer end
  (Corollary 3.11).
- For even N with x >= 1 and x (log N)^2/N -> 0, bin N-m has probability (x/(2m^2))(1 + o(1)),
  uniformly for omega_N x log^2(x+1) <= m <= delta_N N, for any omega_N -> oo with
  omega_N x log^2(x+1) = o(N) and any delta_N -> 0. So the tail is x/(2m^2) for
  x log^2 x << m << N (Theorem S2.1 of Online Resource 1).
- For every N >= 3 and every 0 < eps < 1/2 the second difference of the law changes sign at most
  four times (Theorem 3.18), and once the law has turned convex to the right of its left hump it
  stays strictly convex up to the mirror point (Theorem 3.19). So strict convexity between the
  humps (Definition 3.13) follows from one inequality (Corollary 3.20). It holds for all large even
  N (Theorem 3.21), where the center is then the unique interior minimum (Lemma 3.22 and
  Corollary 3.23), for
  10 <= N <= 2000 by a certified computation (Proposition 3.24), and for all large odd N
  (Proposition 3.25). For odd N the two central bins equal the center of N+1 divided by
  1 - (1 - 2 eps)/N. For every even N from 10 to 2000 the center is the unique interior minimum
  (Proposition 3.26, from the certified convexity and Lemma 3.22).

Heavy-tailed runs and aging walks, which earlier versions treated in Sections 4 and 5 and
Appendices D and E, are now a separate paper in `../paperF`.

## What rests on computation

No statement is left with its details omitted. Section 4 of the paper (`sec_verify.tex`) gives the
full account. The proofs use computation in 3 places only.

- Some constants are values of explicit sums and integrals, such as the 60-term sum in the proof of
  Theorem 2.6(b), enclosed in ball arithmetic (`certify_elephant.py`, and without certification
  `verify_elephant_crossing.py`).
- Lemma 3.10 rests on enclosures of f_L' at 4 points and of f_L'' on an interval, computed in
  ball arithmetic with rigorous error bounds (`certify_elephant.py`).
- For every 10 <= N <= 2000 a ball-arithmetic enclosure of eps_N and of the law at the crossing
  proves Propositions 3.24 and 3.26 (`certify_convex.py` and `certify_center.py`), and for even
  10 <= N < 1688 the same enclosure of eps_N gives Proposition 3.7 (`certify_center.py`).

Short exact computations, such as C_N/E_N for N = 2, 4, 6 and 8 in Proposition 3.7, are done in
rational arithmetic (`certify_elephant.py`). The double-precision computation with a rounding bound
that the paper used for Proposition 3.7 before October 17 is still in `certify_elephant.py` as a
supplementary check.

The tables, the figures and the numbers quoted outside the proofs rest on computation alone, and so
does the evidence for Conjecture 3.14 beyond what Section 3.5 proves (double precision at
N = 3200, 6400, 12800 and 25600). The numbers in Remarks 3.12 and 3.27, and in Remark S1.3 of
Online Resource 1, are of this kind.

## Open

- An upper bound log C_N <= log(eps c_1) + eps c_2/c_1 + O(eps^2 (log N)^k), where
  C_N = c_1 eps + c_2 eps^2 + ... at fixed N,, and an explicit N beyond
  which the root g_N exceeds x_N (Remark S1.3 of Online Resource 1).
- Conjecture 3.14 (strict convexity between the humps) for N between 2000 and the constants N_1 and
  N_1' of Theorem 3.21 (even N) and Proposition 3.25 (odd N). Section 3.5 proves it for all large N,
  and `certify_convex.py` certifies it for 10 <= N <= 2000. The constants are not explicit, and the
  proof as it stands cannot work below N of about 3.5 * 10^56, so no computation closes the gap
  (Remark 3.27). For even N >= 8 and odd N >= 1689 the conjecture follows from one inequality
  (Corollary 3.20 and Proposition 3.25(c)).
- The tail for m between x log x and x log^2 x, effective constants in Theorem S2.1, and
  an effective error term in Corollary 3.11 (Remark 3.12).

## Prior work

The elephant walk is due to Schütz and Trimper (2004). The cluster picture is Kürsten's coupling with
random recursive trees, and Guérin, Laulin, Raschel and Simon (2025) prove unimodality with a fixed
first step. We did not find in the
literature an asymptotic formula for the center probability of the elephant walk when eps -> 0 as N
grows.

## Files

- `problem131_memory.tex` and the section files `sec_*.tex` and `app_*.tex` make up the paper, the
  main text and Appendices A to D in one PDF, `problem131_memory.pdf`. The sections are
  `sec_intro`, `sec_erw_crossing`, `sec_erw_shape` and `sec_verify`, and the
  appendices are `app_erw_bounds`, `app_erw_profile`, `app_erw_bulk` and `app_erw_signs`
  (the proofs for the sign pattern of the second difference).
- `online_resource.tex` is Online Resource 1, a separate PDF `online_resource.pdf` with the center
  and the crossing to second order, the tail and the proof of parts (b) to (d) of Proposition 3.25.
  It reads the labels of the paper through the package `xr-hyper`, so build the paper, then the
  Online Resource, then the paper again.
- `figures/` holds the two figures of the paper, with the captions in `figures/captions.md`.
  Figure 1 (`family.pdf`) is made by `figures/make_family_figure.py` and Figure 2 (`shape.pdf`) by
  `figures/make_figures.py`, both in the shared style `../figures/series_style.py`. The second script makes the
  figure `heavy.pdf` for the heavy-tailed and aging walks and writes it to `../paperF/figures`.
  `figures/make_figures.py` also makes `crossing.pdf`, which the paper no longer prints. Versions
  before October 15, 2026 also printed the shared figure `../figures/program_D.pdf` as Figure 1.
- The research scripts named in the ledgers are not included. The check scripts below recompute the
  numbers printed in the paper.
- `verify_elephant_crossing.py` checks Section 2, Table 1 and Appendix A.
- `verify_elephant_shape.py` checks Section 3 and Appendices B and C.
- `certify_elephant.py` certifies Lemma 3.10, the series in Theorem 2.6(b) and the exact ratios
  for N = 2, 4, 6 and 8 in Proposition 3.7. It also keeps, as a supplementary check, the
  double-precision computation for 8 <= N < 1688 with the rounding bound of the removed lemma. Its
  output is in `data/certify_elephant_output_2026-10-17.txt`, whose labels use the current numbers
  and TeX labels. The older `data/certify_elephant_output.txt` uses the numbers before
  October 17 (see the table below). It needs python-flint.
- `certify_center.py` certifies that every possible mode has 2m*+1 <= N/2 for even N from 10 to
  2000, which with Proposition 3.24 and Lemma 3.22 makes the center the unique interior minimum
  there (Proposition 3.26). It also certifies that the enclosure of eps_N lies above 2/(N+2), which
  gives Proposition 3.7 for 10 <= N < 1688. It takes about half an hour, so `verify_all.py` does not
  run it. Its output is in `data/certify_center_output_2026-10-17.txt`, with per-N witnesses in
  `data/witnesses_center_2026-10-17.jsonl`. The historical outputs
  `data/certify_center_output_2026-10-16.txt` and `data/certify_center_output.txt` (which lacks the
  check for Proposition 3.7) are kept as they were.
- `certify_convex.py` certifies convexity between the humps (Definition 3.13, the property of
  Conjecture 3.14) for a range
  of N in ball arithmetic
  (Proposition 3.24). The whole range 10 to 2000 takes about an hour, so `verify_all.py` does not
  run it. Its output is in `data/certify_convex_output_2026-10-17.txt`, with per-N witnesses in
  `data/witnesses_convex_2026-10-17.jsonl`. The historical output `data/certify_convex_output.txt`
  (October 9) is kept as it was.
- `verify_elephant_odd.py` checks Proposition 3.25 (odd N, with the identity of part (a) in exact
  arithmetic) and the numbers of Remark 3.27. It takes about 10 seconds.
- `verify_all.py` runs the four scripts.
- `data/ledger.md` is the index of the prediction ledgers. `data/ledger_D1.md` and `ledger_D2.md` are
  here, and `ledger_D3.md` and `ledger_D4.md` (heavy tails and aging) are in `../paperF/data`.
- `data/figdata_*.json` holds cached data for the figures.
- `data/verify_output.txt` and `data/verify_output_full.txt` hold the output of the quick run and
  the full run of the checks from September 26, 2026, and `data/verify_output_2026-10-09.txt` the
  output of a quick run from October 9, 2026. All 3 predate the split of October 13, so they also
  run `verify_heavy_runs.py` and `verify_aging.py`, which are now in `../paperF`, and they use the
  statement numbers of their dates. The runs of September 26 predate `verify_aging_urn.py`,
  `verify_elephant_odd.py`, `certify_elephant.py` and `certify_convex.py`. The run of October 9
  includes `verify_aging_urn.py` and `certify_elephant.py` but not `verify_elephant_odd.py`.
- `removed_proofs/` keeps the paper as first written in September 2026, before it was shortened. The
  October revision put several of those proofs back.
- `../lean/PaperD/` holds Lean 4 proofs of selected finite statements. They are the
  correspondence between sign words and the count chain, the strict monotonicity relative to the
  end and the unique crossing, the derivative C_N'(0) = 4/(N+2), unimodality with a fixed first
  step and the inequalities for the end and its neighbor. The non-unimodality at the crossing is
  proved with the endpoint dip as a hypothesis. The identification of the Pólya chain with the
  random recursive tree and the principal analytic and shape results are not formalized end to
  end, and the Python and Arb certificates are separate from Lean. `MAP.md` there gives the Lean
  name of each formalized statement, with its number in the paper. It names 136 declarations, but
  85 of them are for Paper F and many are support lemmas, so they are not 136 theorems of
  Paper D.

Each check script recomputes the numbers of its section and compares them with the printed values.
Where two independent methods were used when the numbers were first found, the script runs both. The
scripts also keep some checks of numbers from the research notes that the paper no longer prints.
Their labels say "research notes, not printed".

The one verification supplement for the Problem 131 folder is `../SUPPLEMENT.md`, and
`python -B verify_all.py --paper d` in the Problem 131 folder runs the checks of this paper by
calling `verify_all.py` here. Run `python -B verify_all.py` here (or `python -B verify_all.py
--quick`, the same thing) for the quick run, which takes a few minutes, or add `--full` for the
heavy cells. The scripts need numpy, scipy, mpmath and python-flint. Build the
paper with `pdflatex problem131_memory.tex`, run three times so that the references settle, and
then `pdflatex online_resource.tex` twice and the paper once more. The arXiv version is pinned
in the paper's Code availability statement.

## Statement labels and old numbers

The `certify_*.py` scripts and `verify_elephant_crossing.py` name statements by their numbers in
the first build of October 17, 2026, before the move to Online Resource 1. `verify_all.py` and
`verify_elephant_shape.py` still use the numbers before October 17 (column four). The
`certify_*.py` scripts add the TeX label, which does not change when statements move. Outputs of
earlier runs are kept in `data/` exactly as they were printed, so some of them use older numbers.
The table gives, for each label the scripts use and for each statement of Section 3, the number now,
the number in the first build of October 17 (the numbers of the check scripts) and the number in the
build just before October 17 (the numbers of `data/certify_elephant_output.txt`, with the same
shift as in `../lean/PaperD/MAP.md`). Numbers with the prefix S are in Online Resource 1.

| TeX label | number now | first build of October 17 | number before October 17 |
|---|---|---|---|
| `prop:mlr` | Proposition 2.3 | Proposition 2.3 | Proposition 2.3 |
| `prop:first-mutation` | Proposition 2.5 | Proposition 2.5 | Proposition 2.5 |
| `thm:erw-bounds` | Theorem 2.6 | Theorem 2.6 | Theorem 2.6 |
| `thm:erw-crossing` | Theorem 2.7 | Theorem 2.7 | Theorem 2.7 |
| `thm:erw-markov` | Theorem 2.8 | Theorem 2.8 | Theorem 2.8 |
| `prop:second-order`, `prop:refined`, `rem:refined` | Propositions S1.1, S1.2, Remark S1.3 | Propositions 2.9, 2.10, Remark 2.11 | Propositions 2.9, 2.10, Remark 2.11 |
| `lem:tree`, `lem:split`, `lem:firstmark`, `lem:unimodal` | Lemmas 3.1 to 3.4 | Lemmas 3.1 to 3.4 | Lemmas 3.1 to 3.4 |
| `thm:dip` | Theorem 3.5 | Theorem 3.5 | Theorem 3.5 |
| `cor:dip` | Corollary 3.6 | Corollary 3.6 | Corollary 3.6 |
| (removed, no label) | none, the rounding bound is now in the docstring of `certify_elephant.py` | none | Lemma 3.7 |
| `prop:dip-hyp` | Proposition 3.7 | Proposition 3.7 | Proposition 3.8 |
| `thm:cp` | Theorem 3.8 | Theorem 3.8 | Theorem 3.9 |
| `thm:landau` | Theorem 3.9 | Theorem 3.9 | Theorem 3.10 |
| `lem:landau-mode` | Lemma 3.10 | Lemma 3.10 | Lemma 3.11 |
| `cor:mode-location` | Corollary 3.11 | Corollary 3.11 | Corollary 3.12 |
| `rem:bulk` | Remark 3.12 | Remark 3.12 | Remark 3.13 |
| `thm:profile` | Theorem S2.1 | Theorem 3.13 | Theorem 3.14 |
| `def:convex` | Definition 3.13 | Definition 3.14 | none (new) |
| (removed, no label) | none | none | Theorem 3.15 (the window) |
| `conj:convex` | Conjecture 3.14 | Conjecture 3.15 | Conjecture 3.16 |
| `lem:D-rec` | Lemma 3.15 | Lemma 3.16 | Lemma 3.17 |
| `lem:interleave` | Lemma 3.16 | Lemma 3.17 | Lemma 3.18 |
| `lem:level-one` | Lemma 3.17 | Lemma 3.18 | Lemma 3.19 |
| `thm:five-blocks` | Theorem 3.18 | Theorem 3.19 | Theorem 3.20 |
| `thm:no-holes` | Theorem 3.19 | Theorem 3.20 | Theorem 3.21 |
| `cor:one-point` | Corollary 3.20 | Corollary 3.21 | Corollary 3.22 |
| `thm:convex-large` | Theorem 3.21 | Theorem 3.22 | Theorem 3.23 |
| `lem:center-convex` | Lemma 3.22 | Lemma 3.23 | none (new) |
| `cor:unique-min` | Corollary 3.23 | Corollary 3.24 | Corollary 3.24 |
| `prop:convex-certified` | Proposition 3.24 | Proposition 3.25 | Proposition 3.25 |
| `prop:odd` | Proposition 3.25 | Proposition 3.26 | Proposition 3.26 |
| `prop:center-small` | Proposition 3.26 | Proposition 3.27 | Proposition 3.27 |
| `rem:convex-open` | Remark 3.27 | Remark 3.28 | Remark 3.28 |
| `sec:convex` | Section 3.5 | Section 3.5 | Section 3.6 |

Legend for the stored outputs in `data/`.

- `certify_elephant_output_2026-10-17.txt`, `certify_center_output_2026-10-17.txt` and
  `certify_convex_output_2026-10-17.txt` are the runs of October 17, 2026, with the current
  numbers. The last line of each is the exit status of the run.
- `certify_elephant_output.txt` (October 16) uses the numbers before October 17 (column four).
  Its Lemma 3.7 is the removed rounding lemma, its Proposition 3.8 is Proposition 3.7 now, and its
  Lemma 3.11 is Lemma 3.10 now.
- `certify_center_output.txt` (October 13), `certify_center_output_2026-10-16.txt` and
  `certify_convex_output.txt` (October 9, in nine chunks) print no statement numbers. They are
  historical aggregate logs without per-N witnesses, and the runs of October 17 replace them as the
  record cited in the paper.
- `verify_output.txt`, `verify_output_full.txt` (September 26) and `verify_output_2026-10-09.txt`
  use the numbers of their dates, before the split of October 13. The table above was checked only
  against the build just before October 17 and does not cover them.

## Certificate runs, exit status and witnesses

`certify_convex.py`, `certify_center.py` and `certify_elephant.py` exit with status 1 if any check
fails. The two range scripts exit with status 2 before computing anything if the range is empty
(Nlo > Nhi), starts below 10, or, for `certify_center.py`, contains no even N. Check the exit
status as well as the printed summary.

With `--witness FILE` the two range scripts also write a JSON-lines file (gzipped if FILE ends in
`.gz`). The printed output is the same with or without it. The first line is a header with the
sha256 of the script and of the files it imports (`certify_convex.py` and
`verify_elephant_shape.py`), the Python, python-flint and FLINT versions, the working precision and
the start time. Then there is one line per N with the exact rational ends `eps_lo` and `eps_hi` of
the enclosure of the crossing, the certified signs of P_N(center) - P_N(N) at the two ends, every
index that can be a mode with its m*, and the certified margins (for `certify_convex.py` the lower
bound of the second difference on [2m*+1, N-2m*-1], the point a0 with its negative upper bound and
the lower bound at 2m*+1, and for `certify_center.py` the slack N/2 - (2m*+1), the lower bound of
P_N(a) - P_N(N/2) over a != N/2, and lo (N+2)/2 as an exact rational). Bounds of balls are written
exactly as `m*2^e`, with a float beside them. The last line is a summary with the counts and the
exit status. The runs of October 17, 2026 were

    python -I -B certify_center.py 10 2000 --witness data/witnesses_center_2026-10-17.jsonl
    python -I -B certify_convex.py 10 2000 --witness data/witnesses_convex_2026-10-17.jsonl

run in parallel from this folder, with the printed output in `data/certify_center_output_2026-10-17.txt`
and `data/certify_convex_output_2026-10-17.txt`. The center run took 2072 s and the convex run 3754 s, side by side
(Python 3.14.3, python-flint 0.9.0, FLINT 3.6.0). Both exited with status 0, with no failures.
The sha256 values in the witness headers are of the files as they were on disk during the run.
`certify_center.py` and `certify_convex.py` had LF line endings and `verify_elephant_shape.py` had
CRLF endings. Its LF form, as committed, has sha256
49c78eea387b293d1dd24acc257a1d362bd7e6ce5fb6219e0eb06465223f811a.
