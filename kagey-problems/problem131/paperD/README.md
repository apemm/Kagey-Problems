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
numbers that moved. Theorems 1.1, 1.2 and 1.3 in the introduction collect the main results below.

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
  log C_N = log(4 eps/(N+2)) + 2 eps log N + O(eps), with explicit constants (Proposition 2.9). So
  x_N = g_N - (2 g_N log N + g_N^2/2)/(N(1 + 1/g_N)) + O(log N/N), where g_N is the root of
  g + log g = 2 log N - log 8, and x_N < g_N for large N (Proposition 2.10).
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
  x log^2 x << m << N (Theorem 3.13).
- For every N >= 3 and every 0 < eps < 1/2 the second difference of the law changes sign at most
  four times (Theorem 3.19), and once the law has turned convex to the right of its left hump it
  stays strictly convex up to the mirror point (Theorem 3.20). So strict convexity between the
  humps (Definition 3.14) follows from one inequality (Corollary 3.21). It holds for all large even
  N (Theorem 3.22), where the center is then the unique interior minimum (Lemma 3.23 and
  Corollary 3.24), for
  10 <= N <= 2000 by a certified computation (Proposition 3.25), and for all large odd N
  (Proposition 3.26). For odd N the two central bins equal the center of N+1 divided by
  1 - (1 - 2 eps)/N. For every even N from 10 to 2000 the center is the unique interior minimum
  (Proposition 3.27, from the certified convexity and Lemma 3.23).

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
  proves Propositions 3.25 and 3.27 (`certify_convex.py` and `certify_center.py`), and for even
  10 <= N < 1688 the same enclosure of eps_N gives Proposition 3.7 (`certify_center.py`).

Short exact computations, such as C_N/E_N for N = 2, 4, 6 and 8 in Proposition 3.7, are done in
rational arithmetic (`certify_elephant.py`). The double-precision computation with a rounding bound
that the paper used for Proposition 3.7 before October 17 is still in `certify_elephant.py` as a
supplementary check.

The tables, the figures and the numbers quoted outside the proofs rest on computation alone, and so
does the evidence for Conjecture 3.15 beyond what Section 3.5 proves (double precision at
N = 3200, 6400, 12800 and 25600). The numbers in Remarks 2.11, 3.12 and 3.28 are of this
kind.

## Open

- An upper bound log C_N <= log(eps c_1) + eps c_2/c_1 + O(eps^2 (log N)^k), where
  C_N = c_1 eps + c_2 eps^2 + ... at fixed N,, and an explicit N beyond
  which the root g_N exceeds x_N (Remark 2.11).
- Conjecture 3.15 (strict convexity between the humps) for N between 2000 and the constants N_1 and
  N_1' of Theorem 3.22 (even N) and Proposition 3.26 (odd N). Section 3.5 proves it for all large N,
  and `certify_convex.py` certifies it for 10 <= N <= 2000. The constants are not explicit, and the
  proof as it stands cannot work below N of about 3.5 * 10^56, so no computation closes the gap
  (Remark 3.28). For even N >= 8 and odd N >= 1689 the conjecture follows from one inequality
  (Corollary 3.21 and Proposition 3.26(c)).
- The tail for m between x log x and x log^2 x, effective constants in Theorem 3.13, and
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
  output is in `data/certify_elephant_output.txt`, whose labels still use the numbers of
  October 15. It needs python-flint.
- `certify_center.py` certifies that every possible mode has 2m*+1 <= N/2 for even N from 10 to
  2000, which with Proposition 3.25 and Lemma 3.23 makes the center the unique interior minimum
  there (Proposition 3.27). It also certifies that the enclosure of eps_N lies above 2/(N+2), which
  gives Proposition 3.7 for 10 <= N < 1688. It takes about half an hour, so `verify_all.py` does not
  run it. Its output is in `data/certify_center_output_2026-10-16.txt` (the earlier
  `data/certify_center_output.txt` lacks the check for Proposition 3.7).
- `certify_convex.py` certifies convexity between the humps (Definition 3.14, the property of
  Conjecture 3.15) for a range
  of N in ball arithmetic
  (Proposition 3.25). The whole range 10 to 2000 takes about an hour, so `verify_all.py` does not
  run it. Its output is in `data/certify_convex_output.txt`.
- `verify_elephant_odd.py` checks Proposition 3.26 (odd N, with the identity of part (a) in exact
  arithmetic) and the numbers of Remark 3.28. It takes about 10 seconds.
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
- `../lean/PaperD/` holds the Lean 4 proofs of the exact statements (not the asymptotics). `MAP.md`
  there gives the Lean name of each statement, with its number in the paper.

Each check script recomputes the numbers of its section and compares them with the printed values.
Where two independent methods were used when the numbers were first found, the script runs both. The
scripts also keep some checks of numbers from the research notes that the paper no longer prints.
Their labels say "research notes, not printed".

The one verification supplement for the Problem 131 folder is `../SUPPLEMENT.md`, and
`python -B verify_all.py --paper d` in the Problem 131 folder runs the checks of this paper by
calling `verify_all.py` here. Run `python -B verify_all.py` here (or `python -B verify_all.py
--quick`, the same thing) for the quick run, which takes a few minutes, or add `--full` for the
heavy cells. The scripts need numpy, scipy, mpmath and python-flint. Build the
paper with `pdflatex problem131_memory.tex`, run three times so that the references settle. The
release for the arXiv version is `paperD-arxiv-v1`.
