# Problem 131, Paper D: endpoint crossings for the elephant random walk

Kagey asks when the middle bin of a Galton board is as likely as its ends if the ball tends to keep
its direction. Paper D asks the same question for the elephant random walk, in which each step
copies a uniformly chosen earlier step and flips it with probability eps. The crossing is at
x_N = N eps_N = 2 z_N - log(2 pi) + o(1), about twice the Markov value, and the law at the crossing
has a hump near each end.

The series has six papers by A. Pemmasani, which call each other Papers A to F.

- Paper A (`../paperA`), "Uniform Bessel bounds for endpoint crossings in the persistent random
  walk", arXiv:2610.06935. Kagey's board, at every N.
- Paper B (`../paperB`), "Vertex crossings in a symmetric Markov multinomial model",
  arXiv:2610.09258. The complete graph on d directions.
- Paper C (`../paperC`), "Face selection for slowly switching Markov chains" (in preparation). The
  general theory for the transition matrix I + (T/N)Q.
- Paper D (`../paperD`), "Endpoint crossings for the elephant random walk" (in preparation).
- Paper E (`../paperE`), "Kagey's board in the plane: endpoint crossings for the planar persistent
  walk" (in preparation). Until October 13, 2026 this was Section 6 and Appendix C of Paper C.
- Paper F (`../paperF`), "Endpoint crossings for random walks with heavy-tailed runs and for aging
  walks" (in preparation). Until October 13, 2026 this was Sections 4 and 5 and Appendices D and E
  of Paper D.

The titles of Papers C to F are working titles. Paper A cites Papers C and D under their titles
from before the split, so its references need an update at revision.

Conventions. Paper D uses the notation that the papers share. The walk has N steps (Kagey's
row N+1), L = log N, and P_N(k) is the probability of bin k. For the elephant walk x = N eps plays the
role of T and its crossing x_N plays the role of z_N. A_N is the number of right steps,
C_N = P_N(N/2) is the probability of the center bin and E_N = P_N(N) that of the right end. The
first step is fair unless we say otherwise. (Earlier versions of the paper, and the check scripts
and Lean files, write n for N.)

## What is proved

The statement numbers below are those of the build of October 13, 2026, after the split. Sections 2
and 3 kept their numbers. Check them against the current PDF if the paper has changed since then.

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
- With the crossing equation of Paper A for the Markov crossing z_N,
  x_N = 2 z_N - log(2 pi) + c_*/log N + O(log log N/(log N)^2), where
  c_* = (1/2) log(2 pi) - 1/4 (Theorem 2.8).
- The center to second order. In the range of Theorem 2.6(b),
  log C_N = log(4 eps/(N+2)) + 2 eps log N + O(eps), with explicit constants (Proposition 2.9). So
  x_N = g_N - (2 g_N log N + g_N^2/2)/(N(1 + 1/g_N)) + O(log N/N), where g_N is the root of
  g + log g = 2 log N - log 8, and x_N < g_N for large N (Proposition 2.10). Also
  k_2(N) - 2 log N -> 2 gamma - 2 - log 2 = -1.5387, where k_2(N) = c_2/c_1 comes from
  C_N = c_1 eps + c_2 eps^2 + O(eps^3) (Proposition 2.11).
- The end is strictly below its neighbor whenever x >= 2(1 - eps), with two-sided bounds on their
  ratio (Theorem 3.5). So the law at the crossing is not unimodal once x_N >= 2(1 - eps_N)
  (Corollary 3.6). This hypothesis holds for every even N >= 8 (Proposition 3.8). For N >= 1688
  the proof uses Theorem 2.6(b) at eps = 2/N. For 8 <= N < 1688 it uses a double-precision
  computation of C_N/E_N at eps = 2/(N+2), whose rounding error Lemma 3.7 bounds. For N = 2, 4 and 6
  the hypothesis fails.
- Given the first step, let M_N be the number of steps that differ from it. For N >= 2 and
  eps <= 1/4 its law is within an explicit delta_B of a compound Poisson law with jumps d at rates
  x/(d(d+1)), bin by bin (Theorem 3.9). The bulk (M_N - x log x)/x tends to the Landau law when
  x -> oo and x^3 (log N)^2/N -> 0, in particular at the crossing, with a bound for each bin
  (Theorem 3.10).
- The Landau density f_L has exactly one mode lambda_0, with -0.22278299 < lambda_0 < -0.22278297,
  and -0.0792 <= f_L'' <= -0.0786 near it (Lemma 3.11, by ball arithmetic). So at the crossing every
  mode is at distance x log x + lambda_0 x + O(sqrt(x log x)) from the nearer end
  (Corollary 3.12).
- For even N with x >= 1 and x (log N)^2/N -> 0, bin N-m has probability (x/(2m^2))(1 + o(1)),
  uniformly for omega_N x log^2(x+1) <= m <= delta_N N, for any omega_N -> oo with
  omega_N x log^2(x+1) = o(N) and any delta_N -> 0. So the tail is x/(2m^2) for
  x log^2 x << m << N (Theorem 3.14).
- There are absolute constants C_w and N_0 such that for even N >= N_0 with 2 <= x_N <= N^(1/4),
  every interior bin at distance at least C_w (N x_N log N)^(1/2) from the center is above the
  center at the crossing (Theorem 3.15). This window has width O(sqrt(N) log N).
- For large even N the modes a* of the law at the crossing satisfy
  min(a*, N - a*) = O(x_N log^2 x_N) (Corollary 3.17). This is weaker than Corollary 3.12.
- For every N >= 3 and every 0 < eps < 1/2 the second difference of the law changes sign at most
  four times (Theorem 3.21), and once the law has turned convex to the right of its left hump it
  stays strictly convex up to the mirror point (Theorem 3.22). So strict convexity between the
  humps follows from one inequality (Corollary 3.23). It holds for all large even N
  (Theorem 3.24), where the center is then the unique interior minimum (Corollary 3.25), for
  10 <= N <= 2000 by a certified computation (Proposition 3.26), and for all large odd N
  (Proposition 3.27). For odd N the two central bins equal the center of N+1 divided by
  1 - (1 - 2 eps)/N.

Heavy-tailed runs and aging walks (the old Sections 4 and 5 and Appendices D and E) are now Paper F,
in `../paperF`.

## What rests on computation

No statement is left with its details omitted. Section 4 of the paper (`sec_verify.tex`) gives the
full account. The proofs use computation in 4 places only (the three below, and Proposition 3.26,
which rests on the ball-arithmetic computation of `certify_convex.py` for 10 <= N <= 2000).

- Some constants are values of explicit sums and integrals, such as the 60-term sum in the proof of
  Theorem 2.6(b), evaluated in 30-digit arithmetic (`verify_elephant_crossing.py`).
- Lemma 3.11 rests on enclosures of f_L' at 2 points and of f_L'' on the interval between them,
  computed in ball arithmetic with rigorous error bounds (`certify_elephant.py`).
- Proposition 3.8 rests for N < 1688 on a double-precision computation of C_N/E_N at
  eps = 2/(N+2), with the rounding error bounded in Lemma 3.7 (`certify_elephant.py`, which also
  repeats it in exact integer arithmetic for 20 values of N).

The tables, the figures and the numbers quoted outside the proofs rest on computation alone, and so
does the evidence for Conjecture 3.16 beyond what Section 3.6 proves (double precision at
N = 3200, 6400, 12800 and 25600). The numbers in Remarks 2.12, 3.13 and 3.28 are of this
kind.

## Open

- An upper bound log C_N <= log(eps c_1) + eps k_2(N) + O(eps^2 (log N)^k), and an explicit N beyond
  which the root g_N exceeds x_N (Remark 2.12).
- Conjecture 3.16 (strict convexity between the humps) for N between 2000 and the constants N_1 and
  N_1' of Theorem 3.24 (even N) and Proposition 3.27 (odd N). Section 3.6 proves it for all large N,
  and `certify_convex.py` certifies it for 10 <= N <= 2000. The constants are not explicit, and the
  proof as it stands cannot work below N of about 3 * 10^56, so no computation closes the gap
  (Remark 3.28). For even N >= 8 and odd N >= 1689 the conjecture follows from one inequality
  (Corollary 3.23 and Proposition 3.27(c)).
- The tail for m between x log x and x log^2 x, effective constants in Theorems 3.14 and 3.15, and
  an effective error term in Corollary 3.12 (Remark 3.13).

## Prior work

The elephant walk is due to Schütz and Trimper (2004). The cluster picture is Kürsten's coupling with
random recursive trees, and Guérin, Laulin, Raschel and Simon (2025) prove unimodality with a fixed
first step. We did not find in the
literature an asymptotic formula for the center probability of the elephant walk when eps -> 0 as N
grows.

## Files

- `problem131_memory.tex` and the section files `sec_*.tex` and `app_*.tex` make up Paper D, the
  main text and Appendices A to C in one PDF, `problem131_memory.pdf`. The sections are
  `sec_intro`, `sec_erw_crossing`, `sec_erw_shape` and `sec_verify`, and the
  appendices are `app_erw_bounds`, `app_erw_profile` and `app_erw_bulk`.
- `figures/` holds Figure 2 of the paper (`shape.pdf`), made by
  `figures/make_figures.py`, with the captions in `figures/captions.md`. The same script makes the
  figure `heavy.pdf` of Paper F and writes it to `../paperF/figures`. Figure 1 is the shared
  program figure `../figures/program_D.pdf`, made by `../figures/make_program_figure.py`. The paper
  includes it directly, so there is no copy here. `figures/make_figures.py` also makes
  `crossing.pdf`, which the paper no longer prints.
- The research scripts named in the ledgers are not included. The check scripts below recompute the
  numbers printed in the paper.
- `verify_elephant_crossing.py` checks Section 2, Table 1 and Appendix A.
- `verify_elephant_shape.py` checks Section 3 and Appendices B and C.
- `certify_elephant.py` certifies the computations behind Lemma 3.7, Proposition 3.8 and
  Lemma 3.11. It needs python-flint.
- `certify_convex.py` certifies Conjecture 3.16 for a range of N in ball arithmetic
  (Proposition 3.26). The whole range 10 to 2000 takes about an hour, so `verify_all.py` does not
  run it. Its output is in `data/certify_convex_output.txt`.
- `verify_elephant_odd.py` checks Proposition 3.27 (odd N, with the identity of part (a) in exact
  arithmetic) and the numbers of Remark 3.28. It takes a few seconds.
- `verify_all.py` runs the four scripts.
- `data/ledger.md` is the index of the prediction ledgers. `data/ledger_D1.md` and `ledger_D2.md` are
  here, and `ledger_D3.md` and `ledger_D4.md` (heavy tails and aging) are in `../paperF/data`.
- `data/figdata_*.json` holds cached data for the figures.
- `data/verify_output.txt` and `data/verify_output_full.txt` hold the output of the quick run and
  the full run of the checks from September 26, 2026. They predate `verify_aging_urn.py`,
  `verify_elephant_odd.py` and `certify_convex.py`, and they use the statement numbers of that date.
- `removed_proofs/` keeps Paper D as first written in September 2026, before it was shortened. The
  October revision put several of those proofs back.
- `../lean/PaperD/` holds the Lean 4 proofs of the exact statements (not the asymptotics). `MAP.md`
  there gives the Lean name of each statement, with its number in the paper.

Each check script recomputes the numbers of its section and compares them with the printed values.
Where two independent methods were used when the numbers were first found, the script runs both. The
scripts also keep some checks of numbers from the research notes that the paper no longer prints.
Their labels say "research notes, not printed".

The one verification supplement for the papers is `../SUPPLEMENT.md`, and
`python -B verify_all.py --paper d` in the Problem 131 folder runs the checks of this paper by
calling `verify_all.py` here. Run `python -B verify_all.py` here (or `python -B verify_all.py
--quick`, the same thing) for the quick run, which takes about 5 minutes, or add `--full` for the
heavy cells (about 45 minutes). The scripts need numpy, scipy, mpmath and python-flint. Build the
paper with `pdflatex problem131_memory.tex`, run three times so that the references settle. The
release for the arXiv version is `paperD-arxiv-v1`.
