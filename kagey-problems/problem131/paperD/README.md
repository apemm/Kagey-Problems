# Problem 131, Paper D: endpoint crossings for random walks with memory

Kagey asks when the middle bin of a Galton board is as likely as its ends if the ball tends to keep
its direction. This is the last of four papers on Problem 131, which call each other Papers A, B, C
and D. They share the notation N (the number of steps), L = log N, T (the switching scale of a Markov
walk with transition matrix I + (T/N)Q), z_N (the crossing value of T for two states), lambda_F and
K_F.

- Paper A, "Uniform Bessel bounds for endpoint crossings in the persistent random walk"
  (arXiv:2610.06935), treats the two-state walk, the zero-field Ising chain with free boundaries. It gives explicit uniform Bessel
  bounds for every bin and brackets the crossing p_N for every N >= 2, which gives the crossing
  equation z_N + (1/2) log z_N = L + c_0 + 1/(8 z_N) + R_N with an explicit remainder R_N. It also
  proves a uniform local law for every q <= 1/2, from the diffusive to the ballistic regime.
- Paper B, "Vertex crossings in a symmetric Markov multinomial model" (arXiv:2610.09258), treats the
  complete graph,
  the d-state Potts chain. Every face ties with the vertices at first order, and Paper B resolves
  the tie at second order. The constants a_k are a face's mass over a Gaussian volume, square roots
  of weighted spanning-tree sums, and the mode changes exactly once, from the vertices to the full
  centers. A start law or a weak field shifts the constants.
- Paper C, "Face selection for slowly switching Markov chains and the planar persistent walk" (in
  preparation), gives the general theory for P = I + (T/N)Q. To first order the mode sits on a face
  F that minimizes tau lambda_F + |F| - 1, where lambda_F is the principal Dirichlet eigenvalue. For
  strongly connected faces it finds the second order, with constants K_F and a crossing equation,
  and it applies the theory to the planar persistent walk.
- Paper D (this folder), "Endpoint crossings for random walks with memory" (in preparation), asks
  what memory changes. The elephant walk crosses at x_N = 2 z_N - log(2 pi) + o(1), about twice the
  Markov value, with a hump near each end. Heavy-tailed runs have the golden-ratio threshold, which
  is the lattice form of a heuristic of Wang, Li and Hänggi. Aging walks, with two states and with d
  states, tie exactly at one value of the parameter for every N.

Conventions. Paper D uses the notation that the four papers share. The walk has N steps (Kagey's
row N+1), L = log N, and P_N(k) is the probability of bin k. For the elephant walk x = N eps plays the
role of T and its crossing x_N plays the role of z_N. A_N is the number of right steps,
C_N = P_N(N/2) is the probability of the center bin and E_N = P_N(N) that of the right end. The
first step is fair unless we say otherwise. (Earlier versions of the paper, and the check scripts
and Lean files, write n for N.)

## What is proved

The statement numbers below are those of the build of October 9, 2026. Check them against the
current PDF if the paper has changed since then.

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

Heavy-tailed runs (alternating runs, with run lengths xi such that P(xi >= k) = k^(-alpha)).

- The end is E_N = P(D >= N)/2, where D is the first run, with an explicit expansion for the
  stationary start (Proposition 4.1). The law of A_N is a sum over products of the masses of two
  independent renewal processes (Proposition 4.2).
- For 1 < alpha < 2 and every a.s. finite first run, C_N is asymptotic to an explicit constant
  times N^(-1/alpha) (Theorem 4.4).
- With a stationary start, E_N/C_N ~ C(alpha) N^(1 - alpha + 1/alpha), so for large N the ends win
  exactly when alpha < phi. At alpha = phi the ratio tends to C(phi) = 0.7761317206, so the center
  still wins by the factor 1.2884. With a fresh start, E_N/C_N ~ C_fr(alpha) N^(-alpha + 1/alpha),
  so the center wins for every 1 < alpha < 2 (Corollary 4.5).
- For alpha > 2, C_N ~ sqrt(2 mu/(pi v N)) for every a.s. finite first run, and for alpha = 2,
  C_N ~ sqrt(2 mu/(pi N log N)). So the center wins for alpha >= 2 with either start (Theorem 4.7).
- For 0 < alpha < 1 and a fresh start, N C_N tends to the Lamperti density at 1/2, which is
  (2/pi) tan(pi alpha/2), so the ends win (Theorem 4.8). With a fresh start the threshold is
  alpha = 1, where the paper has only a heuristic (Remark 4.9 and Table 3).

The aging walk (switch at step k >= 2 with probability c/k), in its own section, `sec_aging.tex`.

- With the first step fixed, A_N is uniform on {1, ..., N} at c = 1. The ratio of each interior
  bin to the end increases strictly in c, so the crossing is exactly c = 1 for every N and every
  interior bin (Proposition 5.1).
- With d states (start in state 1, and at step k >= 2 move to each of the other d-1 states with
  probability theta/(k+d-2)), the count vector at theta = 1 is exactly uniform over all
  compositions with n_1 >= 1, and every bin ties with the corner exactly at theta = 1 for every N
  (Theorem 5.2).
- A chain that at each step draws a fresh uniform state or repeats its last state has counts with
  exactly the law of Pólya's urn with d colors, for every weight theta (Proposition 5.4).
- With a fair first step each interior bin is twice as likely as an end at c = 1, and its crossing
  is unique and below 1 (Proposition 5.6). For the center,
  c_N = 1 - log 2/(log N + gamma + 2 - 2 log 2) + O((log N)^(-3)) (Proposition 5.7, proved in
  Appendix E).

## What rests on computation

No statement is left with its details omitted. Section 6 of the paper (`sec_verify.tex`) gives the
full account. The proofs use computation in 3 places only.

- Some constants are values of explicit sums and integrals, such as the 60-term sum in the proof of
  Theorem 2.6(b), evaluated in 30-digit arithmetic (`verify_elephant_crossing.py`).
- Lemma 3.11 rests on enclosures of f_L' at 2 points and of f_L'' on the interval between them,
  computed in ball arithmetic with rigorous error bounds (`certify_elephant.py`).
- Proposition 3.8 rests for N < 1688 on a double-precision computation of C_N/E_N at
  eps = 2/(N+2), with the rounding error bounded in Lemma 3.7 (`certify_elephant.py`, which also
  repeats it in exact integer arithmetic for 20 values of N).

Conjecture 3.16, the tables, the figures and the numbers quoted outside the proofs rest on
computation alone. The numbers in Remarks 2.12, 3.13, 4.6 and 4.9 are of this kind, and the row
alpha = 1 of Table 3 is a heuristic.

## Open

- An upper bound log C_N <= log(eps c_1) + eps k_2(N) + O(eps^2 (log N)^k), and an explicit N beyond
  which the root g_N exceeds x_N (Remark 2.12).
- The window around the center. Closing it needs second differences of the law, as in
  Conjecture 3.16 (strict convexity between the humps, which would make the center the unique
  interior minimum). The conjecture is checked for 10 <= N <= 600 and N = 800, 1600, ..., 25600.
- The tail for m between x log x and x log^2 x, effective constants in Theorems 3.14 and 3.15, and
  an effective error term in Corollary 3.12 (Remark 3.13).
- For heavy tails, a rate in Theorem 4.4, monotonicity of E_N/C_N and uniqueness of the crossover
  size (Remark 4.6), the case alpha = 1 (Remark 4.9), and the full profile of the law.

## Prior work

The elephant walk is due to Schütz and Trimper (2004). The cluster picture is Kürsten's coupling with
random recursive trees, and Guérin, Laulin, Raschel and Simon (2025) prove unimodality with a fixed
first step. For heavy tails, both scalings are in Godrèche and Luck (2001), and Wang, Li and Hänggi
(2016) already noted the golden ratio as a heuristic for Lévy walks. The Beta limit of the aging walk
is due to Dietz and Sethuraman (2007) and to Engländer and Volkov (2018). We did not find in the
literature an asymptotic formula for the center probability of the elephant walk when eps -> 0 as N
grows.

## Files

- `problem131_memory.tex` and the section files `sec_*.tex` and `app_*.tex` make up Paper D, the
  main text and Appendices A to E in one PDF, `problem131_memory.pdf`. The sections are
  `sec_intro`, `sec_erw_crossing`, `sec_erw_shape`, `sec_heavy`, `sec_aging` and `sec_verify`, and the
  appendices are `app_erw_bounds`, `app_erw_profile`, `app_erw_bulk`, `app_heavy` and `app_aging`.
- `figures/` holds Figures 2 and 3 of the paper (`shape.pdf`, `heavy.pdf`), made by
  `figures/make_figures.py`, with their captions in `figures/captions.md`. Figure 1 is the shared
  program figure `../figures/program_D.pdf`, made by `../figures/make_program_figure.py`. The paper
  includes it directly, so there is no copy here. `figures/make_figures.py` also makes
  `crossing.pdf`, which the paper no longer prints.
- The research scripts named in the ledgers are not included. The check scripts below recompute the
  numbers printed in the paper.
- `verify_elephant_crossing.py` checks Section 2, Table 1 and Appendix A.
- `verify_elephant_shape.py` checks Section 3 and Appendices B and C.
- `verify_heavy_runs.py` checks Section 4, Tables 2 and 3, and Appendix D.
- `verify_aging.py` checks Section 5 and Appendix E.
- `verify_aging_urn.py` checks Proposition 5.4 in exact arithmetic for d = 2, 3, 4.
- `certify_elephant.py` certifies the computations behind Lemma 3.7, Proposition 3.8 and
  Lemma 3.11. It needs python-flint.
- `verify_all.py` runs the six scripts.
- `data/ledger.md` is the index of the prediction ledgers `data/ledger_D1.md` to
  `data/ledger_D4.md`.
- `data/figdata_*.json` holds cached data for the figures.
- `data/verify_output.txt` and `data/verify_output_full.txt` hold the output of the quick run and
  the full run of the checks from September 26, 2026. They predate the 2 newest scripts and use the
  statement numbers of that date.
- `removed_proofs/` keeps Paper D as first written in September 2026, before it was shortened. The
  October revision put several of those proofs back.
- `../lean/PaperD/` holds the Lean 4 proofs of the exact statements (not the asymptotics). `MAP.md`
  there gives the Lean name of each statement, with its number in the paper.

Each check script recomputes the numbers of its section and compares them with the printed values.
Where two independent methods were used when the numbers were first found, the script runs both. The
scripts also keep some checks of numbers from the research notes that the paper no longer prints.
Their labels say "research notes, not printed".

The one verification supplement for all four papers is `../SUPPLEMENT.md`, and
`python -B verify_all.py --paper d` in the Problem 131 folder runs the checks of this paper by
calling `verify_all.py` here. Run `python -B verify_all.py` here (or `python -B verify_all.py
--quick`, the same thing) for the quick run, which takes about 5 minutes, or add `--full` for the
heavy cells (about 45 minutes). The scripts need numpy, scipy, mpmath and python-flint. Build the
paper with `pdflatex problem131_memory.tex`, run three times so that the references settle. The
release for the arXiv version is `paperD-arxiv-v1`.
