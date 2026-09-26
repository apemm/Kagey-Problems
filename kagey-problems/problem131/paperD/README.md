# Problem 131, Paper D: endpoint crossings for random walks with memory

Kagey asks when the middle bin of a Galton board is as likely as its ends if the ball tends to keep
its direction. This is the last of 4 papers on Problem 131. They share the notation N (the number of
steps), L = log N, T (the switching scale of a Markov walk with transition matrix I + (T/N)Q), z_N
(the crossing value of T for 2 states), lambda_F and K_F.

- Paper A, "Uniform Bessel bounds for endpoint crossings in the persistent random walk", treats the
  2-state walk, the zero-field Ising chain with free boundaries. It gives explicit uniform Bessel
  bounds for every bin and brackets the crossing p_N for every N >= 2, which gives the crossing
  equation z_N + (1/2) log z_N = L + c_0 + 1/(8 z_N) + R_N with an explicit remainder R_N. It also
  proves a uniform local law for every q <= 1/2, from the diffusive to the ballistic regime.
- Paper B, "Vertex crossings in a symmetric Markov multinomial model", treats the complete graph,
  the d-state Potts chain. Every face ties with the vertices at first order, and Paper B resolves
  the tie at second order. The constants a_k are a face's mass over a Gaussian volume, square roots
  of weighted spanning-tree sums, and the mode changes exactly once, from the vertices to the full
  centers. A start law or a weak field shifts the constants.
- Paper C, "Face selection for slowly switching Markov chains and the planar persistent walk",
  gives the general theory for P = I + (T/N)Q. To first order the mode sits on a face F that
  minimizes tau lambda_F + |F| - 1, where lambda_F is the principal Dirichlet eigenvalue. For
  strongly connected faces it finds the second order, with constants K_F and a crossing equation,
  and it applies the theory to the planar persistent walk.
- Paper D (this folder), "Endpoint crossings for random walks with memory", asks what memory
  changes. The elephant walk crosses at x_n = 2 z_n - log(2 pi) + o(1), about twice the Markov
  value, with a hump near each end. Heavy-tailed runs have the golden-ratio threshold, and aging
  walks get a short remark.

Conventions. Paper D writes n for N, and x_n plays the role of z_n. The walk has n steps (Kagey's
row n+1), A_n is the number of right steps, C_n is the probability of the center bin and E_n the
probability of the right end. The first step is fair unless we say otherwise.

## What is proved

The elephant walk (each step copies a uniformly chosen earlier step and flips it with probability
eps). Put x = n eps.

- For every even n the crossing eps_n is unique and eps_n < 1/2, because C_n/E_n increases in eps
  (Proposition 2.3).
- C_n'(0) = 4/(n+2) exactly (Proposition 2.5).
- C_n >= (4 eps/(n+2))(1 - 2 eps) for 0 < eps < 1/2, and C_n <= (4 eps/(n+2)) n^(2 eps) e^(5200 eps)
  for even n >= 64 and eps(1 + log n) <= 1/100 (Theorem 2.6). So
  log C_n = log(4 eps/(n+2)) + O(eps log n) there.
- x_n = n eps_n satisfies x_n + log x_n = 2 log n - log 8 + O((log n)^2/n), so
  x_n = 2 log n - log log n - log 16 + O(log log n/log n) (Theorem 2.7).
- With the crossing equation of Paper A for the Markov crossing z_n,
  x_n = 2 z_n - log(2 pi) + c_*/log n + O(log log n/(log n)^2), where
  c_* = (1/2) log(2 pi) - 1/4 (Theorem 2.8).
- The end is strictly below its neighbor whenever x >= 2(1 - eps), with two-sided bounds on their
  ratio (Theorem 3.5). So the law at the crossing is not unimodal once x_n >= 2(1 - eps_n)
  (Corollary 3.6). This hypothesis holds for every even n >= 1688 by Theorem 2.6(b) at eps = 2/n
  (the text after Corollary 3.6), and a computation shows it for every 8 <= n < 1688. So the law at
  the crossing is not unimodal for every even n >= 8, computer-assisted below 1688.
- For even n with x >= 1 and x (log n)^2/n -> 0, bin n-m has probability (x/(2m^2))(1 + o(1)),
  uniformly for omega_n x log^2(x+1) <= m <= delta_n n, for any omega_n -> oo with
  omega_n x log^2(x+1) = o(n) and any delta_n -> 0. So the tail is x/(2m^2) for
  x log^2 x << m << n (Theorem 3.8).
- There are absolute constants C_w and n_0 such that for even n >= n_0 with 2 <= x_n <= n^(1/4),
  every interior bin at distance at least C_w (n x_n log n)^(1/2) from the center is above the
  center at the crossing (Theorem 3.9). This window has width O(sqrt(n) log n).
- For large even n the modes a* of the law at the crossing satisfy
  min(a*, n - a*) = O(x_n log^2 x_n), so the profile has a hump near each end (Corollary 3.11).

Heavy-tailed runs (alternating runs, with run lengths xi such that P(xi >= k) = k^(-alpha)).

- The end is E_n = P(D >= n)/2, where D is the first run, with an explicit expansion for the
  stationary start (Proposition 4.1). The law of A_n is a sum over products of the masses of 2
  independent renewal processes (Proposition 4.2).
- For 1 < alpha < 2 and every a.s. finite first run, C_n is asymptotic to an explicit constant
  times n^(-1/alpha) (Theorem 4.4).
- With a stationary start, E_n/C_n ~ C(alpha) n^(1 - alpha + 1/alpha), so for large n the ends win
  exactly when alpha < phi. At alpha = phi the ratio tends to C(phi) = 0.7761317206, so the center
  still wins by the factor 1.2884. With a fresh start, E_n/C_n ~ C_fr(alpha) n^(-alpha + 1/alpha),
  so the center wins for every 1 < alpha < 2 (Corollary 4.5).

The aging walk (switch at step k >= 2 with probability c/k), in Remark 4.8. With the first step
fixed, A_n is uniform on {1, ..., n} at c = 1, and the crossing is exactly c = 1 for every n and
every interior bin.

## Stated with the details omitted

- The two-sided bound log C_n = log(4 eps/(n+2)) + 2 eps log n + O(eps) for n >= 64 and
  eps(1 + log n) <= 1/100, the second-order crossing
  x_n = g_n - (2 g_n log n + g_n^2/2)/(n(1 + 1/g_n)) + O(log n/n), so that x_n < g_n for large n,
  and k_2(n) - 2 log n -> 2 gamma - 2 - log 2 = -1.5387, where k_2(n) = c_2/c_1 comes from
  C_n = c_1 eps + c_2 eps^2 + O(eps^3) (Remark 2.9).
- Given the first step, let M_n be the number of steps that differ from it. Its law is within an
  explicit delta_B of a compound Poisson law with jumps d at rates x/(d(d+1)), and the bulk
  (M_n - x log x)/x tends to the Landau law when x -> oo and x^3 (log n)^2/n -> 0, in particular at
  the crossing (Remark 3.7).
- If f_L''(lambda_0) < 0, every mode m* is x log x + lambda_0 x + O(sqrt(x log x)) at the crossing
  for large n. We computed f_L''(lambda_0) = -0.0789 but did not certify its sign (Remark 3.7).
- For alpha > 2, C_n ~ sqrt(2 mu/(pi v n)) with either start, and for alpha = 2,
  C_n ~ sqrt(2 mu/(pi n log n)). So the center wins for alpha >= 2 (Remark 4.6 and Table 3).
- For 0 < alpha < 1 and a fresh start, n C_n tends to the Lamperti density at 1/2, which is
  (2/pi) tan(pi alpha/2), so the ends win. With a fresh start the threshold is alpha = 1, where we
  only have a heuristic (Remark 4.6 and Table 3).
- For the aging walk with a fair first step,
  c_n = 1 - log 2/(log n + gamma + 2 - 2 log 2) + O((log n)^(-3)) (Remark 4.8).

## Open

- An upper bound log C_n <= log(eps c_1) + eps k_2(n) + O(eps^2 (log n)^k), which would prove the
  refined crossing equation (it matches x_n to 3.6e-10 at n = 51200), and an explicit n beyond
  which the root g_n exceeds x_n.
- The window around the center. Closing it needs second differences of the law, as in
  Conjecture 3.10 (strict convexity between the humps, which would make the center the unique
  interior minimum). The conjecture is checked for 10 <= n <= 600 and n = 800, 1600, ..., 25600.
- The tail for m between x log x and x log^2 x, and effective constants in Theorems 3.8 and 3.9.
- For heavy tails, a rate in Theorem 4.4, monotonicity of E_n/C_n and uniqueness of the crossover
  size (Remark 4.7), the case alpha = 1, and the full profile of the law.

## Prior work

The elephant walk is due to Schütz and Trimper (2004). The cluster picture is Kürsten's coupling with
random recursive trees, and Guérin, Laulin, Raschel and Simon (2025) prove unimodality with a fixed
first step. For heavy tails, both scalings are in Godrèche and Luck (2001), and Wang, Li and Hänggi
(2016) already noted the golden ratio as a heuristic for Lévy walks. The Beta limit of the aging walk
is due to Dietz and Sethuraman (2007) and to Engländer and Volkov (2018). We did not find in the
literature an asymptotic formula for the center probability of the elephant walk when eps -> 0 as n
grows.

## Files

- `problem131_memory.tex` and the section files `sec_*.tex` and `app_*.tex` make up Paper D, the
  main text and Appendices A to C in one PDF, `problem131_memory.pdf`.
- `figures/` holds Figures 2 and 3 of the paper (`shape.pdf`, `heavy.pdf`), made by
  `figures/make_figures.py`, with their captions in `figures/captions.md`. Figure 1 is the shared
  program figure `../figures/program_D.pdf`, made by `../figures/make_program_figure.py`. The paper
  includes it directly, so there is no copy here. `figures/make_figures.py` also makes
  `crossing.pdf`, which the paper no longer prints.
- The research scripts named in the ledgers are not included. The check scripts below recompute the
  numbers printed in the paper.
- `verify_elephant_crossing.py` checks Section 2, Table 1 and Appendix A.
- `verify_elephant_shape.py` checks Section 3 and Appendix B.
- `verify_heavy_runs.py` checks Section 4, Tables 2 and 3, and Appendix C.
- `verify_aging.py` checks Remark 4.8.
- `verify_all.py` runs the 4 scripts.
- `data/ledger.md` is the index of the prediction ledgers `data/ledger_D1.md` to
  `data/ledger_D4.md`.
- `data/figdata_*.json` holds cached data for the figures.
- `data/verify_output.txt` and `data/verify_output_full.txt` hold the output of the quick run and
  the full run of the checks.
- `removed_proofs/` keeps Paper D as first written, before it was cut to its current length.
- `../lean/PaperD/` holds the Lean 4 proofs of the exact statements (not the asymptotics). `MAP.md`
  there gives the Lean name of each statement, with its number in the paper.

Each check script recomputes the numbers of its section and compares them with the printed values.
Where 2 independent methods were used when the numbers were first found, the script runs both. The
scripts also keep some checks of numbers from the research notes that the paper no longer prints.
Their labels say "research notes, not printed".

The one verification supplement for all 4 papers is `../SUPPLEMENT.md`, and
`python -B verify_all.py --paper d` in the Problem 131 folder runs the checks of this paper by
calling `verify_all.py` here. Run `python -B verify_all.py` here (or `python -B verify_all.py
--quick`, the same thing) for the quick run, which takes about 5 minutes, or add `--full` for the
heavy cells (about 45 minutes). The scripts need numpy, scipy and mpmath. Build the paper with
`pdflatex problem131_memory.tex`, run 3 times so that the references settle.
