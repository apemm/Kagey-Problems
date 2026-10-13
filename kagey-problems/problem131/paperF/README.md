# Problem 131, Paper F: heavy-tailed runs and aging walks

Kagey asks when the middle bin of a Galton board is as likely as its ends if the ball tends to keep
its direction. Paper F asks the same question for two walks that remember more than their last step.
With alternating runs whose lengths have tail k^(-alpha), started in equilibrium, the ends win for
large N exactly when alpha is below the golden ratio. An aging walk, which switches at step k with
probability c/k, ties exactly at c = 1 for every N, and so does its version with d states. The title
is "Endpoint crossings for random walks with heavy-tailed runs and for aging walks".

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

Conventions. The walk has N steps, L = log N, and P_N(k) is the probability of bin k. A_N is the
number of right steps, C_N = P_N(N/2) is the probability of the center bin and E_N = P_N(N) that of
the right end. The first step is fair unless we say otherwise.

## What is proved

The statement numbers are those of the build of October 13, 2026. Before the split the statements of
Section 2 were numbered 4.x in Paper D and those of Section 3 were numbered 5.x, and the Lean files,
the ledgers and the recorded outputs still use the old numbers.

Heavy-tailed runs (alternating runs, with run lengths xi such that P(xi >= k) = k^(-alpha)).

- The end is E_N = P(D >= N)/2, where D is the first run, with an explicit expansion for the
  stationary start (Proposition 2.1). The law of A_N is a sum over products of the masses of two
  independent renewal processes (Proposition 2.2).
- For 1 < alpha < 2 and every a.s. finite first run, C_N is asymptotic to an explicit constant
  times N^(-1/alpha) (Theorem 2.4).
- With a stationary start, E_N/C_N ~ C(alpha) N^(1 - alpha + 1/alpha), so for large N the ends win
  exactly when alpha < phi. At alpha = phi the ratio tends to C(phi) = 0.7761317206, so the center
  still wins by the factor 1.2884. With a fresh start, E_N/C_N ~ C_fr(alpha) N^(-alpha + 1/alpha),
  so the center wins for every 1 < alpha < 2 (Corollary 2.5).
- For alpha > 2, C_N ~ sqrt(2 mu/(pi v N)) for every a.s. finite first run, and for alpha = 2,
  C_N ~ sqrt(2 mu/(pi N log N)). So the center wins for alpha >= 2 with either start (Theorem 2.7).
- For 0 < alpha < 1 and a fresh start, N C_N tends to the Lamperti density at 1/2, which is
  (2/pi) tan(pi alpha/2), so the ends win (Theorem 2.8). With a fresh start the threshold is
  alpha = 1, where the paper has only a heuristic (Remark 2.9 and Table 3).

The aging walk (switch at step k >= 2 with probability c/k), in its own section, `sec_aging.tex`.

- With the first step fixed, A_N is uniform on {1, ..., N} at c = 1. The ratio of each interior
  bin to the end increases strictly in c, so the crossing is exactly c = 1 for every N and every
  interior bin (Proposition 3.1).
- With d states (start in state 1, and at step k >= 2 move to each of the other d-1 states with
  probability theta/(k+d-2)), the count vector at theta = 1 is exactly uniform over all
  compositions with n_1 >= 1, and every bin ties with the corner exactly at theta = 1 for every N
  (Theorem 3.2).
- A chain that at each step draws a fresh uniform state or repeats its last state has counts with
  exactly the law of Pólya's urn with d colors, for every weight theta (Proposition 3.4).
- With a fair first step each interior bin is twice as likely as an end at c = 1, and its crossing
  is unique and below 1 (Proposition 3.6). For the center,
  c_N = 1 - log 2/(log N + gamma + 2 - 2 log 2) + O((log N)^(-3)) (Proposition 3.7, proved in
  Appendix B).

## What rests on computation

No proof in this paper rests on a computation. The tables, the figures and the numbers quoted outside
the proofs rest on computation alone. The numbers in Remarks 2.6 and 2.9 are of this kind, and the
row alpha = 1 of Table 2 is a heuristic.

## Open

- For heavy tails, a rate in Theorem 2.4, monotonicity of E_N/C_N and uniqueness of the crossover
  size (Remark 2.6), the case alpha = 1 (Remark 2.9), and the full profile of the law.
- Whether the d-state law of Theorem 3.2 is already in Chapter 7 of Engländer and Volkov's 2024 book.
  We have not seen that chapter.

## Prior work

For heavy tails, both scalings are in Godrèche and Luck (2001), and Wang, Li and Hänggi (2016)
already noted the golden ratio as a heuristic for Lévy walks. The Beta limit of the aging walk is due
to Dietz and Sethuraman (2007) and to Engländer and Volkov (2018).

## Files

- `problem131_heavy_aging.tex` is the paper. It includes `sec_intro.tex`, `sec_heavy.tex`,
  `sec_aging.tex` and `sec_verify.tex` (Sections 1 to 4) and the appendices `app_heavy.tex` and
  `app_aging.tex` (Appendices A and B).
- `figures/` holds Figure 2 (`heavy.pdf`), made by `../paperD/figures/make_figures.py`, and Figure 3
  (`aging.pdf`), made by `figures/make_aging_figure.py`. Figure 1 is the program figure
  `../figures/program_F.pdf`, made by `../figures/make_program_figure.py`.
- `verify_heavy_runs.py` checks Section 2, Tables 1 and 2, and Appendix A.
- `verify_aging.py` checks Section 3 and Appendix B.
- `verify_aging_urn.py` checks Proposition 3.4 in exact arithmetic for d = 2, 3, 4.
- `verify_all.py` runs the three scripts.
- `data/figdata_heavy.json` holds cached data for Figure 2, and `data/ledger_D3.md` and
  `data/ledger_D4.md` are the prediction ledgers (they keep their names from Paper D).
- `../lean/PaperD/` holds the Lean 4 proofs of the exact statements of Papers D and F, with the
  statement numbers from before the split.

## How to run the checks

From the Problem 131 folder, `python -B verify_all.py --paper f` runs the checks of this paper. In
this folder, `python -B verify_all.py` does the same, and `--full` adds the heavy cells. The scripts
need numpy, scipy and mpmath. Build the paper with pdflatex, 3 times. The build reads the program
figure from `../figures/program_F.pdf`.
