# The elephant random walk with rare reversals: a Luria–Delbrück approximation and the shape of the law

The paper was titled "The center and the ends of the elephant random walk with rare reversals" from
October 17 to October 24, 2026, and "Endpoint crossings for the elephant random walk" before that.
It is prepared for the Journal of Theoretical Probability.

In the elephant random walk each step copies a uniformly chosen earlier step and reverses (flips) it
with probability eps. The paper studies the regime in which eps tends to 0 as the number of steps N
grows, with x = N eps of order log N. The main result is an explicit total variation bound between
the number M_N of steps that disagree with the first step and a truncated Luria–Delbrück (compound
Poisson) law, and a Landau local limit theorem with an explicit rate that follows from it. The modes,
the shape and the crossing are consequences. Every mode is at distance about x log x - 0.2228 x from
an end. For an even N the crossing is the value of eps at which the walk is as likely to end at the
origin (N/2 right steps) as at an end (N right steps). It is unique, and x_N = N eps_N =
2 log N - log log N - log 16 + o(1), about twice the value for the persistent random walk, because
a walk that ends in the middle usually has a reversal among its first few steps. At the crossing the
law has a hump near each end, and for every even N >= 8 the middle is the unique interior minimum.
The law rises strictly from each end to an interval of maximizing points and falls strictly from
there to the middle.

The question for the persistent (Markov) walk, which copies its last step instead, is Problem 131 of
Kagey's Open Problem Collection (https://peterkagey.com/problems/131/). The paper names it once, in
the acknowledgments. The arXiv version uses one result on the persistent walk, the crossing equation
of A. Pemmasani, "Uniform Bessel bounds for magnetization crossings in finite Ising chains",
arXiv:2610.06935 (Proposition 3.8 there, with its source in `../paperA`), and only to compare the two
crossings (Theorem S1.7 of the arXiv version). The journal version cites that preprint only for the
heuristic comparison in its introduction.

Conventions. The walk has N steps, L = log N, A_N is the number of right steps, and P_N(k) is the
probability of the value k. C_N = P_N(N/2) is the probability of the center and E_N = P_N(N) that of
the right end. For the persistent walk T = Nq is the expected number of switches and z_N is its
value at the crossing. For the elephant walk x = N eps plays the role of T and its crossing x_N plays
the role of z_N. The first step is fair unless we say otherwise. (Earlier versions of the paper, and
the check scripts and Lean files, write n for N.)

## What is proved

The October 24 reframing for the Journal of Theoretical Probability changes the presentation, not
the mathematics. The title, abstract and introduction now open with the regime and put the total
variation approximation and the Landau local limit first (Theorem 1.1), then the modes (Theorem 1.2),
the center and the crossing (Theorem 1.3) and the shape (Theorem 1.4). The convexity window is no
longer part of the main shape theorem. It is Proposition 1.5 (`prop:main-window`), stated as an
eventual result with an uncomputed threshold, certified for 5 <= N <= 2000 at the crossing and
conjectured beyond, and `thm:convex-large` is now Proposition 3.23 (it was Theorem 3.23). The journal
version has no Online Resource. Sections S1 to S4 (second order, tail, odd N, likelihood) are in the
arXiv version only, and the journal text points to that version where it needs them. The likelihood
theorem no longer appears in the journal version. The paper now speaks of points or values k of A_N
where it used to say bins. Fan and Qi (arXiv:2610.16065) and Roy, Takei and Tanemura (J. Appl.
Probab. 62 (2025), 997–1009, doi:10.1017/jpr.2024.106) are cited in the prior-work paragraph.

The October 23 revision adds the following results, with full proofs in the paper or in what is now
the arXiv-only part (then Online Resource 1).

The October 23 editorial changes also retitle Section 3 "The shape of the law at the crossing", split its last subsection into "The shape at every even crossing" and "The prescribed window", retitle Section 4 "The fixed-memory limit", and move the likelihood theorem to Online Resource 1.

- `cor:unique-min` closes the minimum gap for every even N >= 8 and proves exactly two symmetric modal intervals. The argument uses `lem:center-no-holes`, the oriented sign pattern, and the existing endpoint-dip certificates. The stronger prescribed convexity window is still open outside the proved ranges. `cor:height-window` gives a nonempty central convexity window at every even crossing, with endpoint determined by the last left mode and the maximum mass. It can consist only of the center.
- `thm:cp` now bounds total variation, with the same displayed delta_Sigma. `thm:assay-mle` is now Theorem S4.1 of Online Resource 1 (section `or:likelihood`), with its proof there. It gives finite-sample concentration, mean-bias bounds and uniform absolute consistency for the constrained compound Poisson likelihood, using ceil((log N)^3) independent sensitive-founder cultures of size N. The comparison law truncates jump sizes, not the total count. The theorem does not cover the fair-founder mixture likelihood or continuous-time switching of existing cells.
- `cor:fixed-memory-bridge` proves the weak Landau limit of the fixed-memory superdiffusive position limit as memory tends to one. It does not assert uniform local convergence or a sharp bimodality threshold.

The all-even minimum and complete modal-interval theorem are now composed in `../lean/PaperD/ShapeAllEven.lean`, using `CenterNoHoles.lean`, `ModalIntervals.lean` and the existing sign and endpoint-dip results. The height window, total variation strengthening, likelihood theorem and fixed-memory bridge are not formalized. The old pointwise compound Poisson formalization remains valid. Superseded proofs are preserved in `removed_proofs/cuts_2026-10-23`.

The statement numbers below are historical, from the build of October 17, 2026. Check them against the
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
  for even N >= 2 and eps(1 + log N) <= 1/100 (Theorem 2.6). So
  log C_N = log(4 eps/(N+2)) + O(eps log N) there.
- x_N = N eps_N satisfies x_N + log x_N = 2 log N - log 8 + O((log N)^2/N), so
  x_N = 2 log N - log log N - log 16 + O(log log N/log N) (Theorem 2.7).
- With the crossing equation of the persistent walk (arXiv:2610.06935, Proposition 3.8) for its
  crossing z_N,
  x_N = 2 z_N - log(2 pi) + c_*/log N + O(log log N/(log N)^2), where
  c_* = (1/2) log(2 pi) - 1/4 (Theorem S1.7).
- The center to second order. For even N >= 64 and eps(1 + log N) <= 1/100,
  log C_N = log(4 eps/(N+2)) + 2 eps log N + O(eps), with explicit constants, and the lower bound
  holds for every 0 < eps < 1/2 (Proposition S1.1 of the arXiv version). So
  x_N = g_N - (2 g_N log N + g_N^2/2)/(N(1 + 1/g_N)) + O(log N/N), where g_N is the root of
  g + log g = 2 log N - log 8, with the error at most 20822 log N/N for log N >= 30, and
  x_N < g_N for every even N with log N >= 3500 (Proposition S1.2).
- The end is strictly below its neighbor whenever x >= 2(1 - eps), for every N >= 2 and
  0 < eps < 1, with a lower bound on their ratio for these N and eps and an upper bound for
  N >= 3 and eps <= 1/2 (Theorem 3.5). So the law is not unimodal whenever x >= 2(1 - eps) and
  C_N <= E_N, in particular at the crossing once x_N >= 2(1 - eps_N) (Corollary 3.6). This
  hypothesis holds for every even N >= 8 (Proposition 3.7). For N >= 1688
  the proof uses Theorem 2.6(b) at eps = 2/N. For 10 <= N < 1688 it uses the ball-arithmetic
  enclosure of eps_N from `certify_center.py`, whose lower end lies above 2/(N+2), and for N = 8 an
  exact computation. For N = 2, 4 and 6 the hypothesis fails.
- Given the first step, let M_N be the number of steps that differ from it. For N >= 1 and
  0 < eps < 1 its law is within an explicit delta_Sigma <= delta_B of a compound Poisson law with
  jumps d at rates x/(d(d+1)), now in total variation (`thm:cp`, formerly Theorem 3.8). The bulk (M_N - x log x)/x tends to the
  Landau law when x -> oo and x^3 (log N)^2/N -> 0, in particular at the crossing, with the bound
  (889 + 165 log x)/x + 6.6 x/N + x delta_Sigma for each value when eps <= 1/4 and x >= 1
  (Theorem 3.9).
- The Landau density f_L has exactly one mode lambda_L, with -0.22278299 < lambda_L < -0.22278297,
  and -0.0792 <= f_L'' <= -0.0786 near it (Lemma 3.10, by ball arithmetic, and also in Lean by
  kernel-checked integration given the unimodality of f_L). So for every large N, even or odd, and
  every eps with log N <= x <= 2 log N, in particular at the crossing, every mode is at distance
  x log x + lambda_L x + O(sqrt(x log x)) from the nearer end (Corollary 3.11).
- For even N with x >= 1 and x (log N)^2/N -> 0, the value N-m has probability (x/(2m^2))(1 + o(1)),
  uniformly for omega_N x log^2(x+1) <= m <= delta_N N, for any omega_N -> oo and any
  delta_N -> 0. So the tail is x/(2m^2) for x log^2 x << m << N (Theorem S2.1 of Online
  Resource 1).
- For every N >= 3 and every 0 < eps < 1/2 the second difference of the law changes sign at most
  four times, and so does that of the law given the first step for every N >= 2 (Theorem 3.18),
  and once the law has turned convex to the right of its left hump it
  stays strictly convex up to the mirror point (Theorem 3.19). So strict convexity between the
  humps (Definition 3.13) follows from one inequality (Corollary 3.20). It holds for every large
  N, even or odd, and every eps with log N <= x <= 2 log N, so at the crossing for every large N
  (Theorem 3.21 and Proposition 3.25). The October 23 argument proves the unique interior
  minimum and two-hump shape for every even N >= 8 without this convexity window. The window holds for
  5 <= N <= 2000 by a certified computation (Proposition 3.24, for N <= 9 in Lean only). For odd N the two central values equal the center of N+1 divided by
  1 - (1 - 2 eps)/N. The old finite-range minimum result (Proposition 3.26) is superseded by `cor:unique-min`.

Heavy-tailed runs and aging walks, which earlier versions treated in Sections 4 and 5 and
Appendices D and E, are now a separate paper in `../paperF`.

## What rests on computation

No statement is left with its details omitted. Section 5 of the paper (`sec_verify.tex`) gives the
full account. The proofs use computation in 3 places only.

- Some constants are values of explicit sums and integrals, such as the 60-term sum in the proof of
  Theorem 2.6(b), enclosed in ball arithmetic (`certify_elephant.py`, and without certification
  `verify_elephant_crossing.py`).
- Lemma 3.10 rests on enclosures of f_L' at 4 points and of f_L'' on an interval, computed in
  ball arithmetic with rigorous error bounds (`certify_elephant.py`). Lean proves
  enclosures of the same quantities by an integration that its kernel checks, so the Arb run is an independent check.
- For every 10 <= N <= 2000 a ball-arithmetic enclosure of eps_N and of the law at the crossing
  proves Propositions 3.24 and 3.26 (`certify_convex.py` and `certify_center.py`), and for even
  10 <= N < 1688 the same enclosure of eps_N gives Proposition 3.7 (`certify_center.py`). For
  5 <= N <= 9 (only N = 8 for Proposition 3.26) the two propositions rest on the certificate runs
  in Lean alone, with brackets of eps_N found by bisection in exact rational arithmetic.

Short exact computations, such as C_N/E_N for N = 2, 4, 6 and 8 in Proposition 3.7, are done in
rational arithmetic (`certify_elephant.py`). The double-precision computation with a rounding bound
that the paper used for Proposition 3.7 before October 17 is still in `certify_elephant.py` as a
supplementary check.

The tables, the figures and the numbers quoted outside the proofs rest on computation alone, and so
does the evidence for Conjecture 3.14 beyond what Section 3.5 proves (double precision at
N = 3200, 6400, 12800 and 25600). The numbers in Remarks 3.12 and 3.27, and in Remark S1.3 of
the arXiv version, are of this kind.

## Open

- An upper bound log C_N <= log(eps c_1) + eps c_2/c_1 + O(eps^2 (log N)^k), where
  C_N = c_1 eps + c_2 eps^2 + ... at fixed N, and the smallest N beyond which the root g_N exceeds
  x_N. Proposition S1.2 proves g_N > x_N for log N >= 3500, while Table 1 has it already at N = 50
  (Remark S1.3 of the arXiv version).
- Conjecture 3.14 (strict convexity between the humps) for N between 2000 and the constants N_1 and
  N_1' of Theorem 3.21 (even N) and Proposition 3.25 (odd N). Section 3.5 proves it for all large N,
  and `certify_convex.py` certifies it for 10 <= N <= 2000 (Lean also for 5 <= N <= 9). The thresholds are not computed. The shorter mass argument proves the eventual
  window but does not connect it to the finite checks. The maximum-height window
  in `cor:height-window` is available for every even N >= 8. For even N >= 8 and odd N >= 1689 the conjecture follows from one inequality
  (Corollary 3.20 and Proposition S3.1(b)).
- The tail for m between x log x and x log^2 x, effective constants in Theorem S2.1, and
  an effective constant K in Corollary 3.11(b) (Remark 3.12).

## Prior work

The elephant walk is due to Schütz and Trimper (2004). The cluster picture is Kürsten's coupling with
random recursive trees, and Guérin, Laulin, Raschel and Simon (2025) prove unimodality with a fixed
first step. Bokes, Hlubinová and Singh (2023) already give the first-order center coefficient
and a two-Landau approximation in their reversible fluctuation-assay model. The additions here
are the explicit error bounds, exact crossing and shape results, the constrained-likelihood
guarantees and the weak bridge to the fixed-memory limit. The manuscript distinguishes these
from the classical approximations.

## Files

- `problem131_memory.tex` and the section files `sec_*.tex` and `app_*.tex` make up the paper, the
  main text and Appendices A to E in one PDF, `problem131_memory.pdf`. The sections are
  `sec_intro`, `sec_erw_crossing`, `sec_erw_shape`, `sec_bulk_applications` and `sec_verify`, and the
  appendices are `app_erw_bounds` (A), `app_erw_profile` (B, the family-estimate statements),
  `app_erw_bulk` (C), `or_family_proofs` (D, the proofs of the family estimates) and
  `app_erw_signs` (E, the second-difference proofs). Appendices D and E were Sections S5 and S6
  of the Online Resource from October 17 to October 24, 2026, and returned to the article so that
  every proof used by the main theorems is in the article.
- The journal version is `problem131_memory.tex` alone. It has no Online Resource and no
  supplementary material. Where it needs a result of Sections S1 to S4 it cites the arXiv version
  of the paper (bibliography item `arxivD`, "arXiv number to be added", with the comment
  `% arXiv id in November`) through the macro `\arxivonly`. Add the arXiv number to that item once
  the arXiv version has one.
- `online_resource_body.tex` holds Sections S1 to S4: the center and the crossing to second order
  (S1), the tail (S2), the proof of parts (b) to (d) of Proposition 3.25 (S3) and the likelihood
  theorem for the reversible fluctuation assay (S4). Only the arXiv version prints them. Its one
  bibliography item that the journal version does not cite (Hoeffding 1963) is in
  `online_resource_bib.tex`. The separate Online Resource file `online_resource.tex` and its PDF
  were removed on October 24, 2026 (they are in the git history).
- `problem131_arxiv.tex` is the arXiv version. It defines `\PaperDCombined`, inputs
  `problem131_memory.tex` unchanged and appends `online_resource_body.tex` before the bibliography
  under the heading "Further results", so the S numbers and the references between the two parts
  resolve inside one PDF. In this build `\arxivonly{Theorem}{label}` prints the S number instead of
  a citation, and the item `arxivD` is left out. Make it the top-level file of the arXiv
  submission. The upload holds `problem131_arxiv.tex`, `problem131_memory.tex`, the `sec_*` and
  `app_*` files, `or_family_proofs.tex`, `online_resource_body.tex`, `online_resource_bib.tex`, `figures/*.pdf` and a
  `00README.json` that names `problem131_arxiv.tex` as the top-level file.
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
- `../lean/PaperD/` holds the Lean 4 proofs, with the current statement map in
  `MAP.md`. The finite identities, center and crossing bounds, sign chain,
  endpoint-dip certificates and the complete all-even crossing shape are
  kernel-checked. `shape_at_crossing_all_even` gives the strict interior minimum,
  positive central curvature, strict rise and fall, and both complete intervals
  of maximizing points for every even N >= 8, with no convex-window premise.
  The Landau, mode-location, eventual convexity and second-order proofs retain
  the named classical inputs listed in the map. The earlier pointwise compound
  Poisson bound is formalized, but its total variation strengthening is not.
  The maximum-height window, likelihood theorem and fixed-memory bridge also
  remain written proofs. No module uses `native_decide`, and the axiom audit
  permits only `propext`, `Classical.choice` and `Quot.sound`. The Python and Arb
  checks are separate. The library also contains the earlier Paper F modules,
  and most declarations are generated certificate steps, not separate results.

Each check script recomputes the numbers of its section and compares them with the printed values.
Where two independent methods were used when the numbers were first found, the script runs both. The
scripts also keep some checks of numbers from the research notes that the paper no longer prints.
Their labels say "research notes, not printed".

The one verification supplement for the Problem 131 folder is `../SUPPLEMENT.md`, and
`python -B verify_all.py --paper d` in the Problem 131 folder runs the checks of this paper by
calling `verify_all.py` here. Run `python -B verify_all.py` here (or `python -B verify_all.py
--quick`, the same thing) for the quick run, which takes a few minutes, or add `--full` for the
heavy cells. The scripts need numpy, scipy, mpmath and python-flint. Build the
paper with `pdflatex problem131_memory.tex`, run three times so that the references settle. The Code availability statement
of the paper pins the supporting code, certificate records and Lean files to commit
`6f7f9068fc0ebb19c16d6a53fd8df5400bbd91a2`. Later edits to the text of the paper do not change
that pin, but a change to a script, a record or a Lean file would need a new checked commit. The arXiv
version is `problem131_arxiv.tex`. Build it with `pdflatex problem131_arxiv.tex` three times. It
gives the paper followed by Sections S1 to S4 in one PDF, with one bibliography.

## Statement labels and old numbers

The `certify_*.py` scripts and `verify_elephant_crossing.py` name statements by their numbers in
the first build of October 17, 2026, before the move to Online Resource 1. `verify_all.py` and
`verify_elephant_shape.py` still use the numbers before October 17 (column four). The
`certify_*.py` scripts add the TeX label, which does not change when statements move. The
docstrings and comments of the scripts keep these older numbers on purpose. The witness headers
record the sha256 of the raw bytes of the scripts, so even an edit to a comment would break the
link between a script and its archived witnesses. Use the table below to read them. Outputs of
earlier runs are kept in `data/` exactly as they were printed, so some of them use older numbers.
The table preserves the October 17 numbering. For each label the scripts use and each statement of Section 3, it gives that number,
the number in the first build of October 17 (the numbers of the check scripts) and the number in the
build just before October 17 (the numbers of `data/certify_elephant_output.txt`, with the same
shift as in `../lean/PaperD/MAP.md`). Numbers with the prefix S are in Sections S1 to S4, which are now in the arXiv version only.

| TeX label | later build of October 17 | first build of October 17 | number before October 17 |
|---|---|---|---|
| `prop:mlr` | Proposition 2.3 | Proposition 2.3 | Proposition 2.3 |
| `prop:first-mutation` | Proposition 2.5 | Proposition 2.5 | Proposition 2.5 |
| `thm:erw-bounds` | Theorem 2.6 | Theorem 2.6 | Theorem 2.6 |
| `thm:erw-crossing` | Theorem 2.7 | Theorem 2.7 | Theorem 2.7 |
| `thm:erw-markov` | Theorem S1.7 (Theorem 2.8 before October 19) | Theorem 2.8 | Theorem 2.8 |
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
| `prop:odd` | Proposition 3.25 (first paragraph and (a)), with (b) to (d) now Proposition S3.1(a) to (c) | Proposition 3.26 | Proposition 3.26 |
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
CRLF endings. Its LF form, as committed at the pinned commit `6f7f9068`, has sha256
49c78eea387b293d1dd24acc257a1d362bd7e6ce5fb6219e0eb06465223f811a.

On October 24, 2026 two printed labels of `verify_elephant_shape.py` changed from "bin" to
"value", and four printed labels and two docstring lines of `verify_elephant_odd.py` likewise. No
computation changed. So the current `verify_elephant_shape.py` no longer matches the hash in the
witness header of `data/witnesses_convex_2026-10-17.jsonl`. Check the witnesses against the file at
the pinned commit `6f7f9068`, which the Code availability statement of the paper names. The
current files have sha256 0f3ab9a3ae64d0aef9cad82e3c1d86b66be884e3f82fb9824dc1ee666276193d
(`verify_elephant_shape.py`) and
b40d38c8371ff03bd2c1cddb1e1baaebaf14ab7e8b600fa68ae495a5214fab3e (`verify_elephant_odd.py`).
`certify_center.py` and `certify_convex.py` did not change. The quick run of October 24 is in
`data/verify_output_2026-10-24.txt`.

## Final editorial revision

The article is 35 pages, with a 17-page Online Resource and a 52-page combined arXiv version, compared with the preceding 41 + 12 = 53 pages. Six pages have left the main article, but the total reduction is one page: most of the change moves auxiliary proofs rather than deleting mathematics. The center and compound-Poisson/Landau proofs remain in the article. Appendix B retains its statements and numbering, with complete proofs in S5 (S4 before the likelihood theorem moved). The former Appendix D is now S6. The introduction gives shorter summaries of the explicit bounds and the verification section points to existing records instead of repeating their metadata. `cover_letter.md` requests refereeing of all the supplementary proofs. That earlier shortening did not change the Lean proofs or numerical certificates. The later October 23 revision adds the all-even shape formalization and the height window. The fixed-memory result now forms Section 4, after the shape section, and the likelihood theorem is Section S4 of the Online Resource. After that move the article is 34 pages, the Online Resource 18 pages and the combined arXiv version 52 pages. No numerical certificate was recomputed.

On October 24, 2026 the family proofs (S5) and the second-difference proofs (S6) returned to the article as Appendices D and E, so that every proof used by the main theorems is in the article and the Online Resource holds only the additional results S1 to S4. The text of the proofs did not change. The article is now 39 pages, the Online Resource 14 pages and the combined arXiv version 53 pages.

Later on October 24, 2026 the paper was reframed for the Journal of Theoretical Probability (see the
first paragraph of "What is proved"). The journal version is now the article alone, 40 pages, with no
Online Resource. The arXiv version, with Sections S1 to S4 appended, is 53 pages. The figure
`shape.pdf` was redrawn from the cached data with the axis label "right steps a" in place of
"bin a". No numerical certificate was recomputed, and the Lean proofs did not change.
`../SUPPLEMENT.md` still describes the Online Resource and should be brought up to date with this
folder.
