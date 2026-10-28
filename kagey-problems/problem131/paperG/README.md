# Problem 131, Paper G: the local Lamperti law

Title: "The local Lamperti law: point probabilities for the occupation time of on/off processes
with infinite-mean periods". Target journal: Electronic Journal of Probability (class `ejpecp`, in
TeX Live). This is the infinite-mean companion of Paper F (`../paperF`), and the two papers close
the Problem 131 series. The October 25, 2026 draft that this paper replaces is archived in
`../archive/paperG_lamperti_draft`.

## Abstract

Let A_N be the number of time slots spent in the on state during the first N slots of a discrete-time
on/off process whose on and off periods are independent and have regularly varying tails with indices
in (0,1), so that the periods have infinite mean. Equivalently, A_N counts the right steps of a lattice
Lévy walk in the ballistic regime. When the two tails are comparable, the limit law of A_N/N is the
generalized arcsine law of Lamperti. We prove its local form: N P(A_N = k) converges to Lamperti's
density at one interior point iff uniformly on compact sets iff both period laws satisfy the strong
renewal theorem. Near the ends the law is the tail of a period times a renewal mass function, which
matches the bulk uniformly under Doney's local condition, and the global mode sits at bounded distance
from an end for every index. We give the exact effect of an arbitrary initial period, and we prove that
an initial period of length of order N turns the law into an explicit mixture. Hence the process observed
from time theta N on has a local aging law, with atoms of order 1 at the endpoints and end layers of the
fresh shape and a smaller height. When one tail is heavier, the time on the lighter side has a local
limit law at an intermediate scale, with no renewal condition when the lighter mean is finite or its
index exceeds 1/2. We classify the critical points of Lamperti's density for every index and every tail
ratio, with a closed-form window for the W shape, and we give a lower bound on the number of modes of
the discrete law that two difference statements would turn into the exact count.

## Status

Written October 28, 2026 from the report `reports/Paper F and G finale research.md` (Section 5) and the
research notes in `research_notes/Paper FG finale/` (notes 01, 02, 06 and their audits 08, 09, 10).
Journal build 43 pages, arXiv build 44 pages. Both builds are clean. Seven lettered theorems:

- Theorem A (`thm:local`, Section 4). One point, uniform on compacts and (SRT) for both laws are
  equivalent, under (BAL) and (SPAN). `prop:lambda` identifies the limit with Lamperti's density.
  `cor:local-cases` (alpha > 1/2 free, alpha <= 1/2 iff Caravenna and Doney), `cor:lower` (the lower
  half under (BAL) alone).
- Theorem B (`thm:ends`, Section 5). (a) under (RV); (b), (c) and `cor:mode` under Doney's (LB).
  `lem:E` gives the upper half of (b) under (SRT) for alpha != 1/2. `rem:M0` names the missing lower half.
- Theorem C (`thm:initial`, Section 6). (a) to (f) for a fixed initial run.
- Theorem D (`thm:mixture`, Section 7.1). Initial runs of length of order N under (H0) to (H2) and
  (SRT) for both laws, with no (LB). Proved with the counting bound `lem:count` and `cor:count`.
- Theorem E (`thm:aging`, Section 7.2). The aged law: (a) the bulk is the mixture L_theta under (LB),
  or alpha > 1/2 with nothing more, or alpha <= 1/2 with (SRT) and the cycle condition (U); (b) the
  atoms Q^inf_pm(theta) in closed form under (BAL) alone; (c) the end layers c_pm(theta) u(j) under (U).
  `lem:DL` is the marked Dynkin-Lamperti law of the straddling run, `lem:U` says when (U) holds,
  `lem:aged-pointwise` the pointwise bounds.
- Theorem F (`thm:dominated`, Section 8). One tail heavier, (DOM): (a) the global law, (b) the lower
  half, (c) the local law (free when the lighter mean is finite or alpha_- > 1/2, iff (SRT_-) and (W_+)
  for alpha_- <= 1/2), (d) the end layers and the uniform matching for alpha_- != 1/2. Inputs: the
  one-big-jump estimate `lem:onejump` (Chernoff bound), the local inverse renewal count `lem:Q`, and
  `lem:R`. `rem:dom-initial` outlines the initial run; `rem:claimK` (arXiv build) conjectures the
  big-jump kernel toward the lighter end.
- Theorem G (`thm:shape`, Section 9.1). The critical points of L_{alpha,b} for every alpha and b: three
  iff |log b| < beta_c(alpha), with beta_c in closed form on (alpha_c, alpha_1), zero below alpha_c and
  infinite above alpha_1 = 0.7365 (the root of sin(pi alpha) = alpha), and the degenerate cases.
  `lem:dsrt` (the difference renewal theorem for log-convex laws), `lem:prep-profile`, `thm:signs`
  (the lower bound sigma_L + sigma_+ + sigma_-), `prop:count` (the exact count M_+ + M_- + m_L under the
  two difference statements (L) and (B), which are open), `rem:oscillating` (arXiv build: the earlier
  conjecture fails for oscillating starts).
- Section 10 lists the open problems and Section 11 the computations. Appendix A has the routine facts.

The main file `problem131_lamperti_arxiv.tex` holds the whole paper and compiles alone as the arXiv
version. `problem131_lamperti.tex` is a three-line driver that sets `\arxivbuildfalse` and inputs it,
which builds the journal version. The switch `\ifarxivbuild` marks the two remarks that only the arXiv
version carries. Section files: `sec_intro` (1), `sec_setting` (2), `sec_tools` (3), `sec_local` (4),
`sec_ends` (5), `sec_initial` (6), `sec_aging` (7), `sec_dominated` (8), `sec_shape` (9), `sec_open`
(10), `sec_verify` (11), `sec_appendix` (A).

## Hypotheses

(RV) regularly varying tails with indices in (0,1) or (1,2) for each sign; (BAL) equal indices alpha < 1
with T_-/T_+ -> b in (0, inf); (DOM) alpha_+ < 1 and T_- = o(T_+); (SPAN) aperiodicity; (SRT_sigma) the
strong renewal theorem u(n) ~ (sin pi alpha/pi)/(n T(n)); (LB_sigma) Doney's f(n) <= C T(n)/n; (LR) local
regular variation; (LD2) the second-difference bound; (DSRT_sigma) the difference renewal theorem;
(U) the cycle renewal sequences bounded by C omega; (W_+) the weak condition on the heavier law in the
dominated regime; (S) smoothness of the initial run; (H0) to (H2) for N-dependent initial runs.

## Scripts

Run everything from this folder with `py -I <script>`. The recorded runs used Python 3.14.3, numpy
2.4.2, scipy 1.17.1 and mpmath 1.3.0. The figure also needs matplotlib.

- `verify_all.py`, runs the six main checks below (a few minutes) and writes `data/verify_all_output.txt`.
- `verify_identities.py`, the identities of Section 2 against a sum over all sign strings, N <= 12.
- `verify_shape.py`, the threshold alpha_c, the transform of `prop:lambda` and the double integral at
  alpha = 1/2.
- `verify_local.py`, the exact law at N = 1000, 2000, 4000: Table 1, the end layers, the sign changes,
  the unequal-law ratios.
- `verify_initial.py`, the initial run of Theorem C and the mixture of Theorem D for D uniform on
  {1, ..., N/2}.
- `lamperti_critical.py`, Theorem G: the closed form of beta_c against zero counts of the exponential sum
  on a grid of (alpha, beta), and the flip at beta_c(0.7).
- `layer_check.py [Nmax]`, the ratios behind (L) and (B) of `prop:count`, Sibuya laws.
- `01_exact_law.py`, the exact law by the run recursion for two arbitrary run laws, with a brute-force
  check; `01_compare.py`, the dominated regime (Theorem F) and the control cases, output
  `01_compare_output.txt` (about two minutes).
- `02_aging_exact.py`, the aged law of Theorem E (and the finite-mean aged law of Paper F), with a
  brute-force check for t_a + N <= 12, output `02_aging_output.txt`.
- `shape_engine.py`, the exact law by the run-start recursion with a brute-force self-test, used by
  `scan_alpha_lt1.py [Nmax]` (the counts of `prop:count`: Sibuya laws, unequal tails, runs of length
  at least 2), `scan_starts.py [Nmax]` (general starts and the oscillating counterexamples of
  `rem:oscillating`), `alpha_c_check.py [Nmax]` (the degenerate point) and `mixed_index.py [Nmax]`
  (the shape of the dominated limit laws and the threshold curve). Each writes `<name>_output.txt`.
- `lamperti_law.py`, the Lamperti density and the exact law for the figure; `figures/make_shape_figure.py`
  draws Figure 1 (panels (a) the density, (b) the exact law, (c) the curve beta_c) in the shared style
  `../figures/series_style.py`.

Every output starts with the hash of the script that wrote it. The scripts name statements by their TeX
labels, never by number.

## Build

`pdflatex problem131_lamperti.tex` (journal) or `pdflatex problem131_lamperti_arxiv.tex` (arXiv), three
times each. The class `ejpecp` is in TeX Live.
