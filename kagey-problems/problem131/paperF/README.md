# Problem 131, Paper F: local laws for the occupation time of an on/off process with finite-mean periods

Title: "Local laws for the occupation time of on/off processes with heavy-tailed, finite-mean periods:
bulk, big jumps, boundary layers and aging".
Target journal: Electronic Journal of Probability (class `ejpecp`, no page limit, proofs in the article).

An on/off process alternates on and off periods with independent lengths whose tails are regularly
varying with indices between 1 and 2. A_N is the number of on slots among the first N, equivalently the
number of right steps of a lattice Lévy walk, and P_N(k) is its law. The paper describes P_N at every
point of the range {0,...,N}: a stable bulk at the scale B_N, a big-jump zone on each side where one
period is macroscopic, a renewal boundary layer at each end, and an atom at each endpoint. The initial
period (the first run) enters each zone through a sharp criterion, and observation from time theta N on
ages the atom, the layer and the big-jump zone but not the bulk. The shape follows, including the
golden-ratio threshold for the global mode, which survives aging, an interior minimum at the stable
scale of the opposite runs, and the exact number of modes for all large N. The last section reads the
theorems as the exposure law of a switchback experiment that switches arm at the regenerations of a
slotted queue with heavy-tailed service, after proving that the cycle law of the queue satisfies the
difference hypotheses. The companion paper G treats infinite means (0 < alpha < 1, the local Lamperti
law). The two papers close the Problem 131 series.

Started October 24, 2026 from the plan of October 23, and restructured on October 27 and 28, 2026
from the report `reports/Paper F and G finale research.md` (aging, the queue, the on/off framing, the
journal and arXiv builds). The earlier draft in this folder, "The golden-ratio threshold for a lattice
Lévy walk and ties in coin-turning walks", is archived in `../archive/paperF_golden_aging`.

## Status

Every statement is proved in the article, except that the journal build states Theorem 4.13
(`thm:window`) and refers to the arXiv build for its proof. The journal build is 91 pages and the
arXiv build 95 pages (October 28, 2026). The main results are seven theorems, lettered A to G in the
order of the sections. Statements are numbered by section, and the scripts and the Lean map name them
by their TeX labels, which do not change when statements move.

- Theorem A (`thm:bulk`, Section 3). For a fresh start, under (RV) and (SPAN),
  `sup_k |B_N P_N(k) - h_N((k-pN)/B_N)| -> 0` over the whole range of the count, `sup_k P_N(k) <= C/B_N`,
  and the ratio form on `|k-pN| <= K B_N`, for every relation between the two scales. The classical
  inputs are in Appendix A (`sec_appendix.tex`).
- Theorem B (`thm:bigjump`, Section 4). The boundary layer `P_N(N-j)/T_+(N) -> kappa(j)` under (RV),
  and under (LR) for the plus sign the big-jump kernel `G_N` of `eq:G` on
  `pN + K lambda_N B_N <= k <= N` in the double limit. The uniform boundary layer is now a
  remark after the theorem (`rem:uniform-layer`), read off the additive form of (b). The infinite
  density (`cor:infinite-density`), the need for the double limit (`rem:no-single-formula`) and for
  (LR) (`ex:rv-not-lr`).
- Theorem 4.13 (`thm:window`, Section 4.5). When `b_{+,N} <= b_{-,N}`, the start of the big-jump zone
  up to a factor `1 +- delta`, with the Cramér cost `I_N` of a shortfall of the minus runs. The
  statement is in both builds. The proof (`lem:laplace`, `lem:tilt`, about 5 pages) is in the arXiv
  build only; the journal build says so after the conjecture `rem:window-conj`.
- Theorem C (`thm:preparation`, Section 5). Every law of the initial run, fixed or depending on N under
  the tightness `eq:tight`: the exact defect in the bulk, the bulk criterion `B_n P(D=n) -> 0` (for a
  family, `B_N nubar(N/2) -> 0` with the upper envelope `nubar` of `eq:envelope`), the big-jump zone with
  the term `Psi_N` and its removal when `nubar_+(n) = o(T_+(n))`, the regular case under the scale
  condition (R nu) with one formula on the whole zone up to the end, the boundary layer with the
  prepared kernel, and the interior of the big-jump zone with the window condition. The stationary
  start in closed form (`cor:stationary`), no universal trim (`cor:no-trim`). The identification of the
  run laws from the ends (`thm:inverse`, also labelled `rem:thinning`) is in the arXiv build only.
- Theorem D (`thm:aging`, Section 5.8), a corollary of Theorem C for the run in progress at step
  `t_a + 1`, whose law `eq:aged-nu` satisfies `eq:tight` and (R nu) uniformly in `t_a` (`lem:aged-nu`).
  (a) The bulk does not age, for every `t_a(N)`. (b) The atom is `(1/s) sum_{i=N}^{N+t_a} T_+(i)`, which
  is `N T_+(N)(1 - (1+theta)^(1-alpha))/(s(alpha-1))` for `0 < theta < infinity`. (c) On the whole
  big-jump zone up to the end, for every `t_a(N)`, the kernel gains the term
  `(1/s)[T_+(L_k) - T_+(L_k + t_a)](1 + mu_+ u_-(N-k))`; hence the layer
  `p u_-(j) + 1/s + (1/s)(1 - (1+theta)^(-alpha))(1 + mu_+ u_-(j))` and the interior kernel
  `(N-L_k) f_+(L_k)/mu_- + [2 T_+(L_k) - T_+(L_k + t_a)]/mu_-`. The golden-ratio threshold survives
  aging (`cor:aged-mode`).
- Theorem E (`thm:mode`, Section 6). The global mode is an endpoint or a bulk point according to
  `B_N Q_sigma(N)/H_N`, with the golden-ratio threshold for the stationary start and the constant
  `C(phi) = 0.7761317...` at `alpha = phi`.
- Theorem 6.1 (`thm:second-order`) and Theorem F (`thm:antimode`, Section 6). The exact second-order
  coefficient `C(j)` of the boundary layer and the interior minimum near the plus end at
  `T_-(j*_N) ~ 2 alpha_+ s/N` when `u_- > 1/mu_-`.
- Section 6.4 (`sec:extrema`). The difference renewal theorem (`lem:diff-renewal`), the prepared
  profile (`lem:prep-diff`), the copies of the end profile (`prop:copy`), at least `M_+ + M_- + 1`
  modes (`thm:modes-lower`), a prepared log-convex start with at least four modes
  (`cor:four-modes`), the first differences in the layer under (LD) (`lem:plus-diff`,
  `thm:first-diff`), and the extrema up to distance `N^(1-eta)` (`thm:ends`).
- Theorem G (`thm:mode-count`, Section 6.5). Under (SPAN), (LR), (LD2) for both signs and (EQ), for a
  fresh or fair start with no ties, the first differences of P_N change sign in a fixed order for all
  large N and P_N has exactly `M_+ + M_- + 1` modes. Three modes for all large N if and only if each
  end profile has one local maximum (`cor:three-modes`, `lem:one-max`, `cor:logconvex-three`).
  (EQ) may be replaced by `min theta_N >= theta_0` along a sequence (`cor:sequences`). Laws with
  `f(1) = 0` give at least five modes for the fair start, and the law `f(n) ∝ n^{-5/2}` on n >= 2 gives
  15 (`ex:runs2`). The difference form of the local big jump, uniform in the number of runs
  (`lem:diff-bigjump`), is stated in Section 6.5. Open: unequal scales and a bound for every N
  (`rem:mode-open`, Section 8).
- Section 7 (`sec:exposure`). The slotted Geo/G/1 queue, the switchback that switches arm at the
  regenerations, and the reduction to A_N. Proposition 7.1 (`prop:cycle`): the cycle law satisfies (LR)
  and (SPAN) when the service does (known: Kortchemski 2015, Janson 2012, Denisov and Shneer 2010 for
  the M/G/1 busy period), and (LD) and (LD2) when the service satisfies (LD2), with
  `f_C(n+1) - f_C(n) = -(alpha+1+o(1)) f_C(n)/n`; (EQ) across arms. The second-difference bounds of
  `lem:second-bigjump` (Appendix B), stated for deviations of order m, give (LD2). The exposure corollaries:
  the imbalance at the scale `N^(1/alpha)` (`cor:exposure-bulk`, with the endpoint exception for a
  random-time start when alpha < phi), severe imbalance and no switch (`cor:exposure-tail`), the most
  likely exposure and the 3 modes (`cor:exposure-mode`, the last conditional on strict log-convexity
  of the cycle law, checked numerically only).
- Section 8 (`sec:open`). Open problems. Section 9 (`sec:verify`). The computations.
- Appendix B (`app:modes`). The proofs for Theorem G, including `lem:second-bigjump`, the one second-difference
  lemma, from which `lem:plus-second`(i) to (iii) and the (LD2) bound of Section 7 follow.
- The exact identities of Section 2 (`prop:fresh-identity`, `prop:first-run`, `lem:green`,
  `prop:final-run` with its explicit form `eq:final-explicit`, `lem:counting`) hold for every `N`
  with no hypothesis. The facts on regular variation are collected in `lem:rv`.

## Files

- `problem131_levy_arxiv.tex`, the whole paper (class `ejpecp`, in TeX Live). Compiled alone it
  builds the arXiv version. `problem131_levy.tex` is a three-line driver that sets `\arxivbuildfalse`
  and inputs it, which builds the journal version. The switch `\ifarxivbuild` marks the material
  that only the arXiv version carries (the proof of `thm:window`, the identification remark, the
  remark on switching after a geometric number of cycles). The section files are `sec_intro` (1),
  `sec_setting` (2), `sec_bulk` (3), `sec_bigjump` (4), `sec_preparation` and `sec_aging` (5),
  `sec_shape` (6), `sec_exposure` (7), `sec_open` (8), `sec_verify` (9), `sec_appendix` (Appendix A)
  and `sec_modeproofs` (Appendix B). The PDFs are `problem131_levy.pdf` (journal) and
  `problem131_levy_arxiv.pdf` (arXiv).
- `figures/atlas.pdf` (and `.png`), Figure 1, made by `figures/make_atlas_figure.py` from
  `data/atlas_N5000.json` and `data/antimode.json` in the shared style `../figures/series_style.py`.
  The caption source is `figures/captions.md`. The script also writes `data/atlas_pieces.json`.
- `certify_atlas.py`, the exact law `P_N` by the recursion `eq:run-recursion` and the final-run
  identity `prop:final-run` in double precision, with the a priori relative error bound
  `eps_N = (1 + gamma_{N+2})^{N+2} - 1` and a comparison with the same recursion in 128-bit ball
  arithmetic at N = 600. Output `data/atlas_N5000.json`. The other scripts import its functions.
- `certify_antimode.py`, the certified antimodes at N = 600, 1200, 2400, 4000, 8000 and the two
  predictions of `thm:antimode` for the figure. Output `data/antimode.json`.
- `verify_identities.py`, the identities of Section 2, `eq:kappa`, `prop:final-run` in both forms,
  the renewal identities `eq:cover`, `eq:cover-v`, `eq:conv-v`, the two forms of `eq:Cj` and the
  inversion of `thm:inverse`(a), by brute force in exact rational arithmetic for N <= 12. Output
  `data/verify_identities_output.txt`.
- `verify_coefficient.py`, `C(j)` of `thm:second-order` against the exact law, Table 1
  (`tab:antimode`) against the certificates, the ratios after `eq:second-renewal`, the constant of
  `thm:mode`(d) and the certificate `data/atlas_N5000.json`. Output `data/verify_coefficient_output.txt`.
- `verify_preparation.py`, `thm:preparation`(c), (d) and `cor:stationary` for the fresh, the
  stationary and one regularly varying initial run at N = 1200 and 2400. Outputs
  `data/verify_preparation_output.txt` and `data/preparation_ratios.json`.
- `verify_bigjump.py`, the numbers of `rem:no-single-formula`. Output `data/verify_bigjump_output.txt`.
- `verify_modes.py`, the numbers of Section 6.4 quoted in Section 9. Output `data/verify_modes_output.txt`.
- `verify_mode_count.py`, the numbers of Section 6.5 quoted there and in Section 9, every sign
  certified against the rounding bound. Output `data/verify_mode_count_output.txt`.
- `verify_aging.py`, Theorem D and `cor:aged-mode` against the exact aged law (zeta law, alpha = 1.5,
  theta = 0.5, 1, 2, N = 500, 1000, 2000), after a brute-force check of the method for `t_a + N <= 12`.
  Output `data/verify_aging_output.txt`.
- `verify_exposure.py`, Section 7: the cycle law of the slotted queue from the cyclic lemma against a
  dynamic program on the workload and a simulation, the ratios of `prop:cycle`(a) and (b) up to
  n = 2^14, strict log-convexity of `f_C` (finite check), and the exposure law for the fresh, the
  random-time and the control-only start at N = 1000, 2000, 4000 against `cor:exposure-bulk`,
  `cor:exposure-tail` and `cor:exposure-mode`, with a simulation of the switching queue at N = 200.
  Output `data/verify_exposure_output.txt`.
- `verify_all.py`, runs the eight `verify` scripts, and with `--full` the two `certify` scripts
  first. Outputs `data/verify_all_output.txt` and `data/verify_all_output_full.txt`.
- Every output in `data/` starts with the sha256 of the script that wrote it and the date.
- `../lean/PaperF/`, the Lean 4 proofs of the identities of Section 2, the first part of
  `lem:counting` and the inversion of `thm:inverse`(a), with the map from labels to Lean names in
  `../lean/PaperF/MAP.md`. Lean 4.33.1 and Mathlib v4.33.1 (commit `0df444a360ea`). No module uses
  `sorry` or `native_decide`, and the axioms are `propext`, `Classical.choice` and `Quot.sound`.
- The earlier draft is in `../archive/paperF_golden_aging`, with its ledgers in its `data` folder.

## How to build and run

Build the journal version with `pdflatex problem131_levy.tex` and the arXiv version with
`pdflatex problem131_levy_arxiv.tex`, each run three times so that the references settle. Run the
checks from this folder with `py -I verify_all.py` (about three minutes) or `py -I verify_all.py --full`
(about five minutes). Each script can also be run alone with `py -I <script>`, and
`py -I certify_atlas.py 1200` writes the law at any other N to `data/atlas_N1200.json`. Redraw the
figure with `py -I figures/make_atlas_figure.py`. The scripts need numpy, scipy, mpmath and
python-flint, and the figure also matplotlib. The recorded runs used Python 3.14.3, numpy 2.4.2,
scipy 1.17.1, mpmath 1.3.0, python-flint 0.9.0 (FLINT 3.6.0) and matplotlib 3.10.8. The Lean
library builds with `lake exe cache get` and `lake build PaperF` in `../lean` (see
`../lean/PaperF/MAP.md` for the workspace outside OneDrive).

## Statement labels

The scripts, their outputs and the Lean map name statements by their TeX labels (`thm:bulk`,
`prop:final-run`, ...), never by number. The seven main theorems are lettered A to G (`thm:bulk`,
`thm:bigjump`, `thm:preparation`, `thm:aging`, `thm:mode`, `thm:antimode`, `thm:mode-count`). All
other statements are numbered within sections. Numbered constants (`C_3`, `c_2`, ...) are fixed once
and never reused, as Section 2.2 states. Hypotheses carry the names (RV), (LR), (SPAN), (LD), (LD2)
and (EQ) in the paper and in the scripts.

## Hypotheses and notation

(RV) regularly varying tails of index -alpha_sigma with 1 < alpha_sigma < 2; (LR) local regular
variation f_sigma(n) ~ alpha_sigma T_sigma(n)/n; (SPAN) span one; (LD) |f_sigma(n) - f_sigma(n+1)|
= O(f_sigma(n)/n), used in Sections 6.4, 6.5 and 7; (LD2) |f_sigma(n+1) - 2 f_sigma(n) + f_sigma(n-1)|
= O(f_sigma(n)/n^2) and (EQ) T_+(n)/T_-(n) bounded above and below, used in Section 6.5, Section 7
and Appendix B. mu_sigma mean run length, s = mu_+ + mu_-, p = mu_+/s. Scales b_{sigma,N} = a_sigma(N/s),
B_N the larger one, moving profile h_N. Renewal mass function u_sigma, boundary kernel
kappa_+^{(sigma_0)}. Big-jump kernel G_N. Directional defect D_N^sigma, with supremum Delta_{sigma,N}.
Aged initial run nu^{(t_a)} (`eq:aged-nu`), aged layer kappa^{(theta)}. In Section 7 the arrival
probability is lambda, the work per customer is Y, the work per slot is W, the cycle is C, the loads
are rho_+ and rho_-, and mu_+- = 1/(1 - rho_+-).
