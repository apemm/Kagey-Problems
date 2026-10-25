# Problem 131, Paper F: the occupation law of a lattice Lévy walk

Working title: "Bulk, big jumps and boundary layers in the occupation law of a lattice Lévy walk".
Target journal: Electronic Journal of Probability (class `ejpecp`, no page limit, proofs in the article).

The walk takes N steps in runs of alternating sign whose lengths are independent with regularly varying
tails of index between 1 and 2. A_N is the number of plus steps and P_N(k) its law. The paper
describes P_N at every point of the range {0,...,N}: a stable bulk at the scale B_N, a big-jump zone on
each side where one run is macroscopic, a renewal boundary layer at each end, and an atom at each
endpoint. The initial run (the first run) enters each zone through a sharp criterion. For the
occupation count of the lattice walk with 1 < alpha < 2 this answers the question of Wang, Schulz,
Deng and Barkai (2018) on the effect of the initial preparation on the rare fluctuations. Their
question also covers other observables and 0 < alpha < 1.
The shape follows, including the golden-ratio threshold for the global mode, an interior
minimum at the stable scale of the opposite runs, and the exact number of modes for all large N
(Theorem F), and the boundary layer identifies the law of the opposite run.

Started October 24, 2026 from the plan of October 23. The earlier draft in this folder, "The
golden-ratio threshold for a lattice Lévy walk and ties in coin-turning walks", is archived in
`../archive/paperF_golden_aging`. Its heavy-tail half is absorbed here (its center theorem is the
bulk theorem at the center point, its golden-ratio corollary is part of the mode theorem). Its aging
half (coin-turning ties at c = 1, the Pólya urn, the fair-start expansion) is to become a short
separate note. The infinite-mean case (0 < alpha < 1, the local Lamperti law) is left to a second
paper.

## Status

The draft is complete, with every statement proved in the article or stated as a conjecture (80
pages after the integration of the exact mode count on October 25, 2026, see
`research_notes/Paper F audits/20_mode_count_integration.md`. The earlier integrations are in
`16_novelty_repositioning.md` and `17_O1_O2_integration.md`).
The main results are six theorems, lettered A to F in the order of the sections, and the
identification from the ends is Remark 5.6. Statements are numbered by section, and the
scripts and the Lean map name them by their TeX labels, which do not change when statements move.
The label of Remark 5.6 stays `thm:inverse` for that reason (it was Proposition 7.1).

- Theorem A (`thm:bulk`, Section 3). For a fresh start, under (RV) and (SPAN),
  `sup_k |B_N P_N(k) - h_N((k-pN)/B_N)| -> 0` over the whole range of the count, `sup_k P_N(k) <= C/B_N`, and the
  ratio form on `|k-pN| <= K B_N`, for every relation between the two scales. Section 3 opens
  with what is new (the uniform error and bound over the whole range under (RV) alone) and why it
  needs work. The classical inputs (`lem:stable`, `lem:kernels`, `lem:small`, the proofs of
  `lem:rv` and `lem:profile`) are in Appendix A (`sec_appendix.tex`).
- Theorem B (`thm:bigjump`, Section 4). The boundary layer `P_N(N-j)/T_+(N) -> kappa(j)` under (RV),
  and under (LR) for the plus sign the big-jump kernel `G_N` of `eq:G` on
  `pN + K lambda_N B_N <= k <= N` in the double limit, with a uniform boundary layer. The proof
  splits by the largest run (`lem:no-giant`, `lem:two-giant`, `lem:one-giant`). The infinite
  density (`cor:infinite-density`), the lower bound without `lambda_N` (`cor:bigjump-lower`), the
  need for the double limit (`rem:no-single-formula`) and for (LR) (`ex:rv-not-lr`).
- Theorem 4.13 (`thm:window`, Section 4.5). When `b_{+,N} <= b_{-,N}`: a two-sided bound
  `max{(1-eps)G_N, e^{-(1+eps)I_N(x)}/B_N} <= P_N <= (1+eps)G_N + e^{-(1-eps)I_N(x)}/B_N` on
  `K <= x <= X_N`, with `I_N` the Cramer cost of a shortfall `xB_N/p` of the minus runs
  (`lem:laplace`, `lem:tilt`), and, when `theta_{+,N} -> 0`, the zone of Theorem B(b) starts at
  `(1+delta) xi_N B_N` and not at `(1-delta) xi_N B_N`, with `xi_N = o(lambda_N)`. The strip
  `(1 +- delta) xi_N` is open, and the composite relative-error form is `rem:window-conj`. The
  theorem assumes a fresh start. For sums the same crossover is due to Rozovskii (1997, Corollary 2A,
  tail, with a representation uniform in x > 0) and Denisov, Dieker and Shneer (2008, Section 9.2,
  local), and both are cited. What is new is the count at a fixed time with the run in progress.
- Theorem C (`thm:preparation`, Section 5). Every law of the initial run: the exact defect in the bulk, the
  bulk criterion `B_n P(D=n) -> 0`, the big-jump zone with the term `Psi_N` and its removal exactly
  when `nu_+(n) = o(T_+(n))` (part (c)), the boundary layer with the prepared kernel (part (d)),
  and the interior of the big-jump zone with the window condition `W_n` and the explicit target
  `eq:interior-target` (part (e)). The stationary start in
  closed form (`cor:stationary`), no universal trim (`cor:no-trim`), regularly varying
  initial runs (the paragraph after `cor:stationary`). The tightness of the count `lem:prep-tight`
  and the uniform big-jump bound `eq:unif-bigjump` are the tools of Section 5.
- Theorem D (`thm:mode`, Section 6). The global mode is an endpoint or a bulk point according to
  `B_N Q_sigma(N)/H_N`, with the golden-ratio threshold for the stationary start and the constant
  `C(phi) = 0.7761317...` at `alpha = phi`.
- Theorem 6.1 (`thm:second-order`) and Theorem E (`thm:antimode`, Section 6). The exact
  second-order coefficient `C(j)` of the boundary layer, at fixed `j` in part (a) and uniformly on
  `1 <= j <= N^(1-eta)` in part (b), and the interior minimum near the plus end
  at `T_-(j*_N) ~ 2 alpha_+ s/N` when `u_- > 1/mu_-`, asymptotic to the minimizer of
  `u_-(j) + C(j)/N`, and at bounded distance otherwise.
- Section 6.4 (`sec:extrema`). The difference renewal theorem `u_-(j) - u_-(j-1) ~ -T_-(j)/mu_-^2`
  (`lem:diff-renewal`, by Wiener's lemma), the prepared profile (`lem:prep-diff`), the copies of the
  end profile (`prop:copy`), at least `M_+ + M_- + 1` modes (`thm:modes-lower`), a prepared
  log-convex start with at least four modes (`cor:four-modes`), the first differences in the layer
  under (LD) (`lem:plus-diff`, `thm:first-diff`), and the extrema up to distance `N^(1-eta)`
  (`thm:ends`).
- Theorem F (`thm:mode-count`, Section 6.5). Under (SPAN), (LR), (LD2) for both signs and (EQ),
  for a fresh or fair start with no ties, the full sign pattern of the first differences is fixed
  for all large N and P_N has exactly `M_+ + M_- + 1` modes. Three modes for all large N if and
  only if each end profile has one local maximum (`cor:three-modes`). When a profile has one
  local maximum is said in terms of `u_-` in `lem:one-max`. Monotonicity of `u_-` is sufficient,
  and it is necessary only at an end whose profile starts above `u_-(1)`. Log-convex run laws give
  three modes (`cor:logconvex-three`). (EQ) may be replaced by `min theta_N >= theta_0` along a
  sequence (`cor:sequences`). Laws with `f(1) = 0` give at least five modes for the fair start, and
  the law `f(n) ∝ n^{-5/2}` on n >= 2 with the fair start gives at least 15 (`ex:runs2`). The 15 is
  specific to that law and start. The index 7/5 law on n >= 2 gives 13 modes (N = 3000, 4000), and a
  fresh start with the index 3/2 law has the lower bound 14. The difference form of the local
  big jump, uniform in the number of runs (`lem:diff-bigjump`), is stated in Section 6.5 as a
  result of its own. Open: unequal scales and a bound for every N (`rem:mode-open`).
- Appendix B (`app:modes`). The proofs for Theorem F: `lem:ld2`, `lem:second-renewal`,
  `lem:plus-second`, `thm:layer-second` and `cor:convex` (one antimode), `lem:trunc-local`,
  `lem:fourier-diff` and the proof of `lem:diff-bigjump`, `thm:zone-diff` (the big-jump zone),
  `lem:pointwise`, `lem:second-bigjump`, `lem:tails`, `lem:bell` (Kwasnicki's bell shape and
  analyticity), `thm:bulk-diff` and `cor:bulk-sign` (the bulk), and the junctions.
- Remark 5.6 (`thm:inverse`, also labelled `rem:thinning`, Section 5.7). For a fresh plus start the atoms give the plus law
  directly (`P_N(N) = T_+(N)`), the plus-end layer gives the minus law through the renewal
  inversion, and the ratios at the minus end determine the plus law only up to a geometric
  thinning (`rem:thinning`). Part (b) assumes only `Q_+(N)/T_+(N) -> q`.
- The exact identities of Section 2 (`prop:fresh-identity`, `prop:first-run`, `lem:green`,
  `prop:final-run` with its explicit form `eq:final-explicit`, `lem:counting`) hold for every `N`
  with no hypothesis. The facts on regular variation are collected in `lem:rv`.

Section 7 (`sec_verify.tex`, label `sec:verify`) is a short account of the computations. It states
the run recursion `eq:run-recursion` and the run form `eq:run-sum` of the final-run identity, which
the scripts and the Lean library use, and points to this folder for the rest. Table 1
(`tab:antimode`) is now at the end of Section 6. No proof uses a computed number. The pass of
October 25 removed `sec_inverse.tex` (its content is Remark 5.6) and replaced the proof of
`lem:local-bigjump` by a citation of Denisov, Dieker and Shneer (2008, Theorem 9.1).

The editing pass of October 24 removed the labels `lem:final-explicit` (now `prop:final-run`,
display `eq:final-explicit`), `eq:AB-recursion` (now `eq:run-recursion` in Section 8),
`prop:uniform-second` (now `thm:second-order`(b)), `lem:unif-bigjump` (now the display
`eq:unif-bigjump`), `lem:end-crude`, `rem:inverse-scope` and `rem:rho-diagram`. Outputs in `data/`
dated before the pass may still print the old names.

## Files

- `problem131_levy.tex`, the main file (class `ejpecp`, in TeX Live), with the section files
  `sec_intro`, `sec_setting` (2), `sec_bulk` (3), `sec_bigjump` (4), `sec_preparation` (5),
  `sec_shape` (6), `sec_verify` (7) and `sec_appendix` (Appendix A). The PDF
  is `problem131_levy.pdf`.
- `figures/atlas.pdf` (and `.png`), Figure 1, made by `figures/make_atlas_figure.py` from
  `data/atlas_N5000.json` and `data/antimode.json` in the shared style `../figures/series_style.py`.
  The caption source is `figures/captions.md`. The script also writes `data/atlas_pieces.json`, the
  zones of panel (a) and the largest relative error of each piece in its zone.
- `certify_atlas.py`, the exact law `P_N` by the recursion `eq:run-recursion` and the final-run
  identity `prop:final-run` in double precision,
  with the a priori relative error bound `eps_N = (1 + gamma_{N+2})^{N+2} - 1` and a comparison
  with the same recursion in 128-bit ball arithmetic at N = 600. Output `data/atlas_N5000.json`.
  The other scripts import its functions (law, recursion, renewal function, `C(j)`).
- `certify_antimode.py`, the certified antimodes at N = 600, 1200, 2400, 4000, 8000 (the value at every
  other point of `[pN, N]` above the minimum by more than `2 eps_N`) and the two predictions of
  `thm:antimode` for the figure. Output `data/antimode.json`.
- `verify_identities.py`, the identities of Section 2, `eq:kappa`, `prop:final-run` in both forms
  (`eq:final-explicit`, and `eq:run-sum` with `eq:run-recursion`), the
  renewal identities `eq:cover`, `eq:cover-v`, `eq:conv-v`, the two forms of `eq:Cj` and the inversion
  of `thm:inverse`(a), by brute force in exact rational arithmetic for N <= 12, with two pairs of
  run laws and a general initial run. Output `data/verify_identities_output.txt`.
- `verify_coefficient.py`, `C(j)` of `thm:second-order` against the exact law at N = 1200, 2400,
  4800 (the table of Section 8.2 of the plan review of October 23), the two forms of
  `prop:final-run` at N = 1200, Table 1 (`tab:antimode`, Section 6) against the certificates, the ratios after `eq:second-renewal`, the constant of `thm:mode`(d) and the
  certificate `data/atlas_N5000.json`. Output `data/verify_coefficient_output.txt`.
- `verify_preparation.py`, `thm:preparation`(c), (d) and `cor:stationary` for the fresh, the
  stationary and one regularly varying initial run at N = 1200 and 2400, and the stationary kernel
  `(2/s)(1 + mu_+ u_-(j))`. Outputs `data/verify_preparation_output.txt` and
  `data/preparation_ratios.json`.
- `verify_bigjump.py`, the numbers of `rem:no-single-formula`. Output
  `data/verify_bigjump_output.txt`.
- `verify_modes.py`, the numbers of Section 6.4 quoted in Section 7: the ratio of
  `lem:diff-renewal`, the error of `thm:first-diff` at N = 1000 and 3000, the certified modes of
  the fair start (N = 400, 1000) and of the start of `cor:four-modes` (N = 1000). Output
  `data/verify_modes_output.txt`.
- `verify_mode_count.py`, the numbers of Section 6.5 quoted there and in Section 7: three modes for
  the zeta law at N = 2500, ..., 4000 (fresh plus and fair), the renewal mass function and the 15
  modes of the fair start for the law `f(n) ∝ n^{-5/2}` on n >= 2 at every N = 2500, 2600, ..., 4000 (and 17,
  19, 17 at N = 1000, 1500, 2000), and the law with f(1) = 0.6, f(2) = 0.3 (three modes for the fair
  start, four for the fresh plus start). Every sign is certified against the rounding bound.
  Output `data/verify_mode_count_output.txt`.
- `verify_all.py`, runs the six `verify` scripts, and with `--full` the two `certify` scripts
  first. Outputs `data/verify_all_output.txt` and `data/verify_all_output_full.txt`.
- Every output in `data/` starts with the sha256 of the script that wrote it and the date.
- `../lean/PaperF/`, the Lean 4 proofs of the identities of Section 2, the first part of
  `lem:counting` and the inversion of `thm:inverse`(a), with the map from labels to Lean names in
  `../lean/PaperF/MAP.md`. Lean 4.33.1 and Mathlib v4.33.1 (commit `0df444a360ea`). No module uses
  `sorry` or `native_decide`, and the axioms are `propext`, `Classical.choice` and `Quot.sound`.
- The earlier draft is in `../archive/paperF_golden_aging`, with its ledgers `ledger_D3.md` and
  `ledger_D4.md` in its `data` folder.

## How to build and run

Build the paper with `pdflatex problem131_levy.tex`, run three times so that the references settle.
Run the checks from this folder with `py -I verify_all.py` (about a minute and a half) or
`py -I verify_all.py --full` (about three minutes, most of it the antimode at N = 8000 and the mode
counts). Each script
can also be run alone with `py -I <script>`, and `py -I certify_atlas.py 1200` writes the law at any
other N to `data/atlas_N1200.json`. Redraw the figure with `py -I figures/make_atlas_figure.py`. The
scripts need numpy, scipy, mpmath and python-flint, and the figure also matplotlib. The recorded
runs used Python 3.14.3, numpy 2.4.2, scipy 1.17.1, mpmath 1.3.0, python-flint 0.9.0 (FLINT
3.6.0) and matplotlib 3.10.8. The Lean library builds with `lake exe cache get` and
`lake build PaperF` in `../lean` (see `../lean/PaperF/MAP.md` for the workspace outside OneDrive).

## Statement labels

The scripts, their outputs and the Lean map name statements by their TeX labels (`thm:bulk`,
`prop:final-run`, ...), never by number. The six main theorems are lettered A to F
(`thm:bulk`, `thm:bigjump`, `thm:preparation`, `thm:mode`, `thm:antimode`). All other
statements are numbered within sections, so `prop:final-run` is Proposition 2.6,
`thm:second-order` is Theorem 6.1, `thm:inverse` is Remark 5.6, `lem:stable` is Lemma A.1
and `tab:antimode` is Table 1 in the build of October 25, 2026. Numbered constants (`C_3`, `c_2`,
...) are fixed once and never reused, as Section 2.2 states. Hypotheses carry the names (RV), (LR), (SPAN), (LD), (LD2) and (EQ) in the paper and
in the scripts.

## Hypotheses and notation

(RV) regularly varying tails of index -alpha_sigma with 1 < alpha_sigma < 2; (LR) local regular
variation f_sigma(n) ~ alpha_sigma T_sigma(n)/n; (SPAN) span one; (LD) |f_sigma(n) - f_sigma(n+1)|
= O(f_sigma(n)/n), used only in Sections 6.4 and 6.5; (LD2) |f_sigma(n+1) - 2 f_sigma(n) + f_sigma(n-1)|
= O(f_sigma(n)/n^2) and (EQ) T_+(n)/T_-(n) bounded above and below, used only in Section 6.5 and
Appendix B. mu_sigma mean run length,
s = mu_+ + mu_-, p = mu_+/s. Scales b_{sigma,N} = a_sigma(N/s), B_N the larger one, moving
profile h_N. Renewal mass function u_sigma, v_sigma = sum_m m f_sigma^{*m}, boundary kernel
kappa_+^{(sigma_0)}. Big-jump kernel G_N. Directional defect D_N^sigma (\mathcal D^\sigma_N), with supremum Delta_{sigma,N}.
