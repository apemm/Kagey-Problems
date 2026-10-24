# Problem 131, Paper F: the occupation law of a lattice Lévy walk

Working title: "Bulk, big jumps and boundary layers in the occupation law of a lattice Lévy walk".
Target journal: Electronic Journal of Probability (class `ejpecp`, no page limit, proofs in the article).

The walk takes N steps in runs of alternating sign whose lengths are independent with regularly varying
tails of index between 1 and 2. A_N is the number of plus steps and P_N(k) its law. The paper
describes P_N bin by bin over the whole row: a stable bulk at the scale B_N, a big-jump zone on
each side where one run is macroscopic, a renewal boundary layer at each end, and an atom at each
endpoint. The preparation (the law of the first run) enters each zone through a sharp criterion.
The shape follows, including the golden-ratio threshold for the global mode and an interior
minimum at the stable scale of the opposite runs, and the boundary layer identifies the law of the
opposite run.

Started October 24, 2026 from the plan of October 23. The earlier draft in this folder, "The
golden-ratio threshold for a lattice Lévy walk and ties in coin-turning walks", is archived in
`../archive/paperF_golden_aging`. Its heavy-tail half is absorbed here (its center theorem is the
bulk theorem at the center bin, its golden-ratio corollary is part of the mode theorem). Its aging
half (coin-turning ties at c = 1, the Pólya urn, the fair-start expansion) is to become a short
separate note. The infinite-mean case (0 < alpha < 1, the local Lamperti law) is left to a second
paper.

## Status

The draft is complete, with every statement proved in the article (October 24, 2026, 53 pages
after the editing pass). The
introduction states six theorems, lettered A to F in the order of the sections. Statements are
numbered by section, and the scripts and the Lean map name them by their TeX labels, which do not
change when statements move.

- Theorem A (`thm:bulk`, Section 3). For a fresh start, under (RV) and (SPAN),
  `sup_k |B_N P_N(k) - h_N((k-pN)/B_N)| -> 0` over the whole row, `sup_k P_N(k) <= C/B_N`, and the
  ratio form on `|k-pN| <= K B_N`, for every relation between the two scales.
- Theorem B (`thm:bigjump`, Section 4). The boundary layer `P_N(N-j)/T_+(N) -> kappa(j)` under (RV),
  and under (LR) for the plus sign the big-jump kernel `G_N` of `eq:G` on
  `pN + K lambda_N B_N <= k <= N` in the double limit, with a uniform boundary layer. The proof
  splits by the largest run (`lem:no-giant`, `lem:two-giant`, `lem:one-giant`). The infinite
  density (`cor:infinite-density`), the lower bound without `lambda_N` (`cor:bigjump-lower`), the
  need for the double limit (`rem:no-single-formula`) and for (LR) (`ex:rv-not-lr`).
- Theorem C (`thm:preparation`, Section 5). Every preparation: the exact defect in the bulk, the
  bulk criterion `B_n P(D=n) -> 0`, the big-jump zone with the term `Psi_N` and its removal exactly
  when `nu_+(n) = o(T_+(n))`, the boundary layer with the prepared kernel. The stationary start in
  closed form (`cor:stationary`), no universal trim (`cor:no-trim`), regularly varying
  preparations (the paragraph after `cor:stationary`). The tightness of the count `lem:prep-tight`
  and the uniform big-jump bound `eq:unif-bigjump` are the tools of Section 5.
- Theorem D (`thm:mode`, Section 6). The global mode is an endpoint or a bulk bin according to
  `B_N Q_sigma(N)/H_N`, with the golden-ratio threshold for the stationary start and the constant
  `C(phi) = 0.7761317...` at `alpha = phi`.
- Theorem 6.1 (`thm:second-order`) and Theorem E (`thm:antimode`, Section 6). The exact
  second-order coefficient `C(j)` of the boundary layer, at fixed `j` in part (a) and uniformly on
  `1 <= j <= N^(1-eta)` in part (b), and the interior minimum near the plus end
  at `T_-(j*_N) ~ 2 alpha_+ s/N` when `u_- > 1/mu_-`, asymptotic to the minimizer of
  `u_-(j) + C(j)/N`, and at bounded distance otherwise.
- Theorem F (`thm:inverse`, Section 7). The boundary layers identify both run laws through the
  renewal inversion, and the minus end needs the normalization by `T_-(N)` (`rem:thinning`).
- The exact identities of Section 2 (`prop:fresh-identity`, `prop:first-run`, `lem:green`,
  `prop:final-run` with its explicit form `eq:final-explicit`, `lem:counting`) hold for every `N`
  with no hypothesis. The facts on regular variation are collected in `lem:rv`.

Section 8 (`sec_verify.tex`) describes the computations and the Lean library. It states the run
recursion `eq:run-recursion` and the run form `eq:run-sum` of the final-run identity, which the
scripts and the Lean library use, and holds Table 1 (`tab:antimode`). No proof uses a computed
number.

The editing pass of October 24 removed the labels `lem:final-explicit` (now `prop:final-run`,
display `eq:final-explicit`), `eq:AB-recursion` (now `eq:run-recursion` in Section 8),
`prop:uniform-second` (now `thm:second-order`(b)), `lem:unif-bigjump` (now the display
`eq:unif-bigjump`), `lem:end-crude`, `rem:inverse-scope` and `rem:rho-diagram`. Outputs in `data/`
dated before the pass may still print the old names.

## Files

- `problem131_levy.tex`, the main file (class `ejpecp`, in TeX Live), with the section files
  `sec_intro`, `sec_setting` (2), `sec_bulk` (3), `sec_bigjump` (4), `sec_preparation` (5),
  `sec_shape` (6), `sec_inverse` (7) and `sec_verify` (8). The PDF is `problem131_levy.pdf`.
- `figures/atlas.pdf` (and `.png`), Figure 1, made by `figures/make_atlas_figure.py` from
  `data/atlas_N5000.json` and `data/antimode.json` in the shared style `../figures/series_style.py`.
  The caption source is `figures/captions.md`. The script also writes `data/atlas_pieces.json`, the
  zones of panel (a) and the largest relative error of each piece in its zone.
- `certify_atlas.py`, the exact law `P_N` by the recursion `eq:run-recursion` and the final-run
  identity `prop:final-run` in double precision,
  with the a priori relative error bound `eps_N = (1 + gamma_{N+2})^{N+2} - 1` and a comparison
  with the same recursion in 128-bit ball arithmetic at N = 600. Output `data/atlas_N5000.json`.
  The other scripts import its functions (law, recursion, renewal function, `C(j)`).
- `certify_antimode.py`, the certified antimodes at N = 600, 1200, 2400, 4000, 8000 (every other
  bin of `[pN, N]` above the minimum by more than `2 eps_N`) and the two predictions of
  `thm:antimode` for the figure. Output `data/antimode.json`.
- `verify_identities.py`, the identities of Section 2, `eq:kappa`, `prop:final-run` in both forms
  (`eq:final-explicit`, and `eq:run-sum` with `eq:run-recursion`), the
  renewal identities `eq:cover`, `eq:cover-v`, `eq:conv-v`, the two forms of `eq:Cj` and the inversion
  of `thm:inverse`(a), by brute force in exact rational arithmetic for N <= 12, with two pairs of
  run laws and a general preparation. Output `data/verify_identities_output.txt`.
- `verify_coefficient.py`, `C(j)` of `thm:second-order` against the exact law at N = 1200, 2400,
  4800 (the table of Section 8.2 of the plan review of October 23), the two forms of
  `prop:final-run` at N = 1200, Table 1 (`tab:antimode`, Section 8) against the certificates, the ratios after `eq:second-renewal`, the constant of `thm:mode`(d) and the
  certificate `data/atlas_N5000.json`. Output `data/verify_coefficient_output.txt`.
- `verify_preparation.py`, `thm:preparation`(c), (d) and `cor:stationary` for the fresh, the
  stationary and one regularly varying preparation at N = 1200 and 2400, and the stationary kernel
  `(2/s)(1 + mu_+ u_-(j))`. Outputs `data/verify_preparation_output.txt` and
  `data/preparation_ratios.json`.
- `verify_bigjump.py`, the numbers of `rem:no-single-formula`. Output
  `data/verify_bigjump_output.txt`.
- `verify_all.py`, runs the four `verify` scripts, and with `--full` the two `certify` scripts
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
Run the checks from this folder with `py -I verify_all.py` (about half a minute) or
`py -I verify_all.py --full` (about two minutes, most of it the antimode at N = 8000). Each script
can also be run alone with `py -I <script>`, and `py -I certify_atlas.py 1200` writes the law at any
other N to `data/atlas_N1200.json`. Redraw the figure with `py -I figures/make_atlas_figure.py`. The
scripts need numpy, scipy, mpmath and python-flint, and the figure also matplotlib. The recorded
runs used Python 3.14.3, numpy 2.4.2, scipy 1.17.1, mpmath 1.3.0, python-flint 0.9.0 (FLINT
3.6.0) and matplotlib 3.10.8. The Lean library builds with `lake exe cache get` and
`lake build PaperF` in `../lean` (see `../lean/PaperF/MAP.md` for the workspace outside OneDrive).

## Statement labels

The scripts, their outputs and the Lean map name statements by their TeX labels (`thm:bulk`,
`prop:final-run`, ...), never by number. The theorems of the introduction are lettered A to F
(`thm:bulk`, `thm:bigjump`, `thm:preparation`, `thm:mode`, `thm:antimode`, `thm:inverse`). All other
statements are numbered within sections, so `prop:final-run` is Proposition 2.6,
`thm:second-order` is Theorem 6.1, `cor:stationary` is Corollary 5.4 and `tab:antimode` is Table 1
in the build of October 24, 2026. Hypotheses carry the names (RV), (LR) and (SPAN) in the paper and
in the scripts.

## Hypotheses and notation

(RV) regularly varying tails of index -alpha_sigma with 1 < alpha_sigma < 2; (LR) local regular
variation f_sigma(n) ~ alpha_sigma T_sigma(n)/n; (SPAN) span one. mu_sigma mean run length,
s = mu_+ + mu_-, p = mu_+/s. Scales b_{sigma,N} = a_sigma(N/s), B_N the larger one, moving
profile h_N. Renewal mass function u_sigma, v_sigma = sum_m m f_sigma^{*m}, boundary kernel
kappa_+^{(sigma_0)}. Big-jump kernel G_N. Directional defect D_N^sigma (\mathcal D^\sigma_N), with supremum Delta_{sigma,N}.
