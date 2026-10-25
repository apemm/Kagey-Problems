# Problem 131: Galton board with persistence

A ball goes left or right with probability 1/2 at the first peg and after that repeats its previous
direction with probability p. Kagey asks for the distribution of the bins, the lattice-path meaning of
his numerator tables, when the middle bin is as likely as the endpoints, the normal limit, and what
changes on a cylinder or a tetrahedron.

Status. There are seven papers by A. Pemmasani, which call each other Papers A, B, C1, C2, D, E
and F, and four working notes, S1 to S4. Paper A (arXiv:2610.06935) solves the binary problem at
every N, and Paper B (arXiv:2610.09258) treats d directions on the complete graph. Papers C1, C2,
D, E and F are in preparation. In October 2026 Paper B was merged into Paper C. Paper B v1
remains available as the versioned arXiv record, and its folder `archive/paperB` keeps it
unchanged. On October 24, 2026 Paper C was split in two. Paper C1 (the forward theory of slowly
switching chains, in `paperC`) keeps the folder and the results of Paper B, and Paper C2 (what the
occupation law determines about the generator, in `paperC2`) holds the identifiability half. The
earlier EJP version of Paper C is in `archive/paperC_switching_ejp`. Paper C and Paper E (the
planar walk, in `paperE`) were one paper until October 13, 2026, and so were Paper D (the elephant
walk, in `paperD`) and the first draft of Paper F (heavy-tailed runs and aging walks). On October
24, 2026 that draft was archived in `archive/paperF_golden_aging`, its aging half became the note
`S4_aging_note`, and Paper F was started again in `paperF` as a paper on the occupation law of a
lattice Lévy walk. The titles of Papers C1 to F are working titles, and Paper A cites C and D
under their old titles. The papers share the notation N, L = log N, T, z_N, lambda_F and K_F.
`PUBLICATION.md` has notes on where to send them.

Conventions. N is the number of bounces, so Kagey's row n has N = n-1. For p = a/(a+b) his numerator
is 2(a+b)^(N-1) P_N(k). Write u = (1-p)/p for the switching odds, T = N(1-p) for the switching scale
and z_N = N(1-p_N) for the value of T at the central crossing p_N.

## Paper A: Uniform Bessel bounds for magnetization crossings in finite Ising chains

Paper A (arXiv:2610.06935) treats the walk with 2 states, which is the zero-field 1D Ising chain
with free boundaries.
It gives the exact law and explicit uniform Bessel bounds for every bin, with relative error at most
N u^2/2 + u at every N. At the center these bracket the crossing p_N for every N >= 2. With
zeta_N = W_0(pi N^2/4)/2, the value z_N lies below zeta_N + 1/(8 zeta_N) and within
zeta_N(zeta_N + 1)/N + 1/(16 zeta_N^2) of it. The proof is analytic for N >= 175 and uses exact
integer certificates below that, and all of it is checked in Lean. This gives the crossing equation
z_N + (1/2) log z_N = L + c_0 + 1/(8 z_N) + R_N with c_0 = (1/2) log(pi/8) and
|R_N| <= 1/(4L^2) + (L^2 + L)/N. The paper also expands the crossing of every other bin, with a
Laguerre law for fixed bins, and compares free and periodic boundaries. It also gives the normal
limit and reads Kagey's numerator tables as weighted counts of words. The uniform local law for
every q <= 1/2 is in `paperA/llt_note` (the start of a separate paper), and the bijections of the
p = 2/3 and p = 1/3 tables with OEIS A035002 and A348595 are in `paperA/tables_note`.

Files. The folder `paperA`, with `problem131.tex` and `problem131.pdf`, the sections
`sec_exact.tex`, `sec_crossing.tex`, `allbin_thresholds.tex` and `periodic_window.tex`, the
appendix `app_every_n.tex`, the check scripts, `paperA/README.md`, and the notes `llt_note` and
`tables_note`.

## Historical Paper B

Paper B, "Vertex crossings in a symmetric Markov multinomial model", is now incorporated
into Paper C1. Its original source, PDF, data and verification scripts are preserved in
[`archive/paperB`](archive/paperB/README.md). The earlier preprint remains available as
[arXiv:2610.09258v1](https://arxiv.org/abs/2610.09258v1). Paper C1 reproves its results on the
crossings with a vertex and near a vertex as cases of the general theory, and C1 is intended to
replace it under the same arXiv identifier. The Bessel majorant and boundary crossover that were
not carried into C1 remain in this historical version.

## Paper C1: Occupation counts of rarely switching Markov chains

Full title "Occupation counts of rarely switching Markov chains: stratified local laws, crossings
and the boundary layer". Paper C1 (in preparation, for the Journal of Theoretical Probability) is
the forward theory for a chain on d states with transition matrix P = I + (T/N)Q, run for N steps
with T = tau L. The counts of the N visits play the role of the bin. Every rate on a face is the
restriction of the Donsker and Varadhan functional of the whole chain. To first order the mode
sits on a face F that minimizes tau lambda_F + |F| - 1, where lambda_F is the exit rate of F, for
every start. For a strongly connected face with start mass we prove a stratified local law with an
explicit constant K_F, face maxima with a field, a crossing equation for 2 such faces and the tie
windows. The boundary layer at a facet is proved for every face with at least 2 states. The
complete graph, the Potts chain, is the main example, and there every face ties at first order,
each balanced crossing is unique at every N, the mode changes exactly once, and a start law or a
weak field can let an intermediate face win. Near a vertex the crossing is given by a product of
Laguerre polynomials. The two-state walk of Paper A is the simplest case. The application to
sticky priors for hidden Markov models moved to the note `S3_sticky_note`.

Files. The folder `paperC`, with the main file `problem131_chains.tex` and `problem131_chains.pdf`
(article class, 70 pages), the same paper in the Springer Nature template
`problem131_chains_sn.tex` and `problem131_chains_sn.pdf` (77 pages, `paperC/TEMPLATE.md` says how
it was set up and built), their shared section and appendix files, the check scripts,
`paperC/EXPORTS.md` (the statements that Paper C2 cites, with their numbers) and
`paperC/README.md`. The earlier main file `problem131_switching.tex` (class `ejpecp`), its PDF and
its supplement are in `archive/paperC_switching_ejp/`.

## Paper C2: What the occupation law of a finite Markov chain determines

Full title "What the occupation law of a finite Markov chain determines: principal minors, modal
supports and cycle trees". Paper C2 (in preparation, for Stochastic Processes and their
Applications) asks what coarse functionals of the law of C1 determine about Q. The Donsker and
Varadhan functional determines exactly the principal minors of -Q, and the generators with the
same minors form a finite set, which is {Q, Q*} without a cut and for d <= 3. From the stationary
start Q and its time reversal give the same law, while the second-order amplitudes separate them
for a generic start. The controlled boundaries of the modal supports determine the same minors.
A reversible design fixed in advance recovers Q, also at a finite horizon uniformly over a compact
class. At low temperature the calibrated rewards read off the cycle tree. Section 2 states the
results of C1 that the paper uses, each with its C1 number.

Files. The folder `paperC2`, with the main file `problem131_reconstruction.tex` and
`problem131_reconstruction.pdf` (class `elsarticle`, 40 pages), its section files, the check
scripts, the cover letter and `paperC2/README.md`.

## Paper D: Endpoint crossings for the elephant random walk

Paper D (in preparation) asks what memory changes. In the elephant random walk each step copies a uniformly chosen
earlier step and flips it with probability eps. The crossing x_N = N eps_N is unique and
x_N = 2 z_N - log(2 pi) + o(1), about twice the Markov value. The law at the crossing has 2 humps,
one near each end, and for large N it is strictly convex between them. On October 24, 2026 the
family proofs and the second-difference proofs came back from the Online Resource into the
article as Appendices D and E, so every proof used by the main theorems is in the article.

Files. The folder `paperD`, with `problem131_memory.tex` and `problem131_memory.pdf`, its section
and appendix files, the check scripts and `paperD/README.md`.

## Paper E: Endpoint crossings for the planar persistent walk

Paper E (in preparation) treats the planar persistent walk, which is Kagey's board in 2 dimensions.
Its corner and origin cross exactly
once, at T/L -> min(2/(2r+s), 1/s), and the paper finds the crossing to second order when reversals
dominate and when turns dominate. On one curve of rates the walk is exactly 2 independent copies of
Paper A's walk.

Files. The folder `paperE`, with `problem131_planar.tex` and `problem131_planar.pdf`, its section and
appendix files, the check scripts and `paperE/README.md`.

## Paper F: Bulk, big jumps and boundary layers in the occupation law of a lattice Lévy walk

Paper F (in preparation, for the Electronic Journal of Probability) was started on October 24,
2026. A lattice Lévy walk moves in runs of alternating direction whose lengths are independent with
regularly varying tails of index between 1 and 2. The paper describes the law of the number of
right steps after N steps bin by bin over the whole row. It has a stable bulk, a big-jump zone on
each side where one run is macroscopic, a renewal boundary layer at each end and an atom at each
endpoint. The law of the first run enters each piece through a sharp criterion. The global mode is
an endpoint or a bulk bin, and for the equilibrated start the threshold is the golden ratio. The
boundary layers identify both run laws. The draft is complete, with every statement proved in the
article (55 pages after the revision of October 24, 2026).

The first draft of Paper F, "The golden-ratio threshold for a lattice Lévy walk and ties in
coin-turning walks", is archived in `archive/paperF_golden_aging`. Its heavy-tail half is part of
the new paper: its center theorem is the bulk theorem at the center bin, and its golden-ratio
corollary is part of the theorem on the mode. Its aging half is the note `S4_aging_note`. The
infinite-mean case 0 < alpha < 1 is left to a later paper.

Files. The folder `paperF`, with `problem131_levy.tex` and `problem131_levy.pdf` (class `ejpecp`,
55 pages), its section files, the figure and its script in `figures/`, the recorded output of the
computations in `data/`, the check scripts and `paperF/README.md`.

## Earlier work

The exact law, the normal limit, interior log-concavity, the Bessel scaling at a fixed scale and the
periodic endpoint/center comparison are all in earlier papers (Renshaw and Henderson 1981, Dekking
and Kong 2011, Stepanyan et al. 2024 and others). Our results give uniform error control when p and
the bin vary with N. `literature_review.md` says what each source covers, and each paper has its own
section on related work.

## Shared files

Each paper has its own folder, `paperA` to `paperF` and `paperC2` (Paper B in `archive/paperB`), with its source
and PDF, its figures, its check scripts and runner, their recorded output and ledgers in `data/`,
and a `README.md`. Papers B, C and D also keep the proofs cut while shortening them in
`removed_proofs/`, for reference. The files below are shared.

- `SUPPLEMENT.md` is the one verification supplement for the papers. It lists each result that
  rests on computation with the script that checks it.
- `verify_all.py` runs the checks with `--paper a`, `b`, `c`, `c2`, `d`, `e`, `f`, `s4` or `all`
  (the default). It calls `paperA/verify_all.py` to `paperF/verify_all.py`, each in its own folder,
  with `c` for Paper C1 in `paperC` and `c2` for Paper C2 in `paperC2`, and says so in one line
  when a runner is missing. With `s4` it runs the 2 check scripts of the note `S4_aging_note`.
- `figures/` holds the variants of the program figure (`program_A` to `program_F`), made by
  `figures/make_program_figure.py`, with the captions in `figures/program_captions.md`. The current
  drafts of Papers C to F do not include their variants. The variants A and B are the ones posted
  with those papers and carry the labels of the series as it stood then.
- `S1_endpoint_information_note/` is a working note on the Fisher information in the endpoint, which was Section 8 and Appendix E of an earlier version of Paper C.
- `S3_sticky_note/` is a working note on sticky priors for hidden Markov models, which was Section 6 and Appendix D of Paper C until the merge with Paper B in October 2026.
- `S2_counts_note/` is a working note on which rate matrices the visit counts of a slowly switching chain can tell apart, with its 4 check scripts.
- `S4_aging_note/` is a short note, "When the end ties the center in a coin-turning walk", on the walk that switches at step k with probability c/k and its version with d states. Every interior bin ties with the end exactly at c = 1 for every N, and the chain that redraws or repeats its state has the law of Pólya's urn. It was the aging half of the first draft of Paper F until October 24, 2026, and it has 2 check scripts.
- `archive/` holds Paper B v1 (`archive/paperB`), the earlier EJP version of Paper C, "Face selection for slowly switching Markov chains", with its supplement (`archive/paperC_switching_ejp`), and the first draft of Paper F, "The golden-ratio threshold for a lattice Lévy walk and ties in coin-turning walks" (`archive/paperF_golden_aging`), each kept as it was and with its own `README.md`.
- `animations/` shows a Galton board with persistence at 4 values of p (`galton.gif`, `galton.mp4`),
  made by `animations/animate.py`.
- `lean/` holds the Lean 4 proofs, one library per paper (not the large-argument asymptotics).
  `lean/README.md` says what each library covers.
- `ledger.md` holds the predictions written down before the first computations for Papers A and B,
  what happened to them, and an index of the ledgers of the papers.
- `early_runs/` holds the recorded output of the joint checks of Papers A and B from 21 and 22
  September 2026, before the papers were split.
- `literature_review.md` says what each earlier source proves.

Run `python -B verify_all.py --paper a` (or `b`, `c`, `c2`, `d`, `e`, `f`, `s4`, or `all`). Add
`--full` for the long runs and `--dry-run` to list the commands. Build each paper in its folder with
pdflatex, 3 times, for example `pdflatex problem131.tex` in `paperA` and
`pdflatex problem131_multistate.tex` in `archive/paperB`. The builds of the three papers in
progress are these.

- Paper C1, article build. In `paperC`, `pdflatex -interaction=nonstopmode problem131_chains.tex`,
  3 times.
- Paper C1, Springer build. In `paperC`, from Git Bash,
  `TEXINPUTS=".;../common/sn-jnl;" pdflatex -interaction=nonstopmode problem131_chains_sn.tex`,
  3 times. The class is in `common/sn-jnl`, as `paperC/TEMPLATE.md` explains.
- Paper C2, `elsarticle` build. In `paperC2`,
  `pdflatex -interaction=nonstopmode problem131_reconstruction.tex`, 3 times (the class
  `elsarticle` is in TeX Live).
- Paper F, `ejpecp` build. In `paperF`, `pdflatex problem131_levy.tex`, 3 times (the class
  `ejpecp` is in TeX Live).
