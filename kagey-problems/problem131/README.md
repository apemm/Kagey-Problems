# Problem 131: Galton board with persistence

A ball goes left or right with probability 1/2 at the first peg and after that repeats its previous
direction with probability p. Kagey asks for the distribution of the bins, the lattice-path meaning of
his numerator tables, when the middle bin is as likely as the endpoints, the normal limit, and what
changes on a cylinder or a tetrahedron.

Status. There are eight papers by A. Pemmasani, which call each other Papers A, B, C1, C2, D, E,
F and G, and four working notes, S1 to S4. Paper A (arXiv:2610.06935) solves the binary problem at
every N, and Paper B (arXiv:2610.09258v1) treats d directions on the complete graph. Papers C1, C2,
D, E, F and G are in preparation, and C1 is under review at the Journal of Theoretical Probability. In October 2026 Paper B was merged into Paper C. Paper C1 will
replace it as version 2 of arXiv:2610.09258. Version 1 stays available on arXiv, and the folder
`archive/paperB` keeps it unchanged. On October 24, 2026 Paper C was split in two. Paper C1 (the forward theory of slowly
switching chains, in `paperC`) keeps the folder and the results of Paper B, and Paper C2 (what the
occupation law determines about the generator, in `paperC2`) holds the identifiability half. The
earlier EJP version of Paper C is in `archive/paperC_switching_ejp`. Paper C and Paper E (the
planar walk, in `paperE`) were one paper until October 13, 2026, and so were Paper D (the elephant
walk, in `paperD`) and the first draft of Paper F (heavy-tailed runs and aging walks). On October
24, 2026 that draft was archived in `archive/paperF_golden_aging`, its aging half became the note
`S4_aging_note`, and Paper F was started again in `paperF` as a paper on the occupation law of a
lattice Lévy walk. Papers F and G close the series. F treats the on/off process with finite-mean
periods and G the one with infinite-mean periods, and together they give the local law of the
occupation time on the whole square of tail indices in (0,1) and (1,2). The first draft of G, of
October 25, 2026, is in `archive/paperG_lamperti_draft`. The titles of Papers C1 to F are working titles, and Paper A cites C and D
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
[`archive/paperB`](archive/paperB/README.md). It was posted as
[arXiv:2610.09258v1](https://arxiv.org/abs/2610.09258v1), and Paper C1 will replace it as version 2
of the same entry, arXiv:2610.09258. Paper C1 reproves its results on the crossings with a vertex
and near a vertex as cases of the general theory. The next term of the crossing equation, the
Bessel majorant and the boundary crossover were not carried into C1 and remain in version 1, which
C1 cites for them.

## Paper C1: Occupation counts of rarely switching Markov chains

Full title "Occupation counts of rarely switching Markov chains: stratified local laws, support
selection and the boundary layer". Paper C1 (in preparation, for the Journal of Theoretical
Probability) is the forward theory for a chain on d states with transition matrix P = I + (T/N)Q,
run for N steps with T = tau L. Its object is the law of the vector of occupation counts, which
has a face of the simplex as support. Every rate on a face is the
restriction of the Donsker and Varadhan functional of the whole chain. To first order the mode
sits on a face F that minimizes tau lambda_F + |F| - 1, where lambda_F is the exit rate of F, for
every start. For a strongly connected face with start mass we prove a stratified local law with an
explicit constant K_F, face maxima with a field, a crossing equation for 2 such faces and the tie
windows. The boundary layer at a facet is proved for every face with at least 2 states. The
complete graph, the Potts chain, is the main example, and there every face ties at first order,
each balanced crossing is unique at every N and the mode changes exactly once. Near a vertex the
crossing is given by a product of Laguerre polynomials. The two-state walk of Paper A is the case
d = 2 of the complete graph. The application to sticky priors for hidden Markov models moved to the
note `S3_sticky_note`.

On October 24, 2026 an editing pass for the journal cut C1 from 67 to 59 pages. It removed the tree
formula on a general face, the pair identity and the two-state corollary, a remark on first-order
winners on other graphs, the restated local law on the complete graph and the figure of the 6-cycle.
No remaining statement changed. `paperC/EXPORTS.md` records the new numbers, and
`lean/PaperC/MAP.md` keeps the Lean theorems of the removed statements in its section on cut
statements.

On October 25, 2026 the paper gained the local law over the whole switching range, the face maxima
and crossings of every admissible face and the counts near a facet, and it now has 81 pages.

Files. The folder `paperC`, with the main file `problem131_chains.tex` and `problem131_chains.pdf`
(article class, 81 pages), the same paper in the Springer Nature template
`problem131_chains_sn.tex` and `problem131_chains_sn.pdf` (89 pages, `paperC/TEMPLATE.md` says how
it was set up and built), their shared section and appendix files, the check scripts,
`paperC/EXPORTS.md` (the statements that Paper C2 cites, with their numbers) and
`paperC/README.md`. The earlier main file `problem131_switching.tex` (class `ejpecp`), its PDF and
its supplement are in `archive/paperC_switching_ejp/`.

## Paper C2: What the occupation law of a finite Markov chain determines

Full title "What the occupation law of a finite Markov chain determines: time reversal, principal
minors and cycle trees". Paper C2 (in preparation, for Stochastic Processes and their
Applications) asks what the law of C1 and its coarse functionals determine about Q. The Donsker and
Varadhan functional determines exactly the principal minors of -Q, and the generators with the
same minors form a finite set, which is {Q, Q*} without a cut and for d <= 3. The exact law of the
occupation times at one time determines it at every time, and it determines Q for a generic start
(Section 4). From the stationary start Q and its time reversal give the same law, and they are the
only generators that do when d <= 4, without a cut, and for almost all rates, while reversal inside
a memoryless block gives a third one for d = 5. The controlled boundaries of the modal supports determine the same minors.
A reversible design fixed in advance recovers Q, also at a finite horizon uniformly over a compact
class. At low temperature the calibrated rewards read off the cycle tree. The introduction states
these results as Theorems A to D. Section 2 states the results of C1 that the paper uses, each with
its C1 number.

Files. The folder `paperC2`, with the main file `problem131_reconstruction.tex` and
`problem131_reconstruction.pdf` (class `elsarticle`, 43 pages), the arXiv build
`problem131_reconstruction_arxiv.tex` and its PDF (46 pages, with the reversible design as Section
8), its section files, the check scripts, the cover letter and `paperC2/README.md`.

## Paper D: The elephant random walk with rare reversals

Full title "The elephant random walk with rare reversals: a Luria-Delbrück approximation and the
shape of the law". Paper D (in preparation, for the Journal of Theoretical Probability) asks what
memory changes. In the elephant random walk each step copies a uniformly chosen earlier step and
flips it with probability eps, with x = N eps of order log N. The main result bounds the total
variation distance between the number of steps that disagree with the first one and a truncated
Luria-Delbrück law, with a local limit theorem as a consequence. The crossing x_N = N eps_N is
unique and x_N = 2 z_N - log(2 pi) + o(1), about twice the Markov value. The law at the crossing has
2 humps, one near each end, and the middle is its unique interior minimum. On October 24, 2026 the
family proofs and the second-difference proofs came back into the article as Appendices D and E,
so every proof used by the main theorems is in the article. There is no Online Resource. The
second order, the tail, odd N and the likelihood theorem are Sections S1 to S4 of the arXiv build,
and the convexity window and the proofs for the threshold certificate are Sections S5 and S6.
The journal version cites that build where it needs them.

Files. The folder `paperD`, with the journal version `problem131_memory.tex` and
`problem131_memory.pdf` (45 pages), the arXiv build `problem131_arxiv.tex` and
`problem131_arxiv.pdf` (64 pages) with Sections S1 to S6, its section and appendix files, the check scripts
and `paperD/README.md`.

## Paper E: Endpoint crossings for the planar persistent walk

Paper E (in preparation) treats the planar persistent walk, which is Kagey's board in 2 dimensions.
Its corner and origin cross exactly
once, at T/L -> min(2/(2r+s), 1/s), and the paper finds the crossing to second order when reversals
dominate and when turns dominate. On one curve of rates the walk is exactly 2 independent copies of
Paper A's walk.

Files. The folder `paperE`, with `problem131_planar.tex` and `problem131_planar.pdf`, its section and
appendix files, the check scripts and `paperE/README.md`.

## Paper F: Local laws for the occupation time of on/off processes with heavy-tailed, finite-mean periods

Paper F (in preparation, for the Electronic Journal of Probability) was started on October 24,
2026 and restructured on October 27 and 28. An on/off process alternates on and off periods with
independent lengths whose tails are regularly varying with indices between 1 and 2, so the periods
have a finite mean. Equivalently, a lattice Lévy walk moves in runs of alternating direction. The
paper describes the law of the number of on slots among the first N at every point of the range
{0, ..., N}. It has a stable bulk, a big-jump zone on each side where one period is macroscopic, a
renewal boundary layer at each end and an atom at each endpoint. The law of the first period enters
each piece through a sharp criterion, for a fixed law and for laws that depend on N, and observation
from time theta N on ages the atom, the layer and the big-jump zone but not the bulk. The global
mode is an endpoint or a point of the bulk, and for the stationary start and for every aged start the
threshold is the golden ratio. For fresh and fair starts with comparable scales, a second-order
smoothness condition and no ties in the end profiles the law has exactly M_+ + M_- + 1 modes for all
large N, where M_± counts the local maxima of the end profiles. The last section reads the theorems
as the exposure law of a switchback experiment that switches arm at the regenerations of a slotted
queue with heavy-tailed service, after proving that the cycle law of the queue satisfies the
difference hypotheses. Journal build 90 pages, arXiv build 93 pages.

Files. The folder `paperF`, with `problem131_levy_arxiv.tex` (the whole paper, the arXiv version
when compiled alone), the journal driver `problem131_levy.tex`, the two PDFs, the section files, the
figure and its script in `figures/`, the recorded output of the computations in `data/`, the check
scripts and `paperF/README.md`.

## Paper G: The local Lamperti law

Paper G (in preparation, for the Electronic Journal of Probability) was rewritten on October 28,
2026 from its first draft of October 25. It is the infinite-mean companion of Paper F: the periods
have regularly varying tails with indices in (0,1). When the two tails are comparable the limit law
of the occupation fraction is Lamperti's generalized arcsine law, and the paper proves its local
form: the rescaled point probabilities converge at one interior point iff uniformly on compact sets
iff both period laws satisfy the strong renewal theorem. Near the ends the law is the tail of a
period times a renewal mass function, and the global mode sits at bounded distance from an end for
every index. The paper gives the exact effect of an arbitrary initial period, proves that an initial
period of length of order N turns the law into an explicit mixture, and so obtains the local aging
law of the process observed from time theta N on, with atoms of order 1 and end layers of explicit
height. When one tail is heavier it gives the local law of the time on the lighter side at an
intermediate scale, with the exact renewal conditions. It classifies the critical points of
Lamperti's density for every index and tail ratio, with a closed-form window for the W shape, counts
the modes near the ends exactly, and leaves one second-difference local limit theorem in the bulk
between a lower bound and the exact count. Both builds are about 47 pages.

Files. The folder `paperG`, with `problem131_lamperti_arxiv.tex` (the whole paper), the journal
driver `problem131_lamperti.tex`, the two PDFs, the section files, the figure and its script in
`figures/`, the check scripts and the scans with their outputs, and `paperG/README.md`.

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
- `S4_aging_note/` is a short note of 12 pages, "The finite-size shape transition of coin-turning walks" (for Electronic Communications in Probability), on the walk that switches at step k with probability c/k and its version with d states. Every interior point ties with the end exactly at c = 1 for every N, and the chain that redraws or repeats its state has the law of Pólya's urn. It was the aging half of the first draft of Paper F until October 24, 2026, and it has 2 check scripts.
- `archive/` holds Paper B v1 (`archive/paperB`), the earlier EJP version of Paper C, "Face selection for slowly switching Markov chains", with its supplement (`archive/paperC_switching_ejp`), the first draft of Paper F, "The golden-ratio threshold for a lattice Lévy walk and ties in coin-turning walks" (`archive/paperF_golden_aging`), and the first draft of Paper G, "A local Lamperti law for the occupation count of a lattice Lévy walk with infinite-mean runs" (`archive/paperG_lamperti_draft`), each kept as it was and with its own `README.md`.
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
- Paper F, `ejpecp` build. In `paperF`, `pdflatex problem131_levy.tex` (journal) or
  `pdflatex problem131_levy_arxiv.tex` (arXiv), 3 times (the class `ejpecp` is in TeX Live).
- Paper G, `ejpecp` build. In `paperG`, `pdflatex problem131_lamperti.tex` (journal) or
  `pdflatex problem131_lamperti_arxiv.tex` (arXiv), 3 times.
