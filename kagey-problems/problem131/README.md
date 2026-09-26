# Problem 131: Galton board with persistence

A ball goes left or right with probability 1/2 at the first peg and after that repeats its previous
direction with probability p. Kagey asks for the distribution of the bins, the lattice-path meaning of
his numerator tables, when the middle bin is as likely as the endpoints, the normal limit, and what
changes on a cylinder or a tetrahedron.

Status. Answered, in a series of 4 papers by A. Pemmasani, The middle and the ends I-IV (preprint, 2026). Paper A solves the binary problem
at every N, Paper B treats d directions on the complete graph, Paper C gives the general theory for
slowly switching chains, and Paper D asks what memory changes. The 4 papers share the notation N,
L = log N, T, z_N, lambda_F and K_F and cite each other by description. `PUBLICATION.md` has notes
on where to send them.

Conventions. N is the number of bounces, so Kagey's row n has N = n-1. For p = a/(a+b) his numerator
is 2(a+b)^(N-1) P_N(k). Write u = (1-p)/p for the switching odds, T = N(1-p) for the switching scale
and z_N = N(1-p_N) for the value of T at the central crossing p_N.

## Paper A: Uniform Bessel bounds for endpoint crossings in the persistent random walk

Paper A treats the walk with 2 states, which is the zero-field 1D Ising chain with free boundaries.
It gives the exact law and explicit uniform Bessel bounds for every bin, with relative error at most
N u^2/2 + u at every N. At the center these bracket the crossing p_N for every N >= 2. With
zeta_N = W_0(pi N^2/4)/2, the value z_N lies below zeta_N + 1/(8 zeta_N) and within
zeta_N(zeta_N + 1)/N + 1/(16 zeta_N^2) of it. The proof is analytic for N >= 175 and uses exact
integer certificates below that, and all of it is checked in Lean. This gives the crossing equation
z_N + (1/2) log z_N = L + c_0 + 1/(8 z_N) + R_N with c_0 = (1/2) log(pi/8) and
|R_N| <= 1/(4L^2) + (L^2 + L)/N. The paper also expands the crossing of every other bin, with a
Laguerre law for fixed bins, compares free and periodic boundaries, and proves a uniform local law
for every q <= 1/2, from the diffusive to the ballistic regime. Kagey's side questions are answered
there too. His p = 2/3 and p = 1/3 tables are OEIS A035002 and A348595 by bijection, the walk has a
normal limit, and on a cylinder the limit is uniform.

Files. The folder `paperA`, with `problem131.tex` and `problem131.pdf`, the sections
`sec_exact.tex`, `sec_crossing.tex`, `allbin_thresholds.tex`, `periodic_window.tex` and
`sec_llt.tex`, the appendices `app_every_n.tex`, `app_llt.tex` and `app_tables.tex`, the check
scripts and `paperA/README.md`.

## Paper B: Vertex crossings in a symmetric Markov multinomial model

Paper B treats the complete graph on d states, which is the 1D d-state Potts chain. Every face of
the simplex ties with the vertices at first order when T is near log N, and Paper B resolves the
tie at second order. A balanced bin with k states crosses a vertex at T = z, where
z + (1/2) log z = L + a_k + 1/(8z) + O(L^-2). The constants a_k come from the mass of a face over a
Gaussian volume, and Paper B writes them with square roots of weighted spanning-tree sums on K_k.
Since a_2 > a_3 > ..., the mode changes exactly once, from the vertices straight to the full
centers. A start law or a weak Potts field shifts the constants, so a start can make an edge win
on 3 states and a field can make every support size win in turn. The paper also gives a Bessel
majorant for every count vector and the crossing near a vertex, uniformly over rare counts of
total o(b).

Files. The folder `paperB`, with `problem131_multistate.tex` and `problem131_multistate.pdf`, the
sections `multistate_model.tex`, `simplex_thresholds.tex`, `general_start.tex`,
`frontier_modes.tex` and `frontier_boundary.tex`, the appendices `app_thresholds.tex`,
`app_start_field.tex`, `app_boundary.tex` and `vertex_completion.tex`, the check scripts and
`paperB/README.md`.

## Paper C: Face selection for slowly switching Markov chains and the planar persistent walk

Paper C gives the general theory for a chain on d states with transition matrix P = I + (T/N)Q, run
for N steps with T = tau L. The counts of the N visits play the role of the bin. To first order the
mode sits on a face F that minimizes tau lambda_F + |F| - 1, where lambda_F is the principal
Dirichlet eigenvalue of -Q on F, the rate at which the chain leaves F. At second order a strongly
connected face with start mass has a constant K_F, and the crossings of 2 such faces satisfy a
crossing equation. The constants of Papers A and B are corollaries. The main application is the
planar persistent walk, which is Kagey's board in 2 dimensions. The paper also treats sticky priors
for hidden Markov models and the Fisher information carried by the endpoint.

Files. The folder `paperC`, with `problem131_switching.tex` and `problem131_switching.pdf`, its
section and appendix files, the check scripts and `paperC/README.md`.

## Paper D: Endpoint crossings for random walks with memory

Paper D asks what memory changes. In the elephant random walk each step copies a uniformly chosen
earlier step and flips it with probability eps. The crossing x_n = n eps_n is unique and
x_n = 2 z_n - log(2 pi) + o(1), about twice the Markov value. The law at the crossing has 2 humps,
one near each end. For alternating runs with P(xi >= k) = k^(-alpha) and 1 < alpha < 2, the ends win
for large n exactly when alpha is below the golden ratio. A short remark treats aging walks, where
the crossing with a fixed first step is exactly c = 1.

Files. The folder `paperD`, with `problem131_memory.tex` and `problem131_memory.pdf`, its section
and appendix files, the check scripts and `paperD/README.md`.

## Earlier work

The exact law, the normal limit, interior log-concavity, the Bessel scaling at a fixed scale and the
periodic endpoint/center comparison are all in earlier papers (Renshaw and Henderson 1981, Dekking
and Kong 2011, Stepanyan et al. 2024 and others). Our results give uniform error control when p and
the bin vary with N. `literature_review.md` says what each source covers, and each paper has its own
section on related work.

## Shared files

Each paper has its own folder, `paperA` to `paperD`, with its source and PDF, its figures, its check
scripts and runner, their recorded output and ledgers in `data/`, and a `README.md`. Papers B, C and
D also keep the proofs cut while shortening them in `removed_proofs/`, for reference. The files
below are shared.

- `SUPPLEMENT.md` is the one verification supplement for the 4 papers. It lists each result that
  rests on computation with the script that checks it.
- `verify_all.py` runs the checks with `--paper a`, `b`, `c`, `d` or `all` (the default). It calls
  `paperA/verify_all.py` to `paperD/verify_all.py`, each in its own folder.
- `figures/` holds the program figure shared by all 4 papers (`program_A` to `program_D`), made by
  `figures/make_program_figure.py`, with the captions in `figures/program_captions.md`.
- `animations/` shows a Galton board with persistence at 4 values of p (`galton.gif`, `galton.mp4`),
  made by `animations/animate.py`.
- `lean/` holds the Lean 4 proofs, one library per paper (not the large-argument asymptotics).
  `lean/README.md` says what each library covers.
- `ledger.md` holds the predictions written down before the first computations for Papers A and B,
  what happened to them, and an index of the ledgers of all 4 papers.
- `early_runs/` holds the recorded output of the joint checks of Papers A and B from 21 and 22
  September 2026, before the papers were split.
- `literature_review.md` says what each earlier source proves.

Run `python -B verify_all.py --paper a` (or `b`, `c`, `d`, `all`). Add `--full` for the long runs
and `--dry-run` to list the commands. Build each paper in its folder with pdflatex, 3 times, for
example `pdflatex problem131.tex` in `paperA` and `pdflatex problem131_multistate.tex` in
`paperB`.
