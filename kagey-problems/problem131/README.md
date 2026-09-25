# Problem 131: Galton board with persistence

A ball goes left or right with probability 1/2 at the first peg and after that repeats its previous
direction with probability p. Kagey asks for the distribution of the bins, the lattice-path meaning of
his numerator tables, when the middle bin is as likely as the endpoints, the normal limit, and what
changes on a cylinder or a tetrahedron.

Status: answered, in two papers. Paper A (`problem131.tex`) is the binary problem. Paper B
(`problem131_multistate.tex`) is the version with d directions and is still a draft.

Conventions: N is the number of bounces, so Kagey's row n has N = n-1. For p = a/(a+b) his numerator
is 2(a+b)^(N-1) P_N(k). Write u = (1-p)/p for the switching odds.

## Paper A: binary crossings

- Exact law by run counts, generating function and recurrence. The p = 2/3 table is A035002 (rook
  paths) and the p = 1/3 table is A348595 (Mathar's blocked walks), both by bijection.
- Variance, normal limit, and the cylinder (uniform limit, no normal shape).
- For every N there is exactly one p_N where the middle bin equals the endpoints, and p_N increases
  strictly to 1. The adjacent bin equals the endpoints at p = (1 + sqrt(N-1))/(2 + sqrt(N-1)).
- Bessel approximation with relative error at most N u^2/2 + u for every bin. This gives
  N(1-p_N) = log N - (1/2) log log N + (1/2) log(pi/8) + o(1), with the next 1/log N term.
- The same kind of expansion for every bin whose distance a from the edge grows, a Laguerre law at
  fixed distance with correction -1/b for every a, and a theorem matching the two.
- Periodic boundaries: relative error at most N u^2/2, and the periodic and free central crossings
  differ by N(u_P - u_F) = log 2 + o(1).
- Under both boundaries the ratio near the center has the profile exp(t - 2y^2), and the scaled
  number of bins above the endpoints tends to sqrt(2 max(t,0)).

## Paper B: d directions

- Exact finite sum for the bin probabilities, covariance and normal limit (d = 3 is the tetrahedral
  board). Other rules at the walls of a board give different models, which are not covered.
- Unique crossings for the balanced center of each face, with explicit constants, and the global
  modes in the critical window. At d = 3, N = 4 an edge center is the global mode, so the asymptotic
  result does not hold for every N.
- A Bessel bound with relative error at most k(k+1)v + k^2 N v^2/2, v = u/(1-u), for every positive
  composition, and a crossover when some coordinates have size N/(log N)^2.
- Near a vertex: a product of Laguerre polynomials gives the crossing, first for fixed rare counts
  and then uniformly for total rare count A = o(b), with relative error O(sqrt((A+1)/b)). An example
  shows that the probabilities themselves need not be approximated uniformly in that range.
- Volumes of the superlevel sets on each face, and a weak field h_i = -(i-1)^2 under which every
  support size is the mode in turn.

Open: a uniform higher-order expansion near a vertex for all A = o(b), a growing number of
directions, and the full mode diagram at finite N.

The exact law, the normal limit, interior log-concavity, the Bessel scaling and the periodic
endpoint/center comparison are all in earlier papers (Renshaw and Henderson 1981, Dekking and Kong
2011, Stepanyan et al. 2024 and others). What is new here is the uniform error control when p and
the bin vary with N. See `literature_review.md` for what each source covers.

## Files

- `problem131.tex`, `problem131.pdf`: Paper A. Includes `allbin_thresholds.tex` and
  `periodic_window.tex`.
- `problem131_multistate.tex`, `problem131_multistate.pdf`: Paper B. Includes
  `simplex_thresholds.tex`, `frontier_boundary.tex`, `vertex_completion.tex` and
  `frontier_modes.tex`.
- `verify*.py`, `check_bessel.py`: checks for both papers; `SUPPLEMENT.md` says what each one covers.
- `lean/`: Lean 4 proofs of the finite algebraic steps (not the asymptotics).
- `data/ledger.md`: predictions written down before the computations, and what happened to them.
- `data/`: recorded output of the checks.

Run `python -B verify_all.py` (standard library only), or add `--paper a` or `--paper b`. Build a
paper with `pdflatex problem131.tex` twice, or `problem131_multistate.tex`.
