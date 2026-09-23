# Problem 131: endpoint competition with memory

A ball chooses left or right fairly at the first peg and thereafter repeats its previous
direction with probability p. This folder answers Kagey's distribution, lattice-walk,
center/endpoint crossing and normal-limit questions, and treats the cylinder and the
explicit symmetric d-direction interpretation of a tetrahedral board. The September 22,
2026 revision separates the binary endpoint-crossing results (Paper A) from the
multistate simplex results (Paper B). Paper B is an unsubmitted draft held for
further review; its citation to Paper A is an unpublished-companion citation.

## Status

- Exact binary law, two OEIS bijections, variance and normal limit: proved.
- Unique center/endpoint crossing p_N, strictly increasing to 1: proved.
- Bessel approximation: now proved uniformly, with parameter error O(log(N)^2/N^2).
- Refined threshold: N(1-p_N) = log N - (1/2) log log N + (1/2) log(pi/8) + o(1),
  with an additional inverse-logarithm correction in the manuscript.
- Adjacent-bin/endpoint equality: p = (1 + sqrt(N-1))/(2 + sqrt(N-1)).
- Symmetric d-direction board: explicit finite bin-probability sum and multivariate CLT,
  including the tetrahedral case d=3. Different geometric transition rules are separate models.
- All binary bins: relative Bessel error at most N u^2/2+u, independent of the bin,
  where u=(1-p)/p. This gives a uniform threshold expansion for every growing distance
  from an edge, a fixed-distance Laguerre law with universal -1/b correction, and a
  matching theorem and moving boundary-layer law.
- Periodic spin boundaries: relative error at most N u^2/2, a rigorous central-crossing
  expansion, and N(u_periodic-u_free)=log(2)+o(1).
- Both binary boundaries: critical ratio profile exp(t-2y^2), and scaled number of bins
  beating the endpoints tending to sqrt(2 max(t,0)).
- Symmetric d-direction model: unique, strictly row-monotone crossings for balanced
  face centers, explicit constants and inverse-log corrections, and global modes in
  the critical window. A finite N=4,d=3 counterexample shows that intermediate face
  centers can be the global modes outside the asymptotic conclusion.
- Every positive multistate composition: a Bessel-integral majorant with relative error
  at most k(k+1)v + k^2 N v^2/2, where v=u/(1-u), independent of coordinate proportions.
- Near a face with at least two macroscopic coordinates: a proved crossover when rare
  coordinates have size N/log(N)^2, with explicit Bessel factors in the crossing constant.
- Near a vertex with fixed rare counts: a product-Laguerre crossing law and first correction.
  For ell singleton rare colors the odds are b^(-1/2)-(ell+1)/(2b)+O(b^(-3/2)).
- Near a vertex with arbitrary growing rare counts: for fixed ell and total A=o(b),
  the Laguerre-product root has relative error O_ell(sqrt((A+1)/b)), uniformly over
  unequal counts. An explicit finite bracket and exact compound-binomial/gamma
  representation prove the result. A counterexample shows that root asymptotics
  can remain valid while the corresponding relative probability approximation diverges.
- Spatial superlevel sets on each face: a Gaussian profile and explicit lattice-volume law.
- A separately defined Gibbs occupation tilt with fields h_i/N: an explicit asymptotic
  support-selection diagram. Every intermediate support size can remain a global mode
  on an open parameter interval for suitable fixed fields.
  The single choice h_i=-(i-1)^2 realizes all support sizes successively, with explicit
  ordered transition parameters.

The classical law, normal limits, interior log-concavity and Bessel connections have prior
literature. The deeper review also found direct work on periodic endpoint/center crossings
by Stepanyan et al. (2024) and exact periodic coefficients by Dantchev and Rudnick (2022).
The proposed contribution is the uniform moving-parameter analysis and its additional
consequences. Novelty remains unconfirmed; see `PUBLICATION.md` for precise attribution
and reading gaps.
The full Renshaw--Henderson (1981) paper has now been checked, including its
fixed-scale Bessel limit and subsequent large-parameter limit. Dekking--Kong
Proposition 4.3 and the wording around Stepanyan et al. equation (16) have also
been checked. The binary extrema proof uses an independent coefficient-ordering
argument; it includes the strict central/adjacent crossing gap for N>=4 and the
N=2,3 ties. Details and source locations are in `literature_review.md`.
Library access also provided the full 2001 local-limit paper and confirmed that
its main theorem excludes the persistence regime used here. It also identifies the
square-root composition exponent as the classical occupation-time large-deviation rate;
the proposed advance is the uniform discrete control and its consequences.

This answers the original problem for the stated models. It does not classify every
finite-size multistate mode or every physical board geometry. The analytic theorems have
written proofs; the Lean development covers finite algebraic ingredients, not the full
asymptotic arguments.

Conventions: N is the number of bounces; Kagey's row n has N=n-1. For p=a/(a+b),
his numerator is 2(a+b)^(N-1) P_N(k).

## Files and verification

- `problem131.tex`, `problem131.pdf`: Paper A, *Endpoint crossings in the persistent
  random walk: uniform Bessel bounds and boundary effects*.
- `allbin_thresholds.tex`, `periodic_window.tex`: the two sections included by Paper A.
- `problem131_multistate.tex`, `problem131_multistate.pdf`: Paper B, *Vertex crossings
  and boundary regimes in a symmetric Markov multinomial model*. This is a
  self-contained draft, held for further mathematical and literature review.
- `simplex_thresholds.tex`: balanced-face crossings, included by Paper B.
- `frontier_boundary.tex`, `frontier_modes.tex`: uniform simplex bounds, rare-coordinate
  crossings, spatial superlevel counts and weak-field face phases.
- `vertex_completion.tex`: uniform leading near-vertex law for all A=o(b), explicit
  brackets, shape asymptotics and a failure of relative probability approximation.
- `verify.py`: original 25 checks of the binary law, generating functions, bijections and roots.
- `check_bessel.py`: 1,400 uniform-bound cases and high-precision root checks through N=10^8.
- `verify_geometry.py`: exact finite-sum, DP, enumeration, moments and boundary checks.
- `verify_adjacent.py`: adjacent-bin polynomial and global-extrema checks.
- `verify_allbin.py`: exact coefficient comparisons, uniform estimates, edge expansions
  and moving boundary-layer checks.
- `verify_periodic_window.py`: independent cyclic enumeration, relative errors,
  boundary-shift and critical-profile checks.
- `verify_simplex_threshold.py`: enumeration, balancing, finite-size counterexample,
  and high-precision face-crossing checks.
- `verify_frontier_boundary.py`, `verify_frontier_modes.py`: checks for the frontier extensions.
- `verify_vertex_completion.py`: 462 exact identity comparisons, 200 rational elasticity
  checks, 16 root brackets and four large growing-rare-count stress cases.
- `verify_all.py`: runs all ten verification scripts and fails if any fail;
  `--paper a` and `--paper b` select the five scripts for the corresponding paper.
- `SUPPLEMENT.md`: script coverage, reproduction commands, and formalization limits.
- `lean/`: formal finite-product and algebraic proofs, with coverage/build documentation.
- `data/ledger.md`: original predictions preserved with subsequent proof status.
- `data/bessel_verification.txt`: recorded high-precision results.

Run `python -B verify_all.py` with standard-library Python 3. No packages are required.
Numerical checks corroborate the proofs; they do not establish novelty or replace human review.
Build Paper A with `pdflatex -interaction=nonstopmode -halt-on-error problem131.tex`
twice, or replace the filename with `problem131_multistate.tex` for Paper B.

Complete analytic proofs are in the two main TeX files and their included sections.
Literature comparisons and reading gaps are recorded in `PUBLICATION.md`;
formalization coverage is described in `lean/README.md`. Verification results
are under `data/`. Full higher-order uniformity for all A=o(b) and a growing
number of rare colors remain open here.
