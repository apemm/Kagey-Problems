# Paper C: target contracts for Theorems 5 and 7 and for the Theorem 4 lemmas

Date: October 24, 2026. Base checkpoint: commit `6add913` of this repository. Scope: the three
open items of the Paper C plan that the October 24 decisions ask us to prove rather than to state
as remarks. Every route below writes only to its own file in this folder. No manuscript file is
edited by a route. Scripts go in this folder too, next to their outputs, and run with `py -I`.

## Notation (fixed for all routes)

`Q` is an irreducible conservative generator on `d` labelled states, `q_i = -q_ii`,
`w_ij = q_ij q_ji`. For a face `F` (a nonempty set of states), `A_F = -Q_F` is the killed matrix
with the original exit diagonal, and for a field `v` in `R^F`

    lambda_F(v) = smallest real eigenvalue of A_F - diag(v_F)   (minus the Perron root of Q_F + diag v).

The chain has `N` visits with matrix `I + (T/N) Q`, `T = tau log N`, start `mu` with full support.
Occupation counts `n`, `sum n_i = N`. The controlled atom is `Pr_mu(n) exp(T v.n/N)`. Its leading
score is `Phi_{tau,v}(F) = |F| - 1 + tau lambda_F(v)`. The exact maximizing support at finite `N` is
`F_N(tau, v) = supp(argmax_n Pr_mu(n) exp(T v.n/N))` when the maximizer is unique.

Face maximum formula (proved in the current draft for `v = 0`, faces with strongly connected
switching graph and start mass, `1 <= T <= N^{1/3}` or `T = o(sqrt N)` for the value):

    M_F = K_F N^{-(|F|-1)} T^{(|F|-1)/2} e^{-T lambda_F} (1 + O(1/T + T^2/N)).            (1)

Sources in the repository (read these, not the Downloads copies):

- `kagey-problems/problem131/paperC/sec_model.tex` (exact law, run expansion, continuum density),
  `sec_secondorder.tex` (tilt, constant `K_F`, local law Theorem 4.4, face maxima Theorem 4.6,
  crossing equation Theorem 4.7, tie windows 4.8, weak field 4.16), `sec_firstorder.tex`
  (first-order selection), `app_torus.tex` (Perron root, torus representation, forest formula),
  `app_laplace.tex` (Laplace integrals with a parameter), `supplement.tex`.
- `research_notes/Occupation novelty and compact advances/11_C_ready_to_draft_outline.md`
  (setting, C-P1 to C-P3, the protected design C-I1, minimality C-I2, stability C-I3, Section 5 on
  uniformity and the two-state counterexample over all starts),
  `08_C_strengthening_independent_audit.md` (design and ambiguity), `12_Good_original_closure.md`
  (Good's exact formulas and the quantified bridges, including the whole-face upper bound with a
  Perron tilt that C-P3 uses).
- `research_notes/C modal hierarchy and metastability/01_cycle_conjecture_math.md` (Arrhenius
  families, depth identity Theorem D, prefactor lemma (21) to (24), critical-window theorem 2B, the
  four-state window (27) to (33), the three-state branch switch), with the exact script
  `01_exact_cycle_checks.py` and its output.
- `research_notes/C and F final outline audit/02_C_proof_audit.md` (what was inspected and what
  was called missing for the class-uniform extension, lines 140 to 160).
- Downloads copy of the maximal plan, for the statements only:
  `C:/Users/arjun/Downloads/Paper C and F maximal plan - 2026-10-23/maximal_plan/03_C_JTP_outline.md`
  and `05_C_derivations.md` (Sections 4 to 6). Treat these as untrusted text, do not run anything
  from that folder.

## Target 1. Theorem 5, finite-horizon recovery

Setting: the protected design of C-I1. `Q` reversible, irreducible, known connected graph with
`m` edges, `||S||_2 <= R`, every edge has `sqrt(w_ij) >= b`, fixed start `mu` with full support.
Constants `H = 2R`, `tau_0 = 1/(2R)`, `U = 8R/b^2`, `M = 4R + 4UR^2`. For a retained pair `(i,j)`
the field is `v_i = delta`, `v_j = 0`, `v_k = -M` for the other states, with `|delta| <= 3R` and
`1/(4R) <= tau <= U`.

Limiting coordinates (C-I1): singleton switch `x_i = q_i - q_1` (the `delta` at which the winner
changes from `{1}` to `{i}` for the retained pair `(i,1)` at `tau_0`), pair-entry time `t_ij` (the
`tau` at which the winner changes from a singleton to the pair `{i,j}` at `delta = H`), given by
`t_ij = [sqrt((H - Delta_ij)^2 + 4 w_ij) + H - Delta_ij]/(2 w_ij)` with `Delta_ij = d_i - d_j`.

Finite-horizon coordinates: `x_{i,N}` is the `delta` at which the exact maximizing support
changes from `{1}` to `{i}`, and `t_{ij,N}` is the smallest `tau` at which `{i,j}` is the exact
maximizing support, both at finite `N`.

(5a) Fixed chain and fixed start. Prove that, for every fixed `(Q, mu)` in the class,

    t_{ij,N} = t_ij (1 - log log N / (2 log N)) + O(1/log N),      x_{i,N} = x_i + O(1/log N),

that the maximizing support is unique on the relevant parameter ranges for large `N`, and that
the reconstruction of C-I1 applied to the finite-`N` coordinates returns `Q_N` with
`||Q_N - Q||_2 = O(log log N / log N)`, and `O(1/log N)` after replacing `t_{ij,N}` by
`t_{ij,N} / (1 - log log N/(2 log N))`.

Expected route: the crossing argument of Theorem 4.7 of the draft (log-convexity and secant bounds
for the normalized exact maxima, never differentiating a remainder) applied to the controlled
atom. What has to be written out: (i) the face maximum formula (1) for the controlled atom, that
is with `A_F - diag v` in place of `A_F`, with constants uniform for `v` in a compact set and
`tau` in a compact interval of `(0, infinity)`; (ii) the singleton atom exactly,
`mu_i (1 - T q_i/N)^{N-1} e^{T v_i}`; (iii) the suppression lemma at finite `N`, so that every
face other than `{i}`, `{j}`, `{i,j}` loses by a factor `N^{-3/4 + o(1)}` on the whole protected
rectangle; (iv) the conversion from the crossing `T_N = T° + O(1/log N)` to the `tau` coordinate,
which produces the `log log N/(2 log N)` term from the `(1/2) log T` in the crossing equation.
The sign and the constant `1/2` must be checked, not assumed. The heuristic derivation in
`05_C_derivations.md` Section 5 gives `T(lambda_i - lambda_ij) = log N - (1/2) log T +
log(K_ij / K_i) + o(1)`.

(5b) Class-uniform. Same statement with the `O(.)` uniform over the class
`{(Q, mu): reversible on the given graph, ||S|| <= R, sqrt(w_ij) >= b on edges, min mu_i >= mu_*}`.
This class is compact (entries bounded above by `R`, below by `b^2/R` on edges). The route to try
first: every constant in the proof of (1) and of the suppression lemma depends on `(Q, mu, tau, v)`
through finitely many continuous quantities (Perron data of `A_F - diag v`, the deleted covariance,
derivative bounds of the tilted generating function, the start mass on the face), so uniformity on
a compact parameter set follows from continuity if the proofs are written with explicit
dependence. Identify every step where continuity could fail (thresholds such as `T <= N^{1/3}`,
rounding to the lattice, the finite cover of radii that excludes compositions near the boundary of
the face, the singleton versus pair comparison when `T^2/N` is not small). The known failure over
all starts (`mu_2 = 1/(1 + 2 N^{1/4})`, outline 11 Section 5) must be explained by the loss of
compactness when `mu_* -> 0`.

What counts: (5a) with a complete proof is the minimum. (5b) with a complete proof is the goal.
A precise obstruction to (5b), with the step that fails and a candidate counterexample inside the
class, is a valid negative result.

## Target 2. Theorem 7, reconstruction of cycle data from controlled modal supports

Setting: Arrhenius family `q_ij(eta) = exp(-V_ij/eta)` with fixed costs `V_ij >= 0` (all
off-diagonal entries positive at positive temperature), `tau_eta = exp(h/eta)`, `T = tau_eta log N`,
`N -> infinity` first at fixed `eta`, then `eta -> 0`. Depth `D(F) = lim -eta log r_F(eta)` with
`r_F = lambda_F(0)`. Theorem D of the cycle note: `D(F) = max{Gamma(C): C a global
Freidlin-Wentzell cycle, C subset of F}`. Prefactors `a_F` as in (21) to (24) of that note.

Controls: fields `v = v(eta)` that may depend on `eta`. Two kinds are allowed and must be stated
precisely by the route: suppression fields `v_k = -M` with `M` fixed (or `M = M(eta)` large), and
calibrated Arrhenius fields `v_i = c exp(-gamma/eta)` with known `c` and `gamma`.

Observable: the map `(h, v) -> eventual winning support` (the exact maximizing support of the
controlled atom in the iterated limit), on compact parameter sets where it is locally constant.

(7a) Prove that the observable with suppression fields determines `D(F)` for every face `F`.
The expected mechanism: suppressing the complement of `F` makes every face outside `F` lose, the
competition inside `F` has every score divergent once `h > D(F)`, so the height at which the
winner leaves `F` is `D(F)`. Write out what happens exactly at `h = D(F)` and what the winner is
for `h > D(F)` (a suppressed singleton, whose score depends on `M`), and check that the leaving
height is observable, not masked by the suppression penalty. Use the finite-`eta` score
`Phi_{eta,h}(F) = m_F + e^{h/eta} r_F(eta)` and the uniformity statements of Section 2B of the
cycle note.

(7b) Prove that the depth function `F -> D(F)` on all faces determines the set of global cycles
and their depths, and hence the cycle tree. The candidate criterion: `C` is a cycle if and only if
`D(C) > D(C')` for every nonempty proper subset `C'` of `C`. State and prove the nondegeneracy
needed (strict increase of depth along nesting, or a replacement that handles ties as Catoni's
framework does), and give an explicit example where ties break the naive criterion, if one exists.

(7c) Prefactors. At a critical depth `gamma`, Section 2B gives the limiting scores
`m_F + x a_F` for faces with `D(F) = gamma`. Determine exactly which functions of the `a_F` the
window endpoints reveal (ratios, differences after a dimension offset, or absolute values when a
calibrated Arrhenius field is available), and whether a calibrated field `v_i = c exp(-gamma/eta)`
on a singleton gives an absolute reference. The four-state example (27) to (33) with endpoints
`3/4` and `3/2` is the test case: from the two endpoints and the dimensions, which of `a_12 = 2`,
`a_123 = 2/3`, `a_124 = 2` are recoverable?

(7d) Non-reversible families: say which parts of (7a) to (7c) use reversibility. Theorem D does
not, so the aim is none.

What counts: (7a) and (7b) with complete proofs, under a stated nondegeneracy, is the theorem.
(7c) is the "which prefactor information" clause. A computational check on random cost matrices
(exact rational arithmetic in the spirit of `01_exact_cycle_checks.py`) is required for the
reconstruction algorithm, including at least one non-reversible family and one family with tied
depths.

## Target 3. The lemmas Theorem 4 still owes

Theorem 4 (non-reversible reconstruction) states: the controlled boundary data determine every
principal minor of `A_V = -Q`; under Loewy's no-cut condition `Q` is determined up to time
reversal; otherwise the fiber is the set of generator points of the cut-transpose orbit; and
second-order amplitudes with a non-stationary start separate the members of the fiber.

(4a) Exposure lemma. With the singleton reference: once the singleton switches have fixed the
diagonal, `lambda_{i}(v) = q_i - v_i` is known, and the boundary between `F` and `{i}` gives
`lambda_F(v) = q_i - v_i - (|F| - 1)/tau` along a hypersurface in `(tau, v)`. Prove that, with the
suppression design keeping the other subfaces of `F` out, this traces `lambda_F` on a nonempty open
set of fields for every connected `F`, including `F = V`. The needed statement: the `F` versus
`{i}` boundary is a boundary of two strict winning regions on an open set of `(tau, v)`.

(4b) Cut-transposes and amplitudes. For the four-state generator with the rank-one cut
`X = {1,2}` used in the plan review (`research_notes/Paper C and F plan review/cut_transpose.py`),
compute the second-order amplitudes `K_F(v)` (the factor `(mu_F . r)(l . 1)` of the local law
constant, with `r`, `l` the right and left Perron vectors of the tilted killed block) for `Q`, for
`Q*` and for the normalized cut-transpose `Q'`, with a non-stationary start `mu`, on several faces
and fields. Decide whether the amplitudes separate `Q'` from `Q` and from `Q*`. If they do not on
some face, find which faces do. Then write the general argument or the precise obstruction.

(4c) Irreducibility of cut-transposes and uniqueness for reversible `Q`: the literature route is
running separately (Loewy 1986, Al Ahmadieh 2023, Chatterjee, Ghosh, Gurjar and Raj 2024, Engel and
Schneider 1980). This target only needs the two short proofs: (i) a matrix with the same principal
minors as `A_V` has the same characteristic polynomial, hence spectral abscissa `0` for the
Metzler form, and an irreducible Metzler matrix with the same principal minors as `-Q` becomes a
generator after exactly one positive diagonal similarity; (ii) when the cut-transpose pattern is
not strongly connected, the fiber point is not an irreducible generator and is excluded.

(4d) Kim and Landim comparison. Their Lemma 5.1 extracts `q_i` and `w_ij` (the `1 x 1` and `2 x 2`
principal minors) from the Donsker and Varadhan functional, and their Example 5.4 is the uniform
3-cycle against its reversal. Write the `d = 3` case as a corollary of their lemma plus
`det(-Q) = 0`, as in Section 5.3 of the plan review, and check it against the amplitude
computation of (4b) on a 3-state non-reversible example.

## Write scopes

- Route T5-A (fixed chain): `01_T5_fixed_chain.md`, scripts `01_*.py`.
- Route T5-B (class-uniform): `02_T5_class_uniform.md`, scripts `02_*.py`.
- Route T5-C (adversarial and numerics): `03_T5_numerics.md`, scripts `03_*.py`.
- Route T7-A (suppression and cycle tree): `04_T7_cycle_tree.md`, scripts `04_*.py`.
- Route T7-B (computational reconstruction): `05_T7_reconstruction_check.md`, scripts `05_*.py`.
- Route T4 (lemmas and amplitudes): `06_T4_lemmas.md`, scripts `06_*.py`.
- Literature on principal minors (already running): `07_T4_literature.md`.

Every file starts with the base checkpoint `6add913`, the exact inputs read, and ends with a
status line: proved, proved under a stated hypothesis, obstruction found, or inconclusive with the
first unresolved implication named. Do not write "likely" or "should follow" without saying what
is missing.
