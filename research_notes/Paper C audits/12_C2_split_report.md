# Paper C audit 12. The split, Paper C2

October 24, 2026. Paper C2 is built in `kagey-problems/problem131/paperC2` from the copy of
`paperC` made that morning. Main file `problem131_reconstruction.tex` (elsarticle, SPA). The old
main files `problem131_chains.tex` and `problem131_chains_sn.tex`, the forward sections, the
appendices, the figures, the forward scripts and their outputs, and the old ledgers were deleted
from `paperC2` (they remain in `paperC`). Nothing outside `paperC2` was changed apart from this note.

## Title

"What the occupation law of a finite Markov chain determines: principal minors, modal supports and
cycle trees".

Alternatives.
1. "Which coarse functionals of the occupation law determine a Markov generator?"
2. "The Donsker and Varadhan functional, principal minors and the identifiability of Markov
   generators"

## Table of contents (build of October 24, 41 pages)

1. Introduction (Theorems D, E, F, G, with the lettering continuing C1's A to C)
   1.1 The Donsker and Varadhan functional (Theorem D). 1.2 Modal supports (Theorem E, the
   retention paragraph, what is borrowed and what is new). 1.3 A reversible design and finite
   horizons (Theorem F). 1.4 Low temperature and the cycle tree (Theorem G, with its own
   paragraph on the question it settles). 1.5 Related work. 1.6 Plan.
2. Setting and results from the forward theory. 2.1 Setting. 2.2 Imported results (Lemma 2.1,
   Lemma 2.2, Proposition 2.3, Lemma 2.4, Theorem 2.5, Definition 2.6, Proposition 2.7, Theorem
   2.8, Theorem 2.9).
3. The Donsker and Varadhan functional and the principal minors. Lemma 3.1 (irreducibility,
   now by citation), Lemma 3.2 (Perron branch), Theorem 3.3 (J_V and the minors), Remark 3.4
   (survival probability), Theorem 3.5 (generator fiber, parts (a) to (d)), the four-state
   cut-transpose example, Remark 3.6 (three states), Proposition 3.7 (stationary start),
   Proposition 3.8 (amplitudes).
4. Modal supports. Proposition 4.1 (controlled score law), Lemma 4.2 (strict regions),
   Definition 4.3 (controlled boundaries), Lemma 4.4 (suppression), Lemma 4.5 (exposure), Proposition
   4.6 (identifiability), Theorem 4.7 (modal supports and minors).
5. A reversible design and finite horizons. Lemma 5.1, Theorems 5.2, 5.3, Remark 5.4, Theorem
   5.5, Proposition 5.6 (imported), Theorem 5.7, Remarks 5.8 and 5.9.
6. Low temperature and the cycle hierarchy. Theorems 6.1, 6.2, Proposition 6.3, Theorem 6.4,
   Examples 6.5, 6.6, Proposition 6.7, Lemmas 6.8 to 6.10, Theorems 6.11 to 6.13, Remark 6.14.
7. Computations and open questions.
Data and code availability, Funding, Declaration of competing interest, Acknowledgments,
References (25 entries, alphabetical, numbered).

## What is imported from C1

`paperC/EXPORTS.md` appeared during the work, so all numbers are filled in (no `% C1 number`
placeholder remains). C1 is cited as `\cite{paperC1}`, "A. Pemmasani, Occupation counts of rarely
switching Markov chains, in preparation, 2026". EXPORTS.md gives C1's full title as "Occupation
counts of rarely switching Markov chains: stratified local laws, crossings and the boundary
layer". The bibliography uses the short title as instructed, and the C1 editor may still change
the subtitle.

| C2 statement | C1 number | Content |
|---|---|---|
| Lemma 2.1 | Lemma 2.2 | admissible faces |
| Lemma 2.2 | Lemma 3.2 | monotonicity of the exit rate in the face |
| Proposition 2.3 | Propositions 3.1 and 3.4 | restriction identity, variational formula, reversible form |
| Lemma 2.4 | Lemma 4.1 and (6) | upper bound with the Perron tilt |
| (2.2) | (1) | singleton atom |
| Theorem 2.5 | Theorem 4.2 and Remark 4.3 | first-order selection with a field |
| Definition 2.6 | Definition 5.1 | tilt and constant K_F(v) |
| Proposition 2.7 | Proposition 5.2 and the text after Definition 5.1 | analyticity, Hessian, Perron vectors at alpha*(v) |
| Theorem 2.8 | Theorem 5.7 | face maxima with a field |
| Theorem 2.9 | Theorem 5.6 | stratified local law |
| Proposition 5.6 | Proposition 5.16 | uniform face maxima on the class |
| text in 6.4, 3.4, 7 | Theorems 4.4, 5.8, Lemma 2.3 | convex hull, crossing equation, run expansion |

Proposition 5.6 was first kept in C2 with its proof, since it was not clear that C1 would keep it.
EXPORTS.md lists it as C1's Proposition 5.16, so C2 now imports it and keeps a two-sentence
summary of the compactness argument.

## The author's instructions

1. `def:controlled` (Definition 4.3, with Lemma 4.2). The ambient space is
   Omega = (0, infinity) x R^d. The strict set S_Q is open and dense with closed nowhere dense
   complement, W_Q is locally constant and shift invariant (Lemma 4.2). Two generators have the
   same controlled boundaries if W_Q = W_Q' on S_Q cap S_Q'. The remark after the definition shows
   this is agreement outside a closed nowhere dense set, that failure means an open set of
   disagreement, and that agreement on the open quadrant (0, infinity) x (-infinity, 0)^d is
   equivalent. The definition has no threshold. The thresholds are in Lemma 4.4 (bar v_0
   depending only on Q, F, the compact set K and eta, with the explicit bound
   q_max/epsilon + max|rho_P| + eta) and in Lemma 4.5 (depending on Q, F and v^0). The suppression
   lemma now allows v_j <= -bar v_0 rather than v_j = -bar v, so the sets O of the exposure lemma
   are open in Omega. Each step of the induction was checked against this version. Irreducibility
   of Q' uses the open region where V wins and the density of S_Q'. The singleton step uses an
   open slab argument. The face step uses density of S_Q' in O and continuity of the scores to get
   the tie on the hypersurface. Done.
2. `thm:nonreversible`(d) is now part (c), stated for an irreducible Z-matrix with the principal
   minors of -Q, and the paragraph after the theorem gives the counterexample 3I - P. Done.
3. v = 0 is excluded. Proposition 3.8(b) says the exceptional set of fields is closed and nowhere
   dense and always contains v = 0, where every generator has r = 1, l = pi and a_V(0) = 1. Done.
4. Survival probability (Remark 3.4). It now proves that a generator with the same survival
   probabilities is irreducible. A reducible Q' would have lambda'_V = lambda'_C on an open set,
   independent of v_j for j outside C, while d lambda_V / d v_j < 0. Done.
5. Observation model. Theorem D comes first, in the introduction and in Section 3, with the data
   first. The modal-support result is Section 4. We did not find an honest setting in which the
   modal support is observed and the survival probability is not. The most likely composition has
   probability N^(-Phi + o(1)), so locating its face from independent runs needs far more runs than
   estimating the survival probability e^(-T lambda_V(v)). A set of visited states from many short
   runs gives face masses, which is a probability estimate and a different functional (the mass of
   a face behaves like e^(-T lambda_F) without the N^(-(k-1)) entropy factor). The paper says this
   plainly (Section 1.2, "We should say plainly ...") and frames Theorem E as retention. The forward
   theory, or any exact optimizer that reports only a maximizer, outputs the label, and the label
   loses nothing that J_V keeps. Done, with the retention framing.
6. Identifiability proposition (Proposition 4.6). The induction is out of the exposure lemma.
   Lemma 4.5 now states only the geometry of the boundary and refers to Proposition 4.6, which
   states both forms (same boundaries gives same minors, and different minors give an open set of
   different strict winners). Done.
7. Introduction, "What is borrowed and what is new" (Section 1.2). It starts with the data
   (Theorem 3.3 reads the minors off J_V, Theorem 4.7 off the modal-support map through the
   exposure and Perron-branch lemmas), states the borrowed fiber correctly (no-cut condition,
   Al Ahmadieh's converse, cut-transposes of CGGR Theorem 1.1), and argues the exposure lemma as
   the main contribution and the translation to generators as the second, shortest one. The
   sentence "known up to diagonal similarity and transposition" is gone. Done.
8. Al Ahmadieh check. See below. Lemma 3.1 is now proved by citation. Done.
9. Notation. Exit differences d_i are now x_i (the singleton switches were already x_i), so d is
   only the number of states. The design field delta is now xi and bar delta is bar xi, so delta is
   only the width in the exposure lemma. The test value xi in the suppression proof is epsilon. The
   block E in the reversible suppression proof is Z (E is the edge set). D_N(T) in the
   finite-horizon proof is Lambda_N(T), and the diagonal similarities in (R) and in parts (b) to
   (d) are E, so D stays a diagonal matrix of a vector (D_pi, D_x, D_phi) and the depth in Section
   6. The step size h = T/N no longer appears anywhere (written T/N), so h is only the height of
   Section 6. Catoni's domain D is now O, the uniformization constant c is varkappa (c is the reward
   amplitude), the limiting window score J_{gamma,x} is \mathcal J_{gamma,x} (J is the functional),
   and the 3-cycle products are omega, omega'. tau is the time scale throughout Section 4 and 5,
   with tau_1(v) the boundary value of tau and tau_0 a fixed design value. In Section 6 tau_{F^c}
   is still a hitting time, as in the joint paper, and that section never uses tau for a time
   scale except in tau_eta = e^(h/eta) at its start. Done for Sections 3 to 5, as the referee asked.
10. Low temperature. The remark after Theorem 6.2 now says the lower-order terms may decide but
    need not, and that in the symmetric case (two disjoint cycles from the same costs with a
    symmetric start) nothing at any order separates them, so the theorem then places the mode on
    one of the tied cycles and Section 6.2 treats such ties as unobserved. In Lemma 6.9 the
    uniformization bound is now d - 1 + max(c, 1) with varkappa > d + c, which covers V_ij = 0 and
    gamma = 0. The proof of Theorem 6.1 also states the bound d - 1 for the exit rates there. Done.
11. Finite horizon. One sentence after Theorem 5.7. The design runs to tau = U = 8R/b^2 and needs
    T q_max <= N, so the admissible range of N already grows like b^(-2), and in exact computations
    on three-state chains the faces with a suppressed state come closest near N of order bar v T.
    This is what 03_T5_numerics.md supports, with no numerical value claimed. Done.
12. Verification. Kept `verify_reconstruction.py`, `verify_finite_horizon.py`, `verify_cycles.py`,
    `verify_attraction.py` with `attraction_core.py`. No other script serves Theorem D or the fiber
    theorem (the three-state fibers, cut-transposes and the Perron-branch derivative are inside
    `verify_reconstruction.py`). Deleted the seven forward scripts and `verify_sticky_fisher.py`
    and their outputs. `verify_all.py` runs the four. Docstrings updated to the new labels
    (`thm:nonreversible`(c) and (d), `rem:three-states`, xi_bar, the C1 run expansion). Run of
    `py -I verify_all.py` on October 24: all four PASS (169 s). sha256 of the scripts in the
    output headers: verify_reconstruction 9a87e383..., verify_finite_horizon 9f4ed516...,
    verify_cycles 0a14daa6..., verify_attraction 465cf418.... No hash is quoted elsewhere.

Theorem 7 (now Theorem G, Theorems 6.11 and 6.12) is in the abstract and has its own paragraph in
Section 1.4. The paragraph says what question it settles. The noncycle window shows that modal
winners need not be cycles, so it was open whether the modal supports determine the cycles at all.
The unperturbed path and the killing design both fail, and the calibrated reward settles it
positively. We do not claim that the question was posed in the literature.

## The referee's other items, as far as they concern C2

- Interface not stated. Section 2 states it, and the plan of the paper says nothing else enters.
- Identifiability induction hidden. Proposition 4.6 (item 6).
- Observation model. Item 5. Question 2 of the referee is answered in the paper: we know of no such
  setting.
- Borrowed and new. Item 7.
- `def:controlled`, `thm:nonreversible`(d), v = 0 in (f), irreducibility of Q', the tie remark and
  the uniformization bound. Items 1 to 4 and 10.
- Notation. Item 9. The orientation of the score between the complete graph and Section 9 no longer
  arises, since the complete graph is in C1.
- Citation pointers. The Kim and Landim entry now lists exactly the statements cited (Lemmas 5.1,
  5.2, Corollaries 5.3, 5.8, Example 5.4, numbered as in arXiv v2). The quoted results of paperA,
  "incorporates" for paperB and Good's exponent concern C1 only and do not appear in C2.
- "Read off the cycle tree" is now tied to Theorem G, whose statement lists exactly what is
  determined.
- Hypothesis L, the Bessel claim, the heuristic before `thm:simplex-balance` and the identity in
  `sec_boundary.tex` are C1 matters and are not in C2.

## The Al Ahmadieh check (item 8)

Read on October 24 from arXiv:2309.00806v2 (A. Al Ahmadieh, "The fiber of the principal minor map",
8 Sep 2023), Section 5 and the statements it uses. Lemma 5.1 says, for an n x n matrix A with
entries in any field F, that A is irreducible if and only if f = det(diag(x_1, ..., x_n) + A) is
irreducible. There is no restriction on n. Its proof uses Lemma 4.2 (Hartfiel and Loewy 1984,
Theorem 1, every entry of the adjugate of diag(x) + A is nonzero for irreducible A), Theorem 2.3
(the Rayleigh difference Delta_ij(f) = G_ij G_ji) and Lemma 2.2 (Delta_ij(f) = 0 exactly when f
splits). Corollary 5.6 (fiber of an irreducible matrix consists of irreducible matrices) is stated
for n >= 4 but follows from Lemma 5.1 for every n. Theorem 5.2 relates the irreducible factors of f
to the strongly connected components.

So our lemma is the case F = C, A = -Q_F of Lemma 5.1, after the change of variables x = -w,
R_F(w) = det(diag(-w) + A). Lemma 3.1 of C2 is now proved by this citation in four lines, with the
reducible case from the block triangular form, and the paper names the Hartfiel and Loewy input.
The old direct proof by minimal crossing cycles was removed. The remark that the case A = -Q of
Corollary 5.6 needs n >= 4 is replaced by the observation that Lemma 3.1 gives it for every n.
Our own short argument in Theorem 3.5(a) for the irreducibility of fiber members is kept, since it
uses only the positivity of proper minors. We did not search further sources, since the statement
was found in the source the referee named.

## SPA format facts

Source: the SPA guide for authors at
https://www.sciencedirect.com/journal/stochastic-processes-and-their-applications/publish/guide-for-authors,
read on October 24, 2026. Details and our choices are in `paperC2/TEMPLATE.md`. In short, research
papers are expected to be 30 to 40 pages, with a justification in the cover letter if longer. The
review is single anonymized with at least two reviewers. The abstract has at most 250 words and no
references (author and year if essential). There are 1 to 7 keywords. Highlights (3 to 5 bullets of
at most 85 characters) are encouraged. References are numbered in square brackets, listed
alphabetically. Acknowledgements go directly before the references. The journal asks that the key
steps of the main proofs be outlined before details. Funding must be declared (a standard sentence
if none), competing interests through the declarations tool, and arXiv posting at submission is
strongly encouraged. The guide says nothing about MSC codes, and we give the 2020 codes with
`\MSC[2020]` of elsarticle.

The abstract has 247 words by a whitespace count, with "Kim and Landim (2025)" as its one
reference.

## Page count

41 pages in `elsarticle` with `preprint,12pt` and 1in margins, one over the guide's 30 to 40. The
cover letter gives the reason (the low-temperature section with its three cycle lemmas and two
examples). Cuts made to get there from 42: the related-work paragraph, the direct irreducibility
proof (now a citation), the discussion after Theorem 6.13, Remark 6.14, the three-state remark,
the paragraph on the observation model in Section 4.1, and the proof of the uniform face maxima
(now imported). Further candidates if the author wants 40 or fewer: Example 6.6 (branch switch),
Remark 5.4 (partial data), and the four-state cut-transpose example (both checked by scripts, so
their docstrings would need updating).

The build has no undefined references, no multiply defined labels and no overfull boxes. The
auxiliary files were deleted and the PDF kept.

## Declined or left open

- No item was declined.
- The notation in Section 6 keeps tau_{F^c} for hitting times (item 9 asked for Section 9, now
  Sections 3 to 5).
- The cut-transpose example and Example 6.6 were kept although they cost space, because scripts
  check them.
- The highlights file is not created. A proposed text is in `TEMPLATE.md`.
- The cover letter has a placeholder for the arXiv number of C2, and says C1 will be posted first.
