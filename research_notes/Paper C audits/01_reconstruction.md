# Paper C audit 01: Section "Reconstruction from controlled boundaries"

Scope: `paperC/sec_reconstruction.tex` up to (not including) the subsection "Finite horizons",
read against `sec_model.tex`, `sec_dv.tex` (Proposition `prop:variational` and Lemma
`lem:face-monotone` still have `\proofpending`), the statements of Lemma `lem:upper`,
Theorems `thm:first`, `thm:local`, `thm:facemax`, Proposition `prop:rate` and
Proposition `prop:constant`, and the proof of Lemma `lem:upper` in `app_torus.tex`.
Every proof was checked by hand. Literature checked against the texts: Chatterjee, Ghosh,
Gurjar and Raj, arXiv:2410.01961v1 (Theorem 1.1, Definition 2.10, Remark 2.11, Lemma 2.8,
which restates Loewy 1986 Theorem 1 and Hartfiel and Loewy 1984 Theorem 3); Al Ahmadieh,
arXiv:2309.00806v2 (Lemma 5.1, Corollary 5.6, Theorem 4.1, Lemma 4.5, Lemma 6.1, Theorem 6.2);
Kim and Landim, arXiv:2412.13515v2, Section 5 (Lemma 5.1, Lemma 5.2, Corollary 5.3,
Example 5.4). Loewy 1986 and Engel and Schneider 1980 are not on arXiv. Their content is
checked only through the restatements in the two arXiv papers above.

A small numerical check (random 4-state generator with a rank-one cut, and a random 3-state
generator) confirmed: the cut-transpose keeps all 15 principal minors (difference 1e-16);
its generator point has zero row sums, differs from both Q and Q* (by 0.12 and 0.11), has
Q'_X = Q_X and Q'_Y = Q*_Y to machine precision; lambda_V(v) agrees for Q, Q', Q* at random
fields; the null vector has the form (1_X, s_0 pi_Y); and the d = 3 identities hold.

Bottom line: I found no false statement and no gap that breaks a proof. The fixes are about
literature (one missing citation that changes a novelty claim), one scope gap in Theorem
`thm:nonreversible`(a), one citation whose exact hypotheses I could not check, the two
pending proofs, and notation.

---

## 1. Gaps ranked by severity

### Serious (fix before submission; they change what can be claimed)

**S1. Hartfiel and Loewy 1984 is missing, and part (e) is not new beyond (N).**
CGGR Lemma 2.8(1), citing Hartfiel and Loewy [HL84, Theorem 3], states: for n = 2 or 3 and
A irreducible, equal principal minors imply diagonal equivalence, over any field. With (N),
this gives Theorem `thm:nonreversible`(e) at once: -Q' is DAD^{-1} or DA^TD^{-1}, so Q' is Q
or Q*. The paper's proof of (e) is correct (and I recomputed the identities, see Section 2),
but the remark after the theorem attributes (e) to Kim and Landim Lemma 5.1 plus
det A_V = 0 and does not cite HL84. Add the citation, and say that (e) is HL84 plus (N), with
the explicit cycle-product proof as a self-contained alternative. The same remark should say
that Loewy's theorem needs n >= 4 and HL84 covers n = 2, 3, which is how CGGR combine them.

**S2. Theorem `thm:nonreversible`(a) only rules out irreducible competitors.**
The statement says the boundaries determine every principal minor, which means: among all
generators. The proof starts "Let Q' be an irreducible generator with the same controlled
boundaries", and the induction in Lemma `lem:exposure` also assumes Q' irreducible. A
reducible Q' is never excluded in writing. The fix is one sentence, since irreducibility
follows. V is a strict winner for Q at large tau and v = 0 (Lemma `lem:face-monotone`), so V
is a strict winner for Q' at the same points. Proposition `prop:controlled-score`, applied to
Q' with the same full-support start, makes V irreducible for Q'. The rest of the induction
never uses irreducibility of Q' (λ'_V(0) = 0 holds for every generator). Drop "irreducible"
from the first line of the proof of (a) and from the induction in Lemma `lem:exposure`, and
add this sentence.

**S3. The Engel and Schneider step in (d) ("if Q is reversible, the fiber is {Q}") rests on a
theorem whose exact hypotheses I could not check.** CGGR say that Engel and Schneider show
"principal minor equivalence of a symmetric matrix with another matrix implies their diagonal
similarity". That fits the use in the paper. But I could not see their Theorem 3.5 itself, so
I cannot confirm which matrix has to be "completely reducible", nor the theorem number. Two
replacements that I have checked:
- Al Ahmadieh Lemma 6.1 / Theorem 6.2(a) (n >= 4, any field): the fiber of an irreducible
  symmetric matrix is its diagonal-equivalence class, and transposition is trivial for a
  symmetric matrix. For d <= 3 use HL84 (S1) or part (e).
- A self-contained argument from the paper's own (d): if C is symmetric and C[X,Y] = -ab^T,
  then C[Y,X] = -ba^T, so c = b and u = a, and the cut-transpose of C is C itself. With the
  diagonal-similarity lemma in (d), every C_s in the CGGR sequence is diagonally similar to S,
  and transposition fixes S. So -Q' is diagonally similar to S, and (N) gives Q' = Q.
  This takes three lines and needs no outside citation. I recommend it.
Also note that Al Ahmadieh says Engel and Schneider Theorem 3.5 follows from her Theorem 6.2,
so cite it next to Engel and Schneider in any case.

**S4. Two proofs this section depends on are still pending.** Proposition `prop:variational`
is used in the lower bound of Proposition `prop:controlled-score` (an interior minimizer
alpha_v), in (f) (alpha*_F(v), and J'_F = J_F by Legendre duality) and in Corollary
`cor:dv-fiber` (both directions). Lemma `lem:face-monotone` is used in Lemma `lem:exposure`
(positivity of rho_H's denominator, and that V wins at large tau) and in (b). Both statements
are correct as written. One point for the writer of the variational proof: uniqueness of the
minimizer needs the boundary case, J_F - v.alpha >= lambda_{F'}(v) > lambda_F(v) on Delta_{F'}.
This is Proposition `prop:rate`(d) with Q_F + diag v in place of Q_F. The resolvent proof of
the lower bound in `prop:rate` carries over word for word. Lemma `lem:face-monotone` repeats
itself: "F, G irreducible faces and Q_G irreducible" says the same thing twice.

### Moderate (a reader will stop; the proof is right, but a step must be written)

**M1. Exposure induction: the ranges for the pair step depend on Q.** In the induction, the
pair step uses tau in a compact subinterval of (0, 1/(2 q_max)] and delta in an interval that
contains q_i - q_1 in its interior. To compare with Q', both choices must work for both
generators: tau <= 1/(2 max(q_max, q'_max)) and an interval containing q_i - q_1 and
q'_i - q'_1. Alternatively, argue that if Q' had its boundary at another delta, then the
strict winner of Q' would differ from that of Q at some point of a common range. One sentence.

**M2. Strict regions and observations.** "Same controlled boundaries" is defined as "same
strict winning regions". These regions are defined through Phi, not through what is
observed. The observation is the support of the mode for large N, and Proposition
`prop:controlled-score` gives it only where Phi has a unique minimizer. For the induction you
need: if Q' shows the label F on an open set where Q has F strictly, then Phi'(F) < Phi'(H)
on a dense subset there. This holds because for fixed v two faces of different sizes tie in
Phi' at only one tau, so the ties of Phi' are nowhere dense; continuity then gives the
inequality on the closure and the tie on the hypersurface. Either add this remark or define
the data explicitly as the Phi-strict regions and say that Proposition `prop:controlled-score`
links them to the observation.

**M3. The sign of alpha in the comparison with CGGR's cut-transpose (proof of (d)).** The
claim "alpha > 0" is true, but "both have nonnegative factors up to sign" does not prove it.
The check: in CGGR Definition 2.10, q is the first nonzero row of A[X,Xbar] and u the first
nonzero column of A[Xbar,X]. For a Z-matrix, q <= 0, p >= 0, u <= 0 and v >= 0, so CGGR's
ct(A,X) is itself a Z-matrix. The paper's version differs from it by
diag(gamma I_X, I_Y) with gamma = s t > 0, where p = s a and u_CGGR = -t c. Note also that
the sign is not needed. (N) accepts any real invertible D, and the block computation in (d)
holds for any real invertible diagonal matrix. Either write the two lines above or drop the
positivity claim.

**M4. The section intro says "when the graph has no cut".** A cut is a condition on the
ranks of the blocks of Q, not on its graph. A block with entries in two different rows and two
different columns has rank 2 for generic rates but can have rank 1 for special ones. Say
"when Q has no cut".

**M5. The remark after Theorem `thm:nonreversible`: the "third generator on four states" has
no example.** My numerical check confirms that such generators exist (random rates, cut
X = {1,2}). Print one explicit example, preferably with rational entries, since the
introduction will probably quote it.

**M6. Al Ahmadieh Theorem 4.1 holds for n >= 4.** The remark states it without this condition.

### Minor (wording, notation, constants)

- Theorem `thm:reversible-reconstruction`(a) says |x_i| <= 2R, while the proof uses and proves
  |x_i| <= R, since q_k lies in [0,R]. State R.
- Notation collisions in the section: `A_F` means the zero-diagonal switching matrix in
  `sec_model` and Lemma `lem:upper` (so in V_F), but -Q_F in `sec_dv` and in the
  non-reversible subsection. The paper flags this in the non-reversible subsection but not in
  `sec_dv`, where "A_F = -Q_F" is stated as if it were the old definition. Also: `h` is both
  T/N and the ground vector; `H` is both 2R and the generating function of `sec_model`; `M`
  is both the suppression constant and the face maximum M_F; `S` is both the symmetrized
  matrix and a subset in R_F; `U` is both 8R/b^2 and the open sets of Lemmas
  `lem:perron-branch` and `lem:exposure`; `beta` is both a polynomial coefficient and l∘r in
  Lemma `lem:perron-branch`; `\epsilon` and `\varepsilon` are two different small numbers in
  Lemma `lem:suppression-nr`; `s` means two things in the stability proof; `c` is both the
  shift in Lemma `lem:perron-branch` and the 3-cycle product. Rename at least the epsilon
  pair and beta.
- Proposition `prop:controlled-score`: it is worth one clause that the tilted radius is
  automatically positive (theta = A r / r with every row of the switching matrix nonzero,
  as in Step 1 of the proof of Lemma `lem:upper`). Full support of mu is used only in the
  lower bound and in the winner step, through Lemma `lem:admissible`(b) for the component C.
  It is not used in the upper bound.
- Proof of (d), Schur complement: say that the case U_X empty is trivial (both sides equal
  det C_{U_Y}).
- (f), the stationary-start obstruction: "for every N and T" needs h q_max <= 1, so that
  I + hQ and I + hQ* are stochastic. Under the paper's standing h q_max <= 1/2 this holds.
- Corollary `cor:dv-fiber`: the boundary argument is correct. Fenchel and Moreau would give
  it in one line, but the elementary version is fine.
- The comment block at the top of the file names scratch scripts and research-note paths.
  Move them before submission (these are drafting comments, not text).

---

## 2. Proof-by-proof record

**Proposition `prop:controlled-score`.**
- Tilted radius: theta_i = q_i - v_i - lambda_F(v) = sum_j q_ij r_j / r_i. The zero-diagonal
  switching matrix minus diag theta equals Q_F + diag v + lambda_F(v) I, whose Perron root is
  0. So theta lies in V_F, and theta > 0 automatically. The weighted bound follows from
  q - theta = v + lambda_F(v) 1 and sum n_i = N. C_theta does not depend on tau. Correct.
- Lower bound: J_F <= q_max (drop the subtracted terms) and J_F >= lambda_F >= 0. The
  Lipschitz argument through beta' = beta + rho (beta - alpha)/|beta - alpha| stays inside the
  3 rho ball, and convexity gives J_F(beta) - J_F(alpha) <= s q_max <= q_max |beta-alpha|/rho.
  The rounded point is O(1/N) from alpha_v, so its cost is lambda_F(v) + O(1/N).
  Theorem `thm:first`(i) applies on K, since F satisfies (H) under full support. Correct.
- Reducible faces: Q_F + diag v is still block triangular, so lambda_F(v) = min_C lambda_C(v).
  Lemma `lem:upper` is applied per block with start delta_{y_j}. The singleton block bound
  (1 - x)^{N-1} e^{x' N} <= e^{1/2} e^{-(q_i - v_i) h N_j} holds, and e^{1/2} < 2. The bound
  sum lambda_{D_j}(v) N_j >= lambda_F(v) N holds even if some lambda are negative. The powers
  of h add to k - 1. Phi(F) >= Phi(C) + 1 with C a minimizing component. C is admissible by
  full support. Correct.
- Winner step: correct.

**Lemma `lem:suppression`.** All constants check. Wholly suppressed:
tau (M - R) >= (3R + 4UR^2)/(4R) = 3/4 + UR. Mixed: ||E|| <= R, S_J >= 0, |e| <= 4R. The
2 x 2 bound lambda_min [[e,-R],[-R,M]] >= e - R^2/(M - e) holds through
sqrt(s^2 + R^2) <= s + R^2/(2s). M - e >= 4UR^2 gives the 1/(4U) loss and the 3/4 gap at
tau <= U. A non-edge pair gives a diagonal B, and G_* is the better singleton. The lemma
covers only connected F, which by Lemma `lem:admissible`(c) are all the admissible faces.
Correct.

**Theorem `thm:reversible-reconstruction`.**
- (a) Weyl gives lambda_pair >= min(q_i - delta, q_1) - sqrt(w). At tau_0 = 1/(2R) the pair
  loses by at least 1 - tau_0 R = 1/2, for every delta, so the pair never wins. tau_0 lies in
  [1/(4R), U] since b <= R. Correct.
- (b) s = H - Delta lies in [R, 3R]. The smaller eigenvalue of [[a,-sqrt w],[-sqrt w,c]] is
  a - g with g = (sqrt(s^2+4w) - s)/2 <= sqrt w. Phi(pair) - Phi({i}) = 1 - tau g, so the
  entry time is t = 1/g. The formula increases in s and decreases in w, which gives
  t <= (sqrt 13 + 3) R/(2 b^2), about 3.30 R/b^2, below U/2 = 4R/b^2. From
  (a - x)(c - x) = w at x = a - 1/t we get w = s/t + 1/t^2. Correct.
- (c) B = S - q_1 I. sqrt(pi) is the unit null vector, simple by Perron-Frobenius applied to
  R I - S (nonnegative and irreducible). Correct.

**Theorem `thm:minimality`.**
- (a) kappa∘Psi = id is checked: off-diagonal entries sqrt(w) h_j / h_i, detailed balance
  with h^2, exit differences d_i. Psi∘kappa = id by (c). The implicit-function Jacobian is
  invertible at a simple eigenvalue. Psi is an injective immersion with continuous inverse
  kappa, so an embedding of dimension m + d - 1. The rank argument holds: maximal rank rho is
  locally constant near x_0, Z has dimension p - rho >= 1, every df_s vanishes on TZ, and f
  is constant on the connected piece of Z. Correct.
- (b) The fiber in the chart is (0,inf)^{m-|J|} x (affine space of dimension c(K) - 1).
  Correct.
- (c) I recomputed: the rows sum to 0, w12 = w23 = 1, w13 = z^2, nu = (1, 4/l^2, 1) gives
  detailed balance, all exit rates equal l, and z > 0 for l > sqrt 2. Correct.

**Theorem `thm:stability`.** I rederived every constant.
- |1/s_hat - 1/s| <= (4/3) eps.
- |s_hat^{-2} - s^{-2}| <= (4/3)(4/3 + 1) eps = (28/9) eps.
- |a_hat/s_hat - a/s| <= (8/3) eps + 4 eps = (60/9) eps.
- Total: (88/9) eps < 10 eps.
- w_hat >= eta^2/2 when eps <= eta^2/20, and then |sqrt(w_hat) - sqrt(w)| <= 10 eps/eta.
- Row-sum bound: eps + (d-1) 10 eps/eta <= 10 d eps/eta = beta. For a symmetric matrix the
  2-norm is at most the infinity-norm.
- h_* follows from h_l >= sqrt(w_lk) h_k / q_l >= eta h_k.
- g_*: the Dirichlet form is sum c_kl (f_k - f_l)^2 with c >= eta h_*^2. With the variance
  identity and paths of length at most d - 1 this gives 2 eta h_*^2/(d - 1). In unscaled form
  this is 2 b h_*^2/(d-1), as stated.
- Ground vector: ||z|| <= 2 beta/g_*, and gamma <= sqrt2 ||z|| once ||z|| <= 1, which the
  final condition guarantees. h_hat_min >= h_*/2.
- Entry bound 20 eps/(eta h_*) + 4 gamma/h_*^2. Condition
  eps <= eta g_* h_*/(40 sqrt2 d). eps_0 = min(1/4, eta^2/20, that). All correct.

**Lemma `lem:RF-irreducible`.** Each variable lies in exactly one factor. The coefficient
identities det A_{S∪T} = g_S h_T are correct with the normalization g_∅ = h_∅ = 1. A minimal
crossing cycle U exists. Every non-preserving permutation with a nonzero term has a cycle
meeting X and Y, which by minimality is Hamiltonian on U. Its term is
(-1)^{|U|-1} (-1)^{|U|} prod q = -prod q. The difference is strictly negative because C
exists. Correct, over C. The citation to Al Ahmadieh Lemma 5.1 (any field, any n) and
Corollary 5.6 (n >= 4) is accurate.

**Lemma `lem:perron-branch`.** Both polynomials vanish on phi(U). The coefficient alpha of
w_1 in R~ has coefficient -1 at prod_{i>=2}(-w_i), so alpha is nonzero. The Jacobian of
y -> (phi(v^0 + (0,y)))_{i>=2} is I - 1 beta'^T, with determinant beta_1 > 0 by the
matrix-determinant lemma, where beta is the quasi-ergodic law of Q'_F + diag v. So the
projection contains an open set, and the w_1-free polynomial alpha beta' - alpha' beta
vanishes. R~ is prime, does not divide alpha, and every nonzero multiple of it has
w_1-degree >= 1, so R~ divides R'_F. The degrees and leading coefficients match. Last step:
smallest real root. Correct.

**Lemma `lem:suppression-nr`.** Collatz and Wielandt upper bounds hold for every Metzler
matrix. P empty: the row sums are <= -M. P nonempty: Dini applies, since the perturbed roots
decrease monotonically to a continuous limit on a compact set. The normalized Perron vector
is continuous and positive, so x_* > 0. Rows p: (Q_P + diag v) x <= (... + eps J) x. Rows s:
sum_p q_sp x_p <= q_max and -eps M. The condition
M >= q_max/eps + |rho_P| + eta suffices. Correct.

**Lemma `lem:exposure`.**
- rho_H is the crossing time.
- Generic partners: lambda_{H1} <= q_j - t and lambda_F >= -t give
  rho_{H1} >= (k - |H1|)/q_j while rho_{H2} -> 0. So E is closed and nowhere dense.
- Boundary: Phi(H) - Phi(F) = (lambda_H - lambda_F)(tau - rho_H) >= kappa. Reducible
  subfaces lose by 1. The faces outside F lose by 1/2 with eta = 1/(2 tau_+), through a
  component C of P with lambda_C = lambda_P. If P is empty, the loss is >= tau_- M.
- Induction: λ'_F = λ'_G - (|F| - |G|)/tau_1 = λ_F + c on U. Lemma `lem:perron-branch`
  extends this to R^F. lambda_V(0) = 0 fixes c.
Correct, subject to S2, M1 and M2.

**Theorem `thm:nonreversible`.**
- (N): the characteristic polynomial comes from the principal minors. -C is irreducible
  Metzler with spectral abscissa 0, so it has a positive null vector, unique up to scale.
  Uniqueness holds for any real invertible D'. Correct.
- (a): correct up to S2.
- (b): "no fiber point is reducible" is correct. A proper C gives det A_C > 0, because every
  component D of C has lambda_D > 0, so every eigenvalue of A_C has real part > 0. This
  contradicts det A_V = 0, and the argument works for any real matrix. Q* is a generator in
  the fiber. Finiteness: fewer than 2^d cuts per step and fewer than 2d steps.
- (c): Loewy's hypotheses as restated by CGGR Lemma 2.8(2) are: A irreducible, n >= 4, A has
  no cut (2 <= |X| <= n-2, both blocks of rank one), B arbitrary, over any field. Then A and B
  are diagonally equivalent with D over the same field. The paper's use matches exactly. The
  paper's "no cut" definition (|X|,|Y| >= 2, one block of rank >= 2) is the same condition.
- (d): the Schur-complement identity is correct. Both determinants equal
  det C_{U_X} det(C_{U_Y} - kappa c b^T), the second after transposition, with the same
  kappa = u^T C_{U_X}^{-1} a. The t-shift and polynomial-identity argument is sound. The
  diagonal-similarity lemma diag(D_X, D_Y) -> diag(D_X, D_Y^{-1}) is checked block by block.
  CGGR Theorem 1.1 assumes both matrices irreducible, over any field, k < 2n, and diagonal
  equivalence over the same field. The paper establishes irreducibility of Q' (b) before using
  it, and there is no circularity. See M3 on the sign and S3 on the reversible case.
- (e): recomputation. Expanding det(-Q) on three states gives
  det = q1 q2 q3 - q1 w23 - q2 w13 - q3 w12 - (q12 q23 q31 + q13 q32 q21).
  So det = 0 gives c + c' = q1q2q3 - q1 w23 - q2 w13 - q3 w12, and
  c c' = (q12 q21)(q23 q32)(q13 q31) = w12 w23 w13. Both match the paper, and both were also
  confirmed numerically. The arc-pattern and potential argument is correct. Q* has the pair
  (c', c). See S1 on priority.
- (f): det Sigma = 1/det Hess J_F (Proposition `prop:constant`(a)), so the Gaussian factors
  agree. r attains the supremum at alpha*_F(v) by the stationarity criterion, so
  K'/K = a'/a. For F = V: if g' = g, then (A' - A) r(v) = 0, and the limit v = t e_j gives
  r/max r -> e_j, hence A' = A. So W^⊥ is a proper subspace, which cannot contain an open
  piece of the simplex. Time reversal: r* = D_pi^{-1} l and l* = D_pi r, so a*_V = a_V at
  mu = pi. The path-reversal identity holds, which gives the exact stationary-start
  obstruction. Cut-transpose blocks: I verified the three identities, A'x = 0 for
  x = (1_X, s_0 pi_Y), Q'_X = Q_X and Q'_Y = Q*_Y. K_F depends on Q_F (exit rates included)
  and mu_F only. Correct.

**Corollary `cor:dv-fiber`.** The forward direction uses the variational formula and Lemma
`lem:perron-branch` with U = R^V. Converse: equal minors give equal lambda_V, Legendre
duality gives equality on the interior, and convexity with lower semicontinuity extends it to
the boundary. Correct, given Proposition `prop:variational`.

---

## 3. Verdicts

| Statement | Verdict |
|---|---|
| Prop. `prop:controlled-score` | Sound (minor: note theta > 0 is automatic; depends on pending Prop. `prop:variational`) |
| Lemma `lem:suppression` | Sound |
| Thm `thm:reversible-reconstruction` | Sound with listed fixes (state abs(x_i) <= R) |
| Thm `thm:minimality` | Sound |
| Thm `thm:stability` | Sound (all constants check) |
| Lemma `lem:RF-irreducible` | Sound |
| Lemma `lem:perron-branch` | Sound (rename beta) |
| Lemma `lem:suppression-nr` | Sound (rename the epsilon pair) |
| Lemma `lem:exposure` | Sound with listed fixes (S2, M1, M2; depends on pending Lemma `lem:face-monotone`) |
| Remark `rem:singleton-partner` | Sound |
| Thm `thm:nonreversible` (a) | Sound with listed fixes (S2) |
| Thm `thm:nonreversible` (b) | Sound |
| Thm `thm:nonreversible` (c) | Sound (Loewy used with exactly his hypotheses) |
| Thm `thm:nonreversible` (d) | Sound with listed fixes (M3; S3 for the reversible sentence) |
| Thm `thm:nonreversible` (e) | Sound; not new beyond (N) given HL84 (S1) |
| Thm `thm:nonreversible` (f) | Sound (state h q_max <= 1 for "every N and T") |
| Cor. `cor:dv-fiber` | Sound (depends on pending Prop. `prop:variational`) |

No statement is unsound.

---

## 4. What is new here (for the introduction)

Relative to Kim and Landim Section 5, which recovers exit rates and edge products from J_V
(Lemma 5.1), recovers a reversible generator assumed reversible (Corollary 5.3), and gives
the 3-cycle counterexample (Example 5.4), the new content is the exact description of the
information in J_V as the principal minors of -Q (Corollary `cor:dv-fiber`), and with it the
fact that J_V singles out a reversible generator among all generators, which their
Corollary 5.3 does not address. Relative to Loewy 1986, Hartfiel and Loewy 1984, Al
Ahmadieh's fiber theorems (n >= 4) and CGGR's cut-transpose characterization, all stated for
matrices up to diagonal equivalence over a field, the new linear-algebra content is the
normalization (N): each point of the orbit has exactly one positive diagonal similarity to a
generator, so the generator fiber is {Q, Q*} without a cut, {Q} for reversible Q, finite in
general, together with the computation that a cut-transpose acts as Q on X and as Q* on Y.
Parts (c) and (e) are, with (N), immediate from Loewy and from Hartfiel and Loewy
respectively, and the reversible case is immediate from Al Ahmadieh (or Engel and Schneider),
so the introduction should present them as corollaries of known theorems, not as new
identifiability results. The genuinely probabilistic novelty is the observation reduction:
the controlled score law with a tilted radius valid up to the face boundary, the explicit
design with constants from R and b alone (exact reversible reconstruction from m + d - 1
boundary coordinates, minimality, Lipschitz stability), and the descent through exposure
boundaries that turns strict-winner regions into lambda_F on every face and hence into all
principal minors. The amplitude statements in (f) (generic-start separation of fiber points
by K_V(v), and the exact stationary-start indistinguishability of Q and Q*) are new as far
as these texts show, but the separation concerns K_V(v), which the paper itself says cannot
yet be read off boundaries, so it should be claimed as a property of the local law, not of
the boundary data.
