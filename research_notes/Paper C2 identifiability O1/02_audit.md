# Paper C2, (O1): audit of `01_report.md`

Date: 2026-10-25. Object audited: `01_report.md` and its four scripts in this folder.
Context read: `kagey-problems/problem131/paperC2/sec_minors.tex` (working tree; Lemma 2.1,
Corollary 2.5 = `thm:nonreversible`, the cut-transpose (eq:cut-transpose), Remark
`rem:stationary`, Proposition `prop:amplitudes`). Verdict and confidence wording in the
report was ignored; only the mathematics was judged.

Independent checks were run with my own code, exact (sympy rationals and `fractions`),
`py -I`, in a scratch folder outside the repo (`audit/a1.py`, `audit/a2b.py`). They do not
reuse any function from the report's scripts. What they compute is stated under each claim.

## Summary of verdicts

| # | Claim | Verdict |
|---|---|---|
| 1 | Memoryless-block reversal keeps the stationary law; d = 5 counterexample to "up to reversal" | **Proved as written** (general statement and example both confirmed) |
| 2 | One T suffices, any start (Theorem 1) | **Proved as written**, two routine steps stated too briefly (below); no gap in substance |
| 3 | (b) generic start gives Q (Theorem 2) | **Proved as written** |
| 4 | (c) second moments: d <= 4 to T^4 for all Q; generic to T^5 (Theorem 3) | **Proved as written** |
| 5 | Corrected (a): d <= 4, no cut, generic (Theorem 4) | **Proved as written** |
| 6 | Gluing formula and the balance criterion (Proposition 5) | **Proved as written** |

Side errors found (do not affect any claim): Lemma 1.1(iv) drops a term, see Claim 2.

---

## Claim 1. Reversal inside a memoryless block

**Card.** Q irreducible, B a set of states with 2 <= |B| <= d-1, kappa > 0, nu a law on
B^c, c >= 0 on B^c, with q_iy = kappa nu_y (i in B, y not in B) and q_yi = c_y pi_i/pi(B).
Q^[B] := Q with Q_B replaced by D_B^{-1} Q_B^T D_B. Claim: F_{Q^[B]} = F_Q, hence the same
stationary law of O(T) for all T and the same count laws of I + hQ for all N, h.

**My derivation (before reading Theorem 6).** Probabilistic route.
1. Flux across B: kappa pi(B) = sum_y pi_y c_y. Balance at j in B:
   (pi_B Q_B)_j + pi_j (sum_y pi_y c_y)/pi(B) = 0, so pi_B Q_B = -kappa pi_B. Rows of Q_B sum
   to -kappa. So R := Q_B + kappa I is a generator on B with stationary law pi_B/pi(B).
2. Exit from B happens at rate kappa from every state, to nu, independent of the state.
   Entry lands with law pi_B/pi(B), which is stationary for R. So the process decomposes:
   the "macro" process (time in B^c, B-sojourn start times and lengths, entry and exit
   points) has a law that does not involve the internal dynamics R, and given the macro
   process the internal paths of the B-sojourns are independent stationary R-paths on
   intervals of the given lengths. The sojourn at time 0 (if X_0 in B) also fits: X_0 has
   law pi_B/pi(B) given X_0 in B, and the residual sojourn is Exp(kappa) by memorylessness.
   The last sojourn is truncated at T by a time that is a function of the macro process
   only.
3. The occupation vector of a stationary R-path on a fixed interval has the same law as
   that of the reversed path, which is a stationary R*-path (path reversal; no
   irreducibility of R is needed, only pi_B > 0 stationary).
4. Q^[B] has internal generator R* - kappa I and the same cross rates, so the same macro
   law. Hence O(T) has the same stationary law under Q and Q^[B] for every T.
5. Discrete: I + hQ^[B] = (I + hQ)^[B], and the same argument (or Lemma 1.1(ii), checked
   below) gives every N and every admissible h, in particular h = T/N.

So the general block statement is **true**. The report's own proof (Theorem 6) is a
different, algebraic route; I checked it too.

**Implications checked in Theorem 6.**
- Step 1 identities: match mine. Correct.
- Step 2, Q^[B] is a generator with law pi: rows of Q*_B sum to -kappa, columns j in B
  receive pi_B Q*_B = -kappa pi_B plus inflow kappa pi_j. Correct. Irreducibility is
  asserted without proof; it holds (every state of B exits, entry hits every state of B,
  and the B^c-level dynamics are unchanged). Minor omission.
- Step 3, |B^c| = 1: q*_iy = pi_y c_y / pi(B) = kappa, so Q^[B] = Q*. Correct.
- Step 4: in symmetrized coordinates G_iy = e_i kappa nu_y / e_y and
  G_yi = e_y c_y e_i / pi(B), so both x1 and x2 are proportional to e_B; after the
  normalization x1.e = x2.e they are equal, p1 = theta E_B = p2, and Proposition 5 gives
  F_Q = F_{flip_{B^c}Q}. With x1 = x2, (flip_{B^c} G)^T = G with A -> A^T, and
  e^T (Lam - H^T)^{-1} e = e^T (Lam - H)^{-1} e. Desymmetrizing A^T gives Q*_B. Correct.
  (Proposition 5 is pure algebra and does not need |X|, |Y| >= 2.)
- Equality cases: Q^[B] = Q iff Q_B is pi_B-reversible; automatic for |B| = 2 since R is a
  two-state generator. Q^[B] = Q* iff y1 = y2 and B_{YY} symmetric, i.e. the side B^c is
  symmetric. Correct.
- "Probabilistic reading" paragraph: agrees with my derivation.
- Lemma 1.1(ii) (generating function of counts): sum_N y^N mu (ZP)^{N-1} Z 1 =
  mu((yZ)^{-1} - P)^{-1} 1, and Lam - I - hQ = h((Lam - 1)/h - Q). Correct.

**Independent check of the d = 5 example** (`audit/a1.py`).
- Q as described (B = {1,2,3}; inside q12 = q23 = q31 = 2, reverse 1; B -> 4 at 1, B -> 5
  at 2; 4 -> i at 1, 5 -> i at 2; q45 = 1, q54 = 4). Rows sum to 0;
  pi = (4/21, 4/21, 4/21, 2/7, 1/7). kappa = 3, nu = (1/3, 2/3), entry uniform = pi_B
  normalized: memoryless.
- Q^[B] is Q with the B block transposed. pi Q^[B] = 0, rows sum to 0.
- Q^[B] != Q, Q^[B] != Q*, Q* != Q: all true.
- Stationary Laplace transform. Using the matrix determinant lemma,
  pi adj(A) 1 = det(A + 1 pi) - det A with A = diag(lam) - M, I computed numerator and
  denominator polynomials of F_M(lam) = pi (Lam - M)^{-1} 1 for M = Q, Q^[B], Q*. The
  denominators agree (so all 31 principal minors agree, also checked one by one), the
  numerators agree identically. After the substitution lam = s 1 + w the numerators and
  denominators of pi (sI - Q + W)^{-1} 1 agree identically in (s, w_1..w_5). The lemma was
  spot-checked against a direct solve at a rational point.
- Nontriviality: from the start e_1 the numerators of e_1 (Lam - Q)^{-1} 1 and
  e_1 (Lam - Q^[B])^{-1} 1 differ, so the law does see the difference off the stationary
  start (consistent with Theorem 2).
- Discrete counts, exact enumeration over (state, count vector) with `Fraction`, start pi:
  P = I + hQ versus I + hQ^[B] (and I + hQ*), for h = T/N with T = 1/10 and T = 1/20,
  N = 1..7, and for fixed h = 1/10, N = 1..7. All laws equal.

**Generality check** (`audit/a2b.py` part 1). Three random rational d = 6 chains with a
memoryless block of size 3 (R random on B, rho its stationary law, entry c_y rho_i,
random B^c block): pi Q^[B] = 0, Q^[B] != Q, Q*, and F_Q = F_{Q^[B]} exactly at 4 random
rational points each; the e_1-start transforms differ. Consistent with the general
statement.

**Verdict: proved as written.** The counterexample to "stationary occupation law
determines Q up to reversal" is valid.

---

## Claim 2. One T suffices (Theorem 1), and Lemma 2.1

**Card.** Q irreducible, Q' any generator, starts mu, mu'. Equal law of O(T0) at one
T0 > 0 implies Q' has the principal minors of -Q and F^{mu'}_{Q'} = F^{mu}_Q.

**My derivation of the critical step.** The law at T0 gives h(w) = mu e^{T0(Q-W)} 1 on
R^d, entire. Along w = t v with v having distinct entries and v_1 minimal, all other
exponentials are e^{-ct} smaller than the one for the eigenvalue near -t v_1, and
e^{T0 t v_1} h(tv) is an analytic function of 1/t near 0 up to O(e^{-ct}); an analytic
function of u = 1/t that is O(e^{-c/u}) vanishes, so that analytic piece is determined.
This gives C_1 e^{T0 mu_1} on an open cone. The ratio of the two such pieces is
e^{T0(mu_1 - mu'_1)} = (algebraic), and exp of a nonconstant algebraic function has an
essential singularity at a pole, so mu'_1 - mu_1 is a constant c. Spectra then force c = 0
(-c in spec Q gives c >= 0, c in spec Q' gives c <= 0). This is the report's route.

**Implications checked.**
- Lemma 2.1: P(s,w) = R(-(s1+w)) with R irreducible (paper Lemma 2.1, Al Ahmadieh); the
  linear change (s,w) -> (s, lam) preserves irreducibility and P does not involve s.
  N_mu has s-degree d-1 with leading coefficient mu.1 = 1. So N_mu/P is in lowest terms
  and the monic-in-s denominator is P, whose coefficients are the principal minors.
  Correct, and no full support is used.
- Step 2: eigenvalues and residues of Q - tV are analytic in 1/t (simple eigenvalues of
  Q/t - V near -v_i). Correct. Brief point: to get an open set U of w one needs the
  threshold t0(v) locally bounded in v; it is, since the eigenvalue separation is uniform
  on compact sets of v with distinct entries. Not stated, routine.
- Step 3: C = N_mu / dP/ds is not identically 0 on {P = 0} (degree argument at d simple
  roots). Correct.
- Step 4: the one-variable lemma (e^f = g with f, g algebraic forces f constant) is correct
  as proved: f, g are meromorphic on the compact Riemann surface of the branch, e^f = g
  continues off the poles of f, and a pole of a nonconstant f gives an essential
  singularity of e^f. Constancy on each complex line through a connected U gives a single
  constant c; c is real because mu_1, mu'_1 are real for real w. Correct.
- Step 5: P'(mu + c, w) vanishes on {(mu_1(w), w): w in U}, a real open piece; by
  analyticity in w this extends to an open subset of the complex hypersurface, then
  irreducibility gives P | P'(mu + c, .), and monicity in mu gives equality. The
  extension from real to complex w is not written; routine. Then Q' - cI and Q have the
  same principal minors, and the spectral argument gives c = 0. Correct. Irreducibility of
  Q' follows (paper Corollary 2.5(a) argument, or reducibility would factor P).
- Step 6: C' = C on the irreducible hypersurface, then partial fractions at simple roots
  with deg N < deg P. Correct.

**Side error (Remarks, Lemma 1.1(iv)).** The formula
E_pi[n n^T] = N D + sum_{k=1}^{N-1} h^k C(N+1, k+2) Sigma_k omits the k = 0 term: the
I-part of P^r contributes 2D for each r = 1..N-1 with weight N - r, i.e. N(N-1) D. The
correct formula is N^2 D + sum_{k=1}^{N-1} h^k C(N+1, k+2) Sigma_k. Exact check at N = 2,
d = 3 (`audit/a2b.py` part 3): E[n n^T] = 4D + h Sigma_1, not 2D + h Sigma_1. D is known,
so the conclusion of (iv) and the N = 2 remark are unaffected.

**Verdict: proved as written** (two routine steps, the local uniformity in Step 2 and the
real-to-complex extension in Step 5, should be one sentence each in a paper). The
discrete-time scope is correctly limited: one T with all N at fixed h is equivalent to
continuous time; one N alone is not enough.

---

## Claim 3. (b): a generic start gives Q (Theorem 2)

**Card.** For Q irreducible, Fib = generators with the principal minors of -Q (finite by
Corollary 2.5(a)). For mu outside Z = union over Q' in Fib \ {Q} of
{mu : mu.(v_{Q'} - v_Q) == 0}, equality of the law of O(T0) under (Q', mu) and (Q, mu)
implies Q' = Q.

**My derivation.** v_Q(lam) = (Lam - Q)^{-1} 1 = m + diag(m) Q m + O(m^3), m = 1/lam
(Neumann series). Component i of the second-order term is m_i sum_j q_ij m_j, so v_Q
determines every q_ij (diagonal through m_i^2). Hence v_{Q'} - v_Q != 0 and each Z_{Q'} is
a proper subspace; finitely many of them by finiteness of Fib.

**Implications checked.** Theorem 1 puts Q' in Fib and gives F^mu_{Q'} = F^mu_Q, i.e.
mu.(v_{Q'} - v_Q) == 0, i.e. mu in Z_{Q'}, unless Q' = Q. A proper subspace cannot contain
the affine hyperplane mu.1 = 1, so Z meets the simplex in a closed nowhere dense set.
Neither facemax nor full support of mu is used. Z depends on Q, so this is
identifiability at a fixed known start, which is the intended statement. The remark that
pi lies in Z_{Q*} and Z_{Q^[B]} agrees with Claim 1 and the paper's Remark
`rem:stationary`.

**Verdict: proved as written.**

---

## Claim 4. (c): second moments (Theorem 3)

**Card.** (i) d <= 4: pi, Sigma_1, Sigma_2 determine Q up to reversal for every
irreducible Q. (ii) Under multiplicity-2 nonzero eigenvalues of N = K^2 and connectivity
of the S-coupling graph on the eigenplanes, pi and Sigma_1..Sigma_3 do. (iii) The
conditions of (ii) hold off a closed nowhere dense null set of positive-rate generators
with given pi.

**My derivation.**
- E_pi[O_i O_j](T) = int_0^T (T - r)(pi_i P_ij(r) + pi_j P_ji(r)) dr, and
  int_0^T (T - r) r^m/m! dr = T^{m+2}/(m+2)!, so the T^{m+2} coefficient is Sigma_m/(m+2)!
  with Sigma_m = D Q^m + (D Q^m)^T = 2 D^{1/2} sym(G^m) D^{1/2}. Sigma_0 = 2D gives pi.
- sym(G^2) = S^2 + K^2 (SK + KS is antisymmetric). sym(G^3): words in S, K with an even
  number of K are the symmetric ones: S^3, SKK + KKS (symmetric together), KSK. So
  sym(G^3) = S^3 + SN + NS + KSK. Correct.
- K e = 0 and K' e = 0 (same pi). If K'^2 = K^2 = N, then |K'x|^2 = -x^T N x, so K' kills
  ker N, and K' commutes with N, so it preserves each eigenspace. On a 2-dimensional
  eigenspace with eigenvalue -sigma^2, an antisymmetric map squaring to -sigma^2 is
  +-sigma J. For d <= 4, K lives on e-perp of dimension <= 3, rank <= 2, at most one
  plane: K' = +-K, G' = G or G^T, Q' = Q or Q*.

**Implications checked.**
- (ii): P_k (K'SK') P_l = eps_k eps_l K_k S K_l and K_k is invertible on E_k, so
  P_k S P_l != 0 forces eps_k = eps_l. Uses only the data of Q; no condition on Q'.
  Correct.
- (iii): failure lies in the zero set of (discriminant of psi) x (constant term of psi) x
  prod_{k<l} ||P_k S P_l||^2 (a symmetric function of the planes, hence polynomial after
  clearing denominators). Pairwise nonvanishing is stronger than connectivity, which is
  fine for a sufficient condition. Real-analytic on the connected (convex) slice of
  positive-rate generators with given pi, so one witness suffices. Witness:
  S0 = -(I - e e^T) has off-diagonal e_i e_j > 0 and acts as -I on e-perp, so
  P_k S0 P_l = 0 for k != l; S1 = u u^T with u = sum f_i gives P_k S1 P_l =
  (f_{2k-1} + f_{2k})(f_{2l-1} + f_{2l})^T != 0; K with distinct sigma_k. G = S0 +
  eps S1 + delta K has e as two-sided null vector and positive off-diagonal for small
  eps, delta. Correct. Open and dense follow from the nonvanishing of a nonzero
  real-analytic function.
- The orders: Sigma_2 sits at T^4, Sigma_3 at T^5. Correct.
- The memoryless example as an exception to (ii) (planes not coupled) is consistent with
  Claim 1, since the full law cannot separate it.

**Verdict: proved as written.**

---

## Claim 5. Corrected (a) (Theorem 4)

**Card.** Equal stationary law of O(T0) at one T0 implies Q' in {Q, Q*} when d <= 4, when
Q has no cut, or when Q satisfies Theorem 3(ii).

**My derivation.** Theorem 1 (with mu = pi, mu' = pi') gives equality of the laws at all T,
so E O(T) = T pi' = T pi and all second moments agree; Theorem 3 applies for (i), (iii).
For (ii), Theorem 1 gives the principal minors, and the paper's Corollary 2.5(b) (Loewy
plus the normalization (N)) gives the fiber {Q, Q*} from the minors alone, for d >= 4;
d <= 3 is covered by Corollary 2.5(d), and in any case by (i).

**Implications checked.** All three routes are as above. The paper's definition of "no
cut" (every partition with |X|, |Y| >= 2 has a cross block of rank >= 2) is the one used.
The remark that the paper's d = 4 cut-transpose is separated already by Sigma_1 is
consistent with Theorem 3(i) (S' != S there) and with the report's d = 4 output.

**Verdict: proved as written.** Together with Claim 1, the correct form of (a) is "up to
reversal for d <= 4, for Q without a cut, and generically; false in general from d = 5".

---

## Claim 6. Gluing formula and balance criterion (Proposition 5)

**Card.** For a cut X | Y, in symmetrized coordinates G_XY = x1 y1^T, G_YX = y2 x2^T,
normalized x1.e = x2.e (then y1.e = y2.e). flip_Y G = [[A, x1 y2^T], [y1 x2^T, B^T]].
Then F_Q = E_X + E_Y + (p1 q1 + p2 q2 + alpha q1 q2 + beta p1 p2)/(1 - alpha beta) and
F_Q - F_{flip_Y Q} = (p1 - p2)(q1 - q2)/(1 - alpha beta).

**My derivation.** Lam - G = K0 - U V^T with U = [(x1;0), (0;y2)], V = [(0;y1), (x2;0)].
V^T K0^{-1} U = [[0, beta], [alpha, 0]]; e^T K0^{-1} U = [p1, q2];
V^T K0^{-1} e = [q1, p2]^T; (I - C)^{-1} = [[1, beta], [alpha, 1]]/(1 - alpha beta).
Woodbury gives the correction p1 q1 + beta p1 p2 + alpha q2 q1 + q2 p2, over
1 - alpha beta. The flip sends B -> B^T, y1 <-> y2: q1' = y2^T (Lam - B^T)^{-1} e = q2,
q2' = q1, beta' = beta, E_Y' = E_Y. The difference is
(p1 q1 + p2 q2 - p1 q2 - p2 q1)/(1 - alpha beta) = (p1 - p2)(q1 - q2)/(1 - alpha beta).

**Implications checked.**
- Normalization exists: (x1.e)(y1.e) = (x2.e)(y2.e) = -e^T A e > 0 (nonnegative nonzero
  factors, e > 0), and rescaling x_i by t, y_i by 1/t keeps nonnegativity.
- flip_Y G has e as two-sided null vector (I redid the four block identities with
  A e = -b x1, e^T A = -b x2^T, B e = -a y2, e^T B = -a y1^T). Correct.
- flip_Y G is -(paper's cut-transpose of -G) with (a, b, c, u) = (x1, y1, y2, x2), and its
  generator point is diag(e)^{-1} flip_Y G diag(e). Correct. Every cut-transpose
  generator point has stationary law pi: follows.
- Balance criterion: rational functions form an integral domain and 1 - alpha beta -> 1,
  so the law is kept iff p1 == p2 or q1 == q2. Zero-ness of p1 - p2 does not depend on the
  remaining joint rescaling. Correct. Since F is transpose-invariant, flipping X instead
  of Y gives the same criterion.
- Corollary 5.1: order 1 gives x1 = x2; order 2 gives coefficient
  e_i e_j (rho_j - rho_i)(A_ij - A_ji) of m_i m_j. Then A e = -b x1 = -b x2 = A^T e, so
  K_X e_X = 0, and a 2 x 2 antisymmetric matrix killing a positive vector is 0: a side of
  size 2 is balanced only if symmetric, so for d = 4 no nontrivial cut-transpose keeps the
  law. Correct.

**Independent check** (`audit/a2b.py` part 2). Random rational cut with |X| = |Y| = 3,
built in Q coordinates; the cut-transpose built from the paper's formula
(eq:cut-transpose) and its generator point from the null vector (no use of the report's
flip). With the Q-coordinate factors normalized by pi_X.a = u.1 and b.1 = pi_Y.c, and
p1 = pi_X M_X^{-1} a, p2 = u^T M_X^{-1} 1, alpha = u^T M_X^{-1} a, q1 = b^T M_Y^{-1} 1,
q2 = pi_Y M_Y^{-1} c, beta = b^T M_Y^{-1} c (M = Lam - Q block): Q' is a generator with
pi Q' = 0, and at 3 random rational points both the Woodbury identity and the gluing
identity hold with residual exactly 0, while F_Q - F_{Q'} != 0.

**Verdict: proved as written.**

---

## Items not graded

Conjectures A and B, the open (N, T) question and the prior-work section were not
audited. The numerical sign-propagation test in `check_second_moments.py` is floating
point and is evidence only; Theorem 3 does not depend on it.
