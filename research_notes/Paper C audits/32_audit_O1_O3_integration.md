# 32. Audit of the O1 and O3 integration into Paper C1 (October 25, 2026)

Scope: the parts of `kagey-problems/problem131/paperC` that integration 30 wrote new, checked
against `Paper C1 discrete layer O1/02_audit.md` and `Paper C1 reducible faces O3/03_audit.md`.
Read: `app_counts.tex` in full, Sections 4.2 to 4.4 (`sec_firstorder.tex`), Theorems 5.4 to 5.8
and Proposition 5.12 with the diff against HEAD (`sec_secondorder.tex`), Theorem 6.1 with its
proof of (a) and Section 6.9 (`sec_boundary.tex`), Lemmas 4.1, A.3, A.4 and the proof of
Lemma 5.5 (`app_torus.tex`), the abstract, the introduction, Section 9 and `EXPORTS.md`.
Nothing in the paper was changed. One numerical check was run outside the repository (item 4).

## Verdicts

| Item | Verdict |
|---|---|
| 1. Lemma E.4 and its use in Theorem 4.5 | proved as written (one omitted line, 1c) |
| 2. Theorem 5.7(b) from 5.7(a) | the derivation is proved as written. Proposition 5.12(b), which is exported, is **incomplete**: its uniformity proof follows a proof of 5.7(b) that is no longer in the paper |
| 3. (H) lifted in Theorems A and B(ii) | proved as written. Every lifted statement is covered by Theorem 4.5 or Corollary 4.6. No place where (H) was dropped and is still needed |
| 4. Theorems 4.5, 6.11, 6.12, Corollary 4.6, Schwarz step | 4.5, 4.6, 6.12, 6.1(a) match the audited versions and are proved. **Theorem 6.11(c), second sentence, is false as written**; correct after restoring T <= N^(1/2) |
| 5. Abstract and introduction | nothing false. Two loose claims and two stale sentences (5a to 5d) |

## 1. The bridge maxima (Lemma E.4) and Theorem 4.5

**My derivation of the critical step.** Inside the ball U, Lemma E.3 gives
G_C(m)_yx = h^(k-1) Phi_C(hm)_yx (1 + O(s^2/l)), and Lemma A.4 with (nu, e) = (e_y, e_x) at t = s alpha
gives H(s alpha) = (2 pi s)^(-a) e^(s<alpha, theta(alpha)>) (r_y l_x)(alpha)/sqrt(det Sigma_alpha) (1 + O(1/s)).
Since Phi_C = e^(-<q,t>) H and J_C(alpha) = <q - theta(alpha), alpha>,
G = Y_yx (c_yx(alpha)/c_yx(alpha*)) e^(-s J^0(alpha)) (1 + E), |E| <= C_2(1/s + s^2/l), as written.
The product r_y l_x does not depend on the scaling of r and l, and r_alpha o l_alpha = alpha, so
c_yx(alpha*) uses r_C, l_C with l.r = 1, as in Y. The log of the middle factors is at most
g.xi + (C_1 - c_U s)|xi|^2 <= g.xi - (c_U s/2)|xi|^2 <= |g|^2/(2 c_U s) once s >= 2C_1/c_U.

**Implications checked.**
- (a) Outside U: J^0 is lower semicontinuous (a supremum of linear functions, the definition of
  J_C over u > 0 in Section 4.2, valid on the closed simplex, value +infinity allowed), positive
  on the compact E, so >= 3 eta. The cover by finitely many theta in V_C is right, and Lemma 4.1
  with start e_y (its constant depends on the start, finitely many y) gives
  C h^(k-1) e^(-s(lambda + 2 eta)) = Y O(s^((k-1)/2) e^(-2 eta s)) = Y O(1/s).
- (b) The maximum over supp m = C is automatic: G_C(m) is defined only for m in Z_{>=1}^C. This is
  the restriction of audit 03 (the counterexample m = l e_y is excluded by the definition), and
  B2 uses n^(j), which has full support.
- (c) Part (ii): |xi| <= sqrt(k)/l <= k/l, Lipschitz bound and s J^0 <= C_U k^2 s/l^2. Correct.
- Lemma E.1: Theorem 5.7(b) with start e_y on C_j (which satisfies (H) for that start), l = sN/T
  >= N^(2/3), s^3 <= l iff s^2 T <= N. The exponent arithmetic l^(-(k-1)) s^((k-1)/2) =
  h^(k-1) s^(-(k-1)/2) is right.
- Theorem 4.5, upper bound, cases A, B1, B2 and k* = 1: each step checked. In B2 the range of
  Lemma E.4 holds (N_j >= N/2, s_j^2/N_j = s_j T/N <= T^2/N), the h-count
  kappa_< + kappa_> + k* - 1 = k_F - 1 is right, and A_j B_j/(...) <= K closes it. For k* = 1 the
  flat scalars factor out and the product splits at a flat j in S*, so Psi* = A_j B_j for every
  flat j in S*, hence all such products equal K.
- Lower bound: entrywise use of Lemma E.2 (take w = e_y), s + |hn^<| + |hn^>| = T, s^(-a) >= T^(-a).
  Correct.
- 1c, omitted line. For k* = 1 the lower bound "treats the blocks that are not flat in the same
  way", which needs a maximizing point of Psi* over the non-flat times. The text states
  attainment only for k* >= 2. It holds for k* = 1 too: after the flat factors are set to 1, each
  remaining factor is bounded by C_0 w~ <= C_0 and the one whose time grows tends to 0, so the
  function tends to 0 at infinity. One sentence. (A near-maximizer within h would not do, since its
  times could grow as h -> 0.)

The worked constant K^red = sqrt(2/pi) for {1} -> {2,3} (Sigma = 1/4 for the symmetric pair with
rate 1) and K^red_{1,2} = b in Example 5.11 agree with the definitions, and Corollary 4.6 with
pi = 1, kappa = log b, delta = b - 1 and with pi = 0, delta = 1 reproduces Example 5.11(ii), (iii)
including the constants.

## 2. Theorem 5.7(b) from 5.7(a)

**My derivation.** With K^(h)(v) = K(v)(1 + O(h)), lambda^(h)(v) = lambda(v) + O(h) and
alpha^(*h)(v) = alpha*(v) + O(h) uniformly on V (Proposition 3.6(c), Lemma A.6), the value of (a)
is N^-(k-1) T^((k-1)/2) K(v) e^(-T lambda(v)) e^(O(Th)) (1 + O(h)). For T <= N^(1/3), Th = T^2/N <= 1
and h <= T^2/N, so this is (1 + O(T^2/N)) times the claimed value. The maximizer is within
O(1/T) + O(h) of alpha*(v), and h <= 1/T. The range of (a) holds since h <= N^(-2/3) <= h_*. The
singleton case and (9) follow. **Proved as written.**

Side remark: the same lines give 5.7(b) and 5.6(b) for T <= N^(1/2), since only Th <= 1 and h <= 1/T
are used. So the paragraph "Where the cube root came from" and the introduction sentence "The range
T <= N^(1/3) of the continuum form comes from the step that locates the most likely counts, which
needs T^2/N <= 1/T" describe the proof that was removed. They are not false about the
statements, but they no longer describe the proof in the paper.

**What lost its proof.** Proposition 5.12(b) (`prop:uniform-facemax`, exported to paperC2). Its
proof says that part (b) is Theorem 5.7(b) for fixed (Q, mu), and then makes the constants uniform
on P x K_0 by going through (i) C_theta of Lemma 4.1, (ii) Theorem 5.4(a), (iii) Steps 3, 4 of
Lemma 5.5, and (iv) "in Theorem 5.7(b) the bounds for Sigma_alpha^-1, the third derivatives of
J_F and two derivatives of log C_F ... away from the ball J_F(beta) - v.beta - lambda_F(v) ... for
bounded T, f_T is continuous and positive on [1, T_2] x P x K_0". Those are the ingredients of the
old continuum proof of 5.7(b): the ball argument with J_F, C_F, Theorem 5.4(a) with Lemma 5.5
inside, Lemma 4.1 outside, and f_T for bounded T. The paper now proves 5.7(b) through 5.7(a),
whose constants come from J^(h)_F, C^(h)_F, Theorem 5.4(b), equation (30) and Lemma A.6, and
Proposition 5.12 shows none of these to be uniform over the class. So the uniformity argument
certifies a proof that the paper no longer contains.

Smallest missing implication: one sentence after the proof of 5.7(b), like the one already given
for 5.6(b): "Part (b) also follows from the proof of (a) with J_F, C_F, K_F(v), lambda_F(v),
Theorem 5.4(a) with Lemma 5.5 and Lemma 4.1 in place of J^(h)_F, C^(h)_F, K^(h)_F(v),
lambda^(h)_F(v), Theorem 5.4(b) and (30), with |E| <= C_2(1/T + T^2/N) in (31), and with
T^2/N <= 1/T in the step that locates the maximizer." With that sentence, items (i) to (iv) of the
proof of Proposition 5.12 apply as written. The gap dates from integration 28, which replaced the
proof. Integration 30 inherits it and lists Proposition 5.12 as unchanged.

No other exported statement depends on the removed proof: Theorems 4.2(i), (iv), 5.8, Remark 4.3
and the complete-graph section cite the statement of 5.7 only.

## 3. Hypothesis (H) lifted

- Theorem A, last sentence: "every face that a path of positive probability can fill" is
  admissibility. For such F, Theorem 4.5 gives M_F = X K^red (1 + O(1/T + T^2/N)) on
  [T_1, N^(1/3)], since K^red > 0. Singletons: p = 0, K^red = mu_i, and (1) gives the display.
  Irreducible admissible faces satisfy (H) by Lemma 2.2(b), and K^red = K_F there. Covered.
- Theorem B(ii), last sentence: Corollary 4.6(ii) is exactly the equation with pi log T and
  kappa, for roots in [T_1, N^(1/3)]. No existence or uniqueness is claimed there. Covered.
- Introduction, the coefficient (p_F - p_G)/Delta and "1 and then 0": Corollary 4.6 and
  Example 5.11. Covered.
- Kept with (H): Theorem B(i) (mode location), Theorem 4.2(iv), Theorem 5.8, Section 6. Correct,
  since Theorem 4.5 does not locate maximizers and Section 6 needs F irreducible and G with (H).
- Searched every occurrence of "reducible", "admissible", "(H)", K^red and p_F in the sections
  and appendices. Theorem 4.2's "part (ii) is the only part that covers reducible faces" refers
  to the parts of Theorem 4.2 and is still true. Line 328 of `sec_firstorder.tex` ("1/2 when F and
  G are irreducible") is for admissible faces, so irreducible means (H). No place drops (H) where
  it is needed.

## 4. Theorems 4.5, 6.11, 6.12, Corollary 4.6 and the Schwarz step

- **Theorem 4.5** is R' of 02: T_1 <= T <= N^(1/3), N >= N_1, rate C(1/T + T^2/N), two-sided as
  a consequence of K > 0. Matches.
- **Corollary 4.6**: on [T_1, N^(1/3)], no uniqueness ("We do not claim that the zero is unique"),
  the extension of R(a) to 1 <= T <= T_0 is not stated. Matches. Proof checked: (ii) the case
  pi < 0 uses log T_N <= L/3. (iii) Xi' = delta + pi/T >= delta/2 on the window, and the formula
  for b follows from log T° = log L + log(Delta/delta) + O(log L/L).
- **Theorem 6.12**: T_0 <= T <= eps_1 N^(1/2), 1 <= n_i <= delta N, |E| <= 1/2 in (a). Matches the
  O1(ii) restriction for the whole theorem. Lemma 5.5 for G with N' steps needs S^2 <= N', which
  is h^2 N' <= T^2/N <= eps_1^2. Lemmas E.5 and E.6 follow Lemmas C and B of O1, checked by 02.
  The cancellation of 1 + eps(0) and E = O(rho/S + T^2/N) are right.
- **Theorem 6.11(a), (b), (d)**: match Theorem 1 of O1. The second claim of 1(d) is omitted, which
  loses nothing. The 1(d) fix is written out correctly: E_e[(K-1)(K-e)] = U' for each e; the
  integer bounds E_e[K(K-1)] <= 3U' (e <= 1), <= 3U' + 2 (e = 2) hold (for e = 1 use
  E(K-1) <= E(K-1)^2 = U', for e = 2 use m <= m(m+1)); the weights S omega I(U'), >= c_1 I(U'),
  c_2 x I(U') give nu'(e = 2) <= c_2 x/(c_1 + S omega), so the constant 2 costs c_2 h/c_1.
- **Theorem 6.11(c), second sentence: false as written.** The paper states "So if n_i <= N' and
  T >= 1, then R = K^h(n_i,S)(1 + O(h + h^2 sqrt(N' n_i)))". The audited version (01, Theorem 1(c);
  02, card 1c) has 1 <= T <= N^(1/2). The upper bound e^(2hq_j(1 + 2 sqrt U)) gives 1 + O(...) only
  while h^2 sqrt(N' n_i) is bounded. Without that, R/K^h grows exponentially in N' while
  h + h^2 sqrt(N' n_i) grows linearly. Check (pair face, q_ji = q_ij = 1, mu_i = 0, h = 1/4,
  n_i = N', so T = N'/2): R/K^h = 35.1, 1.52e3, 2.85e6, 1.00e13 at N' = 100, 200, 400, 800, so
  (R/K^h - 1)/(h + h^2 sqrt(N' n_i)) = 5.2, 119, 1.1e5, 2.0e11. Fix: add "and T <= N^(1/2)" (or
  "h^2 sqrt(N' n_i) <= 1"). The two-sided bound itself, and the remark that it "holds at every T",
  are correct.
- Wording after Theorem 6.12: "For k = 2, Theorem 6.11 makes (a) exact." Theorem 6.11(a) makes
  the ratio P_N/P_N' exact, but that ratio is R, not K^h, and R/K^h - 1 is not 0. Suggest "gives
  the ratio in (a) exactly".
- **Theorem 6.1(a), Schwarz step.** My derivation: |eps| <= C/S on |z| <= z_0 (Theorem 6.8), eps
  holomorphic there, so g = (eps - eps(0)) S/(2C) maps the disc to the unit disc with g(0) = 0,
  and |eps(z) - eps(0)| <= 2C|z|/(z_0 S). Then e^(q_i x) f_F = (1 + eps(0)) A + D with
  |D| <= (2C rho/(z_0 S)) A^abs, f_G = Lambda(0)(1 + eps(0)), |E| <= 2|D|/A = O(rho/S), and
  rho <= C/S (few visits) or rho <= 2 z_* = O(sqrt(x/S)) (many visits) give
  C(T^-2 + x^(1/2) T^(-3/2)) <= 2C/T for x <= delta T. **Proved.** The EXPORTS row for `thm:layer`
  records it.

## 5. Abstract and introduction

Each sentence of the abstract was matched with a theorem. Nothing is false. Dropping the
balancing clause removes a claim. Dropping "at every N" weakens "each face crosses a vertex
exactly once", which remains true (Theorem C(i): exactly one root in (0, N/(d-1)) for every
N >= k, and N/(d-1) is the whole range of T).

- 5a. "Every face has an explicit power of T and constant in its largest probability." Only
  admissible faces (M_F = 0 otherwise), and only for T_1 <= T <= N^(1/3). Suggest "every face that
  a path can fill".
- 5b. "we locate the crossing of their largest probabilities up to O(1/log N)" for two faces
  without (H): Corollary 4.6 locates the zeros in [T_1, N^(1/3)] only. Zeros in (N^(1/3), h_* N]
  (or below T_1) are not excluded for reducible faces. The abstract has no range. A reader can
  supply it from Theorem B(ii), but "the crossing" suggests more than is proved.
- 5c. Introduction, paragraph after Theorem A, and the text after Theorem 4.5: "every other class
  C gets time of order one and costs (T/N)^(|C|-1). This gives the power p_F." The r - 1 switches
  also cost T/N each. Without them the count gives N^-(k_F - r) T^(p_F - r + 1), not
  N^-(k_F - 1) T^(p_F). Add "and each of the r - 1 switches costs T/N".
- 5d. The sentence on the range T <= N^(1/3) in the introduction (item 2, side remark).

Section 1.2, Theorem B(ii), the organization paragraph, Section 9 and the open questions agree with
Theorems 4.5, 6.11, 6.12 and Corollary 4.6 as stated.

## Changes needed

1. Theorem 6.11(c): add T <= N^(1/2) to the second sentence (the only false statement found).
2. After the proof of Theorem 5.7(b): one sentence that restores the continuum route, so that
   the proof of Proposition 5.12(b) has a proof to make uniform (exported statement).
3. Proof of Theorem 4.5, k* = 1: one sentence on attainment.
4. Wording: 5a, 5c, "makes (a) exact", and the two sentences on where the cube root comes from.

## Fixes applied (October 25, 2026)

1. Theorem 6.11(c), second sentence: the range is now `n_i <= N'` and `1 <= T <= N^(1/2)`. The
   proof in Appendix E gains one sentence. For T <= N^(1/2), h^2 sqrt(N' n) <= h^2 N = T^2/N <= 1,
   so the exponent 2 h q_j (1 + 2 sqrt U) is bounded and the upper bound is 1 + O(h + h^2 sqrt(N' n)).
   The sentence after Theorem 6.12 now says "gives the ratio in (a) exactly".
2. Theorem 5.7: a paragraph "The continuum route to (b)" at the end of its proof. It runs the
   proof of (a) with J_F, C_F, K_F(v), lambda_F(v), Theorem 5.4(a) with Lemma 5.5, and Lemma 4.1 in
   place of the discrete objects, Theorem 5.4(b) and (30), with |E| <= C_2(1/T + T^2/N) in (31),
   which is at most 1/2 for T_2 <= T <= N^(1/3) and large N, f_T continuous and positive for bounded
   T, and T^2/N <= 1/T in the step that locates the maximizer. The proof of Proposition 5.12 now
   says that it uses this route, and its item (iv) says "In the continuum route to Theorem 5.7(b)".
   Items (i) to (iv) then apply as written.
3. The paragraph after Theorem 5.7, now "The range of part (b)": the proof of 5.7(b) from 5.7(a)
   uses only Th <= 1 and h <= 1/T, so it gives 5.7(b) and 5.6(b) for T <= N^(1/2). Both are stated
   for T <= N^(1/3), the range of the continuum route, which Proposition 5.12 makes uniform. No
   statement was widened. The introduction sentence on the cube root says the same in two lines.
4. Proof of Theorem 4.5, lower bound for k* = 1: the supremum Psi* is attained. With the flat
   factors equal to 1 every other factor is at most C_0 w~ <= C_0, and a factor whose time grows
   tends to 0 since it is not flat, so the function tends to 0 at infinity.
5. Abstract (both builds, 249 words, 1533 characters): "Every admissible face ... for large
   T <= N^(1/3)", and "we locate every crossing of their largest probabilities there up to
   O(1/log N)" for two admissible faces, with uniqueness for T <= eps N when the states of each face
   communicate. `18_abstract_C1.txt` and `18_arxiv_form_C1.txt` hold the new text, and the arXiv
   comments now say 81 pages.
6. Introduction: Theorem A says "every admissible face F, one that a path of positive probability
   can fill". The power count after Theorem A and the text after Theorem 4.5 now count the factor
   T/N of each switch between classes.

Both builds are clean, with no undefined or multiply defined references and no overfull boxes. The
article build has 81 pages and the Springer build 89. No label was added or removed, and the
exported numbers did not move (Theorem 4.5, 5.7, 6.11 and Proposition 5.12 checked in the `.aux`).
`py -I verify_all.py --quick` passes, 9 of 9 scripts. `EXPORTS.md` and `paperC/README.md` record
the change.
