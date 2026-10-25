# 28. Paper C1, the local law over the whole switching range (October 25, 2026)

Source: `Paper C1 full range O2/01_report.md` (Theorem A_h and its proof) and `02_audit.md` (verdict
"proved as written", three repairs). Paper: `kagey-problems/problem131/paperC`.

Page counts: article build 72 pages (was 64), Springer build 78 (was 71). Abstract 247 words,
1452 characters on one line (in `18_abstract_C1.txt` and `18_arxiv_form_C1.txt`).

## Where the theorem went

The full-range law is now the main form of the local law. No new numbered statement sits in
Sections 2, 4 or 5, and no numbered equation was added before `eq:A-radii`, so no exported number
moved.

- **Section 3.3** (`sec:discrete-rate`, new). The functional J^(h)_F = (1/h) sup_u sum alpha_i
  log(u_i/((I+hQ_F)u)_i), with J^(0)_F = J_F, written through L_h(y) = int_0^1 y ds/(1 - shy).
  - Proposition 3.5 (`prop:discrete-rate`) is D1(a) to (c): the restriction identity, the unique
    maximizer with a negative definite Hessian, analyticity in (h, alpha) up to h = 0, strict
    convexity, and the criterion alpha_i/(p_i + h theta_i) proportional to l_i e^(psi_i).
  - Proposition 3.6 (`prop:discrete-variational`) is D2: min (J^(h)_F - v.alpha) =
    -(1/h) log rho(e^(h diag v)(I + hQ_F)), attained only at l o r, strict on subfaces, and at
    v = 0 the value -(1/h) log(1 - h lambda_F) at alpha*_F for every h. Analyticity at h = 0
    goes through B = (M - I)/h, an irreducible Metzler matrix analytic in (h, v) with
    B = Q_F + diag v at h = 0, since rho(M) at h = 0 is the multiple eigenvalue 1 of I.
- **Section 5.2.** The discrete constant C^(h)_F (Hessian form) and K^(h)_F(v) are defined in
  the text before Theorem 5.4, with c_h(alpha*_F) = 1/(1 - h lambda_F).
  - Theorem 5.4 (`thm:local`): old statement is (a). New (b) is the local law of the counts for
    1 <= T <= h_* N with a field, error O(1/T), and a ratio bounded above and below.
  - Theorem 5.6 (`thm:stratified`): new (a) with J^(h)_V and C^(h)_F. The old statement is (b),
    proved from (a) by analyticity in h, and also by the old route.
  - Theorem 5.7 (`thm:facemax`): new (a) with K^(h)_F(v) e^(-T lambda^(h)_F(v)), maximizers at
    alpha^(*h)_F(v) + O(1/T), and (1 - h lambda_F)^N at v = 0. The old statement and
    `eq:logmax` are (b), derived from (a). The proof of (a) is the old proof with (h, v) in
    [0, h_*] x V, the bound outside the ball from the exact Chernoff bound, and no T^2/N.
  - A paragraph "Where the cube root came from" after Theorem 5.7. N^(1/3) came only from the
    maximizer step, which needed T^2/N <= 1/T. T J^(h) - T J_F is (T^2/2N) sum alpha_i
    (q_i - theta_i)^2 + O(T^3/N^2), and the sum vanishes only if lambda_F = 0 and
    alpha = alpha*_F (theta determines alpha). The same paragraph says that Theorem 4.2(ii),
    Theorem 7.4(ii) and the tie windows keep their ranges.
  - Theorem 5.8 (`thm:crossing`): (ii) and (iv) for every zero in [1, h_* N]. A first step puts
    every such zero in W = [Delta L/(2 delta), 2 Delta L/delta], using Xi_N' =
    delta/((1 - h lambda_F)(1 - h lambda_G)) + Delta/(2T) >= delta. The old steps then run on W.
    This is the audit's "exactly one root in [1, h_* N]".
- **Lemma 4.1** (`lem:upper`) and (6) (`eq:upper-field`): the audit's stronger reading. The factor
  exp(C_theta h^2 |n|) is gone, with C_theta = 2^k b(theta') prod_{i>=2} theta_i. The proof
  (Appendix A.3) is now the modulus bound of the discrete torus formula, equation (30)
  (`eq:A-chernoff`, A5 in the Springer build), which is Corollary U_h. Step 2 keeps the bound
  (`eq:A-Hsigma`) for the continuum sums that Lemma 5.5 and Lemma A.5 use. `eq:A-sigma` is
  removed. Appendix A.7 lost its h^2 term too.
- **Lemma A.2** (`lem:torus`) also states Good's discrete formula on the same torus (Lemma T_h).
  Lemma A.3 now says "the formula for H", so it does not claim the discrete one.
- **Appendix A.8** (`app:full-range`, new). Lemma A.6 (`lem:discrete-hessian`) is D1(d), (e):
  theta' minimizes Psi_h(alpha; .) = -sum alpha_i L_h(q_i - s_i), Hess J^(h) = K^T H_h^-1 K with
  det K = 1/(c_h pi_1 prod(p_i + h theta_i)), and the torus form of C^(h)_F. Then the proof of
  Theorem 5.4(b). For bounded T the ratio is bounded below through Lemma 5.5 and Theorem 5.4(a).

## The three repairs

1. **Localized Laplace.** Remark B.2 (`rem:laplace-uniform`) now states the localized form: Psi
   and a defined only on the cube, with the bounds there, and any integrand off the cube of
   modulus at most B e^(T(Psi(0) - eta)). It says why: the logarithm has no branch on the whole
   torus. The proof of Theorem 5.4(b) cites it.
2. **The subface bound.** Proposition 3.6(a) first uses Proposition 3.5(a) (the argument of D1(a))
   to get J^(h)_F = J^(h)_{F'} on Delta_{F'}, then the resolvent bound for the principal submatrix
   and strict Perron monotonicity. No direct comparison of P_F with P_{F'}.
3. **Part (c) without exceptions.** The expansion is in the paragraph after Theorem 5.7, with no
   "except" clause. The only statement about where the term vanishes is the correct one
   (lambda_F = 0 and alpha = alpha*_F).

## Positioning and framing

- Related work: Theorems 6.3 and 6.5 of Kontoyiannis and Meyn give exact asymptotics of
  P{S_n >= nc} for one geometrically ergodic chain, non-lattice and lattice, with no rate in n and
  no uniformity over kernels. The new point is uniformity as I + hQ -> I, joined at h = 0 to the
  continuum estimate. Good's discrete formula (3) is now named as the object of Theorem 5.4(b).
- Introduction: T ranges up to h_* N, Theorem A is the full-range law with the N^(1/3) form as
  its last sentence, the paragraph after it explains the torus route and why T^2/N is real, and
  Theorem B(ii) has exactly one root in [1, h_* N]. Abstract: relative error O(1/T) uniformly
  for 1 <= T <= epsilon N, and N times the Donsker and Varadhan functional of the chain.
- "Why N^(1/3)" was not listed in the open questions of Section 9 (audit 25 had kept O2 out of
  the paper), so nothing was removed there. Section 9 now says that Theorem 4.2(ii) on reducible
  faces and Theorem 7.4(ii) stay at T <= N^(1/3).

## Numbers

No exported number moved (checked against the `.aux` of both builds). New unexported numbers:
Section 3.3, Propositions 3.5 and 3.6, Lemma A.6, Appendix A.8, equation (30) (A5). `eq:A-Hsigma`
moved from (30) to (29) (A5 to A4). EXPORTS.md has a dated note and updated rows for `lem:upper`,
`eq:upper-field`, `thm:local`, `thm:stratified`, `thm:facemax`, `eq:logmax`, `thm:crossing` and
`lem:torus`. paperC2 cites Theorems 5.6 and 5.7 in their N^(1/3) form, which is now part (b) of
each, so its citations stay correct and could be sharpened to 5.6(b) and 5.7(b).

## Checks

- New script `verify_full_range.py` (60 assertions, 13 s), in `verify_all.py`:
  - the discrete torus formula against the exact law (two states with h q_max up to 0.9, a
    non-reversible chain on three states);
  - the two forms of C^(h)_F, and C^(0)_F = C_F from Definition 5.1;
  - the least values of Proposition 3.6 with and without a field;
  - T |R - 1| <= 0.199 for q12 = 1, q21 = 2, N = 4000, T = 16 to 1000 = N/4, two starts
    (continuum form 180 to 1000 at T >= 200), and 0.255 at T = 1600;
  - the face maximum of a face with exit rates to 5e-4, with T |alpha_hat - alpha*| <= 0.18;
  - k = 3 non-reversible at N = 400, T |R - 1| <= 0.27;
  - the T^2/N ratio tending to 1.
- `py -I verify_all.py --quick`: 8 of 8 scripts pass (224 s). Outputs in `data/` with sha256
  headers.
- Both builds settle with no undefined or multiply defined references and no overfull boxes. The
  Springer log keeps its one bookmark-level warning from the class.

## Left for later integrations

- Reducible faces beyond N^(1/3): Theorem 4.2(ii) and Appendix A.7 still assume T <= N^(1/3)
  (Claim A needs h small). Equation (30) holds for h q_max <= 1 and any block length, so it can
  replace Lemma 4.1 on blocks there.
- The discrete layer: Section 3.3 and Appendix A.8 give the discrete functional and the discrete
  torus, which a discrete form of Theorem 6.1 would use. Nothing about the layer was added.
- Theorem 7.4(ii) on the complete graph and Proposition 5.12(b) (uniform over a class) keep
  T <= N^(1/3). The uniformity of the full-range law over a class was not attempted.
- `lean/PaperC/MAP.md` was not touched (outside the write scope).
