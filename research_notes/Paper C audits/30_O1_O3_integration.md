# 30. Paper C1, the discrete layer (O1) and the reducible faces (O3) (October 25, 2026)

Sources: `Paper C1 discrete layer O1/01_report.md` with `02_audit.md`, and `Paper C1 reducible
faces O3/01_report.md`, `02_report.md` with `03_audit.md`. Paper: `kagey-problems/problem131/paperC`.

Page counts: article build 80 pages (was 72), Springer build 88 (was 78). Abstract 249 words,
1485 characters on one line (in `18_abstract_C1.txt` and `18_arxiv_form_C1.txt`).

## Where the results went

No new numbered statement or equation sits before the end of Section 4, the end of Section 6 or
the new Appendix E, so nothing before them was renumbered.

- **Section 4.4** (`sec:reducible-max`, new). The block order, k*, S*, a_F, p_F, the bridge
  densities Phi_C(t)_{yx} = e^{-<q,t>} H_{A_C,e_y,e_x}(t), the suprema A_j and B_j, and K^red_F.
  - Theorem 4.5 (`thm:reducible`) is Theorem R' of 02: |M_F/X - K^red_F| <= C(1/T + T^2/N) for
    T_1 <= T <= N^(1/3), with 0 < K^red_F < infinity. The two-sided bound of R(a) is stated as its
    consequence (the ratio lies in [K/2, 2K] after enlarging T_1), since K > 0. So Lemma 3 of 01
    and its separate lower-bound construction are not needed.
  - Corollary 4.6 (`cor:reducible-crossing`) is Corollary E, on [T_1, N^(1/3)], with no uniqueness
    claim, and the text says so. It recovers the coefficients 1 and 0 of Example 5.11 with their
    constants (K^red_{1,2} = b).
- **Section 6.9** (`sec:layer-counts`, new). The lattice kernel K^h_beta(n_i, S), its Laguerre
  form, and the one power of h.
  - Theorem 6.11 (`thm:pair-counts`) is Theorem 1(a) to (d) of O1. The second claim of 1(d) (the
    factor [1 - u/2, 1 - (u/2) e^{-n_i u/2}] between the leading terms) is left out. The text says
    only that (c) holds at every T and that (d) needs hS small.
  - Theorem 6.12 (`thm:layer-counts`) is Theorem 2(a) to (c), with the kernel L_beta written
    K^h_beta, since \mathcal L_beta is the Laplacian of Section 6.1.
- **Theorem 6.1(a)** now has |E| <= C(T^-2 + x^(1/2) T^(-3/2)) <= 2C/T, the Schwarz sharpening.
  Its proof gained six lines: epsilon(z) is holomorphic on |z| < 2z_0 (C_G != 0 there by Step 1(i),
  (ii) of the proof of Theorem 6.8), the Schwarz lemma gives |eps(z) - eps(0)| <= 2C|z|/(z_0 S), and
  dividing by f_G = Lambda(0)(1 + eps(0)) leaves rho/S, which is C/S^2 with few visits and
  C x^(1/2) S^(-3/2) with many.
- **Appendix E** (`app_counts.tex`, new, 6 pages). E.1 the block factorization, the bridge run
  expansion and Lemmas E.1 to E.4 (one bound per block, blocks of bounded time with Corollary B',
  the bridge law, the bridge maxima). E.2 the proofs of Theorem 4.5 and Corollary 4.6. E.3 the
  proof of Theorem 6.11. E.4 Lemmas E.5 (the discrete contour, Lemma C of O1) and E.6 (the facet
  states discretized, Lemma B of O1), the coefficient identity (Lemma D of O1, now one sentence),
  and the proof of Theorem 6.12.

## The repairs

- **O1 (i), Theorem 1(d), first claim.** The proof in E.3(d) averages over nu', the law of the
  terms of K, not nu. For fixed e the ratio test gives E_e[(K-1)(K-e)] = U' = omega S x exactly,
  so E_e[K(K-1)] <= 3U' for e <= 1 and 3U' + 2 for e = 2. The total weights of e = 0, 1, 2 are
  S omega I(U'), at least c_1 I(U') and c_2 x I(U'), so nu'(e = 2) <= c_2 x/(c_1 + S omega), and
  the constant 2 contributes c_2 h/c_1 = O(h). This is the audit's fix, worked out.
- **O1 (ii), the range.** Theorem 6.12 is stated for T_0 <= T <= epsilon_1 N^(1/2), with
  |E| <= 1/2 there. Not only part (a) needs this. The denominator P_N'(n-hat) is compared with
  h^(k-2) f_G by Lemma 5.5, whose lower bound needs T^2/N small, so the whole theorem takes the
  smaller range.
- **O1 (iii), the labels of check_facet.py.** No number from `out_check_facet.txt` is quoted. The
  new script uses h = T/N with N = N' + n_i, and its numbers agree with the audit's own table
  (E = 0.187, 0.072, 0.029, 0.012 at N' = 200 to 1600, T = 8, n_3 = 10, and 4.5e-3 at T = 4).
- **O3, Lemma D.** Lemma E.4(i) maximizes over supp m = C, the only case that the proof of Theorem
  4.5 uses (case B2 has n^(j) with full support).
- **O3, Corollary E.** Stated on [T_1, N^(1/3)], no uniqueness. The extension of R(a) to
  1 <= T <= T_0 is left out.

Two adaptations to the current paper. Lemma E.1 (Lemma 2 of 01) cites Lemma 4.1 without the factor
exp(C h s), which audit 28 removed, and Theorem 5.7(b) with the start e_y. Lemma E.4 (Lemma D of
02) is written out in full, because the paper now proves Theorem 5.7(b) from (a), and the old
proof of 5.7(b) that 02 followed is no longer in the paper. The written proof is the one in 02,
Section 4 (the ball from Proposition 5.2(a), finitely many theta in V_C outside it, Lemma E.3 and
Lemma A.4 inside).

## Hypothesis (H)

Removed where Theorem 4.5 covers the case:
- Theorem A: the face-maximum display now holds for every admissible face for
  T_1 <= T <= N^(1/3), with T^(p_F) and K^red_F.
- Theorem B(ii): a sentence for admissible faces, with (p_F - p_G) log T and K^red, for roots in
  [T_1, N^(1/3)].
- The introduction now gives the coefficient (p_F - p_G)/Delta, which is 1 and then 0 in Example
  5.11, in place of "it can be 1 or 0".

Kept:
- Theorem 4.2 as exported (its part (ii) is now sharpened by Theorem 4.5, said in the text).
- Theorem B(i), the location of the mode at alpha*_F + O(1/log N). Theorem 4.5 does not locate
  the maximizers of a reducible face.
- Theorem 5.8 and Theorem B(ii) for [1, h_* N] and the uniqueness of the root.
- Every local law, Theorem 5.9, Corollary 5.10 and Proposition 5.12.
- Section 6. The layer needs F irreducible and G with (H).

## Text

- Abstract: the power and the constant on every face, the crossing located for all faces and
  unique with coefficient 1/2 when the states of each face communicate, and the counts near a
  facet as a lattice form with the extra error T^2/N. To stay under 250 words the balancing
  clause and "at every N" left the abstract (both stay in Theorem C).
- Introduction: Theorem A, the paragraph after it (the mechanism behind p_F), Theorem B(ii), the
  paragraph after Theorem B, Section 1.2 retitled "The boundary layer", whose last paragraph now
  states Theorems 6.11 and 6.12 and that the regime T^2/N of order one is open for three or more
  states, and the organization paragraph.
- Section 4.2: the sentence after Theorem 4.2 points to Theorem 4.5.
- Section 5: "Where the cube root came from" lists Theorem 4.5 with Theorem 4.2(ii), and Section
  5.4 says that Corollary 4.6 predicts the coefficients of Example 5.11.
- Section 6: the opening paragraph no longer says the counts are open.
- Section 8: the last paragraph cites Theorem 6.11(a) for the main part of P_N(b, a).
- Section 9: the conjecture on the power of T and the sentence on the discrete layer are gone.
  The open questions now name the reducible faces beyond N^(1/3), the uniqueness of the zero in
  Corollary 4.6, the maximizers of a reducible face, and the counts near a facet of three or more
  states when T^2/N is of order one. The computations paragraph describes `verify_counts.py`.

## Numbers

No exported number moved (checked against the `.aux` of both builds, every row of `EXPORTS.md`,
including `eq:A-radii` (28)/A3, `eq:A-chernoff` (30)/A5 and `prop:uniform-facemax` 5.12). New
unexported numbers: Section 4.4, Theorem 4.5, Corollary 4.6, Section 6.9, Theorems 6.11 and 6.12,
Appendix E with Lemmas E.1 to E.6. `EXPORTS.md` has a dated note and rows for the new statements,
and the row of `thm:layer` records the sharper error of part (a).

## Checks

- New script `verify_counts.py` (17 assertions, a few seconds), in `verify_all.py`.
  - A. Theorem 6.11(a) against all paths in exact rational arithmetic (a pair face inside a chain
    on three states with killing), N <= 12, h = 1/7 and 1/13, all 1 <= n_i < N (132 cases), and
    P_N'(n-hat) = mu_j p_j^(N'-1).
  - B. The two-sided bound of 6.11(c) in 83 cells, N' <= 10^4, n_i <= N', T from 1/2 to
    N'^(1/2). Part (d): |K^h/(hK) - 1|/(h + hS) <= 1.25 where hS <= 1.
  - C. Theorem 6.12 on the cycle of Proposition 6.2(e), i = 3, beta = (1/2, 1/2), uniform start.
    Exact law by a forward recursion over (c_1, c_3, state), lattice kernel by the contour with
    the closed forms of Lemma 6.9 (radius independent to 1e-15). E N/T^2 = 0.61, 0.46, 0.36, 0.30
    at N' = 200 to 1600 (T = 8, n_3 = 10), 0.45 at N' = 1600, T = 4, n_3 = 1. E falls by 2.58,
    2.52, 2.43 as N' doubles. |K^h/(hK(x - h, S)) - 1| <= T^2/N in all rows.
  - D. Theorem 4.5 on {1} -> {2,3}, q12 = q23 = q32 = 1, start 1, at N = 40000. Local slope
    1.5002 to 1.5003 for T = 8 to 20, and M_F/(N^-2 T^1.5 sqrt(2/pi)) = 1.00006 to 1.00027.
    The block engine equals brute force at N = 10 to 4e-16.
- `py -I verify_all.py --quick`: 9 of 9 scripts pass. Outputs in `data/` with sha256 headers.
- Both builds settle with no undefined or multiply defined references and no overfull boxes. The
  Springer log keeps its one bookmark-level warning from the class.

## Left for later

- The rate of R' beyond N^(1/3) (Theorem 4.5 uses Theorem 5.7(b) on the long block and Claim A
  nowhere, so the full-range face maxima of Theorem 5.7(a) may extend it).
- The other three faces of the O3 numerics (E2 to E4) are not in a paper script. The paper quotes
  only the reviewer's face.
- `lean/PaperC/MAP.md` was not touched (outside the write scope).
