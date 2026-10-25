# Paper D, two modes of the fixed-memory limit law and novelty fixes

October 25, 2026. Folder `kagey-problems/problem131/paperD`, with the coverage files in
`kagey-problems/problem131/lean/PaperD`. Builds of October 25. The journal version
`problem131_memory.pdf` has 42 pages (40 before). The arXiv version `problem131_arxiv.pdf` has 57
pages (53 before). Both build with no undefined or multiply defined reference, no overfull or
underfull box and no hyperref warning. `py -I verify_all.py --quick` passes all 5 scripts in 4.1
minutes (`data/verify_output_2026-10-25.txt`).

## 1. At most two modes for every memory (proved)

Theorem 4.2 (`thm:two-modes`), stated in the introduction as part of Theorem 1.5
(`thm:main-limit`). Let a in (1/2, 1), eps = (1-a)/2, and let g_a be the density of the limit of
(2A_N - N)/N^a with a fair first step. Exactly one of the following holds. (a) g_a is
nondecreasing on (-inf, 0] and nonincreasing on [0, inf). (b) For some c > 0, g_a is
nondecreasing on [0, c] and nonincreasing on [c, inf), with g_a(0) < g_a(c). In case (b) g_a is
not unimodal. The only possible strict local maxima are 0 in case (a) and +-c in case (b), and the
same holds for every local maximum if g_a is constant on no interval.

Proof, in five steps.

1. Smoothing. V_N(y) = eta^-2 sum_{k=1}^{N-1} D_N(k) phi_sigma(y - z_k), with eta = 2N^-a and
   z_k = (2k-N)/N^a. Since phi_sigma(y - z) = phi_sigma(y) e^{-z^2/2sigma^2} e^{yz/sigma^2}, V_N is a
   positive function times an exponential sum with increasing exponents. Descartes' rule for
   exponential sums (Lemma F.1, proved by Rolle and induction on the number of sign changes) and
   Theorem 3.16 give that every pattern of values of V_N is a subsequence of (+,-,+,-,+).
2. N to infinity. Summation by parts turns sum_k D_N(k) phi(y - z_k) into
   sum_k P_N(k) Delta phi(y - z_k). The four boundary terms (k = -1, 0, N, N+1) are bounded by
   phi(0)(6P_N(0) + 2P_N(1)), with P_N(0) <= (1-eps)^{N-1} and P_N(1) <= eps N (1-eps)^{N-2} from the
   proof of Theorem 3.5, so times eta^-2 = N^{2a}/4 they vanish. Taylor gives
   |eta^-2 Delta phi - phi''| <= eta^2 ||phi''''||/12. So V_N(y) -> E phi''(y - L) = u''(y), using
   only the a.s. convergence S_N/N^a -> L (Bercu, Theorem 3.7, and GLR (1.3), (1.6)). Lemma F.2
   (pointwise limits preserve the bound on patterns, since nonzero limit values fix the signs for
   large n) gives the pattern bound for u''.
3. One derivative fewer. u'(y) -> 0 at +-inf by dominated convergence. Lemma F.3: if u'' has
   values at most (+,-,+,-,+) and u' vanishes at +-inf, the mean value theorem applied to u'
   between alternating points, with two extra points far out, gives j+1 alternating signs of u''
   starting with the sign of u'(y_1). So u' has values at most (+,-,+,-), and u has increments at
   most (+,-,+,-).
4. Width to zero. u_sigma(y) -> g_a(y) pointwise because g_a is bounded and continuous
   (GLR, Theorem 1.3). Lemma F.2 for increments.
5. Symmetry. For 0 <= y_1 < ... < y_j with increment pattern p, the mirrored points have the
   pattern reverse(-p) followed by p, of length 2|p|, which must be a subsequence of (+,-,+,-). So
   p is empty, (+), (-) or (+,-), and there is no fall followed by a rise on [0, inf). The case
   analysis then gives (a) or (b). Flat pieces are handled by the monotone formulation: no claim is
   made that local maxima are isolated, only that strict ones are.

Regularity used: only that g_a is a bounded continuous probability density. This is checked
against Guerin, Laulin and Raschel, arXiv:2308.14630v2, Theorem 1.3: "For any q in [0,1], a in
(1/2,1), the random variable L_q is absolutely continuous with respect to Lebesgue measure. Its
density is a positive, bounded, smooth function on R." Published version: Ann. Inst. Henri
Poincare Probab. Stat. 62 (2026), no. 2, 973-1005, doi:10.1214/24-AIHP1534 (Crossref). Trinas and
Valle cite the published version as [6, Theorems 1.3 and 1.4], so the numbering is the same. The
published PDF itself was not accessible. Positivity of g_a is not used.

## 2. Exactly two modes near memory one (proved, threshold 39/40)

Theorem 4.3 (`thm:two-modes-near-one`). Case (b) holds for 39/40 <= a < 1, that is eps <= 1/80.

Moments. GLR Theorem 1.4 (k = 1, 2): m_1 = 1, m_2 = a/(2a-1), E L^k = (k-1)! m_k/(a Gamma(ka)), so
E L_1 = 1/Gamma(1+a) and E L_1^2 = 1/((2a-1)Gamma(2a)). Trinas and Valle (4.3) give the same two
formulas. Note: GLR Lemma 3.2 for d = 1 simplifies to 1/(2a(2a-1)Gamma(2a)), which disagrees with
Theorem 1.4 and with the uniform-start formula of their Section 3.8. The slip is in the second line
of that lemma. The paper cites only Theorem 1.4 and TV (4.3).

Bounds. log Gamma is convex (DLMF 5.15.1, psi' > 0), Gamma(1) = Gamma(2) = 1 (5.4.1),
psi(2) = 1 - gamma (5.4.14). So on [1,2], 0 >= log Gamma(y) >= (1-gamma)(y-2). With delta = 1-a this
gives 1 <= mu <= M = e^{(1-gamma)delta} and Var <= V = e^{2(1-gamma)delta}/(1-2delta) - 1. At
delta = 1/40, M = 1.0106257 and V = 0.0751202.

Contradiction with unimodality. In case (a), F(t) = P(|L| <= t) is concave with F(0) = 0, so
F(2/5)/(2/5) >= F(7/4)/(7/4). Cantelli gives F(2/5) <= V/(V + 9/25) = 0.17279. Chebyshev gives
F(7/4) >= 1 - V/(7/4 - M)^2 = 0.86241. Then 0.4325 < 0.4926, a contradiction. The constants are
checked in 50-digit arithmetic by `verify_elephant_modes.py`, which also checks mu and Var against
M and V on 1000 values of a in [39/40, 1). The proof itself is analytic. The moment method would
reach about a = 0.96 with optimized s and r and exact moments, which needs a finite table of Gamma
values. We kept the analytic 39/40.

## 3. The conjecture (cited with verification) and what stays open

Guerin, Laulin, Raschel and Simon, EJP 30 (2025), paper no. 102, 1-25, doi:10.1214/25-EJP1362
(Crossref). Wording checked against arXiv:2409.06836v1 (the only arXiv version), Remark 2.1(b),
quoted verbatim in Section 4.2. The EJP PDF was not accessible. The remark numbering agrees with
TV's citation [7, Remark 2.3] of the neighbouring remark in the published version.

At q = 1/2 the condition |q - 1/2| < q(a) just says q(a) > 0, so the conjecture at q = 1/2 says
that L_{1/2} is unimodal or bimodal. Theorem 4.2 proves this for every a. Theorem 4.3 shows that
the bimodal case occurs, so q(a) > 0 for a >= 39/40 if the conjecture holds. Open: the threshold
in a at q = 1/2 (and whether it is unique), the conjecture for q != 1/2, and the monotonicity in q.
For q != 1/2 the finite law is not symmetric and Theorem 3.16 has no analogue.

Remark 4.4 (numerical, not used in any proof). Theorem 4.2 makes the sign of g_a''(0) decide the
case. The computed g_a''(0) = -(1/pi) int_0^inf t^2 E cos(t L_a) dt, from the GLR moment recursion
in ball arithmetic (cut at T with T^2 |E cos(T L_a)| <= 7.3e-7 on the whole grid), is negative for
a = 0.55, ..., 0.66 and positive for a = 0.67, ..., 0.85, and bisection gives a_c = 0.6688128. A
second run with cut at T = 20 and 1600 terms gives the same signs at 0.668812 and 0.668814. On the
exact finite law the center second difference changes sign at a = 0.647124 (N = 1000), 0.656287
(N = 4000) and 0.659207 (N = 8000). The two values quoted in the paper are 0.6563 and 0.6592.

## 4. Novelty fixes (each source verified)

- Pakes, J. Appl. Probab. 30 (1993), 991-994, doi:10.2307/3214530 (Crossref; PDF read). Section 3:
  "norming and centering gives a non-trivial limit law: as m -> oo, (Z_m/m) - log m -> S, a stable
  random variable". Cited at p. 993, the page Moehle gives.
- Moehle, J. Appl. Probab. 42 (2005) (PDF read): Theorem 4.1 "can also be found in [2, Equation
  (15)] and goes back to [13, p. 993]", where [13] is Pakes. Note: [2] there is Angerer, Mutation
  Res. 479 (2001), not the J. Math. Biol. paper. Angerer is not cited.
- Bertoin, EJP 19 (2014), no. 24 (arXiv:1305.4762 read): Proposition 1, k^{-3/4} Delta_k - (3/4)c ln k
  => c(Z + ln c) for q_k = 1 - c k^{-1/4}, Delta_k the number of vertices disconnected from the root.
  His (11) credits the Luria-Delbrueck limit to "Pakes [20] or Theorem 4.1 in Moehle [19]".
- Iksanov and Moehle, Electron. Commun. Probab. 12 (2007), 28-35, doi:10.1214/ECP.v12-1253
  (Crossref; PDF read from the EMIS mirror). Section 2 builds the coupled process (R_i, S_i), and
  Section 3 takes p_k = P(xi = k) = 1/(k(k+1)) and proves (Proposition 1) that M_n has the law of
  the number of cuts. Bertoin (4) states the coupling D_k(l) = S_l for l < N(k). Meir and Moon,
  Math. Biosci. 21 (1974), 173-181, doi:10.1016/0025-5564(74)90013-3 (Crossref) for the cutting
  procedure. The paper says the removed subtree sizes are those of independent steps with law
  1/(j(j+1)) up to a first passage time, and that the same weights give D's mean family counts.
- Trinas and Valle, arXiv:2609.14753v1 (read): Theorem 3.1 (uniform local limit theorem),
  Propositions 4.2, 4.3 and Theorem 4.4 (disproof of GLRS Remark 2.3, log-concavity), Section 4
  ("unimodality and log-concavity do not automatically extend from f_a to f_{q,a}"), (4.3) and
  (4.5). Positioned in the prior-work paragraph and in Section 4.
- Bokes, Hlubinova and Singh, Axioms 12 (2023), 249 (published PDF read from a web archive copy).
  Equation numbers checked: (6)-(10) first-order regular solution, (10) the formula with m(m+1),
  (21) coarse-grained tail, (50) the Landau pdf approximation, (51) the right-boundary Landau cdf,
  (52) the composite, and (58)-(60) the stochastic initial condition, the sum of two Landau
  densities being (60). The earlier citations (58)-(60) for the random start and (6)-(10) for the
  center coefficient are correct for the published version. In the bioRxiv v1 the random start is
  (56)-(58). The paper now adds (50)-(52) for the formal Landau shape.
- What D adds, as now stated in the introduction and after Theorem 3.9: the total variation bound,
  the explicit local rate with truncation at N-1, the transfer to the walk, and the shape theorems.
  Theorem 3.9(c) is said to be new only through the transfer.

## 5. Pages

Moved to the arXiv-only Section S5 ("Convexity between the humps"): the former Section 3.6
(`def:convex`, `cor:one-point`, `thm:convex-large`, `prop:convex-certified`, the double-precision
paragraph, `conj:convex`, `rem:convex-open`) and Proposition 1.5 (`prop:main-window`), now
Proposition S5.1. The journal text points there with `\arxivonly`. `prop:odd` stays in the journal
as Section 3.6 (Proposition 3.21), since Section 3 and Section S3 use it. Proposition 3.7 no longer
refers to `prop:convex-certified` for the bracketing method. The abstract is 229 words.

New and moved numbers: Theorem 1.5 `thm:main-limit`; Proposition 3.21 `prop:odd` (3.25);
Theorems 4.2, 4.3, Remark 4.4; Lemmas F.1 to F.3; S5.1 to S5.7 for the moved statements. Section S
numbering of S1 to S4 is unchanged. `lean/PaperD/MAP.md` and `coverage_tables.tex` record the new
numbers. No Lean source changed.

## 6. Left open or not done

- The threshold a_c is numerical. A certified sign of g_a''(0) at two points around 0.6688 would
  prove two modes above the upper point by Theorem 4.2, but not unimodality below the lower point.
- The EJP and AIHP published PDFs were not accessible. Wording and numbering were checked on arXiv
  versions and against citations of the published versions by Trinas and Valle.
- The journal version is 42 pages, the upper limit. Getting to 41 would need about one more page of
  cuts, for example the heuristic part of the paragraph after Corollary 3.20.
