# 10. Audit of 06_shape.md (Theorems C and A, the G1 refutation, the fair 5-mode example)

2026-10-26. Adversarial audit. I judged the mathematics only and ignored the status words in the
source. My own scripts are outside the repo (a scratch folder). They are: `thmC.py` (mpmath),
`runrec.py` (my own run-boundary recursion, float and exact `Fraction` modes, checked against a
sum over all 2^N sign strings for N <= 12, error <= 1.3e-16), `osc.py`, `osc_detail.py` and
`fair5.py`. None of them imports `shape_engine.py`, `cm_everyN.py` or `lamperti_critical.py`.

## Verdicts

| item | verdict |
|---|---|
| 1. Theorem C | **proved as written** |
| 2. Theorem A | (i), the counting deduction, Lemma D, Lemma P: **proved**. (ii): **incomplete**. Missing: L\* for fresh and fair starts, plus the remainder-length bound for general (S) starts. I think L\* is routine (route below). (iii): **incomplete**. Missing: the uniform first- and second-difference local limit theorem. Theorem A as a whole: **incomplete** |
| 3. Refutation of G's `conj:count` | the counts are **reproduced exactly**. As a disproof it is **incomplete**: a finite computation cannot refute an "all large N" statement, and the asymptotic step depends on Theorem B |
| 4. Fair-start 5-mode example | **proved as written** (exact rational arithmetic, both N = 39 and N = 145) |

## 1. Theorem C

**Re-derivation.** I started from G's x-form,
L = (sin pi a/pi) b x^{a-1}(1-x)^{a-1} / (b^2 x^{2a} + 2bc x^a(1-x)^a + (1-x)^{2a}). Put
w = (1-x)/x = e^t. The denominator is x^{2a} b w^a * 2(cosh(at - beta) + c), and
x^{-2} w^{-1} = 2 + 2cosh t, so L = (sin pi a/pi)(1 + cosh t)/(cosh(at - beta) + c). This agrees
with G eq. `eq:L-cosh`. Since x -> t is a diffeomorphism, critical points and their types
(including degeneracy) carry over.

I checked each step of the proof:

- Step 1. phi'/phi = tanh(t/2) - aR(s), and k -> -(1-a) at -inf, so the order is min, max, min.
  Correct.
- Step 2. On D, k = tanh(A) - tanh(B) with A = (s+beta)/(2a) and B = artanh(aR). So k has the sign
  of beta - H(s). At a zero, k'(s) = sech^2(A)(A' - B') = -sech^2(A) H'(s)/(2a), so k has a simple
  zero iff H' != 0 there. Since phi'' = phi k' at a zero, this is also nondegeneracy of L. Off D,
  |aR| >= 1 > |tanh|, so there is no zero. Correct.
- Step 3. Correct. R' = (1 + c cosh s)/(cosh s + c)^2. The identity
  2a^2 R' - (1 - a^2 R^2) = -Q(w)/(w + c)^2 checks term by term. The roots are
  w_pm = -c pm a sin(pi a)/sqrt(1 - a^2), from discriminant (1 - a^2) a^2 (1 - c^2), and w_- < 1.
  The step w_+ > 1 iff a > cos(pi a/2) iff a > a_c is right: both sides are nonnegative before
  squaring, and cos(pi a/2) - a is decreasing.
- Step 4. Correct. R_max = 1/sin(pi a) at cosh s_m = -1/c. On (1/2, 1), sin(pi a) - a is
  decreasing, so D = R iff a < a_1. For a >= a_1, aR -> a < 1 at infinity, so the excluded set
  is a bounded closed interval.
- Step 5. Correct, including the a >= a_1 case. On (0, s_1), H rises from 0 to +inf, which forces
  s_0 >= s_1. On (s_2, inf), H falls from +inf, which forces s_0 <= s_2. One small point needs
  stating: a_1 > a_c, so w_+ > 1 there. That is true.
- The degenerate list in (c) is complete. For a = a_c and beta != 0 the root is at s != 0, so it
  is nondegenerate.

The closed form is beta_c = H(s_0) with R(s_0) = sinh s_0/(w_+ + c).

**Numerics** (mpmath, 40 digits, `py -I thmC.py`). The count is the number of sign changes of
d/dx log L, computed from the original x-form (not from H or E).

- a_c = 0.594611644056836 and a_1 = 0.736484448241517.
- The closed form beta_c agrees to 10 digits with a direct numerical maximisation of H:
  0.005889187665 (a = 0.6), 0.2352945474, 0.8647845439, 1.476521613, 3.291519829
  (a = 0.735), with b_c = 1.0059, 1.2653, 2.3745, 4.3777, 26.884. These match the values in the
  source.
- Directly from L, the count flips from 3 to 1 between beta_c - 1e-4 and beta_c + 1e-4 at
  a = 0.6, 0.65, 0.7, 0.72.
- Grid: 32 values of alpha in [0.05, 0.97], including 0.5946, 0.7364, 0.737 and 0.74, and
  beta in {0, ±0.003, ±0.05, ..., ±6, ±9}. That is 863 cases with **0 mismatches**. One case was
  skipped: a = 0.5946 with b = 1, which is within 1e-3 of degenerate.

## 2. Theorem A

**Part (i): proved.** Under (S), Sum_{m >= n} |Delta nu(m)| = o(1/n) gives n nu(n) -> 0. Then
W^+_N <= o(1/N) Sum_{m < N/2} T(m) = o(T(N)), which is G's own argument in `sec_initial`. G
`thm:initial`(f) then gives P_N(N-j) = T_+(N) kappa~_+(j) + o(T_+(N)) for each fixed j, and the
no-tie condition (H5) gives the signs.

Part (i) holds for every fixed j, not only j < J_+. This matters: Theorem L only starts at its
own J, which can exceed J_+, and the finite range J_+ <= j < J is covered by (i).

**Counting deduction: proved given (i)-(iv).**

- The plus end: the local maxima of P_N near N correspond one-to-one with those of kappa~_+.
  kappa~_+ is strictly decreasing after J_+ and P_N is strictly monotone through the layer. The
  endpoint convention matches kappa~(0) vs kappa~(1).
- Junctions: (ii) holds for every small epsilon and (iii) for each fixed epsilon. So one epsilon
  below the first critical point and above 1 minus the last one makes the ranges overlap, and
  the signs agree there (L' > 0 near 1 and D_N < 0 in the layer).
- "Exactly once near each c_i" needs ΔP_N to be strictly monotone on a window of width delta N
  around c_i N. That is exactly the second-difference half of Theorem B. The first-difference
  limit alone cannot exclude extra sign changes near a critical point.

**Lemma D: proved.**

- Log-convex with f -> 0 implies nonincreasing.
- f(n) <= 2T(n/2)/n gives (LB). Doney gives (SRT) for every a in (0,1).
- de Bruijn-Erdos gives u log-convex.
- The sandwich argument is right.
- One index detail. ⌊lambda j⌋ skips integers, so the liminf bound should be stated for every i
  by taking j = ⌊i/lambda⌋ and using that r is monotone. This is a one-line fix and changes
  nothing.

**Lemma P: proved.** The decomposition of Delta kappa_+ and the identity
Sum_{i < j/2} Delta u(i) = u(⌈j/2⌉) - 1 are right. The bounds
|nu(j-i) - nu(j+1)| <= (i+1) delta_j and Sum_{i <= j} (i+1)|Delta u(i)| <= C j u(j) give
|R| = o(u(j)/j). Only the first-difference half of (S) is used.

**Part (ii), Theorem L.** I checked the orders of I to IV for the fresh start, using (P1), (P2),
(P3) and (M):

- I: (j/N)^alpha
- II and III: j/N
- IV: (j/N)^2
- tail m > K/T_-(j): e^{-cK}

All are relative to T_+(N) u_-(j)/j, and they are consistent. (P2) and (P3) use only Doney's level
bound and Fourier, so they hold. (P1) and (M) use L\*. So Theorem L is complete modulo L\* for
fresh starts. The fair start, as a mixture, is also covered.

For general (S) starts there is a second gap, which the source admits: the bound
Sum_n |Pi^-_n(j+1) - Pi^-_n(j)| <= C/j over remainder lengths j <= n <= j/epsilon. The table row
"layer part (ii): proved modulo L\*" is therefore accurate only for fresh and fair starts.

**L\*: not proved in the source. In my judgement it is routine**, and easier than F's alpha > 1
version because no centering is needed. The source's obstruction is that (m T(n/K))^K does not
tend to 0. A halving trick with K chosen large in terms of alpha gets around it. Take y = n/K and
split by the first index i with X_i >= y:

1. **Some jump >= y.** Put the difference on that jump. By (LD), |Delta f(z)| <= C f(z)/z
   <= C_K f(n)/n for z >= y. The remaining sum is at most m.
   - The cutoff boundary term is f(y) P(rest = n - y) <= C_K f(n) m T(n)/n, by Doney's local
     bound at n - y >= n/2. This is <= C m f(n)/n because m T(n) <= C for n >= a_m.
   - The range y <= z < n/2 gives (f(y)/y) P(rest >= n/2) <= C_K (f(n)/n) m T(n).
2. **All jumps < y.** Split S_m into two halves. One half must exceed n/2. Summation by parts
   moves the difference onto the other half, leaving a boundary term that is a product of two
   truncated local probabilities at about n/2. Fuk-Nagaev for nonnegative summands gives
   P(S_{m/2} >= n/2, M < n/K) <= (C_K m T(n))^{K/2}. A Fourier difference LLT for the truncated
   law, uniform in y >= a_m/K, gives sup |Delta| <= C_K a_m^{-2}. By Potter,
   a_m^{-2} <= C n^{-2} (m T(n))^{-2/(alpha - delta)}, so the product is <= C m T(n)/n^2,
   which is about C m f(n)/n, once K >= 2 + 4/(alpha - delta).

The ingredients are (LD), (LR), (SPAN), Doney's local large deviation bound, Fuk-Nagaev, and a
truncated-law Fourier bound of the type of F `lem:trunc-local`. I see no obstacle, but this is a
proof route, not a written proof. It is about one to two pages.

**Part (iii), Theorem B: incomplete (sketch).** The smallest missing implication is: uniformly for
k/N in compacts of (0,1), N^2 ΔP_N(k) -> L'(k/N) and N^3 Δ^2 P_N(k) -> L''(k/N). The second limit is
indispensable (see the counting paragraph). It needs:

- (a) first- and second-difference LLTs in space and in m in the scaling range (Fourier; standard);
- (b) a second-difference form of L\* under (LD2), for the one-giant-run range t < delta. The claim
  that this range contributes O(delta^2) at the N^2 level is asserted and not shown, and nothing is
  said at the N^3 level;
- (c) the second-order defect estimate for (S) starts.

None of this looks conceptually new, but (b) and (c) are real work, not a remark. "Routine" is
fair for (a) only.

**Theorem A' inherits all of this.** M_pm = 1 for fresh and fair starts is right:

- fresh: (1, u(1), u(2), ...) and (0, u(1), u(2), ...) via the renewal equation;
- fair: (1/2, u(1), ...), no tie iff f(1) != 1/2.

For CM laws with regularly varying tail, (LR) and (LD2) follow from the monotone density theorem,
since f, -Delta f and Delta^2 f are all monotone.

## 3. G's Conjecture `conj:count`

I recomputed everything with my own recursion (`osc.py`): Sibuya laws for both signs, initial plus
run as in the source (mass 1/2 at d = 1, 1/2 on n >= 2, support cut at 2*10^6). The total mass is 1
to 1e-15. The smallest relative |ΔP| at a sign change is >= 2.7e-7, against rounding near 1e-13.

| start | N = 500 | 1000 | 2000 | 3000 |
|---|---|---|---|---|
| alpha = 0.3, lam = 0.3 | 54 | 110 | 223 | 338 |
| alpha = 0.7, eps = 0.9 | 31 | 35 | 50 | 62 |

These agree with the source table at every N I computed.

- For alpha = 0.3 the extra modes are the even k in [188, 290] (N = 500) and [1080, 1750]
  (N = 3000), around N/2, as described.
- kappa_- is strictly decreasing from j = 1 (alpha = 0.3) and from j = 6 (alpha = 0.7), as stated.
- For alpha = 0.7 the extra modes move. At N = 500 they are at k = 2, ..., 54. At N = 1000 they are
  at 2, ..., 10 and 54, ..., 102. So the modes at k = 6, ..., 10 are finite-N layer effects that
  leave as N grows, and the persistent ones sit near the W minimum 0.085 N.
- I checked the hypotheses of `thm:signs` and `conj:count` against G's text: the local law
  (n nu(n) -> 0), W = o(T), finite kappa(0), kappa eventually strictly decreasing, (LB), and strictly
  log-convex laws. The starts satisfy them.
- The support cut changes only Q_+(N), that is P_N(N). This matters for alpha = 0.3, where the cut
  removes about 1% of the n >= 2 mass. But P_N(N) is above P_N(N-1) either way, so the counts do not
  change.

**Why this is not yet a disproof.** The conjecture asserts equality for all large N, and the data
end at N = 3000. Here is the shortest complete route for the alpha = 0.3 start. P_N is linear in
nu, so write nu = nu_smooth + nu_alt. nu_smooth = 1/2 delta_1 + c n^{-1-alpha} satisfies (S).

1. Theorem B (first-difference half only) for the smooth part.
2. An alternating-sum lemma for the nu_alt part:
   N^2 ΔP_N[nu_alt](k) = (-1)^k g(k/N) + o(1), with g(1/2) != 0. The mechanism in Sec. 4.1
   identifies g, but no proof is given.
3. Then near k = N/2, where L' -> 0, the sign of ΔP_N alternates on an interval of length about
   N, and the count tends to infinity.

The alpha >= 1/2 start needs more: a second-difference limit together with a rate o(N^{-1-2alpha})
for the smooth part near the critical points.

The source says, in its Sec. 9 summary, that "the refutation of `conj:count` as stated" is proved.
That should read: "refuted conditionally on the first-difference local limit theorem (Theorem B);
the counts are exact up to N = 3000."

## 4. Fair-start 5-mode example

`fair5.py`: my run recursion in exact `Fraction` arithmetic, with
f(n) = Sum w_i (1 - th_i) th_i^{n-1}, the same law for both signs, and the fair start
nu_pm = f/2. Each law sums to exactly 1, and fair = (fresh+ + fresh-)/2 holds exactly.

- **N = 39**, w = (17/42, 17/42, 4/21), th = (19/20, 49/100, 31/50):
  - fair modes at 0, 4, {19, 20}, 35, 39;
  - sign pattern `-+++------------+++0---++++++++++++---+`;
  - fresh plus strictly increasing, fresh minus strictly decreasing.
- **N = 145**, w = (9/35, 13/35, 13/35), th = (49/50, 1/5, 33/50):
  - fair modes at 1, 4, {72, 73}, 141, 144;
  - fresh plus modes 7, 77, 145;
  - fresh minus modes 0, 68, 138.

All of this matches the source.

One caveat, which does not affect the verdict. The middle mode is a two-point plateau. It is forced
because P_N(k) = P_N(N-k) when N is odd, the law is the same for both signs and the start is fair.
It counts once under F's block convention. Even without it, each example has 4 strict local maxima,
so "at most 3 modes for every N, fair start" is refuted under either convention.

## Corrections the source should make

1. Sec. 1 table and Sec. 9: "the refutation of `conj:count`" should be called conditional on
   Theorem B (first-difference form), with exact counts to N = 3000.
2. Theorem A(ii): "proved modulo L\*" holds for fresh and fair starts only. General (S) starts
   also need the remainder-length bound.
3. Theorem A(iii): state the second-difference local limit theorem as the missing piece, not just
   "routine difference LLTs". The O(delta^2) claim for the one-giant-run range is unproved.
4. Lemma D: state the liminf step for all i through j = ⌊i/lambda⌋ (cosmetic).
5. L\*: a proof route exists (halving trick with K > 2 + 4/alpha, Fuk-Nagaev, truncated Fourier
   bound). It should be written out rather than described as "expected to carry over".
