# 09. Audit of Theorem D (note 01, Section 3)

Scope: the dominated regime of note 01. Plus is the heavier side, 0 < alpha_+ < 1, alpha_- in
(0,1) u (1,2), T_- = o(T_+), (RV) and (SPAN) for both signs. Notation as in note 01. I judge only the
mathematics. Background checked against G Section tools (Lemmas cd, sums, key, decay) and F
Appendix (Lemmas stable, kernels, small).

## Verdicts

| Item | Verdict |
|---|---|
| 1. Centering, scales, limit laws in every sub-case | Correct. I get the same D_N and limits by an independent derivation |
| 1'. Theorem D(a) | Incomplete as written (the note defers it to the literature). It follows from (b) in two lines (A below). Routine |
| 2a. (b) lower half | Proved as written |
| 2b. (c) mixed region, no extra condition | Proved as written. The one slip is harmless: a missing log factor at alpha_+ = 1/2 |
| 2c. (c) alpha_- < 1, sufficiency of (SRT_-) + (W_+) | Proved as written |
| 2d. (c) necessity of (SRT_-) and of (W_+) | Proved, after two short steps the sketch skips (B, C below). Routine |
| 2e. Lemma Q(iii) for t near 0 | Incomplete. The cited "dyadic estimate of G Lemma key" gives only O(T(k)), not 1 + o(1). Not needed for (b), (c). Needed for the uniform matching. A proof is in D below. Routine once the right input is used |
| 3a. (d) fixed j at both ends | Proved as written |
| 3b. (d) uniform matching over 0 <= j <= y_2 D_N | Incomplete. Three gaps: Lemma Q(iii) near t = 0 (D); the bounds on R_N in the range 1 << j << D_N, which as displayed are not o(1) (E); and the case alpha_- = 1/2 (F). The first two close by routine steps. The third needs a restriction |
| 4. Exact spot checks, one mixed case and one unequal infinite-mean case | Consistent with every claim. Nothing is refuted |

## 1. Centering, scales and limits

Let n = A_N be the plus time and j = N - n the minus time. The number of completed plus runs is
M(n) = #{m >= 1 : S^+_m < n}. Up to one run, the number of completed minus runs equals it. With
S_+(1) normalized by Levy tail x^(-alpha_+) (so t T_+(a_+(t)) -> 1),

    P(T_+(n) M(n) >= t) = P(S^+_{t/T_+(n)} < n) -> P(S_+(1) < t^(-1/alpha_+)) = P(S_+(1)^(-alpha_+) > t),

so T_+(n) M(n) => E = S_+(1)^(-alpha_+). This is the note's E. E[E] = E[S^(-alpha)] =
1/(Gamma(1+alpha) Gamma(1-alpha)) = sin(pi alpha)/(pi alpha), as stated. phi_E(0) = 1 because
P(E <= eps) = P(S_+ >= eps^(-1/alpha)) ~ eps.

Self-consistency: the minus time is j ~ S^-_{M(n)} with n = N - j. If j = o(N), then
T_+(n) ~ T_+(N) and M(n) ~ E/T_+(N).
- mu_- < inf: j ~ mu_- E/T_+(N), so D_N = mu_-/T_+(N), of order N^(alpha_+) up to a slowly varying
  factor. This is o(N). Limit E, density phi_E.
- alpha_- < 1: j ~ a_-(E/T_+(N)) S_-(1) ~ E^(1/alpha_-) a_-(1/T_+(N)) S_-(1). So D_N = a_-(1/T_+(N)),
  that is T_-(D_N) ~ T_+(N). The limit is Y = E^(1/alpha_-) S_-(1) = S_-(1)/S_+(1)^(alpha_+/alpha_-),
  with E and S_- independent in the limit. D_N = o(N) because T_-(D_N) ~ T_+(N) >> T_-(N) and T_-
  has a negative index. This covers alpha_+ < alpha_- as well as alpha_+ = alpha_- with b = 0.
- alpha_+ = alpha_- = alpha, b = 0: Y = S_-/S_+, a ratio of two i.i.d. alpha-stable laws with the
  same normalization. Its density is the classical one quoted in note 01. Reading L_{alpha,b} at
  1 - x = b^(1/alpha) y and letting b -> 0 gives b^(-1/alpha) rho(y). So the join with BAL is right.
- Psi(0+) = 1: P(Y <= y) = P(E <= (y/S_-)^alpha_-) ~ y^alpha_- E[S_-^(-alpha_-)] phi_E(0)
  = y^alpha_- sin(pi alpha_-)/(pi alpha_-), whose derivative is (sin(pi alpha_-)/pi) y^(alpha_- - 1).
  The density version follows from the mixture integral by dominated convergence (phi_E is bounded
  and continuous at 0).

**A. (a) from (b).** Suppose liminf_N inf_{y_1 D_N <= j <= y_2 D_N} (D_N P_N(N-j) - rho(j/D_N)) >= 0
for all 0 < y_1 < y_2. A Riemann sum gives
liminf_N P((N - A_N)/D_N in [y_1, y_2]) >= int_{y_1}^{y_2} rho. Now rho is a probability density on
(0, inf) with no atom at 0. Lower bounds of this kind on every compact interval, together with total
mass 1, give convergence in law: the mass outside any [y_1, y_2] is eventually at most
1 - int_{y_1}^{y_2} rho + o(1), and that is small. So (a) needs no literature input and no condition
beyond (RV) and (SPAN).

## 2. The local law

### 2.1 Inputs, and whether they apply

Every lemma cited from G is stated there under G's equal-index (RV_alpha), but each has a one-sign
proof, so it applies to any sign with index in (0,1).
- G Lemma cd(i), Gnedenko. Applies to both signs, any index in (0,1) u (1,2) (for (1,2) it is F
  Lemma stable(ii)).
- G Lemma cd(ii), Caravenna-Doney's u_m(x) <= C (m/a_m) T(x). Used for the plus law only. Fine.
- G Lemma cd(iv), (SRT) as a small-m condition. Used for the minus law only when alpha_- < 1. Fine.
- G Lemma key, q_{m+1}(k) <= C T(k). Index in (0,1) is needed through (R3), (R4) and m T(a_m) <= C.
  Used for the plus law, and for the minus law only when alpha_- < 1. Fine.
- G Lemma sums(i), P(S_m >= x) <= C m T(x). Used in Lemma Q(ii). Fine.
- F Lemma stable(iii) and F Lemma small. Used for the minus law with alpha_- in (1,2), which is F's
  setting. The note's split m <= delta j with delta mu_- <= 1/4 is the same estimate as F Lemma small
  (there 8 m mu <= j). Either constant works.

Lemma Q(i), (ii) and (iii) on t in [eps, K] are correct as written. (ii) is even easier than
stated: T(k - r) >= T(k) for every r >= 0, so q_{m+1}(k) >= P(S_m < k) T(k) >= (1 - C m T(k)) T(k).
In (iii) on [eps, K] the part r >= (1-eta)k is at most C eta^(1-alpha) t^(-1/alpha) T(k), as in G
Lemma kernel-limit. Lemma R(i) and R(ii) are correct.

### 2.2 Sufficiency

Mixed region. On the window |m - j/mu_-| <= A a_-(j) we have m T_+(n) -> y uniformly, because
a_-(j)/D_N -> 0 when alpha_- > 1. Only Lemma Q(iii) at t in a compact subset of (0, inf) is used.
Off the window, Lemma Q(i) and Lemma R(i) apply. Correct.

For R_N, the count in 3.3 is right. q^-_m(j) <= C T_-(j)(1 + m/a_-(m)) for m <= delta j (F Lemma
small) and u^+_m(n) <= C (m/a_+(m)) T_+(n) (Caravenna-Doney). Both exponents are negative, by the
inequalities written in 3.3. One slip: at alpha_+ = 1/2 the sum of m/a_+(m) up to j carries a
slowly varying factor, not max(1, ...). The indices are strictly negative, so this is harmless.
The part m > delta j is O(1/N) because a_+(delta j) is of order N when j is of order D_N. This is
true in the bulk. It is false for smaller j, see E.

Infinite lighter mean. The middle Riemann sum, the large-m bound, and the small-m bound through G
Lemma cd(iv) are all correct. In the bound on R_N, the split at delta/T_+(n) is right. The
reduction (SRT_+) => (W_+) is right. So is (W_+) for alpha_- > 1/2, via
D_N T_+(N) (T_+(N) + 1/(N T_+(N))) = D_N T_-(D_N)^2 (1 + o(1)) + D_N/N -> 0.

**Equivalence over delta in (W_+).** For delta < delta', the extra terms number at most
delta'/T_+(n). Each is at most C/a_+(delta/T_+(n)) <= C_delta/n. So the difference is
O(D_n T_+(n) delta'/(T_+(n) n)) = O(D_n/n) -> 0. Hence "some delta" is equivalent to "every delta".

### 2.3 Necessity

**B. Failure of (SRT_-) breaks the local law.** By the monotonicity in delta, failure of (SRT_-)
means there is c > 0 such that, for every eps > 0, j T_-(j) sum_{m < eps/T_-(j)} u^-_m(j) >= c
along some sequence j -> inf. That sequence depends on eps. Fix y in (y_1, y_2) and eps <= delta_0.
For each such j choose N with j/D_N in [y - eta, y + eta]. Such N exists: N -> (N - n)/D_N moves
by steps of o(1), since D_N is nondecreasing and D_{N+1}/D_N -> 1. Then
D_N P_N(N-j) >= (middle part, -> int_{eps'}^{K} ...) + (c/2) y^(alpha_- - 1)(1 + o(1)). Here the
first term tends to rho(y) - eta(eps', K), where eta can be made smaller than c y^(alpha_- - 1)/4
by choosing eps' and K before the sequence. So limsup_N sup_j (D_N P_N(N-j) - rho(j/D_N)) > 0.

**C. Failure of (W_+) breaks the local law.** Choose delta so small that m <= delta/T_+(n) gives
m T_-(j) <= delta_0 for j <= y_2 D_N. Then Lemma Q(ii) for the minus law (alpha_- < 1) gives
R_N(j) >= (T_-(j)/2) sum_{m <= delta/T_+(n)} u^+_m(n). Along the bad n, pick j with
j/D_{n+j} near y and put N = n + j. This works by the same step argument, and D_{n+j} ~ D_n because j = o(n).
The term R_N then adds at least c'/D_N on top of the lower half (b).

The proof of the "iff" is complete. The note does not show that (W_+) can actually fail when
alpha_- <= 1/2 and (SRT_+) fails. This does not affect the truth of the theorem, but the merged
paper should not suggest it is known to be a genuine extra condition. I note that for
alpha_+ < 1/2, sum_{m <= delta/T_+(n)} u^+_m(n) = o(T_+(n)) always holds: fixed m gives o(T_+(n)),
and the tail of sum m/a_+(m) converges. (W_+) asks for more, namely o(1/(D_n T_+(n))), and that is
smaller once D_n T_+(n)^2 -> inf, which happens when alpha_- < 1/2.

### 2.4 Lemma Q(iii) near t = 0

**The gap.** The sketch bounds the part r >= eta k by "O_eta(m T(k)) T(k) by the dyadic estimate in
the proof of G Lemma key". That proof uses only the pointwise bound C (m/a_m) T(k) and the window
bound C m T(k). Its output is C m T(k) T(a_m) <= C T(k). That is O(T(k)) and not small, because
m T(a_m) is of order 1. The squeeze to 1 + O(eps) does not follow.

This is not used in (b) or (c): there the middle range has t in [eps, K], and the small range uses
only Lemma Q(i) and (ii). It is used in the uniform matching, where q^+_{m+1}(n) = T_+(n)(1 + o(1))
is needed uniformly for m T_+(n) -> 0.

**D. A proof.** Write delta_k = sup_{1/2 <= lam <= 1} |T(lam k)/T(k) - lam^(-alpha)| -> 0. Use the
uniform one-big-jump estimate

    rho(eps, k) = sup { |P(S_m >= x)/(m T(x)) - 1| : x >= k/2, m T(x) <= eps },
    lim_{eps -> 0} limsup_k rho(eps, k) = 0.

This is standard for alpha < 1. For x/a_m -> inf it is Nagaev's theorem (Cline-Hsing). For x/a_m in
[eps^(-1/alpha)/2, Gamma] it follows from the stable limit and P(S > s) = s^(-alpha)(1 + O(s^(-alpha))).
It is not among the lemmas of F and G, so it has to be cited.

Let m T(k) <= eps and 0 < theta, eta < 1/2. Split q_{m+1}(k) = sum_{r<k} u_m(r) T(k - r):
- r < eta k: at most T((1-eta)k) = (1-eta)^(-alpha)(1 + o(1)) T(k);
- eta k <= r <= (1-eta)k: at most T(eta k) P(S_m >= eta k) <= C_eta eps T(k);
- i = k - r < eta k, in dyadic blocks [w/2, w): a block is at most T(w/2) P(S_m in [k-w, k)), and
  P(S_m in [k-w, k)) <= min{ C w m T(k)/a_m , m T(k)(C w/k + delta_k + 3 rho(eps,k)) }.
  The first bound is Caravenna-Doney. The second is the difference of the one-big-jump estimate at
  k - w and at k.

Blocks with w <= theta a_m contribute at most C theta^(1-alpha-) m T(a_m) T(k) <= C theta^(1-alpha-) T(k).
Blocks with theta a_m < w <= eta k contribute at most
C eta^(1-alpha) eps T(k) + C (delta_k + 3 rho) theta^(-alpha-) T(k), using m T(theta a_m) <= C theta^(-alpha-).
Take limsup in k, then eps -> 0, then theta -> 0, then eta -> 0. This gives
sup_{m T(k) <= eps_k} q_{m+1}(k)/T(k) <= 1 + o(1) for every eps_k -> 0. The lower bound in 2.1 gives
the reverse inequality. So Lemma Q(iii) holds on all of [0, K]. The point is to use the window
probability, which the one-big-jump estimate makes o(m T(k)) for windows of width o(k), in place of
the pointwise local bound.

## 3. End layers and matching

**Fixed j (both ends).** Correct as written. Two details the sketch leaves implicit:
- u^+_m(x) = o(T_+(x)) for fixed m. For m = 1 this is f(x) = T(x) - T(x+1) = o(T(x)). For m >= 2,
  sum_y f(y) u_{m-1}(x - y) <= 2 max_{y >= x/2} f(y) + (the term with the other factor at >= x/2),
  and both are o(T(x)).
- q^+_{m+1}(x) = P(S_{m+1} >= x) - P(S_m >= x) ~ T(x) for fixed m.
Only (RV) of the sign whose tail sets the layer is used. The start corrections (k = N atom T_+(N)
for a plus start, P_N(0) = T_-(N) for a minus start) agree with the exact law.

**Uniform matching.** The pieces needed are j bounded (done), j/D_N -> y > 0 (this is (c)), and
1 << j << D_N. The subsequence principle joins them. For the third range the sketch has three gaps.

**E. R_N for 1 << j << D_N.** The bounds as displayed do not give o(1).
- Infinite case. The note's ratio bound C j T_-(j)^2 (1 + 1/(N T_+(N)^2)) is not o(1) when
  alpha_+ > 1/2. Then N T_+(N)^2 -> 0, and at j = N^c with c small the ratio is of polynomial
  size. Example: alpha_+ = 0.6, alpha_- = 0.8, j = N^0.2 gives a ratio of order N^0.08. Bounding
  q^-_m(j) by T_-(j) (or q^-_m(j) = 0 for m > j) and summing the Caravenna-Doney bound up to m = j
  also fails near alpha_- = alpha_+, for instance at (0.6, 0.65).

  Fix: use G Lemma decay, q^-_m(j) <= C T_-(j) e^{-c m T_-(j)}. Then
  R_N(j) <= C T_-(j) T_+(N) sum_m e^{-c m T_-(j)} m/a_+(m). Relative to T_+(N) omega(j), this is
  at most:
  - C j/a_+(1/T_-(j)) when alpha_+ > 1/2. This tends to 0 because T_+(j)/T_-(j) -> inf forces
    a_+(1/T_-(j))/j -> inf.
  - C j T_-(j)^2 when alpha_+ < 1/2. This tends to 0 when alpha_- > 1/2.
  The term m > delta/T_+(n), of size C/N, gives a ratio j T_-(j)/(N T_+(N)) <= D_N/N -> 0. For
  alpha_- < 1/2, the note's (W_+) argument is right, since j T_-(j)^2 <= C D_N T_-(D_N)^2 by Potter.
- Mixed case. 3.3 bounds the part m > delta j by C/a_+(delta j), and "this is O(1/N)" holds only
  for j of order D_N. For j << D_N it can exceed T_+(N). Example: alpha_+ = 0.6, j = N^0.3 gives
  1/(a_+(j) T_+(N)) of order N^0.1. Fix: for m > delta j, u^+_m(n) <= C T_+(n) m/a_+(m)
  <= C T_+(N) j/a_+(j). This holds because m/a_+(m) has a negative index, and
  sum_m q^-_m(j) = 1. So this part is o(T_+(N)) as j -> inf. The part m <= delta j is the 3.3
  count, which is o(T_+(N)) as j -> inf with no condition on j/D_N.

**I_N for 1 << j << D_N.**
- Mixed case. All m <= j, and j T_+(N) -> 0. So I_N(j) = T_+(N) u_-(j)(1 + o(1)) is exactly
  Lemma Q(iii) near t = 0, which is D above. I see no way round it here. The weights u^-_m(j)
  sit on a window of width a_-(j) << j, so averaging in m does not help.
- Infinite case. D is enough, but there is also an elementary route. Since
  sum_{m<M} q_{m+1}(n) = P(S^+_M >= n) = M T_+(n)(1 + o(1)) uniformly for M T_+(n) -> 0, and
  q_{m+1}(n) >= (1 - C m T_+(n)) T_+(n), we get sum_{m<M} |q_{m+1}(n) - T_+(n)| = o(M T_+(n)).
  With M = K/T_-(j) and u^-_m(j) <= C_eps/j for m >= eps/T_-(j), the middle range contributes
  o(T_+(N) omega(j)). The small range is controlled by (SRT_-), and the large range by Lemma R(ii).

**F. alpha_- = 1/2.** For alpha_- < 1/2 the (W_+) route works, and for alpha_- > 1/2 the decay
route works. At alpha_- = 1/2 both give only o(1) times a ratio of slowly varying factors,
l_-(j)^2 or l_-(j)^2/l_-(D_N)^2, where T_-(x) = x^(-1/2) l_-(x). That ratio need not be bounded
when l_- oscillates. The bulk statement (c) is unaffected. Restriction: state the uniform matching
for alpha_- != 1/2, or at alpha_- = 1/2 assume (SRT_+) with alpha_+ < 1/2. Then
R_N/(T_+(N) omega(j)) <= C l_-(j)^2/(N T_+(N)^2) -> 0, because N T_+(N)^2 grows polynomially.

## 4. Exact spot checks

Scripts are in my scratch folder (`phase_audit/`, outside the repo):
- `audit_engine.py`: the exact law from the decomposition P_N(N-j) = I_N(j) + R_N(j), with u_m by
  FFT convolution powers;
- `audit_limits.py`: phi_E, the stable density (Kanter's integral), and rho;
- `audit_run.py`: the comparisons;
- `audit_lighter.py`: the finite-m law of S^-_m.

All are run with `py -I`. Checks of the code:
- the engine agrees with brute force over all compositions for N = 6, 9, 12 in both cases (max
  deviation 1.9e-16), and total mass is 1;
- phi_E at alpha = 1/2 matches exp(-pi x^2/4) to 1e-13;
- the stable density at alpha = 1/2 matches the Levy density to 1e-14;
- int phi_E = 1, and E[E] = sin(pi alpha)/(pi alpha) to 1e-12.

These are zeta laws with a fresh plus start, at parameters different from note 01. "Mix" is
T_+(n) sum_m u^-_m(j) phi_E(m T_+(n)).

| Case, quantity | N = 500 | 1000 | 2000 | 4000 |
|---|---|---|---|---|
| Mixed (0.7, 1.4): max rel err of D_N P_N vs phi_E, y in [0.1, 0.6] | 0.441 | 0.370 | 0.314 | 0.263 |
| Mixed: max R_N/I_N on the core | 0.290 | 0.218 | 0.169 | 0.131 |
| Mixed: P/(T_+ u_-(j)), worst of j = 0..5 | 1.086 | 1.053 | 1.032 | 1.020 |
| Mixed: P_N(i)/(T_- u_+(i)), worst of i = 1..5 | 1.055 | 1.027 | 1.014 | 1.007 |
| Mixed: P/(T_+ u_-(j) phi_E(j/D_N)) at j = sqrt(D_N) | 1.076 | 1.054 | 1.040 | 1.028 |
| Infinite (0.55, 0.85): max rel err vs rho, y in [0.2, 3] | 0.963 | 0.863 | 0.767 | 0.690 |
| Infinite: max rel err of P vs Mix on the core | 0.267 | 0.191 | 0.140 | 0.104 |
| Infinite: max R_N/I_N on the core | 0.291 | 0.206 | 0.150 | 0.111 |
| Infinite: plus end, worst of j = 0..5 | 1.033 | 1.022 | 1.015 | 1.010 |
| Infinite: minus end, worst of i = 1..5 | 1.051 | 1.028 | 1.015 | 1.009 |
| Infinite: P/(T_+ u_-(j) Psi(j/D_N)) at j = sqrt(D_N) | 1.029 | 1.023 | 1.018 | 1.015 |

Lemma Q directly. sup |q^+_{m+1}(n)/T_+(n) - phi_E(m T_+(n))| at n = 1000 and n = 4000:
- for t <= 0.1: 0.045 and 0.030 at alpha = 0.7; 0.0024 and 0.0016 at alpha = 0.55;
- for 0.1 < t <= 3: 0.170 and 0.119 at alpha = 0.7; 0.0099 and 0.0057 at alpha = 0.55.

What the numbers say:
- Every error decreases monotonically in N. R_N/I_N -> 0, which is the content of 3.3. The layers
  and the j ~ sqrt(D_N) matching ratio approach 1.
- In the infinite case the error against rho is large but falls steadily. Most of it is not from
  the occupation mechanism: P against Mix is within 10% at N = 4000. It comes from the slow
  convergence of the lighter sums. With Levy-tail normalization, P(S^-_m <= 5 a_-(m)) is 0.561,
  0.483 and 0.412 at m = 32, 128 and 512, against 0.086 in the limit. At N = 4000 there are only
  about 128 cycles.
- In the mixed case, Mix is not closer than the limit (0.338 against 0.263 at N = 4000). The
  error sits at the right end of the core, where phi_E for alpha_+ = 0.7 falls steeply after its
  mode near 0.45 and Lemma Q converges slowly (0.119 at n = 4000). This does not contradict
  anything in Theorem D. It does mean the note's P3-type statement (mixture better than limit) is
  parameter-dependent.

## 5. Smaller points

- The remark in Section 2 of note 01 that a finite-variance lighter law is "covered by Theorem D
  verbatim" is not quite verbatim. The mixed-region count uses F Lemma small, which assumes (RV)
  with index in (1,2). With only E X_-^2 < inf, the halving argument gives
  u_m(r) <= C sqrt(m)/j^2 for r - m mu >= j/4, and then
  q^-_m(j) <= T_-(j/2) + C sqrt(m)/j^2. The 3.3 sum still tends to 0, with indices
  2 - 1/alpha_+ - 2 and 1/2 - 1/alpha_+. So the claim is true, after a short substitute.
- Theorem D(d) says "this needs only (RV) for the plus sign" for the plus end. That is right. The
  minus end needs (RV) for the minus sign, which is assumed anyway.
- The uniform statement in (d) uses u_-(j) <= C omega(j) when alpha_- < 1, that is (SRT_-). This is
  part of "the condition of (c)" when alpha_- <= 1/2 and automatic when alpha_- > 1/2. Correct, but
  worth saying in the statement.

## Summary

Theorem D(a), (b), (c) and the fixed-j part of (d) are correct in the stated generality. (a) needs
the two-line deduction A. The necessity half of (c) needs the selection steps B and C. The uniform
matching in (d) is true for alpha_- != 1/2 after two routine repairs: the small-t case of Lemma
Q(iii), proved via the uniform one-big-jump estimate (D), and the bounds on R_N for 1 << j << D_N
via G Lemma decay and Caravenna-Doney (E). At alpha_- = 1/2 it needs an extra hypothesis (F). The
"only lemmas already in F and G" claim should add one external input, the uniform one-big-jump
estimate used in D.
