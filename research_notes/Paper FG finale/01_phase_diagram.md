# 01. The phase diagram of the local law of A_N over (alpha_+, alpha_-)

Research note for the merged paper (F + G). Scripts: `01_exact_law.py` (exact law by the run
recursion, brute-force check), `01_compare.py` (comparisons), output in `01_compare_output.txt`.

## 0. Predictions (written before any computation)

Zeta laws f(n) = n^(-a-1)/zeta(a+1), fresh plus start unless stated. N up to 4000.
Notation of Section 2 below: in the plus-dominated regime D_N is the scale of N - A_N, phi_E the
density of E = S_+^(-alpha_+), rho the density of S_-(E).

- P1 (mixed, alpha_+ = 0.6, alpha_- = 1.5). D_N = mu_-/T_+(N). D_N P_N(N - j) -> phi_E(j/D_N) on
  y = j/D_N in [0.25, 3]. Max relative error below 0.2 at N = 4000 and decreasing in N, roughly
  like N^(-0.3) (smoothing by the minus fluctuations, of relative size (a_-(1/T_+)/D_N)^alpha_-).
  End layer: P_N(N - j)/T_+(N) within 3% of u_-(j) for j <= 5 at N = 4000.
  Shape: exactly three modes, at k = N (global), at an interior point near N - y* D_N with
  y* the mode of phi_E (phi_E increases at 0 since alpha_+ > 1/2), and at k = 1.
- P2 (unequal infinite mean, alpha_+ = 0.5, alpha_- = 0.8). D_N defined by T_-(D_N) = T_+(N).
  D_N P_N(N - j) -> rho(j/D_N), rho the density of S_- / S_+^(alpha_+/alpha_-), on y in [0.3, 5].
  Slower: max relative error below 0.25 at N = 4000, decreasing. Big-jump kernel
  P_N(N-j) ~ gamma_+(N-j) f_-(j) + T_-(j) u_+(N-j) at j = vN, v in [0.2, 0.8]: ratio within 0.3 of 1
  at N = 4000 and improving.
- P3 (mechanism). The mixture formula T_+(N-j) sum_m u^-_m(j) phi_E(m T_+(N-j)) is closer to P_N than
  the limit rho(j/D_N)/D_N in P1 and P2, by at least a factor 2 in max relative error on the bulk.
- P4 (finite mean, unequal: alpha_+ = 1.3, alpha_- = 1.8, Paper F region). B_N P_N(k) vs the
  moving profile h_N((k - pN)/B_N): max relative error on |x| <= 2 below 0.1 at N = 4000.
- P5 (control, Paper G region, alpha = 0.7 both). N P_N(k) vs L_{0.7,1}(k/N) on k/N in [0.1, 0.9]:
  max absolute error below 0.05 at N = 4000.
- P6 (boundary, alpha_+ = 0.6, alpha_- = 1, lighter law in the Cauchy domain with infinite mean).
  The limit phi_E at the scale D_N = m_-(a_-(1/T_+))/T_+ (m_- the truncated mean) is reached only
  at rate 1/log N: errors of order 0.15 or more at N = 4000, with a systematic shift. The mixture
  formula of P3 stays within 0.1.
- P7 (added after P1-P6 had run, before computing it). Mixed with alpha_+ = 0.4 < 1/2,
  alpha_- = 1.5. phi_E is decreasing (phi_E'(0) = -Gamma(1-a)^2/Gamma(1-2a) < 0 for a < 1/2) and
  u_- is decreasing (log-convex zeta law), so for a fresh plus start: exactly two modes, k = 1 and
  k = N. For a fresh minus start: P_N(N) = 0, the layer is T_+(N) u_-(j) 1{j >= 1}, modes at k = 1
  (from the minus-end layer, now T_-(N)(u_+(i) - ...) shape) and k = N - 1.

(Everything below was written after the computations of Section 6. The predictions above are left
as they were, and Section 6 scores them.)

## 1. Setting and notation

Runs alternate in sign. Plus runs have law f_+, minus runs f_-, and the tails T_s(n) = P(X_s >= n)
are regularly varying with index -alpha_s. A_N is the number of plus steps among the first N,
P_N(k) = P(A_N = k), and j = N - k is the number of minus steps. u_s is the renewal mass function,
u^s_m = f_s^{*m}, and q^s_m(k) = P(S^s_{m-1} < k <= S^s_m) is the probability that the m-th run of
sign s covers level k in the time of its sign. The fresh-plus identity (F Prop. fresh-identity),
for j, n >= 1 with n + j = N:

    P_N(N - j) = I_N(j) + R_N(j),
    I_N(j) = sum_{m>=1} u^-_m(j) q^+_{m+1}(n)   (m complete minus runs, plus run in progress at N),
    R_N(j) = sum_{m>=1} u^+_m(n) q^-_m(j)       (m complete plus runs, minus run in progress at N).

Every statement is for a fresh start unless said otherwise. Hypotheses as in F and G: (RV), (SPAN),
(LR) f_s(n) ~ alpha_s T_s(n)/n, (LB_s) Doney's bound f_s(n) <= C T_s(n)/n, and
(SRT_s) u_s(n) ~ (sin(pi alpha_s)/pi)/(n T_s(n)) for alpha_s < 1.

Stable objects. For 0 < a < 1, S_s(1) is the positive a-stable law with Laplace transform
exp(-Gamma(1-a) lam^a). Its Levy tail is x^-a, which matches F's normalization t T(a(t)) -> 1.
For the dominant sign (say plus, with alpha_+ < 1) put

    E = S_+(1)^(-alpha_+),   phi_E its density,   phi_E(0) = 1,
    E[E^n] = n!/(Gamma(1 + n alpha_+) Gamma(1 - alpha_+)^n),   E[E] = sin(pi alpha_+)/(pi alpha_+).

E is the limit of T_+(N) times the number of plus runs completed in plus-time N (the inverse
subordinator at 1, a rescaled Mittag-Leffler law). Since phi_E'(0) = -Gamma(1-a)^2/Gamma(1-2a),
phi_E decreases from 0 when alpha_+ < 1/2 (at alpha_+ = 1/2, phi_E(x) = exp(-pi x^2/4)) and has an
interior mode when alpha_+ > 1/2.

## 2. The phase diagram

The tails decide who dominates, not the indices alone.

- If both means are finite (alpha_+, alpha_- in (1,2)), each side takes a fixed fraction of the
  time, and the heavier tail sets the fluctuation scale.
- If at least one mean is infinite, the side with the heavier tail dominates, in the sense that
  T_light(n) = o(T_heavy(n)). With different indices this is automatic. With equal indices
  alpha < 1 it is the condition b = lim T_-/T_+ in {0, infinity}, and b in (0, infinity) is G's
  balanced case. If T_-/T_+ has no limit, there are only subsequential limit laws.

The regions follow. Plus is the heavier side where it matters, and the mirror regions follow by
exchanging the signs and k <-> N - k.

| Region | Centering | Scale | Global limit | Local law | Status |
|---|---|---|---|---|---|
| FF: alpha_+, alpha_- in (1,2), any relation of the scales | pN, p = mu_+/s | B_N = max b_s,N, of order N^(1/alpha_*) | (1-p) theta_+ Z_+ - p theta_- Z_- (moving profile) | B_N P_N(k) - h_N((k-pN)/B_N) -> 0 uniformly over all k, under (RV), (SPAN) | F Thm bulk |
| BAL: alpha_+ = alpha_- = alpha < 1, b in (0, inf) | 0 | N | Lamperti L_{alpha,b} | N P_N(k) = L(k/N) + o(1) on compacts of (0,1) iff (SRT_+) and (SRT_-); the lower half always | G Thm 1 |
| DOM-mixed: alpha_+ < 1 < alpha_- (mirror alpha_- < 1 < alpha_+) | N (count near the plus end) | D_N = mu_-/T_+(N), of order N^(alpha_+) | (N - A_N)/D_N => E | D_N P_N(N-j) - phi_E(j/D_N) -> 0 on compacts of (0, inf), under (RV), (SPAN) only | new, Thm D |
| DOM-inf: alpha_+ < alpha_- < 1, or alpha_+ = alpha_- < 1 with b = 0 | N | D_N = a_-(1/T_+(N)), i.e. T_-(D_N) ~ T_+(N); of order N^(alpha_+/alpha_-) | (N - A_N)/D_N => Y = E^(1/alpha_-) S_-(1) = S_-(1)/S_+(1)^(alpha_+/alpha_-) | D_N P_N(N-j) - rho(j/D_N) -> 0 on compacts iff (SRT_-) and (W_+); both automatic if alpha_- > 1/2 | new, Thm D |

(W_+) is defined in Section 3. For equal indices with b = 0 the density rho is explicit. Then
Y = S_-/S_+ is a ratio of two independent alpha-stable variables, and

    rho(y) = (sin(pi alpha)/pi) y^(alpha-1) / (1 + 2 y^alpha cos(pi alpha) + y^(2 alpha)).

This is also the b -> 0 limit of L_{alpha,b} read at 1 - x = b^(1/alpha) y, so BAL and DOM-inf
join continuously at b = 0. Correspondingly D_N/N is of order b_N^(1/alpha) with
b_N = T_-(N)/T_+(N).

The lines alpha_s = 1 and alpha_s = 2 are treated in Section 5. Outside (0,2)^2, the dominated
region with a finite-variance lighter law is covered by Theorem D verbatim, since the lighter law
only needs a local limit theorem and a finite mean.

The other zones. In every region the law has three kinds of zone.
1. A bulk at the scale above.
2. End layers at bounded distance from each end: P_N(N-j) ~ T_+(N) kappa_+(j) and
   P_N(i) ~ T_-(N) kappa_-(i). Here kappa is the renewal mass of the other sign, with the start
   correction of F eq. (kappa).
3. Big-jump zones between the bulk and an end. There one run of macroscopic length carries the
   deviation, and the law is a two-term kernel: a complete giant run times the expected number of
   places it can sit, plus the giant run in progress at N times a renewal mass.

Which zones exist:

| Region | Plus end | Minus end |
|---|---|---|
| FF | big-jump zone + layer | big-jump zone + layer |
| BAL | layer joined to the bulk (no zone) | layer joined to the bulk |
| DOM (plus heavier) | layer joined to the bulk; when mu_- < inf, at the same height T_+(N) as the bulk | big-jump zone of the lighter sign + layer |

## 3. The dominated regime (new)

Plus is the heavier side throughout this section. Assume 0 < alpha_+ < 1, (RV) for both signs with
alpha_- in (0,1) or (1,2), T_-(n) = o(T_+(n)), and (SPAN) for both. Put

- if mu_- < inf: D_N = mu_-/T_+(N), rho = phi_E, omega(j) = 1;
- if alpha_- < 1: D_N = a_-(1/T_+(N)), rho = the density of S_-(1) E^(1/alpha_-), and
  omega(j) = 1/(j T_-(j)) for j >= 1;
- Psi(y) = rho(y) if mu_- < inf, and Psi(y) = rho(y)/((sin(pi alpha_-)/pi) y^(alpha_- - 1)) if
  alpha_- < 1. In both cases Psi(0+) = 1 (Section 3.4);
- (W_+): D_n T_+(n) sum_{m <= delta/T_+(n)} u^+_m(n) -> 0 for some (equivalently every) delta > 0.

Since D_N = o(N), T_+(N - j)/T_+(N) -> 1 uniformly for j <= K D_N.

**Theorem D.** Under these assumptions, for a fresh start of either sign, the following hold.

(a) (Global.) (N - A_N)/D_N converges in law to the law with density rho.

(b) (Lower half, no further condition.) For 0 < y_1 < y_2,
liminf_N inf_{y_1 D_N <= j <= y_2 D_N} (D_N P_N(N - j) - rho(j/D_N)) >= 0.

(c) (Local law.) If mu_- < inf, or alpha_- > 1/2, then
sup_{y_1 D_N <= j <= y_2 D_N} |D_N P_N(N - j) - rho(j/D_N)| -> 0. If alpha_- <= 1/2, this holds if and
only if (SRT_-) and (W_+) hold. (W_+) follows from (SRT_+), hence from (LB_+), and it holds
automatically when alpha_- > 1/2.

(d) (End layers.) For fixed j, P_N(N - j)/T_+(N) -> kappa_+(j), which is u_-(j) for a plus start and
u_-(j) 1{j >= 1} for a minus start. This needs only (RV) for the plus sign. For fixed i,
P_N(i)/T_-(N) -> kappa_-(i), which is u_+(i) 1{i >= 1} for a plus start and u_+(i) for a minus
start. Under the condition of (c), uniformly over 0 <= j <= y_2 D_N,
P_N(N - j) = T_+(N) [kappa_+(j) Psi(j/D_N) + o(omega(j))].

In words, N - A_N is the time spent on the lighter side. The number of cycles is E/T_+(N), and the
lighter time is the lighter sum run up to that random index, S_-(E), which equals mu_- E when
mu_- < inf. The local law needs only two inputs: the local limit theorem for the lighter sums, and a
local form of the inverse renewal count of the heavier runs. The strong renewal theorem enters only
through the lighter law, and only when its mean is infinite with index at most 1/2. In that case
the heavier law must also satisfy the weak condition (W_+).

### 3.1 Two lemmas

**Lemma Q (local inverse renewal count; heavier law, alpha < 1, (RV), (SPAN)).**
(i) q_{m+1}(k) <= C T(k) for all m >= 0 and k >= 1 (G Lemma key, (RV) only).
(ii) q_{m+1}(k) >= T(k)/2 when m T(k) <= delta_0, for some delta_0 > 0.
(iii) sup_{m T(k) <= K} |q_{m+1}(k)/T(k) - phi_E(m T(k))| -> 0 as k -> infinity, for every K.

Proof. (ii) We have q_{m+1}(k) >= P(S_m < k/2) T(k) and P(S_m >= k/2) <= C m T(k), by one big
jump under (RV).

(iii) First let t = m T(k) lie in [eps, K]. Gnedenko's local limit theorem (G Lemma cd(i)) gives
u_m(r) = a_m^{-1}(g(r/a_m) + o(1)) uniformly in r, and a_m/k -> t^{1/alpha}. Write
q_{m+1}(k) = sum_{r<k} u_m(r) T(k - r) and split at r = (1-eta)k.
- The part r < (1-eta)k is a Riemann sum. Since T(k - r)/T(k) -> (1 - r/k)^(-alpha) uniformly, it
  converges to T(k) int_0^{(1-eta) t^(-1/alpha)} g(w) (1 - t^(1/alpha) w)^(-alpha) dw.
- The part r >= (1-eta)k is at most (C/a_m) sum_{i <= eta k} T(i) <= C eta^(1-alpha) T(k), because
  alpha < 1.

Letting eta -> 0 gives the limit

    int_0^{t^(-1/alpha)} g(w)(1 - t^(1/alpha) w)^(-alpha) dw = int_0^1 P(S_+(t) in dx) (1 - x)^(-alpha).

This is the first-passage formula for the density of the inverse subordinator at 1 (driftless,
Levy tail x^(-alpha)), that is, phi_E(t).

Now let t lie in [0, eps]. The lower bound is P(S_m < eta k) T(k) >= (1 - C eta^(-alpha) eps) T(k).
The upper bound is T((1-eta)k) plus the part r >= eta k, which is O_eta(m T(k)) T(k) by the dyadic
estimate in the proof of G Lemma key. Together they squeeze q_{m+1}(k)/T(k) to 1 + O(eps)
uniformly, and phi_E(t) = 1 + O(eps) on [0, eps]. QED

This proof is routine and written at the level of a sketch. All its inputs are in G, Section tools.

**Lemma R (where u(j) lives in m; lighter law, (RV), (SPAN)).**
(i) If mu < inf, then lim_{A->inf} limsup_j sum_{|m - j/mu| > A a(j)} u_m(j) = 0.
(ii) If alpha < 1, then sum_{m > K/T(j)} u_m(j) <= C K^(1 - 1/alpha) / (j T(j)). The middle part
j T(j) sum_{eps/T(j) <= m <= K/T(j)} u_m(j) is a Riemann sum for the corresponding piece of the
integral identity behind (SRT). The small-m part j T(j) sum_{m < eps/T(j)} u_m(j) tends to zero as
eps -> 0, uniformly in large j, iff (SRT) holds (G Lemma cd(iv), from Caravenna-Doney).

Proof. (i) By Gnedenko, sum_{|m - j/mu| <= A a(j)} u_m(j) -> (1/mu) int_{|z| <= A'} g(z) dz, which
tends to 1/mu as A -> inf. By the renewal theorem u(j) -> 1/mu, and the rest is the difference.
(ii) We have sup_x u_m(x) <= C/a_m, and sum_{m > M} 1/a_m <= C M/a_M since 1/a_m has index
-1/alpha < -1. QED

### 3.2 Proof of (b) and (c): the main term I_N(j)

Let j = y D_N with y in [y_1, y_2], and n = N - j, so that T_+(n) ~ T_+(N) uniformly.

Finite mean lighter law. Split I_N(j) by m.
- On the window |m - j/mu_-| <= A a_-(j) we have m T_+(n) = y + O(A a_-(j)/D_N) + o(1) = y + o(1).
  So by Lemma Q(iii) and the uniform continuity of phi_E, q^+_{m+1}(n) = T_+(N)(phi_E(y) + o(1)).
  Summing u^-_m(j) over the window gives 1/mu_- + o_A(1), by Lemma R(i).
- Off the window, q^+_{m+1}(n) <= C T_+(N) by Lemma Q(i), and the u^- mass is o_A(1).

So I_N(j) = (T_+(N)/mu_-)(phi_E(y) + o(1)) = (phi_E(y) + o(1))/D_N. No strong renewal theorem
appears, because with a finite mean the renewal theorem always holds under (SPAN).

Infinite mean lighter law. Here T_-(j) ~ y^(-alpha_-) T_+(N), so 1/T_-(j) and 1/T_+(N) are
comparable. Split m into small (m < eps/T_+(N)), middle and large (m > K/T_+(N)).
- Middle. Gnedenko for u^-_m and Lemma Q(iii) for q^+ turn the sum into a Riemann sum. Using
  a_-(x/T_+(N)) ~ x^(1/alpha_-) D_N,

      T_+(N) sum_m (1/a_-(m)) g_-(j/a_-(m)) phi_E(m T_+(N))
        -> (1/D_N) int_eps^K phi_E(x) x^(-1/alpha_-) g_-(y x^(-1/alpha_-)) dx.

  As eps -> 0 and K -> inf the integral tends to rho(y), the density of E^(1/alpha_-) S_-(1).
- Large m. Lemma Q(i) and Lemma R(ii) bound this part by
  C T_+(N) K^(1-1/alpha_-)/(j T_-(j)) <= C' K^(1-1/alpha_-)/D_N, since
  j T_-(j) ~ y^(1-alpha_-) D_N T_+(N).
- Small m. Lemma Q(i) bounds this part by

      C T_+(N) sum_{m < eps'/T_-(j)} u^-_m(j)
        = C (T_+(N)/(j T_-(j))) [j T_-(j) sum_{m < eps'/T_-(j)} u^-_m(j)].

  Here T_+(N)/(j T_-(j)) is of order 1/D_N, and the bracket vanishes as eps' -> 0 iff (SRT_-) holds
  (Lemma R(ii)).

Necessity. On the small range Lemma Q(ii) gives the matching lower bound
q^+_{m+1}(n) >= T_+(N)/2. So if (SRT_-) fails, the small-m part of I_N is at least c/D_N along a
sequence of j. Since D_{N+1}/D_N -> 1, we can choose N with D_N close to j/y, and this breaks the
local law on every compact y-interval that contains the corresponding ratios.

Part (b). All terms are nonnegative, so dropping the small-m part and R_N gives (b) with no
condition at all.

### 3.3 Proof of (c): the second term R_N(j) (minus run in progress at N)

Infinite mean lighter law. Lemma Q(i) for the minus law gives q^-_m(j) <= C T_-(j), and
T_-(j) ~ y^(-alpha_-) T_+(N). Split at m = delta/T_+(n).
- For m > delta/T_+(n), u^+_m(n) <= C/a_+(delta/T_+(n)) <= C_delta/N, and sum_m q^-_m(j) = 1. So this
  part is O(1/N) = o(1/D_N).
- For m <= delta/T_+(n), the part is at most C T_+(N) sum_{m <= delta/T_+(n)} u^+_m(n). This is
  o(1/D_N) exactly under (W_+).
- (W_+) is also necessary. For delta small, Lemma Q(ii) for the minus law gives q^-_m(j) >= T_-(j)/2
  on this range.

When (W_+) holds:
- If (SRT_+) holds, then sum_m u^+_m(n) = u_+(n) = O(1/(n T_+(n))), and (W_+) reduces to D_N/N -> 0,
  which is true.
- In general, Caravenna-Doney's bound u^+_m(n) <= C (m/a_m) T_+(n) (G Lemma cd(ii)) gives
  sum_{m <= delta/T_+(n)} u^+_m(n) <= C (T_+(n) + 1/(n T_+(n))). Hence D_N T_+(N) times this sum is
  at most C (D_N T_-(D_N)^2 + D_N/N). This tends to zero when alpha_- > 1/2, because x T_-(x)^2 is
  regularly varying with index 1 - 2 alpha_- < 0.

This completes (c) for alpha_- < 1.

Finite mean lighter law (the mixed region). Here q^-_m(j) is not O(T_-(j)) uniformly in m, so a
separate count is needed. Split at m = delta j, with delta mu_- <= 1/4.
- For m > delta j, u^+_m(n) <= C/a_+(delta j). Since j is of order 1/T_+(N), a_+(delta j) is of
  order N, and this part is O(1/N) = o(T_+(N)).
- For m <= delta j, write q^-_m(j) = sum_{r<j} u^-_{m-1}(r) T_-(j - r). The part r < j/2 is at most
  T_-(j/2) <= C T_-(j). For r >= j/2 we have r - (m-1) mu_- >= j/4, and F Lemma stable(iii) (local
  large deviations under (RV) alone) gives u^-_{m-1}(r) <= C m T_-(j)/a_-(m). Summing T_-(j - r)
  over r gives at most mu_-. So

      q^-_m(j) <= C T_-(j) (1 + m/a_-(m))      (m <= delta j).

  Combine this with u^+_m(n) <= C (m/a_+(m)) T_+(n) (Caravenna-Doney, (RV) only). Then the part
  m <= delta j of R_N(j) is at most

      C T_-(j) T_+(N) sum_{m <= delta j} (m/a_+(m)) (1 + m/a_-(m))
        <= C T_+(N) T_-(j) [ max(1, j^2/a_+(j)) + max(1, j^3/(a_+(j) a_-(j))) ].

  Each of the two terms of T_-(j)[...] is regularly varying in j, with indices
  -alpha_- + max(0, 2 - 1/alpha_+) and -alpha_- + max(0, 3 - 1/alpha_+ - 1/alpha_-). Both are
  negative:
  - 2 - 1/alpha_+ < 1 < alpha_-;
  - 3 - alpha_- - 1/alpha_+ - 1/alpha_- < 2 - alpha_- - 1/alpha_- <= 0, since 1/alpha_+ > 1.

So R_N(j) = o(T_+(N)) = o(1/D_N) under (RV) and (SPAN) alone, and the local law in the mixed region
needs nothing else. The margin closes only at the corner alpha_+ = alpha_- = 1.

I expected a condition here and found none. The reason is that in the mixed region the bulk sits at
height T_+(N), the same as the end layer. The run in progress at N costs a factor of order 1/N
relative to T_+(N) unless the plus law is very irregular, and the irregular part is controlled by
the polynomial margin above. So it never competes.

### 3.4 Proof of (d), and the matching

Fixed j. In I_N(j) only m <= j occur. For fixed m, q^+_{m+1}(N - j) ~ T_+(N) by subexponentiality
(P(S_{m+1} >= x) - P(S_m >= x) ~ T(x)), so I_N(j) ~ T_+(N) u_-(j). In R_N(j) only m <= j + 1
occur, and for fixed m, u^+_m(N - j) = o(T_+(N)), because f_+(n) = o(T_+(n)) under (RV). This
needs only (RV) for the plus law. The minus end is the same with the signs exchanged:
q^-_m(N - i) ~ T_-(N) and u^-_m(N - i) = o(T_-(N)) for fixed m. The start corrections are those of
F eq. (kappa).

Uniform matching. First, Psi(0+) = 1.
- If mu_- < inf, this is phi_E(0) = 1.
- If alpha_- < 1, it follows from rho(y) ~ (sin(pi alpha_-)/pi) y^(alpha_- - 1) as y -> 0.
  Substituting x = (y/t)^alpha_- in the mixture integral gives
  rho(y) -> alpha_- y^(alpha_- - 1) E[S_-^(-alpha_-)] phi_E(0) = (sin(pi alpha_-)/pi) y^(alpha_- - 1).

Next take 1 << j << D_N. Every m that carries the mass of u_-(j) has m T_+(N) -> 0, so Lemma Q
gives I_N(j) = T_+(N) u_-(j)(1 + o(1)). The tail sum_{m > K/T_-(j)} u^-_m(j) is
O(K^(1-1/alpha_-)) u_-(j) by Lemma R(ii) when alpha_- < 1, and empty in the limit when mu_- < inf.
The bounds of 3.3 control R_N(j) relative to T_+(N) u_-(j). For alpha_- < 1 the ratio is at most
C j T_-(j)^2 (1 + 1/(N T_+(N)^2)), and it is o(1) under (W_+) when alpha_- <= 1/2. Combined with (c),
this gives the uniform statement. It is the analogue of G Thm ends(b), and routine.

### 3.5 Big-jump zone toward the lighter end (conjectured statement, structure checked numerically)

**Claim K.** Assume in addition (LR) for the minus law. Then, uniformly over K D_N <= j <= N - 1
(in the sense N -> inf, then K -> inf; when mu_- < inf, over K lambda_N D_N <= j, see below),

    P_N(N - j) = [ gamma_+(N - j) f_-(j) + T_-(j) u_+(N - j) ] (1 + o(1)),
    gamma_+(n) = sum_{r=1}^{n-1} u_+(r) = E #{m >= 1 : S^+_m < n} ~ E[E]/T_+(n).

The first term is a complete giant minus run, which can sit after any of the plus runs completed
before plus level n. The second is the giant minus run in progress at N. This is F's kernel
gamma(N-k) f_+(L_k) + T_+(L_k) u_-(N-k), with the signs exchanged and no centering. At j = N - i
with i fixed it reduces to T_-(N) u_+(i), which is (d). Under (SRT_+), at j = vN,

    P_N(N - vN) N T_+(N) / T_-(N) -> (sin(pi alpha_+)/pi) v^(-alpha_-) (1 - v)^(alpha_+)
                                      [ alpha_-/(alpha_+ v) + 1/(1 - v) ],

which is an infinite density for the dominated regime.

How the bulk joins the kernel:
- For alpha_- < 1 the tail of rho, rho(y) ~ alpha_- E[E] y^(-alpha_- - 1), matches the first term at
  j = y D_N. So the bulk and the kernel join with no window, as on the dominant side in F.
- When mu_- < inf, the bulk phi_E decays super-exponentially,
  P(E > x) = exp(-c x^(1/(1-alpha_+)) (1+o(1))), while the kernel is polynomial. So the kernel takes
  over only at y of order (log N)^(1-alpha_+). This is a window of the same kind as F's lambda_N
  window, and presumably has the same answer (bulk plus kernel, additively).

Status: not proved. The proof should be F's Section bigjump, with two inputs: a local big-jump bound
for sums of m lighter runs, uniform in m <= K/T_+(n) (of the type of Berger PTRF 2019 Thm 2.4 under
(LR)), and Lemma Q for the plus side. This is new work, but along F's lines.

### 3.6 Shape in the dominated regime

Take mu_- < inf and a log-convex lighter law, so that u_- decreases to 1/mu_-. Near the plus end
the profile is T_+(N) u_-(j) phi_E(j/D_N).
- If alpha_+ <= 1/2, phi_E is decreasing, and the end k = N is the only mode on that side.
- If alpha_+ > 1/2, phi_E has an interior mode y*. Then P_N has an interior mode at distance about
  y* D_N from the end, as well as the mode at the end.

The global mode is the end iff max phi_E < mu_-. For zeta laws with alpha_+ = 0.6 and
alpha_- = 1.5, max phi_E = 1.131 < mu_- = 1.947, so the end wins. An exact mode count in the style
of F Thm mode-count looks plausible here, and easier than in F because the bulk is not a stable
density with two-sided tails. I have not tried it.

### 3.7 Initial run in the dominated regime (outline only)

The first-run decomposition (F Prop. first-run) works unchanged.

Minus initial run. A minus initial run of length d shifts j by d, and the defect is
T_+(N) sum_i nu_-(j - i) u_-(i).
- If mu_- < inf, u_- is bounded, and the defect is O(T_+(N) P(D in [j/2, j])) = o(1/D_N) for every
  initial run that is finite almost surely.
- If alpha_- < 1, it is G's defect with D_N T_+(N) in place of N T_+(N). The necessary condition
  becomes nu_-(n) = o(1/(n T_-(n))), and n nu_-(n) -> 0 should suffice under (LB_-), as in G Thm
  initial(b),(c).

Plus initial run. A plus initial run changes the horizon from N to N - d, and the bulk is
continuous in the horizon on the scale N. What remains is a uniform bound for the contribution of
d close to N, which I have not done.

So in the mixed region the bulk probably needs no condition on the initial run, as in F. With
alpha_- < 1 it needs G-type conditions on the lighter initial run. An initial run of length of
order N (aging) gives a mixture over D_{N-d}. This is easier than G's aging conjecture, because when
mu_- < inf the dominant end and the bulk are at the same height.

### 3.8 What is known in distribution

Part (a) is a distributional statement of Darling-Kac or Lamperti type.
- In the mixed region, the lighter time divided by 1/T_+(N) has a Mittag-Leffler limit. This is the
  Darling-Kac theorem for the time spent in a finite-mean part of a null-recurrent system.
- Lamperti 1958 covers the occupation fraction for every b in [0, inf], and the limit is
  degenerate for b in {0, inf}.
- Mitov and Yanev 2001 treat occupation times of alternating renewal processes with infinite-mean
  cycles.

I have not checked which of these states the scaled limit of N - A_N in the unequal-index case. So
after checking, the merged paper should cite (a) as standard and claim only (b)-(d) and Claim K. I
found no local version.

## 4. A unified statement for the merged paper

**Theorem (the local occupation law on (0,2)^2).** Assume (RV) with alpha_+, alpha_- in
(0,1) u (1,2), (SPAN), a fresh start, and, if alpha_+ = alpha_- < 1, that b = lim T_-/T_+ exists in
[0, inf]. Then exactly one of the following holds.

1. (Finite means.) alpha_+, alpha_- > 1, and sup_k |B_N P_N(k) - h_N((k - pN)/B_N)| -> 0. [F]
2. (Balanced infinite means.) alpha_+ = alpha_- < 1 and 0 < b < inf. Then
   N P_N(k) = L_{alpha,b}(k/N) + o(1) on compacts of (0,1) iff (SRT_+) and (SRT_-), and iff it holds
   at one point. [G]
3. (Dominated.) Otherwise one side, say plus, has the heavier tail, and alpha_+ < 1. Then
   D_N P_N(N - j) = rho(j/D_N) + o(1) on compacts of (0, inf). This always holds if the lighter mean
   is finite or alpha_- > 1/2, and otherwise iff (SRT_-) and (W_+). [Theorem D]

In all three cases, for fixed j and i, P_N(N - j)/T_+(N) -> kappa_+(j) and
P_N(i)/T_-(N) -> kappa_-(i) under (RV) alone, and the layer joins the bulk uniformly (F Thm
bigjump and bulk; G Thm ends(b); Theorem D(d)). Between the bulk and an end that is not joined to
it, the law is the two-term big-jump kernel: [complete giant run x number of places] + [giant run in
progress x renewal mass]. This is F Thm bigjump in case 1, and Claim K (conjectural) in case 3.

Case 3 has a compact description that also explains cases 1 and 2. N - A_N is the time on the
lighter side. When the heavier mean is infinite, the heavier side alone sets the number of cycles.
Case 2 is the only case where both sides set the number of cycles together.

What is proved where:
- Proved in F: all of case 1, including unequal scales and the window; the end layers and the
  big-jump kernel for 1 < alpha < 2; the initial run; the modes.
- Proved in G: case 2 (equal indices, b in (0, inf)), with its end layers and matching, and the
  initial run.
- Proved here at the level of a proof sketch, and routine given F and G: Theorem D(a)-(d). This
  covers the mixed region, unequal infinite means, and b in {0, inf}. The only new estimates are
  Lemma Q (the local inverse renewal count) and the count in 3.3 for the mixed region. Both use
  only lemmas already in F and G: Gnedenko, Caravenna-Doney's local bound, F Lemma stable(iii) and
  G Lemma key. The one-point equivalence in case 3 should follow as in G Thm 1 ((i) => (iii)), but I
  have not checked it.
- Needs new work: Claim K (the big-jump kernel toward the lighter end in case 3) and its window when
  mu_- < inf; the initial-run theorem in case 3 (plus initial runs); the boundaries of Section 5.

## 5. The boundaries (conjectures)

Write m_s(x) = sum_{n <= x} T_s(n) for the truncated mean, and a_s(t) for the scale with
t T_s(a_s(t)) -> 1.

C1 (lighter law at alpha_- = 1, heavier alpha_+ < 1). Theorem D holds with
D_N = b_-(1/T_+(N)), where b_-(t) = t m_-(a_-(t)) (= mu_- t if mu_- < inf), and rho = phi_E. The
reasons:
- relative stability gives S^-_m / b_-(m) -> 1;
- Gnedenko's local theorem holds in the Cauchy domain with the centering b_-(m);
- at alpha_- = 1 the exponent count of 3.3 gives -(1/alpha_+ - 1) < 0, so R_N is still negligible.

This is probably a routine extension. Convergence is at rate 1/log N (Section 6, P6).

C2 (heavier law at alpha_+ = 1 with infinite mean, lighter alpha_- in (1,2)). Here the
Mittag-Leffler mixture collapses (E -> 1 as alpha_+ -> 1). The number of cycles is
N/m_+(N) (1 + o_p(1)), and (N - A_N) m_+(N)/(mu_- N) -> 1 in probability. This is relative
stability, with no limit law at first order. Conjecture:

    (N - A_N - c_N)/sigma_N => -C_+,   sigma_N = mu_- a_+(N/m_+(N))/m_+(N),

with C_+ a totally skewed 1-stable law and c_N an explicit centering built from m_+. Moreover
sigma_N P_N(N - c_N - x sigma_N) converges to the density of -C_+ uniformly on compacts, under
(SPAN). The fluctuations of the lighter sums, of order a_-(N/m_+(N)), are smaller by a polynomial
factor, so they do not enter.

C3 (balanced at alpha_+ = alpha_- = 1 with infinite means, m_-(x)/m_+(x) -> beta in (0, inf)).
Relative stability gives A_N/N - p_N -> 0, with p_N = m_+(N)/(m_+(N) + m_-(N)) -> 1/(1+beta).
Conjecture: put sigma_N = N L(N)/m(N), with L(x) = x (T_+(x) + T_-(x)) and m = m_+ + m_-, and let
c_N = p_N N + O(sigma_N) be the centering given by the truncated means at the level a(N/m(N)). Then

    sigma_N P_N(k) - h_N((k - c_N)/sigma_N) -> 0 uniformly in k,

where h_N is the density of (1 - p_N) theta_+ C_+ - p_N theta_- C_- and C_s is totally skewed
1-stable. The centering correction is of the same order as sigma_N (logarithmic corrections),
which is why this needs care. With finite means at alpha = 1 (sum T_s < inf), the conjecture is F's
Theorem bulk with the 1-stable profile and the centering
pN + (N/s)[(1-p)(m_+(b_+) - mu_+) - p (m_-(b_-) - mu_-)]. F's big-jump kernel should hold verbatim.

C4 (alpha = 2 and finite variance).
- Lighter law with finite variance or alpha_- = 2, and alpha_+ in (1,2): F's Theorem bulk holds
  with theta_- -> 0, since the Gaussian part lives on the scale sqrt(N L(N)) = o(B_N). F's proof
  should go through, the only change being the local limit theorem for the lighter sums.
- Both with finite variance: the local CLT at scale sqrt(N), from Takacs' CLT plus a lattice local
  limit theorem (routine).
- alpha_+ = 2 with infinite variance: a Gaussian bulk at scale sqrt(N l(N)), with l slowly varying
  (the truncated second moment). F's big-jump kernel should hold beyond the Nagaev threshold
  k - pN >= (1 + eps) sqrt(c N l(N) log N), and fail below it.
- alpha_+ < 1 with a finite-variance lighter law: Theorem D applies as stated.

## 6. Computations

Scripts.
- `01_exact_law.py` computes the exact law by the run recursion. It agrees with brute force over
  all sign strings for N <= 11 and both starts (max deviation 2.2e-16).
- `01_compare.py` runs all the comparisons, with output in `01_compare_output.txt`.

Zeta laws, a fresh plus start unless stated, and N = 1000, 2000, 4000. P_N is exact, computed by
the O(N^3) recursion, which uses nonnegative terms only. Two checks of the density code:
- the quadrature for the ratio density at alpha = 0.7 agrees with the closed form of Section 2 to
  10 digits;
- phi_E at alpha = 1/2 agrees with exp(-pi x^2/4) to 8 digits.

The "mixture" is the main term of the proof evaluated at finite N with exact convolution powers,
T_+(N - j) sum_m u^-_m(j) phi_E(m T_+(N - j)). It separates the plus-side approximation (Lemma Q)
from the slow convergence of the lighter sums.

Max relative error on a core interval (the ratios at single points are in the output file):

| Case | N = 1000 | N = 2000 | N = 4000 |
|---|---|---|---|
| P1 mixed (0.6, 1.5), limit phi_E, y in [0.05, 1] | 0.304 | 0.247 | 0.201 |
| P1 mixture | 0.181 | 0.133 | 0.098 |
| P1 layer x bulk T_+ u_-(j) phi_E, 0 <= y <= 1 | 0.331 | 0.271 | 0.221 |
| P2 unequal (0.5, 0.8), limit rho, y in [0.1, 3] | 0.588 | 0.533 | 0.478 |
| P2 mixture | 0.142 | 0.104 | 0.078 |
| P2 layer x bulk, 0 <= y <= 3 | 0.218 | 0.205 | 0.193 |
| P6 boundary (0.6, 1), limit phi_E, y in [0.05, 1] | 0.245 | 0.239 | 0.233 |
| P6 mixture | 0.304 | 0.230 | 0.175 |
| P4 F region (1.3, 1.8), B_N P_N / h_N, abs(x) <= 2 | 0.188 | 0.156 | 0.146 |
| P5 G region (0.7, 0.7), max abs N P_N - L on [0.1, 0.9] | 0.122 | 0.105 | 0.089 |

Where the errors sit.
- P1. At N = 4000 the layer x bulk formula is within 2% for y <= 0.3, a range that contains the
  interior mode, and the mixture is within 0.5% there. The error grows on the right (at y = 1 the
  mixture is off by 10%). That is the lower-deviation side of the plus renewal count, where phi_E
  decays super-exponentially. Near y = 0.05-0.2 the ratio to the limit is 1.08-1.13 at N = 4000,
  because u_-(j) - 1/mu_- decays only like j^(1 - alpha_-). The layer x bulk formula removes this.
- P2. The limit converges slowly because S^-_m/a_-(m) carries a drift term of relative size
  m^(1 - 1/alpha_-), with m ~ 1/T_+(N) ~ 83 at N = 4000. So the rate is about
  N^(-alpha_+(1/alpha_- - 1)) = N^(-0.125). A post hoc refinement with the drift,
  S^-_m ~ a_-(m) S_- + m zeta(alpha_-)/zeta(alpha_- + 1), brings the ratio within 8% on the core (last
  column in the output). At N = 4000 the layer x bulk formula is within 1.4% for y <= 0.5.

End layers (Theorem D(d)). At N = 4000 the ratio P_N(N - j)/(T_+(N) u_-(j)) for j = 0..5 lies in
1.0000-1.0172 for P1, 1.0000-1.0003 for P2 and 1.0000-1.0153 for P6. At the minus end the ratio
P_N(i)/(T_-(N) u_+(i)) for i = 1..5 is within 0.9% in all three. All of these drift to 1 with N.

Big-jump kernel (Claim K). The ratio P / [gamma_+ f_- + T_- u_+] at j = vN:

| Case | N | v = 0.5 | v = 0.8 | v = 0.95 |
|---|---|---|---|---|
| P1 | 1000 | 1.660 | 1.188 | 1.063 |
| P1 | 4000 | 1.313 | 1.103 | 1.037 |
| P2 | 1000 | 1.560 | 1.247 | 1.096 |
| P2 | 4000 | 1.445 | 1.184 | 1.074 |

In P1 at v = 0.2 the ratio is 3.4. That point is inside the predicted window (j/D_N = 2.1, where
the bulk still dominates). Every ratio decreases toward 1, slowly. This is consistent with Claim K,
but at these sizes it does not confirm the constant.

Modes.
- P1 has strict local maxima exactly at k = 1, N - 34, N (N = 1000), at k = 1, N - 54, N (N = 2000)
  and at k = 1, N - 86, N (N = 4000). At N = 4000, y* D_N = 0.278 x 387 = 108. The observed 86 is
  pulled toward the end by the decreasing factor u_-(j).
- P7 (alpha_+ = 0.4). For a fresh plus start the maxima are exactly at k = 1 and k = N, for all
  three N. For a fresh minus start they are at k = 0 and N - 1.

Score of the predictions.
- P1: the rate is confirmed (0.304, 0.247, 0.201, about N^(-0.3)), but the stated bound "below 0.2 at
  N = 4000" missed narrowly (0.201). The layer prediction (within 3% for j <= 5) is confirmed (1.7%),
  and so are the three modes at k = 1, an interior point and N.
- P2: failed. The limit error at N = 4000 is 0.478, not below 0.25, and it decreases only slowly
  (the drift term, rate about N^(-0.125)). The kernel prediction (within 0.3) failed for v <= 0.65
  (ratios 1.30-1.80).
- P3: confirmed in P1 (0.098 against 0.201, a factor 2.05) and in P2 (0.078 against 0.478). In P6
  it holds only from N = 2000 on; at N = 1000 the mixture is worse than the limit on the core (0.304
  against 0.245).
- P4: failed as stated (0.146, not below 0.1). The errors are 15% on the light-tail side x = -2 and
  8% at the center, and they decrease slowly with theta_- (0.33 -> 0.24).
- P5: failed as stated (0.089, not below 0.05). The ratio at the center, 0.928, approaches 1 slowly.
- P6: as predicted, the limit error is about 0.23 and nearly flat. The prediction that the mixture
  stays within 0.1 failed (0.175 at N = 4000, decreasing).
- P7: confirmed for the fresh plus start. For the fresh minus start the mode at k = N - 1 is
  confirmed, but the minus-end mode is the atom k = 0 (P_N(0) = T_-(N) for a minus start), not k = 1
  as I wrote.

Overall, every structural claim agrees with the exact law: the scales, the limit shapes, the
layers, the matching, the structure of the kernel and the modes. The errors decrease with N in
every case. My quantitative error guesses were too optimistic everywhere except P1. The main cause
is finite-m drift corrections in the stable approximations, which are slow when the indices are
near 1 or when there are few cycles (P2 has about 83 cycles at N = 4000).

## 7. Summary for the merge

- Leaving out the lines alpha = 1 and alpha = 2, the square (0,2)^2 has three regimes: finite means
  (F), balanced infinite means (G), and the dominated regime. The dominated regime is new. It covers
  mixed indices, unequal infinite-mean indices, and equal indices with b in {0, inf}, and it is the
  larger part of the diagram that neither paper covers.
- In the dominated regime the count of the lighter side lives at the scale D_N. This is
  mu_-/T_+(N) when the lighter mean is finite, and a_-(1/T_+(N)) when it is infinite. The limit is
  S_-(E). The local law holds with no renewal condition when the lighter mean is finite or
  alpha_- > 1/2. Otherwise it holds iff (SRT_-) and the weak condition (W_+) on the heavier law. The
  proof sketch above is built from lemmas already in F and G.
- The headline for the merged paper is the three-case theorem of Section 4, with the common end
  layers and the common two-term kernel. Parts 1 and 2 are F and G. Part 3 is Theorem D, proved
  here at sketch level and still to be written out. The kernel in part 3 and the boundaries are
  open.
