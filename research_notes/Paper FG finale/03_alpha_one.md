# 03. The boundary alpha = 1: the occupation count in the Cauchy domain

Research note for the merged paper (F + G). Scripts in this folder: `03_alpha_one_engine.py`
(exact law, two independent methods and a brute force), `03_alpha_one_checks.py` (all
comparisons), output in `03_alpha_one_output.txt`.

## 0. Predictions (written before any code was run, 2026-10-26)

Notation (fixed in Section 1). T(n) = P(X >= n) = L(n)/n with L slowly varying (tail index 1).
mu(x) = sum_{n <= x} n f(n), the truncated mean, slowly varying. For m > 0, a(m) solves
m T(a) = 1. m_N solves m [mu_+(a_+(m)) + mu_-(a_-(m))] = N. p_N = mu_+(a_+)/(mu_+(a_+) + mu_-(a_-))
at m = m_N, and sigma_N = (1 - p_N) a_+ + p_N a_-. W_N = (1-p_N) a_+ Z - p_N a_- Z', with Z, Z'
independent, Levy measure x^-2 dx on (0, inf), compensated by x 1{x <= 1}.

Laws (all defined by their tails, so they are exact probability laws):
 Q1: T(n) = 1/n, f(n) = 1/(n(n+1)), L = 1, mu(x) = H_{x+1} - 1 ~ log x.
 Q2: T(n) = log 2 / (n log(n+1)), f ~ log 2 / (n^2 log n), L ~ log 2/log n, mu ~ log 2 log log x.
 Q3: T(n) = 2/(n+1), L -> 2, mu ~ 2 log x (comparable to Q1 with ratio 2).
 H : T(n) = n^(-1/2) (index 1/2). K : T(n) = n^(-3/2) (index 3/2, mean zeta(3/2)).

- P1 (engine). The transform engine agrees with the direct run recursion to 1e-12 (absolute) for
  N <= 300, and both agree with a sum over all sign strings for N <= 12.
- P2 (Cauchy bulk, Q1 both signs, fair start). With gamma_N = (pi/2) sigma_N = pi m_N / 2:
  (a) R_N = pi gamma_N P_N(N/2) is within 0.15 of 1 at N = 8000 and |R_N - 1| decreases in N
      (N = 1000, 2000, 4000, 8000). Error of relative order L/mu ~ 1/log N, so slow.
  (b) The half-width at half maximum divided by gamma_N is within 0.15 of 1 at N = 8000.
  (c) With the fitted scale, P_N(N/2 + x)/P_N(N/2) matches 1/(1 + (x/gamma_fit)^2) within 0.05
      (absolute) for |x| <= 3 gamma_fit.
- P3 (Q2 both signs, fair start, barely infinite mean). The same Cauchy law with a = a(m_N),
  a = m log 2 / log(a+1). R_N within 0.15 of 1 at N = 8000. The peak is much narrower:
  gamma_N / N about 0.03 to 0.05.
- P4 (unequal but comparable, Q1 plus and Q3 minus, fresh plus start). p_N -> 1/3 slowly. The
  local law is the 1-stable density h_N of W_N, whose skewness beta_N -> 0, so the limit is a
  symmetric Cauchy law. Max of |sigma_N P_N(k) - h_N((k - p_N N)/sigma_N)| over |k - p_N N| <=
  3 sigma_N is below 0.1 times max h_N at N = 8000 and decreasing in N. |beta_N| < 0.1 at N = 8000.
- P5 (end layer, Q1 both, fresh plus). P_N(N - j)/T_+(N) within 1% of u_-(j) for j <= 10 at
  N = 8000. Here u_-(j) ~ 1/mu_-(j) -> 0 (Erickson), unlike F where u -> 1/mean.
- P6 (big-jump kernel, Q1 both, fresh plus). With j = N - k, rbar = mu_+(a_+(j))/mu_-(a_-(j)) at the
  scale of j, L_k = k - rbar j, and
      K_N(k) = T_+(L_k) u_-(j) + f_+(L_k) (j / mu_-(j)) (1 + mu_+(L_k)/mu_-(j)),
  the ratio P_N(k)/K_N(k) lies in [0.8, 1.25] for L_k/N in [0.2, 0.8] at N = 8000. On the
  ballistic scale this is the infinite density T_+(N)/mu_-(N) * l^-2 (the alpha = 1 member of F's
  family (1-l) l^-2 + l^-1).
- P7 (antimode, Q1 both, fresh plus). f is log-convex, u_- is decreasing, and the interior
  minimum of P_N between the bulk and the plus end sits at N - j* with
  T_-(j*) ~ 2(mu_+ + mu_-)/N, that is j* ~ N/(4 mu(j*)) for Q1. Within 30% at N = 8000.
- P8 (mixed, Q1 plus, H minus, fair start). A_N is not relatively stable in N: with
  D_N = mu_+(1/T_-(N)) / T_-(N), D_N P_N(k) -> e^{-pi y^2/4} at y = k/D_N (half-normal density of
  Z^(-1/2), Z the 1/2-stable law with Laplace transform exp(-sqrt(pi lambda))). Max absolute
  error on y in [0.2, 1.5] below 0.2 at N = 8000, decreasing. E[A_N]/D_N within 20% of 2/pi.
- P9 (mixed, Q1 plus, K minus, fresh plus). Relatively stable, the local law is h_N (now with Z'
  of index 3/2), dominated by the Cauchy-domain plus side, so right-skewed: the right tail of
  P_N around p_N N is heavier than the left. Max error as in P4 below 0.1 max h_N at N = 8000.
- P10 (bridge to G). The Lamperti density with alpha_eff = 1 - L(a_N)/mu(a_N) and b = 1,
  divided by N, matches P_N for Q1 about as well as the Cauchy law (P2), since both are the same
  to leading order. With alpha_eff = 1 - N T(N)/mu(N) (scale N instead of a_N) the width is too
  small by about 30% at N = 8000.

(The predictions above were not edited after the computations. Section 8 scores them.)

## 1. Setting, notation, standing facts

Runs alternate in sign and are independent. The plus runs have mass function f_+ and tail
T_+(n) = P(X_+ >= n), the minus runs likewise. A_N is the number of plus steps among the first
N, and P_N(k) = P(A_N = k). The start is a fresh plus start unless stated. The fresh minus start
is the mirror image, and the fair start is the average of the two.

(RV1) T_s(n) = L_s(n)/n for s = +, -, with L_s slowly varying. Equivalently X_s is in the
domain of attraction of a totally right-skewed 1-stable law (Berger, PTRF 2019, (1.1) with
alpha = 1, p = 1, q = 0).

(SPAN) The support of each run law is not contained in a proper arithmetic progression.

(CMP) 0 < liminf L_+/L_- <= limsup L_+/L_- < infinity (comparable slowly varying parts).
This is the "equal indices" case of the task. Section 6 drops it.

Truncated mean: mu_s(x) = E[X_s; X_s <= x] = sum_{n <= x} n f_s(n). It is slowly varying,
mu_s(x) -> E X_s in (0, infinity], and L_s(x)/mu_s(x) -> 0. If E X_s = infinity this is
Bingham-Goldie-Teugels Prop. 1.5.9a, which Berger uses in Section 3. If E X_s < infinity, then
sum L_s(n)/n < infinity forces L_s -> 0. The de Haan function m_s(x) = sum_{n <= x} T_s(n)
differs from mu_s(x) by x T_s(x+1) = L_s(x)(1 + o(1)). So the two are interchangeable to first
order but not to second order, which matters numerically (Section 8).

Scales. For t >= 1 let a_s(t) = inf{x >= 1 : T_s(x) <= 1/t}. Then t T_s(a_s(t)) -> 1 and
a_s(t) = t L_s(a_s(t))(1 + o(1)) (Berger (1.2)). Put b_s(m) = m mu_s(a_s(m)) and
s(m) = b_+(m) + b_-(m), which is nondecreasing in m. For N let m_N solve s(m_N) = N (up to O(1),
since s has jumps of order 1), and put
 a_+ = a_+(m_N), a_- = a_-(m_N), V_N = mu_+(a_+) + mu_-(a_-), p_N = mu_+(a_+)/V_N,
 sigma_N = (1 - p_N) a_+ + p_N a_-,  rho_N = sigma_N / V_N.
Then b_+(m_N) = p_N N and b_-(m_N) = (1 - p_N) N. Note that rho_N/m_N is of order L/mu -> 0: the
number of completed cycles fluctuates on a scale much smaller than its size (relative
stability), and sigma_N/N -> 0.

Limit laws. Z denotes the 1-stable variable with Levy measure x^-2 dx on (0, inf), compensated
by x 1{x <= 1}:
 E e^{iuZ} = exp(psi_1(u)),  psi_1(u) = -(pi/2)|u| - i u log|u| + i (1 - gamma_E) u.
It is the limit of (S_m - b(m))/a(m) for a sum of m runs (Berger (1.3)-(1.4): b_n = n mu(a_n)
with mu(x) = E[X 1{|X| <= x}] when alpha = 1). The output checks the closed form of psi_1
against quadrature. Let Z, Z' be independent copies, and
 W_N = (1 - p_N) a_+ Z - p_N a_- Z',   w_N = (1 - p_N) a_+ / sigma_N.
W_N / sigma_N = w Z - (1 - w) Z' is 1-stable with exponent
 -(pi/2)|u| - i (2w - 1) u log|u| - i u [w log w - (1 - w) log(1 - w)] + i (1 - gamma_E)(2w - 1) u,
that is, scale pi/2, skewness beta_N = 2 w_N - 1 and a bounded location term. Let h_N be its
density. The family {h_N} is indexed by w in [0, 1] and is compact in the uniform topology.

## 2. Sources: what was verified

Read in full text (arXiv:1706.07924v4, the preprint of the PTRF paper, downloaded to a scratch
folder and not added to the repo):

- Berger, Notes on random walks in the Cauchy domain of attraction, PTRF 175 (2019) 1-44.
  * (1.1)-(1.3): the tail hypothesis, the scale n L(a_n)/a_n -> 1, and the centering
    b_n = n mu(a_n), mu(x) = E[X 1{|X| <= x}], at alpha = 1.
  * (1.4): Gnedenko's local limit theorem sup_x |a_n P(S_n = x) - g((x - b_n)/a_n)| -> 0
    (Berger cites Gnedenko-Kolmogorov, Ch. 9, Sec. 50). Used as stated.
  * Theorem 2.1: P(S_n - b_n > x) ~ n p L(x) x^-1 as x/a_n -> infinity, at alpha = 1 with no
    restriction on b_n.
  * Theorem 2.3 (alpha in (0, 2), new at alpha = 1): there is C_0 with
      P(S_n - floor(b_n) = x) <= C_0 (n / a_n) L(|x|) (1 + |x|)^-1  for all x in Z.
    This is the only local large deviation input of Theorem A. Berger's (2.4) says it is
    optimal under (1.1) alone.
  * Theorem 2.4: under the local bound (2.5) P(X = x) <= C_1 L(x) x^-2, the bound
    P(S_n - b_n = x) <= C n L(x) x^-2 holds for x >= a_n. Under (2.7) P(X = x) ~ p L(x) x^-2,
    P(S_n - b_n = x) ~ n p L(x) x^-2 as x/a_n -> infinity. This is the input of the big-jump
    kernel (Section 5).
  * Lemma 4.3: mu(a_n) ~ mu(n mu(a_n)) (Berger takes the proof from his reference [1]).
  * Section 3.2, display (3.6): "Erickson [13] also proved that P(x in S) ~ 1/mu(x) if alpha = 1
    with |mu| = +infinity", for a renewal process (X_1 > 0). Here [13] = K. B. Erickson, Strong
    renewal theorems with infinite mean, Trans. AMS 151 (1970) 263-291. No local hypothesis is
    attached. Berger's Theorem 3.6 recovers the statement for general walks under (2.5)-(2.6).
- Caravenna and Doney, Local large deviations and the strong renewal theorem (arXiv v3, copy in
  research_notes/Occupation novelty and compact advances/evidence_02). Remark 1.2: "The Cauchy
  case alpha = 1 is left out from our analysis, because of the extra care needed to handle the
  centering issues. However, an analogue of Theorem 1.1 holds also in this case, as shown by
  Q. Berger [Ber17]." Their Section 1.2 assumes alpha in (0, 1) and says that the strong renewal
  theorem holds for alpha > 1/2, "see [GL62, Wil68, Eri70, Eri71]". They say nothing more about
  alpha = 1.

Not read directly: Erickson 1970 itself (the AMS server returned a bot check). The statement
u(n) ~ 1/mu(n) at alpha = 1 is used as Berger quotes it in (3.6), and it is checked numerically
below: u(j) mu(j) = 0.57, 0.75, 0.84, 0.88 at j = 10, 1e2, 1e3, 8e3 for Q1, and 0.82, 0.93,
0.96, 0.97 for Q2. The convergence is logarithmic. In the paper it should be cited as Erickson
(1970), with Berger (3.6) as the pointer, once the theorem number in Erickson has been read.
Theorem A needs only the upper bound u(n) <= C/mu(n). In the finite-mean case that bound is the
elementary renewal theorem.

A point for the merged paper: at alpha = 1 the strong renewal theorem needs no local hypothesis,
unlike alpha <= 1/2, where G assumes (SRT) or Doney's (LB). So no analogue of G's (SRT) appears
in Theorem A.

## 3. Theorem A: the local Cauchy law in the bulk

**Theorem A.** Assume (RV1) and (SPAN) for both signs, and (CMP). For a fresh plus, fresh minus
or fair start and every K < infinity,
 sup_{|k - p_N N| <= K sigma_N} | sigma_N P_N(k) - h_N((k - p_N N)/sigma_N) | -> 0.

**Corollary A1 (global law).** (A_N - p_N N)/sigma_N - W_N/sigma_N -> 0 in distribution (Levy
metric), and A_N/N - p_N -> 0 in probability. A_N/N converges in law if and only if p_N
converges, and the limit is then a point mass. So A_N/N never has a nondegenerate limit when
both indices equal 1. For tightness: the mass of the window tends to the h_N-mass of [-K, K],
and {h_N} is a compact family.

**Corollary A2 (symmetric Cauchy law).** If both means are infinite and L_+/L_- -> c in
(0, inf), then w_N -> 1/2 and h_N converges uniformly to the Cauchy density with scale pi/2. So
 P_N(k) = (1 + o(1)) / (pi gamma_N) * 1/(1 + ((k - p_N N)/gamma_N)^2) + o(1/gamma_N),
 gamma_N = (pi/2) sigma_N,
uniformly on |k - p_N N| <= K gamma_N. Indeed mu_+ ~ c mu_- (integrate L/u), so
p_N -> c/(1+c) and (1-p_N) a_+ / (p_N a_-) -> 1, and the location term vanishes with 2w - 1. For
equal laws and a start that is symmetric under exchange of the signs (for example the fair
start), p_N = 1/2 and the limit is centered exactly at N/2. Examples: for Q1, a = m,
m_N ~ N/(2 log N) and gamma_N ~ pi N/(4 log N). For Q2, gamma_N ~ pi N/(4 log N log log N). In
general sigma_N ~ N (mu_- L_+ + mu_+ L_-)/V^2, with L and mu evaluated at the scales a_+, a_-
and not at N (for wild L the two differ to first order).

**Corollary A3 (finite means).** If E X_+, E X_- < infinity, then p_N -> p = E X_+/(E X_+ + E X_-),
but p_N N - p N ~ N [E(X_+; X_+ > a_+) (1-p) - E(X_-; X_- > a_-) p]/(E X_+ + E X_-) up to
O(sigma_N), and E(X; X > a) / L(a) -> infinity. So the naive centering pN is off by many units
of sigma_N. This is the alpha = 1 centering problem of Berger, Section 4. Here h_N is a skewed
1-stable density unless the two tail constants balance (w_N -> 1/2 iff (1-p) L_+ ~ p L_-).

### 3.1 Two lemmas

**Lemma 1 (local left deviations).** Let X >= 1 satisfy (RV1), and put a_m = a(m),
b_m = m mu(a_m), u_m(x) = P(S_m = x). There are C, c > 0 with
 u_m(b_m - x) <= (C/a_m) e^{-c x / a_m}  for all m >= 1, x >= 0.

Proof. (i) sup_y u_m(y) <= C/a_m for all m: this is Gnedenko's theorem for m >= m_0, and a_m is
bounded for m < m_0. (ii) Truncate: X~ = X 1{X <= a}, a = a_m. Then S_m >= S~_m, E S~_m = b_m,
|X~ - E X~| <= a, and by summation by parts
E[X^2; X <= a] <= sum_{n <= a}(2n - 1) T(n) <= 2 sum_{n <= a} L(n) ~ 2 a L(a) (Karamata), so
Var S~_m <= C m a L(a) <= C a^2 since m L(a) ~ a. Bernstein's inequality gives
P(S_m - b_m <= -x) <= exp(-x^2 / (2(C a^2 + a x/3))) <= exp(-c x/a) for x >= a. (iii) The local
form. Write m = m_1 + m_2 with m_1 = floor(m/2). Since mu(a_.) is nondecreasing, the defect
D = b_m - b_{m_1} - b_{m_2} lies in [0, m (mu(a_m) - mu(a_{m_1}))], and
mu(a_m) - mu(a_{m_1}) <= a_m T(a_{m_1}), so D <= C a_m. If S_{m_1} + S'_{m_2} = b_m - x, then one of
the two partial sums lies below its centering by at least (x - D)/2. Condition on the other and
use (i): u_m(b_m - x) <= 2 (C/a_{m_2}) exp(-c (x - D)/(2 a_{m_1})) <= (C'/a_m) e^{-c' x/a_m},
using a_{m_1} >= c a_m. For x < a the claim is (i). QED.

**Lemma 2 (bivariate local renewal theorem at alpha = 1).** Assume the hypotheses of Theorem A.
Let A(k, j) = sum_{m >= 0} u+_m(k) u-_m(j) and B(k, j) = sum_{m >= 1} u+_m(k) u-_{m-1}(j). These
are the probabilities that a plus run, respectively a minus run, starts right after exactly k
plus and j minus steps, for a fresh plus start. For every K, uniformly in k + j = n and
|k - p_n n| <= K sigma_n,
 sigma_n V_n A(k, j) = h_n((k - p_n n)/sigma_n) + o(1),   and the same holds for B.

Proof. Write m_* = m_n, rho = rho_n and x = k - p_n n. Under (CMP), a_+(m) and a_-(m) are both of
the order of sigma for m in [delta m_*, 2 m_*], mu_+ and mu_- are of the order of V, and
rho/m_* -> 0. Split the sum over m into four ranges.

(IV) |m - m_*| <= W rho (the main window). For such m, a_s(m) = a_s(m_*)(1 + o(1)), and
b_s(m) = b_s(m_*) + (m - m_*) mu_s(a_s(m_*)) + o(sigma), because
m_* [mu_s(a_s(m)) - mu_s(a_s(m_*))] <= m_* T_s(a_s(m_*)) |a_s(m) - a_s(m_*)| = O(|m - m_*| L_s) = o(sigma).
With b_+(m_*) = p_n n and b_-(m_*) = (1 - p_n) n, Gnedenko's theorem for each sign gives, with
tau = m - m_*,
 u+_m(k) u-_m(j) = (a_+ a_-)^-1 [g((x - tau mu_+)/a_+) g((-x - tau mu_-)/a_-) + o(1)]
uniformly. There are O(W rho) terms, so the errors add up to o(rho/sigma^2) = o(1/(sigma V)),
and the sum is a Riemann sum (mesh 1 in tau, scale rho) for
 (a_+ a_-)^-1 Int g((x - tau mu_+)/a_+) g((-x - tau mu_-)/a_-) d tau.
The change of variables v = -p(x + tau mu_-) shows that this integral over all tau equals V^-1
times the density of (1-p) a_+ Z - p a_- Z' at x, by p/(1-p) = mu_+/mu_- and mu_-/(1-p) = V.
That density is h_n(x/sigma)/sigma. The part |tau| > W rho of the integral is O(1/(sigma V W)),
because for large |tau| both arguments are large, and g(z) <= C/(1+z^2) on the right while it
decays faster than any power on the left.

(I) m <= delta m_*. Then b_+(m) <= (m/m_*) b_+(m_*) <= delta p n <= k/2, since mu(a_.) is
nondecreasing, and similarly for the minus sign. Berger's Theorem 2.3 gives
u+_m(k) <= C (m/a_+(m)) L_+(n)/n = C L_+(n) / (n L_+(a_+(m))), and the same for the minus sign.
The function m -> 1/(L_+(a_+(m)) L_-(a_-(m))) is slowly varying in m, so by Karamata the sum is
at most C delta m_* L_+(n) L_-(n) / (n^2 L_+(a_+(delta m_*)) L_-(a_-(delta m_*))). Since
m_* V = n and n/a_s(delta m_*) is of order V/(delta L), Potter's bounds make the ratio of this to
1/(sigma V) at most C delta^{1-2 eps} (L/V)^{1 - 2 eps} -> 0.

(II) delta m_* < m < m_* - W rho. Since mu(a_.) is nondecreasing,
p_n n - b_+(m) >= (m_* - m) mu_+(a_+(m_*)), so k - b_+(m) >= (m_* - m) mu_+/2 once W >= W_0(K),
and the same holds for j - b_-(m). With r = (m_* - m)/rho >= W, both deviations are at least
c r sigma. Theorem 2.3 and Potter give u_s(.) <= C r^eps / (r sigma) for each factor, and the sum
is at most (C rho / sigma^2) Int_W^inf r^{2 eps - 2} dr = C W^{2 eps - 1}/(sigma V).

(III) m > m_* + W rho. Now b_+(m) - k >= (m - m_*) mu_+/2. For m <= 2 m_*, Lemma 1 for the plus
factor and (i) for the minus factor bound the sum by (C rho/sigma^2) Int_W^inf e^{-c r} dr.
For m > 2 m_* we have s(m) >= 2n, so j <= b_-(m)/2 + K sigma, and Lemma 1 gives
u-_m(j) <= (C/sigma) exp(-c Lambda_n) with Lambda_n = inf_{x >= a_-(2 m_*)} mu_-(x)/L_-(x) -> infinity.
Hence the sum over m > 2 m_* is at most (C/sigma) e^{-c Lambda_n} sum_m u+_m(k)
<= (C/sigma) e^{-c Lambda_n} u_+(k) <= C e^{-c Lambda_n}/(sigma mu_+(k)) = o(1/(sigma V)). This uses
the renewal bound u_+(k) <= C/mu_+(k) (Erickson, or the elementary renewal theorem if the mean is
finite).

Let n -> infinity, then W -> infinity, then delta -> 0. This proves the claim for A. For B the
same four ranges apply to sum_m u+_m(k) u-_{m-1}(j). The index shift moves b_-(.) by
mu_-(a_-) = o(sigma), and in (I) the term m = 1 has u-_0(j) = 0 for j >= 1. QED.

### 3.2 Proof of Theorem A

Split on the run in progress at step N (G, eq. (run-sum); F, Section 2). With j = N - k,
 P_N(k) = sum_{y=1}^{k} T_+(y) A(k - y, j) + sum_{y=1}^{j} T_-(y) B(k, j - y).
Fix K and W, let lambda = (V/L)^{1/4} -> infinity, and put D_0 = sigma/lambda = o(sigma).

Near range, y <= D_0. The points (k - y, j) and (k, j - y) lie in the window of Lemma 2 at total
n = N - y. Passing from (N, p_N, sigma_N, h_N) to (n, p_n, sigma_n, h_n) changes the argument by
o(1), since p_n - p_N = O((y/N) L/V). So A(k - y, j) = [h_N(x/sigma) + o(1)]/(sigma V) with
x = k - p_N N, by the uniform continuity of the compact family {h_N}. The weights add up to
m_+(D_0) = sum_{y <= D_0} T_+(y), and m_+(a_+) - m_+(D_0) <= C L(a_+) lambda^eps log lambda = o(V)
by Potter, while m_+(a_+) - mu_+(a_+) = O(L) = o(V). So the near range of the first sum equals
[h_N(x/sigma) + o(1)] mu_+(a_+)/(sigma V) + o(1/sigma), and the near range of the second sum gives
the same with mu_-(a_-).

Middle range, D_0 < y <= W sigma. Lemma 2 bounds A and B by C/(sigma V) there, and
m_s(W sigma) - m_s(D_0) = o(V) as above, so this range contributes o(1/sigma).

Far range, y > W sigma. T_+ is nonincreasing and sum_{k'} A(k', j) = u_-(j), so the first sum
contributes at most T_+(W sigma) u_-(j) <= (C L/(W sigma)) / mu_-(j) = o(1/sigma), since j >= cN
and L/mu -> 0. In the second sum, sum_{j'} B(k, j') = sum_{m>=1} u+_m(k) <= u_+(k), and the bound
is T_-(W sigma) u_+(k) = o(1/sigma).

Adding up, sigma P_N(k) = h_N(x/sigma)(mu_+(a_+) + mu_-(a_-))/V + o(1) = h_N(x/sigma) + o(1).
The fresh minus start is the mirror image, with the same limit h_N, and the fair start is the
average. QED.

Hypotheses used: (RV1), (SPAN) (for Gnedenko's theorem) and (CMP) (only to keep a_+, a_- and
mu_+, mu_- comparable in the range estimates). Inputs: Gnedenko's local limit theorem, Berger's
Theorem 2.3, the bound u <= C/mu (Erickson), and Potter's bounds, Karamata's theorem and the
uniform convergence theorem. No local condition on f and no strong renewal hypothesis is needed.

What is not proved. (a) The uniform version over all k in {0, ..., N}, the form of F's Theorem
bulk. It needs the off-ray bound A(k', j) <= C/(V (sigma + d)) at distance d from the ray. This
should follow from the same four ranges (one factor typical, the other deviating), but it is not
written out. Named missing lemma M1. (b) An arbitrary initial run. The first-run decomposition
gives the window statement whenever the initial run is tight on the scale sigma_N. The sharp
criterion (F's bulk criterion B_n nu(n) -> 0) is expected to carry over with B_n = sigma_n.

## 4. The ends: atom and boundary layer

For a fresh plus start, P_N(N) = T_+(N) (the first run covers everything), as for every alpha.

**Proposition C (boundary layer).** Assume only that T_+ is regularly varying with index -1
(the minus law is arbitrary). For a fresh plus start and every fixed j >= 0,
 P_N(N - j) / T_+(N) -> u_-(j).

Proof. Use the final-run identity (G, Prop. final-run):
P_N(N-j) = sum_{r <= j} u-_r(j) E[T_+(N - j - S+_r); S+_r <= N - j - 1]
         + sum_{m=1}^{j} T_-(m) sum_{r <= j-m} u-_r(j-m) u+_{r+1}(N - j).
Here r is bounded. (a) E[T_+(N - j - S+_r); S+_r < N - j]/T_+(N) -> 1. On {S+_r <= delta N} the ratio
lies in [1 + o(1), (1 - 2 delta)^-1 (1 + o(1))], since S+_r < infinity a.s. and T_+ is regularly
varying. On {delta N < S+_r < N - j}, write the expectation as
sum_t f_+(t) P(max(delta N, N - j - t) <= S+_r < N - j). For t <= delta N the probability is at
most P((1-2 delta)N <= S+_r < N) = r T_+(N)[(1 - 2 delta)^-1 - 1] + o(T_+(N)) (the subexponential
tail P(S_r >= x) ~ r T(x) for fixed r), which is O(delta) T_+(N). For t > delta N the sum is at
most T_+(delta N) P(S+_r > delta N) = O(T_+(N)^2). (b) u+_{r+1}(N-j) = o(T_+(N)) for fixed r:
P(S_{r+1} = n) = P(S_{r+1} >= n) - P(S_{r+1} >= n+1) = (r+1)[T(n) - T(n+1)] + o(T(n)), and
T(n+1)/T(n) -> 1. Let delta -> 0. QED.

So the layer is T_+(N) u_-(j), the same formula as in F and G. What changes at alpha = 1 is the
size of u_-: by Erickson, u_-(j) ~ 1/mu_-(j) -> 0 when E X_- = infinity, slowly (like 1/log j
for Q1). In F, u_- -> 1/E X_- > 0. In G, u_-(j) ~ (sin pi alpha/pi)/(j T_-(j)) -> 0 like a power.
For log-convex f_- the layer is decreasing in j (de Bruijn-Erdos, as in F). Numerically (Q1,
N = 8000), P_N(N - j)/(T_+(N) u_-(j)) = 1.0025, 1.0081, 1.0137 at j = 1, 5, 10, and the error
halves when N doubles (about const j/N).

## 5. The big-jump zone, the infinite density at alpha = 1, and the antimode

Heuristic kernel (the alpha = 1 member of F's Theorem bigjump). Let (CMP) hold, let both means be
infinite, and assume the local form (LR1) f_+(n) ~ T_+(n)/n. Put j = N - k, and let kbar(j) be
the typical number of plus steps accompanying j minus steps (kbar(j) = j mu_+/mu_- at the scale
of j). For L_k = k - kbar(j) >> sigma_N,
 P_N(k) ~ T_+(L_k) u_-(j) + f_+(L_k) [U_-(j) + mu_+(L_k) V_-(j)],
with U_-(j) = sum_{i<j} u_-(i) and V_-(j) = sum_m m u-_m(j). The first term is the giant run in
progress at step N. The second is a complete giant run, with the final run a minus run (U_-) or
an ordinary plus run (mu_+(L_k) V_-). Since U_-(j) ~ j/mu_-(j) and V_-(j) ~ j/mu_-(j)^2, on the
ballistic scale k - p_N N = (1 - p_N) l N with l fixed in (0, 1) this reduces to
 N mu_-(N) P_N(k) / L_+(N) -> l^-2.
This is the alpha = 1 member of F's infinite density (1/mu_-)[alpha(1-l) l^{-alpha-1} + l^{-alpha}] T_+(N),
now with 1/mu_-(N) -> 0. The same expression is the tail of the bulk: the right tail of W_N has
density (1 - p) a_+ / x^2, and at x = (1-p) L this equals N L_+/(mu_- L^2), because
m_N/(1 - p_N) = N/mu_-. So when the plus scale is not the smaller one (here, under (CMP)), one
formula covers the plus side from K sigma_N to the end layer: the Cauchy tail continues into the
infinite density, and as l -> 1 it joins the end layer through u_-(j) ~ 1/mu_-(j).

Status: leading order only. A proof would follow F's proof of Theorem bigjump. The inputs would be
Berger's Theorem 2.4, (2.10), uniform over m in [delta m_*, m_*/delta] (named missing lemma M2;
Berger states it for one sequence with x_n/a_n -> infinity), its analogue for B, and Lemma 2. At
alpha = 1 the second-order terms are only logarithmically smaller, and they depend on choices
that agree to first order (mu at L or at N, mu or the de Haan m). Numerically, at l = 0.6 the
kernel with exact u, U, V is off by 13% (stable in N), and the bare form l^-2 by 29 to 33%
(decreasing very slowly). See Section 8.

Window. When one scale is smaller (possible without (CMP)), the bulk side of the smaller scale
has the left tail of a spectrally positive 1-stable law, which decays doubly exponentially,
P(Z < -y) = exp(-e^{pi y/2 + O(1)}). Equating it with the big-jump density gives a crossover at
k - p_N N ~ (2/pi) s_- log log(s_-/s_+) (s_+ = (1-p) a_+, s_- = p a_-), a log log multiple of the
larger scale. F's window sits at the multiple (log(B/b_+))^{(alpha-1)/alpha} (Cramer transform of
the minus runs), whose exponent tends to 0 as alpha -> 1, consistent with log log. This is a
remark, not checked numerically.

Antimode (fresh plus, (CMP), f_- log-convex). Between the decreasing layer T_+(N) u_-(j) and the
increasing big-jump zone, P_N has an interior minimum at N - j*. Differentiating the kernel with
u_-'(j) ~ -T_-(j)/mu_-(j)^2 gives T_-(j*) ~ 2(mu_+ + mu_-)/N, so j* is of the order of the stable
scale a_-(N/V) of the minus runs, as in F (T_-(j*) ~ 2 alpha_+ s/N, s the sum of the means). At
accessible N the constant is far off when mu is evaluated at j*: the observed j* is about half of
N/(4 mu(j*)) for Q1, because mu(N)/mu(j*) is about 1.9 there and u mu is about 0.8. With mu at N,
T_-(j*) N/(4 mu(N)) = 1.20, 1.18, 1.13, 1.11 at N = 1000, 2000, 4000, 8000 (Q1), and the argmin of
the kernel is within 15% of j*. The difference law u(j) - u(j-1) ~ -T(j)/mu(j)^2 at alpha = 1 is
not proved here (F proves its analogue for alpha > 1). Named missing lemma M3.

## 6. Mixed indices: one side at 1

(i) One side at 1, the other in (1, 2) (say T_+ of index 1, T_- of index alpha_- in (1, 2)). The
minus mean is finite. The proof of Theorem A goes through with Z' of index alpha_-, Gnedenko's
theorem for the minus sign, Berger's Theorem 2.3 (Caravenna-Doney's Theorem 1.1 for alpha in
(1, 2)) and the renewal theorem. The bookkeeping for unequal scales is that of F's bulk theorem
and is not done here. Now s_+ = (1-p) a_+ is of order m L_+ mu_-/mu_+, while s_- = p a_- is of
order m^{1/alpha_-}, so s_+/s_- -> infinity: the Cauchy side dominates, beta_N -> 1, and the local
law is a totally skewed 1-stable law, with the heavy tail toward excess plus steps. If
E X_+ = infinity, then p_N -> 1 and N - A_N ~ N mu_-/mu_+(N) = o(N): the minus time is still
relatively stable but sublinear. Numerically (Q1 plus, T_- = n^-1.5, fresh plus), beta_N rises
from +0.41 to +0.56 for N = 1000 to 8000, the ratio of the right to the left tail at 3 sigma rises
from 4.5 to 6.6, and the error against h_N decreases (Section 8). The window of Section 5 sits on
the minus side here, at a log log multiple of s_+. Status: expected, not proved.

(ii) One side at 1, the other in (0, 1) (T_+ of index 1, T_- of index alpha_- in (0, 1)). Now A_N
is not relatively stable in N. Put D_N = mu_+(a_+(1/T_-(N))) / T_-(N), so D_N/N -> 0.

**Theorem D (global).** A_N / D_N -> Y = Z_-^{-alpha_-} in distribution, where Z_- is the positive
alpha_--stable variable with E exp(-lambda Z_-) = exp(-Gamma(1-alpha_-) lambda^{alpha_-}). For
alpha_- = 1/2 the density of Y is exp(-pi y^2/4) on (0, inf) (half-normal, mean 2/pi).

Proof sketch. The plus time is o(N) in probability: it is of order D_N, and N T_-(N) is
regularly varying of positive index while mu_+ is slowly varying. So the number R_N of minus
runs begun by step N satisfies T_-(N) R_N -> Y, by the classical limit for renewal counts
(Dynkin, Lamperti): P(R_N >= m) = P(S-_m <= N(1 + o(1))) with m = y/T_-(N) and
a_-(m) ~ N y^{1/alpha}. Given R_N = M, A_N is the sum of M (or M +- 1) plus runs, and
S+_M/(M mu_+(a_+(M))) -> 1 in probability (relative stability at alpha = 1, since
a_+(M)/b_+(M) ~ L/mu -> 0), uniformly for M T_-(N) in compacts, with
mu_+(a_+(M)) ~ mu_+(a_+(1/T_-(N))) there (uniform convergence theorem in m). The run in progress at
step N is a plus run with probability O(D_N/N) -> 0. The plus runs are independent of the minus
runs, and R_N depends on the plus runs only through the o(N) plus time. QED (sketch).

The normalization must use mu_+ at the plus scale a_+(1/T_-(N)), not at N. For Q1 and
T_- = n^-1/2, D_N = sqrt(N) mu_+(sqrt N), about sqrt(N)(log sqrt(N) - 0.42), and mu_+(N) would be
off by a factor near 2. For wild L_+ even mu_+(1/T_-(N)) is not equivalent to mu_+(a_+(1/T_-(N))).

**Conjecture D' (local).** Under (SPAN), and (SRT_-) when alpha_- <= 1/2,
sup_{y in [y_1, y_2]} |D_N P_N(floor(y D_N)) - phi_Y(y)| -> 0 for 0 < y_1 < y_2, phi_Y the density
of Y. Mechanism: in the fresh-plus identity the term sum_m u+_m(k) q-_m(j) dominates. The sum
over m of u+_m(k) concentrates near m = k/mu_+ with total mass u_+(k) ~ 1/mu_+(k), and
q-_m(j) ~ T_-(N) Q_t(1) (G's covering kernel, t = m T_-(N)), where Q_t(1) is the density of Y. The
other term is smaller by a factor mu_+/(N T_-(N)) -> 0. Missing: the small-m range (G's key lemma
with the minus SRT) and the uniformity of the plus local limit theorem in m. The approach is very
slow numerically, since the relative plus fluctuation a_+(M)/(M mu_+) = 1/mu_+(M) is about 0.25
at N = 8000. The mixture predictor (half-normal count, exact 1-stable plus sum) cuts the error
by a factor 7 to 10 (Section 8), which supports the mechanism.

The mean is not a typical-value statistic here: E A_N ~ U_-(N) mu_+(N), with the plus runs
truncated at N rather than at their own scale. Numerically E[A_N]/D_N = 1.27 to 1.32, about 2 E Y,
which is why the mean part of prediction P8 failed.

This boundary (alpha_+ in (0, 1), alpha_- = 1) is case P6 of note 01, with the same scale
m_-(a_-(1/T_+))/T_+ written from the other side.

## 7. Where F's and G's pictures meet

Let eps_N = N T(N)/mu(N), the local index d log mu(x)/d log x at x = N, so that 1 - eps_N is the
effective index of the truncated mean. For pure power tails of index alpha:
- alpha < 1: eps_N -> 1 - alpha > 0. A_N/N has the Lamperti law (G), whose width is of order
  1 - alpha. No concentration.
- alpha = 1: eps_N -> 0 like L/mu (1/log N for Q1, 1/(log N log log N) for Q2). A_N concentrates
  at p_N N with Cauchy fluctuations of relative width (pi/2) sigma_N/N, which is of order eps_N
  (Theorem A).
- alpha > 1: eps_N is of order (alpha - 1)/(N^{alpha-1} - 1) -> 0 like a power. Stable bulk at
  relative scale N^{1/alpha - 1} (F).
At fixed N the three regimes merge when |alpha - 1| log N is of order 1, where eps_N is of order
1/log N in all three. So the change from G's picture to F's picture is not sharp at finite N: it
happens over a window of width about 1/log N around alpha = 1, and alpha = 1 itself is the case
where concentration holds, but only logarithmically.

The two limits match. As alpha -> 1 from below, with t = log((1-x)/x) and beta = log b, G's
density (eq. L-cosh) becomes
 Lambda(x) = (1/pi) [pi eps / ((t - beta/alpha)^2 + (pi eps)^2)] |dt/dx| (1 + O(eps)),  eps = 1 - alpha,
a Cauchy law in the log-odds t with width pi eps. Proof: sin(pi alpha) = pi eps + O(eps^3),
cosh(alpha t - beta) + cos(pi alpha) = [(alpha t - beta)^2 + pi^2 eps^2]/2 + (fourth order), and
1 + cosh t = 1/(2x(1-x)) = |dt/dx|/2. Near its center x_0 = 1/(1+b^{1/alpha}) this is a Cauchy law
in x with scale pi eps x_0(1 - x_0). At alpha = 1, Theorem A gives the scale (pi/2) sigma_N/N,
which is pi p(1-p)(L_+/mu_+ + L_-/mu_-)/2 to first order. So the two agree when eps is read as
the average of the local indices L_s/mu_s at the scale of the fluctuations. Numerically (Q1,
N = 8000) the Lamperti density with alpha_eff = 1 - L(a_N)/mu(a_N) has a width within 5% of the
exact one, and its maximal error (0.174 of the peak) is close to that of the Cauchy law (0.158).
With eps read at N instead of a_N the width is 33% too small. The approach from above is the
same statement for F's stable bulk: the alpha-stable density tends to the 1-stable one, with a
centering that diverges like 1/(alpha - 1) and is absorbed by p_N.

At the ends: the layer T_+(N) u_-(j) is common to all alpha. Its level u_-(infinity) is 1/E X_- > 0
for alpha > 1 and 0 for alpha <= 1, and it is approached like 1/mu_-(j) at alpha = 1 and like a
power for alpha < 1. The macroscopic big-jump zone carries mass of order eps_N: a negative power
of N for alpha > 1, 1/log N at alpha = 1, and order 1 for alpha < 1, where it merges with the
Lamperti density.

## 8. Exact computations: scoring the predictions

Engine: `03_alpha_one_engine.py`. Method 1 extracts the coefficient of t^N from
G(tw, t) = [Tc_+(tw) + F_+(tw) Tc_-(t)]/[1 - F_+(tw) F_-(t)] on a radius-r circle (r^M = 1e-14,
M >= 4(N+1)), with w on the roots of unity. Method 2 is the direct run recursion. Method 3 sums
over sign strings. The laws are defined by their tails, so they are exact probability laws. Full
output: `03_alpha_one_output.txt` (run time 24 min, N up to 32000).

P1 (engine): transform vs sign strings (N <= 12) max difference 1.4e-14, transform vs direct
recursion (N = 300) 5.7e-16, total mass 1 to 2e-14, for four pairs of laws. **Pass.**

P2 (Q1 both, fair). gamma_N = pi m_N/2.

| N | m_N | gamma_N/N | R_N = pi gamma_N P_N(N/2) | HWHM/gamma_N | shape err, fitted scale | err vs Cauchy | err vs semi-asymptotic |
|---|---|---|---|---|---|---|---|
| 1000 | 115.3 | 0.181 | 1.290 | 1.019 | 0.102 | 0.290 | 0.174 |
| 2000 | 204.0 | 0.160 | 1.244 | 1.036 | 0.037 | 0.244 | 0.158 |
| 4000 | 365.0 | 0.143 | 1.210 | 1.046 | 0.029 | 0.211 | 0.155 |
| 8000 | 659.0 | 0.129 | 1.184 | 1.052 | 0.027 | 0.187 | 0.149 |
| 16000 | 1199.8 | 0.118 | 1.164 | 1.054 | | | |
| 32000 | 2199.7 | 0.108 | 1.148 | 1.055 | | | |

(a) |R_N - 1| decreases, but it is 0.18 at N = 8000: **fail** on the tolerance 0.15. (R_N - 1) log N
falls slowly (2.00, 1.85, 1.74, 1.65, 1.59, 1.54), consistent with R_N -> 1 at a rate slower
than 1/log N. (b) HWHM/gamma within 0.06 of 1 and flattening at N = 32000: **pass**. (c) With the
fitted scale the profile is Cauchy to 0.03: **pass**. So the shape is Cauchy early, while the
peak height (equivalently the scale) converges logarithmically. The excess peak comes from mass
conservation: the Cauchy law puts mass of order gamma_N/N outside {0, ..., N}, which is about
0.16 here.

P3 (Q2 both, fair): R_N = 1.192, 1.140, 1.106, 1.082; gamma_N/N = 0.070, 0.059, 0.050, 0.044;
fitted-shape error 0.04; semi-asymptotic error 0.076 to 0.043. **Pass.** HWHM/gamma rises
(1.03 to 1.10): at these N the slowly varying L = log 2/log n still changes by 1/log a, about
15%, across the fluctuation scale, a second-order effect that Theorem A does not see. Not a
contradiction, but not a confirmation of the scale constant either.

P4 (Q1 plus, Q3 minus, fresh plus): p_N = 0.351, 0.349, 0.347, 0.346 (-> 1/3 slowly);
beta_N = -0.036, -0.033, -0.030, -0.027 (**pass**, |beta| < 0.1). The error against h_N is 0.40,
0.34, 0.30, 0.27, and against the semi-asymptotic predictor 0.20, 0.19, 0.18, 0.17: **fail** on
the tolerance 0.1, decreasing.

P5 (end layer, Q1, fresh plus): P_N(N-j)/(T_+(N) u_-(j)) at N = 8000 is 1.0025, 1.0041, 1.0081,
1.0137 for j = 1, 2, 5, 10. **Pass for j <= 5, fail for j = 10** (1.4% against 1%). At N = 32000
it is 1.0007, 1.0023, 1.0038 for j = 1, 5, 10. The error halves when N doubles.

P6 (big-jump kernel, Q1, fresh plus), P_N/K_N:

| N | l=0.1 | 0.2 | 0.4 | 0.6 | 0.8 | 0.95 | bare l^-2 form at 0.4, 0.6, 0.8 |
|---|---|---|---|---|---|---|---|
| 1000 | 0.148 | 0.460 | 0.980 | 1.129 | 1.101 | 1.040 | 1.08, 1.33, 1.40 |
| 8000 | 0.230 | 0.643 | 1.087 | 1.130 | 1.079 | 1.028 | 1.19, 1.29, 1.31 |

**Pass on l in [0.4, 0.95], fail at l = 0.2.** The prediction was badly posed: at N = 8000,
l = 0.2 is k - N/2 = 0.1 N, which is less than gamma_N = 0.13 N, so that point is still in the
bulk. The zone starts at l >> 2 gamma_N/N.

P7 (antimode, Q1, fresh plus): j* = 32, 59, 112, 210 against N/(4 mu(j*)) = 66, 115, 204, 365:
**fail** (factor 0.5 to 0.6, ratio rising). T(j*) N/(4 mu(N)) = 1.20, 1.18, 1.13, 1.11, and the
argmin of the exact-renewal kernel is 37, 68, 128, 239 (ratio 0.87 to 0.88). The prediction used
mu at j*. The asymptotic law is the same with mu at N, but the two choices differ by a factor of
almost 2 at these N.

P8 (Q1 plus, T_- = n^-1/2, fair): D_N = 96.7, 151.8, 236.8, 365.2. E[A_N]/D_N = 1.27 to 1.32:
**fail** (the mean picks up the plus runs truncated at N; Section 6). The maximal error of
D_N P_N against exp(-pi y^2/4) on [0.2, 1.5] is 0.30, 0.29, 0.28, 0.27 (**fail**), and 0.21 to
0.18 with mu_+ read at D_N. The mixture predictor (half-normal count times the exact 1-stable
law of M plus runs centered at M mu_+(M)) has error 0.040, 0.031, 0.024, 0.018. So the mechanism
is confirmed, and the limit law is reached only through the logarithmically slow concentration
of the plus sums.

P9 (Q1 plus, T_- = n^-1.5, fresh plus): beta_N = +0.41, +0.46, +0.51, +0.56; ratio of the right
to the left tail at 3 sigma = 4.5, 5.0, 5.7, 6.6 (**pass**, right-skewed and growing). The error
against h_N is 0.37, 0.32, 0.29, 0.26, and against the semi-asymptotic predictor 0.22, 0.19, 0.17,
0.15: **fail** on 0.1, decreasing.

P10 (bridge): at N = 8000 (Q1), the Lamperti law with alpha_eff = 1 - L(a_N)/mu(a_N) = 0.835 has
width ratio 0.951 and max error 0.174 of the peak; the Cauchy law has 0.158. With
alpha_eff = 1 - N T(N)/mu(N) = 0.883 the width ratio is 0.674. **Pass.**

Also checked: the closed forms of the Levy exponents psi_1 and psi_{3/2} against quadrature (to
2e-8), and Erickson's u(j) mu(j) -> 1 (Section 2).

Summary of the scoring. The structural predictions passed: the engine, Cauchy shape, symmetry
(beta -> 0) under (CMP), skewness in the mixed case, end layer for small j, kernel on the
ballistic range, and the bridge to Lamperti. Every quantitative tolerance of 10 to 15% on a limit
constant failed at N <= 8000 (P2a, P4, P8, P9), as did P7, whose constant used the wrong scale.
All errors decrease monotonically in N, roughly like a constant over log N. The semi-asymptotic
predictor (Lemma 2's limit for A inserted into the exact run-sum identity) removes between a
third and two thirds of the error. This locates the main correction in the logarithmic weight
sum_{y <= sigma} T(y) of the run in progress, and supports the structure of the proof of
Theorem A.

## 9. Status and recommendation

| Statement | Status |
|---|---|
| Theorem A (local law in the window, (CMP)) | Proved here, given Gnedenko, Berger Thm 2.3 and Erickson's bound u <= C/mu (Erickson read only through Berger (3.6)). Lemmas 1 and 2 proved. |
| Corollary A1 (A_N/N - p_N -> 0, no nondegenerate limit, 1-stable fluctuations) | Follows from A. |
| Corollary A2 (symmetric Cauchy law when L_+/L_- -> c, infinite means) | Follows from A. |
| Uniform version over all k | Missing lemma M1 (off-ray bound for A). |
| Proposition C (end layer T_+(N) u_-(j)) | Proved, needs only RV of T_+. |
| Big-jump kernel, infinite density l^-2 T_+(N)/mu_-(N) | Leading order derived. Missing lemma M2 (Berger (2.10) uniform in m). Numerics: 13% with exact renewal terms; the bare form converges very slowly. |
| Antimode, T_-(j*) ~ 2(mu_+ + mu_-)/N | Heuristic, needs the difference renewal theorem at alpha = 1 (M3). Numerics consistent with mu read at N. |
| Mixed (1, (1,2)): skewed 1-stable bulk | Expected from the proof of A with F's bookkeeping for unequal scales. Not written out. |
| Mixed (1, (0,1)): Theorem D (A_N/D_N -> Z^{-alpha_-}) | Proof sketch, complete in outline. |
| Mixed (1, (0,1)): local version D' | Conjecture with mechanism. The mechanism is confirmed numerically, the limit is not reached at accessible N. |
| Bridge (eps_N = N T(N)/mu(N); Lamperti -> Cauchy in log-odds) | Exact expansion; numerics consistent. |
| Window at a log log multiple of the larger scale | Heuristic remark. |

Recommendation for the merged paper. Include Theorem A with Corollaries A1 and A2 as a short
section on the boundary alpha = 1: the statement plus about one page of proof, with Lemma 2 in the
appendix. Reasons: it closes the range (0, 2) with a statement of the same form as F's bulk
theorem; it reuses the run-sum identity and needs only one new lemma; its inputs are exactly
Berger's Cauchy-domain result (Theorem 2.3) and Erickson's theorem, which can be cited cleanly;
and the meeting of F's and G's pictures (Section 7) gives the paper one phase diagram in which the
boundary is explained rather than left out. Proposition C costs one sentence, since F's proof
applies verbatim. Put the big-jump kernel, the antimode, the log log window and the mixed cases
into one remark with the numbers, labelled as heuristics. Do not put alpha = 1 into the atlas
figure: at N <= 10^4 the Cauchy law is visibly off (about 18% at the peak for Q1), and a reader
would take the logarithmic convergence for an error. If space is tight, keep only Theorem A and
Corollary A2, as a remark with a proof sketch. The weakest point is the Erickson citation, which
someone should check in the original before submission.

Novelty: this note did not search for prior local limit theorems of the occupation time at
alpha = 1. Lamperti's 1958 theorem covers the degenerate global limit. The local statement, the
scale sigma_N and the symmetric Cauchy law under (CMP) do not appear in the two sources read
(Berger, Caravenna-Doney), but this is not a novelty claim.
