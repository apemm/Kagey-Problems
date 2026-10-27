# 02. The local aging law

Research note for the merged paper (F + G). Scripts: `02_aging_exact.py` (exact law of the aged
count, brute-force check, all comparisons), output in `02_aging_output.txt`.

## 0. Predictions (written before any computation)

Zeta laws f(n) = n^(-a-1)/zeta(a+1) for both signs (so b = 1, p = 1/2), fresh plus start at time 0,
observation window = steps t_a+1, ..., t_a+N with t_a = round(theta N). A_N = plus steps in the window.

Infinite mean (0 < alpha < 1). L_theta is the mixture density of Section 2 (with the Dynkin-Lamperti
density of the residual), Q^inf_+(theta) = (1/2)(sin pi a/pi) B(theta/(1+theta); a, 1-a) the atom,
c_+(theta) = int_0^1 rho_+(z)(1-z)^(-a) dz the layer constant.
- P1. N P_N(floor(xN)) -> L_theta(x) on x in [0.1, 0.9], theta in {0.5, 1, 2}. At alpha = 0.5 the max
  relative error is below 5% at N = 2000 and decreasing in N. At alpha = 0.7 below 15%, decreasing.
- P2. P_N(N) -> Q^inf_+(theta) (an atom of order one, against T_+(N) for a fresh start). Relative
  error below 5% at N = 2000, alpha = 0.5.
- P3. P_N(N-j)/(T_+(N) u_-(j)) -> c_+(theta) for j = 1..5; within 10% at N = 2000, alpha = 0.5.
- P4. Mass identity int_0^1 L_theta + Q^inf_+ + Q^inf_- = 1 (exact; numerically to 1e-6).

Finite mean (1 < alpha < 2), alpha = 1.5, theta in {0.5, 1, 2}.
- P5. Bulk unchanged: B_N P_N(k) for the aged start and the fresh start agree to within 2% on
  |k - N/2| <= B_N at N = 2000 (B_N = a(N/s)).
- P6. Big-jump zone, k = pN + (1-p) lambda N, lambda in {0.3, 0.5, 0.7}: P_N(k)/Pred_N(k) -> 1 with
  Pred_N(k) = ((N-L_k)/mu_-) f_+(L_k) + T_+(L_k) kappa^(N)_+(N-k) + nu^(N)_+(L_k)(1 + mu_+ u_-(N-k)),
  within 10% at N = 2000 and moving toward 1. The aging term is not small: it is the fraction
  [l^-a - (l+theta)^-a] / [a(1-l) l^(-a-1) + 2 l^-a - (l+theta)^-a] of the kernel (0.22 at l = 0.5, theta = 1).
- P7. Atom: P_N(N) / [N T_+(N) (1 - (1+theta)^(1-a)) / (s(a-1))] -> 1, within 10% at N = 2000.
- P8. Layer: P_N(N-j)/T_+(N) -> p u_-(j) + 1/s + (1/s)(1 - (1+theta)^(-a))(1 + mu_+ u_-(j)), j = 1..5,
  within 10% at N = 2000.
- P9. The exact recursion agrees with brute force over all run sequences for t_a + N <= 14 to 1e-14.

(Sections 1 onward are written after the computations; the predictions above are not edited.)

---

## 1. Summary

Setting. Alternating runs, fresh start (either sign) at time 0, observation window = steps
t_a+1, ..., t_a+N with t_a/N -> theta in (0, inf). A_N = plus steps in the window, P_N(k) = P(A_N = k).
The initial run of the window is the run that straddles step t_a+1, cut at t_a. Notation as in Paper F
(sec_setting.tex) and Paper G (sec_setting.tex): T, f, u, u^s_m, q^s_m, F^s_n, Pi^s_m, L = L_{alpha,b},
omega_s(n) = min(1, 1/(n T_s(n))) with omega(0) = 1, s_+ = 1/(1+b), s_- = b/(1+b). I write a for alpha in
displayed formulas.

| Item | Status |
|---|---|
| Literature: the global (distributional) aging law for 0 < alpha < 1 is Akimoto-Sera-Yamato-Yano, Thm 2 (arXiv 2004.00808). Its density is the mixture L_theta below. Nothing local; nothing for 1 < alpha < 2 beyond the stationary start | Checked (Section 2) |
| Lemma 2: the initial run of the aged window has the marked Dynkin-Lamperti law (sign independent of length in the limit, plus share s_+), RV only | Proved |
| **Theorem A: G's Conjecture `rem:aging` (initial runs of length of order N) holds under (RV), (SPAN), (SRT_pm), without (LB).** The near-diagonal bound is closed by a counting identity (Lemma 4), not by the end-layer theorem | Proved (4.2) |
| Lemma E: end-layer upper bound F^-_n(i) <= C T(n) omega_+(i), i <= n/2, under SRT alone (alpha != 1/2) | Proved (4.3) |
| **Theorem B: local aging law, 0 < alpha < 1: N P_N(floor(xN)) -> L_{a,b,theta}(x) uniformly on compacts.** (i) under (LB_pm), every alpha; (ii) for 1/2 < alpha < 1 under (RV), (SPAN) alone; (iii) for alpha < 1/2 under (SRT_pm) and the cycle bound (U) | (i) proved; (ii), (iii) proved here, by a longer argument that needs a second look |
| Theorem B': ends, 0 < alpha < 1: atom P_N(N) -> Q^inf_+(theta), of order one; layer P_N(N-j) = T_+(N)[c_+(theta) u_-(j) + o(1)] for fixed j >= 1 | (a) proved, RV only; (b) proved under (U) |
| Closed forms: Q^inf_pm = s_pm (sin pi a/pi) B(theta/(1+theta); a, 1-a); c_pm = s_pm (sin pi a/pi) theta^(a-1) B(1-a,1-a) 2F1(1, 1-a; 2-2a; -1/theta) | Proved; checked numerically |
| Non-commuting limits: theta -> 0 gives the fresh bulk L, but the layer constant c_+ -> s_+, not 1 | Proved (ASYY's c(r) -> 1/2 for Brownian motion is the case b = 1) |
| **Theorem C (1 < alpha < 2)**: (a) the bulk stable law is unchanged, for every aging time; (b) atom ~ N T_+(N)(1 - (1+theta)^(1-a))/(s(a-1)); (c) the boundary kernel gains (1/s)(1 - (1+theta)^(-a))(1 + mu_+ u_-(j)); (d) the interior big-jump kernel gains [T_+(L_k) - T_+(L_k + t_a)]/mu_- | (a), (b), (c) proved; (d) proved in outline (triangular-array version of F Thm C(c)) |
| Golden ratio survives aging: the endpoint atom beats the bulk iff alpha < phi, for every theta > 0 | Corollary of C(a), C(b) and F Thm D |
| Numerics (exact recursion, brute force to 6e-16) | 6 of 9 predictions pass; the 3 failures are rate predictions, each explained by a diagnostic (Section 6) |

The answer in one paragraph. For 0 < alpha < 1, aging at time theta N replaces the initial run by a run of
length of order N with the marked Dynkin-Lamperti law. The local law becomes the explicit mixture L_theta
of rescaled Lamperti densities, with atoms of order one at both ends, and end layers with the fresh shape
u_-(j) but height multiplied by c_+(theta) < 1. For 1 < alpha < 2 the aged initial run is O(1) in
probability (it converges to the stationary residual), so the bulk does not change. What changes is
everything of order T(N). The run straddling t_a has the tail nu_+(d) ~ (1/s)[T_+(d) - T_+(d + t_a)] at scale N.
That tail adds one term to the big-jump kernel and one to the boundary kernel, and turns the endpoint atom
from T_+(N) into order N T_+(N). The aged law interpolates between the fresh start (theta -> 0) and Paper F's
stationary start (theta -> inf).

One correction to the brief. For 1 < alpha < 2 the initial run is not of length of order N in the typical
sense: P(D >= epsilon N) is of order N T(N) -> 0. It is of length of order N only on the probability scale
T(N) that governs the big-jump zone and the ends.

---

## 2. Literature (what is known, exactly)

- **Akimoto, Sera, Yamato, Yano, "Aging arcsine law in Brownian motion and its generalization"**,
  arXiv 2004.00808v1 (April 2020); Phys. Rev. E 2020 (volume and page not checked here). Read in full,
  main text and supplement.
  - Thm 1 (Brownian motion, rigorous): for t_a, t_m > 0 and r = t_a/t_m the law of T_+(t_m; t_a)/t_m is an
    explicit density phi(r; s) (Eq. 12) plus atoms q(r) = (1/pi) arccot(r^(-1/2)) at 0 and at 1.
  - Eq. (18) (renewal processes, stated without proof): the forward recurrence time at t_a, jointly with
    the sign, has limit density p_pm (sin pi a/pi) r^a/(tau^a (tau + r)) in units of t_m, p_pm = A_pm/(A_+ + A_-).
  - **Thm 2** (two-state renewal process with durations rho_pm(tau) ~ A_pm tau^(-1-a), 0 < a < 1, any initial
    condition): as t_m -> inf with t_a/t_m = r fixed,
    P(T_+(t_m; t_a)/t_m <= s) -> int_0^s phi_{a,b}(r; s') ds' + q^-_a(r) + 1[s >= 1] q^+_a(r), where phi_{a,b}(r; s) is
    exactly our L_theta (theta = r, b = A_-/A_+) and q^pm_a(r) = int_1^inf psi^pm_r. The proof in the supplement
    is a scaling argument (Eqs. B1-B5); the convergence of the occupation time to its scaling limit is
    asserted, not proved.
  - Remark after Eq. (15): near s -> 0 and s -> 1, phi(r; s) ~ c(r) phi(s), with c(r) -> 1/2 as r -> 0, so the
    limits do not commute. Our c_+(theta) is their c(r) in the Brownian case (c_+(1) = 1/(2 sqrt 2) at
    alpha = 1/2 from both formulas).
  - Not in the paper: anything local (point probabilities), lattice end layers, rates, the finite-mean
    case, a proof of Thm 2 at the level of a mathematics paper.
- **Akimoto, arXiv 2306.00359 (2023)**, Sections III-V read: aging alternating renewal process, triple
  Laplace transform of the aged occupation time (Eqs. 99-100), recurrence-time densities (Eq. 52),
  moments; credits the aging generalized arcsine law to ASYY (its ref. [59]). For 1 < alpha < 2 only the
  equilibrium start. Distributional.
- **Yamato, arXiv 2605.23659 (May 2026)**, introduction and Section 5 read: multiscale joint
  occupation-time limits for state-dependent inverse-subordinator time changes. Distributional, no aging
  window, nothing local.
- Earlier aging of renewal limits (Godreche-Luck 2001; Schulz-Barkai-Metzler PRL 2013, PRX 2014) are cited
  by ASYY; not read here.
- Searches (alphaXiv and web: aging, generalized arcsine, distributional aging, alternating renewal, local
  limit) found no local aging law and no aging result for 1 < alpha < 2 beyond equilibrium. A bounded
  search, not a proof of novelty.

So the global law for 0 < alpha < 1 is known, with a physics-level proof. New here: the local law, the end
layers and atoms, the closing of G's conjecture, and the finite-mean case.

---

## 3. The initial run of the aged window

**Lemma 1 (exact law).** Fresh plus start at time 0. Let u_c be the renewal mass function of the cycle
law f_c = f_+ * f_-, and v_- = f_+ * u_c. A plus run starts at step s+1 with probability u_c(s), a minus run
with probability v_-(s). The initial run of the window therefore has
  nu_+(d) = sum_{s=0}^{t_a} u_c(s) f_+(t_a - s + d),     nu_-(d) = sum_{s=0}^{t_a} v_-(s) f_-(t_a - s + d),
  Q_+(N) = sum_s u_c(s) T_+(t_a - s + N),               Q_-(N) = sum_s v_-(s) T_-(t_a - s + N),
and after it the walk is fresh and independent, so the first-run decomposition (F Prop. first-run) holds
with nu = nu^(N). (A run of length l starting at step s+1 straddles step t_a+1 iff s <= t_a and
l >= t_a - s + 1, and its residual is d = s + l - t_a.) For a fresh minus start exchange the roles. Checked
against brute force (P9).

**Lemma 2 (marked Dynkin-Lamperti law; (RV_alpha) only, 0 < alpha < 1).** If t_a/N -> theta in (0, inf), then for
every r > 0, P(Sigma = pm, D >= rN) -> int_r^inf rho_pm(z) dz, where
  rho_pm(z) = s_pm (sin pi a/pi) theta^a z^(-a)/(theta + z),
and P(Sigma = pm) -> s_pm and lim_{epsilon->0} lim_N P(D < epsilon N) = 0.

*Proof.* T_c(n) = P(X_+ + X_- >= n) ~ (1+b) T_+(n) (independent summands with RV tails of equal index). The
renewal measure U_c(n) = sum_{s<=n} u_c(s) satisfies U_c(n) T_c(n) -> sin(pi a)/(pi a) (Karamata's Tauberian
theorem; Feller II, XIV.3; BGT Sec. 8.6). So U_c(N dy)/U_c(N) -> d(y^a) vaguely, and
T_+(t_a - y + rN)/T_+(N) -> (theta - y + r)^(-a) uniformly in y in [0, theta] (UCT; the argument is >= rN). Hence
  P(+, D >= rN) = int_[0,t_a] T_+(t_a - y + rN) U_c(dy) -> (sin pi a/(pi (1+b))) int_0^theta (theta - y + r)^(-a) d(y^a).
Differentiating in r and using the identity
  (I)  int_0^theta y^(a-1)(theta + r - y)^(-a-1) dy = theta^a/(a r^a (theta + r))
(substitute v = y/(theta + r - y): the integrand becomes (theta + r)^(-1) v^(a-1) dv on [0, theta/r]) gives the
density rho_+. The minus sign is the same with v_-, whose renewal measure has the same asymptotics (a
proper delay). Summing the signs, P(D >= rN) -> int_r^inf (rho_+ + rho_-), the Dynkin-Lamperti tail of D/t_a,
which tends to 1 as r -> 0; hence P(Sigma = pm) -> s_pm and no mass escapes to 0. []

In the scaling limit the run boundaries are the range of a stable subordinator whose jumps are marked
plus with probability s_+ independently (Poisson thinning of the jumps of sigma_+ + sigma_-), so the sign
of the straddling run is asymptotically independent of its length. This is ASYY Eq. (18), here proved.
Identity (I) is checked numerically in the script.

**Hypothesis (U).** u_c(n) <= C omega_+(n) and v_-(n) <= C omega_+(n) for all n >= 1 (mirror for a fresh minus
start). It holds:
- under (LB_pm): LB is preserved by convolution (split at n/2), so Doney 1997 gives SRT for f_c; for v_-,
  sum_{i<=n/2} f_+(i) u_c(n-i) <= C omega(n) and sum_{i>n/2} f_+(i) u_c(n-i) <= (C T(n)/n) U_c(n/2) <= C/n;
- for 1/2 < alpha < 1 under (RV), (SPAN) alone: SRT for the aperiodic cycle law (Garsia-Lamperti, Erickson);
  for v_- the second part is f_+(n) + C sum_{1<=z<n/2} f_+(n-z) omega(z) <= C omega(n), since
  omega(z) <= 1/(z T(z)^2) and the Caravenna-Doney quantity I_1 is bounded (CD Thm 1.4, automatic for alpha > 1/2);
- for alpha <= 1/2 when f_c satisfies SRT and f_+ satisfies SRT (CD Thm 1.4 for the second part of v_-).
Whether (SRT_pm) alone implies SRT for f_c when alpha <= 1/2 I did not settle (M-U, Section 7).

**Lemma 3 (pointwise bounds).** Split nu_pm = nu^y_pm + nu^o_pm according to s > t_a/2 (young: the run started
after t_a/2) or s <= t_a/2 (old).
(a) Under (U): N nu^y_pm(d) <= C_{epsilon,theta} for all d >= epsilon N.
(b) Under (LB_pm), which gives (U): N nu_pm(d) <= C_{epsilon,theta} for all d >= epsilon N.

*Proof.* (a) u_c(s) <= C omega(t_a/2) <= C/(N T(N)) for s > t_a/2, and sum_s f_+(t_a - s + d) <= T_+(d) <= C T(N).
(b) For s <= t_a/2 the argument of f_+ is >= t_a/2 + d >= cN, so f_+ <= C T(N)/N by (LB), and
sum_{s<=t_a/2} u_c(s) = U_c(t_a/2) <= C/T(N). Same for nu_- (partial sums of v_- are <= U_c). []

Without (LB) the old part can exceed C/N pointwise: under (SRT) f(n) can be as large as o(1/(n T(n))) on a
sparse set, and the term s = 0 of nu^o_+ is f_+(t_a + d). That is why Theorem B(ii), (iii) handle the old part
by averaging (4.4) instead of by (H2).

---

## 4. Infinite mean, 0 < alpha < 1

For 0 < x < 1 put
  L_theta(x) = L_{a,b,theta}(x) = int_0^x rho_+(z) L((x-z)/(1-z)) dz/(1-z) + int_0^{1-x} rho_-(z) L(x/(1-z)) dz/(1-z),
  Q^inf_pm(theta) = int_1^inf rho_pm = s_pm (sin pi a/pi) B(theta/(1+theta); a, 1-a)   (incomplete beta, u = 1/(1+y)),
  c_pm(theta) = int_0^1 rho_pm(z)(1-z)^(-a) dz = s_pm (sin pi a/pi) theta^(a-1) B(1-a, 1-a) 2F1(1, 1-a; 2-2a; -1/theta)
(Euler's integral). L_theta is ASYY's phi_{a,b}(r; s) with r = theta. The first integral is a plus straddler of
length zN followed by a fresh minus walk of length (1-z)N; the second a minus straddler followed by a fresh
plus walk.

### 4.1 Lemma 4 (the counting bound)

For a fresh minus walk and integers n_0 >= 1, I >= 0, m_0 >= 1,
  sum_{i=0}^{I} F^-_{n_0+i}(i) <= C m_0 T_-(n_0) + exp(-m_0 T_+(I+1)) + u_-(n_0) sum_{n=1}^{I} T_+(n),
and the mirror sum_{i=0}^{I} F^+_{n_0+i}(n_0) <= C m_0 T_+(n_0) + exp(-m_0 T_-(I+1)) + u_+(n_0) sum_{n=1}^{I} T_-(n).

*Proof.* Let C_m be the number of minus steps among the first m and t_b the step of the b-th minus step.
F^-_{n_0+i}(i) = P(C_{n_0+i} = n_0), so by Tonelli the left side is E #{m in [n_0, n_0+I] : C_m = n_0}. The set
{m : C_m = n_0} is [t_{n_0}, t_{n_0+1}). It has length 1 unless step t_{n_0} ends the r-th minus run
(S^-_r = n_0), and then its length is 1 + X^+_r (proof of F Lemma green); X^+_r is independent of the event
{S^-_r = n_0} (proof of F Lemma green-conc). So the count is at most
1{t_{n_0} - n_0 <= I} + sum_r 1{S^-_r = n_0} min(X^+_r, I), whose expectation is at most
P(t_{n_0} - n_0 <= I) + u_-(n_0) E min(X_+, I). Next, t_{n_0} - n_0 = S^+_{J-1}, where J - 1 is the number of
complete minus runs before the n_0-th minus step, and {J - 1 < m_0} = {S^-_{m_0} >= n_0} has probability
<= C m_0 T_-(n_0) (G (A1)). On {J - 1 >= m_0}, S^+_{J-1} >= S^+_{m_0}, and P(S^+_{m_0} <= I) <= (1 - T_+(I+1))^{m_0}. []

**Corollary 4.1 (near-diagonal bound).** Assume (RV_alpha) and the upper half of (SRT_-). Let n_0 >= cN, I = delta N,
m_0 = ceil(eta/T_+(N)) with eta = delta^(a/4). Then for N >= N_0(delta, c),
  sum_{i<=delta N} F^-_{n_0+i}(i) <= zeta(delta) := C_c (delta^(a/4) + exp(-delta^(-a/4)) + delta^(1-a-epsilon')),
using T_-(n_0) <= C_c T_+(N), T_+(delta N)/T_+(N) >= delta^(-a/2), u_-(n_0) <= C/(N T(N)), and
sum_{n<=delta N} T(n) <= C delta N T(delta N) <= C delta^(1-a-epsilon') N T(N) (Karamata, Potter). zeta(delta) -> 0.

### 4.2 Theorem A (G's Conjecture `rem:aging`, without Doney's condition)

**Theorem A.** Assume (RV_alpha), (SPAN), (SRT_pm). Let the initial-run law nu^(N) satisfy
- (H0) pi^0 = lim_{epsilon->0} lim_N P(D^(N) < epsilon N) exists (both limits);
- (H1) for each sign, P(Sigma = pm, D^(N)/N in .) restricted to (0,1) converges vaguely to rho_pm(z) dz, with rho_pm
  continuous on (0,1);
- (H2) for each epsilon in (0, 1/2), sup_N sup_{epsilon N <= d <= (1-epsilon)N} N nu^(N)_pm(d) < inf.

Then, uniformly for x in compact subsets of (0,1),
  N P_N(floor(xN)) -> pi^0 L(x) + int_0^x rho_+(z) L((x-z)/(1-z)) dz/(1-z) + int_0^{1-x} rho_-(z) L(x/(1-z)) dz/(1-z).

G's hypotheses (N nu(floor(zN)) -> rho uniformly on compacts, sup_{d >= epsilon N} N nu < inf, pi^0 exists) imply
(H0)-(H2), and G also assumed (LB_pm). So the conjecture holds under (SRT_pm), which for alpha > 1/2 is
automatic.

*Proof.* Fix 0 < x_1 < x_2 < 1, k = k_N with k/N in [x_1, x_2], j = N - k, and 0 < delta < epsilon < x_1/4. Split the
plus part sum_{d<=k} nu_+(d) F^-_{N-d}(k-d) into three ranges.
1. d < epsilon N. The horizon is n = N - d >= (1-epsilon)N and (k-d)/n lies in a compact of (0,1). G Thm 1(ii)
   (uniform in k/n on compacts, for all large n) gives N F^-_{N-d}(k-d) = L(k/N) + O(epsilon) + o(1), by continuity
   of L. Contribution: P(+, D < epsilon N)(L(x) + O(epsilon) + o(1))/N.
2. epsilon N <= d <= k - delta N. Here (k-d)/(N-d) lies in [delta, (x_2 - epsilon)/(1 - epsilon)], so
   N F^-_{N-d}(k-d) = g_x(d/N) + o(1) with g_x(z) = L((x-z)/(1-z))/(1-z), and F^- <= C/N. By (H1), with an absolutely
   continuous limit (Portmanteau for the indicator of [epsilon, x - delta]), N * sum = int_epsilon^{x-delta} rho_+ g_x + o(1),
   uniformly in x since g_x is equicontinuous in x on this range.
3. k - delta N < d <= k. With i = k - d the terms are nu_+(k-i) F^-_{j+i}(i), i <= delta N, j >= (1-x_2)N. By (H2) and
   Corollary 4.1, N * sum <= C_epsilon zeta(delta).

The minus part sum_{d<=j} nu_-(d) F^+_{N-d}(k) is the same, with F^+_{N-d}(k) = F^+_{k+i'}(k), i' = j - d, and the
mirror of Corollary 4.1 (upper half of (SRT_+)). Let N -> inf, then delta -> 0 (g_x(z) ~ C (x-z)^(a-1) near z = x is
integrable, and rho_+ is bounded near x), then epsilon -> 0, using (H0) and the integrability of rho_pm near 0. []

What changed relative to G's outline. G bounded the remainder walk in its end layer pointwise by
C T(N) omega(k-d), which needs G Thm 2(b) and so (LB). Lemma 4 bounds the near-diagonal sum directly by a
Green-type count. That costs only the upper bound u_-(n_0) <= C omega_-(n_0) at n_0 of order N and the crude
estimates (A1), (A2).

### 4.3 Lemma E (end-layer upper bound under SRT)

**Lemma E.** Assume (RV_alpha), (SPAN), and one of: 1/2 < alpha < 1; alpha < 1/2 and (SRT_pm); alpha = 1/2, (SRT_pm), and
n T_+(n)^2 bounded above and away from 0. Then F^-_n(i) <= C T(n) omega_+(i) for all n >= 1 and 0 <= i <= n/2, and
the mirror F^+_n(n - i) <= C T(n) omega_-(i). (Under (LB_pm) this is G Thm 2(b), for every alpha.)

*Proof.* At i = 0, F^-_n(0) = T_-(n). For i >= 1 and j = n - i >= n/2 the fresh-minus identity gives two terms.
Term 1 = sum_m u^+_m(i) q^-_{m+1}(j) <= C T_-(j) u_+(i) <= C T(n) omega_+(i), by G (B2) and the upper half of (SRT_+)
(automatic for alpha > 1/2). Term 2 = sum_m u^-_m(j) q^+_m(i), and q^+_m(i) <= C T(i) e^{-c m T(i)} by G (B3).
- alpha > 1/2: u^-_m(j) <= C m T(j)/a_m for every m (CD (1.6), RV only). Since m/a_m is RV with index
  1 - 1/alpha > -1, sum_m (m/a_m) e^{-c m T(i)} <= C T(i)^(-2)/a_{1/T(i)} <= C/(i T(i)^2), so Term 2 <= C T(n)/(i T(i)).
- alpha < 1/2: Term 2 <= C T(i) sum_m u^-_m(j) = C T(i) u_-(j) <= C T(i)/(n T(n)) by (SRT_-), and
  T(i)/(n T(n)) <= C T(n)/(i T(i)) iff i T(i)^2 <= C n T(n)^2, true for i <= n because i T(i)^2 is RV with positive
  index 1 - 2 alpha (BGT Thm 1.5.3).
- alpha = 1/2: the second route, with i T(i)^2 bounded above and below. []

### 4.4 Theorem B (the local aging law in the bulk)

**Theorem B.** Fresh start of either sign (or a mixture of the two) at time 0, t_a/N -> theta in (0, inf),
0 < alpha < 1, (RV_alpha), (SPAN). Assume one of
- (i) (LB_pm);
- (ii) 1/2 < alpha < 1 (nothing more);
- (iii) alpha < 1/2, (SRT_pm) and (U); or alpha = 1/2, (SRT_pm), (U), and n T(n)^2 bounded above and below.

Then N P_N(floor(xN)) -> L_{a,b,theta}(x) uniformly on compact subsets of (0,1).

*Proof of (i).* Lemma 2 gives (H0) with pi^0 = 0 and (H1), Lemma 3(b) gives (H2), and (LB_pm) gives (SRT_pm)
(Doney). Apply Theorem A. []

*Proof of (ii), (iii).* In the proof of Theorem A, ranges 1 and 2 used only (H0) and (H1). In range 3 split
nu = nu^y + nu^o (Lemma 3). The young part is handled as in Theorem A by Lemma 3(a) and Corollary 4.1. For
the old part put M = t_a + k, n_0 = j, and use Lemma E (n_0 + i is of order N and i <= delta N <= (n_0 + i)/2):
  E_o := sum_{i<=delta N} nu^o_+(k-i) F^-_{j+i}(i) <= C T(N) sum_y f_+(M - y) W(y),
  W(y) = sum_{i+s=y, i<=delta N, s<=t_a/2} omega(i) u_c(s),
with M - y >= t_a/2 + k - delta N >= cN on the range. By (U), u_c <= C omega (with omega(0) = 1), so
- (W1) W(y) <= C (omega*omega)(y) <= C/(y T(y)^2) for y >= 1 (split at y/2, and sum_{i<=Y} omega(i) <= C/T(Y) by Karamata);
- (W2) W(y) <= C omega(y)/T(delta N) for y > 2 delta N.

Part 1, y <= 2 delta N. If alpha > 1/2, 1/(y T(y)^2) is RV with index 2 alpha - 1 > 0, so W <= C/(delta N T(delta N)^2) on
this range and Part 1 <= C T(N)^2/(delta N T(delta N)^2) <= C delta^(2 alpha - 1 - epsilon')/N. If alpha <= 1/2, Part 1 is at most
C T(N) [f_+(M) + sum_{1<=y<=2 delta N} f_+(M-y)/(y T(y)^2)]. By CD Thm 1.4, (SRT_+) holds iff I_1^+ is
asymptotically negligible, and its term z = 1 gives f(x) = o(1/(x T(x))). So Part 1 <= C (zeta_CD(C delta) + o(1))/N
with zeta_CD -> 0.

Part 2, y > 2 delta N. Put eta = delta^(1-alpha), which exceeds 2 delta for small delta.
- (2a) 2 delta N < y <= eta N: sum f_+(M-y) omega(y) <= C omega(delta N)[T_+(M - eta N) - T_+(M - 2 delta N)]
  <= C omega(delta N) T(N)(C eta + o(1)), by (RV) at the scale M of order N. Contribution
  <= C (eta + o(1)) T(N)^2/(delta N T(delta N)^2) <= C (delta^(alpha - epsilon') + o(1))/N.
- (2b) y > eta N, in dyadic blocks (Y, 2Y]: the drop of T_+ over a window of length <= Y inside [cN, M] is
  <= T(N)(C Y/N + o(1)). So the sum is <= C T(N)[sum_Y Y omega(Y)/N + o(1) omega(eta N) log(1/eta)]
  <= C T(N)[1/(N T(N)) + o(1) omega(eta N) log(1/eta)], and the contribution is
  <= C T(N)/(N T(delta N)) + o(1/N) <= C delta^(alpha - epsilon')/N + o(1/N).

So N E_o <= C delta^(min(alpha, 2 alpha - 1) - epsilon') (or C zeta_CD(C delta)) + o(1), which tends to 0 as N -> inf and then
delta -> 0. The minus side is the same with v_- (<= C omega by (U)), f_-, the CD condition for f_- and the mirror
of Lemma E. Under (ii) every hypothesis used ((SRT_pm), (U), Lemma E, the CD condition) is automatic. []

Remarks. (1) Necessity. G Thm 1 needs (SRT_pm) for fresh starts. In the aged decomposition the plus part
sees F^-_{N-d}(k-d), whose small-m excess is T(N) sum_{m small} u^-_m(N-k), with the same j = N - k for every d.
So I expect a failure of (SRT_-) to survive the averaging over d, as in G Cor. lower. Not proved.
(2) The global aging law (ASYY Thm 2) follows under (RV) alone from Lemma 2 and Lamperti's global theorem
for the fresh remainder, by continuous mapping. Theorem B is its local refinement.

### 4.5 Theorem B' (ends)

**Theorem B'.** Same setting.
- (a) (RV_alpha) only: P_N(N) = Q_+(N) -> Q^inf_+(theta) and P_N(0) -> Q^inf_-(theta). These atoms are of order one
  (for a fresh start they are T_+(N) and 0).
- (b) (RV_alpha), (SPAN), (U): for every fixed j >= 1,
  P_N(N - j) = T_+(N)[c_+(theta) u_-(j) + o(1)],     P_N(j) = T_-(N)[c_-(theta) u_+(j) + o(1)].

*Proof.* (a) is Lemma 2 at r = 1. (b) The first-run decomposition at k = N - j reads
P_N(N-j) = sum_{m=1}^{N-1} nu_+(N-m) Pi^-_m(j) + sum_{d=1}^{j} nu_-(d) F^+_{N-d}(N-j).
- Second sum: F^+_{N-d}(N-j) <= C_j T_+(N) (G Thm 2(a)), and nu_-(d) <= max_{n>=t_a/2} v_-(n) + T_-(t_a/2) -> 0 (v_- -> 0 by
  the renewal theorem with infinite mean and (SPAN)). So it is o(T(N)).
- First sum, m > eta N: Pi^-_m(j) = T_+(m)[u_-(j) + o(1)] (G Thm 2(a) for a fresh minus walk, j >= 1), so this part
  is T_+(N) u_-(j) E[T_+(N - D)/T_+(N); Sigma = +, D < (1-eta)N] + o(T(N)) -> T_+(N) u_-(j) int_0^{1-eta} rho_+(z)(1-z)^(-a) dz,
  by Lemma 2 (the integrand converges uniformly on [0, 1-eta]).
- First sum, m <= eta N: Pi^-_m(j) <= C_j T_+(m). Young part, by Lemma 3(a): <= (C/N) sum_{m<=eta N} T(m)
  <= C eta^(1-alpha-epsilon') T(N). Old part: <= C_j sum_y f_+(M' - y) W'(y) with M' = t_a + N and
  W'(y) = sum_{m+s=y, m<=eta N, s<=t_a/2} T(m) u_c(s). By (U), W' <= C everywhere, and W'(y) <= C omega(y) eta N T(eta N)
  for y > 2 eta N. The range y <= 2 eta N costs <= C T(N)(eta + o(1)) (a drop of T_+ over a window of length 2 eta N at
  scale N), and the dyadic blocks above cost <= C T(N)(eta^(1-alpha-epsilon') + o(1)).

Let N -> inf, then eta -> 0. []

Finite-N size of the error. The second sum is T_+(N) sum_{d<=j} nu_-(d) u_-(j-d) + o(T(N)), with
nu_-(d) ~ v_-(t_a) T_-(d) of order 1/(N T(N)). So the relative error in (b) is of order 1/(N T(N) u_-(j)),
growing in j. Diagnostic D1 shows this term is all of the visible bias.

Matching (remark, not a theorem). As x -> 1, L_theta(x) ~ (sin pi a/(pi b)) c_+(theta)(1-x)^(a-1) (the minus integral
stays bounded). With (SRT_-) and pure power tails, T_+(N) c_+ u_-(j) gives the same for 1 << j << N. A uniform
layer-to-bulk statement (the aged analogue of G Thm 2(b)) is not proved.

### 4.6 Properties of L_theta

- Mass: int_0^1 L_theta + Q^inf_+ + Q^inf_- = int_0^1 (rho_+ + rho_-) + int_1^inf (rho_+ + rho_-) = 1.
- theta -> 0: rho_pm dz -> s_pm delta_0, so L_theta -> L uniformly on compacts and Q^inf_pm -> 0 (like theta^a). But
  c_+(theta) -> s_+, not the fresh value 1 (for j >= 1 a fresh start of either sign has layer u_-(j)). The limits
  theta -> 0 and j fixed (or x -> 1) do not commute: for small theta the straddling run is still of length
  theta N >> 1, and only plus straddlers feed the plus layer. ASYY's c(r) -> 1/2 is the case b = 1.
- theta -> inf: Q^inf_pm -> s_pm and L_theta = O(theta^(a-1)), since rho_pm(z) ~ s_pm (sin pi a/pi) theta^(a-1) z^(-a).
- Shape: symmetric under x -> 1 - x when b = 1, and much flatter than L (alpha = 0.7, theta = 1: centre 0.843
  against 1.249). Its critical points were not studied.

---

## 5. Finite mean, 1 < alpha < 2

Notation of Paper F: B_N, h_N, x_{N,k}, L_k = (k - pN)/(1-p), p, s, mu_pm, kappa, G^nu_N,
I_+(v) = [a(1-l) l^(-a-1) + l^(-a)]/mu_- with l = (v-p)/(1-p). Aging time t_a = t_a(N); alpha = alpha_+ in the
plus-end statements.

**Theorem C.** Fresh start of either sign at time 0.
- (a) (Bulk; (RV), (SPAN); any t_a = t_a(N) >= 0.) sup_{1<=k<N} |B_N P_N(k) - h_N(x_{N,k})| -> 0. The bulk stable law does
  not change, whatever the aging time.
- (b) (Atom; (RV), (SPAN), t_a/N -> theta in (0, inf).) P_N(N) = Q_+(N) = (1 + o(1)) (1/s) sum_{i=N}^{N+t_a} T_+(i)
  ~ N T_+(N)(1 - (1+theta)^(1-a))/(s(a-1)). The same at k = 0 with the minus sign.
- (c) (Layer; (RV), (SPAN), t_a/N -> theta.) For every fixed j >= 1,
  P_N(N-j)/T_+(N) -> p u_-(j) + 1/s + (1/s)(1 - (1+theta)^(-a))(1 + mu_+ u_-(j)).
- (d) (Interior of the big-jump zone; (RV), (SPAN) for both signs, (LR) for plus, t_a/N -> theta.) For every
  epsilon, uniformly over k with epsilon N <= L_k <= (1-epsilon)N,
  P_N(k) = (N - L_k) f_+(floor L_k)/mu_- + [2 T_+(L_k) - T_+(L_k + t_a)]/mu_- + o(T_+(N)),
  so P_N(floor(vN))/T_+(N) -> I_+(v) + [l^(-a) - (l + theta)^(-a)]/mu_-.

All four interpolate between the fresh start (theta -> 0) and F Cor. stationary (theta -> inf), and reproduce
the latter at theta = inf: atom N T(N)/(s(a-1)), layer (2/s)(1 + mu_+ u_-(j)), interior term l^(-a)/mu_-.

*Proof of (a).* F's proof of Thm C(a), (b) (sec_preparation.tex) uses the initial run only through three
facts, and each holds uniformly in N for the aged law. (E1) The terms d <= J: any weights of total mass at
most 1. (E2) P(D > J) small uniformly in N: P(Sigma = +, D > J) <= sum_{s<=t_a} T_+(t_a - s + J + 1) <= sum_{i>J} T_+(i) -> 0
(u_c <= 1, finite mean). (E3) The defect is <= (1 + mu_+) B_N sup_{d>N/2} nu^(N)_+(d) <= (1 + mu_+) B_N T_+(N/2) -> 0,
since nu_+(d) <= sum_s f_+(t_a - s + d) <= T_+(d). []

*Proof of (b).* u_c(s) -> 1/s (renewal theorem, (SPAN)); the terms with s < M contribute <= M T(N) = o(N T(N)), and
sum_{i=N}^{N+t_a} T(i) ~ N T(N) int_1^{1+theta} y^(-a) dy. []

*Proof of (c).* First, nu^(N)_+(d) = (1/s)[T_+(d) - T_+(d + t_a + 1)] + o(T_+(N)) uniformly in d >= epsilon N: for
s >= M use u_c(s) = 1/s + o(1) and sum_s f_+(t_a - s + d) <= T(d); for s < M the error is
<= M sup_{n >= t_a + d - M} f_+(n) = o(T(N)), since f(n) = o(T(n)) under (RV). Also pi^(N)_+ -> p and
nu^(N)_-(d) -> T_-(d)/s for fixed d (dominated convergence, v_- -> 1/s). Now follow F's proof of Thm C(d):
- plus initial runs with d <= N/2 give T_+(N)[pi^(N)_+ u_-(j) + o(1)] (F Thm B(a) uniformly in the horizon, and
  (E2));
- minus initial runs (d <= j) give T_+(N) sum_{d<=j} (T_-(d)/s) u_-(j-d) + o(T(N)) = T_+(N)/s + o(T(N)), by the covering
  identity;
- plus initial runs with d > N/2 give sum_{m<N/2} nu_+(N-m) Pi^-_m(j), where nu_+(N-m)/T_+(N) -> (1/s)(1 - (1+theta)^(-a))
  for each fixed m, nu_+(N-m) <= C T(N), and sum_m Pi^-_m(j) = 1 + mu_+ u_-(j) < inf (F Lemma green), so dominated
  convergence gives T_+(N)(1/s)(1 - (1+theta)^(-a))(1 + mu_+ u_-(j)). []

*Proof of (d) (outline).* First-run decomposition at k with L_k = lN.
- Initial runs (either sign) with d <= delta N: the remainder is a fresh walk at horizon N - d with a big jump of
  size about L_k. By F eq. (unif-bigjump) and (E2) this gives the fresh kernel
  (N - L_k) f_+(L_k)/mu_- + T_+(L_k)/mu_- + o(T(N)) (kappa(N-k) -> 1/mu_- in the interior).
- Plus initial runs with delta N < d < L_k - R B_N, and minus initial runs with d > delta N: nu <= C T(N) and the
  remainder needs a second big jump, F <= C T(N); total <= N T(N)^2 = o(T(N)).
- Plus initial runs with d >= L_k - R B_N: with m = N - d the term is sum_m nu_+(N-m) Pi^-_m(N-k). The Green measure
  m -> Pi^-_m(N-k) has mass 1 + mu_+ u_-(N-k) -> s/mu_- and is concentrated within R B_N of (N-k)/(1-p) = N - L_k
  (F Lemma green-conc), while nu_+(N-m) varies on scale N. So this is
  nu_+(L_k) s/mu_- + o(T(N)) = [T_+(L_k) - T_+(L_k + t_a)]/mu_- + o(T(N)).

These are the steps of F Thm C(c) in its regular case, with the fixed law replaced by the triangular array
nu^(N). The properties needed (nu^(N)_+(d) <= C T(N) for d >= epsilon N, uniform continuity on scale N, tightness)
were shown in (c). The epsilon-delta bookkeeping is not written.

Remarks. (1) On the whole zone pN + K lambda_N B_N <= k < N one expects
P_N(k) = G^nu_N(k) + nu^(N)_+(floor L_k)(1 + mu_+ u_-(N-k)) + o(hat G_N(k)), as in F Thm C(c) (regular case). For
L_k << t_a, nu^(N)_+(L_k) ~ T_+(L_k)/s and this is F's stationary kernel G^st; near the end it is (c). Not proved
near the start of the zone.
(2) Mode (with F Thm D(b), (c)). Q_+(N) is RV with index 1 - alpha, as for the stationary start. So for equal
indices the endpoint atom beats the bulk for alpha < phi and loses for alpha > phi, for every theta in (0, inf). For
equal pure-power laws B_N Q(N)/H_N ~ (1 - (1+theta)^(1-a)) C(alpha) N^(1-a+1/a), and at alpha = phi the limit
(1 - (1+theta)^(1-phi)) C(phi) is below C(phi) = 0.7761: the mode is interior. The fresh start is the only case with
no golden-ratio transition.

---

## 6. Numerics

Scripts: `02_aging_exact.py` (pre-registered checks, 18 min) and `02_aging_diagnostics.py` (added after,
about 12 min). The method is in the docstring of the first: Lemma 1 plus the fresh identities, with
G^s(a,b) computed from u^s_m and q^s_m by two matrix products. Laws: zeta, f(n) = n^(-a-1)/zeta(a+1); for
b != 1 the minus law is f(n) proportional to (n+3)^(-a-1).

P9 (brute force over all run sequences, t_a + N <= 14, alpha = 0.5 and 1.5, plus law zeta, minus law shifted by 2):
max difference 6.4e-16; total mass 1 to 15 digits. PASS.

**Infinite mean.** Ratios N P_N(floor(xN))/L_theta(x) over x = 0.1, ..., 0.9:

| alpha | theta | N | max abs(ratio - 1) | ratio at x = 0.5 |
|---|---|---|---|---|
| 0.5 | 0.5 | 500 / 1000 / 2000 | 0.0259 / 0.0185 / 0.0132 | 1.0198 / 1.0140 / 1.0099 |
| 0.5 | 1 | 500 / 1000 / 2000 | 0.0243 / 0.0174 / 0.0124 | 1.0195 / 1.0138 / 1.0098 |
| 0.5 | 2 | 500 / 1000 / 2000 | 0.0228 / 0.0163 / 0.0117 | 1.0193 / 1.0137 / 1.0097 |
| 0.7 | 0.5 | 500 / 1000 / 2000 | 0.1151 / 0.0997 / 0.0853 | 0.8849 / 0.9003 / 0.9147 |
| 0.7 | 1 | 500 / 1000 / 2000 | 0.1190 / 0.1028 / 0.0878 | 0.8810 / 0.8972 / 0.9122 |
| 0.7 | 2 | 500 / 1000 / 2000 | 0.1240 / 0.1068 / 0.0910 | 0.8760 / 0.8932 / 0.9090 |

P1 PASS (0.0124 < 5% at alpha = 0.5; 0.0878 < 15% at alpha = 0.7; both decreasing). At alpha = 0.5 the error behaves
like N^(-1/2). At alpha = 0.7 the slowness is the fresh one (G reports a fresh centre ratio of 0.93 at N = 4000).
The aged density is far from the fresh one (alpha = 0.5, theta = 1: L_theta(1/2) = 0.3676 against L(1/2) = 0.6366), so
the check is not vacuous.

P2 (atom), alpha = 0.5, N = 2000: P_N(N)/Q^inf = 1.0293, 1.0198, 1.0133 for theta = 0.5, 1, 2 (Q^inf = 0.1959, 0.2500,
0.3041), errors shrinking like N^(-1/2). PASS. (alpha = 0.7: 1.0946, 1.0724, 1.0555, decreasing.)

P3 (layer), alpha = 0.5, N = 2000: P_N(N-j)/(T(N) u(j) c_+) for j = 1..5 lies in [1.060, 1.107], [1.050, 1.089],
[1.045, 1.078] for theta = 0.5, 1, 2. **FAIL at theta = 0.5** (1.107 > 1.10); PASS at theta = 1, 2. The bias grows
with j and decays like N^(-1/2). Diagnostic D1: adding the leading correction T_+(N) sum_{d<=j} nu_-(d) u_-(j-d)
(minus straddler with residual <= j, Section 4.5) gives ratios 1.0175-1.0176 (theta = 0.5) and 1.0155-1.0156
(theta = 1) at N = 2000, flat in j, and 1.034, 1.025, 1.018 at N = 500, 1000, 2000 (theta = 0.5). The theorem
stands; the prediction underestimated an o(T(N)) term of relative size 1/(N T(N) u(j)).

P4 (mass): 1 to 1e-8 at alpha = 0.5 and to 1.3e-7 at alpha = 0.7 (quadrature accuracy at the z^(-0.7)
singularities). PASS. The atom formula agrees with direct quadrature of rho to 1e-10. D4: the 2F1 closed form
of c_+ agrees with quadrature to 1e-9 (alpha = 0.3, 0.5) and 2e-6 (alpha = 0.7, quadrature-limited).

A local form of Lemma 2: N nu_+(floor(zN))/rho_+(z) at z = 0.2, 0.5, 0.8 is 1.010-1.015 at N = 2000 (alpha = 0.5,
theta = 1).

D3 (asymmetric, alpha = 0.5, theta = 1, b = 2.4498): N P_N/L_{a,b,theta} at x = 0.1, 0.3, 0.5, 0.7, 0.9 is 1.0034-1.0109
at N = 2000 (1.0056-1.0200 at N = 500); atom ratios 1.0447 and 1.0195; P(plus at t_a) = 0.2974 against
s_+ = 0.2899. This checks the sign share s_+ = 1/(1+b) of Lemma 2 with b != 1.

**Finite mean, alpha = 1.5** (mu = 1.947372, s = 3.894745; B_N = 17, 26, 41 at N = 500, 1000, 2000).

| theta | N | bulk: max abs(aged/fresh - 1), abs(k - N/2) <= B_N | P/Pred at l = 0.3, 0.5, 0.7 | fresh control P/G | atom ratio | layer ratios j = 1..5 |
|---|---|---|---|---|---|---|
| 1 | 500 | 0.0543 | 1.354, 1.181, 1.093 | 1.494, 1.263, 1.146 | 1.0421 | 1.033-1.085 |
| 1 | 1000 | 0.0432 | 1.309, 1.140, 1.071 | 1.402, 1.193, 1.106 | 1.0291 | 1.022-1.048 |
| 1 | 2000 | 0.0347 | 1.242, 1.104, 1.053 | 1.302, 1.139, 1.076 | 1.0203 | 1.015-1.028 |

(theta = 0.5 and 2 are in the output file and behave the same way.)

- P5 **FAIL** (0.0347 > 2% at N = 2000), decreasing like N^(-0.32). Theorem C(a) is a limit statement; the rate
  prediction was too optimistic.
- P6 **FAIL** at l = 0.3 and 0.5 (1.242, 1.104 > 1.10), PASS at l = 0.7. The fresh control column shows that Paper F's
  own big-jump kernel for a fresh start has the same slow bias (1.302 at l = 0.3). So the failure comes from
  the fresh kernel at this N, not from the aging term. Diagnostic D2 isolates the aging increment:
  (P_aged - P_fresh)/(predicted increment) = 0.945, 0.998, 1.002 at l = 0.3, 0.5, 0.7, N = 2000, theta = 1 (from 0.669,
  0.932, 0.974 at N = 500). The aging share of the kernel is 0.17, 0.25, 0.31 (theta = 1). The pre-registered figure
  0.22 at l = 0.5 was an arithmetic slip: the formula gives 0.244.
- P7 PASS: atom ratio 1.020 to the limit formula (1.0198 to the finite sum (1/s) sum T).
- P8 PASS: layer ratios 1.015-1.028.

---

## 7. Honest status

Proved, given the cited inputs (G Thm 1, Thm 2(a), (A1), (A2), (B2), (B3); CD Thm 1.1 eq. (1.6), Thm 1.4,
Sec. 4.1; Doney 1997; Gnedenko's LLT; F Thm B and the proofs of F Thm C(a)-(d), F Lemmas green and
green-conc):
- Lemmas 1-4, Corollary 4.1, Lemma E.
- Theorem A: G's Conjecture `rem:aging` holds under (RV), (SPAN), (SRT_pm), without (LB). The named missing
  near-diagonal bound is closed, by a different route (Lemma 4).
- Theorem B(i): the local aging law for every 0 < alpha < 1 under Doney's condition.
- Theorem B(ii), (iii): the local aging law for 1/2 < alpha < 1 under (RV), (SPAN) alone, and for alpha < 1/2 under
  (SRT_pm) and (U). This is the longest new argument (Parts 1 and 2 of 4.4). It has not been checked
  independently and is the first place to audit.
- Theorem B'(a), (b): atoms and layers.
- Theorem C(a), (b), (c).

Proved in outline: Theorem C(d) (the triangular-array bookkeeping of F Thm C(c) is not written).

Open, named:
- (M-U) For alpha <= 1/2, does (SRT_pm) imply the cycle bound (U), that is, the upper half of SRT for f_+ * f_-? If
  so, Theorem B holds under (SRT_pm) alone for alpha != 1/2.
- (M-1/2) alpha = 1/2 with a general slowly varying factor in Lemma E (both routes lose a slowly varying factor).
- (M-nec) Necessity of (SRT_pm) for the aged local law (expected; Remark (1) of 4.4).
- (M-match) Uniform matching of the aged end layer with the bulk (aged analogue of G Thm 2(b)).
- (M-zone) Theorem C near the start of the big-jump zone (Remark (1) of Section 5).
- Rates: none proved. Observed: N^(-1/2) at alpha = 0.5; at alpha = 0.7 and in the big-jump zone for 1 < alpha < 2 the
  slow convergence is inherited from the fresh laws.

Novelty (bounded search, Section 2): the global aging law for 0 < alpha < 1 is ASYY Thm 2, with a physics-level
proof. I found no local version, no lattice end layers, and no aging result for 1 < alpha < 2 beyond the
stationary start. Theorem A settles G's conjecture as stated, under a weaker hypothesis.

## Files

- `02_aging_exact.py`, `02_aging_output.txt`: exact aged law, brute-force check, P1-P9.
- `02_aging_diagnostics.py`, `02_aging_diagnostics_output.txt`: D1-D4 (added after the predictions).
