# 08. Audit of the aging note (02_aging.md)

Scope: Theorems A, B, B', C of `02_aging.md` and the lemmas they use (Lemmas 1 to 4, Corollary 4.1,
Lemma E, hypothesis (U)). Inputs from Paper G (`sec_setting`, `sec_tools`, `sec_initial`, `sec_ends`,
Theorem `thm:local`) and Paper F (`sec_setting`, `sec_preparation`) were read in the source and taken as
given. Labels (A1), (A2), (B2), (B3) are those of `research_notes/Paper G infinite mean/01_report.md`:
(A1) = G Lemma `lem:sums`(i), (A2) = `lem:sums`(ii), (B2) = G Lemma `lem:key`, (B3) = G Lemma `lem:decay`.
Status words in the note were ignored. Only the mathematics was judged.

Verdicts at a glance.

| Item | Verdict |
|---|---|
| Lemma 2 (marked Dynkin-Lamperti law) | Proved as written |
| Lemma 4 and Corollary 4.1 (counting bound) | Proved as written |
| Theorem A | Correct after a stated restriction (choose epsilon < min(x_1, 1 - x_2)/4, not only epsilon < x_1/4). Cosmetic |
| Lemma E | Proved as written |
| Theorem B(i) | Proved as written |
| Theorem B(ii), (iii) | Proved as written, up to one typo in step (2b) that does not change the bound |
| Theorem B'(a), closed forms of Q^inf and c_+ | Proved as written |
| Theorem B'(b) (end layer, constant c_+(theta)) | Proved as written, under (U) as stated |
| theta -> 0 non-commuting limit | Proved as written |
| Theorem C(a), (b), (c) | Proved as written |
| Theorem C(d) | Incomplete. One step of the outline is false as written; the gap closes by F's own route (Section 4 below) |

No statement was refuted. The exact spot-check (Section 5) agrees with B'(a), B'(b), C(b), C(c).

---

## 1. Theorem A and the counting bound

### Claim card

- Hypotheses: (RV_alpha) with 0 < alpha < 1, (SPAN), (SRT_pm). The initial run law nu^(N) depends on N and
  satisfies (H0) (pi^0 = lim_eps lim_N P(D < eps N) exists), (H1) (P(Sigma = pm, D/N in .) converges
  vaguely on (0,1) to rho_pm(z) dz, rho_pm continuous), (H2) (sup_N sup_{eps N <= d <= (1-eps)N} N nu_pm(d) < inf).
- Conclusion: N P_N(floor(xN)) -> pi^0 L(x) + int_0^x rho_+(z) L((x-z)/(1-z)) dz/(1-z)
  + int_0^{1-x} rho_-(z) L(x/(1-z)) dz/(1-z), uniformly on compacts of (0,1).
- Key input: Lemma 4. For a fresh minus walk,
  sum_{i=0}^{I} F^-_{n_0+i}(i) <= C m_0 T_-(n_0) + exp(-m_0 T_+(I+1)) + u_-(n_0) sum_{n=1}^{I} T_+(n).

### My derivation of the critical step (Lemma 4)

F^-_{n_0+i}(i) = P(C_{n_0+i} = n_0), where C_m counts minus steps among the first m. By Tonelli the sum is
E #{m in [n_0, n_0+I] : C_m = n_0}. The level set {m : C_m = n_0} is [t_{n_0}, t_{n_0+1}). Its length is 1,
except when step t_{n_0} closes a minus run r (S^-_r = n_0), and then it is 1 + X^+_r. Intersecting with a
window of I+1 integers that starts at n_0 <= t_{n_0}:

  count <= 1{t_{n_0} <= n_0 + I} + sum_r 1{S^-_r = n_0} min(X^+_r, I).

X^+_r is independent of {S^-_r = n_0} (the event is a function of minus runs only), and
E min(X_+, I) = sum_{n=1}^{I} T_+(n). So the second term has expectation u_-(n_0) sum_{n<=I} T_+(n).
For the first, t_{n_0} - n_0 = S^+_{J-1} with J - 1 = #{r >= 1 : S^-_r < n_0}, a function of the minus runs.
{J - 1 < m_0} = {S^-_{m_0} >= n_0} has probability <= C m_0 T_-(n_0) by (A1). On {J - 1 >= m_0},
S^+_{J-1} >= S^+_{m_0}, and by independence P(S^+_{m_0} <= I) <= (1 - T_+(I+1))^{m_0}. This is the
stated bound. The mirror for F^+_{n_0+i}(n_0) is the same with signs exchanged.

Corollary 4.1, with n_0 >= cN, I = delta N, m_0 = ceil(eta/T_+(N)), eta = delta^(a/4):
- C m_0 T_-(n_0) <= C_c (eta + T_+(N)) (Potter for T_-(n_0) <= C_c T_+(N));
- m_0 T_+(delta N + 1) >= eta T_+(delta N)/T_+(N) >= delta^(a/4) delta^(-a/2) = delta^(-a/4) for N >= N_0(delta);
- u_-(n_0) <= C omega_-(n_0) <= C_c/(N T(N)) (upper half of SRT_-), and
  sum_{n<=delta N} T_+(n) <= C delta N T(delta N) <= C delta^(1-a-eps') N T(N) (Karamata, Potter).
All three terms tend to 0 with delta. Correct.

### Implications checked (proof of Theorem A)

1. Range d < eps N. Horizon n = N - d >= (1-eps)N; (k-d)/n lies in a compact of (0,1) and differs from k/N by
   <= 2 eps. G Theorem `thm:local`(ii) is uniform in the ratio as n -> inf, so it is uniform over all
   n >= (1-eps)N. With N/n = 1 + O(eps) and uniform continuity of L: N F^-_{N-d}(k-d) = L(k/N) + O(eps) + o(1).
   Checked. Both signs give the same L (G's local law does not depend on the starting sign), so this range
   gives P(D < eps N) L(x) + O(eps) + o(1). Checked.
2. Range eps N <= d <= k - delta N. (k-d)/(N-d) in [delta, (x_2 - eps)/(1 - eps)], horizon >= (1 - x_2)N, so
   N F = g_x(d/N) + o(1) uniformly. g_x is continuous on [eps, x - delta] and the limit measure has a density,
   so (H1) gives convergence of the weighted sum. The o(1) error multiplies total mass <= 1. (H2) is not used
   here. Checked.
3. Range k - delta N < d <= k. Terms nu_+(k-i) F^-_{j+i}(i) with i <= delta N and n_0 = j = N - k >= (1-x_2)N.
   (H2) needs d in [eps N, (1-eps)N]; this holds if eps <= 1 - x_2 - delta. The note only states
   eps < x_1/4. For the minus part the near-diagonal d lie in (j - delta N, j] and need eps <= x_1.
   **Restriction:** take 0 < delta < eps < min(x_1, 1 - x_2)/4. With that, N * sum <= C_eps zeta(delta). Checked.
4. Minus part: F^+_{N-d}(k) = F^+_{k+i'}(k), i' = j - d, mirror of Corollary 4.1 with n_0 = k >= x_1 N and the
   upper half of SRT_+. Checked.
5. Limits. N -> inf, then delta -> 0 (g_x(z) ~ C (x-z)^(a-1) is integrable at z = x, rho_+ bounded near x),
   then eps -> 0 (rho_pm integrable on (0,1) because the vague limit of sub-probabilities has mass <= 1, and
   g_x is bounded near z = 0), using (H0) for the range-1 mass. Checked.
6. G's hypotheses imply (H0)-(H2): uniform convergence of N nu(floor(zN)) on compacts gives the vague
   convergence by Riemann sums; the sup bound on d >= eps N gives (H2). Checked. So G's Conjecture
   `rem:aging` holds, with (LB_pm) replaced by (SRT_pm).

Verdict: **correct after the stated restriction on eps** (a bookkeeping choice; nothing else changes).

---

## 2. Theorem B (local aging law in the bulk, 0 < alpha < 1)

### Claim card

- Setting: fresh start (either sign or a mixture), t_a/N -> theta in (0, inf), (RV_alpha), (SPAN).
- (i) under (LB_pm); (ii) 1/2 < alpha < 1 with nothing more; (iii) alpha < 1/2 with (SRT_pm) and (U), or
  alpha = 1/2 with (SRT_pm), (U) and n T(n)^2 bounded above and below.
- Conclusion: N P_N(floor(xN)) -> L_{a,b,theta}(x) uniformly on compacts of (0,1).

### Lemma 2 (feeds (H0), (H1)), checked in full

P(+, D >= rN) = sum_{s=0}^{t_a} u_c(s) T_+(t_a - s + rN): a plus run starting at step s+1 with length l
straddles step t_a+1 iff s <= t_a and l >= t_a - s + 1, residual d = s + l - t_a. Checked. T_c ~ (1+b) T_+
and U_c(n) T_c(n) -> sin(pi a)/(pi a) = 1/(Gamma(1-a) Gamma(1+a)) (Karamata Tauberian). The limit measure
d(y^a) has no atom at theta, and T_+(t_a - y + rN)/T_+(N) -> (theta - y + r)^(-a) uniformly on [0, theta].
Identity (I) re-derived: with v = y/(theta + r - y), y^(a-1)(theta + r - y)^(-a-1) dy = (theta+r)^(-1) v^(a-1) dv,
upper limit theta/r, giving theta^a/(a r^a (theta + r)). Differentiating gives rho_+ with s_+ = 1/(1+b). The minus
sign uses v_- = f_+ * u_c, whose partial sums are ~ U_c (dominated convergence). Total mass:
(sin pi a/pi) int_0^inf theta^a z^(-a)/(theta+z) dz = 1, so pi^0 = 0 and P(Sigma = pm) -> s_pm. Lemma 2 needs no
(SPAN). **Proved as written.**

Hypothesis (U) (u_c, v_- <= C omega_+): the three sufficient conditions were checked. Under (LB_pm),
f_c(n) <= C T(n)/n by splitting at n/2, so Doney applies to f_c. For alpha > 1/2: SRT for the aperiodic cycle
law (the support of f_+ * f_- has difference gcd 1 because supp f_+ does), and for v_- the far part is
f_+(n) + C sum_{z<n/2} f_+(n-z)/(z T(z)^2) <= C omega(n), since 1/(z T(z)^2) has positive index 2a - 1 (BGT 1.5.3)
and f_+(n) <= T(n) <= omega(n) eventually. Correct.

### Lemma E, checked

Term 1 <= C T_-(j) u_+(i) by (B2), and u_+ <= C omega_+. Term 2 with q^+_m(i) <= C T(i) e^{-c m T(i)} (B3):
- alpha > 1/2: u^-_m(j) <= C m T(j)/a_m (CD (1.6)); m/a_m has index 1 - 1/a in (-1, 0), so
  sum_m (m/a_m) e^{-c m T(i)} <= C M^2/a_M with M = 1/T(i), a_M ~ i, giving C/(i T(i)^2). Checked.
- alpha < 1/2: Term 2 <= C T(i) u_-(j) <= C T(i)/(n T(n)), and i T(i)^2 has index 1 - 2a > 0. Checked.
**Proved as written.**

### Critical step re-derived: the old part E_o in (ii), (iii)

E_o = sum_{i<=delta N} nu^o_+(k-i) F^-_{j+i}(i). Lemma E applies since i <= delta N <= j (needs delta <= 1 - x_2).
So E_o <= C T(N) sum_y f_+(M - y) W(y) with M = t_a + k, y = i + s, and M - y >= t_a/2 + k - delta N >= cN.

(W1) (omega * omega)(y) <= 2 omega(y/2) sum_{i<=y/2} omega(i) <= C/(y T(y)^2). (W2) for y > 2 delta N, s >= y/2,
so W(y) <= C omega(y) sum_{i<=delta N} omega(i) <= C omega(y)/T(delta N). Both checked.

- Part 1, alpha > 1/2: sup_{y<=2 delta N} W(y) <= C/(delta N T(delta N)^2) (positive index; W(0) = 1 is dominated
  since delta N T(delta N)^2 -> 0). Contribution <= C T(N)^2/(delta N T(delta N)^2) ~ C delta^(2a-1)/N. Checked.
- Part 1, alpha <= 1/2: CD Theorem 1.4 at x = M with z <= 2 delta N <= C delta M, uniform over M in the range; the
  term z = 1 gives f_+(x) = o(1/(x T(x))), so T(N) f_+(M) = o(1/N). Checked.
- (2a): sum_{2 delta N < y <= eta N} f_+(M-y) W(y) <= C [omega(delta N)/T(delta N)] [T_+(M - eta N) - T_+(M - 2 delta N)], and the
  bracket is <= T(N)(C eta + o(1)) by uniform convergence at scale N (M - eta N >= cN). Times C T(N):
  C (eta + o(1)) T(N)^2/(delta N T(delta N)^2) ~ C delta^a/N with eta = delta^(1-a). Checked.
- (2b): on a dyadic block (Y, 2Y], W <= C omega(Y)/T(delta N) and the T_+ drop is <= T(N)(C Y/N + o(1)). Summing,
  sum_Y Y omega(Y) = sum_Y 1/T(Y) <= C/T(N) (geometric, largest block of order N). Contribution
  <= C T(N) * T(N)/T(delta N) * [1/(N T(N)) + o(1) omega(eta N) log(1/eta)] = C T(N)/(N T(delta N)) + o(1/N). This is
  the note's final bound. **Typo:** the middle display of (2b) omits the factor 1/T(delta N) from (W2); the
  final line includes it, so the conclusion stands.

So N E_o <= C delta^(min(a, 2a-1) - eps') (or C zeta_CD(C delta)) + o(1). The young part is Lemma 3(a) plus
Corollary 4.1; Lemma 3(a) uses (U) and s > t_a/2 >= cN. The minus side mirrors with v_-, f_- and the mirror of
Lemma E. Under (ii) every input ((SRT_pm), (U), Lemma E, the CD condition) is automatic. Checked.

### Implications checked, (i)

Lemma 2 gives (H0) with pi^0 = 0 and (H1). Lemma 3(b): under (LB), f_+(t_a - s + d) <= C T(N)/N for s <= t_a/2
and U_c(t_a/2) <= C/T(N), so the old part is <= C/N; the young part by (U), which (LB) implies. (LB) gives
(SRT) by Doney. Theorem A applies (with the eps restriction of Section 1). Checked.

Verdict: **(i) proved; (ii), (iii) proved as written** (one typo in (2b), the eps/delta ranges as in Section 1).

---

## 3. End atoms, end layers, c_+(theta), and theta -> 0

### Claim card

- B'(a), (RV) only: P_N(N) = Q_+(N) -> Q^inf_+(theta) = s_+ (sin pi a/pi) B(theta/(1+theta); a, 1-a), and P_N(0) -> Q^inf_-.
- B'(b), (RV), (SPAN), (U): P_N(N-j) = T_+(N)[c_+(theta) u_-(j) + o(1)] for fixed j >= 1, with
  c_+(theta) = int_0^1 rho_+(z)(1-z)^(-a) dz = s_+ (sin pi a/pi) theta^(a-1) B(1-a,1-a) 2F1(1, 1-a; 2-2a; -1/theta).
- theta -> 0: L_theta -> L, Q^inf -> 0, but c_+(theta) -> s_+ (not the fresh value 1).

### Derivations

Atom: B'(a) is Lemma 2 at r = 1. Closed form: z = theta w, then u = 1/(1+w) turns w^(-a)/(1+w) dw into
u^(a-1)(1-u)^(-a) du on (0, theta/(1+theta)). Checked.

Layer constant: 1/(theta + z) = theta^(-1)(1 + z/theta)^(-1) and Euler's integral with b = 1 - a, c = 2 - 2a gives the
2F1 form. At a = 1/2, theta = 1: (1/2)(1/pi) * pi * 2^(-1/2) = 1/(2 sqrt 2). Checked (I did not re-read ASYY for
their c(r)).

Critical step of B'(b): the first-run decomposition at k = N - j:
P_N(N-j) = sum_{m=1}^{N-1} nu_+(N-m) Pi^-_m(j) + sum_{d=1}^{j} nu_-(d) F^+_{N-d}(N-j).
- Second sum: F^+_{N-d}(N-j) <= C_j T_+(N) (G Theorem `thm:ends`(a)), and nu_-(d) <= sup_{s > t_a/2} v_-(s) + T_-(t_a/2) -> 0
  (renewal theorem with infinite mean; aperiodicity of the cycle law follows from (SPAN)). Checked.
- m > eta N: Pi^-_m(j) = T_+(m)[u_-(j) + o(1)] uniformly in m >= eta N, and
  sum_{d < (1-eta)N} nu_+(d) T_+(N-d)/T_+(N) -> int_0^{1-eta} rho_+(z)(1-z)^(-a) dz by Lemma 2 (bounded continuous integrand
  on [0, 1-eta], no limit mass at 0). Checked.
- m <= eta N, young part: (C/N) sum_{m<=eta N} T(m) <= C eta^(1-a-eps') T(N). Checked.
- m <= eta N, old part: W'(y) = sum_{m+s=y} T(m) u_c(s) <= C (split at y/2: T(y/2) * C/T(y), and omega(y/2) * C y T(y)), and
  W'(y) <= C omega(y) eta N T(eta N) for y > 2 eta N. The range y <= 2 eta N costs C T(N)(eta + o(1)). The dyadic part
  costs C eta N T(eta N) T(N)[1/(N T(N)) + o(1) omega(eta N)] = C eta T(eta N) + o(T(N)) <= C eta^(1-a-eps') T(N) + o(T(N)).
  Checked.

theta -> 0: int_0^1 z^(-a)(1-z)^(-a)/(theta + z) dz ~ theta^(-a) int_0^inf w^(-a)/(1+w) dw = theta^(-a) pi/sin(pi a), so
c_+ -> s_+. rho_pm has total mass s_pm on (0, inf) and lives on scale theta, so rho_pm dz -> s_pm delta_0 and L_theta -> L;
Q^inf_pm ~ s_pm (sin pi a/pi) theta^a/a. The fresh layer is u_-(j) for either starting sign (G `thm:ends`(a)), so
lim_{theta->0} lim_N P_N(N-j)/(T_+(N) u_-(j)) = s_+ while at theta = 0 the limit is 1. The two limits do not
commute. The mechanism stated in the note (a minus straddler of length about theta N >> j cannot end within the
plus layer) is the right one. Checked.

Matching remark: the plus integral of L_theta behaves like (sin pi a/(pi b)) c_+(theta)(1-x)^(a-1) as x -> 1, consistent
with T_+(N) c_+ u_-(j) under pure power tails. This is labelled a remark and was not audited as a theorem.

Verdict: **B'(a), the closed forms and the theta -> 0 statement are proved as written; B'(b) is proved as
written under (U).**

---

## 4. Theorem C (1 < alpha < 2)

### Claim card

- (a) any t_a(N) >= 0: sup_{1<=k<N} |B_N P_N(k) - h_N(x_{N,k})| -> 0.
- (b) t_a/N -> theta: P_N(N) = Q_+(N) ~ (1/s) sum_{i=N}^{N+t_a} T_+(i) ~ N T_+(N)(1 - (1+theta)^(1-a))/(s(a-1)).
- (c) fixed j >= 1: P_N(N-j)/T_+(N) -> p u_-(j) + 1/s + (1/s)(1 - (1+theta)^(-a))(1 + mu_+ u_-(j)).
- (d) (RV), (SPAN) both signs, (LR) plus: uniformly on eps N <= L_k <= (1-eps)N,
  P_N(k) = (N - L_k) f_+(floor L_k)/mu_- + [2 T_+(L_k) - T_+(L_k + t_a)]/mu_- + o(T_+(N)).

(Notation: the note uses s both for mu_+ + mu_- and as the start index in Lemma 1. Worth separating in a paper.)

### (a): checked against F's proof of Theorem `thm:preparation`(a), (b)

F's proof uses the initial law only through: E_1 (d <= J, weights of total mass <= 1, and the shift estimate
(prep-shift) is uniform in k and does not involve nu); E_2 <= C P(D > J); the defect
<= (1 + mu_+) B_N sup_{d > N/2} nu_+(d). For the aged law, P(+, D > J) = sum_{s<=t_a} u_c(s) T_+(t_a - s + J + 1)
<= sum_{i > J} T_+(i) uniformly in N and t_a (u_c <= 1), the same for minus (v_- <= 1), and
nu_+(d) <= sum_s f_+(t_a - s + d) <= T_+(d), so the defect is <= C B_N T_+(N/2) -> 0. The atoms sit at k = 0, N,
outside the range. **Proved as written**, for every t_a(N).

### (b): checked

Q_+(N) = sum_{i=N}^{N+t_a} u_c(t_a - (i - N)) T_+(i). u_c -> 1/s (aperiodic cycle law, finite mean); the M terms
nearest i = N + t_a cost <= M T(N) = o(N T(N)); sum_{i=N}^{N+t_a} T(i) ~ N T(N) int_1^{1+theta} y^(-a) dy. theta -> inf gives
F's stationary atom. **Proved as written.**

### (c): extra terms re-derived

nu_+(d) = sum_{s<=t_a} u_c(s) f_+(t_a - s + d). Replacing u_c by 1/s gives (1/s)[T_+(d) - T_+(d + t_a + 1)] exactly; the
error is sup_{s>=M} |u_c(s) - 1/s| T(d) + M sup_{n >= t_a + d - M} f_+(n) = o(T(N)) uniformly in d >= eps N. Then:
- plus initial runs d <= N/2: Pi^-_n(j)/T_+(n) -> u_-(j) uniformly in n >= N/2 (F `thm:bigjump`(a)), weights tight by
  the bound in (a), and P(Sigma = +) -> mu_+/s = p by dominated convergence. Gives T_+(N) p u_-(j). Checked.
- minus initial runs d <= j: nu_-(d) -> (1/s) sum_{i>=0} f_-(i + d) = T_-(d)/s (v_- -> 1/s), and the covering identity
  sum_{d<=j} T_-(d) u_-(j-d) = 1 gives T_+(N)/s. Checked.
- plus initial runs d > N/2 (m = N - d < N/2): nu_+(N-m)/T_+(N) -> (1/s)(1 - (1+theta)^(-a)) for each m,
  nu_+(N-m) <= T_+(N/2) <= C T(N), and sum_m Pi^-_m(j) = 1 + mu_+ u_-(j) (F `lem:green`). Dominated convergence.
  Checked.
theta -> inf reproduces F `cor:stationary`(c), (2/s)(1 + mu_+ u_-(j)). **Proved as written.**

### (d): what is missing

The target is true, and F's own proof gives it, but the outline as written has a false step.

- **False intermediate bound.** Bullet 2 claims that plus initial runs with delta N < d < L_k - R B_N contribute
  <= N T(N)^2 because "the remainder needs a second big jump, F <= C T(N)". For y = L_k - d between R B_N and o(N),
  the remainder point k - d sits at excess (1 - p) y over its mean, and F^-_{N-d}(k-d) is of order
  (N/y) T_+(y), not T(N); near y = R B_N it is of order 1/B_N. With nu_+ <= C T(N) on that range the sum is
  about C T(N) N sum_{y >= R B_N} T(y)/y ~ C R^(-a) T(N): small only as R -> inf, and not of order N T(N)^2. When
  alpha_+ != alpha_- the zone of F eq. (unif-bigjump) also needs y >= K lambda_N B_N with lambda_N unbounded, so the
  pointwise route does not even reach y ~ R B_N.
- **How it closes.** Use F's decomposition from the proof of `thm:preparation`(c) instead of bullets 1 and 2.
  That proof bounds |P_N(k) - G^nu_N(k) - Psi_N(k)| by C(eps + r_N + J/(K B_N) + P(D > J)) hat G_N(k), with C, r_N, K_0
  independent of the initial law except through pi_pm and P(D > J). So it holds verbatim for the triangular array
  nu^(N), since sup_N P(D^(N) > J) -> 0 (shown in (a)). All d >= L_k/2 go into
  Psi_N(k) = sum_{d >= L_k/2} nu^(N)_+(d) Pi^-_{N-d}(N-k), handled as in F's "regular case": Green identity, Green
  concentration (`lem:green-conc`) within R B_N = o(N) of L_k, the scale-N continuity of nu^(N)_+ from (c), and
  sup_{d >= eps N/2} nu^(N)_+(d) <= C T(N). This gives Psi_N(k) = nu^(N)_+(floor L_k)(1 + mu_+ u_-(N-k)) + o(T(N)) on
  the interior zone.
- **Smallest missing implications**, in order: (1) the statement that F's decomposition constants depend on
  nu only through pi_pm and P(D > J); (2) the triangular-array regular case for Psi_N above; (3)
  kappa^(N)_+(j) -> 1/mu_- as j -> inf uniformly in N (split sum_{d<=j} nu_-(d) u_-(j-d) at d = J and use the uniform
  tail). Then 1 + mu_+ u_-(N-k) -> s/mu_- and nu_+(L_k) s/mu_- = [T_+(L_k) - T_+(L_k + t_a)]/mu_- + o(T(N)) give the
  stated kernel, and the limit I_+(v) + [l^(-a) - (l + theta)^(-a)]/mu_- follows. Each of (1)-(3) is short. None needs a
  new idea.

Verdict: **(a), (b), (c) proved as written; (d) incomplete** (missing implications (1)-(3); bullet 2 must be
replaced, not just expanded).

Not audited: the golden-ratio remark (it depends on F Theorem D) and Remark (1) of Section 5.

---

## 5. Exact spot-check (independent recursion)

Script: `audit_aging_check.py` in the session scratch folder (run with `py -I`). Written from scratch:
it propagates "a run of sign sigma starts at absolute step t+1" from a fresh plus start, cuts the straddling
run at t_a, and then runs a forward recursion inside the window on (window time, minus count <= 5). It does not
use u_c, v_- or the fresh identities. Laws: zeta, f(n) = n^(-a-1)/zeta(a+1), both signs (b = 1, s_+ = 1/2).
Brute force over all sign strings (t_a + N <= 12, alpha = 0.5 and 1.5, minus law shifted by 2): max difference
2.2e-16 on P_N(N-j), j <= 4.

alpha = 0.5. Closed forms against quadrature: Q^inf = 0.1959132760 (theta = 0.5), 0.25 (theta = 1); c_+ = 0.4082482905,
0.3535533906, equal to 10 digits.

| theta | N | P_N(N)/Q^inf | P_N(N-j)/(T(N) u(j) c_+), j = 1..5 | same after removing the minus-straddler term |
|---|---|---|---|---|
| 0.5 | 1000 | 1.0418 | 1.085 to 1.152 | 1.0259 to 1.0282 |
| 0.5 | 2000 | 1.0293 | 1.060 to 1.107 | 1.0182 to 1.0192 |
| 0.5 | 4000 | 1.0206 | 1.043 to 1.075 | 1.0128 to 1.0132 |
| 1 | 1000 | 1.0282 | 1.071 to 1.126 | 1.0229 to 1.0244 |
| 1 | 2000 | 1.0198 | 1.050 to 1.089 | 1.0161 to 1.0167 |
| 1 | 4000 | 1.0139 | 1.036 to 1.062 | 1.0113 to 1.0116 |

alpha = 1.5, theta = 1 (Theorem C(b), (c)):

| N | atom / limit formula | atom / (1/s) sum T | layer / C(c) value, j = 1..5 |
|---|---|---|---|
| 1000 | 1.0291 | 1.0281 | 1.022 to 1.048 |
| 2000 | 1.0203 | 1.0198 | 1.015 to 1.028 |
| 4000 | 1.0142 | 1.0139 | 1.010 to 1.017 |

All deviations shrink by about 1/sqrt 2 per doubling of N, toward 1. This agrees with B'(a), B'(b) (including the
size 1/(N T(N) u(j)) of the minus-straddler correction), C(b) and C(c). The alpha = 0.5, N = 2000 values coincide
with those in Section 6 of the note, computed there by a different method.

---

## 6. Corrections to make in the note

1. Theorem A proof: choose 0 < delta < eps < min(x_1, 1 - x_2)/4 (also delta <= 1 - x_2 for Lemma E in Theorem B).
2. Theorem B, step (2b): insert the factor 1/T(delta N) in the middle display.
3. Theorem C(d): replace bullets 1 and 2 by F's decomposition, whose constants depend on the initial law only
   through pi_pm and P(D > J), and prove the triangular-array regular case for Psi_N. The claim
   "total <= N T(N)^2" is false for L_k - d = o(N).
4. Rename the start index s in Lemma 1, or the mean cycle length s, in Section 5.
