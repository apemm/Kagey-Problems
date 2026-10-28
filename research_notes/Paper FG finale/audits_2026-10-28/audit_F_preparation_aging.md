# Audit of Paper F: Theorem thm:preparation for families, Lemma lem:aged-nu, Theorem thm:aging, Corollary cor:aged-mode, Remark rem:uniform-layer

Date: 2026-10-27. Files audited: `kagey-problems/problem131/paperF/sec_preparation.tex`, `sec_aging.tex`, `sec_bigjump.tex` (lines 1 to 125 and 620 to 700), with `sec_setting.tex` for the definitions. Taken as given: Theorem thm:bulk, Theorem thm:bigjump, Lemmas lem:rv, lem:profile, lem:green, lem:green-conc, lem:prep-tight, display eq:unif-bigjump, and Proposition prop:first-run. No file in `paperF` or `paperG` was edited.

Method: for each claim I wrote a claim card, re-derived the critical step from the definitions before reading the author's argument, then checked every implication of the proof as printed. Where a step reduces to a fresh-start input, the entry names that input.

## Summary of verdicts

| Claim | Verdict |
|---|---|
| 1a. Theorem thm:preparation(a) for families | Proved as written |
| 1b. Theorem thm:preparation(b), including the family criteria and the fixed-law iff | Proved as written |
| 1c. Theorem thm:preparation(c): decomposition, whole-zone criteria, regular case under (R nu) | Proved as written |
| 1d. Theorem thm:preparation(d), including the regular case | Proved as written |
| 1e. Theorem thm:preparation(e) | Proved as written, conditional on Lemma lem:no-giant and Lemma lem:giant (eq:giant-split, eq:giant-crude) from `sec_bigjump.tex`, which supply eq:far-bound |
| 2a. Lemma lem:aged-nu(a), (b), (c) | Proved as written |
| 2b. Theorem thm:aging(a), (b), (c) with (i) and (ii) | Proved as written |
| 2c. Corollary cor:aged-mode | Proved as written |
| 3. Remark rem:uniform-layer | Proved as written |

No claim is refuted, restricted or incomplete. The items under "Cosmetic findings" are wording issues that don't affect any proof.

## Claim 1a. Theorem thm:preparation(a), the exact defect

Claim card. Under (RV) and (SPAN) for both signs and the tightness eq:tight on the family, uniformly in 0 <= k <= N, B_N P_N(k) equals h_N(x_{N,k}) plus the two atoms plus D^+_N(N-k) + D^-_N(k) plus o(1), where the o(1) depends on the family only through eps_J.

Independent derivation. Split Proposition prop:first-run by the first-run length: d <= J, J < d <= N/2, N/2 < d < N. The third block is the defect by definition (m = N - d runs over 1 <= m < N/2). The second block is at most B_N sum_{J<d<=N/2} nu(d) C_10 / B_{N-d}, and B_N / B_{N/2} is bounded by Lemma lem:rv(v), so it is at most C eps_J by eq:tight. For each fixed d, B_N F^-_{N-d}(k-d) and B_N F^+_{N-d}(k) converge to h_N(x_{N,k}) uniformly in k by Theorem thm:bulk(a) at the horizon N - d, Lemma lem:profile(c) for the switch of horizon, and the Lipschitz and tail bounds of Lemma lem:profile(a), (b). The weights of the first block are at most 1, so the first block differs from P(D <= J) h_N(x_{N,k}) by o(1) uniformly in the family. The remainder P(D > J) h_N is at most C_1 eps_J.

Check of the author's argument. It is this argument. The error bound (C_1 + C C_10) eps_J is independent of N and of the member of the family. The only place the family enters is through the weights, and they are bounded by eps_J or by 1.

Verdict: proved as written.

## Claim 1b. Theorem thm:preparation(b), the bulk criterion

Claim card. Two identities for the interior and whole-range errors, the family criteria ("if B_N nubar(N/2) -> 0, only if B_N P(D^{(N)} = N-1) -> 0", plus the atoms for the whole range), the fixed-law iff statements, and the macroscopic interior with no condition.

Independent derivation of the critical steps.

- Disjoint supports. D^+_N(N-k) > 0 needs some m < N/2 with Pi^-_m(N-k) > 0, hence N - k <= m < N/2, so k > N/2. Symmetrically D^-_N(k) > 0 forces k < N/2. As k runs over 1 <= k < N, the arguments N - k and k run over all b >= 1 at which the defects can be positive. So the supremum of the sum is the maximum of the two suprema.
- Lower bound. The term m = 1, b = 1 of eq:defect is B_N nu_+(N-1) Pi^-_1(1) = B_N nu_+(N-1), because a one-step fresh minus walk has one minus step. So max(Delta_+, Delta_-) >= B_N P(D^{(N)} = N-1) / 2.
- Upper bound. Lemma lem:green with u_- <= 1 gives sum_m Pi^-_m(b) <= 1 + mu_+, so Delta_{+,N} <= (1 + mu_+) B_N nubar_+(N/2).
- Fixed law. The remark after eq:envelope: nubar_+(n) = o(T_+(n)) iff nu_+(n) = o(T_+(n)) because T_+ is nonincreasing; B_n nubar(n/2) -> 0 iff B_n P(D = n) -> 0 because B_n <= C B_d for d >= n/2 (Lemma lem:rv(ii), (v)). Both equivalences check. Together with B_N / B_{N-1} -> 1, the "if" and "only if" conditions coincide for a fixed law. For the whole range, nu_sigma <= Q_sigma gives the reading B_n P(D >= n) -> 0.
- Macroscopic interior. For eps N <= k <= (1 - eps) N, a nonzero term of D^+_N(N-k) has m >= N - k >= eps N, so Pi^-_m(N-k) <= C_10 / B_{eps N}, and the weights sum to at most P(D^{(N)} > N/2) <= eps_J for N > 2J.

Check of the author's argument. The equality sup |f + g| = sup |f| + O(sup |g|) is applied correctly. At k = N the term h_N(x_{N,N}) tends to zero because x_{N,N} = (1 - p) N / B_N -> infinity. The family versions of the criteria are stated as one-directional implications, which is what the proof gives, and the iff is claimed only for a fixed law, where it holds.

Verdict: proved as written.

## Claim 1c. Theorem thm:preparation(c), the big-jump zone

Claim card. Three statements. (1) Decomposition: in the double limit over the zone pN + K lambda_N B_N <= k <= N, P_N(k) = Q_+(N) 1_{k=N} + G^nu_N(k) + Psi_N(k) + o(Ghat_N(k)), uniformly over families with eq:tight. (2) Psi_N can be dropped if nubar_+(n) = o(T_+(n)), and only if nu_+(N-1) = o(T_+(N)). (3) Regular case: under (R nu) uniformly in N, Psi_N(k) can be replaced by nu_+(floor L_k)(1 + mu_+ u_-(N-k)) 1_{k<N}, with Ghat_N(k) + nu_+(floor L_k) as the size function, on the whole zone including the end.

Independent derivation of the critical steps.

- Geometry (Step 1). For d <= j and n = N - d: L^{(n)}_k = L + pd/(1-p) >= L, and k - pn >= k - pN >= K lambda_N B_N >= (K/2) lambda_n B_n by eq:lambda-unif and monotonicity of B. For d < L/2 and n = N - d >= N/2: L^{(n)}_{k-d} = L - d >= L/2 and (k - d) - pn = (1 - p)(L - d) >= (K/4) lambda_n B_n. Both points lie in the zone of eq:unif-bigjump at their horizons when K >= 4 K_0. The comparison Ghat_n(k-d) <= (2N/L) T_+(floor(L/2)) <= C_* Ghat_N(k) uses Potter's bound. All checks pass.
- Kernels (Step 3). With n = N - d and kappa^{(+)}(j-d) = u_-(j-d), kappa^{(-)}(j) = u_-(j) 1_{j>=1} from eq:kappa, the two fresh kernels are as displayed, with n - L' = (j - d)/(1 - p) for the plus start and n - (L - d) = N - L for the minus start. The continuity of f_+ and T_+ at scale floor(L) under shifts of at most 2J/(1-p) follows from (LR) and (RV). The bound f_+(floor L') <= 2C T_+(floor L)/L uses L' >= L. The weight bookkeeping gives kappa_+(j) = pi_+ u_-(j) 1_{j>=1} + sum_{d<=j} nu_-(d) u_-(j-d) with an error of at most eps_J Ghat, and pi_+ + pi_- = 1 because D is finite almost surely. The case j < J is handled by the bound C (J/L) Ghat on both the interior term and its target. Checks pass.
- Only-if direction of (2). At k = N - 1, L = N - 1/(1-p) >= N/2, so d = N - 1 >= L/2 is a term of Psi, and Psi_N(N-1) >= nu_+(N-1) F^-_1(0) = nu_+(N-1). Ghat_N(N-1) <= 2 T_+(floor(N/2)) <= C T_+(N). The point N - 1 lies in the zone for every K once N is large. So the criterion forces nu_+(N-1) = o(T_+(N)). Check passes.
- Regular case (3), re-derived. Write n = floor(L_k), r = nu_+(n) + T_+(n), j = N - k >= 1. The map d -> m = N - d sends |d - L_k| to |m - j/(1-p)| exactly, because N - L_k = j/(1-p). Lemma lem:green-conc at (N, j) puts all but eps of the Green mass sum_m Pi^-_m(j) on the window V = {d : |d - L_k| <= R B_N}. On V, |d - n| <= R B_N + 1 <= delta n once K >= R(1-p)/delta + 2 and N is large, and d >= L_k/2 once K >= 2R(1-p), which holds for delta <= 1/2. The second part of (R nu) gives |nu_+(d) - nu_+(n)| <= eps r on V, and the first part gives nu_+(d) <= C_nu r for every d >= L_k/2 >= n/2. Hence |Psi_N(k) - nu_+(n)(1 + mu_+ u_-(j))| <= (C_nu + 2 + mu_+) eps r. Since T_+(n) <= Ghat_N(k), this is eps times a constant times Ghat_N(k) + nu_+(floor L_k). At k = N both Psi and the replacement vanish. This matches the author's argument line by line.
- On the whole zone up to the end. At k = N - j with j fixed, Lemma lem:green-conc is used with j fixed and 1 <= j <= N, which it covers, and the window V sits within R B_N of L_k = N - js/mu_-. The (R nu) step then compares nu_+ at floor(L_k) with nu_+ at nearby d, not with nu_+(N); the comparison with nu_+(N) is only in the remark after the theorem and is a second application of (R nu) with |floor(L_k) - N| = O(1). Both are legitimate.

Uniformity over the family. The constants K_0, n_0, C_*, C_G, r_N, c_9, c_10, R, N_0 are fresh-start or law-only quantities. The family enters through eps_J, through pi_+, nu_- in kappa_+, and through (R nu), which the statement requires uniformly in N. The proof uses (R nu) at n = floor(L_k), a value that depends on N, so the uniform requirement is necessary and is exactly what is assumed.

One implicit choice. In the regular case the proof takes delta from (R nu) and needs delta <= 1/2 for the inequality d >= L_k/2 on V. The second part of (R nu) is monotone in delta, so any admissible delta can be shrunk. This is not a gap.

Verdict: proved as written.

## Claim 1d. Theorem thm:preparation(d), the boundary layer

Claim card. For fixed j >= 0, P_N(N-j) = Q_+(N) 1_{j=0} + T_+(N) kappa_+(j) + B_N^{-1} D^+_N(j) + o(T_+(N)) for families under eq:tight and (RV) for the plus sign; the defect criteria; the fixed-law reading; and the regular case B_N^{-1} D^+_N(j) = nu_+(N)(1 + mu_+ u_-(j)) + o(nu_+(N) + T_+(N)).

Independent derivation. The first-run decomposition at k = N - j has three parts. A first minus run of length d contributes only for d <= j, and then the fresh plus walk on N - d steps has j - d minus steps, so Theorem thm:bigjump(a) gives T_+(N)(u_-(j-d) + o(1)); the sum has at most j terms. A first plus run of length d <= J contributes T_+(N)(u_-(j) 1_{j>=1} + o(1)) times its weight. For J < d <= N/2 the ratio F^-_n(n-j)/T_+(n) is a convergent sequence in n, hence bounded, and T_+(n) <= C T_+(N) for n >= N/2. For N/2 < d < N the contribution is exactly B_N^{-1} D^+_N(j). The three parts assemble into kappa_+(j) with error (1 + C C_j) eps_J, then J -> infinity.

Criteria. Sufficiency uses Lemma lem:green as in (b). Necessity: the Green weights Pi^-_m(j) have total mass at least 1, so some m_0 = m_0(j) has positive weight, and the single term m = m_0 gives nu_+(N - m_0) Pi^-_{m_0}(j) <= B_N^{-1} D^+_N(j). This is honest for families: it yields nu_+(N - m_0) = o(T_+(N)) and nothing more. For a fixed law T_+(N)/T_+(N - m_0) -> 1 recovers nu_+(n) = o(T_+(n)).

Regular case, re-derived. Split the Green sum at M and at N/2. For m <= M, (R nu) second part at n = N and |d - N| = m <= M <= delta N gives |nu_+(N-m) - nu_+(N)| <= eps_N r_N with eps_N -> 0 (take delta -> 0 after N -> infinity). For M < m < N/2, the first part gives nu_+(N-m) <= C_nu r_N. The tail sum_{m >= N/2} Pi^-_m(j) tends to zero for fixed j. Letting N -> infinity then M -> infinity gives o(r_N). This is the author's argument.

Verdict: proved as written.

## Claim 1e. Theorem thm:preparation(e), the interior of the big-jump zone

Claim card. On Z^eps_N, eq:interior-target holds if nubar_+(n) = o(T_+(n)); eq:interior-target implies W^{(2n)}_n = o(T_+(n)); under (LR) for both signs, sup_{eps N/4 <= n <= N} W^{(N)}_n = o(T_+(N)) for every eps implies eq:interior-target.

Independent derivation.

- Reduction. Z^eps_N lies in the zone of (c) for every K once N is large and excludes k = N. On Z^eps_N, T_+(N) <= Ghat_N(k) <= eps^{-1} T_+(floor(eps N)) <= C_eps T_+(N). So eq:interior-target is equivalent to sup_{Z^eps_N} Psi_N = o(T_+(N)).
- Necessity. With N = 2n and |L_k - n| <= 1/(1-p), the terms d with |d - n| <= B_n have m = N - d in [N/4, 3N/4] and |(m - j) - pm| = (1 - p)|L_k - d| <= 2(1-p) B_n <= c_11 B_m. Theorem thm:bulk(c) with Lemma lem:profile(d) gives B_m Pi^-_m(j) >= c_12. Also d >= L_k/2 and d <= N - 1 for large n, so these d are terms of Psi_N(k). Hence Psi_N(k) >= (c_12/C) W^{(2n)}_n. Check passes, and the conclusion names the law at the horizon 2n, which is the honest family statement.
- Sufficiency. The near blocks |i| <= R use Theorem thm:bulk(b) and the covering of each block by C_eps windows. The far blocks use eq:far-bound, whose four terms I re-summed: the first is at most C t^{-alpha_+ - 1} by eq:NT-bounds and (B_N/b_{+,N})^{-alpha_+} <= 1; the second sums to at most 1/(c c_*); the third is C(N + 2 B_N) e^{-((1-p) eps N)^c}; the fourth is at most C N T_+(B_N) t^{-1 - alpha_+ + delta'} by Potter and N T_+(b_{+,N}) -> s. All sums converge. Checks pass.

Input. eq:far-bound is derived in `sec_preparation.tex` from eq:giant-split, eq:giant-crude (Lemma lem:giant) and Lemma lem:no-giant at eta = 1/32, r = 2, with the inclusion {M_m < g} subset of {M_m < eta L} for g = ceil(L/32). The reading of those lemmas is consistent with their statements, but their proofs are outside this audit.

Verdict: proved as written, conditional on Lemma lem:giant and Lemma lem:no-giant in `sec_bigjump.tex`.

## Claim 2a. Lemma lem:aged-nu

Claim card. For the aged family eq:aged-nu with arbitrary t_a = t_a(N) >= 0: (a) nu^{(t_a)}_sigma(d) <= T_sigma(d), the atom is at most sum_{i>=N} T_sigma(i), eq:tight holds, nubar_sigma <= T_sigma; (b) nu^{(t_a)}_+(d) = s^{-1}[T_+(d) - T_+(d + t_a + 1)] + o(T_+(d)) uniformly in t_a as d -> infinity, and (R nu) holds uniformly in t_a; (c) for t_a -> infinity, nu -> T/s pointwise, pi_+ -> p, and Q^{(t_a)}_+(N) = (1 + o(1)) s^{-1} sum_{i=N}^{N+t_a} T_+(i).

Independent derivation of (b), done before reading the proof. Write a_t = 1/s + eta_t, eta_t -> 0, |eta_t| <= 1. The main part is s^{-1} sum_{i=d}^{t_a+d} f_+(i) = s^{-1}[T_+(d) - T_+(d + t_a + 1)]. The error is sum_{t<=t_a} eta_t f_+(t_a - t + d). Split at M = M(d) -> infinity, M = o(d). The part t >= M is at most sup_{t>=M}|eta_t| T_+(d), uniformly in t_a (empty when t_a < M). The part t < M is at most sum of f_+ over an interval of M consecutive integers starting at a >= d - M + 1 >= d/2, which equals T_+(a) - T_+(a + M) = o(T_+(a)) = o(T_+(d)) by Lemma lem:rv(i), uniformly in t_a. This is the author's argument. The case t_a < M - 1, where the sum has fewer than M terms, is covered because the interval [a, a + M - 1] still contains all the arguments.

Scale-N continuity (the second part of (R nu)), re-derived. For |d - n| <= delta n with delta <= 1/2: nu(d) - nu(n) = s^{-1}[T_+(d) - T_+(n)] - s^{-1}[T_+(d + t_a + 1) - T_+(n + t_a + 1)] + o(T_+(n)). The first bracket is at most eps(delta, n) T_+(n) by Lemma lem:rv(i), since |d/n - 1| <= delta. For the shifted pair D' = d + t_a + 1, N' = n + t_a + 1 we have |D'/N' - 1| = |d - n|/N' <= delta and N' >= n, so the second bracket is at most eps(delta, n) T_+(N') <= eps(delta, n) T_+(n). The o(T_+(n)) collects the two o(T_+(.)) errors of the expansion, using T_+(d) <= C T_+(n) for d >= n/2. None of the bounds depends on t_a. So lim_delta limsup_n sup_{t_a} sup_{|d-n|<=delta n} |nu(d) - nu(n)|/(nu(n) + T_+(n)) = 0. The first part of (R nu) holds with C_nu = C of Lemma lem:rv(ii) because nu(d) <= T_+(d) <= C T_+(n) for d >= n/2.

Check of (a) and (c). (a) is a_t <= 1 and a telescoping sum. (c) is dominated convergence with the summable dominant f_+(m + d), and for the atom the bound Sigma_N >= min(t_a, N) T_+(2N) >= c min(t_a, N) T_+(N) makes the M terms with small coefficient index negligible when M = o(min(t_a, N)); the rest have coefficient 1/s + o(1). Checks pass. The derivation of eq:aged-sums from Lemma lem:rv(i) and (iv) checks in all three regimes.

Numerical check. For f_+ = f_- proportional to n^{-2.5}, a plus start, and t_a in {0, 1, 5, 20, 100, 300, 1000, 2000}: sup_{t_a} |nu(d) - main(d)|/T_+(d) is 0.054, 0.015, 0.0068, 0.0033 at d = 20, 100, 400, 1500, and the (R nu) ratio sup_{t_a} sup_{|d-n|<=delta n} |nu(d) - nu(n)|/(nu(n) + T_+(n)) is about 0.084, 0.036, 0.017, 0.0065 at delta = 0.2, 0.1, 0.05, 0.02, stable in n from 100 to 1500. Script: `C:\Users\arjun\AppData\Local\Temp\claude\C--Users-arjun-OneDrive-Documents-GitHub-Kagey-Problems\e83977a0-ccde-43be-ab6b-f724eaf1ba6e\scratchpad\aged_nu_check.py`. This is a sanity check, not evidence for the proof.

Verdict: proved as written.

## Claim 2b. Theorem thm:aging

Claim card. (a) For every t_a(N), sup_{1<=k<N}|B_N P^{(t_a)}_N(k) - h_N(x_{N,k})| -> 0. (b) For t_a -> infinity with t_a/N -> theta, P^{(t_a)}_N(N) = Q^{(t_a)}_+(N) ~ s^{-1} sum_{i=N}^{N+t_a} T_+(i), evaluated by eq:aged-sums. (c) For every t_a(N), in the double limit over the zone with k < N, P^{(t_a)}_N(k) = G^{(t_a)}_N(k) + o(Ghat_N(k)), with the consequences (i) and (ii) when t_a -> infinity.

Check of the identification. The run in progress at step t_a + 1 has sign Sigma and remaining length D; later runs are independent of the past and alternate. A plus run that starts at step t + 1 <= t_a + 1 covers step t_a + 1 with d remaining steps exactly when its length is t_a - t + d, and the events over t are disjoint. So eq:aged-nu is the law of the initial run and P^{(t_a)}_N is P_N of Section prep-statements. Check passes.

(a). Lemma lem:aged-nu(a) gives eq:tight and B_N nubar(N/2) <= B_N(T_+(N/2) + T_-(N/2)) -> 0 by Lemma lem:rv(ii), (v). Theorem thm:preparation(b), interior form, concludes. Check passes.

(b). Proposition prop:first-run gives P_N(N) = Q_+(N), and Lemma lem:aged-nu(c) with eq:aged-sums gives the asymptotics. Check passes.

(c). Lemma lem:aged-nu(b) gives (R nu) uniformly in t_a, hence uniformly in N for the family indexed by t_a(N), which is what the regular case of Theorem thm:preparation(c) requires. That case gives, on the zone with k < N and in the double limit, P_N(k) = G^nu_N(k) + nu_+(floor L_k)(1 + mu_+ u_-(j)) + o(Ghat_N(k) + nu_+(floor L_k)), and nu_+(floor L_k) <= T_+(floor L_k) <= Ghat_N(k) turns the error into o(Ghat_N(k)). Since L_k >= K B_N/(1-p) -> infinity uniformly on the zone, Lemma lem:aged-nu(b) replaces nu_+(floor L_k) by s^{-1}[T_+(floor L_k) - T_+(floor L_k + t_a + 1)] + o(T_+(floor L_k)), and f_+(floor L_k + t_a) = o(T_+(floor L_k + t_a)) <= o(T_+(floor L_k)) under (RV) moves the shift from t_a + 1 to t_a. This is eq:aged-kernel. Check passes. At t_a = 0 with a plus start, kappa^{(0)}_+ = u_- on j >= 1 and the extra term vanishes, so the display reduces to Theorem thm:bigjump(b) for Gbar, as it should.

(i). For fixed j >= 1 and k = N - j, in the zone for every K: Ghat_N(k) ~ T_+(N), (N - L_k) f_+(floor L_k) = O(T_+(N)/N), T_+(floor L_k)/T_+(N) -> 1, kappa^{(t_a)}_+(j) -> p u_-(j) + s^{-1} sum_{d=1}^j T_-(d) u_-(j-d) = p u_-(j) + 1/s by Lemma lem:aged-nu(c) and eq:cover, and T_+(floor L_k + t_a)/T_+(N) -> (1 + theta)^{-alpha_+} (zero at theta = infinity, by Potter). Dividing eq:aged-kernel by T_+(N) gives kappa^{(theta)}_+(j). At theta = infinity this is (2/s)(1 + mu_+ u_-(j)), the stationary kernel of Corollary cor:stationary(c); at theta = 0 it is p u_-(j) + 1/s. Checks pass.

(ii). The claim kappa^{(t_a)}_+(j) -> 1/mu_- uniformly in t_a as j -> infinity: split at J, use u_-(j - d) -> 1/mu_- for d <= J, the tightness eps_J for d > J and for the weight defect, and pi_+ + pi_- = 1. The bound 2 eps_J + o(1) is independent of t_a. Then 1 + mu_+ u_-(j) -> s/mu_-, and on Z^eps_N both T_+(floor L_k) and Ghat_N(k) are at most C_eps T_+(N). The expansion follows with [2T_+(floor L_k) - T_+(floor L_k + t_a)]/mu_-. For k = floor(vN), the three limits give I_+(v) + [l^{-alpha_+} - (l + theta)^{-alpha_+}]/mu_-, which at theta = infinity is the stationary value of Corollary cor:stationary(b) and at theta = 0 is I_+(v). Checks pass.

Verdict: proved as written.

## Claim 2c. Corollary cor:aged-mode

Claim card. Under (RV), (SPAN), a fresh start and t_a/N -> theta in (0, infinity], the endpoint of sign sigma beats the interior when alpha_sigma - 1 < 1/alpha_* and loses when alpha_sigma - 1 > 1/alpha_*; the golden ratio threshold for equal indices; the explicit constant for pure power laws with the factor 1 - (1 + theta)^{1 - alpha}.

Check. Theorem thm:aging(a) is eq:mode-interior for the aged law, and the proofs of Theorem thm:mode(a) and (b) use the initial run only through that display, so P^max_N = (H_N + o(1))/B_N holds for the aged law. For theta in (0, infinity], t_a -> infinity, so Theorem thm:aging(b) and eq:aged-sums give P^{(t_a)}_N(N) ~ c_theta N T_+(N) with c_theta in (0, infinity), a regularly varying function of index 1 - alpha_+. With B_N in RV_{1/alpha_*} and H_N bounded above and below, B_N P^{(t_a)}_N(N)/H_N tends to infinity or zero according to the sign of 1/alpha_* - (alpha_+ - 1). The "beats" case is Theorem thm:mode(b), first sentence. The "loses" case follows from Theorem thm:mode(a) alone: B_N P^max_N - B_N P^{(t_a)}_N(N) = H_N + o(1) - o(1) >= h_*/2. For equal indices alpha - 1 < 1/alpha iff alpha < phi. For T_+ = T_- = n^{-alpha} the two atoms are equal and the computation of Theorem thm:mode(d) applies with the atom multiplied by 1 - (1 + theta)^{1 - alpha} < 1, so at alpha = phi the ratio tends to a value below C(phi) < 1 and the mode is interior for every finite theta, and at theta = infinity by Theorem thm:mode(d) itself. Checks pass.

Verdict: proved as written.

## Claim 3. Remark rem:uniform-layer

Claim card. Under the hypotheses of Theorem thm:bigjump(b), for every delta_N -> 0, sup_{0<=j<=delta_N N} |P_N(N-j)/T_+(N) - kappa(j)| -> 0, and the ratio P_N(N-j)/(T_+(N) kappa(j)) -> 1 uniformly over the same j with kappa(j) > 0.

Independent derivation. For j <= delta_N N and k = N - j: k - pN >= (1 - p)N/2 for large N, and lambda_N B_N = o(N), so for each K the set {N - j : j <= delta_N N} lies in the zone of (b) once N >= N_K. Hence limsup_N sup_{j<=delta_N N} |P_N - G_N|/Ghat_N is at most limsup_N sup_{zone(K)} for every K, which tends to zero as K -> infinity, so the limsup is zero. Next, L_k = N - js/mu_- >= N(1 - delta_N s/mu_-), so floor(L_k)/N -> 1 uniformly in j, and Lemma lem:rv(i) gives T_+(floor L_k)/T_+(N) -> 1 and Ghat_N(N-j)/T_+(N) -> 1 uniformly. The complete-run term is gamma(j) f_+(floor L_k) <= (1 + mu_+) delta_N N C T_+(N)/N = O(delta_N) T_+(N). So |P_N(N-j) - kappa(j) T_+(N)| <= o(Ghat) + O(delta_N) T_+(N) + kappa(j)|T_+(floor L_k) - T_+(N)| = o(T_+(N)) uniformly. For the ratio form, kappa(j) -> 1/mu_- > 0 by eq:renewal-thm and eq:kappa, so inf{kappa(j) : kappa(j) > 0} > 0, and the additive statement divides through. At j = 0 the additive statement is exact: P_N(N) = T_+(N) = kappa(0) T_+(N) for a plus start and 0 = 0 for a minus start.

Check of the author's argument. It is this argument. The parenthetical "a condition that excludes nothing but j = 0 for a minus start when f_-(1) > 0" is correct as parsed: for a plus start kappa(j) = u_-(j) > 0 for all j >= 0 when f_-(1) > 0, and for a minus start kappa(j) = u_-(j) 1_{j>=1} vanishes only at j = 0. When f_-(1) = 0 more j are excluded, which the sentence does not claim otherwise.

Verdict: proved as written.

## Cosmetic findings (no effect on any proof)

1. `sec_aging.tex`, paragraph before Lemma lem:aged-nu: "a_t is a renewal sequence and b_t = sum_{t'<t} a_{t'} f_+(t - t')" describes a plus start. For a minus start, b_t is the renewal sequence and a_t the delayed one. The proofs use only a_t <= 1 and a_t -> 1/s, which hold for both starts by dominated convergence, so eq:aged-renewal stands as written. A phrase such as "for a plus start, and with the roles exchanged for a minus start" would remove the ambiguity.
2. `sec_aging.tex`, proof of Lemma lem:aged-nu(b): "which is at most delta times the smaller of them" is false when d < n (then |d - n| <= delta d/(1 - delta)), but Lemma lem:rv(i) needs only |x/y - 1| <= delta, which holds for both pairs. The bound is right; the justification could say that directly.
3. `sec_preparation.tex`, regular case of (c): the proof needs delta <= 1/2 for "every d in V has d >= L_k/2". Since the second part of (R nu) is monotone in delta, this is available. A clause "with delta <= 1/2" would close it on the page.
4. `sec_aging.tex`, proof of Corollary cor:aged-mode: "part (b) of Theorem thm:mode concludes" covers the "beats" case; the "loses" case for one endpoint follows from Theorem thm:mode(a) rather than the two-sided second sentence of (b). The same citation habit is in the proof of Theorem thm:mode(c). Harmless.
5. `sec_preparation.tex`, proof of (e), near blocks: the count "(2R + 2)" could be "(2R + 1)" blocks with |i| <= R. Harmless.

## Smallest open implications

None of the audited claims has a missing implication. The only external dependency not on the given list is eq:far-bound in the proof of (e), which rests on Lemma lem:giant and Lemma lem:no-giant from `sec_bigjump.tex`. If those two lemmas are sound, (e) is proved; nothing in (a) through (d), in the aging section, or in Remark rem:uniform-layer depends on them.
