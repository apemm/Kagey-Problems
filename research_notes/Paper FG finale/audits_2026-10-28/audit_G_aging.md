# Audit of Paper G, Section `sec_aging.tex` and Lemma `lem:E`

Files audited: `kagey-problems/problem131/paperG/sec_aging.tex` (whole section) and
`sec_ends.tex` (Lemma `lem:E`, Section `sec:lemE`). Notation and hypotheses from
`sec_setting.tex`; cited lemmas from `sec_tools.tex` taken as given with their stated
hypotheses; Theorems `thm:local`, `thm:ends`, `thm:initial` taken as given.

Method. For each claim: restate, re-derive the critical step from the definitions
before reading the author's argument, then check every implication of the argument.
Numerical checks were run with mpmath (script in the session scratchpad, not in the repo);
they are quoted only where a claim is a closed form or an inequality between constants.

Verdict scale: proved as written / correct only after a stated restriction / conditional
on a named input / incomplete, with the smallest missing implication / refuted, with a
counterexample.

---

## 1. Lemma `lem:E` (the end layer from above)

**Claim card.** (BAL), (SPAN), and one of: alpha > 1/2; alpha < 1/2 and (SRT_pm);
alpha = 1/2, (SRT_pm), and n T_+(n)^2 bounded above and away from 0. Then there is C with
F^-_n(i) <= C T_+(n) omega_+(i) and F^+_n(n-i) <= C T_+(n) omega_-(i) for all n >= 1,
0 <= i <= n/2.

**Independent derivation.** i = 0: F^-_n(0) = T_-(n) <= C T_+(n), omega(0) = 1. For
i >= 1, j = n - i >= n/2 >= 1, the fresh-minus identity (sign exchange of (eq:fresh),
checked) gives F^-_n(i) = sum_m u^+_m(i) q^-_{m+1}(j) + sum_m u^-_m(j) q^+_m(i).

First sum: key bound q^-_{m+1}(j) <= C T_-(j) <= C T_-(n/2) <= C T_+(n) (R2, BAL);
sum_{m>=1} u^+_m(i) = u_+(i) for i >= 1; (SRT_+) gives u_+(i) <= C omega_+(i). For
alpha > 1/2 (SRT_+) is Lemma cd(iii), first sentence, under (RV)+(SPAN).

Second sum, alpha > 1/2: Lemma cd(ii) for the minus sign gives
u^-_m(j) <= C (m/a_-(m)) T_-(j) <= C T_+(n) m/a_m (a_- and a_+ comparable under BAL).
Lemma decay gives q^+_m(i) <= C T_+(i) e^{-c m T_+(i)}. With M = 1/T_+(i) and
phi(m) = m/a_m regularly varying with index 1 - 1/alpha in (-1, 0):
sum_{m<=M} phi(m) <= C M phi(M) by Karamata and the dyadic blocks above M decay
geometrically by Potter, so the sum is <= C M^2/a_M. Since T_+(a_M)/T_+(i) -> 1, (R1) and
Potter force a_M/i -> 1, so a_M asymp i (bounded i absorbed in C). The second sum is
<= C T_+(n) T_+(i) M^2/a_M = C T_+(n)/(i T_+(i)) <= C T_+(n) omega_+(i), the last step
because inf_i i T_+(i) > 0.

Second sum, alpha < 1/2: e^{-cmT} <= 1 gives <= C T_+(i) u_-(j) <= C T_+(i)/(n T_+(n)) by
(SRT_-), (R1), (R2). The needed inequality T_+(i)/(nT_+(n)) <= C T_+(n)/(iT_+(i)) is
i T_+(i)^2 <= C n T_+(n)^2 for i <= n, which holds because x T_+(x)^2 is regularly varying
with positive index 1 - 2alpha (BGT Theorem 1.5.3: sup_{t<=x} psi(t) ~ psi(x)), with
finitely many small n absorbed. At alpha = 1/2 the same inequality is exactly the stated
boundedness of n T_+(n)^2 above and away from zero.

**Check of the author's argument.** Identical to the above at every step. The mirror
statement exchanges the signs; the alpha = 1/2 hypothesis on n T_+(n)^2 is equivalent to
the same for T_- under (BAL), so the mirror needs no new hypothesis.

**Verdict: proved as written.**

---

## 2. Lemma `lem:count` and Corollary `cor:count`

### Lemma `lem:count`

**Claim card.** Fresh minus walk, n_0 >= 1, I >= 0, m_0 >= 1:
sum_{i=0}^I F^-_{n_0+i}(i) <= C m_0 T_-(n_0) + e^{-m_0 T_+(I+1)} + u_-(n_0) sum_{n=1}^I T_+(n),
C the constant of Lemma sums(i); needs only (RV).

**Independent derivation.** F^-_{n_0+i}(i) = P(C_{n_0+i} = n_0) (i plus steps among
n_0 + i steps means n_0 minus steps). Tonelli: the left side is the expected size of
{m in [n_0, n_0+I] : C_m = n_0} = [t_{n_0}, t_{n_0+1}) cap [n_0, n_0+I]. Since
t_{n_0} >= n_0, the size is 0 if t_{n_0} > n_0 + I and otherwise
<= 1 + min(t_{n_0+1} - t_{n_0} - 1, I). The gap t_{n_0+1} - t_{n_0} - 1 is 0 unless the
n_0-th minus step ends the r-th minus run (S^-_r = n_0), in which case it is X^+_r, the
r-th plus run of the fresh minus walk, independent of {S^-_r = n_0}. Expectation:
P(t_{n_0} - n_0 <= I) + sum_{r>=1} u^-_r(n_0) E min(X_+, I)
= P(t_{n_0} - n_0 <= I) + u_-(n_0) sum_{n=1}^I T_+(n) (n_0 >= 1 so the r = 0 term is
absent). The n_0-th minus step lies in minus run J = min{r : S^-_r >= n_0}; before it there
are J - 1 complete plus runs, so t_{n_0} - n_0 = S^+_{J-1}, J measurable in the minus runs.
{J - 1 < m_0} = {S^-_{m_0} >= n_0}, probability <= C m_0 T_-(n_0) (sums(i)). On
{J - 1 >= m_0}, S^+_{J-1} >= S^+_{m_0}, and by independence
P(S^+_{m_0} <= I) = P(S^+_{m_0} < I + 1) <= (1 - T_+(I+1))^{m_0} <= e^{-m_0 T_+(I+1)}
(sums(ii)).

**Check of the author's argument.** Identical. Lemma sums(i),(ii) use only (RV) of the
sign concerned (the preamble of Lemma sums lists (SPAN), but (i) and (ii) do not use it),
so "needs only (RV)" is right.

**Verdict: proved as written.**

### Corollary `cor:count`

**Claim card.** (BAL) and u_- <= C omega_-. Fix c, delta in (0,1). For n_0 >= cN and all
large N, sum_{i<=delta N} F^-_{n_0+i}(i) <= zeta(delta) :=
C_c (delta^{alpha/4} + e^{-delta^{-alpha/4}} + delta^{(1-alpha)/2}).

**Independent derivation.** I = floor(delta N), m_0 = ceil(eta/T_+(N)), eta = delta^{alpha/4}.
Term 1: m_0 T_-(n_0) <= eta T_-(n_0)/T_+(N) + T_-(n_0) <= C_c (eta + T_+(N)), and
T_+(N) <= eta for large N. Term 2: m_0 T_+(I+1) >= eta T_+(delta N + 1)/T_+(N)
-> eta delta^{-alpha} >= eta delta^{-alpha/2} = delta^{-alpha/4} for large N. Term 3:
u_-(n_0) <= C/(n_0 T_-(n_0)) <= C_c/(N T_+(N)) because x T_-(x) has positive index
(Potter lower bound for n_0 >= cN); sum_{n<=delta N} T_+(n) <= C delta N T_+(delta N)
(R3), and the Potter upper bound T_+(delta N)/T_+(N) <= 2 delta^{-(1+alpha)/2} gives
<= C delta^{(1-alpha)/2} N T_+(N).

**Check of the author's argument.** Identical. One presentational point: the step
delta T(delta N) <= C delta^{(1-alpha)/2} T(N) is attributed to "(R2)", but (R2) as stated
has an unspecified constant C_{1/delta}; the explicit power needs Potter's theorem, which
the paper has (it is used for (R4)). "Large N" depends on delta and c, which is how the
corollary is used.

**Verdict: proved as written** (with Potter's theorem in place of (R2) at one step).

**Side remark on the paragraph after Theorem `thm:mixture`.** The sentence "the sum of
these bounds over i <= delta N is of order T(N)/T(delta N), which is not small" is wrong:
sum_{i<=delta N} omega(i) <= C/T(delta N) by (R3), and T(N)/T(delta N) -> delta^alpha,
which is small as delta -> 0. Under (H2) the pointwise bound of Lemma `lem:E` would
control range 3 of the proof of Theorem `thm:mixture` for alpha != 1/2 (giving
C_eps delta^{alpha - eps'}/N). What the counting bound actually buys is independence from
(LB) and from the alpha = 1/2 restriction of Lemma `lem:E`. The claim is not in the audit
list but the stated reason should be corrected.

---

## 3. Theorem `thm:mixture`

**Claim card.** (BAL), (SPAN), (SRT_pm), and the initial law satisfies (H0), (H1), (H2).
Then N P_N(floor(xN)) -> mathcal L(x) of (eq:mixture) uniformly on compact subsets of (0,1).

**Independent derivation of the critical steps.**

Decomposition: for interior k the atoms vanish, and
P_N(k) = sum_{d<=k} nu_+(d) F^-_{N-d}(k-d) + sum_{d<=j} nu_-(d) F^+_{N-d}(k), j = N - k,
since F^-_{N-d}(k-d) = 0 for d > k (and F^-_{N-k}(0) = T_-(N-k) is kept at d = k).

Choice of parameters: 0 < delta < eps < min(x_1, 1-x_2)/4. Range 1 (d < eps N):
(k-d)/(N-d) in [(3/4) x_1, x_2], a compact subset of (0,1), and
|(k-d)/(N-d) - k/N| = d(N-k)/(N(N-d)) <= eps/(1-eps) <= 2 eps. Theorem local(ii) for the
fresh minus walk, N/(N-d) = 1 + O(eps), and Lambda Lipschitz on compacts give
N F^-_{N-d}(k-d) = Lambda(x) + O(eps) + o(1) uniformly in d. Range 2
(eps N <= d <= k - delta N): the ratio is in [delta, (x_2 - eps)/(1 - eps)] (it is
decreasing in d), the horizon is >= (1 - x_2) N, so N F^-_{N-d}(k-d) = g_x(d/N) + o(1)
uniformly and N F^- <= C. Range 3 (k - delta N < d <= k): d in [eps N, (1 - eps) N]
because x_1 - delta > 3x_1/4 > eps and x_2 < 1 - eps; (H2) gives N nu_+(d) <= C_eps, and
Corollary count with n_0 = j >= (1 - x_2) N (its hypothesis u_- <= C omega_- is the upper
half of (SRT_-)) gives the contribution <= C_eps zeta(delta)/N. The three ranges cover
d <= k. Minus side: mirror, with n_0 = k >= x_1 N and the mirror corollary under (SRT_+).

Range 1 for both signs adds to P(D < eps N)[Lambda(x) + O(eps) + o(1)]/N because the
leading term Lambda(x) does not depend on the sign; this is why (H0) needs only the total
mass near 0.

Limits: N -> infinity, then delta -> 0 (zeta(delta) -> 0; the integrals extend to z = x
and z = 1 - x since g_x(z) <= C ((x-z)/(1-z))^{alpha-1} <= C (x-z)^{alpha-1} and rho_pm
is bounded on compacts of (0,1)), then eps -> 0 (O(eps) -> 0; the integrals extend to
z = 0 since g_x is bounded near z = 0 and rho_pm is integrable near 0, as a vague limit of
sub-probability measures has total mass <= 1).

Uniformity in x of the range-2 convergence: the test functions
g_x 1_{[eps, x - delta]} are uniformly bounded, equicontinuous in x away from the moving
endpoint z = x - delta, and the N-measures of any interval of length h in the compact
[eps, x_2 - delta] are at most C h + o(1) by vague convergence to a measure with a
locally bounded density (a finite grid of mesh h). A finite net in x then gives uniform
convergence. (H2) is not needed for this, which matters for the reuse of ranges 1 and 2 in
Theorem aging(a).

**Check of the author's argument.** Identical in structure and in every numerical
choice. Range 2's "uniformly in x" is asserted with the words "with a limit measure that
has a density" and "equicontinuous"; the argument above fills it and it is routine.
(H0) as stated presupposes that lim_N P(D^{(N)} < eps N) exists for small eps; the proof
uses that reading. The theorem statement and proof are consistent with it.

**Verdict: proved as written.**

---

## 4. Lemma `lem:DL`, the closed forms, and c_+(1) = 1/(2 sqrt 2)

**Claim card.** (BAL). For every r > 0, P(Sigma = sigma, D >= rN) -> int_r^infty rho_sigma,
with rho_sigma(z) = p_sigma (sin pi alpha/pi) theta^alpha z^{-alpha}/(theta + z);
P(Sigma = sigma) -> p_sigma; lim_eps lim_N P(D < eps N) = 0. Hence (H0) with pi^0 = 0 and
(H1).

**Independent derivation.** The formula (eq:aged-law) is checked from the definitions:
for a fresh plus start, plus runs start at steps 1 + S^+_m + S^-_m (renewal mass function
u_c of f_+ * f_-), minus runs at steps 1 + S^+_{m+1} + S^-_m (v_c = f_+ * u_c); a run
starting at s + 1 <= t_a + 1 with length l straddles t_a + 1 iff l >= t_a - s + 1, and then
D = s + l - t_a. So P(Sigma = +, D >= rN) = sum_{s<=t_a} u_c(s) T_+(t_a - s + rN).

T_c(n) ~ (1 + b) T_+(n) (independent summands with regularly varying tails of the same
index). Karamata's Tauberian theorem: U_c(n) T_c(n) -> 1/(Gamma(1+alpha)Gamma(1-alpha))
= sin(pi alpha)/(pi alpha). Then U_c(N dy)/U_c(N) -> d(y^alpha) vaguely on [0, infinity)
(the atom of U_c at 0 has relative mass 1/U_c(N) -> 0), and
T_+(N(t_a/N - y + r))/T_+(N) -> (theta + r - y)^{-alpha} uniformly for y in [0, theta]
by (R1) since the argument stays in a compact subset of (0, infinity). The sum is a
weak-convergence integral with U_c(N) T_+(N) -> (sin pi alpha/(pi alpha)) p_+, so
P(Sigma = +, D >= rN) -> (sin pi alpha/pi) p_+ int_0^theta y^{alpha-1}(theta + r - y)^{-alpha} dy.

Density: -d/dr of this is (sin pi alpha/pi) p_+ alpha int_0^theta y^{alpha-1}
(theta + r - y)^{-alpha-1} dy. With v = y/(theta + r - y): y^{alpha-1}
(theta + r - y)^{-alpha-1} dy = (theta + r)^{-1} v^{alpha-1} dv (checked: the powers of
(theta + r) add to -1 and those of (1 + v) to 0), upper limit v = theta/r, so the integral
is theta^alpha/(alpha r^alpha (theta + r)), and the density is rho_+(r) as stated.
Convergence of the distribution functions at every r gives vague convergence on (0,1) to
rho_+ dz.

Mass: int_0^infty theta^alpha z^{-alpha}/(theta + z) dz = int_0^infty w^{-alpha}/(1 + w) dw
= B(1 - alpha, alpha) = pi/sin(pi alpha), so int rho_sigma = p_sigma and they add to 1.
Then liminf P(Sigma = sigma) >= int_r^infty rho_sigma for every r, the two liminfs add to
at least 1, so both limits exist and equal p_sigma; and
P(D < eps N) -> 1 - sum_sigma int_eps^infty rho_sigma -> 0 as eps -> 0.

Minus sign: V_c(n) = sum_i f_+(i) U_c(n - i) lies between (1 - T_+(eps n)) U_c((1 - eps) n)
and U_c(n), so V_c ~ U_c, and the factor becomes U_c(N) T_-(N) -> (sin pi alpha/(pi alpha)) p_-.
No (SPAN) is needed: the Tauberian theorem is about U_c(n), not u_c(n).

Closed forms. Q^infty_sigma: z = theta w, then u = 1/(1 + w) turns
int_{1/theta}^infty w^{-alpha}/(1 + w) dw into int_0^{theta/(1+theta)} u^{alpha-1}(1-u)^{-alpha} du
= B(theta/(1+theta); alpha, 1 - alpha). Checked symbolically and numerically (agreement to
quadrature precision at alpha in {0.3, 0.5, 0.7, 0.9}, theta in {0.01, ..., 10}).
c_sigma: Euler's integral int_0^1 t^{b-1}(1-t)^{c-b-1}(1 - tx)^{-a} dt = B(b, c-b) 2F1(a, b; c; x)
with a = 1, b = 1 - alpha, c = 2 - 2alpha, x = -1/theta, and (theta + z)^{-1}
= theta^{-1}(1 + z/theta)^{-1}, gives
c_sigma(theta) = p_sigma (sin pi alpha/pi) theta^{alpha-1} B(1-alpha, 1-alpha) 2F1(1, 1-alpha; 2-2alpha; -1/theta).
Checked numerically (alpha = 0.9, theta = 1: integral 0.713210 against closed form 0.713231
at 40 digits with the singularity removed by substitution; the residual is quadrature).

c_+(1) at alpha = 1/2, b = 1: p_+ = 1/2, sin(pi/2)/pi = 1/pi, B(1/2, 1/2) = pi,
2F1(1, 1/2; 1; -1) = (1 - (-1))^{-1/2} = 1/sqrt 2, so c_+(1) = 1/(2 sqrt 2). Also directly:
int_0^1 dz/((1 + z) sqrt(z(1 - z))) = pi/sqrt 2. Numerically 0.3535534 both ways. At
alpha = 1/2 the closed form collapses to c_+(theta) = p_+ (1 + theta)^{-1/2} for every theta.

**Check of the author's argument.** Identical. The remark that the straddling run's sign
is asymptotically independent of its length follows from rho_+/rho_- = p_+/p_- being
constant in z, which the derivation gives.

**Verdict: proved as written** (lemma, both closed forms, and the value 1/(2 sqrt 2)).

---

## 5. Lemma `lem:U` and Lemma `lem:aged-pointwise`

### Lemma `lem:U`

**Claim card.** (BAL), (SPAN). (U): u_c(n) <= C omega_+(n) and v_c(n) <= C omega_+(n)
holds under (LB_pm) for every alpha; with no further condition for alpha > 1/2; for
alpha <= 1/2 when f_c and f_+ satisfy the strong renewal theorem.

**Independent derivation.** Aperiodicity of f_c: if supp X_+ + supp X_- lay in c + hZ,
fixing one point of supp X_- would put supp X_+ in a progression, against (SPAN). Under
(LB_pm), splitting f_c(n) = sum_i f_+(i) f_-(n-i) at n/2 gives f_c(n) <= C T_c(n)/n,
Doney's theorem (Lemma cd(iii), last sentence) gives the SRT for f_c, so
u_c(n) <= C/(n T_c(n)) <= C omega_+(n). For alpha > 1/2 the SRT for f_c is automatic.

v_c(n) = sum_{i=1}^n f_+(i) u_c(n - i). Part i <= n/2: u_c(n-i) <= C omega_+(n) (R1 on
[n/2, n]), times sum f_+ <= 1. Part i > n/2, z = n - i:
f_+(n) + sum_{1<=z<n/2} f_+(n-z) u_c(z) with u_c(z) <= C omega_+(z) <= C/(z T_+(z)^2).
Under (LB_+): f_+(n - z) <= C T_+(n)/n for z < n/2, sum_z u_c(z) = U_c(n/2) <= C/T_+(n),
so this part is <= C/n <= C omega_+(n) (omega(n) >= 1/n). Without (LB_+):
S(n) := sum_{1<=z<n/2} f_+(n-z)/(z T_+(z)^2). For z <= delta' n this is the Caravenna-Doney
quantity, which is <= (zeta_CD(delta') + o(1))/(n T_+(n)) when f_+ satisfies the SRT and
alpha <= 1/2. For delta' n < z < n/2: 1/(z T_+(z)^2) <= C_{delta'}/(n T_+(n)^2) and
sum_z f_+(n - z) <= T_+(n/2) <= C T_+(n), so this part is <= C_{delta'}/(n T_+(n)). For
alpha > 1/2 the whole sum is handled by the second argument alone, since 1/(z T(z)^2) has
positive index 2alpha - 1 and is bounded on z <= n/2 by C/(n T(n)^2). So S(n) = O(1/(n T_+(n)))
in every branch. Finally f_+(n) <= C omega_+(n): under (LB_+) from f_+ <= C T_+/n; for
alpha > 1/2 from f_+(n) <= T_+(n) <= 1/(n T_+(n)) eventually (n T_+(n)^2 -> 0); for
alpha <= 1/2 from the z = 1 term of the Caravenna-Doney condition,
n T_+(n) f_+(n - 1)/T_+(1)^2 -> 0, so f_+(n) = o(1/(n T_+(n))).

**Check of the author's argument.** The structure matches. One sentence is false: in the
"otherwise" branch the text closes with "f_+(n) <= T_+(n) <= omega_+(n) for large n". The
inequality T_+(n) <= omega_+(n) means n T_+(n)^2 <= 1, which fails for all large n when
alpha < 1/2 (n T_+(n)^2 is regularly varying with positive index 1 - 2alpha and tends to
infinity), and may fail at alpha = 1/2. The conclusion f_+(n) <= C omega_+(n) is still
true in that branch, by the z = 1 term of the Caravenna-Doney condition (the paper itself
uses exactly this in the proof of Theorem aging(a): "its term z = 1 gives
f_+(M) = o(1/(MT(M)))"). Second, the text calls S(n) "the quantity of Lemma cd(iii)" also
when alpha > 1/2, where Lemma cd(iii) states no such quantity; the bound there is the
elementary positive-index argument above, and the sum up to n/2 (not delta' n) needs the
extra step given above in every case. Neither point changes the statement.

**Verdict: proved as written for the statement; the proof contains one false sentence
(T_+(n) <= omega_+(n)) whose replacement is the z = 1 term of the Caravenna-Doney
condition, and the bound of S(n) over delta' n < z < n/2 is left to the reader.**

### Lemma `lem:aged-pointwise`

**Claim card.** (BAL), (SPAN), eps in (0,1). (a) Under (U), N nu^y_pm(d) <= C_{eps,theta}
for d >= eps N and large N. (b) Under (LB_pm), N nu_pm(d) <= C_{eps,theta} for d >= eps N
and large N.

**Independent derivation.** (a) For t_a/2 < s <= t_a, s T_+(s) >= c t_a T_+(t_a) >= c_theta N T_+(N)
by (R1), so u_c(s) <= C omega_+(s) <= C_theta/(N T_+(N)); sum_s f_+(t_a - s + d) runs over
distinct arguments >= d, so it is <= T_+(d) <= C_eps T_+(N) by (R2). Product <= C_{eps,theta}/N.
Minus sign: v_c <= C omega_+ and T_-(d) <= C T_+(d). (b) Old part s <= t_a/2: the argument
of f_+ is >= t_a/2 >= c_theta N, (LB_+) gives f_+(l) <= C T_+(l)/l <= C_theta T_+(N)/N
(negative-index regular variation of T(l)/l), and U_c(t_a/2) <= C/T_c(t_a/2) <= C_theta/T_+(N),
so the old part is <= C_theta/N with no condition on d. Young part by (a), since
(LB_pm) gives (U) by Lemma U.

**Check of the author's argument.** Identical.

**Verdict: proved as written.**

---

## 6. Theorem `thm:aging` (a), (b), (c)

### (b) The atoms

**Claim card.** (BAL). P_N(N) = Q_+(N) -> Q^infty_+(theta), P_N(0) -> Q^infty_-(theta).

Proposition first-run gives P_N(N) = Q_+(N) = P(Sigma = +, D >= N), which is Lemma DL at
r = 1 with int_1^infty rho_+ = Q^infty_+(theta) by definition (eq:aged-constants). Same at 0.

**Verdict: proved as written.**

### (a) The bulk

**Claim card.** (BAL), (SPAN), and one of: (LB_pm); alpha > 1/2; alpha < 1/2, (SRT_pm), (U);
alpha = 1/2, (SRT_pm), (U), n T_+(n)^2 bounded above and away from 0. Then
N P_N(floor(xN)) -> L_theta(x) uniformly on compacts of (0,1).

**Case (LB_pm).** Lemma DL gives (H0) with pi^0 = 0 and (H1); Lemma aged-pointwise(b) gives
(H2) (finitely many small N contribute N nu(d) <= N); (LB_pm) gives (SRT_pm). Theorem
mixture applies and its limit is L_theta. Correct.

**Other cases.** (SRT_pm) holds (Lemma cd(iii) for alpha > 1/2, assumption otherwise); (U)
holds (Lemma U for alpha > 1/2, assumption otherwise). Ranges 1 and 2 of the proof of
Theorem mixture use (H0), (H1), (SRT_pm) only (see Section 3 above: the uniformity in x in
range 2 does not use (H2)). Range 3, young part: nu^y_+(d) with d in [eps N, (1-eps) N]
satisfies N nu^y_+(d) <= C by aged-pointwise(a), and Corollary count gives
<= C_eps zeta(delta)/N. Correct.

**Range 3, old part E_o.** Re-derived before reading.

Setup: E_o = sum_{i<=delta N} nu^o_+(k - i) F^-_{j+i}(i). Lemma E applies to F^-_{j+i}(i)
with n = j + i >= (1 - x_2) N and i <= delta N <= (1 - x_2) N <= j, so i <= n/2; it gives
F^-_{j+i}(i) <= C T_+(j+i) omega_+(i) <= C T_+(N) omega_+(i), and its hypotheses are the
three non-(LB) cases of the theorem exactly. With M = t_a + k, y = i + s:
E_o <= C T(N) sum_y f_+(M - y) W(y), W(y) = sum_{i+s=y, i<=delta N, s<=t_a/2} omega(i) u_c(s),
and M - y >= t_a/2 + k - delta N >= cN on the range of the sum. Correct, including the
i = 0 term (omega(0) = 1 and Lemma E at i = 0).

(W1): W(y) <= C (omega*omega)(y) by (U) with omega(0) = u_c(0) = 1. Splitting the convolution
at y/2: sum_{i<=y/2} omega(i) omega(y - i) <= C omega(y) sum_{i<=y/2} omega(i) <= C omega(y)/T(y)
using (R1) on [y/2, y] and sum_{i<=Y} omega(i) <= 1 + sum_{1<=i<=Y} 1/(iT(i)) <= C/T(Y)
(R3). Both halves are of this form, and omega(y)/T(y) <= 1/(y T(y)^2). Correct for y >= 1.

(W2): for y > 2 delta N every term has s = y - i >= y - delta N >= y/2, so u_c(s) <= C omega(y)
(R1 on [y/2, y]) and W(y) <= C omega(y) sum_{i<=delta N} omega(i) <= C omega(y)/T(delta N). Correct.

Range y <= 2 delta N, alpha > 1/2: 1/(y T(y)^2) has positive index 2alpha - 1, so
sup_{1<=y<=2 delta N} <= C/(delta N T(delta N)^2) for delta N large (BGT 1.5.3), and
W(0) = 1 is below the same bound since it tends to infinity. With sum_y f_+(M - y) <= 1 the
range is <= C T(N)^2/(delta N T(delta N)^2); Potter, T(N)/T(delta N) <= 2 delta^{alpha - eps'},
gives <= C delta^{2alpha - 1 - 2eps'}/N. Correct; the exponent 2alpha - 1 is positive
exactly when alpha > 1/2, which is why this route is confined to that case.

Range y <= 2 delta N, alpha <= 1/2: the range is <= C T(N)[f_+(M) + sum_{1<=y<=2 delta N}
f_+(M - y)/(y T(y)^2)]. Lemma cd(iii): for alpha <= 1/2, (SRT_+) is equivalent to
lim_{delta'} limsup_x x T(x) sum_{1<=z<=delta' x} f_+(x - z)/(z T(z)^2) = 0. Define
zeta_CD(delta') as the limsup; it is nondecreasing in delta' and tends to 0. Since
M >= (theta/2 + x_1) N for large N, 2 delta N <= delta' M with delta' = C delta, and
M T(M) asymp N T(N) because M/N in [1, theta + 2]; the limsup is over x -> infinity and
M -> infinity, so no separate uniformity over M is needed. The sum is then
<= C (zeta_CD(C delta) + o(1))/(N T(N)). The z = 1 term alone gives
M T(M) f_+(M - 1) <= zeta_CD(delta') + o(1) for every delta', hence f_+(M) = o(1/(M T(M))).
The range is <= C (zeta_CD(C delta) + o(1))/N. Correct, and the Caravenna-Doney condition is
applied within the hypotheses of Lemma cd(iii) (alpha <= 1/2, (SRT_+) assumed).

Range 2 delta N < y <= eta N, eta = delta^{1 - alpha} (which exceeds 2 delta for
delta < 2^{-1/alpha}): (W2) and omega(y) <= C omega(delta N) for y >= 2 delta N (negative
index) give W(y) <= C/(delta N T(delta N)^2); sum of f_+(M - y) over the range is
P(M - eta N <= X_+ < M - 2 delta N) = T(M - eta N) - T(M - 2 delta N) <= T(N)(C eta + o(1))
by (R1) at scale N and the mean value theorem on t^{-alpha}, t >= theta/2. Product:
C (eta + o(1)) T(N)^2/(delta N T(delta N)^2) <= C (eta delta^{2alpha - 1 - 2eps'} + o(1))/N
and eta delta^{2alpha - 1} = delta^alpha. Correct; the o(1) is for fixed delta as N -> infinity,
which is the order of limits used.

Range y > eta N: dyadic blocks (Y, 2Y] with Y >= eta N/2 and y <= M - cN, so boundedly many
blocks (O(log(1/eta))). W(y) <= C omega(Y)/T(delta N); the block sum of f_+(M - y) is
<= T(max(M - 2Y, cN)) - T(M - Y) <= T(N)(C Y/N + o(1)) by (R1) with arguments in
[cN, CN]. Summing: sum_Y Y omega(Y) <= sum_Y 1/T(Y) <= C/T(N) (1/T has positive index,
so the dyadic sum is geometric up to Y <= CN) and sum_Y omega(Y) <= C omega(eta N) log(1/eta).
The range is <= C (T(N)/T(delta N)) [1/N + o(1) T(N) omega(eta N) log(1/eta)]
<= C delta^{alpha - eps'}/N + o(1/N). Correct.

Total: N E_o <= C delta^{2alpha - 1 - eps'} + C delta^{alpha - eps'} + o(1) for alpha > 1/2
(and 2alpha - 1 < alpha, so the stated min(alpha, 2alpha - 1) is 2alpha - 1), and
N E_o <= C zeta_CD(C delta) + C delta^{alpha - eps'} + o(1) for alpha <= 1/2; both tend to 0
as N -> infinity then delta -> 0, independently of eps, which fits the limit scheme of
Theorem mixture. Minus side: mirror with v_c <= C omega_+ from (U), the condition for f_-
from (SRT_-), and the mirror of Lemma E. The closing sentence on which inputs each case
uses is accurate: for alpha > 1/2 everything is automatic, for alpha < 1/2 (SRT_pm) and
(U), and at alpha = 1/2 Lemma E adds the condition on n T_+(n)^2.

**Check of the author's argument.** Matches the above step for step. Two places are
compressed but correct: the truncation y <= M - cN inside the top dyadic block (needed so
that T(M - 2Y) is evaluated at an argument >= cN), and the geometric nature of
sum_Y 1/T(Y) (without it a log(1/eta) would appear, harmless for fixed delta anyway).

**Verdict: proved as written.**

### (c) The end layers

**Claim card.** (BAL), (SPAN), (U). For fixed j >= 1,
P_N(N - j) = T_+(N)[c_+(theta) u_-(j) + o(1)], P_N(j) = T_-(N)[c_-(theta) u_+(j) + o(1)].

**Independent derivation.** First-run decomposition at k = N - j, j >= 1 fixed:
P_N(N - j) = sum_{m=1}^{N-1} nu_+(N - m) Pi^-_m(j) + sum_{d=1}^j nu_-(d) F^+_{N-d}(N - j)
(D >= 1 always; F^+_{N-d}(N - j) = 0 for d > j).

Second sum: F^+_{N-d}(N - j) <= C_j T_+(N) by Theorem ends(a) at the fixed distance j - d
plus a constant for small horizons. nu_-(d) = sum_{s<=t_a} v_c(s) f_-(t_a - s + d)
<= sup_{s>t_a/2} v_c(s) T_-(d) + sum_{s<=t_a/2} f_-(t_a - s + d) <= sup_{s>t_a/2} v_c(s) + T_-(t_a/2),
and v_c(s) -> 0 because u_c(s) -> 0 (renewal theorem for the aperiodic cycle law with
infinite mean) and v_c = f_+ * u_c (dominated convergence). So the second sum is o(T_+(N)).

First sum, m > eta N: Theorem ends(a) for a fresh minus walk gives
Pi^-_m(j) = T_+(m)[u_-(j) + o(1)] uniformly in m >= eta N. With d = N - m,
sum_{d<(1-eta)N} nu_+(d) T_+(N - d)/T_+(N) -> int_0^{1-eta} rho_+(z)(1 - z)^{-alpha} dz:
(R1) makes T_+(N - d)/T_+(N) = (1 - d/N)^{-alpha} + o(1) uniformly on d <= (1 - eta) N;
the mass of nu_+ on d < eps N is controlled by Lemma DL's third statement (pi^0 = 0) with
the integrand bounded by (1 - eps)^{-alpha} there; on [eps N, (1 - eta) N] it is vague
convergence (H1) against a bounded continuous function whose cut points are null for the
limit. Lemma DL supplies all three ingredients.

First sum, m <= eta N: Pi^-_m(j) <= C_j T_+(m). Young part: aged-pointwise(a) with
d = N - m >= (1 - eta) N gives (C/N) sum_{m<=eta N} T_+(m) <= C eta T_+(eta N)
<= C eta^{1 - alpha - eps'} T_+(N). Old part: <= C_j sum_y f_+(M' - y) W'(y), M' = t_a + N,
W'(y) = sum_{m+s=y, 1<=m<=eta N, s<=t_a/2} T_+(m) u_c(s). W' <= C: split at y/2; the part
m <= y/2 is <= C omega(y) sum_{m<=y/2} T_+(m) <= C omega(y) y T_+(y) <= C, the part
m > y/2 is <= T_+(y/2) U_c(y/2) <= C T_+(y)/T_c(y) <= C. For y > 2 eta N every term has
s >= y/2, so W'(y) <= C omega(y) sum_{m<=eta N} T_+(m) <= C omega(y) eta N T_+(eta N).
Range y <= 2 eta N: <= C P(M' - 2 eta N <= X_+ <= M') <= C T_+(N)(eta + o(1)) by (R1)
(M'/N -> theta + 1). Dyadic blocks above 2 eta N: as in (a),
<= C eta N T_+(eta N) T_+(N)[C/(N T_+(N)) + o(1) omega(eta N) log(1/eta)]
= C eta T_+(eta N) + o(T_+(N)) <= C eta^{1 - alpha - eps'} T_+(N) + o(T_+(N)).

N -> infinity then eta -> 0: P_N(N - j)/T_+(N) -> u_-(j) int_0^1 rho_+(z)(1 - z)^{-alpha} dz
= c_+(theta) u_-(j), the tail int_{1-eta}^1 being small because rho_+ is bounded near 1
and (1 - z)^{-alpha} is integrable. Minus end: mirror, with the roles of u_c and v_c and of
the signs exchanged.

**Check of the author's argument.** Identical. The phrase "Lemma DL with the bounded
continuous integrand (1 - z)^{-alpha} on [0, 1 - eta]" uses the pi^0 = 0 part of Lemma DL
for the mass near z = 0 without saying so; Lemma DL contains it.

**Verdict: proved as written.**

---

## 7. Claims after the theorem

**7.1 Mass identity** int_0^1 L_theta + Q^infty_+ + Q^infty_- = 1.
Fubini: int_0^1 int_0^x rho_+(z) Lambda((x - z)/(1 - z)) dz dx/(1 - z)
= int_0^1 rho_+(z) [int_z^1 Lambda((x - z)/(1 - z)) dx/(1 - z)] dz = int_0^1 rho_+(z) dz
by w = (x - z)/(1 - z); the mirror gives int_0^1 rho_-. With Q^infty_sigma = int_1^infty
rho_sigma the total is int_0^infty (rho_+ + rho_-) = p_+ + p_- = 1.
**Verdict: proved as written.**

**7.2 theta -> 0.** rho_sigma dz -> p_sigma delta_0: the mass of rho_sigma on [r, infinity) is
p_sigma (sin pi alpha/pi) int_{r/theta}^infty w^{-alpha}/(1 + w) dw -> 0 while the total is
p_sigma. L_theta -> Lambda uniformly on compacts: on z <= x/2, g_x is uniformly continuous
with g_x(0) = Lambda(x), so int_0^{x/2} rho_+ g_x -> p_+ Lambda(x) uniformly; on
[x/2, x], g_x(z) <= C (x - z)^{alpha - 1} and sup_{z>=x/2} rho_+(z) <= C theta^alpha, so
that piece is O(theta^alpha); same for the minus integral; the sum tends to
(p_+ + p_-) Lambda = Lambda. Q^infty_sigma(theta) = p_sigma (sin pi alpha/pi)
B(theta/(1 + theta); alpha, 1 - alpha) -> 0. c_+(theta) -> p_+: with z = theta w,
theta^alpha int_0^1 z^{-alpha}(1 - z)^{-alpha}(theta + z)^{-1} dz
= int_0^{1/theta} w^{-alpha}(1 - theta w)^{-alpha}/(1 + w) dw -> int_0^infty w^{-alpha}/(1 + w) dw
= pi/sin(pi alpha) (the piece z in [1/2, 1] is O(1), negligible against theta^{-alpha}),
which is the asymptotic the text states. **Verdict: proved as written.**

**7.3 Non-commuting limits at the ends.** The fresh layer is T_+(N) u_-(j) for j >= 1
for either starting sign (Theorem ends(a)); the aged layer is T_+(N) c_+(theta) u_-(j)
with c_+(theta) -> p_+ = 1/(1 + b) < 1 as theta -> 0. So lim_theta lim_N differs from
lim_N at theta = 0 by the factor p_+. **Verdict: proved as written.** (The attribution
to the remark after Eq. (15) of asyy2020 with c(r) -> 1/2 at b = 1 is a citation and was
not checked against the source.)

**7.4 theta -> infinity.** Q^infty_sigma -> p_sigma (sin pi alpha/pi) B(1; alpha, 1 - alpha)
= p_sigma. L_theta = O(theta^{alpha - 1}) on compacts: theta^alpha/(theta + z) <= theta^{alpha - 1},
so rho_sigma(z) <= C theta^{alpha - 1} z^{-alpha} and both integrals in L_theta are
finite for x in a compact subset of (0,1). **Verdict: proved as written** (as a statement
on compact subsets of (0,1), which is how it reads).

**7.5 "The end layers keep the fresh shape u_-(j) and lose the factor
c_+(theta) < p_+ < 1."** The inequality c_+(theta) < p_+ is false for alpha > 1/2.

Derivation. c_+(theta)/p_+ = (sin pi alpha/pi) theta^alpha int_0^1 z^{-alpha}
(1 - z)^{-alpha}(theta + z)^{-1} dz. Split (1 - z)^{-alpha} = 1 + [(1 - z)^{-alpha} - 1].
The first part is (sin pi alpha/pi) int_0^{1/theta} w^{-alpha}/(1 + w) dw
= 1 - (sin pi alpha/pi) theta^alpha/alpha + o(theta^alpha). The second is
(sin pi alpha/pi) theta^alpha [K(alpha) + o(1)] with
K(alpha) = int_0^1 z^{-alpha - 1}[(1 - z)^{-alpha} - 1] dz, finite, and by analytic
continuation of B(s, 1 - alpha) - 1/s to s = -alpha,
K(alpha) - 1/alpha = Gamma(-alpha) Gamma(1 - alpha)/Gamma(1 - 2alpha). Hence
c_+(theta)/p_+ - 1 = (sin pi alpha/pi) [Gamma(-alpha) Gamma(1 - alpha)/Gamma(1 - 2alpha)] theta^alpha + o(theta^alpha).
Gamma(-alpha) < 0 and Gamma(1 - alpha) > 0 on (0,1); Gamma(1 - 2alpha) > 0 for alpha < 1/2
and < 0 for alpha in (1/2, 1). So the coefficient is negative for alpha < 1/2 and positive
for alpha > 1/2: for alpha > 1/2, c_+(theta) > p_+ for all small theta.

Counterexamples (closed form (eq:aged-constants), verified against the integral to
quadrature precision):
- alpha = 0.7, b = 1, theta = 1/2: c_+ = 0.5708 > p_+ = 0.5 (ratio 1.14).
- alpha = 0.9, b = 1, theta = 1: c_+ = 0.7132 > p_+ = 0.5 (ratio 1.43); the ratio
  exceeds 1 for every theta in [0.01, 10] tested.
- alpha = 0.9, b = 0.1, theta = 2: p_+ = 0.909 and c_+ = 1.361 > 1. This also refutes the
  weaker statement in `sec_intro.tex` ("its height is multiplied by an explicit constant
  c_+(theta) < 1") and the word "lose".
Numerically K(alpha) - 1/alpha = -2.532 at alpha = 0.3 and +3.434 at alpha = 0.7, matching
the Gamma formula.

What survives. c_+(theta) -> p_+ as theta -> 0 and c_+(theta) -> 0 as theta -> infinity
(both proved above), so the non-commutation of 7.3 stands. For alpha = 1/2 the closed form
is c_+(theta) = p_+ (1 + theta)^{-1/2} < p_+ for every theta > 0, so the inequality holds on
the line, and in particular at the headline value c_+(1) = 1/(2 sqrt 2) < 1/2. For
alpha < 1/2 the first-order coefficient is negative and the tested values satisfy
c_+ < p_+, but the text gives no proof for all theta, and none was attempted here.
Reading: the factor (1 - z)^{-alpha} is the gain from a straddling plus run that leaves a
remainder of length (1 - z) N with a heavier tail at the horizon; for alpha > 1/2 this gain
beats the loss of mass to runs that reach past the window.

**Verdict: refuted, with counterexample** (alpha = 0.9, b = 1, theta = 1: c_+ = 0.7132,
p_+ = 0.5). **Correct only after the restriction alpha = 1/2** (where
c_+(theta) = p_+ (1 + theta)^{-1/2}); for alpha < 1/2 the inequality is unproved and
numerically plausible; for alpha > 1/2 it is false, and c_+(theta) > 1 occurs for small b.
The same correction applies to the sentence in `sec_intro.tex` quoted above.

---

## Summary table

| Claim | Verdict |
|---|---|
| 1. Lemma lem:E, three cases | proved as written |
| 2. Lemma lem:count | proved as written |
| 2. Corollary cor:count | proved as written (Potter, not (R2), at one step) |
| 3. Theorem thm:mixture | proved as written (range-2 uniformity in x is routine and filled above) |
| 4. Lemma lem:DL, closed forms, c_+(1) = 1/(2 sqrt 2) | proved as written |
| 5. Lemma lem:U | statement proved; one false sentence in the proof ("T_+(n) <= omega_+(n)", false for alpha < 1/2), repaired by the z = 1 term of the Caravenna-Doney condition |
| 5. Lemma lem:aged-pointwise | proved as written |
| 6. Theorem thm:aging (a) | proved as written |
| 6. Theorem thm:aging (b) | proved as written |
| 6. Theorem thm:aging (c) | proved as written |
| 7. Mass identity, theta -> 0 and theta -> infinity limits, non-commutation | proved as written |
| 7. "c_+(theta) < p_+ < 1" | refuted for alpha > 1/2 (alpha = 0.9, b = 1, theta = 1 gives c_+ = 0.713 > 0.5; alpha = 0.9, b = 0.1, theta = 2 gives c_+ = 1.36 > 1); true at alpha = 1/2; unproved for alpha < 1/2 |

Side finding, not in the list: the sentence after Theorem thm:mixture, "the sum of these
bounds over i <= delta N is of order T(N)/T(delta N), which is not small", is wrong;
T(N)/T(delta N) -> delta^alpha. The counting bound is needed to avoid (LB) and the
alpha = 1/2 restriction of Lemma lem:E, not because the pointwise route diverges.
