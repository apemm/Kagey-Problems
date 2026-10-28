# Audit of Paper F: second differences in the big-jump range, the cycle law, and the exposure corollaries

Date: 2026-10-28. Files audited at their current state in `paperF/`: `sec_modeproofs.tex`
(Lemma `lem:second-bigjump`, Lemma `lem:plus-second`), `sec_exposure.tex` (Proposition
`prop:cycle`, Corollaries `cor:exposure-bulk`, `cor:exposure-tail`, `cor:exposure-mode`), with
`sec_setting.tex` for notation. Taken as given with their stated hypotheses: `lem:ld2`,
`lem:trunc-local`, `lem:truncated`, `lem:diff-bigjump`, `lem:stable`, `lem:rv`, and the
theorems of Sections 3 to 7 (`thm:bulk`, `thm:preparation`, `cor:stationary`, `thm:bigjump`,
`cor:infinite-density`, `thm:mode`, `thm:aging`, `cor:aged-mode`, `thm:ends`, `thm:mode-count`,
`cor:three-modes`, `cor:logconvex-three`, `lem:one-max`, `lem:logconvex`).

Method: each claim was restated as a claim card, the critical step re-derived from the
definitions before reading the proof, then every implication of the proof was checked.
Numerical evidence was produced with the paper's own `verify_exposure.py` (class `Model`) for
the zeta service law of index 3/2 and loads 0.6, 0.4, which are the paper's parameters.

Verdict scale: proved as written / correct only after a stated restriction / conditional on a
named input / incomplete, with the smallest missing implication / refuted, with a counterexample.

---

## Claim 1. Lemma `lem:second-bigjump` and its use in Lemma `lem:plus-second` (i) to (iii)

### Claim card

Hypotheses: (SPAN), (LR), (LD2) for one law; c > 0 fixed. Conclusion: there are K_1, L_0, C
depending on the law and on c such that for all m >= 1 and integers n with
L = n - m mu >= max(K_1 a(m), L_0, c m),

  |nabla u_m(n)|       <= C m f(L)/L,
  |nabla^2 u_m(n)|     <= C m f(L)/L^2,
  |nabla delta u_m(n)| <= C f(L)/L,
  |delta^2 u_m(n)|     <= C f(L)/L.

Then Lemma `lem:plus-second`: under (LR), (LD2) for the plus sign, uniformly in
0 <= m <= n^{1-eta}: (i) |nabla^2 V_m(n)| <= C m f(n)/n^2, (ii) |nabla delta V_m(n)| <= C f(n)/n,
(iii) |delta^2 V_m(n)| <= C f(n)/n.

### Independent derivation of the critical steps

Standing consequences of the range (all checked): m <= L/c; m f(L) <= C T(L) by (LR);
m T(delta L) <= C_delta L T(L) by Potter; m T(L) <= C and m T(L) L/a(m) <= C from
L >= K_1 a(m) and (`eq:potter-m`); f(L') <= C_b f(L) for L' >= bL.

Second bound. The exact identity nabla^2 u_m^{(w)} = (nabla g_1) * (nabla g_2) for the
two-block split of the truncated sum is correct (nabla commutes with convolution, and the
truncation event factorizes over blocks). In the convolution sum, (y - m_1 mu) + (n - y - m_2 mu)
= L, so one block exceeds its mean by at least L/2. Sum_{y >= Y}|nabla g(y)| <= 2 P(S >= Y-1,
max < w) holds because |g(y-1) - g(y)| <= g(y-1) + g(y). With `lem:truncated` (exponent
(L/2-1)/(2w) >= L/(8w) for L >= 4) and `lem:trunc-local`(b) (needs only m_i T(w) <= 1), the
no-giant part is at most C a(m)^{-2}(mT(w))^{L/(8w)} <= C L^{-(alpha-1-eps')/(16 delta)}, which
is o(f(L)/L^2) <= o(m f(L)/L^2) once delta is small; the bound is independent of m.

The giant-summand identity was re-derived. With F(n') = sum_{z <= n'-w} h_i(z) f(n'-z),

  nabla^2 F(n) = sum_{z <= n-2-w} h_i(z) nabla^2 f(n-z) + h_i(n-1-w)(f(w+1) - f(w))
                 + f(w)(h_i(n-w) - h_i(n-1-w)),

which is the paper's display. The three parts give C_delta m f(L)/L^2 (LD2 and Potter at
arguments >= delta L), C m f(L)/L^2 times mT(L)L/a(m) <= C (`lem:stable`(iii) at deviation
>= L/2 and LD), and C m f(L)/L^2 times m L f(L) <= C m T(L) <= C. The last part uses the first
bound of `lem:diff-bigjump` as an upper bound for the mixed law h_i at level n-w: its no-giant
part is the pure truncated sum u^{(w)}_{m-1}, and in its giant part the remaining law is
dominated pointwise by u_{m-2}, so `lem:stable`(iii) applies. The exponent of the no-giant
part at deviation L/2 is 1/(64 delta) rather than 1/(16 delta); the proof's "fix delta small"
covers this, since all requirements on delta are of the form delta < delta_0(alpha) and the
delta-dependent constants multiply terms already of the right order.

Third bound. The decomposition of nabla delta u_m(n) = sum_x f(x)[nabla u_m(n-x) - nabla u_m(n)]
at x = L/2 is exact. For x <= L/2 the bracket telescopes into x second differences at points
with deviation in [L/2, L], where the second bound at the constant c/2 applies (the range
L' >= (c/2) m is implied by L' >= L/2 >= cm/2). The sum is C mu m f(L)/L^2 <= C f(L)/(cL):
this is where c enters. The middle term is C(mT(L)) f(L)/L. The summation by parts in the
last sum was checked term by term; it needs only sum_y u_m(y) <= 1 and (LD) at arguments
>= L/2, and the boundary term is C m f(L)^2 <= C(mT(L)/L) f(L).

Fourth bound. delta^2 u_m = f * delta u_m - delta u_m is correct. The first sum uses the third
bound at c/2 on deviations in [L/2, L]. The last sum equals E[gamma(S_m + X) - gamma(S_m)]
with gamma(y) = f(n-y) 1{y < n - L/2}; the three cases (both arguments below n - L/2, the
crossing event, both above) are exhaustive. The crossing event has probability
sum_k T(k) u_m(n'-k) <= C T(L), split at k = L/4 as in the proof, and contributes
C f(L) T(L) = o(f(L)/L). The (LD) telescoping in the first case uses f(y)/y <= C f(L)/L for
every y >= L/2, which follows from Potter's bounds for the index -alpha-1.

Dependence on c. c enters only through m <= L/c (third bound, first sum; the reductions
m f(L) <= CT(L) and m T(delta L) <= C_delta L T(L)) and through L_0 (where C_delta L T(L) <= 1
is first needed). The successive bounds use the previous bound at c/2, and since each bound
is proved for every c > 0 before the next, this is an induction over the four bounds with
K_1(c) and L_0(c) enlarged at each stage; there is no circularity. The constants degrade like
1/c as c decreases, consistent with the statement.

Derivation of `lem:plus-second`. For 1 <= m <= n^{1-eta}: L = n - m mu is in [n/2, n] for large
n; L >= m holds since m <= n^{1-eta} <= n/2 (this is the case c = 1); L >= K_1 a(m) holds since
a(m) <= a(n^{1-eta}) = o(n). The transfer f(L) <= C f(n) and 1/L <= 2/n gives (i) to (iii).
For m = 0: nabla^2 V_0(n) = 0 for n >= 3; nabla delta V_0(n) = f(n-1) - f(n) for n >= 2, which is
(LD) via `lem:ld2`; delta^2 V_0(n) = f*f(n) - 2f(n) for n >= 1, and the symmetric split at n/2
gives 2 sum_{x<n/2} f(x)[f(n-x) - f(n)] - 2f(n)T(n/2) + f(n/2)^2 1{n even}, each part
O(f(n)/n) by (LD), nT(n) -> 0 and f(n/2)^2 <= C f(n) T(n)/n. The statement "the same holds at
every argument n' >= n/2" follows from n^{1-eta} <= (n')^{1-eta/2} for large n.

### Checks on the hypotheses of the inputs

`lem:second-bigjump` assumes (SPAN); `lem:plus-second` assumes only (LR) and (LD2) for the
plus sign. This is not a gap: (LR) gives f(n) ~ alpha T(n)/n with T(n) > 0 for every n, so
f(n) > 0 for all large n and the support is in no progression b + hZ with h >= 2. The paper
uses this implication in the proof of `prop:cycle`(a) but does not record it in Section 2;
a one-line remark there would close the appearance of a mismatch. The same remark applies to
`thm:layer-second`, which states (SPAN) for the minus sign only.

`lem:second-bigjump` sits in Section `app:bulk`, which opens with "We keep the conditions of
Section `app:zone`" (equal indices, comparable scales). The proof of the lemma uses none of
them; its own hypothesis list is complete, and both applications (c = 1 in `lem:plus-second`,
c = (1-rho)/2 in `prop:cycle`(b)) are legitimate.

### Verdict

Proved as written. All four bounds, the dependence on c, and the derivation of
`lem:plus-second`(i) to (iii) including m = 0 hold. Two presentational points: record that
(LR) implies (SPAN), and note that the lemma does not use the standing conditions of
`app:zone`.

---

## Claim 2. Proposition `prop:cycle` (a), (b), (c)

### Claim card

Queue: W = 0 with probability 1 - lambda, W = n with probability lambda f_Y(n); rho = lambda E Y < 1;
cycle C = first passage of U_t - t to -1; phi(n) = n f_C(n) = V_n(2n-1) with V_m = f_{W'}^{*m},
W' = W + 1, mu' = 1 + rho, deviation L = (1-rho)n - 1.

(a) f_C(n) ~ f_W((1-rho)n) ~ lambda (1-rho)^{-alpha-1} f_Y(n), T_C(n) ~ lambda (1-rho)^{-alpha-1} T_Y(n);
C satisfies (LR) with index alpha, and (SPAN).
(b) If Y satisfies (LD2): C satisfies (LD) and (LD2), and f_C(n+1) - f_C(n) = -(alpha+1+o(1)) f_C(n)/n.
(c) Two arms sharing Y: (EQ), and T_+/T_- -> (lambda_+/lambda_-)((1-rho_-)/(1-rho_+))^{alpha+1}.

### Independent derivation

Reduction. V_1 = W_1 and V_t = V_{t-1} - 1 + W_t while V_{t-1} >= 1 give V_t = U_t - t + 1 up to
the end of the cycle, so C = inf{t : U_t - t = -1} and the hitting-time theorem gives
P(C = n) = P(U_n = n-1)/n. U_n = U'_n - n turns this into phi(n) = V_n(2n-1). Checked:
f_C(1) = f_{W'}(1) = 1 - lambda and f_C(2) = lambda(1-lambda) f_Y(1), both agree with the direct
queue computation.

(a) W' has (LR) with index alpha: f_{W'}(n) = lambda f_Y(n-1) ~ lambda alpha T_Y(n)/n and
T_{W'}(n) = lambda T_Y(n-1) ~ lambda T_Y(n). The local big-jump theorem is applied to
xi = W' - mu' at r = n, x = 2n - 1 - n mu' - 1/2. The event {U'_n - n mu' in (x, x+1]} is exactly
{U'_n = 2n - 1}. For the one-step probability, x + mu' = (1-rho)n + rho - 1/2, so
P(x < xi <= x+1) = f_{W'}(n') with n' the unique integer in ((1-rho)n + rho - 1/2,
(1-rho)n + rho + 1/2], that is n' = (1-rho)n + O(1). (A first reading of x + mu' as 2n - 3/2 is
an arithmetic slip; the paper's n' is right.) The uniformity threshold x_r = (1-rho)r/2
satisfies x >= x_n for n >= 3/(1-rho) and r T_{W'}(x_r) ~ c r^{1-alpha} -> 0, which for a
regularly varying tail with index -alpha in (1,2) is equivalent to x_r/a(r) -> infinity, the
boundary of the big-jump domain; this is the same criterion the paper used in
`lem:local-bigjump`, whose hypothesis check for (25) to (27) of Denisov, Dieker and Shneer
transfers to W' (left tail bounded below by -rho, mean zero, index -alpha). Then
f_{W'}(n') = f_{W'}((1-rho)n)(1+o(1)) by uniform convergence, phi(n) = n f_W((1-rho)n)(1+o(1)),
and the rest is regular variation of f_W = lambda f_Y and summation of asymptotically
equivalent nonnegative terms for the tail. (SPAN) from f_C(1) > 0 and f_C(n) > 0 eventually.

(b), (LD). W' has (LD2) because its second differences are those of lambda f_Y shifted by one,
and (LD) by `lem:ld2`. The identity

  phi(n+1) - phi(n) = delta V_n(2n+1) - nabla V_n(2n+1) - nabla V_n(2n)

was re-derived (V_{n+1}(2n+1) - V_n(2n+1) is delta V_n at 2n+1; V_n(2n+1) - V_n(2n-1) is minus
the two nabla's). The deviations at m = n are L+2, L+2, L+1, all >= K a(n) for large n for
every K since a(n) = o(n), so `lem:diff-bigjump` applies with epsilon -> 0. With
n/L -> 1/(1-rho) and mu' - 2 = -(1-rho),

  phi(n+1) - phi(n) = f(L)[1 + (alpha+1)(n/L)(mu'-2) + o(1)] = -alpha f(L)(1+o(1)),

and f_C(n+1) - f_C(n) = [phi(n+1) - phi(n)]/(n+1) - phi(n)/(n(n+1)) = -(alpha+1+o(1)) f(L)/n,
with f(L) ~ f_C(n) by (a). Sanity check: phi is in RV_{-alpha} and f_C in RV_{-alpha-1}; the
constants -alpha and -(alpha+1) are the ones a smooth regularly varying function would have.

(b), (LD2). `lem:second-bigjump` with c = (1-rho)/2 at m = n and points 2n-1 <= x <= 2n+3:
L_x = L + (x - 2n + 1) in [L, L+4] and L = (1-rho)n - 1 >= (1-rho)n/2 = cn for n >= 2/(1-rho),
L >= K_1 a(n) and L >= L_0 for large n; the hypotheses are met. The nine-term expansion of
D(n+1) - D(n) was re-derived from X_{n+1}(x+2) - X_n(x) = delta X_n(x+2) - nabla X_n(x+2)
- nabla X_n(x+1) applied to X = delta V (at x = 2n+1) and X = nabla V (at x = 2n+1 and 2n),
with delta nabla = nabla delta; it matches the paper's display term for term, and the points
involved are 2n+1, 2n+2, 2n+3. Each term is at most C f(L)/L: the delta^2 and nabla delta
terms directly, the nabla^2 terms via C n f(L)/L^2 <= C f(L)/(cL). So |Delta^2 phi(n)| <= C f(L)/n.
The product rule

  Delta^2(g phi)(n) = g(n+2) Delta^2 phi(n) + Delta phi(n)[Delta g(n) + Delta g(n+1)] + phi(n+1) Delta^2 g(n)

was verified by expanding both sides (the coefficients of phi(n+2), phi(n+1), phi(n) are
g(n+2), -2g(n+1), g(n)). With g = 1/n the three terms are O(f(L)/n^2), O(f(L)) O(n^{-2}) and
O(n f(L)) O(n^{-3}); f(L) ~ f_C(n) gives (LD2) for C. The check in Section 10 of the paper
(n Delta f_C/f_C = -2.499 and n^2 Delta^2 f_C/f_C = 8.745 at n = 2^13 against -5/2 and 35/4) is
consistent.

(c) Immediate from (a); the limit is positive and finite, which is (EQ).

### Verdict

Proved as written, for (a), (b) and (c). The application of the local big-jump theorem at
x_r = (1-rho)r/2 is within the reading of Denisov, Dieker and Shneer adopted in
`lem:local-bigjump` (the criterion r T(x_r) -> 0, equivalently x_r/a(r) -> infinity), and the
first-difference computation, the nine-term expansion and the product rule are correct.

---

## Claim 3. Corollaries `cor:exposure-bulk`, `cor:exposure-tail`, `cor:exposure-mode`

### Preamble: convergence of the scale ratio

T_sigma ~ kappa_sigma T_Y with kappa_sigma = lambda_sigma (1-rho_sigma)^{-alpha-1}. If
t T_Y(a_Y(t)) -> 1, then t T_sigma(a_Y(kappa_sigma t)) -> 1, so a_sigma(t) ~ a_Y(kappa_sigma t)
~ kappa_sigma^{1/alpha} a_Y(t) by regular variation of a_Y with index 1/alpha and the uniqueness
of asymptotic inverses up to equivalence. Hence b_{+,N}/b_{-,N} -> (kappa_+/kappa_-)^{1/alpha}
and theta_sigma = min{1, (kappa_sigma/kappa_{bar sigma})^{1/alpha}}, as stated; `lem:profile`(c)
gives h_N -> h_theta uniformly. Correct.

### `cor:exposure-bulk`

Fresh start: `thm:bulk`(a), (b) under (RV), (SPAN), plus ||h_N - h_theta|| -> 0. Random-time
start: the stationary law is a fixed law, so (`eq:tight`) holds; `cor:stationary` gives the
bulk criterion B_n P(D = n) = B_n(T_+(n) + T_-(n))/s -> 0 and `thm:preparation`(b) gives the
uniform statement on 1 <= k < N, from which the bound sup B_N P_N(k) < infinity on 1 <= k < N
follows since h_N <= C_1. The whole range: by `thm:preparation`(b) the second error is
max(..., B_N Q_+(N), B_N Q_-(N)) + o(1), and B_N Q_sigma(N) is in RV_{1/alpha + 1 - alpha} with
equal indices; the exponent is negative iff alpha^2 - alpha - 1 > 0 iff alpha > phi, and
positive iff alpha < phi, where B_N P_N(N) = B_N Q_+(N) -> infinity while h_theta(x_{N,N}) -> 0.
The convergence in law follows from the local statement on 1 <= k < N (Riemann sums over
compact windows, h_theta integrates to one) and Q_+(N) + Q_-(N) -> 0. The phrase "exact order
N^{1/alpha - 1}" is up to the slowly varying factor of T_Y, as elsewhere in the paper.

Verdict: proved as written.

### `cor:exposure-tail` (a)

Independent computation of the integral. With ell = (v-p)/(1-p), dv = (1-p) d ell and
(1-p)/mu_- = 1/s,

  int_{1-eps}^{1} I_+(v) dv = (1/s) int_{ell_eps}^{1} [alpha(1-ell) ell^{-alpha-1} + ell^{-alpha}] d ell
                          = (1/s)[-(1-ell) ell^{-alpha}]_{ell_eps}^{1} = (1-ell_eps) ell_eps^{-alpha}/s
                          = (eps/mu_-) ell_eps^{-alpha},

since d/d ell [-(1-ell) ell^{-alpha}] = ell^{-alpha} + alpha(1-ell) ell^{-alpha-1} and
1 - ell_eps = eps/(1-p). The extra stationary integral is
(1/s) int_{ell_eps}^{1} ell^{-alpha} d ell = (ell_eps^{1-alpha} - 1)/(s(alpha-1)), and adding the
atom Q_+(N) ~ N T_+(N)/(s(alpha-1)) gives ell_eps^{1-alpha}/(s(alpha-1)). Both formulas of the
statement are reproduced.

The argument. The points (1-eps)N <= k <= (1-delta)N have L_k >= ell_eps N exactly (no o(1)
needed), which needs ell_eps > 0, that is eps < 1 - p, as assumed; they lie in the zone of
`thm:bigjump`(b) for every K since lambda_N B_N = o(N). There hat G_N(k) <= ell_eps^{-1}
T_+(ell_eps N) <= C_eps T_+(N), so the additive form, applied for each K and then K -> infinity,
makes the total error over at most N points o(N T_+(N)). Uniform convergence of
G_N(floor(vN))/T_+(N) to I_+(v) on [1-eps, 1-delta]: j = N - k = (1-ell)(1-p)N -> infinity
uniformly, gamma(j)/j -> s/mu_-^2 and kappa(j) -> 1/mu_- uniformly, and N f_+(floor(ell N))/T_+(N)
-> alpha ell^{-alpha-1}, T_+(floor(ell N))/T_+(N) -> ell^{-alpha} uniformly on compacts by
`lem:rv`(i) and (LR); the product gives I_+ with the identity (1-p)s = mu_-. The Riemann sum
then converges since I_+ is continuous on the compact interval. The points (1-delta)N < k < N
have L_k > (1 - delta/(1-p))N >= N/2 for delta <= (1-p)/2, so G_N <= C hat G_N <= C T_+(N) and the
additive form bounds their contribution by C delta N T_+(N). The atom T_+(N) at k = N
(zero for a fresh control start) is o(N T_+(N)). Letting delta -> 0 uses only that I_+ is
bounded near v = 1 (I_+(1) = 1/mu_-). For the random-time start, `cor:stationary`(b) gives the
ratio form on the zone with k < N, G^st_N(floor(vN))/T_+(N) -> (1/mu_-)[alpha(1-ell)ell^{-alpha-1}
+ 2 ell^{-alpha}] = I_+(v) + ell^{-alpha}/mu_- uniformly on compacts (kappa^st_+ -> 2/mu_-), and
G^st_N(k) <= C T_+(N) on L_k >= N/2 since kappa^st_+ <= (2/s)(1 + mu_+); the atom Q_+(N) is not
negligible and is added. The boundary layer near k = N contributes O(T_+(N)) per point and is
covered by the ratio form. The mirror statement needs eps < p, which is what "with the signs
exchanged" means.

Verdict: proved as written.

### `cor:exposure-tail` (b)

{A_N in {0, N}} is the event that the first cycle covers the N slots; T_+(N) exactly for a
fresh treatment start (`prop:fresh-identity`), Q_+(N) + Q_-(N) exactly for the random-time
start (`prop:first-run`), with Q_sigma(N) ~ N T_sigma(N)/(s(alpha-1)) by `cor:stationary`(a).
The ratio of two sums of positive asymptotically equivalent terms is asymptotic to the ratio
of the asymptotics, so the displayed ratio holds whether or not T_-/T_+ converges (it does,
by `prop:cycle`(c)).

Aged start. `thm:aging`(b) gives P^{(t_a)}_N(N) ~ (N T_+(N)/(s(alpha-1)))(1 - (1+theta)^{1-alpha}),
and its mirror gives the same factor at the minus end, since t_a/N -> theta and alpha are
sign-independent. So the whole ratio is multiplied by 1 - (1+theta)^{1-alpha}:

  P_aged(no switch)/P_fresh+(no switch) ~ (N/(s(alpha-1)))(1 - (1+theta)^{1-alpha})(1 + T_-(N)/T_+(N)).

The sentence "the ratio carries the factor 1 - (1+theta)^{1-alpha} in the first term" is
ambiguous: read as the factor N/(s(alpha-1)) it is right; read as the summand 1 inside the
bracket it is wrong, because the summand T_-/T_+ carries the same factor.

Verdict: proved as written, with the wording of the aged sentence to be fixed (the factor
multiplies both atoms, hence the whole ratio).

### `cor:exposure-mode` (a) and (b)

(a) Fresh start: `thm:mode`(d), last sentence, with (a) of that theorem for the location
pN + O(B_N). Hypotheses (RV), (SPAN) hold by `prop:cycle`(a). Proved as written.

(b) Random-time start: `thm:mode`(d) with alpha_+ = alpha_- = alpha and the stationary initial
run. Aged start with t_a/N -> theta in (0, infinity]: `cor:aged-mode`, whose hypotheses (RV),
(SPAN), fresh start at step 1, hold. Control-only start: the initial run is the forward
recurrence time of the control renewal process, nu_-(d) = T_-(d)/mu_-, nu_+ = 0; the bulk
criterion B_n T_-(n)/mu_- -> 0 holds, Q_-(N) is in RV_{1-alpha}, Q_+ = 0, and `thm:mode`(c)
gives the threshold alpha - 1 < 1/alpha for the minus endpoint while the plus endpoint never
competes. "Single most likely value" is the endpoint with the larger atom; with
lambda_+ != lambda_- the two atoms are eventually ordered since kappa_sigma is strictly
increasing in lambda_sigma. Proved as written.

### `cor:exposure-mode` (c)

Statement: if Y satisfies (LD2), the start is fresh or fair, the no-tie condition of
`thm:ends` holds at both ends and "each end profile u_mp(j), j >= 1, has a single local
maximum", then A_N has exactly 3 modes for all large N, "the bulk mode and the two no-switch
outcomes"; the last condition holds when f_pm is strictly log-convex.

Count. `thm:mode-count` and `cor:three-modes` apply once (SPAN), (LR), (LD2), (EQ) hold, which
`prop:cycle` provides. `cor:three-modes` asks that each end profile, in the paper's sense
kappa~_pm = (kappa~_pm(0), u_mp(1), u_mp(2), ...) with kappa~_pm(0) in {1, 0, 1/2}, has exactly
one local maximum. The corollary's hypothesis is about the sequence (u_mp(j))_{j >= 1} without
the j = 0 term. For general run laws the two conditions differ: the paper's own example with
f(1) = 0.6, f(2) = 0.3 has u(1) = 0.6 < u(2) = 0.66 and u decreasing afterwards, so
(u(j))_{j >= 1} has a single local maximum while the fresh profile (1, 0.6, 0.66, ...) has two
and P_N has at least four modes (`thm:modes-lower`, as the paper states after
`lem:one-max`). The proof of (c) does not bridge this gap. For cycle laws of the queue the
bridge exists: u_C(1) = 1 - lambda and u_C(2) = f_C(2) + f_C(1)^2 = lambda(1-lambda) f_Y(1)
+ (1-lambda)^2, so u_C(2) - u_C(1) = -lambda(1-lambda)(1 - f_Y(1)) < 0 since Y is unbounded
under (LR). Hence {1} is a local maximum of (u_C(j))_{j >= 1}; if it is the only one, u_C is
nonincreasing on j >= 1, because a later increase u(i) < u(i+1) would produce a second local
maximum by the argument in the proof of `lem:one-max`(b) (u is eventually strictly
decreasing to 1/mu > 0, so the maximum over [i+1, infinity) is attained after i). Then
`lem:one-max`(a) gives one local maximum of kappa~ for every c_0 in [0,1], in particular for
the fresh start at both ends and the fair start, where c_0 = 1/2 = u(1) is excluded by the
no-tie hypothesis. So the count "exactly 3 modes" is correct under the stated hypotheses,
but by an implication that is not in the paper and that is specific to cycle laws.

Numerical confirmation of the bridge for the paper's parameters (zeta service law, alpha = 3/2,
loads 0.6 and 0.4): u_+(1..8) = 0.6919, 0.6376, 0.6071, 0.5867, 0.5718, 0.5602, 0.5509, 0.5431
and u_-(1..8) = 0.7946, 0.7530, 0.7308, 0.7163, 0.7059, 0.6979, 0.6916, 0.6863, both
decreasing, with u(1) = 1 - lambda.

Location. "The two no-switch outcomes" are A_N = 0 and A_N = N, by the definition in
`cor:exposure-tail`(b). For a fresh treatment start P(A_N = 0) = 0 exactly (`prop:fresh-identity`,
F^+_N(0) = 0), so A_N = 0 is never a mode. The control-end profile of this start is
kappa~_- = (0, u_+(1), u_+(2), ...), whose local maximum is at j = 1 by `lem:one-max`(c) since
0 < u_+(1); by `prop:copy`(b) the third mode of P_N is at A_N = 1, one treated slot followed by
one control cycle covering the rest. This is confirmed by the exact law computed with the
paper's `verify_exposure.py` (fresh treatment start, same parameters): at N = 300 the local
maxima are at k = 1, 171, 300 with P(0) = 0, P(1) = 4.85e-5, P(2) = 4.58e-5; at N = 600 they
are at k = 1, 345, 600. For the fair start, kappa~_pm(0) = 1/2 and u_mp(1) = 1 - lambda_mp, so
the end mode is the no-switch outcome only when lambda_mp > 1/2 (`lem:one-max`(b)); for the
paper's parameters lambda_+ = 0.308 and lambda_- = 0.205, so both end modes of the fair start
are at distance one from the endpoints. `thm:mode-count` itself says only "within distance
J_pm" of the ends, which is consistent with all of this.

Log-convex sentence. `lem:logconvex` gives u_mp strictly decreasing, so the single-maximum
condition holds, and the no-tie condition then reduces to f_C(1) = 1 - lambda != kappa~(0),
automatic for fresh starts and requiring lambda != 1/2 for the fair start, which the
corollary assumes separately. Correct. The paper notes that log-convexity of the
total-progeny law is only checked numerically.

Verdict: the count "exactly 3 modes" is incomplete, with the smallest missing implication:
for cycle laws, a single local maximum of (u_mp(j))_{j >= 1} implies a single local maximum
of the full end profile kappa~_pm, which rests on u_C(2) < u_C(1), that is
lambda(1-lambda)(1 - f_Y(1)) > 0, and `lem:one-max`. The location clause "the bulk mode and the
two no-switch outcomes" is refuted: for every fresh start one of the three modes is at
distance one from the far endpoint (A_N = 1 for a fresh treatment start, where A_N = 0 has
probability zero), and for the fair start the end modes are at the endpoints only when both
arrival probabilities exceed 1/2. Suggested repair: state the hypothesis as "u_mp is
nonincreasing on j >= 1" or "each end profile kappa~_pm has exactly one local maximum", and
replace the location clause by "one within distance one of each end" with the fresh-start
and fair-start cases spelled out.

---

## Summary table

| Claim | Verdict |
|---|---|
| 1. `lem:second-bigjump`, four bounds, dependence on c | proved as written |
| 1. `lem:plus-second` (i) to (iii) from it, including m = 0 | proved as written ((LR) implies (SPAN), not recorded) |
| 2. `prop:cycle` (a) | proved as written (same reading of DDS Thm 9.1 as `lem:local-bigjump`) |
| 2. `prop:cycle` (b) | proved as written |
| 2. `prop:cycle` (c) | proved as written |
| 3. `cor:exposure-bulk` | proved as written |
| 3. `cor:exposure-tail` (a) | proved as written |
| 3. `cor:exposure-tail` (b) | proved as written; aged sentence ambiguous (factor multiplies both atoms) |
| 3. `cor:exposure-mode` (a), (b) | proved as written |
| 3. `cor:exposure-mode` (c), count | incomplete: missing bridge from (u_mp(j))_{j>=1} to kappa~_pm, true for cycle laws via u_C(2) < u_C(1) |
| 3. `cor:exposure-mode` (c), location | refuted: fresh treatment start has P(A_N = 0) = 0 and its third mode is at A_N = 1 (exact law, N = 300, 600: modes at 1, 171, 300 and 1, 345, 600) |
