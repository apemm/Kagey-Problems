# 06. The shape of the law of A_N for 0 < alpha < 2

2026-10-26. Target: one classification of the number and location of the local maxima of
P_N(k) = P(A_N = k), for all large N, across 0 < alpha < 2 and every start, as the closing
theorem of the merged F+G paper. Sources: paperF `sec_shape.tex` (Section 6.5 and
`thm:mode-count`), `sec_modeproofs.tex`; paperG `sec_shape.tex`, `sec_ends.tex`,
`sec_signs.tex`, `sec_initial.tex`; the audits in `research_notes/Paper G infinite mean/` and
`research_notes/Paper F modes O1/`.

Conventions. A local maximum (mode) of a finite sequence is a maximal constant block that beats
both neighbours, an endpoint block needing to beat only its one neighbour (F's convention).
"Count" means the number of modes unless said otherwise.

## 0. Predictions (written before any code was run)

P1. Sibuya laws, T(n) = prod_{i<n}(1 - alpha/i), same alpha for both signs (b = 1), fresh plus
start. The count is M_+ + M_- + m_L with M_+ = 1 (the atom at k = N), M_- = 1 (at k = 1), and
m_L = 0 for alpha < alpha_c = 0.5946, m_L = 1 for alpha > alpha_c. So 2 modes at alpha = 0.3,
0.5 and 3 modes at alpha = 0.7, 0.9, for all N past a few hundred. Bulk mode at N/2 when
m_L = 1.

P2. Same laws, fair start. Profiles (1/2, u(1), u(2), ...) with u(1) = alpha, u strictly
decreasing. One local maximum per profile (at j = 0 if alpha < 1/2, at j = 1 if alpha > 1/2).
Count 2 + m_L.

P3. G's Conjecture `conj:count` fails for an initial run with n nu(n) -> 0 that oscillates:
nu_+(n) proportional to 1/(n log^2 n) on even n only. The bulk then carries a zigzag of
relative size about N^{1-alpha}/log^2 N, and the number of local maxima grows linearly in N.
All other hypotheses of the conjecture hold (Sibuya laws are strictly log-convex, satisfy
(LB), the difference conditions, and the start has W = o(T) and the local law).

P4. At alpha = alpha_c exactly (b = 1, degenerate minimum of L at 1/2) the eventual count is
decided by the sign of a lower-order correction, so a "strict local extremum" hypothesis on L
is not enough: nondegenerate critical points are needed. Guess: the count at alpha_c is 2 for
some laws and 3 for others. Weak prediction.

P5. b != 1: L_{alpha,b} has 1 or 3 critical points for every (alpha, b), never 5, and exactly 1
whenever alpha <= 1/2.

P6. Unequal indices alpha_+ < alpha_- < 1: the minus count j = N - A_N lives on the scale
Lambda_N = a_-(1/T_+(N)), and j / Lambda_N converges to W = Z_+^{-alpha_+/alpha_-} Z_- with Z_+,
Z_- independent positive stable. The density h of W blows up at 0 like w^{alpha_- - 1}; it is
decreasing for alpha_+ small and gains an interior maximum for alpha_+ close to alpha_-.

P7. Mixed indices alpha_+ < 1 < alpha_-: j T_+(N) / mu_- converges to the Mittag-Leffler law
xi = Z_+^{-alpha_+}, whose density is decreasing iff alpha_+ <= 1/2. So the plus-end scale
shows an interior mode iff alpha_+ > 1/2.

P8. Every N, completely monotone (CM) run laws: for the fair start the count is at most 3
for every N (endpoint convention), and for fresh starts the number of interior local maxima
(1 <= k <= N-1) is at most 3 for every N. Weak prediction. Expect total positivity to fail as a
proof route for the reason recorded in O1 (CM kernels are RR_2, not TP_2).

## 1. Results in one page

Status words: **proved** (complete argument here or in F/G), **proved modulo L\*** (complete
except for the named lemma L\* of Section 3.3), **sketch**, **conjecture**, **false**.

| # | Statement | Status |
|---|---|---|
| C | Critical points of L_{alpha,b} for all 0<alpha<1, b>0: three (W) iff \|log b\| < beta_c(alpha), else one (U); beta_c = 0 for alpha <= alpha_c, closed form on (alpha_c, alpha_1), infinite for alpha >= alpha_1 = 0.736484 (the root of alpha = sin pi alpha). Degenerate cases named. Settles G's Remark `rem:unequal`. | **proved** (Sec. 2) |
| A | Exact eventual count for 0<alpha<1, equal indices, b in (0,inf): #modes = M_+ + M_- + m_L, m_L = 1 iff alpha > alpha_c and \|log b\| < beta_c(alpha). Fresh, fair and general starts under a difference condition (S) on the initial run. No antimode in the end layers. | part (i), the count, the profiles, Theorem C: **proved**; layer part (ii): **proved modulo L\***; bulk part (iii): **sketch** (L\* plus routine difference LLTs) |
| A' | Log-convex laws (Sibuya, zeta, every CM law with regularly varying tail), fresh or fair start: exactly 2 + m_L modes. | as A |
| D | Difference strong renewal theorem u(j) - u(j+1) ~ (1-alpha) u(j)/j for log-convex f | **proved** (Sec. 3.2) |
| G1 | G's Conjecture `conj:count` is false: oscillating initial runs satisfying all its hypotheses give a count that grows like N^{2-2 alpha} (alpha >= 1/2) or like N (alpha < 1/2). | **false**: mechanism and exact computation (Sec. 4) |
| G2 | At the degenerate point alpha = alpha_c, b = 1 the count at N <= 3000 is 3 for Sibuya laws and 2 for zeta laws: "each critical point a strict extremum" does not decide the count. | computation (Sec. 4) |
| U | Unequal and mixed indices (plus side heavier, alpha_+ < 1): count M_+ + M_- + m, with m = 1 iff the limit law of the scaled dominated count (W = Z_+^{-alpha_+/alpha_-} Z_-, or the Mittag-Leffler law when alpha_- > 1) has an interior mode; bulk minimum at an explicit x*. Threshold curve from (alpha_1, alpha_1) to (alpha_+, alpha_-) = (1/2, 1). | **conjecture**; ML threshold via f'(0) **proved**; bulk formula agrees with `01_phase_diagram.md` Claim K and with exact laws (Sec. 5) |
| E | Every N, CM laws. "At most 3 modes for every N, fair start" is **false** (5 modes in exact arithmetic at N = 39 and N = 145, same law for both signs; at N = 39 both fresh laws are monotone). Supported conjectures: fresh start, at most 3 interior local maxima for every N; Sibuya laws, at most 3 modes for every N and every fresh or fair start. | counterexamples exact; conjectures supported by exact computation (Sec. 7) |

The closing theorem of the merged paper, in the form I recommend, is in Section 6.

## 2. Theorem C: the critical points of the Lamperti density

Notation of G: 0 < alpha < 1, b > 0, beta = log b, c = cos(pi alpha), t = log((1-x)/x),
L_{alpha,b}(x) = (sin pi alpha / pi) phi(t), phi(t) = (1 + cosh t)/(cosh(alpha t - beta) + c).
Put s = alpha t - beta and R(s) = sinh s/(cosh s + c) (note cosh s + c > 0).

Constants. alpha_c in (0,1) solves cos(pi alpha/2) = alpha (alpha_c = 0.594611644056).
alpha_1 in (1/2,1) solves alpha = sin(pi alpha) (alpha_1 = 0.736484448242). For
alpha_c < alpha < alpha_1 put

    w_+(alpha) = -cos(pi alpha) + alpha sin(pi alpha)/sqrt(1 - alpha^2),   s_0 = arccosh w_+,
    beta_c(alpha) = 2 alpha artanh( alpha sinh(s_0)/(w_+ + c) ) - s_0,

and beta_c = 0 for alpha <= alpha_c, beta_c = +inf for alpha >= alpha_1.

**Theorem C.** (a) If |beta| < beta_c(alpha), L_{alpha,b} has exactly three critical points: a
strict minimum, a strict maximum and a strict minimum (W shape). (b) If |beta| > beta_c(alpha), it
has exactly one, a strict minimum (U shape); for alpha <= alpha_c this holds for every b. (c) All
critical points are nondegenerate, except in two cases: alpha = alpha_c and b = 1 (one critical
point, at x = 1/2, with L''(1/2) = 0); alpha_c < alpha < alpha_1 and |beta| = beta_c(alpha) (a
strict minimum and one double critical point at which the monotonicity does not change).

Values: beta_c(0.6) = 0.00589, beta_c(0.65) = 0.2353 (b_c = 1.2653), beta_c(0.7) = 0.8648
(b_c = 2.3745), beta_c(0.72) = 1.4765 (b_c = 4.378), beta_c(0.735) = 3.2915 (b_c = 26.88). G's
Remark `rem:unequal` reports 3 critical points at alpha = 0.7 for b = 1, 2 and 1 for b = 3, which
fits b_c(0.7) = 2.3745.

*Proof.* Step 1 (reduction). phi'/phi = tanh(t/2) - alpha R(s), so the critical points of phi are
the zeros of k(t) = tanh(t/2) - alpha R(alpha t - beta), and phi' has the sign of k. Since
k(t) -> +-(1 - alpha) as t -> +-inf, phi decreases near -inf and increases near +inf. So if there
are three zeros, all simple, they are a minimum, a maximum and a minimum. The map x <-> t is a
decreasing diffeomorphism, which keeps the types.

Step 2 (the function H). s = alpha t - beta is an increasing bijection in t. A zero needs
|alpha R(s)| < 1. On D = {s : alpha |R(s)| < 1} write
k = tanh((s + beta)/(2 alpha)) - tanh(artanh(alpha R(s))); since tanh is increasing, k has the sign
of beta - H(s), where

    H(s) := 2 alpha artanh(alpha R(s)) - s.

So the critical points of L correspond bijectively to the solutions of H(s) = beta in D, and a
zero of k is simple iff H'(s) != 0 there. Outside D, alpha R >= 1 > tanh (for s > 0) or
alpha R <= -1 (for s < 0), so k has no zero there.

Step 3 (the sign of H'). R'(s) = (1 + c cosh s)/(cosh s + c)^2, and with w = cosh s,

    2 alpha^2 R' - (1 - alpha^2 R^2) = -Q(w)/(w + c)^2,
    Q(w) = (1 - alpha^2) w^2 + 2c(1 - alpha^2) w + c^2 - alpha^2 = (1 - alpha^2)(w - w_-)(w - w_+),

with w_+- = -c +- alpha sin(pi alpha)/sqrt(1 - alpha^2). Since -c <= 1, w_- < 1 <= cosh s. Hence
H'(s) > 0 iff cosh s < w_+, and H'(s) < 0 iff cosh s > w_+. Moreover w_+ > 1 iff alpha > alpha_c:
with sin(pi alpha) = 2 sin(pi alpha/2) cos(pi alpha/2) and 1 + c = 2 cos^2(pi alpha/2), w_+ > 1 reads
alpha sin(pi alpha/2) > cos(pi alpha/2) sqrt(1 - alpha^2), that is alpha^2 > cos^2(pi alpha/2). At
s = 0 this is the sign of G's chi(0+) = 2(cos(pi alpha/2) - alpha)(cos(pi alpha/2) + alpha).

Step 4 (the domain). R is odd. If c >= 0, R increases to 1 and D = R. If c < 0, R increases on
[0, s_m] (cosh s_m = -1/c) to R_max = 1/sin(pi alpha) and then decreases to 1. So D = R iff
alpha < sin(pi alpha), that is alpha < alpha_1 when alpha > 1/2. For alpha >= alpha_1, D is R minus
two closed intervals +-[s_1, s_2] around +-s_m (single points when alpha = alpha_1); H -> +inf at both
edges of the positive interval (alpha R -> 1 from below) and H -> -inf at both edges of the negative
one. In all cases H is odd and H(s) -> -+inf as s -> +-inf (alpha R -> +-alpha, artanh bounded).

Step 5 (counting). alpha <= alpha_c: D = R (as alpha_c < alpha_1) and H' < 0 off s = 0, so H is a
decreasing bijection of R and H = beta has exactly one solution, simple unless s = 0 and
H'(0) = 0, that is alpha = alpha_c and beta = 0. alpha_c < alpha < alpha_1: D = R, H' > 0 on
(-s_0, s_0) and H' < 0 outside, so H has a local minimum -H(s_0) at -s_0 and a local maximum
H(s_0) > H(0) = 0 at s_0, and H = beta has 3, 2 or 1 solutions according as |beta| <, =, > H(s_0) =
beta_c(alpha); all are simple except the double one at +-s_0 in the case of equality.
alpha >= alpha_1: on (0, s_1), H rises from 0 to +inf, so H' cannot be negative just below s_1, so
s_0 >= s_1 and H' > 0 on (-s_1, s_1); on (s_2, inf), H falls from +inf, so s_0 <= s_2 and H' < 0
there, and likewise on (-inf, -s_2). Each of the three components of D carries exactly one
solution, all simple. QED.

Checked numerically (`lamperti_critical.py`, output in the run log): the zero count of the
exponential sum E(t) = sinh t (cosh s + c) - alpha sinh s (1 + cosh t), which has the sign of phi',
agrees with the closed form on the grid alpha = 0.02, ..., 0.98, |beta| <= 6, step 0.05, and flips
between beta_c(0.7) - 10^-3 and beta_c(0.7) + 10^-3.

Remarks. (i) For b = 1 this is G's Theorem `thm:shape`. (ii) As alpha increases to alpha_1,
b_c -> inf. This matches Section 5: for equal indices with T_-/T_+ -> 0 the dominated count has
the ratio density K_alpha(w) = (sin pi alpha/pi) w^{alpha-1}/(w^{2 alpha} + 2 w^alpha cos pi alpha + 1),
which has an interior mode iff alpha > sin(pi alpha) (the numerator of its log-derivative is
-(1+alpha) r^2 - 2cr - (1-alpha) in r = w^alpha, with a positive root iff c^2 > 1 - alpha^2 and
c < 0). (iii) Descartes' rule for exponential sums applied to E gives at most 3 zeros only for
alpha <= 1/2 (at most 5 for alpha > 1/2); the function H is what closes the gap.

## 3. Theorem A: the exact eventual count for 0 < alpha < 1

### 3.1 Hypotheses and statement

- (H1) T_+ in RV_{-alpha}, 0 < alpha < 1, T_-(n)/T_+(n) -> b in (0, inf).
- (H2) (SPAN), (LR) f_s(n) ~ alpha T_s(n)/n, and (LD2) |f_s(n+1) - 2f_s(n) + f_s(n-1)| =
  O(f_s(n)/n^2), for both signs. (LR) implies Doney's condition (LB) of G, hence (SRT). (LR) and
  (LD2) give f(n) - f(n+1) ~ (1+alpha) f(n)/n (F, Lemma `lem:ld2`; I checked that its proof does not
  use alpha > 1).
- (H3) (DSRT_s) u_s(j) - u_s(j+1) ~ (1 - alpha) u_s(j)/j for both signs. Holds for log-convex f_s
  (Lemma D below).
- (H4) (S) for the initial run: |nu_s(n+1) - nu_s(n)| = o(n^-2), |nu_s(n+1) - 2nu_s(n) + nu_s(n-1)| =
  o(n^-3), and kappa~_s(0) := lim Q_s(N)/T_s(N) exists in [0, inf]. Fresh and fair starts satisfy
  (S), since |Delta f(n)| ~ (1+alpha) f(n)/n = O(n^{-2-alpha}). So does every smooth regularly
  varying nu, e.g. nu ~ n^{-1-gamma} for any gamma > 0, or nu ~ 1/(n log^2 n).
- (H5) No tie. The plus-end profile is kappa~_+ = (kappa~_+(0), kappa_+(1), kappa_+(2), ...) with
  kappa_+(j) = pi_+ u_-(j) + (nu_- * u_-)(j) (G eq. `eq:kappa-prep`). Let J_+ be such that kappa~_+ is
  strictly decreasing on [J_+, inf) (it exists by Lemma P), and assume kappa~_+(j+1) != kappa~_+(j) for
  j < J_+. The same at the minus end.
- (H6) (alpha, b) is not degenerate in the sense of Theorem C(c).

M_+- is the number of local maxima of kappa~_+- (a value +inf at j = 0 counts as a maximum).
m_L in {0, 1} is the number of interior local maxima of L_{alpha,b} (Theorem C).

**Theorem A.** Under (H1)-(H6), for all large N:

- (i) for 0 <= j < J_+, D_N(j) = P_N(N-j-1) - P_N(N-j) has the sign of kappa~_+(j+1) - kappa~_+(j);
- (ii) for every small enough epsilon > 0, D_N(j) < 0 for J_+ <= j <= epsilon N: P_N increases
  strictly towards the plus end through the whole layer, and there is no antimode in the layer;
- (iii) on [epsilon N, (1 - epsilon) N] the sign of Delta P_N(k) is that of L'(k/N) away from the
  critical points c_i of L, and it changes exactly once near each c_i, at k = (c_i + o(1)) N;
- (iv) the mirror of (i) and (ii) holds at the minus end.

Hence P_N has exactly M_+ + M_- + m_L modes: M_+ within J_+ of N, M_- within J_- of 0, and m_L at
(x_max + o(1)) N, where x_max is the interior maximum of L. Between the end blocks lie exactly
1 + m_L further local minima, at (c + o(1)) N for the minima c of L.

The count from (i)-(iv) is F's argument (`thm:mode-count`, proof of the count): the sign sequence
of D_N, read in j, is sigma_+ (-)^a [bulk] (+)^d bar(sigma_-), where the bulk block is empty for U
(the single change - to + is the minimum of L) and is (+)^{b'}(-)^{c'} for W. The pairs (+,-), a
first sign - and a last sign + count the local maxima: M_+ from sigma_+ followed by minus signs, M_-
from the mirror, and m_L from the bulk. This is complete given (i)-(iv).

For log-convex laws and fresh or fair starts, M_+ = M_- = 1 by F's Lemma `lem:one-max` (its proof
uses only that u is strictly decreasing with a limit; here the limit is 0), and the no-tie
condition holds when f(1) != 1/2 for the fair start. This gives **A'**: exactly 2 + m_L modes.
Fresh plus: at k = 1, at (x_max + o(1)) N when m_L = 1, and at k = N. Fair: at k = N or N - 1
according as f_-(1) < 1/2 or f_-(1) > 1/2, at k = 0 or 1 according as f_+(1) < 1/2 or > 1/2, and
the bulk mode when m_L = 1.

Comparison with 1 < alpha < 2 (F): there the count is M_+ + M_- + 1 and each layer carries an
antimode at x_* Lambda_N, because u_- tends to 1/mu_- > 0 and the first-order correction c_a/N
wins at j of order Lambda_N. For alpha < 1, u_-(j) -> 0, the relative corrections in the layer are
O((j/N)^alpha), the layer is monotone, and the antimode moves into the bulk, where it is the
minimum (or the two minima) of L.

### 3.2 Proved ingredients

**Part (i)** is G Theorem `thm:initial`(f) (the window condition W^+_N = o(T_+(N)) holds because
n nu(n) -> 0 under (S)) together with F Proposition `prop:copy`. Proved.

**Lemma D (difference renewal theorem, log-convex case).** Let f be log-convex on n >= 1, f(1) > 0,
T in RV_{-alpha}, 0 < alpha < 1. Then u(j) - u(j+1) ~ (1-alpha) u(j)/j.

*Proof.* A log-convex f that tends to 0 is nonincreasing, so f(n) <= 2T(n/2)/n <= C T(n)/n. This is
(LB), and Doney's theorem (G Lemma `lem:cd`(iii)) gives (SRT), so u is regularly varying with index
alpha - 1. By de Bruijn and Erdos (cited in G, Section `sec:signs`) u is log-convex, so
r_j = u(j+1)/u(j) is nondecreasing, and r_j <= 1 since u -> 0. For lambda > 1,
log u(floor(lambda j)) - log u(j) = sum_{i=j}^{floor(lambda j)-1} log r_i lies between
(floor(lambda j) - j) log r_j and (floor(lambda j) - j) log r_{floor(lambda j)}, and it tends to
(alpha - 1) log lambda. Hence limsup j log r_j <= (alpha-1) log(lambda)/(lambda-1), and, applying the
other inequality at j/lambda, liminf j log r_j >= (alpha-1) lambda log(lambda)/(lambda-1). Let
lambda -> 1. QED. For Sibuya laws r_j = (j+alpha)/(j+1) exactly.

**Lemma P (the profile under (S)).** Under (H1), (SPAN), (DSRT_-) and (S),
kappa_+(j+1) - kappa_+(j) = (1 + o(1)) (u_-(j+1) - u_-(j)). In particular kappa~_+ is eventually
strictly decreasing and J_+ exists.

*Proof.* Delta kappa_+(j) = pi_+ Delta u(j) + sum_{d<=j} nu_-(d) Delta u(j-d) + nu_-(j+1), with
Delta u(0) = u(1) - 1. The part d <= j/2 is (pi_- + o(1)) Delta u(j) by dominated convergence, since
Delta u is regularly varying by (DSRT). Using sum_{i<j/2} Delta u(i) = u(ceil(j/2)) - 1, the rest is
R = sum_{0<=i<j/2} (nu_-(j-i) - nu_-(j+1)) Delta u(i) + nu_-(j+1) u(ceil(j/2)). With
delta_j = sup_{[j/2, j+1]} |Delta nu_-| = o(j^-2) and sum_{i<=j} (i+1)|Delta u(i)| <= C j u(j),
|R| <= C delta_j j u(j) + o(1/j) u(j/2) = o(u(j)/j), while |Delta u(j)| ~ (1-alpha) u(j)/j. QED.

### 3.3 Part (ii): the layer, and the missing lemma L\*

**Lemma L\* (difference local large deviations, 0 < alpha < 1).** Assume (SPAN), (LR) and (LD) for one
sign, and let V_m = f^{*m}. There is C such that for all m >= 1 and n >= a_m,

    |V_m(n-1) - V_m(n)| <= C m f(n)/n.

This is the alpha < 1 form (no centering) of F's Lemma `lem:diff-bigjump`, and the difference form
of Doney's bound V_m(n) <= C m T(n)/n (G Lemma `lem:cd`(v)). What is known: for bounded m it follows
from (LD) by the decomposition at the first giant summand (F `lem:plus-diff`(ii)); when a_m is
comparable to n it follows from the difference local limit theorem sup_y |V_m(y-1) - V_m(y)| <=
C a_m^-2 (Fourier, from SPAN and RV only). In between (m T(n) small but not polynomially small) the
truncated-sum bound used in F `lem:plus-diff`(ii) is too weak, because (m T(n/K))^K does not tend
to 0. F proves the corresponding statement for 1 < alpha < 2 in `app:diff-bigjump`, with a Fourier
estimate for truncated sums (`lem:trunc-local`). I expect that proof to carry over to alpha < 1
but have not checked it. This is the one missing lemma of Theorem A(ii).

Consequences used below (from L\*, Doney's level bound and Fourier):

- (P1) |V_{m+1}(n) - V_m(n) - f(n)| <= C f(n)(m T(n) + o(1)) for n >= 2 a_m. Indeed
  V_{m+1}(n) - V_m(n) = sum_x f(x)(V_m(n-x) - V_m(n)); the part x <= n/2 is at most
  C m (f(n)/n) sum_{x<=n/2} x f(x) <= C m T(n) f(n) by L\* and sum_{x<=n} x f(x) <= C n T(n); the
  part x > n/2 is f(n)(1 + o(1)) P(S_m < n/2) + O(m f(n) T(n)).
- (P2) |q_{m+1}(n) - T(n)| <= C m T(n)^2 for n >= 2 a_m (level bound only: split
  q_{m+1}(n) - T(n) = sum_{x<n} V_m(x)(T(n-x) - T(n)) - T(n) P(S_m >= n) at x = n/2, and use
  E[min(S_m, n)] <= C m n T(n)).
- (P3) |u_m(x-1) - u_m(x)| <= C a_m^-2 exp(-c m T(x)) for all m and x: write u_m = u_{m-k} * u_k
  with k = ceil(m/2), and use sup |nabla u_k| <= C a_k^-2 and P(S_{m-k} <= x) <= exp(-(m-k) T(x))
  (G `lem:sums`(ii)).
- (M) sum_m m |u^-_m(j+1) - u^-_m(j)| <= C u_-(j)/(j T_-(j)) (L\* for m <= 1/T_-(j), (P3) beyond),
  and v(j) := sum_m m u^-_m(j) = (u*u)(j) - u(j) <= C u_-(j)/T_-(j).

**Theorem L (layer differences).** Assume (H1), (H2), and L\* for both signs; fresh plus start. For
every eta > 0 there are K, epsilon > 0 and J such that for all large N and J <= j <= epsilon N,

    |D_N(j) - T_+(N) (u_-(j+1) - u_-(j))| <= eta T_+(N) u_-(j)/j.

With (DSRT_-) this gives D_N(j) < 0 there, which is Theorem A(ii).

*Proof (modulo L\*).* Write a_m = u^-_m, V_m = u^+_m, Q_m = q^+_{m+1}, b_m = q^-_m and n = N - j. By
the fresh identity (G `prop:fresh-identity`), P_N(N-j) = sum_m [a_m(j) Q_m(n) + V_m(n) b_m(j)], and
D_N(j) = I + II + III + IV as in F `thm:first-diff`, with
I = sum Delta a_m(j) Q_m(n-1), II = sum a_m(j)[Q_m(n-1) - Q_m(n)], III = sum V_m(n-1) Delta b_m(j),
IV = sum [V_m(n-1) - V_m(n)] b_m(j).
The minus weights are negligible for m > K/T_-(j): a_m(j) <= C a_m^-1 e^{-c m T_-(j)} and
b_m(j) <= C T_-(j) e^{-c m T_-(j)} (G `lem:sums`(iii), `lem:decay`), so these m contribute
O(e^{-cK}) T_+(N) u_-(j)/j (with (P3) for Delta a_m). For m <= K/T_-(j) we have
a^+_m <= C K^{1/alpha} j <= n/4 once epsilon <= c K^{-1/alpha}, so (P1), (P2) and L\* apply at n and n-1.

I. I = T_+(n-1) Delta u(j) + sum_m Delta a_m(j)(Q_m(n-1) - T_+(n-1)). By (P2) and (M) the error is at
most C T_+(N)^2 u(j)/(j T_-(j)) <= C (j/N)^alpha T_+(N) u(j)/j. Also T_+(n-1) = T_+(N)(1 + O(epsilon)).

II. Q_m(n-1) - Q_m(n) = V_{m+1}(n-1) - V_m(n-1), so by (P1) |II| <= C f_+(N)(u(j) + T_+(N) v(j))
<= C f_+(N) u(j) <= C (j/N) T_+(N) u(j)/j.

III. By summation by parts with sum_{m>i} b_m(j) = P(S^-_i < j) (F `thm:first-diff`, fact (5)),
III = sum_i [V_{i+1} - V_i](n-1) u^-_i(j), so |III| <= C f_+(N)(u(j) + T_+(N) v(j)), as for II.

IV. By L\*, |IV| <= C (f_+(N)/N) sum_m m b_m(j) <= C f_+(N)/(N T_-(j)) <= C (j/N)^2 T_+(N) u(j)/j, since
sum_m m b_m(j) <= 1 + U_-(j) <= C/T_-(j).

Choose K with e^{-cK} small, then epsilon small. For the fresh minus start the same computation
applies with Q_m = q^+_m and b_m = q^-_{m+1}; then sum_m Delta b_m(j) = f_-(j), which adds
V_1(n-1) f_-(j) = O(f_+(N) f_-(j)), negligible. For starts in (S) the extra terms come from the
first-run decomposition (G `prop:first-run`). Initial runs of length d <= N/2 leave a remainder walk
to which the same estimates apply, and they turn T_+(N) Delta u_-(j) into T_+(N) Delta kappa_+(j)
(Lemma P). Initial plus runs of length d > N/2 contribute O(sup_{d>N/2} nu(d))/j = o(1/(N j)) to
D_N(j), which is o(T_+(N) u_-(j)/j) for j <= epsilon N. This last step is a sketch: it needs the
bound sum_{n} |Pi^-_n(j+1) - Pi^-_n(j)| <= C/j over remainder lengths n with j <= n <= j/epsilon,
which I checked only at the level of orders of magnitude. QED.

Numerical check (`layer_check.py` -> `layer_check_output.txt`, Sibuya laws, b = 1): the ratio
D_N(j)/(T_+(N) Delta u_-(j)) at j = 5, 20, 50 is 0.952, 0.897, 0.847 (alpha = 0.3, N = 3000, fresh
plus) and 0.969, 0.917, 0.819 (alpha = 0.7), and it rises with N at fixed j (0.930, 0.852, 0.779 and
0.925, 0.778, 0.451 at N = 1000). The fresh minus and fair starts give the same picture. The ratio
falls as j/N grows; for alpha = 0.7 it turns negative near j = 0.085 N, the W minimum 1 - 0.915 of
L (Theorem C), which lies outside every admissible epsilon. DSRT: j (u(j) - u(j+1))/u(j) = 0.6931
and 0.6993 at j = 100 and 1000 for alpha = 0.3.

### 3.4 Part (iii): the bulk (sketch)

**Theorem B.** Under (H1), (H2) and L\* (with its second-order form under (LD2)), for a fresh start,
uniformly for k/N in compact subsets of (0,1),

    N^2 (P_N(k+1) - P_N(k)) -> L'(k/N),   N^3 (P_N(k+1) - 2P_N(k) + P_N(k-1)) -> L''(k/N).

Sketch. Take one and two differences inside G's proof of `thm:local`. In the scaling range
m = t/T_+(N), t in [delta, 1/delta], the differences of u^-_m in j and of q^+_{m+1} in k (note
q_{m+1}(k+1) - q_{m+1}(k) = V_m(k) - V_{m+1}(k), a difference in m) converge after scaling to
-p'_{bt}(1 - x) and to t-derivatives of p_t, by difference local limit theorems in space and in m
(Fourier; SPAN and RV suffice). The Riemann sums give the derivatives of Lambda(x) (G eq.
`eq:Lambda`), which is L. The range t < delta (one giant run) is controlled by L\* and its second
difference form, and contributes O(delta^2) to N^2 Delta P_N. The range t > 1/delta decays
exponentially by (P3) and G `lem:decay`. For starts in (S), the defects D^+-_N of G `thm:initial`(a)
change N^2 Delta P_N by N^2 T(N) [nu(k+1) u_+(k/2) + sum_i (nu(k-i) - nu(k+1)) Delta u_+(i)] + ... =
O(nu(k)/k + sup |Delta nu|) N^2 = o(1) (the computation of Lemma P), and N^3 Delta^2 P_N by o(1)
under the second-difference half of (S). Then (iii) follows from Theorem C: L' != 0 away from the
critical points, and L'' != 0 at them under (H6).

Numerical check (fair start, `layer_check_output.txt`): N^2 Delta P_N at x = 0.2, 0.3, 0.4, 0.45 is
-1.688, -0.681, -0.266, -0.125 against L' = -1.571, -0.635, -0.248, -0.117 (alpha = 0.3, N = 3000),
and 1.435, 1.729, 1.261, 0.697 against 1.413, 1.681, 1.208, 0.666 (alpha = 0.7); both closer than
at N = 1000.

### 3.5 Exact computations for Theorem A

Engine: `shape_engine.py` (the run-start recursion for A(k,j), B(k,j) with direct convolutions;
agrees with the sum over all 2^N sign strings for N <= 12, fresh and general starts, to 1e-14).
Scan: `scan_alpha_lt1.py` -> `scan_alpha_lt1_output.txt`, N = 250, 500, 1000, ..., 3000. The
predicted count is M_+ + M_- + m_L with M_+- read off the computed profiles.

- Sibuya laws, b = 1, fresh plus and fair starts. alpha = 0.3, 0.5 (U): 2 modes at every N, as
  predicted (P1, P2 confirmed). alpha = 0.65, 0.7, 0.9 (W): 3 modes at every N, bulk mode at N/2
  (fair) or N/2 + O(1) (fresh), bulk minima at 0.136 N, 0.085 N, 0.021 N against the minima 0.1388,
  0.085, 0.0216 of L.
- Runs of length >= 2 (zeta(0.7) on n >= 2, b = 1): profile maxima at j = 0, 2, 4 (plus end) and
  at 2, 4 (minus end of the fresh plus start); predicted 6 (fresh plus) and 7 (fair); computed 6 and
  7 at every N from 250 to 3000.
- Unequal tails, same index (minus law p Sibuya(alpha) + (1-p) geometric(1/2), so b = p):
  alpha = 0.7, b = 0.6 (|log b| = 0.51 < 0.865, W): 3 at every N, all three starts.
  alpha = 0.8, b = 0.05 (alpha > alpha_1, so W for every b): 3 at every N, all starts.
  alpha = 0.65, b = 0.5 (|log b| = 0.69 > beta_c = 0.235, U): 3 for N <= 1500, then 2 at N = 2000,
  2500, 3000, for all three starts. The eventual count appears at N = 2000.
  alpha = 0.7, b = 0.25 (|log b| = 1.39 > 0.865, U): still 3 at N = 3000. The bulk maximum drifts
  right (0.718 N, 0.757 N, 0.778 N at N = 1000, 2000, 3000) and N^2 Delta P_N at x = 0.78 moves
  -3.68, -1.83, -0.18. The local law itself is far from converged: N P_N(0.9 N) = 1.55, 1.79, 1.94
  against L(0.9) = 3.38, because the 75% light component adds O(m) = O(N^alpha) steps of finite mean
  against a heavy part of size a(0.25 m), a relative correction of order N^{alpha-1} b^{-1/alpha}.
  Not a counterexample; it shows that the threshold N_0 of Theorem A can be large when b is far
  from 1.
- General starts (`scan_starts.py` -> `scan_starts_output.txt`). F's prepared start (half fresh plus,
  half a minus run of length 3): profile maxima 2 + 1, predicted 4 (alpha = 0.7) and 3 (alpha = 0.3),
  computed 4 and 3 at every N. A smooth heavy start nu_+ ~ n^{-1.2} (then P_N(N) = Q_+(N) >> T(N),
  kappa~_+(0) = inf): predicted 3 and 2, computed 3 and 2 at every N.

## 4. G's Conjecture `conj:count`: two failures and the repair

The conjecture: under the hypotheses of G's Theorem `thm:signs`, (LB_+-), |f(n) - f(n+1)| =
O(f(n)/n) and strictly log-convex run laws, the number of sign changes of Delta P_N equals
sigma_L + sigma_+ + sigma_- for all large N. The hypotheses of `thm:signs` put no smoothness on the
initial run beyond the local law, W^+-_N = o(T(N)), finite limits kappa_+-(0), and eventually
decreasing profiles without ties.

### 4.1 Oscillating initial runs (false for every alpha)

Mechanism. In G `prop:first-run`, the initial plus runs of length d close to k give
P_N(k) contains nu_+(k) T_-(N-k) + sum_{i>=1} nu_+(k-i) F^-_{N-k+i}(i), and F^-_n(i) ~ T_-(n) u_+(i) for
fixed i. If nu_+ = smooth part + alternating part of amplitude a_n, the alternating part enters
P_N(k) with amplitude about a_k T_-(N-k) uhat_+(-1), where uhat_+(-1) = sum_i (-1)^i u_+(i) =
1/(1 - fhat_+(-1)) lies in (1/2, 1]. It does not cancel. The smooth slope is N^-2 L'(k/N), and near a
nondegenerate critical point c of L it is about N^-3 L''(c)(k - cN).

- alpha >= 1/2: take nu_+(n) = c n^{-1-alpha}(1 + eps(-1)^n), eps < 1. Then Q_+(N)/T_+(N) has a
  finite limit, n nu_+(n) -> 0 (local law by G `thm:initial`(c), W = o(T)), and the alternating part
  of kappa_- = nu_+ * u_+ has amplitude O(j^{-1-alpha}) = o(|Delta u_+(j)|) = o(j^{alpha-2}), so
  kappa_- is eventually strictly decreasing. In P_N the zigzag has amplitude ~ N^{-1-2 alpha}, which
  beats the slope on |k - cN| <~ N^{2 - 2 alpha} around every critical point: the count tends to
  infinity.
- alpha < 1/2: take nu_+(n) = c(n^{-1-alpha} + lam (-1)^n n^{alpha-2}) with lam small enough that kappa_-
  stays eventually decreasing. The zigzag has amplitude ~ lam N^-2, of the order of the slope, and
  beats it on a fixed interval around the minimum 1/2: the count grows linearly in N.

All hypotheses of the conjecture hold with Sibuya laws for both signs (strictly log-convex, (LB),
|Delta f| = O(f/n)). Exact computation (`scan_starts.py` -> `scan_starts_output.txt`, initial mass
1/2 at d = 1 and 1/2 on n >= 2, support cut at 2*10^6):

| alpha, start | Q_+(N)/T(N) at N = 1000, 2000, 3000 | profile kappa_- strictly decreasing from | modes at N = 500, 1000, 1500, 2000, 2500, 3000 | conjectured |
|---|---|---|---|---|
| 0.7, eps = 0.9 | 1.710, 1.705, 1.700 | j = 6 | 31, 35, 44, 50, 56, 62 | bounded |
| 0.3, lam = 0.3 | 0.658, 0.641, 0.629 | j = 1 | 54, 110, 167, 223, 281, 338 | bounded |

For alpha = 0.7 the extra modes sit in x < 0.1 (near the W minimum 0.085), near 1/2 and in
x > 0.9; for alpha = 0.3 they fill x in [0.3, 0.6] around the minimum 1/2, as predicted. The
growth for alpha = 0.7 fits N^0.42 over this range against the predicted window exponent 0.6; I did
not pin down the constants. The counts grow without any sign of levelling off.

Deviation from prediction P3: the start written in P3 (mass proportional to 1/(n log^2 n) on even n)
violates the conjecture's own hypothesis that Q_+(N)/T_+(N) has a finite limit (Q_+(N) ~ 1/log N >>
T(N)). I replaced it, before running anything, by the two starts above, which satisfy every
hypothesis.

### 4.2 The degenerate point alpha = alpha_c (b = 1)

`alpha_c_check.py` -> `alpha_c_check_output.txt`, fair start, N = 500, 750, ..., 3000. L has one
critical point, a strict but degenerate minimum at 1/2. Sibuya(alpha_c): 3 modes at every N, the
bulk maximum at N/2 between minima at N/2 -+ w_N with w_N/N = 0.180, 0.151, 0.125, 0.112 at N = 500,
1000, 2000, 3000 (fit w_N/N ~ N^-0.27) and relative depth 4.8e-3 down to 6.0e-4. zeta(alpha_c): 2
modes at every N. At alpha_c -+ 0.005 the Sibuya law has 3 modes at small N and then the count of
Theorem C (2 below, 3 above). So at the degenerate point the count is decided by the next term of the
local expansion, whose sign depends on the law. "Each critical point a strict local extremum" is not
enough; (H6) is the right hypothesis. Whether the Sibuya W at alpha_c persists for all N is open (the
data fit a W whose width shrinks like N^-0.27 and does not close by N = 3000).

### 4.3 The repaired statement

Theorem A is the repair. In G's language: under (H1)-(H6), for all large N,
V((P_N(k+1) - P_N(k))_k) = sigma_L + sigma_+ + sigma_-, with sigma_L = 1 + 2 m_L in {1, 3} given by
Theorem C, and the sign changes are located as in Theorem A. The changes with respect to G's
conjecture: (LR) and (LD2) in place of (LB) and (LD); (DSRT) in place of strict log-convexity (which
implies it, Lemma D); the difference condition (S) on the initial run; nondegenerate critical points
(H6) in place of strict extrema. (S) excludes 4.1 since there |Delta nu_+(n)| ~ n^{-1-alpha} >> n^-2.
(S) is sufficient, not sharp: by the mechanism above an alternating part of amplitude o(n^{alpha-3})
is harmless, while (S) asks o(n^-3) through its second-difference half; the first-difference half
alone would not suffice near the critical points of L.

## 5. Unequal and mixed indices: where one side dominates

Take the plus side heavier: alpha_+ < 1 and either alpha_+ < alpha_- (alpha_- < 1 or 1 < alpha_- < 2),
or alpha_+ = alpha_- with T_-/T_+ -> 0. Then A_N/N -> 1 in probability, and the number of minus steps
j = N - A_N lives on the scale

    Lambda_N = a_-(1/T_+(N)) if alpha_- < 1,     Lambda_N = mu_-/T_+(N) if alpha_- > 1.

Limit object. The number of plus runs completed by time N is about xi/T_+(N) with
xi = Z_+^{-alpha_+} (Mittag-Leffler; Z_s positive stable with E e^{-l Z} = e^{-l^alpha_s}), and the
minus time is the sum of that many minus runs. So j/Lambda_N -> W, with

    W = Z_+^{-alpha_+/alpha_-} Z_-  (alpha_- < 1),     W = xi  (alpha_- > 1),
    E W^s = Gamma(1 - s/a_-) Gamma(1 + s/a_-) / (Gamma(1 - s) Gamma(1 + (a_+/a_-) s)),  |s| < a_-,

the second case being the formula with a_- = 1 (E xi^s = Gamma(1+s)/Gamma(1 + a_+ s)). For
a_+ = a_- = a this is sin(pi s)/(a sin(pi s/a)), the Mellin transform of K_a of Section 2.

Conjectured shape (U). Plus end: the profile kappa~_+ (fixed j; proved, G `thm:ends`(a) needs only RV
of T_+), then the layer T_+(N) u_-(j), then the mesoscale P_N(N - j) ~ Lambda_N^-1 h(j/Lambda_N), h the
density of W. Bulk (one giant minus run, in progress at N or completed):

    P_N(xN) ~ (sin pi a_+ / pi) (T_-(N)/(N T_+(N))) G(x),
    G(x) = x^{a_+ - 1} (1 - x)^{-a_- - 1} ((1 - x) + (a_-/a_+) x),

which is Claim K of `01_phase_diagram.md` (derived independently there; the two formulas agree with
v = 1 - x). G has exactly one critical point, a minimum x*: its critical-point equation is the
quadratic (a_+ - 1)(1-x)(1 + (r-1)x) + (a_- + 1) x (1 + (r-1)x) + (r-1) x (1-x) = 0, r = a_-/a_+, with
values of opposite signs at 0 and 1. Minus end: T_-(N) u_+(k), which joins G as x -> 0. Hence:

**Conjecture U.** Under (LR), (LD2), (SPAN) and (DSRT) for alpha_s < 1 (F's hypotheses for
alpha_s > 1), for fresh, fair and (S) starts, P_N has exactly M_+ + M_- + m_h modes for all large N,
where m_h = 1 iff h has an interior mode. The minima are the profile minima, one bulk minimum at
(x* + o(1)) N, and, when m_h = 1, one antimode on the plus side at the scale Lambda_N (alpha_- < 1;
it is the interior minimum of h) or at the smaller scale a_-(1/T_+(N)) (alpha_- > 1, as F's
antimode, because h(0) is finite and u_- -> 1/mu_-). The mesoscale mode is at (w* + o(1)) Lambda_N
from N.

The shape of h (`mixed_index.py` -> `mixed_index_output.txt`, Mellin inversion along Re s = 0,
checked against K_a to 1e-14):

- Mittag-Leffler case (alpha_- > 1). f(x) = sum_k (-x)^k/(k! Gamma(1 - a - a k)) gives f(0) =
  1/Gamma(1-a) and f'(0) = -1/Gamma(1 - 2a), positive iff a > 1/2 (proved). Numerically f' has one
  sign change for a = 0.55, ..., 0.95 and none for a = 0.3, 0.45, 0.5 (at a = 1/2,
  f(x) = exp(-x^2/4)/sqrt(pi), a half-normal density). So m_h = 1 iff alpha_+ > 1/2. The same threshold is in
  `01_phase_diagram.md`.
- alpha_- < 1. Smallest alpha_+ (step 0.01) with an interior mode of h: none for alpha_- = 0.6,
  0.7; 0.74 at alpha_- = 0.74; 0.73 (0.76), 0.71 (0.80), 0.67 (0.85), 0.64 (0.90), 0.60 (0.95), 0.56
  (0.98). The curve starts at the diagonal point (alpha_1, alpha_1), alpha_1 = 0.7365, where K_a gains
  its mode (Section 2, Remark (ii)), and tends to alpha_+ = 1/2 as alpha_- -> 1, the
  Mittag-Leffler threshold. So the extra mode exists in a region bounded by these two thresholds,
  and the picture is continuous across alpha_- = 1.

Exact laws (Sibuya plus side; minus side Sibuya or zeta(1.5)), N = 500, ..., 3000, both fresh
starts:

| (alpha_+, alpha_-) | m_h predicted | modes computed | bulk minimum (N = 3000) vs x* | P_N / bulk formula at x = 0.2, 0.4, 0.6, 0.8 (N = 3000) |
|---|---|---|---|---|
| (0.75, 0.95) | 1 | 3 at every N: 1, 2453, 3000 (mesoscale mode at j = 547; N^0.79 = 550) | 0.076 vs 0.103 (drifting up) | 1.22, 1.62, 3.3, 16.9 (scales not separated) |
| (0.3, 0.9) | 0 | 2 at every N | 0.188 vs 0.185 | 0.96, 0.96, 0.97, 1.02 |
| (0.7, 1.5) | 1 | 3 at every N: 1, 2490, 3000 | 0.058 vs 0.080 (drifting up) | 1.36, 2.09, 8.6, 54 (scales not separated) |
| (0.4, 1.5) | 0 | 2 at every N | 0.120 vs 0.122 | 1.02, 1.05, 1.13, 1.43 |

So the counts agree with Conjecture U at every computed N. The bulk formula is confirmed where the
mesoscale is well below N; for (0.75, 0.95) and (0.7, 1.5) the mesoscale (N^0.79 and N^0.7) is still
of order N at N = 3000 and the bulk ratio is far from 1 near x = 1.

What a proof needs. The end profiles are proved. The mesoscale local limit P_N(N - j) ~
Lambda_N^-1 h(j/Lambda_N) and the bulk formula are local limit theorems of the type of G
`thm:local` and F `thm:bigjump`; `01_phase_diagram.md` has the level statements. The count needs
their difference forms (as Theorem L and Theorem B), the uniqueness of the mode of h (numerical only
here; for the Mittag-Leffler law I used only f'(0) and a numerical check of a single sign change of
f'), and the junction estimates. Status: conjecture.

1 < alpha_+ < alpha_- < 2 (F without (EQ)). F's parts (i)-(iii) do not use (EQ) and hold; the bulk
is governed by the heavier side, a totally skewed alpha_+-stable density, which is bell-shaped (F's
Lemma `lem:bell`). Conjecture: M_+ + M_- + 1 modes, as in F. Not computed here.

## 6. The closing theorem (recommended form)

**Theorem (the shape of the law of A_N).** Let the run laws satisfy (SPAN), (LR) and (LD2) with
indices alpha_+, alpha_- in (0,1) union (1,2), the renewal sequences of the signs with index < 1
satisfy (DSRT) (true for log-convex laws), and let the start satisfy (S) and the no-tie condition.
Let M_+ and M_- be the numbers of local maxima of the end profiles kappa~_+ and kappa~_-. Then for all
large N the number of modes of P_N is M_+ + M_- + m, where:

1. 1 < alpha_+, alpha_- < 2 with (EQ): m = 1 (F, Theorem `thm:mode-count`; proved);
2. alpha_+ = alpha_- = alpha < 1, T_-/T_+ -> b in (0, inf), (alpha, b) nondegenerate: m = 1 iff alpha > alpha_c
   and |log b| < beta_c(alpha) (Theorem A with Theorem C; proved modulo L\* and the bulk sketch);
3. the plus side heavier (alpha_+ < 1 and alpha_+ < alpha_-, or equal indices with T_-/T_+ -> 0): m = 1
   iff the density h of W has an interior mode; for alpha_- > 1 this is alpha_+ > 1/2 (Conjecture U);
4. 1 < alpha_+ < alpha_- < 2: m = 1 (conjecture);

and the mirror statements with the signs exchanged. The M_+ (M_-) end modes are within a bounded
distance of N (of 0); in case 2 the interior mode, when present, is at the maximum of L_{alpha,b} and
there is no antimode in the layers; in cases 1, 3 (with m = 1) and 4 the interior mode is separated
from each end block by one antimode.

For log-convex laws with a fresh or fair start, M_+ = M_- = 1, and the count is 3 in case 1, 2 or 3
in case 2, and 2 or 3 in case 3. The two phase lines are alpha_c (with its b-window beta_c) for
balanced infinite means, and the threshold curve of Section 5 (ending at alpha_+ = 1/2) when one
side dominates; they meet at the diagonal point alpha_1 (beta_c(alpha) -> inf as alpha -> alpha_1).

If the paper wants only proved statements: item 1, item 2 conditional on L\* (stated as such, with the
bulk part written out), Theorem C in full, and items 3, 4 as conjectures with the computations.

## 7. Every N for completely monotone run laws

### 7.1 What the computations say

`cm_everyN.py` (random CM laws: finite geometric mixtures with rational parameters, often with an
atom near 1; Sibuya laws; Sibuya plus a geometric atom; the two signs independent or equal). Every
2 <= N <= Nmax, starts fair, fresh plus, fresh minus. Runs: 80 pairs with Nmax = 400, 25 pairs with
Nmax = 1000, 300 pairs with Nmax = 300 (`cm_everyN_output.txt`, `cm_everyN_output2.txt`). Every
violation quoted below was rechecked in exact rational arithmetic (`exact_law` in `cm_everyN.py`, a
hidden chain on (sign, component, count), checked against the engine).

- **Fair start: at most 3 modes for every N is false**, even with the same law for both signs and
  counting interior maxima only. Exact examples (same law for both signs):
  w = (17/42, 17/42, 4/21), theta = (19/20, 49/100, 31/50), N = 39: fair modes at 0, 4, {19,20}, 35, 39,
  while the fresh plus law is increasing (one mode, at 39) and the fresh minus law decreasing.
  w = (9/35, 13/35, 13/35), theta = (49/50, 1/5, 33/50), N = 145: fair modes at 1, 4, {72,73}, 141, 144
  (all interior); fresh plus modes 7, 77, 145; fresh minus 0, 68, 138.
  The largest number of sign changes of Delta P_N for the fair start was 9.
- **Fresh starts: at most 3 interior local maxima held at every N in all 405 law pairs**; the total
  (with the endpoint) reached 4 (the N = 186 example of O1, and e.g. modes 8, 70, 162, 164 at N = 164).
  At most 2 interior maxima is false (e.g. 1, 29, 109 at N = 110, exact).
- **Sibuya laws** (`cm_sibuya_everyN.py` -> `cm_sibuya_everyN_output.txt`; all 36 pairs
  alpha_+ <= alpha_- on {0.1, 0.3, 0.5, 0.6, 0.7, 0.8, 0.9, 0.97}, every N <= 800): at most 3 modes for
  every N and every start (fair, fresh plus, fresh minus). The eventual count is 2 + m (Theorem A',
  Conjecture U); a third mode at small N occurs in some U-cases (e.g. (0.5, 0.5) fair at N = 6) but the
  bound 3 is never exceeded.

### 7.2 The every-N statements I would formulate

**Conjecture E1.** If both run laws are completely monotone and the start is fresh, then for every
N >= 1 the law of A_N has at most three local maxima in {1, ..., N-1} (and so at most four in
{0, ..., N}).

**Conjecture E2.** If both run laws are Sibuya laws (any indices in (0,1)), then for every N and every
fresh or fair start the law of A_N has at most three local maxima.

Both are bounded checks only. E1 is sharp in the sense that 3 interior maxima occur. The fair start
has no every-N bound of this kind: Section 7.1.

### 7.3 Attempts, and where they fail

(a) Mixtures of starts. The fair law is the average of the two fresh laws, and the N = 39 example
shows that the average of an increasing and a decreasing sequence, each with no interior extremum,
can have five modes. So no argument that bounds the count for each fresh start can pass to the fair
start, and any every-N statement must fix the start. This is why E1 counts fresh starts only.

(b) Total positivity of the hidden chain. A CM law is a mixture of geometric laws, so the walk is a
Markov chain on (sign, rate). Take one rate per sign (theta_+, theta_-) and let P^s_N(k) be the
probability of A_N = k with current sign s. One step is
P^+_{N+1}(k+1) = theta_+ P^+_N(k) + (1 - theta_+) P^-_N(k), P^-_{N+1}(k) = theta_- P^-_N(k) + (1 - theta_-) P^+_N(k).
In the interleaved order y_{2k} = P^+_N(k), y_{2k+1} = P^-_N(k) the step matrix is a nonnegative
staircase matrix (rows supported on consecutive columns, moving right), and its only nontrivial 2x2
minors are (1 - theta_+)(1 - theta_-) - theta_+ theta_- = 1 - theta_+ - theta_-. So the step is TP_2
iff theta_+ + theta_- <= 1, the anti-persistent case. The other interleaving is not a staircase. The
U shapes and the extra modes come from persistent runs (theta near 1), where the minor is negative.
So the natural variation-diminishing structure fails exactly in the regime of interest, for one
rate already, before mixing over rates (O1 found no ordering of the rates that helps either).
(c) Even where the step is TP_2, Karlin's variation-diminishing property bounds the sign changes of
y - c, not those of Delta(P^+ + P^-); the modes of the sum are not controlled by those of the
interleaved vector. I found no kernel K and weights with few sign changes such that
Delta P_N = K(weights).
(d) Monotone ratio. For a CM law the renewal sequence u is a Hausdorff moment sequence (Kaluza/Horn),
hence log-convex and decreasing, and the end profiles have one maximum (Theorem A'). This controls the
ends asymptotically but gives no finite-N bound: the extra mode at N - 2 in the N = 186 example is a
finite-N effect of the fast component (theta = 0.1), not a copy of a profile maximum.
Status: no proof; E1 and E2 are conjectures with the evidence above.

## 8. Computations: files and how to reproduce

All scripts run with `py -I <script>` from this folder (each adds its own folder to sys.path).

| script | what | output | time |
|---|---|---|---|
| `shape_engine.py` | exact law (run-start recursion, direct convolutions), brute-force self-test | stdout | 1 s |
| `lamperti_critical.py` | Theorem C: closed form vs zero counts, beta_c values | stdout | 40 s |
| `scan_alpha_lt1.py 3000` | Theorem A counts, Sibuya, unequal tails, runs >= 2 | `scan_alpha_lt1_output.txt` | 2 min |
| `scan_starts.py 3000` | general starts, oscillating counterexamples to `conj:count`, alpha_c | `scan_starts_output.txt` | 3 min |
| `alpha_c_check.py 3000` | degenerate point, Sibuya vs zeta | `alpha_c_check_output.txt` | 1 min |
| `layer_check.py 3000` | Theorem L ratio, DSRT, Theorem B | `layer_check_output.txt` | 30 s |
| `mixed_index.py 3000` | h and Mittag-Leffler shapes, threshold curve, unequal/mixed exact laws, bulk formula | `mixed_index_output.txt` | 3 min |
| `cm_everyN.py Nmax nlaws seed` | random CM laws, every N, exact rechecks | `cm_everyN_output.txt`, `cm_everyN_output2.txt` | 1-4 min |
| `cm_sibuya_everyN.py 800` | Sibuya pairs, every N | `cm_sibuya_everyN_output.txt` | 5 min |

The scans of Sections 3-5 use the exact sign of the floating-point differences and print the
smallest relative gap at a counted extremum; it was at least 7e-10 everywhere, against a rounding
error of order 1e-13. The CM scans of Section 7 treat relative differences below 1e-11 as ties.
Every violation quoted in Section 7 was confirmed in exact rational arithmetic.

## 9. Predictions against outcomes, and the honest status

| prediction | outcome |
|---|---|
| P1 Sibuya, fresh plus: 2 modes (alpha < alpha_c), 3 (alpha > alpha_c) | confirmed at every N in 250..3000 |
| P2 fair: 2 + m_L | confirmed |
| P3 oscillating start breaks `conj:count` | confirmed, with a modified start (Sec. 4.1: the written one violated a hypothesis) |
| P4 alpha_c count law-dependent | confirmed: Sibuya 3, zeta 2 (N <= 3000) |
| P5 L_{alpha,b}: 1 or 3 critical points, 1 for alpha <= 1/2 | confirmed and proved, sharper: 1 for alpha <= alpha_c, and 3 for every b when alpha >= alpha_1 |
| P6 unequal indices: h gains a mode for alpha_+ near alpha_- | confirmed, with the threshold curve; no mode at all when alpha_- < alpha_1 |
| P7 mixed: interior mode iff alpha_+ > 1/2 | confirmed (f'(0) proved, shape numerical) |
| P8 every N: fair <= 3 | **false** (5, exact); fresh interior <= 3 holds in every computed case |

Named missing pieces, in order of importance:

1. Lemma L\* (difference local large deviations for alpha < 1, uniform in m with n >= a_m). Expected to
   follow from F's proof of `lem:diff-bigjump` (truncated-sum Fourier bound) without centering; not
   checked. Theorem L is complete given L\*.
2. Theorem B written out: difference and second-difference local limit theorems in space and in m in
   the scaling range (routine Fourier), plus the second-difference form of L\* under (LD2).
3. For starts in (S): the bound sum_n |Pi^-_n(j+1) - Pi^-_n(j)| <= C/j over remainder lengths
   j <= n <= j/epsilon (initial runs of length > N/2 in the layer); checked at the level of orders only.
4. (DSRT) without log-convexity: I do not know whether (LR) + (LD) imply it for alpha <= 1/2 (G
   raised the same question).
5. Conjecture U and case 4 of Section 6: mesoscale local limit, its difference form, and the
   unimodality of h (numerical here).
6. Every N: Conjectures E1, E2 (no proof; the TP route fails at theta_+ + theta_- > 1).
7. The degenerate cases of Theorem C(c): the count there depends on the law (Sec. 4.2).

What is proved here: Theorem C (all of it), Lemma D, Lemma P, part (i) and the count deduction of
Theorem A, the refutation of `conj:count` as stated (by exact computation together with the
mechanism; the asymptotic growth rate is not proved), and the sign of the Mittag-Leffler derivative at
0. Everything else above is conditional or conjectural as marked.
