# Audit of Paper G, Section `sec_shape.tex` (the shape of the law)

Date: 2026-10-28. Scope: `kagey-problems/problem131/paperG/sec_shape.tex`, read against
`sec_setting.tex` (hypotheses, Proposition `prop:fresh-identity`), `sec_tools.tex`
(Lemmas `lem:cd`, `lem:sums`, `lem:key`, `lem:decay`, `lem:onejump`, `lem:fourier`) and
`sec_initial.tex` (Theorem `thm:initial`(f), `eq:kappa-prep`). The cited lemmas and
`thm:initial`(f) are taken as given with their stated hypotheses; the audit checks that
they are applied within those hypotheses. No file in `paperG` or `paperF` was edited.

Method: each claim was restated as a claim card, the decisive step was re-derived from
the definitions before reading the written argument, and the written argument was then
checked implication by implication. Symbolic and numerical checks were run independently
(`py -I`, scratch folder outside the repository); the scripts are summarised at the end.

Verdict vocabulary: proved as written; correct only after a stated restriction;
conditional on a named input; incomplete, with the smallest missing implication;
refuted, with a counterexample.

## Summary of verdicts

| # | Claim | Verdict |
|---|-------|---------|
| 1 | Theorem `thm:shape` (a)-(c), closed form of beta_c, degenerate cases, remark on the ratio density and alpha_1, pitchfork constant | proved as written |
| 2a | Lemma `lem:dsrt` | statement proved; conditional on the named input de Bruijn-Erdos (1953) Thm 1; the proof text transposes its two one-sided bounds (fixable slip, see below) |
| 2b | Lemma `lem:prep-profile` | proved as written |
| 3a | Theorem `thm:signs` | correct only after a stated restriction: exclude the degenerate pairs alpha_c < alpha < alpha_1, abs(log b) = beta_c(alpha), or define sigma_L as the number of strict local extrema of L. At those pairs the parenthetical "1 or 3 ... each a strict local extremum" is false and the proof fails |
| 3b | Example `ex:counts` | proved as written (the fresh-start sentence implicitly uses that u_{-/+} is strictly decreasing, as the theorem's hypothesis requires anyway) |
| 4 | Lemma `lem:Lstar` | proved as written, up to a restriction to n >= n_0 (or f(n) > 0 for all n), which the uses respect; two harmless constant-level slips noted |
| 5 | Lemma `lem:diffs` (i)-(iii) | proved as written (one cosmetic slip in (i)) |
| 6 | Theorem `thm:layer-diff` | proved as written |
| 7 | Proposition `prop:count`, given (B) | proved as written, given (B); one step needs the one-line bridge J_+ versus the J of `thm:layer-diff` |

---

## 1. Theorem `thm:shape`

### Claim card

Let 0 < alpha < 1, b > 0, beta = log b, c = cos(pi alpha), alpha_c the root of
cos(pi alpha/2) = alpha, alpha_1 the root in (1/2, 1) of sin(pi alpha) = alpha, and
beta_c as in `eq:betac` (0 for alpha <= alpha_c, +infinity for alpha >= alpha_1).
(a) abs(beta) < beta_c: exactly 3 critical points of L, min-max-min.
(b) abs(beta) > beta_c: exactly 1 critical point, a strict minimum; for alpha <= alpha_c
this for every b; for alpha >= alpha_1 (a) for every b.
(c) all critical points nondegenerate except: alpha = alpha_c, b = 1 (L''(1/2) = 0, single
critical point); alpha_c < alpha < alpha_1, abs(beta) = beta_c (one strict minimum and one
double critical point without change of monotonicity).
After the proof: the ratio density `eq:ratio-density` has an interior maximum exactly when
alpha > alpha_1; the pitchfork distance near alpha_c for b = 1; Descartes' rule gives at
most 3 zeros only for alpha <= 1/2.

### Independent derivation (before reading the proof)

Reduction. From `eq:L-cosh`, L(x) = (sin(pi alpha)/pi) (1 + cosh t)/(cosh(alpha t - beta) + c)
with t = log((1-x)/x). I re-derived `eq:L-cosh` from `eq:lamperti-intro`: dividing numerator
and denominator by x^{2 alpha} and using 2 + 2 cosh t = 1/(x(1-x)) gives it. The map x -> t is
a decreasing diffeomorphism, so critical points, their type and their order of degeneracy
correspond.

Logarithmic derivative. d/dt log(1 + cosh t) = tanh(t/2) and d/dt log(cosh s + c) = alpha R(s)
with s = alpha t - beta, R = sinh s/(cosh s + c). So k(t) = tanh(t/2) - alpha R(s), with
k -> -(1-alpha) at -infinity and +(1-alpha) at +infinity.

Zeros of k and the function H. On D = {alpha abs(R) < 1}, k = tanh A - tanh B with
A = (s + beta)/(2 alpha), B = artanh(alpha R), so sign k = sign(beta - H(s)),
H = 2 alpha artanh(alpha R) - s. Off D, abs(alpha R) >= 1 > abs(tanh(t/2)) and k has no zero.
At a zero, dk/ds = sech^2(A)(A' - B') = -sech^2(A) H'(s)/(2 alpha), so nondegenerate iff H' != 0.

H'. R' = (1 + c cosh s)/(cosh s + c)^2 and, with w = cosh s,
2 alpha^2 R' - (1 - alpha^2 R^2) = -Q(w)/(w + c)^2,
Q(w) = (1 - alpha^2) w^2 + 2c(1 - alpha^2) w + c^2 - alpha^2. Verified symbolically (sympy):
identity true; discriminant of Q equals 4 alpha^2 (1 - alpha^2)(1 - c^2); roots
w_pm = -c pm alpha sin(pi alpha)/sqrt(1 - alpha^2); and
H' = [2 alpha^2 R' - (1 - alpha^2 R^2)]/(1 - alpha^2 R^2) is exact. Since w_- < 1 <= cosh s
(c > -1), on D: H' > 0 iff cosh s < w_+, H' < 0 iff cosh s > w_+.
w_+ > 1 iff alpha sin(pi alpha/2) > cos(pi alpha/2) sqrt(1 - alpha^2) iff
alpha^2 > cos^2(pi alpha/2) iff alpha > alpha_c (both sides nonnegative). Numerically
w_+ - 1 = -1.97e-31 at alpha = alpha_c (30 digits), +0.0223 at 0.6, -0.0193 at 0.59.

Domain D. R odd; R' > 0 everywhere if c >= 0; if c < 0, R has its maximum at cosh s_m = -1/c
with R(s_m) = 1/sqrt(1 - c^2) = 1/sin(pi alpha) (checked by hand). So D = R iff
alpha < sin(pi alpha) iff alpha < alpha_1. For alpha >= alpha_1, D is R minus
pm[s_1, s_2] (single points at alpha_1), H -> +infinity at both edges of [s_1, s_2],
H -> -infinity at both edges of [-s_2, -s_1], H odd, H(0) = 0, H(s) -> -/+ infinity as
s -> +/- infinity.

Counting. alpha <= alpha_c: w_+ <= 1 so H' < 0 except possibly at s = 0 (alpha = alpha_c):
H is a decreasing bijection of R, one solution, simple unless alpha = alpha_c and beta = 0;
there s = 0, i.e. t = 0, x = 1/2, and the zero of k still changes sign from - to + (H strictly
decreasing), so it is a strict minimum with L''(1/2) = 0.
alpha_c < alpha < alpha_1: D = R, H' > 0 exactly on (-s_0, s_0), cosh s_0 = w_+. H decreases
from +infinity to -H(s_0) at -s_0, increases to H(s_0) > H(0) = 0, decreases to -infinity.
So H = beta has 3, 2, 1 solutions according as abs(beta) <, =, > H(s_0), all simple except the
one at pm s_0 in the case of equality, where H'' != 0 (Q has a simple root at w_+ and
sinh s_0 != 0), so that zero of k is exactly double and k keeps its sign: a critical point with
no change of monotonicity. H(s_0) = 2 alpha artanh(alpha sinh s_0/(w_+ + c)) - s_0 = beta_c.
The three zeros carry H' < 0, > 0, < 0, so k' > 0, < 0, > 0: min, max, min in t, and the same
order in x (reversal preserves it).
alpha >= alpha_1: on (0, s_1), H -> +infinity at s_1-, so H' cannot be negative on (s_0, s_1)
if s_0 < s_1; hence s_0 >= s_1 and H' > 0 on (-s_1, s_1). On (s_2, infinity) H is finite at
s_0 and -> +infinity at s_2+, so H' > 0 on (s_2, s_0) is impossible; hence s_0 <= s_2 and
H' < 0 there. Each of the three components carries exactly one simple solution for every
beta. Numerically s_1 <= s_0 <= s_2 holds at alpha = alpha_1 (all three equal 0.942753),
0.75, 0.8, 0.9, 0.99.

Brute-force count. From the x-form of L (`eq:lamperti-intro`, not the cosh form) I
computed d/dx log L on a grid in t = log((1-x)/x) of 400001 points on [-60, 60] and counted
sign changes, for alpha in {0.1, 0.3, 0.5, 0.59, 0.5946, 0.6, 0.62, 0.65, 0.7, 0.72, 0.735,
0.7364, 0.74, 0.8, 0.9, 0.97} and b in {0.01, 0.1, 0.3, 0.5, 0.8, 1, 1.25, 2, 2.3, 2.45, 3,
5, 10, 30, 100}: 240 pairs, 0 mismatches with the theorem (the x-form and the t-form of the
derivative agree to 5e-6 on the interior). Fine scan at alpha = 0.7: count 3 at
beta = beta_c - 0.001 and 1 at beta_c + 0.001.

Values. alpha_c = 0.594611644056..., alpha_1 = 0.736484448241...;
beta_c(0.6) = 0.0058892, beta_c(0.65) = 0.235295, beta_c(0.7) = 0.864785,
beta_c(0.72) = 1.476522, beta_c(0.735) = 3.291520; exp(beta_c(0.7)) = 2.374494.
All match the text (the text rounds 0.0058892 to 0.00589 and 2.374494 to 2.3745).

Ratio density. With r = y^alpha, y d/dy log rho = -[(1+alpha) r^2 + 2c r + (1-alpha)] /
(1 + 2c r + r^2) (sympy). The quadratic has product of roots (1-alpha)/(1+alpha) > 0 and
sum -2c/(1+alpha), so it has a positive root iff c < 0 and c^2 >= 1 - alpha^2; two distinct
positive roots (a local minimum then a local maximum of rho) iff c^2 > 1 - alpha^2 iff
alpha > sin(pi alpha) iff alpha > alpha_1 on (1/2, 1). At alpha = alpha_1 the root is
double and rho is monotone with an inflection, so "exactly when alpha > alpha_1" is right.

Pitchfork. chi(t) = cosh(alpha t) + c - alpha sinh(alpha t) coth(t/2) has the sign of k for
t > 0 and b = 1. sympy series: chi = (1 + c - 2 alpha^2) + (alpha^2 (1 - alpha^2)/3) t^2 + O(t^4),
as stated. chi(0+) = 2 cos^2(pi alpha/2) - 2 alpha^2 < 0 iff alpha > alpha_c (t = 0 is then a
maximum). The zero t_* satisfies t_*^2 = 3(2 alpha^2 - 1 - c)/(alpha^2 (1 - alpha^2)) to
leading order, and dx/dt = -1/4 at t = 0, which gives the stated distance. Numerically the
ratio of the true distance to the formula is 0.886, 0.968, 0.993, 0.9986, 0.9997 at
alpha = alpha_c + 0.02, 0.005, 0.001, 0.0002, 0.00005.

Descartes. Multiplying k by (1 + cosh t)(cosh s + c) > 0 gives an exponential sum in t with
exponents 1 + alpha, 1, alpha, 1 - alpha and their negatives and coefficients
(1-alpha)/4, c/2, -alpha/2, (1+alpha)/4, -(1+alpha)/4, alpha/2, -c/2, -(1-alpha)/4. Ordering
the exponents, the sign pattern has 3 changes when c >= 0 (alpha <= 1/2) and 5 when c < 0.
The remark is correct.

### Check of the written proof

Every step of the written proof matches the derivation above. Two points deserve a
remark but are not errors. (i) Case (b) is stated for abs(beta) > beta_c, and for
alpha <= alpha_c with b = 1 one has abs(beta) = beta_c = 0; the added sentence "For
alpha <= alpha_c this holds for every b" covers that case, and the proof does prove it
(H is a decreasing bijection for every beta). (ii) In the case alpha >= alpha_1 the proof
says "H rises from 0 to +infinity" before monotonicity is established; the argument that
follows (H' cannot be negative just below s_1) is the correct one and does not use the
word "rises".

Verdict: proved as written.

## 2a. Lemma `lem:dsrt`

### Claim card

f log-convex on {1, 2, ...}, f(1) > 0, tail T regularly varying with index -alpha in (-1, 0).
Then (LB), (SRT), u strictly decreasing, and u(j) - u(j+1) ~ (1 - alpha) u(j)/j.

### Independent derivation

Positivity. Log-convexity with f(1) > 0 and T > 0 everywhere forces f > 0 everywhere
(a zero followed later by a positive value would make the convexity inequality at the last
zero fail). Then f(n+1)/f(n) is nondecreasing, and since f is summable the ratios stay
below 1, so f is nonincreasing. Hence (n/2) f(n) <= sum_{n/2 <= i <= n} f(i) <= T(n/2), which
is f(n) <= 2T(n/2)/n <= C T(n)/n by (R2): (LB). `lem:cd`(iii) gives (SRT), and u is
regularly varying with index alpha - 1.

Log-convexity of u. This is the external input: de Bruijn and Erdos (1953), Theorem 1
(f log-convex implies the renewal sequence u log-convex). It is not among the lemmas the
audit may take as given, so the lemma is conditional on it. Numerically, for the zeta law
with alpha in {0.3, 0.5, 0.7, 0.9} and j <= 4000, u(j)^2 <= u(j-1) u(j+1) holds at every j and
r_j = u(j+1)/u(j) is nondecreasing, which is consistent with the theorem.

The ratio argument. With r_j nondecreasing and r_j < 1 (u -> 0 and u > 0), for lambda > 1 and
j = floor(i/lambda): (i - j) log r_j <= sum_{l=j}^{i-1} log r_l = log u(i) - log u(j)
<= (i - j) log r_i, and the middle tends to (alpha - 1) log lambda by regular variation.
From the right inequality: i log r_i >= (alpha - 1) log lambda . i/(i - j) + o(1), so
liminf_i i log r_i >= (alpha - 1) lambda log lambda/(lambda - 1).
From the left inequality: j log r_j <= (alpha - 1) log lambda . j/(i - j) + o(1), so
limsup_j j log r_j <= (alpha - 1) log lambda/(lambda - 1).
Both constants tend to alpha - 1 as lambda -> 1, so j log r_j -> alpha - 1, which is
u(j) - u(j+1) = u(j)(1 - r_j) ~ (1 - alpha) u(j)/j.

### Check of the written proof

The proof writes the two one-sided bounds the other way round: "limsup_i i log r_i
<= (alpha - 1) lambda log lambda/(lambda - 1)" and "liminf_j j log r_j >= (alpha - 1) log
lambda/(lambda - 1)". Since alpha - 1 < 0 and lambda log lambda/(lambda - 1) > 1 >
log lambda/(lambda - 1) for lambda > 1, the two displayed inequalities would put the limsup
strictly below the liminf; they are false as written. The right inequality in the chain
gives the liminf bound with the constant lambda log lambda/(lambda - 1), and the left one
gives the limsup bound with log lambda/(lambda - 1). The conclusion is unaffected because
both constants tend to alpha - 1. This is a transposition in the text, not a gap in the
mathematics.

The remark after the lemma: for the Sibuya law u has generating function (1 - z)^{-alpha},
so u(j) = Gamma(j + alpha)/(Gamma(alpha) j!) and r_j = (j + alpha)/(j + 1) exactly, and
T(n) = prod_{i<n}(1 - alpha/i); the zeta law is strictly log-convex. Both correct.

Verdict: statement proved; conditional on the named input de Bruijn-Erdos (1953) Thm 1;
the proof text should swap the two one-sided bounds (liminf with constant
lambda log lambda/(lambda - 1), limsup with constant log lambda/(lambda - 1)).

## 2b. Lemma `lem:prep-profile`

### Claim card

Under (BAL), (SPAN), (DSRT_-) and abs(nu_-(n+1) - nu_-(n)) = o(n^{-2}):
kappa_+(j+1) - kappa_+(j) = (1 + o(1))(u_-(j+1) - u_-(j)); in particular kappa~_+ is
eventually strictly decreasing.

### Independent derivation

From `eq:kappa-prep` with u = u_-, for j >= 1,
Delta kappa_+(j) = pi_+ Delta u(j) + sum_{d <= j} nu_-(d) Delta u(j - d) + nu_-(j+1) u(0),
u(0) = 1 and Delta u(0) = u(1) - 1. (DSRT_-) alone implies that u is regularly varying with
index alpha - 1: u(j+1)/u(j) = 1 - (1 - alpha)/j + o(1/j) gives log u(j) = -(1 - alpha) log j
+ sum o(1/i), and exp(sum_{j < i <= lambda j} o(1/i)) -> 1. Hence Delta u is regularly varying
with index alpha - 2 and eventually negative, so Potter bounds apply to abs(Delta u).
Part d <= j/2: abs(Delta u(j - d)/Delta u(j)) <= C uniformly and -> 1 pointwise, sum nu_- < infinity:
dominated convergence gives (pi_- + o(1)) Delta u(j).
Rest, with i = j - d in [0, j/2): using sum_{i < j/2} Delta u(i) = u(ceil(j/2)) - 1 to rewrite
nu_-(j+1), the rest equals sum_{i < j/2} (nu_-(j - i) - nu_-(j+1)) Delta u(i) + nu_-(j+1) u(ceil(j/2)).
abs(nu_-(j - i) - nu_-(j+1)) <= (i + 1) delta_j with delta_j = o(j^{-2}), and
sum_{i <= j} (i + 1) abs(Delta u(i)) <= C sum_{i <= j} u(i) <= C j u(j) (DSRT, then Karamata with
index alpha - 1 > -1). So the first part is o(u(j)/j). nu_-(j+1) = sum_{m > j} (nu_-(m) - nu_-(m+1))
= o(1/j) by the first half of (S), and u(ceil(j/2)) <= C u(j): the second part is o(u(j)/j).
Total: (1 + o(1)) Delta u(j) + o(u(j)/j) = (1 + o(1)) Delta u(j) since abs(Delta u(j)) ~
(1 - alpha) u(j)/j.

### Check of the written proof

Matches the derivation step for step. The phrase "Delta u is regularly varying by (DSRT_-)"
is right for the reason given above (DSRT implies regular variation of u); it would be
clearer to say so, but nothing is missing.

Verdict: proved as written.

## 3a. Theorem `thm:signs`

### Claim card

Under (BAL), (SPAN), (SRT_pm), a bulk-convergent initial run with W^pm_N = o(T_pm(N)),
finite limits kappa~_pm(0), no ties in kappa~_pm, and kappa~_pm eventually strictly decreasing:
V((P_N(k+1) - P_N(k))_{0 <= k < N}) >= sigma_L + sigma_+ + sigma_- for large N, where sigma_L is
the number of critical points of L, "which is 1 or 3 by Theorem thm:shape, each of them a
strict local extremum".

### Independent derivation

Subsequence principle. For a subsequence (s_{i_l}) of (s_i), each nonzero difference
s_{i_{l+1}} - s_{i_l} is a sum of consecutive differences of (s_i) and one of them has its sign;
picking one such term per block gives a subsequence of the nonzero differences of (s_i) with
the same sign pattern, and sign changes cannot increase on passing to a subsequence. Correct.

Bulk. If the critical points c_1 < ... < c_s of L are strict local extrema alternating
min, max, ..., min (true when s = 1 or s = 3 and the points are nondegenerate), then with
z_0 < c_1 and z_{s+1} > c_s the values L(z_0), L(c_1), ..., L(c_s), L(z_{s+1}) have
differences -, +, -, ..., + with s sign changes, and NP_N(floor(zN)) -> L(z) at these
finitely many points settles the signs for large N.

Ends and junctions. P_N(j)/T_-(N) -> kappa~_-(j) and P_N(N - j)/T_+(N) -> kappa~_+(j) for
0 <= j <= J (thm:initial(f), its mirror, P_N(0) = Q_-(N), P_N(N) = Q_+(N)); kappa~_pm(J) > 0
since the sequence is strictly decreasing from J - 1 with nonnegative terms; bulk values are
O(1/N) = o(T_pm(N)). The junction differences are negative on the left and positive on the
right, and they sit between differences of the same sign, so no change is added or lost.
The plus end read in k is the reversed and negated difference sequence of kappa~_+, with the
same count sigma_+, and all its sign changes occur at indices j <= J - 1.

The gap. Theorem `thm:shape`(c) says that for alpha_c < alpha < alpha_1 and abs(log b) = beta_c
the density has two critical points, a strict minimum and a double critical point at which
the monotonicity does not change. There sigma_L as defined ("the number of critical
points") equals 2, the parenthetical "1 or 3 ... each of them a strict local extremum" is
false, and the proof's statement "the critical points alternate between strict minima and
strict maxima" fails: the values L(z_0), L(c_1), L(c_2), L(z_3) have differences -, +, +,
with one sign change, not two. The proof therefore does not establish
V >= 2 + sigma_+ + sigma_- at those pairs, and nothing in the section does. The theorem has
no hypothesis excluding them.

The repair is a one-line restriction: either assume (alpha, b) is not a degenerate pair of
`thm:shape`(c) (as `prop:count` already does), or define sigma_L as the number of strict
local extrema of L (1 or 3 in every case), with which the proof goes through unchanged.
At alpha = alpha_c, b = 1 there is no problem: the single critical point is a strict minimum.

Verdict: correct only after a stated restriction (exclude abs(log b) = beta_c(alpha) for
alpha_c < alpha < alpha_1, or read sigma_L as the number of strict local extrema).

## 3b. Example `ex:counts`

### Claim card

Zeta law for both signs, b = 1, fair start: kappa~_pm = (1/2, u(1), u(2), ...),
sigma_pm = 1 if f(1) > 1/2 and 0 if f(1) < 1/2, f(1) = 1/zeta(1 + alpha); bounds 1, 1, 3, 5 at
alpha = 0.3, 0.5, 0.7, 0.9. Fresh plus start with different laws: bound sigma_L + 1.

### Check

Q_pm(N) = T(N)/2 and kappa~_pm(0) = 1/2. For j >= 1, kappa_pm(j) = u(j)/2 + (f*u)(j)/2 = u(j) by
the renewal equation. u is strictly decreasing by `lem:dsrt` (zeta law is log-convex with
f(1) > 0). zeta(1.3) = 3.93195, zeta(1.5) = 2.61238, zeta(1.7) = 2.05429, zeta(1.9) = 1.74975,
so f(1) = 0.2543, 0.3828, 0.4868, 0.5715: sigma_pm = 0, 0, 0, 1. sigma_L = 1, 1, 3, 3 (b = 1,
alpha_c = 0.5946). Totals 1, 1, 3, 5. The hypotheses of `thm:signs` hold for the fair start
(mixture of two fresh starts; W^pm_N = o(T(N)); no ties since f(1) != 1/2).

Independent computation of the exact law (fresh-plus identity `eq:fresh`, N = 1500, FFT
convolution powers, total mass 1 to 12 digits): V = 1, 1, 3, 5 for alpha = 0.3, 0.5, 0.7, 0.9,
with modes at {0, 1500}, {0, 1500}, {0, 750, 1500}, {1, 750, 1499}, and
P_N(1)/T(N) = 0.2453, 0.3830, 0.4894, 0.5743 against f(1) above. The bound is attained.

Fresh plus start: kappa~_+ = (1, u_-(1), ...) and kappa~_- = (0, u_+(1), ...) are correct
(Q_+(N) = T_+(N), Q_-(N) = 0, kappa_-(j) = (f_+ * u_+)(j) = u_+(j)). "Is strictly decreasing"
and "has one sign change" need u_- and u_+ strictly decreasing, which is not automatic but
is what the theorem's hypothesis on kappa~_pm already demands; the sentence should say "when
u_pm is strictly decreasing, for instance for log-convex laws".

Verdict: proved as written (with the implicit assumption above made explicit).

## 4. Lemma `lem:Lstar`

### Claim card

alpha_s < 1, (SPAN), (LR), (LD) for one sign; V_m = f^{*m}. There is C with
abs(V_m(n-1) - V_m(n)) <= C m f(n)/n for all m >= 1 and n >= a_m.

### Independent derivation

Case n <= Lambda a_m. `lem:fourier`(ii) with y = infinity: sup abs(nabla V_m) <= C a_m^{-2}.
Potter: m T(n) >= m T(Lambda a_m) >= c_Lambda m T(a_m) >= c_Lambda (m T(a_m) -> 1, all terms
positive). With f(n) >= c T(n)/n: m f(n)/n >= c m T(n)/n^2 >= c_Lambda/(Lambda^2 a_m^2). Done,
with a constant depending on Lambda, which is fixed later in terms of the law.

Case n > Lambda a_m. y = ceil(n/K), I = first index with X_i >= y.
V_m(n) = sum_i P(S_m = n, I = i) + V^{(y)}_m(n).

(A) A summand of size at least y. h_i(z) = P(S_m - X_i = z, X_1, ..., X_{i-1} < y) has mass
<= 1 and is independent of n; X_i is independent of (S_m - X_i, X_1, ..., X_{i-1}), so
P(S_m = n, I = i) = sum_{z <= n - y} h_i(z) f(n - z) and
nabla P(S_m = ., I = i)(n) = sum_{z <= n-1-y} h_i(z)[f(n-1-z) - f(n-z)] - h_i(n - y) f(y).
In the sum w = n - z >= y + 1 > n/K; (LD) at w - 1 and f(w-1) <= C f(w) (regular variation,
w large) give abs(f(w-1) - f(w)) <= C f(w)/w <= C_K f(n)/n (Potter for the regularly varying
f(w)/w on w in [n/K, n]); the sum is <= C_K f(n)/n. Boundary term: h_i(n - y) <= V_{m-1}(n - y)
with n - y >= n/2 > a_m >= a_{m-1}; `lem:cd`(v) gives <= C m T(n)/n; f(y) <= C_K f(n). Summing
over i <= m: C_K m f(n)/n + C_K m^2 T(n) f(n)/n <= C_K m f(n)/n since m T(n) <= m T(a_m) <= C.
(Side remark: `lem:cd`(ii) gives u_m(x) <= C (m/a_m) T(x) <= C m T(x)/x for x <= a_m, so the
bound of `lem:cd`(v) in fact holds for all x >= 1; the text's "n - y >= a_m/2" is therefore
enough, though the cleaner reason is n - y > a_m.)

(B) No summand of size y. g_l = V^{(y)}_{m_l}, m_1 = floor(m/2), m_2 = m - m_1, V^{(y)}_m = g_1 * g_2.
nabla(g_1 * g_2)(n) = sum_z g_1(z) nabla g_2(n - z). Splitting at z = n/2 and summing the part
z <= n/2 by parts (w = n - z, then shift w -> w - 1 in the g_2(w - 1) sum) gives exactly
sum_{w >= n/2} nabla g_1(n - w) g_2(w) + g_1(n/2) g_2(n/2 - 1) + sum_{z > n/2} g_1(z) nabla g_2(n - z)
for even n. I re-derived this; it is correct.
Bounds: sup abs(nabla g_l) <= C e^{C m_l T(y)} a_{m_l}^{-2} <= C_K a_m^{-2}, since
m_l T(y) <= m C_K T(n) <= C_K and a_{m_l} >= c a_m (m_l >= m/3 for m >= 2; m = 1 absorbed in
constants, g_1 = delta_0).
Chernoff: all summands of g_l are below y and E[X; X < y] <= C y T(y), so
E e^{lambda X} 1{X < y} <= exp((e^{lambda y} - 1) C T(y)), and with e^{lambda y} = z/(C m T(y) y),
P(W >= z) <= (e C m T(y) y/z)^{z/y} for z >= e C m T(y) y. At z = n/2 the base is
<= C_K m T(n) and the exponent z/y = (n/2)/ceil(n/K) lies in [K/(2(1 + K/n)), K/2]. The text
writes the exponent as K/2. Since the base is <= 1 this is slightly optimistic; the
discrepancy is base^{-O(K^2/n)} = exp(O(K^2 log n / n)) = O(1), so it is absorbed in C_K.
Taking y = floor(n/K) would make the exponent exactly >= K/2. Harmless.
Pointwise bound: for x >= n/2 - 1, split g_l = g_{l,1} * g_{l,2} into halves; one half-sum
is >= n/4 - 1/2, and sup g_{l,r} <= sup u_{m_{l,r}} <= C/a_m (`lem:cd`(i)). This gives
g_l(x) <= C a_m^{-1} (C_K m T(n))^{K/4 (1 - o(1))}; the text claims only the exponent K/8,
which is weaker (base <= 1) and therefore valid. The displayed total
abs(nabla V^{(y)}_m(n)) <= C_K a_m^{-2} (C_K m T(n))^{K/2} + C a_m^{-2} (C_K m T(n))^{K/4}
follows (product of the two K/8 bounds gives K/4).
Exponent arithmetic: lambda = n/a_m > Lambda; Potter gives
c lambda^{-alpha-delta} <= m T(n) <= C lambda^{-alpha+delta}; m f(n)/n >= c m T(n)/n^2. So
a_m^{-2} (C_K m T(n))^{K/4} / (m f(n)/n) <= C lambda^2 (C_K m T(n))^{K/4}/(m T(n))
<= C_K lambda^{2 + alpha + delta - (alpha - delta) K/4}, which is <= C_K for lambda >= 1 once
K >= 4(2 + alpha + delta)/(alpha - delta). With K fixed, Lambda is chosen so large that
C_K m T(n) <= 1 (then the K/2 term is below the K/4 term), n/K exceeds the threshold for
(LR) and (LD), and n/2 > a_m. All constants then depend on the law alone. Correct.

Positivity. The statement is for all m >= 1 and n >= a_m, and the proof uses f(n) >= c T(n)/n
("(LR) gives f(n) asymp T(n)/n") at every such n. (LR) gives this only for n >= n_0. If f has
a zero at a small n >= a_1 (a_1 is a constant of the chosen scale), the claim fails at m = 1:
abs(f(n-1) - f(n)) = f(n-1) > 0 = C f(n)/n. So the lemma needs either n >= max(a_m, n_0) or
f(n) > 0 for all n >= 1. Every use in the section is at levels that tend to infinity
(`lem:diffs`(i) at levels >= n/2 with n -> infinity, `lem:diffs`(iii) at j -> infinity,
`thm:layer-diff` at n = N - j >= N/2), so the restriction costs nothing.

Numerical check: zeta law, alpha in {0.3, 0.7}, convolution powers to length 120000,
sup over n in [a_m, 60000] of abs(nabla V_m(n)) n/(m f(n)): bounded by 2.93 (alpha = 0.3,
m <= 25) and by 4.50 (alpha = 0.7, m <= 120), with the sup attained at n/a_m of order 7 and
slowly stabilising in m, as the local limit theorem predicts.

Verdict: proved as written, up to the stated restriction n >= n_0 (or f > 0 everywhere),
which the uses respect; the K/2 exponent and the K/8 exponent are constant-level slips
in opposite directions, neither affecting the result.

## 5. Lemma `lem:diffs`

### Claim cards and derivations

(i) abs(delta V_m(n)) <= C f(n)(1 + m T(n)) for n >= 2 a_m.
delta V_m(n) = sum_x f(x)[V_m(n - x) - V_m(n)]. For x <= n/2 the levels n - i, i < x, are
> n/2 >= a_m, and `lem:Lstar` gives abs(V_m(n-x) - V_m(n)) <= C x m f(n)/n (Potter on
f(n-i)/(n-i)); sum_{x <= n/2} x f(x) <= sum_{x <= n/2} T(x) <= C n T(n). Part <= C m T(n) f(n).
For x > n/2 the rest is sum_{w < n/2} f(n - w) V_m(w) - V_m(n) T(floor(n/2) + 1); the first is
<= sup_{v > n/2} f(v) <= C f(n) (regular variation of f), the second <= C (m T(n)/n) T(n/2)
<= C m T(n) f(n) by `lem:cd`(v) at n >= a_m and (LR). Correct. The text writes "f(n/2)" for
sup_{v > n/2} f(v); f need not be monotone, so this should read "<= C f(n) by regular
variation". Cosmetic.

(ii) abs(q_{m+1}(n) - T(n)) <= C m T(n)^2 for n >= 2 a_m.
q_{m+1}(n) - T(n) = sum_{x < n} V_m(x)[T(n-x) - T(n)] - T(n) P(S_m >= n). For x <= n/2:
T(n-x) - T(n) = sum_{i=n-x}^{n-1} f(i) <= C x T(n)/n by (LB) and Potter, and
sum_{x <= n/2} x V_m(x) = E[S_m; S_m <= n/2] <= m E[X; X <= n/2] <= C m n T(n). For x > n/2:
V_m(x) <= C m T(n)/n (`lem:cd`(v), x >= n/2 >= a_m) and sum_{x > n/2} T(n - x) <= C n T(n).
Last term <= C m T(n)^2 by `lem:sums`(i). Correct.

(iii) Four bounds. The sums are finite for each j (u^-_m(j) = 0 for m > j), so only large j
matters and the split at m_j = c/T_-(j) with a_-(m_j) ~ c^{1/alpha} j < j is legitimate for
c small. m <= m_j: `lem:Lstar` for the minus law at n = j + 1 >= a_-(m):
abs(Delta u^-_m(j)) <= C m f_-(j)/j, and sum_{m <= m_j} m^2 <= C m_j^3, giving
C (f_-(j)/j) T_-(j)^{-3} <= C/(j^2 T_-(j)^2) by (LR). m > m_j: `lem:fourier`(ii) with
a_-(m) >= a_-(m_j) >= c j and sum_m m e^{-c m T_-(j)} <= C/T_-(j)^2. Second bound: the same
without the factor m (m_j^2 and 1/T_-(j)). Third: sum_m m u_m = (u*u) - u since
sum_{m, m'} u_{m+m'} = sum_s (s+1) u_s; (u*u)(j) <= 2 sup_{l >= j/2} u(l) sum_{l <= j/2} u(l)
<= C omega_-(j) . C/T_-(j) (SRT_- from (LR) via (LB) and `lem:cd`(iii); sum_{l <= x} u(l)
= sum_m P(S_m <= x) <= sum_m e^{-m T(x+1)} <= C/T(x) by `lem:sums`(ii)). Fourth:
sum_m m q^-_m(j) = E[index of the run covering j] = 1 + sum_{i >= 1} P(S_i < j)
= 1 + sum_{l < j} (u(l) - delta_0(l)) <= C/T_-(j). All correct.

Verdict: proved as written (cosmetic slip "f(n/2)" in (i)).

## 6. Theorem `thm:layer-diff`

### Claim card

(BAL), (SPAN), (LR), (LD) both signs; fresh start of either sign or fair;
D_N(j) = P_N(N - j - 1) - P_N(N - j). For every eta > 0 there are epsilon > 0 and J with
abs(D_N(j) - T_+(N)(u_-(j+1) - u_-(j))) <= eta T_+(N) u_-(j)/j for large N and
J <= j <= epsilon N. Mirror at the minus end. Under (DSRT_-), D_N(j) < 0 on the layer.

### Independent derivation

Decomposition. With a_m = u^-_m, b_m = q^-_m, Q_m = q^+_{m+1}, V_m = u^+_m, n = N - j and
`eq:fresh` at (k, j) = (n, j) and (n - 1, j + 1):
D_N(j) = sum_m [a_m(j+1) Q_m(n-1) - a_m(j) Q_m(n)] + sum_m [V_m(n-1) b_m(j+1) - V_m(n) b_m(j)]
= sum_m Delta a_m(j) Q_m(n-1) + sum_m a_m(j)[Q_m(n-1) - Q_m(n)]
  + sum_m V_m(n-1) Delta b_m(j) + sum_m nabla V_m(n) b_m(j) = I + II + III + IV.
Q_m(n-1) - Q_m(n) = [P(S_{m+1} >= n-1) - P(S_{m+1} >= n)] - [P(S_m >= n-1) - P(S_m >= n)]
= V_{m+1}(n-1) - V_m(n-1) = delta V_m(n-1). Correct.
III = II: b_m = B_{m-1} - B_m with B_i(j) = P(S^-_i < j), Delta B_i(j) = P(S^-_i = j) = a_i(j),
so Delta b_m = a_{m-1} - a_m and
sum_{m >= 1} V_m(n-1)[a_{m-1}(j) - a_m(j)] = V_1(n-1) a_0(j) + sum_{i >= 1} a_i(j) delta V_i(n-1).
For j >= 1, a_0(j) = 0, so III = II. All sums are finite (a_m(j) = b_m(j) = 0 for m > j), so
no convergence question arises. Correct. From here D_N(j) = I + 2 II + IV, and "the part
m <= m_0 of II and of III" means both copies of the same sum; that is how the text uses it.
For the fresh minus start, Q_m = q^+_m and b_m = q^-_{m+1}; redoing the summation by parts,
III = V_1(n-1) a_1(j) + sum_{i >= 2} a_i(j) delta V_{i-1}(n-1) and
II = sum_{m >= 1} a_m(j) delta V_{m-1}(n-1) with delta V_0(n-1) = f(n-1), so again III = II,
with the term f(n-1) f_-(j) present in both. The text treats that term as "one extra boundary
term" in III and bounds it by C epsilon tau_N(j), which is right either way
(f(n-1) f_-(j)/tau_N(j) asymp j T_-(j)^2/N <= epsilon). The m = 1 term of II, f_-(j) f(n-1),
is covered by the same bound.

Scales. tau_N(j) = T(N) u(j)/j asymp T(N)/(j^2 T_-(j)) for j >= J by (SRT_-). (R1) gives
T(n-1) = T(N)(1 + O(epsilon) + o(1)) uniformly in j <= epsilon N. m_0 = c_0/T(N) gives
a_+(m_0) ~ c_0^{1/alpha} N <= N/4 <= (n-1)/2 (`lem:rv-facts`(iii)).

Range m <= m_0. Middle sum of I: `lem:diffs`(ii) at n - 1 >= 2 a_+(m) and (iii):
<= C T(N)^2/(j^2 T_-(j)^2) = C (T(N)/T_-(j)) tau_N(j) <= C epsilon^alpha tau_N(j), since
T(N)/T_-(j) <= C T(N)/T(epsilon N) <= C epsilon^alpha. II (both copies): `lem:diffs`(i) at
n - 1 >= 2 a_+(m) and (iii): <= C f(N)[u(j) + T(N)/(j T_-(j)^2)] <= C f(N) u(j)
<= C (j/N) tau_N(j) <= C epsilon tau_N(j). IV: `lem:Lstar` at n >= N/2 >= a_+(m) and
sum_m m b_m(j) <= C/T_-(j): <= C f(N)/(N T_-(j)) <= C (j/N)^2 tau_N(j) <= C epsilon^2 tau_N(j).
All three ratios re-derived; correct.

Range m > m_0. m T_-(j) >= c_0 T_-(j)/T(N) >= c epsilon^{-alpha} for j <= epsilon N.
Minus factors: `lem:sums`(iii), `lem:decay`, `lem:fourier`(ii) give the three exponential
bounds, each applied within its hypotheses (RV and SPAN for the minus sign). Plus factors:
`lem:key`, `lem:fourier`(iii), `lem:fourier`(ii). Tail sums of regularly varying sequences
with index below -1: sum_{m > m_0} a_-(m)^{-2} <= C m_0 a_-(m_0)^{-2} <= C/(T(N) N^2),
sum_{m > m_0} 1/(m a_+(m) a_-(m)) <= C/(a_+(m_0) a_-(m_0)) <= C/N^2,
sum_{m > m_0} a_+(m)^{-2} <= C/(T(N) N^2), using a_pm(m_0) >= c N under (BAL). Hence the
four displayed bounds, with the factor e^{-c epsilon^{-alpha}} pulled out of the exponential
in m. Correct.

Lower bound on tau_N(j). x^2 T_-(x) has index 2 - alpha > 0, so sup_{j <= epsilon N} j^2 T_-(j)
<= C (epsilon N)^2 T_-(epsilon N) <= C epsilon^{2-alpha} N^2 T(N), whence
tau_N(j) >= c epsilon^{alpha-2} N^{-2}; and j^2 T_-(j)^2 <= C epsilon^{2-2alpha} N^2 T(N)^2
handles IV'. Since epsilon^{2-alpha} <= epsilon^{2-2alpha} for epsilon < 1, all four bounds
are <= C e^{-c epsilon^{-alpha}} epsilon^{2-2alpha} tau_N(j). Correct.

Conclusion. sum_{m >= 1} Delta a_m(j) = u(j+1) - u(j) for j >= 1 (the m = 0 term vanishes),
abs(u(j+1) - u(j)) <= C/(j^2 T_-(j)) <= C tau_N(j)/T(N) (`lem:diffs`(iii)), and
T(n-1) - T(N) = T(N)(O(epsilon) + o(1)). Collecting:
abs(D_N(j) - T(N)(u(j+1) - u(j))) <= C(epsilon^alpha + epsilon + epsilon^2
+ e^{-c epsilon^{-alpha}} epsilon^{2-2alpha} + o(1)) tau_N(j), uniformly in J <= j <= epsilon N;
choose epsilon, then N. The fair start is the average of the two fresh starts, with the same
limit. Under (DSRT_-), u(j+1) - u(j) <= -(1 - alpha - o(1)) u(j)/j, so D_N(j) < 0 for
eta < 1 - alpha. Correct.

Numerical check (fresh plus start, exact law by `eq:fresh`, N = 3000): the ratio
D_N(j)/(T(N)(u(j+1) - u(j))) and the normalised error abs(D_N - T Delta u)/(T u(j)/j) were
alpha = 0.3, b = 1: ratio 0.950, 0.927, 0.899, 0.862, 0.817, 0.761 and error 0.029, 0.046,
0.067, 0.093, 0.126, 0.166 at j = 5, 10, 20, 40, 80, 160; alpha = 0.7, b = 1: ratio 0.978,
0.963, 0.935, 0.880, 0.766, 0.512 and error 0.007, 0.012, 0.021, 0.040, 0.076, 0.157;
alpha = 0.7 with a shifted zeta minus law (b = 3.47): ratio 0.992 to 0.714, error 0.003 to
0.100 on the same j. The error grows with j/N as the theorem allows (it is O(epsilon^alpha)
at worst) and D_N < 0 throughout the layer; at j = 320 = 0.107 N and alpha = 0.7, b = 1 the
sign flips, which is the interior minimum of the W-shaped density, outside any admissible
epsilon.

Verdict: proved as written.

## 7. Proposition `prop:count`, given (B)

### Claim card

(BAL), (SPAN), (LR), (LD2), (DSRT_pm), fresh or fair start, (alpha, b) nondegenerate, (B),
no ties in kappa~_pm below J_pm and kappa~_pm strictly decreasing on [J_pm, infinity): P_N has
exactly M_+ + M_- + m_L modes, located as stated; exactly 1 + m_L further local minima at
(c + o(1)) N; no antimode in the layers; M_pm = 1 for strictly log-convex laws.

### Independent derivation

Five ranges of k, read as signs of Delta P_N(k) = P_N(k+1) - P_N(k).
Plus profile, 0 <= j < J_+: by `thm:initial`(f) (W^+_N = o(T_+(N)) for fresh and fair starts,
P_N(N) = Q_+(N), kappa~_+(0) = 1, 0 or 1/2) the ratio P_N(N - j)/T_+(N) converges to
kappa~_+(j) for each fixed j, and the no-tie hypothesis fixes the sign of D_N(j) for large N.
Plus layer, J_+ <= j <= epsilon N: `thm:layer-diff` with (DSRT_-) gives D_N(j) < 0 for
J <= j <= epsilon N, with J from that theorem; (LD) holds since (LR) and (LD2) imply it
(`sec_setting`). If J > J_+, the finitely many j in [J_+, J) are covered by the profile
argument (`thm:initial`(f) and kappa~_+(j+1) < kappa~_+(j) there). The text says "For
J_+ <= j <= epsilon N, Theorem layer-diff ... gives D_N(j) < 0", which is literally true only
for j >= J; the bridge is one line and uses only hypotheses already present.
Bulk, [epsilon' N, (1 - epsilon') N] with epsilon' <= epsilon and epsilon' < c_1, 1 - c_s: by (B),
N^2 Delta P_N(k) -> L'(k/N) uniformly, so away from the critical points the sign is that of L';
near a critical point c, N^3 Delta^2 P_N(k) -> L''(k/N) uniformly, L''(c) != 0 by
nondegeneracy (`thm:shape`(c)), so Delta P_N is strictly monotone on a window of width
delta N around c N and crosses zero exactly once there (the sign of L' differs at the two
ends of the window). Minus side: mirror. Overlaps: the layer gives Delta P_N(k) > 0 for
k >= (1 - epsilon) N - 1 and L' > 0 on (c_s, 1); consistent.
Pattern and count. Minus profile signs, then a block of -, then nothing (m_L = 0) or
(+)^a (-)^b (m_L = 1), then a block of +, then the mirror of the plus profile. Modes are the
+ to - changes plus a leading - (mode at 0) plus a trailing + (mode at N); the profile
blocks contribute exactly M_-, M_+ (their last differences are negative, respectively the
first mirrored one positive, so the junctions add nothing), and the bulk contributes m_L.
Local minima between the end blocks are the - to + changes: one at c_1 and, if m_L = 1, one at
c_3; the layers have constant sign. Locations follow from the windows with delta -> 0.
Log-convex laws: u_pm strictly decreasing with limit 0 (`lem:dsrt`), and the profiles
(1, u(1), ...), (0, u(1), ...), (1/2, u(1), ...) have exactly one local maximum each, at j = 0
or j = 1; for the fair start the no-tie hypothesis requires f_pm(1) != 1/2, which the text
states inside the proof.

Verdict: proved as written, given (B), with the one-line bridge between J_+ and the J of
`thm:layer-diff` made explicit.

---

## Smallest gaps, in order of importance

1. `thm:signs`: at the degenerate pairs alpha_c < alpha < alpha_1, abs(log b) = beta_c(alpha),
   the density has 2 critical points and one is not an extremum; the theorem's "1 or 3 ...
   each a strict local extremum" is false there and the proof does not cover them. Add the
   nondegeneracy hypothesis of `prop:count`, or define sigma_L as the number of strict
   local extrema of L.
2. `lem:dsrt`: the two one-sided bounds in the proof are transposed (the chain gives
   liminf_i i log r_i >= (alpha - 1) lambda log lambda/(lambda - 1) and
   limsup_j j log r_j <= (alpha - 1) log lambda/(lambda - 1)); the conclusion stands. The
   lemma rests on de Bruijn-Erdos (1953) Theorem 1, which is outside the list of inputs
   taken as given here (consistent with the numerics for the zeta law).
3. `lem:Lstar`: "for all n >= a_m" needs f(n) > 0 at every n >= a_1, or n >= n_0; all uses
   are at levels tending to infinity. The Chernoff exponent at z = n/2 is K/2 only up to a
   bounded factor (take y = floor(n/K) to make it exact); the K/8 pointwise exponent is
   weaker than what the halving gives (K/4) and is valid.
4. `prop:count`: "For J_+ <= j <= epsilon N, Theorem layer-diff gives D_N(j) < 0" holds for
   j >= J; the finite range [J_+, J) is covered by `thm:initial`(f). One line.
5. `lem:diffs`(i): "f(n/2)" should be "sup_{v > n/2} f(v) <= C f(n)".
6. `ex:counts`: the fresh-start sentence assumes u_pm strictly decreasing; say so.

## Scripts (outside the repository)

Scratch folder
`C:\Users\arjun\AppData\Local\Temp\claude\C--Users-arjun-OneDrive-Documents-GitHub-Kagey-Problems\e83977a0-ccde-43be-ab6b-f724eaf1ba6e\scratchpad\`:
`shape_check.py` (sympy identities for H', Q, w_pm, the chi expansion and the ratio density;
mpmath alpha_c, alpha_1, beta_c, s_0 against s_1, s_2; brute-force count on the (alpha, b)
grid from the x-form of L), `pitchfork.py` (ratio of the true splitting distance to the
formula), `layer_check.py` (zeta-law renewal sequence: log-convexity, r_j, j log r_j;
`lem:Lstar` ratio over m and n; `thm:layer-diff` ratios at N = 3000 for b = 1 and b = 3.47;
exact fair-start law at N = 1500 and its sign changes). Outputs are in
`shape_check_output.txt` and `layer_check_output.txt` in the same folder.
