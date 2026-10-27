# 11. Audit of note 03 (the boundary alpha = 1)

Independent check of `03_alpha_one.md`, review only. I re-derived the centering and scale, read
each proof line by line, and checked the cited statements against the arXiv text of Berger. I
also wrote my own exact recursion (scratch, outside the repo; the numbers are quoted in Section 4).
I ignored the confidence language and judged only the mathematics.

Verdicts at a glance:

| Item | Verdict |
|---|---|
| 1. Theorem A (with Lemmas 1, 2) | Proved as written, up to two harmless slips (see 1.4). |
| 2a. P_N(N) = T_+(N) and Proposition C (end layer) | Proved as written. In fact it holds for any regularly varying T_+. |
| 2b. u_-(j) ~ 1/mu_-(j) | Cited. Berger's (3.6) checked directly; Erickson's original not reached. |
| 2c. "Big-jump kernel known only to leading order" | Overstated. Incomplete: it is a heuristic at leading order, not a proved leading order. M2 is not actually missing (see 2.3). |
| 3. F-to-G transition | Correct after stated restrictions: eps_N = N T(N)/mu(N) tends to (1 - alpha)/alpha, not 1 - alpha; the Lamperti-to-Cauchy expansion is local, not uniform. |
| 4. Numerics | Reproduced: the end layer exactly, the bulk, kernel and antimode rows to the stated digits (apart from one column, see 4). |

## 1. Theorem A

### 1.1 Claim card

Hypotheses: (RV1) T_s(n) = L_s(n)/n for s = +, -; (SPAN) for both laws; (CMP)
0 < liminf L_+/L_- <= limsup L_+/L_- < infinity. Start: fresh plus, fresh minus or fair.
Objects: a_s(m) = inf{x >= 1 : T_s(x) <= 1/m}, b_s(m) = m mu_s(a_s(m)), m_N given by
b_+(m_N) + b_-(m_N) = N, V_N = mu_+(a_+) + mu_-(a_-), p_N = mu_+(a_+)/V_N,
sigma_N = (1 - p_N) a_+ + p_N a_-, and h_N the density of W_N/sigma_N with
W_N = (1 - p_N) a_+ Z - p_N a_- Z'.
Conclusion: for each fixed K, sup over |k - p_N N| <= K sigma_N of
|sigma_N P_N(k) - h_N((k - p_N N)/sigma_N)| tends to 0.
Inputs: Gnedenko's local limit theorem, Berger's Theorem 2.3, the bound u_s(n) <= C/mu_s(n),
Potter, Karamata, the uniform convergence theorem.

### 1.2 My derivation of the centering and scale

After m cycles the plus and minus times are S+_m = b_+(m) + a_+ Z and S-_m = b_-(m) + a_- Z' to
first order. Near m_N, d b_s/dm = mu_s(a_s) + O(L_s) (the derivative of m mu(a(m)) is
mu(a) + a^2 f(a) to first order, and a^2 f(a) is of order L). The cycle count M at time N solves
N = S+_M + S-_M, so with tau = M - m_N, tau V + a_+ Z + a_- Z' = 0. Then
A_N - b_+(m_N) = tau mu_+ + a_+ Z = (1 - p) a_+ Z - p a_- Z', with p = mu_+/V. This is W_N, and
b_+(m_N) = p_N N. So the centering p_N N and the law of W_N are what I get independently. The
scale: with a_s = m L_s and N = m V, sigma_N/N = p(1 - p)(L_+/mu_+ + L_-/mu_-), which tends to 0
like L/mu.

The exponent of W_N/sigma_N in Section 1 of the note is right. With
psi_1(cu) = c psi_1(u) - i c log c u for c > 0 and the reflected term for -Z', the sum is
-(pi/2)|u| - i(2w - 1)u log|u| - iu[w log w - (1 - w) log(1 - w)] + i(1 - gamma_E)(2w - 1)u. The
closed form of psi_1 agrees with my own quadrature (u = 0.7: -1.0995574 + 0.5456215i both ways;
u = 2.0: -3.1415927 - 0.5407257i). The compensator x 1{x <= 1} matches the centering
m E[X; X <= a_m], so Z is the limit of (S_m - b_m)/a_m with no extra drift. Correct.

### 1.3 Step by step

Lemma 1. (i) Gnedenko gives sup_y u_m(y) <= C/a_m. (ii) The truncated sum dominates from below,
E S~_m = b_m, E[X^2; X <= a] <= 2 sum_{n <= a} L(n) ~ 2aL(a), so Var S~_m <= C a^2, and the
one-sided Bernstein bound gives exp(-c x/a) for x >= a. Checked. (iii) The defect
D = b_m - b_{m_1} - b_{m_2} lies in [0, m(mu(a_m) - mu(a_{m_1}))] (both bounds use only that
mu(a(.)) is nondecreasing and m_1 <= m_2), and mu(a_m) - mu(a_{m_1}) <= a_m T(a_{m_1}) <= a_m/m_1,
so D <= C a_m. The split "one of the two deviations is at most (D - x)/2" is exact, since the two
deviations add to D - x. Correct.

Lemma 2, range (IV). The Riemann sum and the change of variables are correct. I checked the
Jacobian: the map (x, tau) -> (x - tau mu_+, -x - tau mu_-) has determinant V, and on its image
(1 - p) z_1 - p z_2 = x identically (because p mu_- = (1 - p) mu_+). So the integral equals the
density of W_N at x divided by V. The error count o(W rho/sigma^2) = o(1/(sigma V)) for fixed W
is right, and so is the tail bound for |tau| > W rho (in fact O(1/(sigma V W^3))).

Range (I). Berger's Theorem 2.3 gives u+_m(k) <= C (m/a_+(m)) L_+(n)/n for b_+(m) <= k/2, and the
Karamata sum and the Potter comparison give a ratio to 1/(sigma V) of order
delta (L/V)^{1 - 2 eps}. Correct.

Range (II). p_N N - b_+(m) >= (m_* - m) mu_+(a_+(m_*)) is exact (mu(a(m)) <= mu(a(m_*))). The
deviations are at least c r sigma, Theorem 2.3 with Potter gives C(delta) r^eps/(r sigma) per
factor, and the sum is C(delta) W^{2 eps - 1}/(sigma V). The constant depends on delta, which is
harmless because W tends to infinity before delta tends to 0. Correct.

Range (III). For m <= 2 m_* this is Lemma 1 for the plus factor and the sup bound for the minus
factor. For m > 2 m_*, s(m) >= 2N gives j <= b_-(m)/2 + K sigma, Lemma 1 gives the factor
exp(-c Lambda_n), and Lambda_n -> infinity by BGT 1.5.9a. The remaining factor uses
sum_m u+_m(k) <= u_+(k) <= C/mu_+(k) and mu_+(k) >= mu_+(a_+), which is of order V. Correct.

Proof of Theorem A. The run-sum identity is right (I re-derived it from the run in progress at
step N, and my recursion built on it agrees with a sum over all sign strings, see Section 4).
Near range: n = N - y stays in the window of Lemma 2, the change of (p, sigma, w, V) from N to n
is o(1) in the argument of the compact family {h_N}, and
m_+(a_+) - m_+(D_0) <= C L lambda^eps = o(V) with lambda = (V/L)^{1/4}. Middle range: Lemma 2 with
K' = K + W gives the bound C/(sigma V), and the weight is o(V). Far range:
sum_{k'} A(k', j) = u_-(j) exactly, and T_+(W sigma) u_-(j) <= C L_+(W sigma)/(W sigma mu_-(j)),
which is o(1/sigma) under (CMP) since L_+(x)/mu_+(x) -> 0 and mu_+(W sigma) <= C mu_-(j). Adding
the two near ranges gives h_N (mu_+ + mu_-)/V = h_N. The fresh minus start gives the same A (the
sum is symmetric in the two signs) and the analogous B, so the limit is the same. Correct.

### 1.4 Slips (do not affect the result)

1. Range (IV): "m_*[mu_s(a_s(m)) - mu_s(a_s(m_*))] <= m_* T_s(a_s(m_*)) |a_s(m) - a_s(m_*)|
   = O(|m - m_*| L_s)". The last equality needs some local regularity of f (without it a_s can
   jump over a long stretch where f vanishes). Only o(sigma) is needed, and that holds: either
   because |a_s(m) - a_s(m_*)| = o(a_s(m_*)) by regular variation, or directly from
   sum_{a(m_*) < n <= a(m)} n f(n) <= a(m)[T(a(m_*) + 1) - T(a(m) + 1)], which is
   O(|tau| L) + o(a).
2. Section 1: "s has jumps of order 1". In general a jump of s is at most m a f(a), which is o(a)
   (since T(n + 1)/T(n) -> 1), and it is O(1) only under local regularity. Again only o(sigma)
   is used.

Corollaries A1-A3: checked. A2 examples (Q1: gamma_N ~ pi N/(4 log N); Q2:
gamma_N ~ pi N/(4 log N log log N)) are right. In A3, E(X; X > a)/L(a) -> infinity is BGT 1.5.9b.

### 1.5 Sources verified directly

Berger, arXiv:1706.07924v4 (full text extracted to scratch):
- (1.1)-(1.3): as quoted. At alpha = 1, b_n = n mu(a_n) with mu(x) = E[X 1{|X| <= x}].
- (1.4): Gnedenko, sup over x in Z, cited to Gnedenko-Kolmogorov Ch. 9, Sec. 50.
- Theorem 2.3: "For any alpha in (0, 2) ... there exists a constant C_0 > 0 such that for any
  x in Z, P(S_n - b_n = x) <= C_0 (n/a_n) L(|x|)(1 + |x|)^{-alpha}." Two remarks. Berger writes
  b_n, not floor(b_n); the note's floor is the natural reading for integer x and changes only the
  constant. The quantifier on n is implicit ("there exists C_0 ... for any x"), and the bound is
  meant for all n, which is how the note uses it. Optimality (2.4): as the note says.
- Theorem 2.4: (2.9) under (2.5), and (2.10) under (2.7), "as n -> +infinity, x/a_n -> +infinity".
- (3.6): "Erickson [13] also proved that P(x in S) ~ 1/mu(x) as x -> infinity if alpha = 1 with
  |mu| = +infinity", stated for renewal processes (X_1 > 0), with no local hypothesis. Reference
  [13] is Erickson, Trans. AMS 151 (1970) 263-291.

Not verified: Erickson's paper itself (the AMS server returned 403). So the theorem number and
the exact hypotheses in Erickson remain to be read. My recursion gives u(j) mu(j) = 0.5659,
0.7528, 0.8374, 0.8531 at j = 10, 100, 1000, 2000 for Q1 (the same as the note), and
U(j) mu(j)/j = 0.957, 0.983, 0.986 at j = 100, 1000, 2000.

## 2. End layer and big-jump kernel

### 2.1 P_N(N) = T_+(N) and Proposition C

The atom: proved, trivial.

Proposition C: I re-derived the final-run identity (case of a plus run in progress after r
cycles; case of a minus run in progress of age m after r + 1 plus runs). In (a), the split at
delta N, the subexponential bound P(S_r >= x) ~ r T(x) for fixed r, and the O(T(N)^2) bound for
t > delta N are all correct. In (b), u+_{r+1}(n) = (r + 1)(T(n) - T(n + 1)) + o(T(n)) = o(T(n)).
The sums over r <= j and m <= j are finite. **Proved as written.** Remark: the proof uses only
that T_+ is regularly varying (any index, with (1 - 2 delta)^{-alpha} in place of
(1 - 2 delta)^{-1}), so the hypothesis "index -1" is stronger than needed.

The size statement u_-(j) ~ 1/mu_-(j) is a citation (2b above). "Decreasing in j for log-convex
f_-" is Kaluza's theorem and is correct. Q1 has log-convex f.

### 2.2 The kernel algebra

I checked the reduction. On the ray k - p_N N = (1 - p) l N, j = (1 - p)(1 - l) N,
kbar(j) = p(1 - l) N, so L_k = l N exactly. With U_- ~ j/mu_-, V_- ~ j/mu_-^2 and f_+ ~ T_+/n,
the kernel is (L_+/(N mu_-))[1/l + (1 - l)/l^2] = L_+/(N mu_- l^2). The tail match
(1 - p) a_+/x^2 at x = (1 - p) l N equals L_+/(mu_- l^2 N), using m_N/(1 - p_N) = N/mu_-. Both
are correct. (Notation: Section 5 uses L both for the slowly varying function and for the
ballistic variable.) My recursion also confirms the generating identity V_- = u_- * u_- - u_-
(difference 2e-15 for j < 60), which is the V used in the kernel.

### 2.3 "Known only to leading order"

This overstates what is proved. Nothing about the kernel is proved, not even the leading order.
What exists is a heuristic leading-order derivation plus numerics. The status table ("Leading
order derived") should say "heuristic".

On the named gap: M2 is not really missing. Berger's (2.10) is a double limit ("as n -> infinity,
x/a_n -> infinity"). Even in its weakest reading (for every sequence x_n with x_n/a_n -> infinity),
uniformity over m in any range whose lower end tends to infinity follows by a diagonal argument.
Suppose pairs (m_i, x_i) with m_i -> infinity and x_i/a_{m_i} -> infinity have ratio bounded away
from 1. Pass to strictly increasing m_i and set x_n = x_i at n = m_i and x_n = n a_n elsewhere.
This sequence violates the one-sequence statement. So the uniform version over
[delta m_*, m_*/delta] is a consequence of (2.10) as stated.

**Verdict: incomplete.** The smallest missing implication is the assembly itself: the asymptotics
of sum_m u+_m(k) u-_m(j) (and of the B-sum) for k - kbar(j) >> sigma_N. This needs (2.10) for the
plus factor on the bulk range of m, the local limit for the minus factor (a minus-side analogue of
Lemma 2 off the ray, which is essentially M1), and the negligibility of m outside
[delta m_*, m_*/delta]. It also needs the local hypothesis (LR1), which is Berger's (2.7) with
p = 1. The note does assume it, but Theorem A does not. Numerically the kernel with exact u, U, V
sits at 1.129, 1.135 (l = 0.6; N = 1000, 2000 in my run; the note's 4000 and 8000 values are 1.135
and 1.130). So the numerics show no convergence over this range. That is compatible with
logarithmic corrections, but it does not confirm the constant.

Antimode: heuristic, as the note says. One discrepancy: with the note's own
mu(j) = H_{j+1} - 1, N/(4 mu(j*)) is 80.9 and 135.9 at N = 1000, 2000 (j* = 32, 59). The table
in Section 8 gives 66 and 115. Either way the prediction fails, so the conclusion stands, but the
column should be recomputed. T(j*) N/(4 mu(N)) = 1.204, 1.180 matches the note.

## 3. The F-to-G transition (Section 7)

(a) eps_N = N T(N)/mu(N) "the local index d log mu/d log x". For alpha < 1 these are different.
With T(n) = n^{-alpha}, mu(x) ~ alpha x^{1-alpha}/(1 - alpha), so N T(N)/mu(N) tends to
(1 - alpha)/alpha. The local index x^2 f(x)/mu(x), and N T(N)/m(N) with the de Haan function m,
both tend to 1 - alpha. Numerically at N = 10^7: alpha = 0.5 gives N T/mu = 1.0005,
N T/m = 0.5001, N^2 f(N)/mu = 0.5002; alpha = 0.8 gives 0.2616, 0.2073, 0.2092. So the bullet
"alpha < 1: eps_N -> 1 - alpha" is false for the stated definition. Fix: define eps_N with the
de Haan function m (eps_N = N T(N)/m(N)) or as the local index. All three agree to first order
at alpha = 1 and near it, so nothing downstream changes. The alpha > 1 bullet is off by the same
factor alpha (harmless under "of order").

(b) Lamperti to Cauchy. I re-derived G's density in log-odds: with t = log((1 - x)/x) and
beta = log b, Lambda(x) = (sin pi alpha/(2 pi)) / (x(1 - x)[cosh(alpha t - beta) + cos pi alpha]).
The expansions sin pi alpha = pi eps + O(eps^3), cosh + cos = [(alpha t - beta)^2 + pi^2 eps^2]/2
+ O(u^4 + eps^4), 1 + cosh t = 1/(2x(1 - x)), the center x_0 = 1/(1 + b^{1/alpha}) and the scale
pi eps x_0(1 - x_0) are all correct. But the factor (1 + O(eps)) is not uniform in x. The
relative error is O(eps + (t - beta/alpha)^2), so the statement holds on |t - beta/alpha| = o(1),
in particular on every window of K widths, and fails beyond it: the true tails in t are
exponential, not Cauchy. Numerically (b = 1), the ratio Cauchy/Lamperti is 1.00008 at t = 0,
0.983 at t = 10 eps and 1.345 at t = 2 for alpha = 0.99, and 1.378 at t = 2 for alpha = 0.999. So
this is a local limit statement and should be written with that restriction.

(c) Matching with Theorem A. The identity (pi/2) sigma_N/N = pi p(1 - p)(L_+/mu_+ + L_-/mu_-)/2
is correct, so the two scales agree when eps is the average of L_s/mu_s at the fluctuation scales
a_s. But that is a different eps from the eps_N defined at the start of Section 7 (read at N).
The note itself reports a width 33% too small with eps read at N, and the two readings are
equivalent only to first order and only for tame L. The matching is a formal identification of
parameters; no joint limit (alpha -> 1, N -> infinity) is proved. "The regimes merge when
|alpha - 1| log N is of order 1" is a heuristic. **Verdict: correct after the restrictions in
(a)-(c).**

## 4. Numerical spot check (my own code)

Recursion: A(k, j) = sum_y f_-(y) B(k, j - y), B(k, j) = sum_y f_+(y) A(k - y, j), A(0, 0) = 1
(fresh plus), then the run-sum identity. Brute force over all sign strings: maximum difference
1.7e-16 at N = 6 and 10, for Q1/Q1 and Q1/Q3. Total mass equals 1 to rounding.

| Check (Q1 both) | N = 1000 | N = 2000 | Note |
|---|---|---|---|
| P_N(N-j)/(T(N)u(j)), j = 1, 5, 10 | 1.01598, 1.05333, 1.09292 | 1.00868, 1.02847, 1.04888 | identical |
| fair start: m_N, R_N, HWHM/gamma | 115.11, 1.2872, 1.021 | 203.97, 1.2437, 1.036 | 115.34, 1.290, 1.019; 204.0, 1.244, 1.036 |
| max abs(P - Cauchy)/P(N/2), window of 3 gamma | 0.223 | 0.196 | 0.290, 0.244 (normalized by the Cauchy peak, which gives R_N - 1) |
| kernel ratio at l = 0.4, 0.6, 0.8 | 0.980, 1.129, 1.101 | 1.029, 1.135, 1.094 | identical |
| antimode j* | 32 | 59 | identical |

The small m_N difference at N = 1000 comes from where s(m) = N is solved across a jump of s, a
second-order choice. Lemma 2 on the ray: sigma V A(N/2, N/2) = 0.1796 and 0.1790 against
h(0) = 2/pi^2 = 0.2026, and at x = 2, 0.049 and 0.053 against 0.077. That is 11% low with no
visible movement between N = 1000 and 2000. This does not contradict Lemma 2, whose corrections
are logarithmic (the line sum of A is the cycle renewal density 1/mu_cycle(n), while the limit
puts total mass 1/V with V built from mu at a_N), but the convergence of Lemma 2 itself is not
visible at accessible N.

Scripts and output (scratch, not in the repo): `audit11.py`, `lemma2.py`, `audit11_output.txt`,
`lemma2_output.txt` in the session scratch folder.

## 5. Changes recommended for the note

1. Range (IV) of Lemma 2 and Section 1: replace "O(|m - m_*| L_s)" and "jumps of order 1" with
   o(sigma) (1.4).
2. Status table: big-jump kernel "heuristic at leading order"; drop M2 as a separate gap (2.3);
   name the assembly and (LR1) as what is missing.
3. Section 7: define eps_N with the de Haan function, or as the local index; add "locally,
   |t - beta/alpha| = o(1)" to the Lamperti expansion; state the matching as a parameter
   identification.
4. Proposition C: "regularly varying T_+" is enough.
5. P7 table: recompute N/(4 mu(j*)) with mu = H_{j+1} - 1.
6. Read Erickson (1970) for the theorem number and hypotheses before citing.
