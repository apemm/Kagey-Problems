# Proofs for the general version of Problem 137 (route 1)

Date 2026-10-02. Input: `checks_report.md` (read in full). It confirmed the vision file's run rule
with no correction, so the rule proved here is that rule. Predictions and outcomes are in `ledger.md`
(G1 to G16). The only new computation for this note is run 4 (`../q5.py`, G14 to G16, q = 5).

## Status of every statement

| statement | status |
|---|---|
| Lemma 1 (orbit of infinity under T = FG) | proved, every q >= 3 |
| Lemma 2 (the long in-edge, D4_q) | proved, every q >= 3 |
| Proposition 3 (tree = parent-terminating set = orbit of 0 under H_q, minus infinity) | proved, every q >= 3 |
| Theorem 4 (rank = number of parent steps, analogue of Theorem 3.6) | proved, every q >= 3 |
| Corollary 5 (Conjecture C_q: unique shortest word, blue iff negative, children) | proved, every q >= 3 |
| Theorem 6 (reachability: the m-tree is all of Q for m = 1, 2, 3) | proved |
| Lemma 7 (tail lemma: parent strings = run rule) | proved, every q >= 3 |
| Theorem 8 (Conjecture B_q) | proved, every q >= 3, so for m = 2, 3 on all of Q |
| Theorem 9 (Conjecture A_q, recurrence from n = 2q - 2, false at n = 2q - 3, no cancellation) | proved, every q >= 3 |
| Proposition 10 (growth constant psi_q, increasing to the golden ratio) | proved |
| Theorem 11 (free case lambda >= 2, so m >= 4 and x -> x + k, k >= 2: Fibonacci counts) | proved |
| q = 5 tree in Q(sqrt 5) | computer-checked to rank 20 (run 4), and covered by the proofs |
| Hecke's theorem H_q = C_2 * C_q, conjugacies to Gamma_0(2)+ and Gamma_0(3)+ | not used. Status updated 2026-10-02: C_2 * C_q is stated in Short and Walker p. 1 and Winsor p. 4 (FULL in literature.md). Hecke 1936 itself REVIEW only. The Fricke group identification is via Im and Lee (FULL, Sections 1 and 2) plus a hand conjugation (literature.md Section 3) |

Main point. The vision file's route 2 (normal forms in C_2 * C_q) is not needed. The parent-map
argument of the existing paper (Section 3 of `problem137.tex`) generalizes to every Hecke group once
(D4) is replaced by D4_q, which comes from one elementary fact about the orbit of infinity under the
elliptic map T = FG. This settles the three hard parts (i), (ii), (iii) of the normal-form route
directly, and uses no group theory and no literature. Section 9 says how each hard part is covered.

## 0. Setting

Fix q >= 3, put theta = pi/q and lambda = lambda_q = 2 cos theta. Then 1 <= lambda < 2. Work in
X-coordinates with

    F(X) = X + lambda,    G(X) = -1/X   (X != 0),    root 0.

The m-tree of the vision file (f(x) = x + 1, g_m(x) = -1/(m x)) is this tree under X = sqrt(m) x,
since sqrt(m)(x + 1) = X + sqrt(m) and sqrt(m) g_m(x) = -1/X. Since 2 cos(pi/3) = 1,
2 cos(pi/4) = sqrt 2 and 2 cos(pi/6) = sqrt 3, the cases m = 1, 2, 3 are q = 3, 4, 6.

Let Gamma be the directed graph on the reals with edges X -> F(X) for every X and X -> G(X) for every
X != 0. The tree O is the set of points reachable from 0, and d(X) is the length of a shortest path
from 0 (the rank). A word f^{c_1} g f^{c_2} g ... g f^{c_k} is applied right to left, so f^{c_k} is
done first. Its weight is c_1 + ... + c_k + k - 1.

Parent map: P(X) = X - lambda for X > 0, P(X) = -1/X for X < 0. As in the paper, for X != 0 there is
an edge P(X) -> X (an F-edge if X > 0, a G-edge from -1/X != 0 if X < 0). Let T be the set of X for
which X, P(X), P^2(X), ... reaches 0, and for X in T let D(X) be the number of steps. So D(0) = 0 and
D(X) = D(P(X)) + 1 for X in T, X != 0. Note that X in T, X != 0 implies P(X) in T.

## 1. The orbit of infinity under T = FG

Let T(Y) = F(G(Y)) = lambda - 1/Y, with T(0) = infinity and T(infinity) = lambda. As a matrix T is
[[lambda, -1], [1, 0]]. Put U_i = sin((i+1) theta)/sin(theta), so U_{-1} = 0, U_0 = 1,
U_1 = lambda and U_{i+1} = lambda U_i - U_{i-1} (from sin((i+2)t) + sin(i t) = 2 cos t sin((i+1)t)).

**Lemma 1 (proved).** Let t_i = T^i(infinity). Then

(a) t_i = sin((i+1) theta)/sin(i theta) for 1 <= i <= q - 1,
(b) infinity = t_0 > t_1 = lambda > t_2 > ... > t_{q-2} = 1/lambda > t_{q-1} = 0,
(c) T^q is the identity map, and T^{-1}(0) = 1/lambda,
(d) for 0 <= i <= q - 3, T maps the interval (t_{i+1}, t_i] onto (t_{i+2}, t_{i+1}], increasingly
    (for i = 0 the interval is (lambda, infinity], including infinity).

*Proof.* By induction with the recurrence, T^i = [[U_i, -U_{i-1}], [U_{i-1}, -U_{i-2}]] for i >= 1.
The image of infinity is the ratio of the first column, U_i/U_{i-1}, which gives (a) when
U_{i-1} != 0, that is when sin(i theta) != 0, which holds for 1 <= i <= q - 1. For these i,
0 < i theta < pi, so sin(i theta) > 0, and sin((i+1) theta) >= 0 with equality only for i = q - 1.
So t_1, ..., t_{q-2} > 0 and t_{q-1} = 0. Next, for 1 <= i <= q - 2,

    t_i - t_{i+1} = (sin^2((i+1) theta) - sin(i theta) sin((i+2) theta)) / (sin(i theta) sin((i+1) theta))
                  = sin^2(theta) / (sin(i theta) sin((i+1) theta)) > 0,

using sin^2 a - sin(a - b) sin(a + b) = sin^2 b. Also t_{q-2} = sin((q-1)theta)/sin((q-2)theta)
= sin(theta)/sin(2 theta) = 1/lambda. This is (b). For (c), U_{q-1} = sin(q theta)/sin theta = 0,
so T^q = [[U_q, 0], [0, -U_{q-2}]], and U_q = sin((q+1)theta)/sin theta = -1 and
U_{q-2} = sin((q-1)theta)/sin theta = 1, so T^q = -I acts as the identity. Then
T^{-1}(0) = T^{q-1}(0) = T^{q-1}(t_{q-1}) = t_{2q-2} = t_{q-2} = 1/lambda (the t_i have period q).
For (d), T(Y) = lambda - 1/Y is continuous and strictly increasing on (0, infinity], with
T(infinity) = lambda. Since i + 1 <= q - 2, the interval (t_{i+1}, t_i] lies in (0, infinity] by (b),
and its image is (T(t_{i+1}), T(t_i)] = (t_{i+2}, t_{i+1}]. QED

## 2. The long in-edge (D4_q)

**Lemma 2 (proved).** Let Z < 0 and put Y = -1/Z > 0. Define P_1 = Y + lambda,
N_i = -1/P_i and P_{i+1} = N_i + lambda = T(P_i) for 1 <= i <= q - 2, and N_{q-1} = -1/P_{q-1}.
Then

(a) P_1, ..., P_{q-1} > 0 and N_1, ..., N_{q-1} < 0,
(b) N_{q-1} = Z - lambda,
(c) the path Y -> P_1 -> N_1 -> P_2 -> ... -> P_{q-1} -> N_{q-1} = Z - lambda alternates F and G
    and never applies G at 0, and P maps each point of it to the one before,
(d) P^{2q-2}(Z - lambda) = Y = P(Z). Hence Z in T iff Z - lambda in T, and then
    D(Z - lambda) = D(Z) + 2q - 3.

*Proof.* (a) P_1 > lambda, so P_1 is in (t_1, t_0]. By Lemma 1(d), P_i = T^{i-1}(P_1) lies in
(t_i, t_{i-1}] for 1 <= i <= q - 1, and these intervals lie in (0, infinity] with finite points
since P_1 is finite and T maps finite positive points to finite points. So P_i > 0 and
N_i = -1/P_i < 0.
(b) The path applies (G F)^{q-1} to Y. Since G F = G (F G) G^{-1} is conjugate to T, (G F)^q = id
by Lemma 1(c), so (G F)^{q-1} = (G F)^{-1} = F^{-1} G as maps. Hence N_{q-1} = F^{-1}(G(Y))
= F^{-1}(Z) = Z - lambda.
(c) G is applied only at the P_i, which are nonzero. P(N_i) = -1/N_i = P_i since N_i < 0, and
P(P_{i+1}) = P_{i+1} - lambda = N_i and P(P_1) = Y since the P_i are positive.
(d) The path has 2q - 2 edges, so P^{2q-2}(Z - lambda) = Y, and none of the points
N_{q-1}, P_{q-1}, ..., P_1 is 0. If Z in T, then Y = P(Z) in T, so Z - lambda in T and
D(Z - lambda) = 2q - 2 + D(Y) = 2q - 2 + D(Z) - 1. Conversely if Z - lambda in T then Y in T, so
Z in T. QED

For q = 3 this is (D4) of the paper, D(x - 1) = D(x) + 3. In general 2q - 3 is the length of the
relator (G F)^q G minus the two letters that cancel, as in Remark 3.9 of the paper.

## 3. The tree is the parent-terminating set

**Proposition 3 (proved).** (a) O = T. (b) T is closed under F, F^{-1} and G (at nonzero points).
(c) -lambda is in T. (d) O together with infinity is the orbit of 0 under the group H_q generated by
F and G as Moebius maps.

*Proof.* T is contained in O, since the reversed parent sequence of X in T is a path from 0 to X.
For O contained in T it is enough that 0 is in T and T is closed under F and G, since O is the
smallest set with these properties.

G. Let X in T, X != 0. If X > 0, then G(X) < 0 and P(G(X)) = X, so G(X) in T. If X < 0, then
G(X) = P(X), which is in T.

F. Let X in T and W = F(X). If W > 0, then P(W) = X, so W in T. If W = 0, it is in T. If W < 0, then
X = W - lambda, and Lemma 2(d) with Z = W gives W in T.

F^{-1}. Let X in T. If X > 0, then X - lambda = P(X) is in T. If X < 0, Lemma 2(d) gives X - lambda in
T. If X = 0, we need -lambda in T. Note P(-lambda) = 1/lambda = t_{q-2}. For 1 <= i <= q - 2,
t_i > 0 and t_i - lambda = -1/t_{i-1} (since t_i = T(t_{i-1}) = lambda - 1/t_{i-1}), so
P(t_i) = -1/t_{i-1} for i >= 2, which is negative, and P(-1/t_{i-1}) = t_{i-1}. Also
P(t_1) = lambda - lambda = 0. So the parent sequence of -lambda is
-lambda, t_{q-2}, -1/t_{q-3}, t_{q-3}, ..., t_1, 0, and -lambda is in T with
D(-lambda) = 2q - 4.

This proves (a), (b), (c). For (d), O with infinity added is closed under F^{-1}, F and G (F fixes
infinity, G swaps 0 and infinity, and the rest is (b)), so it contains the orbit H_q 0. Conversely O
consists of images of 0 under words in F and G. QED

So for every q the tree is the H_q-orbit of the cusp infinity, minus infinity. Whether that orbit is
all cusps of H_q is a separate question (Leutbecher's, not checked here). For m = 2, 3 Theorem 6
below shows directly that the tree is all of Q.

## 4. The rank is the number of parent steps (analogue of Theorem 3.6)

**Theorem 4 (proved).** For every X in O, d(X) = D(X). The increments are, for X in O,

- (D1) X > 0: D(X) = D(X - lambda) + 1,
- (D2) X < 0: D(X) = D(-1/X) + 1,
- (D3) X > 0: D(-1/X) = D(X) + 1,
- (D4_q) X < 0: D(X - lambda) = D(X) + 2q - 3.

*Proof.* (D1) and (D2) are D(X) = D(P(X)) + 1. (D3) is (D2) at -1/X < 0, which is in T by
Proposition 3. (D4_q) is Lemma 2(d). As in the paper, d <= D because the reversed parent sequence is
a path of length D(X). For d >= D we check D(W) <= D(V) + 1 for every edge V -> W with V in O (then W
is in O as well). An F-edge into W > 0 has V = W - lambda = P(W), equality by (D1). An F-edge into
W = 0 is fine. An F-edge into W < 0 has V = W - lambda and D(V) = D(W) + 2q - 3 > D(W) - 1 by (D4_q).
A G-edge into W < 0 has V = -1/W = P(W), equality by (D2). A G-edge into W > 0 has V = -1/W < 0 and
D(V) = D(W) + 1 by (D3). G never gives 0. Along a shortest path 0 = V_0 -> ... -> V_n = X this gives
D(X) <= D(0) + n = d(X). QED

**Corollary 5 (Conjecture C_q, proved for every q >= 3).** Let X in O, X != 0.

(a) The in-neighbours of X are X - lambda and -1/X, both in O. For X > 0 their ranks are d(X) - 1
    and d(X) + 1. For X < 0 they are d(X) + 2q - 3 and d(X) - 1. So P(X) is the only in-neighbour of
    rank d(X) - 1.
(b) X has exactly one shortest word from 0, the reversed parent sequence. Kimberling-style rows
    list each point once, since a point c with c + lambda = -1/c would solve c^2 + lambda c + 1 = 0,
    which has no real root because lambda < 2.
(c) The last move of the shortest word is f if X > 0 and g if X < 0. So a vertex is blue iff it is
    negative. This proves G6 for m = 2, 3 and for every q.
(d) Children. The children of 0 are lambda. A vertex X > 0 has children X + lambda and -1/X. A vertex
    -lambda < X < 0 has the one child X + lambda > 0. A vertex X <= -lambda is a leaf. For X < -lambda
    the value X + lambda appeared exactly 2q - 3 ranks earlier, with d(X + lambda) = d(X) - (2q - 3),
    and for X = -lambda it is the root.

*Proof.* (a) The in-neighbours are in O by Proposition 3(b). The ranks are Theorem 4 with (D1) to
(D4_q). Since 2q - 3 >= 3, the two in-neighbours have different ranks. (b) By induction on d(X)
using (a): the last edge of a shortest path comes from a point of rank d(X) - 1, which must be P(X).
The rows statement is the argument of Corollary 3.8(a) of the paper word for word. (c) The edge
P(X) -> X is an F-edge for X > 0 and a G-edge for X < 0. (d) Solve P(Y) = X as in Corollary 3.8(c):
Y > 0 needs Y = X + lambda > 0, Y < 0 needs X = -1/Y > 0. For X < -lambda apply (D4_q) to
X + lambda < 0. QED

## 5. Reachability for m = 1, 2, 3

Return to x-coordinates, x = X/sqrt(m), f(x) = x + 1, g_m(x) = -1/(m x). By Proposition 3(b) the
tree T_m = {x : sqrt(m) x in T} contains 0 and is closed under x -> x + 1, x -> x - 1, and
x -> g_m(x) for x != 0.

**Theorem 6 (proved).** For m = 1, 2, 3 the m-tree is all of Q. Hence Conjecture B_q and A_q below
hold for the m-tree on all of Q, and the parent map P(x) = x - 1 (x > 0), -1/(m x) (x < 0) reaches 0
from every rational in exactly d(x) steps.

*Proof.* For x = p/r in lowest terms (r >= 1) put h(x) = r^2/gcd(r, m). Since m is 1 or a prime,
gcd(r, m) is 1 or m. Then h(x + n) = h(x) for every integer n, and for x != 0

    h(g_m(x)) = m x^2 h(x).

Check. If m does not divide r, then g_m(x) = -r/(m p) is in lowest terms up to sign, since
gcd(r, m p) = 1, and m divides its denominator m|p|. So h(g_m x) = m^2 p^2 / m = m p^2
= m (p/r)^2 r^2. If m divides r (this includes m = 1), then m does not divide p, and
g_m(x) = -(r/m)/p with gcd(r/m, p) = 1 and denominator |p| prime to m, so h(g_m x) = p^2
= m (p/r)^2 (r^2/m).

Now use strong induction on h(x), which takes values in (1/m) Z_{>0}, a well-ordered set. Given
x in Q, pick an integer n with |x - n| <= 1/2 and put y = x - n. Since T_m is closed under +1 and -1,
x is in T_m iff y is. If y = 0 we are done. Otherwise h(g_m y) = m y^2 h(y) <= (m/4) h(x) < h(x),
because m <= 3. By induction g_m(y) is in T_m, so y = g_m(g_m(y)) is in T_m. QED

Remark (heuristic, not part of the proof). The step that uses m <= 3 is the bound
m y^2 <= m/4 < 1. For m = 4 the argument does not even start, since T_4 is not closed under
x -> x - 1 (by Theorem 11(a) it misses every x <= -1/2), so nothing about m = 4 follows from it.
G10 is covered by route 2, Theorem 10(e) and the remark after it. The proof does not need the
conjugacy to Gamma_0(2)+ or Gamma_0(3)+.
(Repair 2026-10-02: the earlier wording "matches G10" was an analogy only and has been withdrawn.)

## 6. The tail lemma and Conjecture B_q

For digits d_1, ..., d_n >= 1 write [d_1, ..., d_n]_lambda = d_1 lambda - 1/(d_2 lambda - 1/(...
- 1/(d_n lambda))). Its tails are Y_j = [d_j, ..., d_n]_lambda for 1 <= j <= n, and Y_{n+1} = infinity,
so that Y_j = d_j lambda - 1/Y_{j+1} (with -1/infinity = 0).

**Lemma 7 (tail lemma, proved).** All tails are defined and satisfy Y_j > 1/lambda (1 <= j <= n) iff
the string d_1, ..., d_n has no q - 2 consecutive 1's. In that case every tail is positive.

*Proof.* Note first that Y > 1/lambda gives -1/Y in (-lambda, 0], so for d >= 2,
d lambda - 1/Y > (d - 1) lambda >= lambda, and for d = 1, lambda - 1/Y = T(Y).

(If) Go from j = n down to j = 1 and keep track of the length i of the run of 1's at the left end of
d_j, ..., d_n. We claim Y_j is in (t_{i+1}, t_i]. Start with Y_{n+1} = infinity in (t_1, t_0], i = 0.
If d_j >= 2 and Y_{j+1} > 1/lambda, then Y_j > lambda, so Y_j is in (t_1, t_0] and i = 0. If d_j = 1 and
Y_{j+1} is in (t_i, t_{i-1}] with run length i - 1 <= q - 4, then Y_j = T(Y_{j+1}) is in
(t_{i+1}, t_i] by Lemma 1(d). Since every run has length i <= q - 3, every Y_j lies in some
(t_{i+1}, t_i] with i + 1 <= q - 2, so Y_j > t_{q-2} = 1/lambda by Lemma 1(b).

(Only if) Suppose all tails exceed 1/lambda, and let d_a = ... = d_b = 1 be a maximal run with
L = b - a + 1 >= q - 2. Then Y_{b+1} is in (t_1, t_0]: it is infinity if b = n, and otherwise
d_{b+1} >= 2 and Y_{b+2} > 1/lambda (or Y_{b+2} = infinity) give Y_{b+1} > lambda. By Lemma 1(d),
Y_{b+1-s} = T^s(Y_{b+1}) is in (t_{s+1}, t_s] for s <= q - 2, so Y_{b+3-q} is in
(t_{q-1}, t_{q-2}] = (0, 1/lambda]. Since b + 3 - q >= a >= 1, this tail is at most 1/lambda, a
contradiction. QED

**Lemma 7' (parent strings, proved).** Every positive X in O has exactly one representation
X = [c_1, ..., c_k]_lambda with c_1 >= 1, c_2, ..., c_k >= 1 and all tails Y_j > 1/lambda for
2 <= j <= k. Its digits are read off the parent sequence (c_1 subtractions, a flip, c_2
subtractions, a flip, ...), and D(X) = c_1 + ... + c_k + k - 1.

*Proof.* Existence. Run the parent sequence from X > 0. It subtracts lambda exactly
c_1 = ceil(X/lambda) times, reaching X - c_1 lambda in (-lambda, 0]. If this is 0 then X = c_1 lambda
and k = 1. Otherwise one flip gives Y_2 = -1/(X - c_1 lambda) > 1/lambda, which is in O, and
X = c_1 lambda - 1/Y_2. Repeat with Y_2. This stops because D drops by c_1 + 1 each round. The step
count is c_1 + 1 per round and c_k in the last, so D(X) = sum c_j + k - 1. Uniqueness. In any such
representation with k >= 2, Y_2 > 1/lambda puts X in (c_1 lambda - lambda, c_1 lambda), so X/lambda is
not an integer, c_1 = ceil(X/lambda) and Y_2 = 1/(c_1 lambda - X). With k = 1, X/lambda = c_1 is an
integer. So the length-one case and, for k >= 2, c_1 and Y_2 are forced, and Y_2 has a
representation of the same kind with k - 1 digits. Induction on k finishes it. QED

Reduced strings (vision file and checks report): c_1 >= 0, c_2, ..., c_k >= 1, no q - 2 consecutive
1's among c_2, ..., c_k, except that a run of exactly q - 2 starting at c_2 is allowed when c_1 = 0.

**Theorem 8 (Conjecture B_q, proved for every q >= 3).** The map sending a reduced string to
f^{c_1} g f^{c_2} g ... g f^{c_k}(0) is a bijection from reduced strings onto O. No reduced word
applies g at 0, and the rank of the value is the weight c_1 + ... + c_k + k - 1. The reduced word of
X is its unique shortest word, so every shortest word is reduced. In X-coordinates
X = [c_1, ..., c_k]_lambda with the convention 0 lambda - 1/Y = -1/Y. For m = 2, 3, by Theorem 6, every
rational has exactly one reduced word, and
x = c_1 - 1/(m c_2 - 1/(c_3 - 1/(m c_4 - ...))).

*Proof.* Split reduced strings by c_1.

c_1 >= 1. By Lemma 7 applied to c_2, ..., c_k, the run rule (no q - 2 ones among c_2, ..., c_k)
is equivalent to all tails Y_j > 1/lambda (j >= 2). So these are exactly the strings of Lemma 7', and
they correspond one to one to the positive points of O, with rank equal to weight. The value is
positive since c_1 lambda - 1/Y_2 > (c_1 - 1) lambda >= 0. The word applies g only at the tails
Y_j > 0.

c_1 = 0, k >= 2. The rule says (c_2, ..., c_k) has no q - 2 ones among c_3, ..., c_k (a run starting
at c_2 of length L contributes L - 1 to c_3, ..., c_k, so L <= q - 2 iff L - 1 <= q - 3). So
(c_2, ..., c_k) is a reduced string with first digit c_2 >= 1, which by the first case is the
string of a unique positive Y in O with d(Y) = c_2 + ... + c_k + k - 2. The value is G(Y) = -1/Y < 0,
G is a bijection from the positive points of O to the negative ones (Proposition 3(b) and
Corollary 5(c)), and d(-1/Y) = d(Y) + 1 by (D3), which is the weight.

c_1 = 0, k = 1. The empty word, value 0, weight 0.

The three cases cover positive, negative and zero values, so the map is a bijection onto O. The
reduced word of X spells the reversed parent sequence (Lemma 7'), which is the unique shortest word
by Corollary 5(b). QED

At q = 3 the rule says c_2, ..., c_k >= 2, except c_2 = 1 when c_1 = 0, which is Theorem B(ii) and
Lemma 4.1 of the paper.

## 7. Counting: Conjecture A_q

**Theorem 9 (proved for every q >= 3).** Let a_q(n) be the number of points of rank n. Then

    sum a_q(n) t^n = N_q(t)/D_q(t),
    N_q = 1 + t^2 + t^4 + ... + t^{2q-4} - t^{2q-3},
    D_q = 1 - t - t^3 - t^5 - ... - t^{2q-3},

with gcd(N_q, D_q) = 1. So a_q(n) = a_q(n-1) + a_q(n-3) + ... + a_q(n-2q+3) for every n >= 2q - 2,
and it fails at n = 2q - 3 (there the difference is -1). For m = 2, 3 this counts rationals.

*Proof (repair 2026-10-02, printed in full).* Positives. By Theorem 8, the positive points of rank n
are in bijection with the strings c_1 >= 1, c_2, ..., c_k >= 1 of weight n whose runs of 1's among
c_2, ..., c_k all have length at most q - 3. Give c_1 the weight c_1 and each c_j (j >= 2) the weight
c_j + 1 (the digit and the g before it). Then c_1 contributes t/(1 - t), a later digit 1 contributes
u = t^2, and a later digit at least 2 contributes B = t^3/(1 - t). Read c_2, ..., c_k left to right.
The sequence is uniquely a run of at most q - 3 ones, followed by any number of blocks (one digit at
least 2, then a run of at most q - 3 ones). With R = 1 + u + ... + u^{q-3} this gives R/(1 - BR),
a formal series since B has no constant term. So, with r(n) the number of positive points of rank n,

    sum r(n) t^n = t R/((1 - t)(1 - BR)) = t R/D_q,

since (1 - t)(1 - BR) = 1 - t - t^3 R and t^3 R = t^3 + t^5 + ... + t^{2q-3}.
Negatives. By (D2) and (D3), X -> -1/X is a bijection from the negative points of rank n to the
positive points of rank n - 1 (n >= 1). So a(0) = 1 and a(n) = r(n) + r(n - 1) for n >= 1, and
sum a(n) t^n = 1 + (1 + t) t R/D_q. Now (1 + t) t R = t + t^2 + ... + t^{2q-4}, and adding D_q
cancels the odd terms up to t^{2q-5} and leaves N_q. So the series is N_q/D_q.

(Earlier version, kept for the record.) By Theorem 8, a_q(n) is the number of reduced strings of weight n. The checks report
(section "Counting the reduced words") computes this generating function as N_q/D_q. I audited that
argument line by line: the decomposition of a nonempty digit sequence into runs of at most q - 3
ones separated by digits >= 2 is unique, the -1/(1 - t) from removing the empty sequence in case 2
cancels case 1, case 3 gives u^{q-2}/(1 - BR), (1 - t)(1 - BR) = 1 - t - t^3 R = D_q since
B(1 - t) = t^3, and R + (1 - t) t^{2q-4} = N_q. It is correct.

Coprimality (new). N_q - D_q = t + t^2 + ... + t^{2q-4} = t(1 - t^{2q-4})/(1 - t). A common root
alpha has alpha != 0 (D_q(0) = 1) and alpha != 1 (D_q(1) = 2 - q != 0), so alpha^{2q-4} = 1. Now
D_q = 1 - t - t^3 (1 - t^{2q-4})/(1 - t^2), so (1 - t^2) D_q = (1 - t)(1 - t^2) - t^3 + t^{2q-1}. At
alpha this is (1 - alpha)(1 - alpha^2) - alpha^3 + alpha^3 = (1 - alpha)(1 - alpha^2). If
D_q(alpha) = 0 then alpha = 1 or alpha = -1. But D_q(-1) = 1 + 1 + (q - 2) = q > 0, since each of
the q - 2 terms -t^{2j+1} (j = 1, ..., q - 2) is +1 at -1. So there is no common root.

Recurrence. Comparing coefficients in a(t) D_q(t) = N_q(t) gives
a(n) - a(n-1) - a(n-3) - ... - a(n-2q+3) = [t^n] N_q, which is 0 for n >= 2q - 2 and -1 for
n = 2q - 3. QED

This matches the checks report (n_0 = 6 for q = 4, 10 for q = 6) and run 4 (n_0 = 8 for q = 5).

**Proposition 10 (proved).** D_q has a unique root rho_q of smallest modulus. It is real, simple,
in (0, 1), and every other root has modulus > rho_q. So a_q(n) = C_q psi_q^n (1 + o(1)) with
psi_q = 1/rho_q, the positive root of psi^{2q-3} = psi^{2q-4} + psi^{2q-6} + ... + 1, and
C_q = -N_q(rho_q)/(rho_q D_q'(rho_q)) > 0. Also psi_3 < psi_4 < ... and psi_q tends to the golden
ratio.

*Proof.* On [0, infinity), D_q decreases strictly from 1 to -infinity, so it has one positive root
rho_q, and D_q(1) = 2 - q < 0 puts it in (0, 1). It is simple since D_q'(rho_q) < 0. If D_q(z) = 0
with |z| <= rho_q, then 1 = |z + z^3 + ... + z^{2q-3}| <= rho_q + rho_q^3 + ... = 1, so |z| = rho_q
and all the terms z^{2j+1} have the same argument as z and as each other, and their sum is the
positive real 1, so z is a positive real, z = rho_q. Partial fractions give the asymptotic, with
N_q(rho_q) != 0 by coprimality, and C_q > 0 because a_q(n) > 0. Since
D_{q+1} = D_q - t^{2q-1}, D_{q+1}(rho_q) < 0, so rho_{q+1} < rho_q. Finally put
L(t) = 1 - t - t^3/(1 - t^2) = (1 - t - t^2)/(1 - t^2) on (0, 1). Since
D_q = 1 - t - t^3 (1 - t^{2q-4})/(1 - t^2),

    D_q(t) - L(t) = t^{2q-1}/(1 - t^2) > 0   on (0, 1).

L(1/phi) = 0, so D_q(1/phi) > 0, and since D_q is decreasing on [0, infinity), rho_q > 1/phi. Let
0 < eps < 1 - 1/phi and s = 1/phi + eps. Then L(s) < 0, because 1 - s - s^2 < 0 for s > 1/phi,
and D_q(s) - L(s) = s^{2q-1}/(1 - s^2) tends to 0 as q grows. So D_q(s) < 0 once q is large, which
gives rho_q < s. Hence rho_q -> 1/phi and psi_q -> phi. QED
(Repair 2026-10-02: the earlier "uniform convergence on [0, 0.7]" sentence lacked this sign step.)

Numerically psi_3 = 1.46557, psi_4 = 1.57015, psi_6 = 1.61193 (checks report).

## 8. The free case lambda >= 2 (m >= 4, and x -> x + k with -1/x for k >= 2)

Here T(Y) = lambda - 1/Y has no finite order, there is no D4 relation, and the claims are as follows.

**Theorem 11 (proved for every real lambda >= 2).** Let O, T, P, D be as in Section 0. Then
(a) every point of T is 0, greater than 1, or in (-1, 0), (b) O = T and d = D on O, with a unique
shortest word, blue iff negative, (c) every string c_1 >= 0, c_2, ..., c_k >= 1 is reduced (no run
rule), the map to O is a bijection with rank equal to weight, and (d) a(n) = F(n + 1), with
generating function 1/(1 - t - t^2).

*Proof.* (a) Induction on D(X). D = 0 gives 0. If X > 0 then P(X) = X - lambda is 0 (X = lambda > 1),
or positive and so > 1 by induction (X > 1 + lambda), or in (-1, 0) by induction (X > lambda - 1 >= 1).
If X < 0 then P(X) = -1/X > 1 by induction, so X is in (-1, 0). (b) T is in O as before. T is closed
under G as before. For X in T, F(X) > -1 + lambda >= 1 > 0, so P(F(X)) = X and F(X) is in T. So
O = T. In the edge check of Theorem 4 the only case that used (D4_q), an F-edge from V in O into a
negative W, cannot occur, because F(V) > 0 for V in O. The other four cases and Corollary 5 go through
unchanged (for the in-neighbour X - lambda of a negative X, which is not in O, there is nothing to
check). (c) With Y_{k+1} = infinity, if Y > 1 then d lambda - 1/Y > lambda - 1 >= 1, so every tail of
every string with digits >= 1 exceeds 1 > 1/lambda. So Lemma 7' and the proof of Theorem 8 apply with
no run rule. (d) The checks report's count with R = 1/(1 - t^2) and no case 3 gives 1/(1 - t - t^2),
which I audited. QED

For m >= 4 in x-coordinates lambda = sqrt(m) >= 2, and x -> x + k with -1/x is lambda = k. This
proves G3, G4 and G12 for all n.

## 9. The normal-form route, and where its three hard parts went

- (i) A shortest word is reduced. Corollary 5(b) and Theorem 8: the shortest word is unique and
  it is the reduced word. No rewriting argument is needed.
- (ii) Distinct reduced words give distinct points, prefix case and both ends included. Lemma 7'
  (uniqueness of the parent string) and the case split in Theorem 8. The run allowed at c_2 when
  c_1 = 0 is exactly the statement that for a negative point the tail Y_2 itself only needs Y_2 > 0,
  not Y_2 > 1/lambda. The run forbidden at the c_k end (the root end) is the case b = n in Lemma 7,
  where Y_{n+1} = infinity plays the role of a digit >= 2. This matches the vision file's two ends.
- (iii) Reachability by forward moves. Proposition 3 (for every q the forward orbit is the group
  orbit of 0, because F^{-1} is reachable by forward moves through Lemma 2 and -lambda is in T) and
  Theorem 6 (for m = 1, 2, 3 that orbit is all of Q, by the height h = r^2/gcd(r, m)).
- Remark (not proved here, and nothing depends on it). In the group language one expects
  Stab(0) = G Stab(infinity) G = <G F G>. The identity Stab(0) = G Stab(infinity) G is trivial, but
  Stab(infinity) = <F> needs discreteness or a fundamental domain, which we do not prove or cite.
  The structure H_q = C_2 * C_q is stated in Short and Walker (arXiv:1310.1585, p. 1) and Winsor
  (arXiv:2605.30064, p. 4), both read in full (literature.md). If the paper needs it, it should be
  attributed there. We do not claim that Lemma 7 proves it.
  (Repair 2026-10-02: this replaces two sentences that stated these facts without proof.)

## 10. Sources

Nothing in Sections 1 to 8 relies on a source. Not accessed or checked in this session, so not to be
cited without checking: Hecke (Math. Ann. 112, 1936), Rosen (Duke Math. J. 21, 1954), Leutbecher
(1967, 1974), Burton, Kraaikamp and Schmidt (Trans. AMS 2000), and the conjugacy of H_4 and H_6 to
Gamma_0(2)+ and Gamma_0(3)+.

## 11. For the paper

- Main theorem can now be stated for every q >= 3 (A_q, B_q, C_q, with the tree equal to Q for
  m = 1, 2, 3) plus the free case. The q = 5 tree lives in Q(sqrt 5) and is computer-checked to rank 20
  (run 4), which is a consistency check of the all-q proofs.
- The proofs reuse the structure of Sections 3 and 4 of problem137.tex. The only new ingredients are
  Lemma 1 (the t_i), Lemma 2 (D4_q), the height h of Theorem 6, and Lemma 7.
- OEIS: the q = 4, 5, 6 count sequences are not in the OEIS (checks report and run 4).
