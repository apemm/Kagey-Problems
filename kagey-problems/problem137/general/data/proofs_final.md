# Final proofs for the general version of Problem 137

Date 2026-10-02. This file picks, for each main statement, the one complete proof that goes in the
paper. It is assembled from `proofs_route1.md` (R1, all q, X-coordinates) and `proofs_route2.md`
(R2, x-coordinates, m = 2, 3 and m >= 4) after the audit repair of the same date. Every step below
was read against the audit. No new computation was run for this file. The only new lookup was the
A060961 offset (ledger O1).

Labels. PROVED means a complete proof is printed here. COMPUTER-CHECKED means checked by two
methods to a stated range, with no proof. REFUTED means a recorded prediction failed.

## Summary of status

| statement | status | proof used |
|---|---|---|
| Lemma 1 (orbit of infinity under T = FG) | PROVED, every q >= 3 | R1 Lemma 1 |
| Lemma 2 (the long in-edge D4_q) | PROVED, every q >= 3 | R1 Lemma 2 |
| Proposition 3 (tree = parent-terminating set, closed under F, F^{-1}, G) | PROVED, every q >= 3 | R1 Prop. 3 |
| Theorem 4 (d = D, the analogue of Theorem 3.6) | PROVED, every q >= 3 | R1 Thm. 4 |
| Corollary 5 (C_q: unique shortest word, blue iff negative, children, jump) | PROVED, every q >= 3 | R1 Cor. 5 |
| Theorem 6 (forward reachability of all of Q for m = 1, 2, 3) | PROVED | R1 Thm. 6 |
| Lemma 7, Lemma 7', Theorem 8 (B_q) | PROVED, every q >= 3, on all of Q for m = 2, 3 | R1 Lemma 7, 7', Thm. 8 |
| Theorem 9 (A_q: N_q/D_q in lowest terms, recurrence from 2q - 2, fails at 2q - 3) | PROVED, every q >= 3 | R2 Thm. 9 count, extended to all q via Thm. 8, plus R1 coprimality |
| Proposition 10 (Pisot, C_q, blue share, psi_q increasing to phi) | PROVED, every q >= 3 | R2 Prop. 11 plus R1 Prop. 10 (repaired limit step) |
| Theorem 11 (free case m >= 4, and x + k with -1/x for k >= 2) | PROVED | R2 Thm. 10 |
| a(n) = nearest integer to C_q psi_q^n for all n >= 1, q = 4, 6 | COMPUTER-CHECKED (40-digit floats, no interval arithmetic) | ledger R2-5 |
| Counts a_2(n) to n = 28, a_3(n) to n = 30, q = 5 to n = 20 | COMPUTER-CHECKED (BFS and string enumeration) | ledger G1, G2, G9, G14, G15 |
| r(n) = A060961(n - 1) + A060961(n - 3) for m = 2 | PROVED (Theorem 9 plus the OEIS g.f. and offset 0) | ledger O1 |
| "C_q lies between 0.7 and 0.75" | REFUTED for q = 4 (C_4 = 0.75698) | ledger R2-4 |

## 0. Setting

Fix q >= 3, theta = pi/q, lambda = 2 cos theta, so 1 <= lambda < 2. Work with

    F(X) = X + lambda,    G(X) = -1/X  (X != 0),    root 0.

The m-tree (f(x) = x + 1, g_m(x) = -1/(m x)) is this tree under X = sqrt(m) x, because
sqrt(m)(x + 1) = X + sqrt(m) and sqrt(m) g_m(x) = -1/X. Since 2 cos(pi/3) = 1, 2 cos(pi/4) = sqrt 2
and 2 cos(pi/6) = sqrt 3, the cases m = 1, 2, 3 are q = 3, 4, 6.

O is the set of points reachable from 0 by F and by G at nonzero points, and d(X) is the rank. A word
f^{c_1} g f^{c_2} g ... g f^{c_k} acts right to left and has weight c_1 + ... + c_k + k - 1. The
parent map is P(X) = X - lambda for X > 0 and P(X) = -1/X for X < 0. For X != 0 there is an edge
P(X) -> X. Let T be the set of X whose parent sequence reaches 0, and D(X) the number of steps. So
D(0) = 0, and X in T, X != 0 gives P(X) in T and D(X) = D(P(X)) + 1.

## 1. Lemma 1 (PROVED)

Let T(Y) = F(G(Y)) = lambda - 1/Y, with T(0) = infinity and T(infinity) = lambda, and put
t_i = T^i(infinity) and U_i = sin((i + 1) theta)/sin theta. Then

(a) t_i = sin((i + 1) theta)/sin(i theta) for 1 <= i <= q - 1,
(b) infinity = t_0 > t_1 = lambda > t_2 > ... > t_{q-2} = 1/lambda > t_{q-1} = 0,
(c) T^q is the identity, and T^{-1}(0) = 1/lambda,
(d) for 0 <= i <= q - 3, T maps (t_{i+1}, t_i] increasingly onto (t_{i+2}, t_{i+1}].

*Proof.* U_{-1} = 0, U_0 = 1, U_1 = lambda and U_{i+1} = lambda U_i - U_{i-1}, from
sin((i + 2) t) + sin(i t) = 2 cos t sin((i + 1) t). By induction the matrix of T^i is
[[U_i, -U_{i-1}], [U_{i-1}, -U_{i-2}]] for i >= 1. So t_i = U_i/U_{i-1} whenever sin(i theta) != 0,
which holds for 1 <= i <= q - 1. This is (a). For these i, sin(i theta) > 0 and sin((i + 1) theta) >= 0,
with equality only at i = q - 1. For 1 <= i <= q - 2,

    t_i - t_{i+1} = sin^2(theta) / (sin(i theta) sin((i + 1) theta)) > 0,

by sin^2 a - sin(a - b) sin(a + b) = sin^2 b. Also t_{q-2} = sin(theta)/sin(2 theta) = 1/lambda. This
is (b). Since U_{q-1} = 0, U_q = -1 and U_{q-2} = 1, the matrix of T^q is -I, which is (c), and
T^{-1}(0) = T^{q-1}(t_{q-1}) = t_{2q-2} = t_{q-2} = 1/lambda. For (d), T is continuous and strictly
increasing on (0, infinity], and (t_{i+1}, t_i] lies in (0, infinity] when i + 1 <= q - 2. ∎

## 2. Lemma 2, the long in-edge D4_q (PROVED)

Let Z < 0 and Y = -1/Z > 0. Put P_1 = Y + lambda, N_i = -1/P_i, P_{i+1} = N_i + lambda = T(P_i) for
1 <= i <= q - 2, and N_{q-1} = -1/P_{q-1}. Then every P_i > 0, every N_i < 0, N_{q-1} = Z - lambda,
and P maps each point of the path Y -> P_1 -> N_1 -> ... -> P_{q-1} -> N_{q-1} to the point before
it. Hence Z is in T if and only if Z - lambda is in T, and then D(Z - lambda) = D(Z) + 2q - 3.

*Proof.* P_1 > lambda, so P_1 is in (t_1, t_0]. By Lemma 1(d), P_i is in (t_i, t_{i-1}] for
1 <= i <= q - 1, so P_i > 0 and N_i < 0. The path applies (GF)^{q-1} to Y. Since G is an involution,
GF = G T G, so (GF)^q = G T^q G = id by Lemma 1(c). Then (GF)^{q-1} = (GF)^{-1} = F^{-1} G, and
N_{q-1} = F^{-1}(G(Y)) = Z - lambda. G is applied only at the P_i, which are nonzero.
P(N_i) = P_i since N_i < 0, P(P_{i+1}) = N_i and P(P_1) = Y since the P_i are positive. So the path has
2q - 2 edges and P^{2q-2}(Z - lambda) = Y = P(Z). If Z is in T, then so is Y, so Z - lambda is in T and
D(Z - lambda) = 2q - 2 + D(Z) - 1. Conversely, if Z - lambda is in T, then Y is in T, so Z is. ∎

For q = 3 this is (D4) of problem137.tex.

## 3. Proposition 3 (PROVED)

(a) O = T. (b) T is closed under F, F^{-1}, and G at nonzero points. (c) -lambda is in T with
D(-lambda) = 2q - 4. (d) O together with infinity is the orbit of 0 under the group generated by F, G.

*Proof.* T is in O, since the reversed parent sequence is a path from 0. For O in T it suffices that
T is closed under F and G.

G. Let X in T, X != 0. If X > 0, then P(G(X)) = X, so G(X) is in T. If X < 0, G(X) = P(X) is in T.

F. Let X in T and W = X + lambda. If W > 0, then P(W) = X. If W = 0 it is the root. If W < 0, then
X = W - lambda, and Lemma 2 with Z = W gives W in T.

F^{-1}. Let X in T. If X > 0, X - lambda = P(X). If X < 0, use Lemma 2. If X = 0 we need -lambda.
Note P(-lambda) = 1/lambda = t_{q-2}. For 2 <= i <= q - 2, t_i - lambda = -1/t_{i-1} < 0, so
P(t_i) = -1/t_{i-1} and P(-1/t_{i-1}) = t_{i-1}. Also P(t_1) = 0. So the parent sequence of -lambda
is -lambda, t_{q-2}, -1/t_{q-3}, t_{q-3}, ..., t_1, 0, of length 2q - 4.

For (d), O with infinity added is closed under F, F^{-1}, G (F fixes infinity and G swaps 0 and
infinity), so it contains the orbit of 0. The converse is clear. ∎

## 4. Theorem 4, the analogue of Theorem 3.6 (PROVED)

For every X in O, d(X) = D(X). The increments are, for X in O,
(D1) X > 0: D(X) = D(X - lambda) + 1, (D2) X < 0: D(X) = D(-1/X) + 1,
(D3) X > 0: D(-1/X) = D(X) + 1, (D4_q) X < 0: D(X - lambda) = D(X) + 2q - 3.

*Proof.* (D1) and (D2) are the definition of D. (D3) is (D2) at -1/X, which is in T by
Proposition 3. (D4_q) is Lemma 2. The reversed parent sequence gives d <= D. For d >= D we check
D(W) <= D(V) + 1 on every edge V -> W with V in O. An F-edge into W > 0 is (D1). An F-edge into 0 is
trivial. An F-edge into W < 0 comes from V = W - lambda, and D(V) = D(W) + 2q - 3 by (D4_q). A G-edge
into W < 0 is (D2). A G-edge into W > 0 comes from V = -1/W < 0, and D(V) = D(W) + 1 by (D3). G never
gives 0. Summing along a shortest path gives D(X) <= d(X). ∎

## 5. Corollary 5, Conjecture C_q (PROVED, every q >= 3)

Let X in O, X != 0.
(a) The in-neighbors of X are X - lambda and -1/X, both in O. For X > 0 their ranks are d(X) - 1 and
d(X) + 1. For X < 0 they are d(X) + 2q - 3 and d(X) - 1. So P(X) is the only in-neighbor of rank
d(X) - 1.
(b) X has exactly one shortest word, the reversed parent sequence. In Kimberling's row construction
each point is written down once.
(c) The last move of the shortest word is f if X > 0 and g if X < 0. So a vertex is blue if and only if
it is negative.
(d) The root has the one child lambda. A vertex X > 0 has the children X + lambda and -1/X. A vertex in
(-lambda, 0) has the one child X + lambda. A vertex X <= -lambda is a leaf. For X < -lambda the value
X + lambda appeared exactly 2q - 3 ranks earlier, with d(X + lambda) = d(X) - (2q - 3). For X = -lambda
it is the root.

*Proof.* (a) Proposition 3(b) and Theorem 4. Since 2q - 3 >= 3 the two ranks differ. (b) Induction on
d(X) using (a). For the rows, a parent c with c + lambda = -1/c would solve c^2 + lambda c + 1 = 0,
which has no real root since lambda < 2. The rest is Corollary 3.8(a) of problem137.tex word for word.
(c) P(X) -> X is an F-edge for X > 0 and a G-edge for X < 0. (d) Solve P(Y) = X. Y > 0 needs
Y = X + lambda > 0, and Y < 0 needs X = -1/Y > 0. For X < -lambda apply (D4_q) to X + lambda < 0. ∎

In x-coordinates for m = 2, 3 this reads: for x < -1 the value x + 1 appeared exactly 2q - 3 ranks
earlier (five for m = 2, nine for m = 3), matching Theorem C and Corollary 3.8 of problem137.tex.

## 6. Theorem 6, forward reachability (PROVED for m = 1, 2, 3)

For m = 1, 2, 3 the m-tree is all of Q, and the parent map reaches 0 from every rational in exactly
d(x) steps.

*Proof.* Let T_m = {x : sqrt(m) x in T}. By Proposition 3(b), T_m contains 0 and is closed under
x -> x + 1, x -> x - 1 and x -> g_m(x) for x != 0. For x = p/r in lowest terms (r >= 1) put
h(x) = r^2/gcd(r, m). Since m is 1 or a prime, gcd(r, m) is 1 or m. Then h(x + n) = h(x) for every
integer n, and h(g_m(x)) = m x^2 h(x) for x != 0. Indeed, if m does not divide r, then g_m(x) = -r/(m p)
is in lowest terms up to sign and m divides its denominator, so h(g_m x) = m^2 p^2/m = m x^2 r^2. If m
divides r, then m does not divide p, g_m(x) = -(r/m)/p is in lowest terms with denominator prime to m,
and h(g_m x) = p^2 = m x^2 (r^2/m).

Now use strong induction on h, which takes values in the well-ordered set (1/m) Z_{>0}. Given x, pick
an integer n with |x - n| <= 1/2 and put y = x - n. Then x is in T_m if and only if y is, and
h(y) = h(x). If y = 0 we are done. Otherwise h(g_m y) = m y^2 h(y) <= (m/4) h(x) < h(x), since m <= 3.
By induction g_m(y) is in T_m, so y = g_m(g_m(y)) is too. The last claim is Theorem 4. ∎

The bound m y^2 <= m/4 < 1 is the only place m <= 3 is used. For m = 4 the set T_4 is not closed under
x -> x - 1 (Theorem 11), so the argument does not apply there.

An independent proof for m = 2, 3 (block descent of the same height along the parent map) is R2
Lemmas 2 to 4 with Theorem 5. It is not needed in the paper.

## 7. The run rule and Conjecture B_q (PROVED, every q >= 3)

Write [d_1, ..., d_n]_lambda = d_1 lambda - 1/(d_2 lambda - 1/(... - 1/(d_n lambda))), with tails
Y_j = [d_j, ..., d_n]_lambda and Y_{n+1} = infinity, so Y_j = d_j lambda - 1/Y_{j+1}.

**Lemma 7.** For digits d_j >= 1, all tails are defined and exceed 1/lambda if and only if the string
has no q - 2 consecutive 1's. Then every tail is positive.

*Proof.* If Y > 1/lambda then -1/Y is in (-lambda, 0), so d lambda - 1/Y > (d - 1) lambda >= lambda for
d >= 2, and lambda - 1/Y = T(Y).
(If) Going from j = n down to 1, let i be the length of the run of 1's at the left end of
d_j, ..., d_n. We show Y_j is in (t_{i+1}, t_i]. At the start Y_{n+1} = infinity is in (t_1, t_0]. If
d_j >= 2, then Y_j > lambda, so Y_j is in (t_1, t_0] and i = 0. If d_j = 1 and Y_{j+1} is in
(t_i, t_{i-1}], then Y_j = T(Y_{j+1}) is in (t_{i+1}, t_i] by Lemma 1(d), which applies since
i <= q - 3. Every Y_j then lies above t_{q-2} = 1/lambda.
(Only if) Let d_a = ... = d_b = 1 be a maximal run with b - a + 1 >= q - 2. Then Y_{b+1} is in
(t_1, t_0]. It is infinity if b = n, and otherwise d_{b+1} >= 2 with Y_{b+2} > 1/lambda. By Lemma 1(d),
Y_{b+1-s} is in (t_{s+1}, t_s] for s <= q - 2, so Y_{b+3-q} is in (0, 1/lambda]. Since b + 3 - q >= a,
this is a tail at most 1/lambda. ∎

**Lemma 7'.** Every X > 0 in O has exactly one representation X = [c_1, ..., c_k]_lambda with all
c_j >= 1 and all tails Y_j > 1/lambda for j >= 2. Its digits are read off the parent sequence, and
D(X) = c_1 + ... + c_k + k - 1.

*Proof.* Existence. The parent sequence of X subtracts lambda exactly c_1 = ceil(X/lambda) times and
reaches X - c_1 lambda in (-lambda, 0]. If this is 0, then k = 1. Otherwise one flip gives
Y_2 = -1/(X - c_1 lambda) > 1/lambda, which is in T, and X = c_1 lambda - 1/Y_2. Repeat with Y_2. This
stops since D drops by c_1 + 1 per round, and counting steps gives D(X). Uniqueness. If k >= 2, then
Y_2 > 1/lambda puts X in ((c_1 - 1) lambda, c_1 lambda), so X/lambda is not an integer, c_1 =
ceil(X/lambda) and Y_2 = 1/(c_1 lambda - X). If k = 1, X/lambda = c_1 is an integer. So k = 1 versus
k >= 2, c_1 and Y_2 are forced, and induction on k finishes it. ∎

Reduced strings. c_1 >= 0, c_2, ..., c_k >= 1, no q - 2 consecutive 1's among c_2, ..., c_k, except
that a run of exactly q - 2 starting at c_2 is allowed when c_1 = 0.

**Theorem 8 (B_q).** The map from reduced strings to f^{c_1} g f^{c_2} g ... g f^{c_k}(0) is a bijection
onto O. No reduced word applies g at 0, the rank of the value is the weight, and the reduced word of a
point is its unique shortest word. In X-coordinates the value is [c_1, ..., c_k]_lambda with
0 lambda - 1/Y = -1/Y. For m = 2, 3, by Theorem 6, every rational has exactly one reduced word, and
x = c_1 - 1/(m c_2 - 1/(c_3 - 1/(m c_4 - ...))).

*Proof.* Case c_1 >= 1. By Lemma 7 applied to (c_2, ..., c_k), the run rule is equivalent to all
tails Y_j > 1/lambda (j >= 2). So these are exactly the strings of Lemma 7', and they match the
positive points of O one to one with rank equal to weight. Each such word applies g only at positive
tails, and its value exceeds (c_1 - 1) lambda >= 0.
Case c_1 = 0, k >= 2. A run starting at c_2 of length L contributes L - 1 ones to c_3, ..., c_k, so
the rule says exactly that (c_2, ..., c_k) is a reduced string with first digit at least 1. By the
first case it is the string of a unique positive Y in O with d(Y) = c_2 + ... + c_k + k - 2. The value
is -1/Y. G is a bijection from the positive points of O to the negative ones, and
d(-1/Y) = d(Y) + 1 by (D3), which is the weight.
Case c_1 = 0, k = 1. The empty word, value 0.
The cases cover positive, negative and zero values. The reduced word spells the reversed parent
sequence (Lemma 7'), the unique shortest word by Corollary 5(b). ∎

At q = 3 the rule is Theorem B(ii) and Lemma 4.1 of problem137.tex.

## 8. Theorem 9, Conjecture A_q (PROVED, every q >= 3)

Let a(n) be the number of points of rank n and r(n) the number of positive ones. Put
D_q = 1 - t - t^3 - ... - t^{2q-3}, R_q = 1 + t^2 + ... + t^{2q-6} and
N_q = 1 + t^2 + ... + t^{2q-4} - t^{2q-3}. Then

    sum r(n) t^n = t R_q/D_q,    a(0) = 1,  a(n) = r(n) + r(n - 1) (n >= 1),    sum a(n) t^n = N_q/D_q,

with gcd(N_q, D_q) = 1. So a(n) = a(n-1) + a(n-3) + ... + a(n-2q+3) for every n >= 2q - 2, and it fails
at n = 2q - 3, where the left side minus the right side is -1. For m = 2, 3 these count rationals.

*Proof.* Positives. By Theorem 8, r(n) counts the strings with c_1 >= 1, c_2, ..., c_k >= 1, all runs
of 1's among c_2, ..., c_k of length at most q - 3, and weight n. Give c_1 the weight c_1 and each c_j
(j >= 2) the weight c_j + 1. Then c_1 contributes t/(1 - t), a later digit 1 contributes u = t^2 and a
later digit at least 2 contributes B = t^3/(1 - t). Read left to right, c_2, ..., c_k is uniquely a
run of at most q - 3 ones followed by any number of blocks (one digit at least 2, then a run of at
most q - 3 ones). Each run contributes R_q = 1 + u + ... + u^{q-3}, so

    sum r(n) t^n = t R_q/((1 - t)(1 - B R_q)) = t R_q/D_q,

because (1 - t)(1 - B R_q) = 1 - t - t^3 R_q and t^3 R_q = t^3 + ... + t^{2q-3}. The geometric series is
formal since B has no constant term.

Negatives. By (D2) and (D3), X -> -1/X is a bijection from the negative points of rank n to the
positive points of rank n - 1. So a(n) = r(n) + r(n - 1) for n >= 1, and
sum a(n) t^n = 1 + (1 + t) t R_q/D_q. Now (1 + t) t R_q = t + t^2 + ... + t^{2q-4}, and adding D_q
cancels t, t^3, ..., t^{2q-5} and leaves N_q.

Lowest terms. N_q - D_q = t + ... + t^{2q-4}. A common root alpha has alpha != 0 (D_q(0) = 1) and
alpha != 1 (D_q(1) = 2 - q), so alpha^{2q-4} = 1. Also (1 - t^2) D_q = 1 - t - t^2 + t^{2q-1}, which at
alpha equals 1 - alpha - alpha^2 + alpha^3 = (1 - alpha)(1 - alpha^2). So alpha = 1 or alpha = -1. But
D_q(-1) = q != 0.

Recurrence. The coefficient of t^n in D_q(t) A(t) is a(n) - a(n-1) - a(n-3) - ... - a(n-2q+3), and it
equals [t^n] N_q, which is 0 for n >= 2q - 2 and -1 at n = 2q - 3. ∎

Checks (not part of the proof): the series equals the BFS counts to rank 28 (q = 4), 30 (q = 6) and
20 (q = 5, in Q(sqrt 5)), by two methods each (ledger G9, G14). For m = 2,
r(n) = A060961(n - 1) + A060961(n - 3), since t R_4 = t + t^3 and A060961 has g.f. 1/D_4 and offset 0
(ledger O1). The count sequences for q = 4, 5, 6 have no OEIS entry.

## 9. Proposition 10, growth (PROVED, every q >= 3)

(a) D_q has exactly one root t_0 in (0, 1). It is simple, and every other root has modulus greater than
1, so psi_q = 1/t_0 is a Pisot number, the positive root of psi^{2q-3} = psi^{2q-4} + psi^{2q-6} + ... + 1.
(b) a(n) = C_q psi_q^n + epsilon(n) with C_q = (1 + t_0) R_q(t_0)/(-D_q'(t_0)) > 0 and epsilon(n) -> 0
exponentially. The share of blue (negative) points of rank n tends to 1/(1 + psi_q).
(c) psi_3 < psi_4 < psi_5 < ... and psi_q -> phi.

*Proof.* (a) The sum t + t^3 + ... + t^{2q-3} increases on [0, 1] from 0 to q - 1 >= 2, so D_q has one
root t_0 in (0, 1), and D_q'(t_0) < 0. Let n = 2q - 1 and H = (1 - t^2) D_q = 1 - t - t^2 + t^n. For
t = r e^{i theta} and c = cos theta,

    |1 - t - t^2|^2 = 1 + 3r^2 + r^4 - 2rc(1 - r^2) - 4r^2 c^2,

which is concave in c, so its minimum on |t| = r is at c = 1 or c = -1, where it is (r^2 + r - 1)^2 or
(1 + r - r^2)^2. For 0.62 < r <= 1 the smaller is (r^2 + r - 1)^2. The function r^2 + r - 1 - r^n
vanishes at r = 1 with derivative 3 - n < 0, so it is positive on some (1 - delta, 1). For such r with
r > t_0, |t^n| < |1 - t - t^2| on |t| = r, and Rouché's theorem gives H as many zeros in |t| < r as
1 - t - t^2, which is one (its zeros are 0.618... and -1.618...). That zero is t_0. So D_q has no other
zero in the open unit disk. On |t| = 1 a zero of H needs 5 - 4c^2 = 1, so t = 1 or -1, and
D_q(1) = 2 - q, D_q(-1) = q are nonzero.

(b) A(t) = 1 + (1 + t) t R_q/D_q. Partial fractions give a(n) = C t_0^{-n} plus terms p_i(n) t_i^{-n}
over the other roots, which tend to 0 by (a). Here C = -N_q(t_0)/(t_0 D_q'(t_0)), and
N_q(t_0) = D_q(t_0) + (1 + t_0) t_0 R_q(t_0) = (1 + t_0) t_0 R_q(t_0) > 0, which gives C_q. The same
computation for t R_q/D_q gives r(n) ~ R_q(t_0)/(-D_q'(t_0)) psi_q^n. The negatives of rank n are
counted by r(n - 1), so their share tends to t_0/(1 + t_0) = 1/(1 + psi_q).

(c) D_{q+1} = D_q - t^{2q-1}, so D_{q+1}(t_0) < 0 and the root decreases in q. Put
L(t) = (1 - t - t^2)/(1 - t^2). Then D_q(t) - L(t) = t^{2q-1}/(1 - t^2) > 0 on (0, 1). Since
L(1/phi) = 0, D_q(1/phi) > 0, so t_0 > 1/phi. For 0 < eps < 1 - 1/phi and s = 1/phi + eps, L(s) < 0 and
D_q(s) - L(s) = s^{2q-1}/(1 - s^2) -> 0, so D_q(s) < 0 for large q and t_0 < s. So t_0 -> 1/phi. ∎

Values (computer-checked, two formulas for C_q agree): psi_3 = 1.46557, psi_4 = 1.57015,
psi_6 = 1.61193, C_3 = 0.70193, C_4 = 0.75698, C_6 = 0.73786, C_infinity = phi/sqrt 5 = 0.72361. C_q
is not monotone. psi_4 is the constant A293506 (literature.md).

## 10. Theorem 11, the free case (PROVED)

Let m >= 4 be an integer, f(x) = x + 1, g(x) = -1/(m x). This covers x -> x + k with -1/x for every
k >= 2, which is m = k^2 after x = k y. Call a string free if it is (0), or c_1 >= 1 and
c_2, ..., c_k >= 1, or c_1 = 0, k >= 2 and c_2, ..., c_k >= 1.

(a) Every tail (c_j, ..., c_k), j >= 2, of a free string has value greater than 1/2. A free string with
c_1 >= 1 has value in (c_1 - 2/m, c_1], and one with c_1 = 0, k >= 2 has value in (-2/m, 0). Distinct
free strings have distinct values, and g is never applied to 0.
(b) The reachable rationals are exactly the values of free strings, and the rank is the weight.
(c) a(n) = F(n + 1) for every n >= 0, r(n) = F(n) for n >= 1, with generating function 1/(1 - t - t^2).
(d) Blue if and only if negative, and the shortest word is unique.
(e) The tree is a proper subset of Q. No rational in (-infinity, -2/m] or in (c - 1, c - 2/m] for an
integer c >= 1 is reached. In particular -1 and 1/2 are never reached.

*Proof.* (a) c_k >= 1 > 1/2. If T > 1/2, then c - 1/(m T) > 1 - 2/m >= 1/2 for c >= 1. Downward
induction gives the tail bound and shows g is applied only to positive numbers. Then
c_1 - 1/(m T_2) is in (c_1 - 2/m, c_1) for k >= 2, and -1/(m T_2) is in (-2/m, 0). Since 2/m <= 1/2, the
value x of a string with c_1 >= 1 determines c_1 = ceil(x), whether k = 1, and the tail value
1/(m(c_1 - x)). A negative value determines c_1 = 0 and the tail value g(x). Induction on k gives
uniqueness.
(b) Let V be the set of values and W(x) the weight of the string of x. Each word reaches its value in
W(x) moves, so d <= W on V. For y in V: f(0) = 1 = [1]. If y > 0, f(y) has string (c_1 + 1, ...) and
g(y) has string (0, c_1, ..., c_k), both of weight W(y) + 1. If y < 0 with string (0, c_2, ..., c_k),
g(y) is the value of (c_2, ..., c_k), of weight W(y) - 1, and f(y) has string (1, c_2, ..., c_k), of
weight W(y) + 1. So V is closed under the moves and W goes up by at most 1 per move. Hence W <= d,
and nothing outside V is reached.
(c) Positives give t/(1 - t) times 1/(1 - u - B) = t/((1 - t)(1 - t^2) - t^3) = t/(1 - t - t^2). The map
g pairs negatives of rank n with positives of rank n - 1, so A(t) = 1 + (t + t^2)/(1 - t - t^2) =
1/(1 - t - t^2).
(d) For x < 0, x - 1 < -1 <= -2/m is not reached by (a) and (b), so the last move is g. For x > 0, g(x)
has rank d(x) + 1, so the last move is f. Uniqueness of the shortest word follows by induction.
(e) Immediate from (a) and (b). Note -1 <= -2/m, and 1/2 is in (0, 1 - 2/m] since m >= 4. ∎

For m = 4, f(-1/2) = g(-1/2) = 1/2 and the parent map cycles between 1/2 and -1/2. Both are unreached
by (e). This is G10.

## 11. What remains open or only computer-checked

- a(n) is the nearest integer to C_q psi_q^n for every n >= 1 (q = 4, 6). COMPUTER-CHECKED only: the
  triangle bound on the error is below 1/2 from n = 6 (q = 4) and n = 11 (q = 6), with 40-digit floats
  and direct comparison below that. Not interval arithmetic, so not proved. (The preregistered R2-5,
  "below 1/2 from n = 1", was REFUTED.)
- Stab(0) = <G F G> in H_q. Not proved and not used. The identity needs Stab(infinity) = <F>.
- H_q = C_2 * C_q. Not proved here and not used. Stated in Short and Walker (p. 1) and Winsor (p. 4),
  both read in full. Attribute to them if the paper mentions it.
- Whether the tree (the H_q-orbit of 0, minus infinity) is the full cusp set lambda Q(lambda^2) for q
  other than 3, 4, 6. Not claimed. For q = 5, 8, 10, 12 the literature reports equality (Leutbecher,
  SECONDARY or PARTIAL in literature.md), and for most q >= 7 it is open.
- An exact description of which rationals are reached for m >= 4. Only the necessary conditions of
  Theorem 11(a), (e) are proved.
- The guess "C_q between 0.7 and 0.75" is REFUTED for q = 4.

## 12. Audit items and what was done

1. R1 Section 9 group remarks: relabeled as an unproved remark with the C_2 * C_q sources. Fixed.
2. R1 "Note on m = 4" and the ledger line about G10: reworded as a heuristic, correction appended to
   the ledger. Fixed.
3. R1 Proposition 10 limit step: sign argument added (and used in Section 9(c) here). Fixed.
4. R1 Theorem 9 count: printed in full, left to right. The paper uses the positive-only count plus
   a(n) = r(n) + r(n - 1) (Section 8 here). Clarifying note appended to checks_report.md. Fixed.
5. "2q - 3 ranks older": now "appeared exactly 2q - 3 ranks earlier, with d(x + 1) = d(x) - (2q - 3)" in
   R1 Corollary 5(d), R2 Corollary 6(c) and here. Fixed.
6. Out-of-date status lines: dated updates appended to checks_report.md and literature.md, and the R1
   status row now matches literature.md's access levels. Fixed.
7. A060961 hedge: offset 0 checked on the OEIS page (ledger O1), hedge removed in R2 Section 8. Fixed.
8. Nearest integer: kept as computer-checked. No change needed.

No audit item was rejected. Each one was checked against the text and found accurate.
