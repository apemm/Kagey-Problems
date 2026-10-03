# Route 2 proofs for the general version of Problem 137 (continued fractions, x-coordinates)

Date 2026-10-02. This file proves, in the style of `problem137.tex` (Lemma 4.1, Theorem 3.6,
Corollary 4.3, Theorems A, B, C), the rank formula, the colors, the generating function and the
asymptotics for m = 2 and m = 3, and the free case m >= 4. Everything is done in x-coordinates with
elementary algebra. No group theory and no outside source is used in any proof.

Input from `checks_report.md` (it exists, read before writing). No prediction there failed, so the
reduced-word rule of the vision file is the final rule, and this file proves it. The computer checks
of the new claims below are in `ledger.md` (R2-1 to R2-5), with output in `route2_run.txt` and
`route2b_run.txt` and code in `../route2_checks.py` and `../route2_asymp.py`.

## Status of every statement

| statement | status |
|---|---|
| Lemma 1 (the jump d(x - 1) = d(x) + 2q - 3 for x < 0), m = 2, 3 | proved. Computer-checked (R2-1) |
| Lemma 2 (height ht(p/q) = q^2/gcd(q, m)), m = 1, 2, 3 | proved. Computer-checked (R2-2) |
| Lemma 3 (runs of 1's and the drop of ht over a block), m = 2, 3 | proved. Computer-checked (R2-2) |
| Lemma 4 (the parent map reaches 0), m = 2, 3 | proved |
| Theorem 5 (d = D, the analogue of Theorem 3.6), m = 2, 3 | proved |
| Corollary 6 (in-neighbors, colors C_q, the tree), m = 2, 3 | proved |
| Lemma 7 (existence and uniqueness of the expansion, the analogue of Lemma 4.1), m = 2, 3 | proved |
| Theorem 8 (rank formula B_q), m = 2, 3 | proved |
| Theorem 9 (generating function A_q, first index 2q - 2, failure at 2q - 3), m = 2, 3 | proved. Matches the BFS counts to rank 28 and 30 |
| Theorem 10 (free case m >= 4: a(n) = F(n+1), colors, -1 and 1/2 not reached) | proved. Computer-checked (R2-3) |
| Proposition 11 (psi_q, C_q, all other roots of D_q outside the unit disk) | proved for every q >= 3 |
| a(n) = nearest integer to C_q psi_q^n for every n >= 1 (q = 4, 6) | computer-checked (R2-5, 40-digit floating point) |
| Guess "C_q between 0.7 and 0.75" | refuted for q = 4 (C_4 = 0.75698). Held for q = 6 |

## 0. Setting

Fix m in {2, 3} (m = 1 is the existing paper and every argument below reduces to it). Put

    f(x) = x + 1,    g(x) = -1/(m x)   (x != 0),    q = 4 if m = 2,  q = 6 if m = 3.

Note that g(g(x)) = x, so g is its own inverse. The graph G, the rank d(x), X_n, a(n) and
r(n) = |X_n ∩ Q_{>0}| are as in Definition 3.1 of the paper, with this g. The parent map is

    P(x) = x - 1  (x > 0),    P(x) = g(x) = -1/(m x)  (x < 0).

As in the paper, there is an edge P(x) -> x for every x != 0 (an f-edge if x > 0, a g-edge if x < 0,
and g is applied to g(x) != 0).

Why q. The matrix of g∘f is M = [[0, -1], [m, m]]. For m = 2, M^2 = [[-2, -2], [4, 2]] and
M^4 = -4 I. For m = 3, M^2 = [[-3, -3], [9, 6]], M^3 = [[-9, -6], [18, 9]] and M^6 = -27 I, while
M, M^2, M^3 are not scalar. So g∘f has order exactly 4 and 6 as a Möbius map (proved, by hand).
Lemma 1 below does not use this. It checks the needed identity directly.

The expansion. For integers c_1, ..., c_k put [c_1] = c_1 and

    [c_1, c_2, ..., c_k]_m = c_1 - 1/(m [c_2, ..., c_k]_m),

whenever the denominators are nonzero. Unwinding the recursion gives the alternating form
c_1 - 1/(m c_2 - 1/(c_3 - 1/(m c_4 - ...))). Applying f^{c_k}, then g, then f^{c_{k-1}}, ..., then
f^{c_1} to 0 gives [c_1, ..., c_k]_m, provided g is never applied to 0. The weight of the string is
c_1 + ... + c_k + k - 1, the length of that word.

Reduced strings (the rule of the vision file and of `checks_report.md`). The string (0) is reduced.
A string with k >= 1, c_1 >= 1 and c_2, ..., c_k >= 1 is reduced if every run of consecutive 1's
among c_2, ..., c_k has length at most q - 3. A string with c_1 = 0, k >= 2 and c_2, ..., c_k >= 1 is
reduced if the run of 1's starting at c_2 has length at most q - 2 and every other run among
c_2, ..., c_k has length at most q - 3. For m = 2 this means no two consecutive 1's, except
c_2 = c_3 = 1 when c_1 = 0. For m = 3 it means no four consecutive 1's, except four 1's starting at
c_2 when c_1 = 0.

The thresholds. Put h(T) = 1 - 1/(m T) for T > 0, which is increasing, and t_0 = 1,
t_{i+1} = h(t_i). Then

| m | t_0 | t_1 | t_2 | t_3 | t_4 |
|---|---|---|---|---|---|
| 2 | 1 | 1/2 | 0 | | |
| 3 | 1 | 2/3 | 1/2 | 1/3 | 0 |

So t_{q-3} = 1/m and t_{q-2} = 0 in both cases. We also put t_{-1} = infinity and h(infinity) = 1.

## 1. The jump

**Lemma 1 (the jump, the analogue of (D4)).** Let x < 0 and z = x - 1. Then the parent sequence of z
reaches P(x) = -1/(m x) after exactly 2q - 2 steps, and none of these steps passes through 0. Hence,
once D is defined (Definition 3.3 of the paper, which needs Lemma 4), D(x - 1) = D(x) + 2q - 3,
that is D(x) + 5 for m = 2 and D(x) + 9 for m = 3.

*Proof.* Write a_0 = z and a_{i+1} = P(a_i). We list a_i as a function of x and the interval it lies
in. Each interval follows from the previous one, and the sign of a_i decides which case of P applies
next.

m = 2. Since x < 0 we have z < -1.

| i | a_i | interval | next step |
|---|---|---|---|
| 0 | x - 1 | (-inf, -1) | flip |
| 1 | 1/(2(1 - x)) | (0, 1/2) | subtract |
| 2 | (2x - 1)/(2(1 - x)) | (-1, -1/2) | flip |
| 3 | (1 - x)/(1 - 2x) | (1/2, 1) | subtract |
| 4 | x/(1 - 2x) | (-1/2, 0) | flip |
| 5 | 1 - 1/(2x) | (1, inf) | subtract |
| 6 | -1/(2x) | (0, inf) | |

m = 3.

| i | a_i | interval | next step |
|---|---|---|---|
| 0 | x - 1 | (-inf, -1) | flip |
| 1 | 1/(3(1 - x)) | (0, 1/3) | subtract |
| 2 | (3x - 2)/(3(1 - x)) | (-1, -2/3) | flip |
| 3 | (1 - x)/(2 - 3x) | (1/3, 1/2) | subtract |
| 4 | (2x - 1)/(2 - 3x) | (-2/3, -1/2) | flip |
| 5 | (2 - 3x)/(3(1 - 2x)) | (1/2, 2/3) | subtract |
| 6 | (3x - 1)/(3(1 - 2x)) | (-1/2, -1/3) | flip |
| 7 | (1 - 2x)/(1 - 3x) | (2/3, 1) | subtract |
| 8 | x/(1 - 3x) | (-1/3, 0) | flip |
| 9 | 1 - 1/(3x) | (1, inf) | subtract |
| 10 | -1/(3x) | (0, inf) | |

Each formula comes from the one above it. For example, for m = 3, a_3 = -1/(3 a_2) =
-(1 - x)/(3x - 2) = (1 - x)/(2 - 3x), and a_4 = a_3 - 1 = (2x - 1)/(2 - 3x). Each interval comes from
the one above it. A flip sends (-1, -2/3) to (1/3, 1/2) because 3|a| runs over (2, 3), and so on. The
first interval holds because 1 - x > 1. The last line is -1/(m x) = P(x). No a_i is 0, so
D(z) = (2q - 2) + D(P(x)) = 2q - 2 + D(x) - 1 = D(x) + 2q - 3. ∎

Read backwards, the table is a path of 2q - 2 moves from g(x) to x - 1, the relation f^{-1} =
(g f)^{q-1} g of the vision file. For m = 1 the same table with three lines is the proof of (D4) in the
paper.

## 2. The height and termination

**Lemma 2 (height).** For x = p/q' in lowest terms (q' >= 1) put ht(x) = q'^2 / gcd(q', m). Then ht is
a positive integer, ht(x + 1) = ht(x), and for x != 0

    ht(-1/(m x)) = m x^2 ht(x).

*Proof.* Since m is 1 or a prime, gcd(q', m) is 1 or m, and q'^2/m is an integer when m | q'. Adding 1
keeps the denominator. For the flip, -1/(m x) = -q'/(m p). Since gcd(p, q') = 1, the gcd of q' and
m p is e = gcd(q', m). So in lowest terms the new denominator is m|p|/e. If e = 1 it is m|p|, which m
divides, so the new height is m^2 p^2/m = m p^2 = m x^2 q'^2 = m x^2 ht(x). If e = m it is |p|, which
is prime to m because m | q' and gcd(p, q') = 1, so the new height is p^2 = m x^2 (q'^2/m) =
m x^2 ht(x). ∎

The parent sequence of a positive y subtracts 1 exactly c = ceil(y) times and reaches y - c in (-1, 0].
If y - c = -w with 0 < w < 1, the next step is a flip to 1/(m w) > 0. Call the next ceiling,
c' = ceil(1/(m w)), the digit of this flip. Note that c' = 1 exactly when w >= 1/m. If c' = 1, the
next state is -w' with w' = 1 - 1/(m w) = h(w).

**Lemma 3 (runs and blocks).** Let w_0, ..., w_j be in (0, 1) with w_{i+1} = 1 - 1/(m w_i) and
w_i >= 1/m for i < j (the first j flips have digit 1), and w_j < 1/m (the flip from -w_j has digit
at least 2). Then j <= q - 3, and

    (m w_0^2)(m w_1^2) ... (m w_j^2) < 1.

Also, if w_0 is in (0, 1) and the flips from -w_0, ..., -w_{j-1} all have digit 1 and none of the
states is 0, then j <= q - 3.

*Proof.* m = 2. If j >= 1, then w_0 >= 1/2 and w_1 = 1 - 1/(2 w_0) < 1/2 since w_0 < 1, so the flip
from -w_1 has digit at least 2. Hence j <= 1 = q - 3. If j = 0 the product is 2 w_0^2 < 2/4 = 1/2. If
j = 1 note that 2 w_0 w_1 = 2 w_0 - 1, so the product is (2 w_0 w_1)^2 = (2 w_0 - 1)^2 < 1.

m = 3. While the digits are 1, direct substitution gives

    w_1 = (3w_0 - 1)/(3w_0),   w_2 = (2w_0 - 1)/(3w_0 - 1),   w_3 = (3w_0 - 2)/(3(2w_0 - 1)),

    w_0 w_1 = (3w_0 - 1)/3,   w_0 w_1 w_2 = (2w_0 - 1)/3,   w_0 w_1 w_2 w_3 = (3w_0 - 2)/9.

The condition w_1 >= 1/3 is 3w_0 - 1 >= w_0, that is w_0 >= 1/2. The condition w_2 >= 1/3 is
3(2w_0 - 1) >= 3w_0 - 1, that is w_0 >= 2/3. The condition w_3 >= 1/3 is 3w_0 - 2 >= 2w_0 - 1, that
is w_0 >= 1, which is impossible. So at most three flips in a row have digit 1, and j <= 3 = q - 3.
The product equals 3^{j+1} (w_0 ... w_j)^2, and by the formulas it is

| j | product | range of w_0 | bound |
|---|---|---|---|
| 0 | 3 w_0^2 | (0, 1/3) | < 1/3 |
| 1 | (3w_0 - 1)^2 | [1/3, 1/2) | < 1/4 |
| 2 | 3 (2w_0 - 1)^2 | [1/2, 2/3) | < 1/3 |
| 3 | (3w_0 - 2)^2 | [2/3, 1) | < 1 |

The range of w_0 in row j says that the first j digits are 1 and the next is not. For example, in row
two, w_1 >= 1/3 gives w_0 >= 1/2 and w_2 < 1/3 gives w_0 < 2/3. ∎

**Lemma 4 (termination, the analogue of Lemma 3.2).** For m = 2, 3 and every rational x the parent
sequence x, P(x), P^2(x), ... reaches 0.

*Proof.* Suppose it does not. Each run of subtractions is finite, so there are infinitely many flips.
Let -w_0, -w_1, ... be the states just before them. Each state after a run of subtractions lies in
(-1, 0) (it is not 0 by assumption), so w_i is in (0, 1) for all i >= 1, and also for i = 0 when
x > 0. By Lemma 3 every q - 2 consecutive flips from i = 1 on include one with digit at least 2. So
the flips from i = 1 on split into consecutive blocks, each a run of j <= q - 3 flips with digit 1
followed by one flip with digit at least 2. By Lemma 2 subtractions do not change ht and a flip from
-w multiplies it by m w^2. So by Lemma 3 the height after each block is strictly less than the height
before it. This gives an infinite strictly decreasing sequence of positive integers, which is
impossible. ∎

The existing paper's proof uses the denominator. Here the denominator alone fails, for example
-2/3 -> 3/4 for m = 2. The height ht drops over every block but not over every flip (the flip from
-2/3 multiplies ht by 8/9 here, but the flip from -3/4 to 2/3 multiplies it by 9/8). That is why the
proof groups the flips into blocks.

## 3. The distance formula and the colors

Define D(x) as the number of parent steps from x to 0 (finite by Lemma 4), as in Definition 3.3.
Lemma 3.4 (uniqueness principle) holds with the same proof.

**Theorem 5 (exact distance formula, the analogue of Theorem 3.6).** For m = 2, 3 every rational is
reachable from 0, and d(x) = D(x) for all x.

*Proof.* The increments are

- (D1) D(x) = D(x - 1) + 1 for x > 0, and (D2) D(x) = D(g(x)) + 1 for x < 0. These are the definition.
- (D3) D(g(x)) = D(x) + 1 for x > 0, by (D2) applied to g(x) < 0, since g(g(x)) = x.
- (D4) D(x - 1) = D(x) + 2q - 3 for x < 0, by Lemma 1.

Step 1. The reversed parent sequence is a path of length D(x) from 0 to x, so d(x) <= D(x).

Step 2. D(x) <= D(y) + 1 for every edge y -> x. An f-edge into x > 0 is (D1). An f-edge into 0 comes
from -1. An f-edge into x < 0 comes from y = x - 1, and D(x) = D(y) - (2q - 3) by (D4). A g-edge into
x < 0 is (D2). A g-edge into x > 0 comes from y = g(x) < 0, and D(x) = D(y) - 1 by (D3). There is no
g-edge into 0.

Step 3. Along a shortest path 0 = y_0 -> ... -> y_n = x Step 2 gives D(x) <= n = d(x). ∎

**Corollary 6 (the tree and the colors, the analogue of Theorem C).** Let m = 2 or 3 and x != 0.

(a) The in-neighbors of x are x - 1 and g(x). If x > 0 their ranks are d(x) - 1 and d(x) + 1. If x < 0
they are d(x) + 2q - 3 and d(x) - 1. So P(x) is the only in-neighbor closer to the root.

(b) Every shortest path to x ends with an f-edge if x > 0 and a g-edge if x < 0. So a vertex is blue if
and only if it is negative (Conjecture C_q holds for q = 4, 6). In Kimberling's construction with this
g, each x != 0 is written down exactly once, by P(x). No value is produced twice, because a parent c
reaches x by only one move. Indeed c + 1 = -1/(m c) means m c^2 + m c + 1 = 0, whose discriminant
m^2 - 4m is negative for m <= 3.

(c) A vertex x > 0 has the two children x + 1 and g(x). A vertex in (-1, 0) has the one child x + 1. The
root has the one child 1. A vertex x <= -1 is a leaf, and for x < -1 the value x + 1 appeared exactly
2q - 3 ranks earlier, with d(x + 1) = d(x) - (2q - 3), that is five ranks for m = 2 and nine for m = 3.

*Proof.* As for Corollaries 3.7 and 3.8 of the paper, using (D1) to (D4). Since g is an involution,
g(y) = x only for y = g(x). The proof of (b) by induction on n, and of (c) by solving P(y) = x, is
word for word the same. ∎

## 4. The expansion and the rank formula

**Lemma 7 (existence and uniqueness, the analogue of Lemma 4.1).** Let m = 2 or 3.

(a) Let (c_1, ..., c_k) be reduced with c_1 >= 1, and let r be the number of 1's at its start (the
length of the run of 1's that begins at c_1). Then g is never applied to 0 in evaluating it, r <= q - 2,
and its value x = [c_1, ..., c_k]_m lies in (t_r, t_{r-1}] and in (c_1 - 1, c_1]. In particular x > 0,
c_1 = ceil(x), and x is an integer only when k = 1. Every tail (c_j, ..., c_k) with j >= 2 has value
greater than 1/m.

(b) Every rational x > 0 has exactly one reduced string, and its first digit is ceil(x) >= 1.

(c) For x < 0 the reduced strings of x are exactly (0, s) with s the reduced string of g(x) > 0. The
string (0) is the only reduced string of 0. So every rational has exactly one reduced string.

*Proof.* (a) Induction on k. If k = 1 then x = c_1. If c_1 >= 2 then r = 0 and x is in (1, infinity) =
(t_0, t_{-1}]. If c_1 = 1 then r = 1 and x = 1 is in (t_1, t_0]. Let k >= 2. The tail s = (c_2, ..., c_k)
is reduced with first digit at least 1, and its initial run r' is a run among c_2, ..., c_k, so
r' <= q - 3. By induction its value T is in (t_{r'}, t_{r'-1}], so T > t_{r'} >= t_{q-3} = 1/m > 0.
Hence g is applied to T != 0, and x = c_1 - 1/(m T) is in (c_1 - 1, c_1). The other tails are tails of
s, so they are greater than 1/m by induction. If c_1 >= 2 then r = 0 and x > c_1 - 1 >= 1 = t_0. If
c_1 = 1 then r = r' + 1, and x = h(T) with T in (t_{r-1}, t_{r-2}]. Since h is increasing with
h(t_i) = t_{i+1} and h(infinity) = 1 = t_0, x is in (t_r, t_{r-1}]. Finally r = 1 + r' <= q - 2.

(b) Uniqueness. Take a reduced string of x > 0. The string (0) has value 0, and a string with c_1 = 0
and k >= 2 has value -1/(m T) < 0, with T > 0 by (a) applied to its tail (see (c)). So c_1 >= 1. By
(a), if x is an integer then k = 1 and the string is (x). Otherwise k >= 2, c_1 = ceil(x), and the
tail value is T = 1/(m(c_1 - x)), so both are determined by x. The tail is a reduced string of T, so it
is unique by induction on k.

Existence. We use induction on D(x), which is finite by Lemma 4. If x is a positive integer, (x) is
reduced. Otherwise put c = ceil(x) and y = 1/(m(c - x)). Then y > 1/m because c - x < 1, and
D(y) = D(x) - c - 1 < D(x), since the parent sequence of x is c subtractions and one flip to y. By
induction y has a reduced string, with some initial run r. By (a) y <= t_{r-1}, and y > 1/m = t_{q-3}
forces r - 1 < q - 3, that is r <= q - 3. So (c, string of y) is reduced, and its value is
c - 1/(m y) = x.

(c) Let x < 0. A string with c_1 >= 1 has a positive value by (a), so c_1 = 0 and x = -1/(m T) with T
the value of (c_2, ..., c_k). So T = g(x). Now (c_2, ..., c_k) satisfies the rule for c_1 = 0 (run at
c_2 at most q - 2, others at most q - 3) exactly when it is a reduced string with first digit c_2 >= 1.
Indeed, by (a) a reduced string with c_1 >= 1 has initial run at most q - 2, and every other run lies
among its digits after the first, so has length at most q - 3. The converse is the definition. So the
reduced strings of x are the strings (0, s) with s reduced for g(x), and by (b) there is exactly one.
The value of a string with c_1 >= 1 is positive and with c_1 = 0, k >= 2 is negative, so only (0)
gives 0. ∎

**Theorem 8 (rank formula, Conjecture B_q for q = 4, 6, the analogue of Theorem 4.2).** For m = 2, 3
and every rational x with reduced string (c_1, ..., c_k),

    d(x) = c_1 + c_2 + ... + c_k + k - 1,

and the word f^{c_1} g f^{c_2} g ... g f^{c_k} (applied right to left, starting at 0) is the reversed
parent path of x, so it is a shortest path.

*Proof.* By Theorem 5 we compute D, by induction on D(x). D(0) = 0 and the string of 0 is (0). If
x > 0 is an integer, D(x) = x. If x > 0 is not an integer, c_1 = ceil(x), the values x, x - 1, ...,
x - c_1 + 1 are positive and x - c_1 is in (-1, 0), so D(x) = c_1 + 1 + D(y) with
y = 1/(m(c_1 - x)), whose string is (c_2, ..., c_k) by Lemma 7. By induction
D(y) = c_2 + ... + c_k + k - 2, which gives the formula. If x < 0, D(x) = 1 + D(g(x)), and the
string of x is (0, string of g(x)), which gives the formula with c_1 = 0. The parent path follows
the digits in the same order, which proves the last claim. ∎

**Corollary 8.1 (the ranks explicitly, the analogue of Corollary 4.3).** For n >= 1, X_n ∩ Q_{>0} is
the set of values of the reduced strings with c_1 >= 1 and weight n, and X_n ∩ Q_{<0} =
{g(y) : y in X_{n-1} ∩ Q_{>0}}. Each element is listed once. (Proof as for Corollary 4.3, using
Lemma 7, Theorem 8, (D2) and (D3).)

Examples (proved, by the algorithm of Lemma 7, and matching the BFS ranks). For m = 2,
1/2 = [1, 1]_2 has rank 3 (path 0 -> 1 -> -1/2 -> 1/2), 3/4 = [1, 2]_2 has rank 4, and
-1/2 = g(1) = [0, 1]_2 has rank 2. For m = 2, [0, 1, 1]_2 = g(1/2) = -1 has
rank 4. Here the run c_2 = c_3 = 1 is the allowed exception. For m = 3, -1 = [0, 1, 1, 1, 1]_3 has
rank 8 (the run of four 1's at c_2).

## 5. The generating function

Put D_q(t) = 1 - t - t^3 - t^5 - ... - t^{2q-3}, R_q(t) = 1 + t^2 + ... + t^{2q-6} and
N_q(t) = 1 + t^2 + t^4 + ... + t^{2q-4} - t^{2q-3}.

**Theorem 9 (Conjecture A_q for q = 4, 6, the analogue of Theorem A and Theorem 5.1).** For m = 2, 3,
a(0) = 1, a(n) = r(n) + r(n - 1) for n >= 1, and

    sum_n r(n) t^n = t R_q(t) / D_q(t),       sum_n a(n) t^n = N_q(t) / D_q(t).

Explicitly

    m = 2:  (1 + t^2 + t^4 - t^5) / (1 - t - t^3 - t^5),
    m = 3:  (1 + t^2 + t^4 + t^6 + t^8 - t^9) / (1 - t - t^3 - t^5 - t^7 - t^9).

Hence a(n) = a(n-1) + a(n-3) + ... + a(n-2q+3) for every n >= 2q - 2, that is n >= 6 for m = 2 and
n >= 10 for m = 3. It fails at n = 2q - 3, where the left side minus the right side is -1 (a(5) = 7
against 8 for m = 2, a(9) = 54 against 55 for m = 3). So the starting index cannot be lowered. Also
r(n) = r(n-1) + r(n-3) + ... + r(n-2q+3) + e(n) with e(n) = 1 for odd n <= 2q - 5 and e(n) = 0
otherwise (n >= 1, r(j) = 0 for j <= 0).

*Proof.* Negatives. By (D2) and (D3), g is a bijection from X_n ∩ Q_{<0} to X_{n-1} ∩ Q_{>0} for
n >= 1, so a(n) = r(n) + r(n-1).

Positives. By Corollary 8.1, r(n) is the number of strings with c_1 >= 1, c_2, ..., c_k >= 1, all runs
of 1's among c_2, ..., c_k of length at most q - 3, and weight n. Give c_1 the weight c_1 and each
c_j with j >= 2 the weight c_j + 1 (the digit and the g before it). So c_1 contributes t/(1 - t), a
digit 1 after the first contributes u = t^2, and a digit at least 2 contributes B = t^3/(1 - t). A
sequence over these two kinds of digits with runs of 1's at most q - 3 long is a run of at most q - 3
ones, then any number of (one big digit, then a run of at most q - 3 ones). Each run contributes
R_q = 1 + u + ... + u^{q-3}. So

    sum r(n) t^n = t/(1 - t) * R_q / (1 - B R_q) = t R_q / ((1 - t)(1 - B R_q)) = t R_q / D_q,

since (1 - t)(1 - B R_q) = 1 - t - t^3 R_q = D_q. The geometric series is formal because B has no
constant term.

All ranks. sum a(n) t^n = 1 + (1 + t) t R_q / D_q. Now (1 + t) t R_q = (t + t^3 + ... + t^{2q-5}) +
(t^2 + t^4 + ... + t^{2q-4}), and adding D_q gives N_q. So the series is N_q/D_q.

Recurrence. The coefficient of t^n in D_q(t) A(t) is a(n) - a(n-1) - a(n-3) - ... - a(n-2q+3) (with
a(j) = 0 for j < 0), and it equals the coefficient of t^n in N_q. This is 0 for n >= 2q - 2 and -1
for n = 2q - 3. The statement for r(n) is the same computation with t R_q. ∎

The failure at 2q - 3 again comes from the root. For q = 3 this is Remark 6.2 of the paper.

Agreement with computation. The series of N_4/D_4 and N_6/D_6 equal the BFS counts to rank 28 and 30
(checks_report.md, two methods). This is a check of the theorem, not part of its proof.

## 6. The free case m >= 4

Here g(x) = -1/(m x) with m >= 4 any integer, and no run restriction. Call a string (c_1, ..., c_k)
free if it is (0), or c_1 >= 1 and c_2, ..., c_k >= 1, or c_1 = 0, k >= 2 and c_2, ..., c_k >= 1.

**Theorem 10 (free case).** Let m >= 4.

(a) Every tail (c_j, ..., c_k) with j >= 2 of a free string has value greater than 1/2. A free string
with c_1 >= 1 has value in (c_1 - 2/m, c_1], and one with c_1 = 0, k >= 2 has value in (-2/m, 0).
Distinct free strings have distinct values, and g is never applied to 0.

(b) The rationals reachable from 0 are exactly the values of free strings, and the rank of a value is
the weight c_1 + ... + c_k + k - 1 of its string.

(c) a(n) = F(n + 1) for every n >= 0 (F(1) = F(2) = 1), with r(n) = F(n) for n >= 1 and
a(n) = r(n) + r(n-1). So the generating function is 1/(1 - t - t^2).

(d) Blue iff negative holds. Every reachable negative x has x + 1 in (1 - 2/m, 1) reachable one rank
later, so the tree has no leaves.

(e) The orbit of 0 is a proper subset of Q. Every rational in (-infinity, -2/m] and in
(c - 1, c - 2/m] for c >= 1 is not reached. In particular -1 and 1/2 are never reached, for every
m >= 4.

*Proof.* (a) The last digit gives c_k >= 1 > 1/2. If T > 1/2 then c - 1/(m T) > 1 - 2/m >= 1/2 for
c >= 1 and m >= 4. This gives the tail bound by downward induction, and shows that g is only applied
to positive numbers. Then c_1 - 1/(m T_2) is in (c_1 - 2/m, c_1) when k >= 2, and -1/(m T_2) is in
(-2/m, 0). Since 2/m <= 1/2 < 1, the value x of a string with c_1 >= 1 determines c_1 = ceil(x),
whether k = 1 (x an integer), and the tail value 1/(m(c_1 - x)). A negative value determines c_1 = 0
and the tail value g(x). So uniqueness follows by induction on k, as in Lemma 7.

(b) Let V be the set of values and W(x) the weight of the string of x in V. Each string's word reaches
its value with W(x) moves, so V is reachable and d <= W on V. We show that V is closed under the
moves and that W goes up by at most 1 along each move. Let y be in V with string (c_1, ..., c_k).
If y = 0, f(y) = 1 = [1]. If y > 0, f(y) has string (c_1 + 1, c_2, ..., c_k) and W goes up by 1, and
g(y) < 0 has string (0, c_1, ..., c_k) and W goes up by 1. If y < 0, its string is (0, c_2, ..., c_k),
g(y) is the value of (c_2, ..., c_k) with W one less, and f(y) = 1 - 1/(m T_2) has string
(1, c_2, ..., c_k) with W one more. So along any path from 0 every point is in V and W <= the length,
which gives W <= d. Hence d = W on V and nothing outside V is reachable.

(c) As in Theorem 9 with no run restriction. The positive strings give t/(1 - t) * 1/(1 - u - B) =
t/((1 - t)(1 - t^2) - t^3) = t/(1 - t - t^2), so r(n) = F(n). The map g pairs negatives of rank n
with positives of rank n - 1, by the moves in (b). So A(t) = 1 + (t + t^2)/(1 - t - t^2) =
1/(1 - t - t^2).

(d) Let x != 0 be reachable and y -> x the last move of a shortest path. If x > 0 with c_1 >= 2, x - 1
has string (c_1 - 1, ...) and rank d(x) - 1, and g(x) has rank d(x) + 1. If c_1 = 1, x - 1 is 0 or has
string (0, c_2, ..., c_k), again of rank d(x) - 1. So the move is f. If x < 0, then x - 1 < -1 is not
reachable by (a), so the move is g. The last claim is the move f in (b).

(e) Immediate from (a). For -1, note -1 <= -2/m. For 1/2, note 1/2 is in (0, 1 - 2/m] because
m >= 4. ∎

For m = 4 the point -1/2 is special. There f(-1/2) = g(-1/2) = 1/2, and the parent map cycles
1/2 -> -1/2 -> 1/2 (ledger G10). Neither point is reachable. The case x -> x + k with -1/x is m = k^2
after scaling x = k y, so every k >= 2 is in this free case.

"Fibonacci up to a root correction" from the task. In this tree a(n) = F(n + 1) exactly for all n >= 0,
with no correction. The only role of the root is the split a(0) = 1, a(n) = r(n) + r(n - 1), the same
split as in Theorem 9.

## 7. Asymptotics

**Proposition 11 (asymptotics, the analogue of Proposition 5.2).** Let q >= 3 and S = {1, 3, 5, ...,
2q - 3}, so D_q(t) = 1 - sum_{j in S} t^j.

(a) D_q has exactly one root t_0 in (0, 1). It is simple, and every other root has modulus greater
than 1 (so psi_q = 1/t_0 is a Pisot number). psi_q is the positive root of
psi^{2q-3} = psi^{2q-4} + psi^{2q-6} + ... + 1.

(b) For m = 2, 3 (q = 4, 6), and in general for the series N_q/D_q,

    a(n) = C_q psi_q^n + epsilon(n),   C_q = (1 + t_0) R_q(t_0) / (-D_q'(t_0)),

with epsilon(n) -> 0 exponentially. The share of blue (negative) points of rank n tends to
1/(1 + psi_q).

*Proof.* (a) The sum sum_{j in S} t^j increases on [0, 1] from 0 to q - 1 >= 2, so it equals 1 at
exactly one t_0 in (0, 1), and D_q'(t_0) = -(1 + 3 t_0^2 + ... + (2q - 3) t_0^{2q-4}) < 0, so t_0 is
simple. For the other roots, put n = 2q - 1 >= 5 and H(t) = (1 - t^2) D_q(t). Multiplying out,
H(t) = 1 - t - t^2 + t^n. For t = r e^{i theta} and c = cos theta,

    |1 - t - t^2|^2 = 1 + 3r^2 + r^4 - 2 r c (1 - r^2) - 4 r^2 c^2,

which is concave in c, so on |t| = r its minimum is at c = 1 or c = -1, where it equals
(r^2 + r - 1)^2 and (1 + r - r^2)^2. For 0.62 < r <= 1 the smaller is (r^2 + r - 1)^2. The function
r^2 + r - 1 - r^n vanishes at r = 1 and has derivative 3 - n < 0 there, so it is positive for r in some
(1 - delta, 1). For such r, |t^n| < |1 - t - t^2| on |t| = r, and Rouché's theorem says H has as many
zeros in |t| < r as 1 - t - t^2, which is one (its zeros are 0.618... and -1.618...). Taking r > t_0,
that zero is t_0. So H, and hence D_q, has no other zero in the open unit disk. On |t| = 1 a zero of H
needs |1 - t - t^2| = 1, and the formula with r = 1 gives 5 - 4c^2 = 1, so t = 1 or t = -1. But
D_q(1) = 2 - q != 0 and D_q(-1) = q != 0. So every root of D_q other than t_0 has modulus greater
than 1. The equation for psi_q is D_q(1/psi) = 0 multiplied by psi^{2q-3}.

(b) A(t) = 1 + (1 + t) t R_q(t)/D_q(t), a proper fraction plus 1. Partial fractions give, for n >= 1,
a(n) = C t_0^{-n} + sum over the other roots t_i of p_i(n) t_i^{-n}, with polynomials p_i (constants if
the roots are simple), and C = -N_q(t_0)/(t_0 D_q'(t_0)). Since N_q(t_0) = D_q(t_0) +
(1 + t_0) t_0 R_q(t_0) = (1 + t_0) t_0 R_q(t_0) > 0, this is the stated C_q, and C_q > 0. The other
terms tend to 0 by (a). The same computation for t R_q/D_q gives r(n) ~ R_q(t_0)/(-D_q'(t_0)) psi^n,
and the negatives of rank n are counted by r(n - 1), so their share tends to
t_0/(1 + t_0) = 1/(1 + psi_q). ∎

Values (computer-checked to 15 digits, two formulas for C_q agree, ledger R2-4 and R2-5).

| q | m | psi_q | C_q | blue share 1/(1 + psi_q) | smallest other root modulus of D_q |
|---|---|---|---|---|---|
| 3 | 1 | 1.46557123187677 | 0.701931067901537 | 0.40558 | 1.2106 |
| 4 | 2 | 1.57014731219605 | 0.756978942343591 | 0.38908 | 1.0999 |
| 6 | 3 | 1.61193039656412 | 0.737859436963762 | 0.38286 | 1.0343 |
| inf | >= 4 | 1.61803398874989 | 0.723606797749979 (phi/sqrt 5) | 0.38197 | 1.6180 |

The q = 3 row is Theorem A of the paper (control). The free row is a(n) = F(n + 1) =
(phi^{n+1} - (-1/phi)^{n+1})/sqrt 5. Since D_{q+1} = D_q - t^{2q-1}, the root t_0 decreases in q and
psi_q increases (proved, since D_{q+1} < D_q on (0, 1)). It tends to the golden ratio because D_q(t)
tends to 1 - t - t^3/(1 - t^2) = (1 - t - t^2)/(1 - t^2) on (0, 1). C_q is not monotone (0.702, 0.757,
0.738, then 0.724 in the limit), which refuted the preregistered guess.

Nearest integer (computer-checked, R2-5). For q = 4 and q = 6 the triangle bound
sum |c_i| |t_i|^{-n} on the error is below 1/2 from n = 6 and n = 11 on, and a direct comparison covers
smaller n. So a(n) is the nearest integer to C_q psi_q^n for every n >= 1. This uses 40-digit floating
point roots, not interval arithmetic, so it is labeled computer-checked, not proved.

## 8. What is not done, and sources

- The m = 2, 3 proofs use the explicit numbers of Lemmas 1 and 3. For other q (q = 5 and q >= 7, where
  the tree lives in Q(lambda_q)) the same scheme should work with t_{i+1} = 1 - 1/(lambda^2 t_i), but
  this file does not prove it. Route 1 (proofs_route1.md, a separate task) addresses all q.
- No outside source is used. The Hecke, Rosen and Leutbecher references and the claims about
  Gamma_0(2)+ and Gamma_0(3)+ in the vision file were not opened in this task, so nothing here relies on
  them, and they should not be cited from this file.
- OEIS. Not searched again here. checks_report.md records that the m = 2 and m = 3 counts are not in
  the OEIS and that 1/D_4 is A060961. By Theorem 9, r(n) = A060961(n - 1) + A060961(n - 3) for m = 2
  and every n >= 1 (A060961(j) = 0 for j < 0). Repair 2026-10-02: the hedge is removed. The OEIS page
  gives g.f. 1/(1 - (x + x^3 + x^5)) and offset 0 (%O A060961 0,4), recorded in ledger.md as O1.
