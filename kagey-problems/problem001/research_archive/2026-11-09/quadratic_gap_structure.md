# The quadratic gap: a flexible right-angle exclusion and the rigid/flexible tension

Research note, 9 November 2026. The absolute bound m_0(h) = O(h^2) is not proved here.
This note proves three structural statements about label-only obstructions and records
why the placements they allow still cost a growing factor. Nothing in `full_problem_push/`
is edited. Sections 1 to 3 are proofs. Section 4 is analysis with heuristic counts and is
marked as such.

Notation. Odd rows are 2a+1 with 0 <= a < k_o, even rows are 2b+2 with 0 <= b < k_e,
and k = max(k_o, k_e). A label (a,b) sits at slot s(a,b), physical column 4 s(a,b), and
contributes the odd cell (4s, 2a+1) and the even cell (4s, 2b+2). Write v for the 2-adic
valuation. A right angle is tilted if neither leg is horizontal or vertical.

## 1. Right angles: one prime for the odd side, a 2-adic contraction for the even side

**Theorem R.** Let p be a prime with p > 5h + 4. Suppose an injective placement s
satisfies:

(P) s(a,b) = a (mod p) for every label;

(T) for any two labels with b != b', v(b - b') <= v(s(a,b) - s(a',b')).

Then no three label cells form a tilted right angle. The fourth corner is not required to
lie in the strip.

Condition (T) says that s mod 2^j is a function of b mod 2^j for every j. It holds, for
example, when s = t(b) (mod 2^J) with 2^J >= k_e and t any map with
v(t(b) - t(b')) >= v(b - b'). The linear choice t(b) = b is the binary analogue of the
two-prime CRT placement. The map t may be any 2-adically 1-Lipschitz map, and the bits of
s above position J are unconstrained.

**Proof.** Write x_i for slot differences from the vertex, so horizontal components are
4 x_i. Classify by the row parity of the vertex and of the two endpoints.

*Odd vertex, two even endpoints, or even vertex, two odd endpoints.* Both vertical
components are odd and both horizontal components are divisible by 4. The dot product is
odd.

*Odd vertex, two odd endpoints.* The legs are (4 x_i, 2 d_i) with d_i the differences of
odd indices and x_i = d_i (mod p) by (P). The dot product is 16 x_1 x_2 + 4 d_1 d_2 =
20 d_1 d_2 (mod p). Since p > 5 and |d_i| < k < p, some d_i is zero, and that leg is
horizontal.

*Odd vertex (index a_0), one odd endpoint, one even endpoint.* The odd leg is
(4 x_1, 2 d_1). The even endpoint belongs to a label with odd index a_2 and its leg is
(4 x_2, e) with e odd and x_2 = a_2 - a_0 (mod p). The dot product is
2 d_1 [8 (a_2 - a_0) + e] (mod p). The bracket is an odd integer of absolute value less
than 4h + 4 + h <= p, so it is not divisible by p. Hence d_1 = 0 and the odd leg is
horizontal.

*Even vertex, two even endpoints.* The legs are (4 x_i, 2 c_i) with c_i the differences
of even indices. A tilted angle has all four numbers nonzero. By (T), v(c_i) <= v(x_i).
Then v(4 c_1 c_2) <= 2 + v(x_1) + v(x_2) < 4 + v(x_1) + v(x_2) = v(16 x_1 x_2), so the
dot product 16 x_1 x_2 + 4 c_1 c_2 is nonzero.

*Even vertex, one even endpoint, one odd endpoint.* The legs are (4 x_1, 2 c_1) and
(4 x_2, e) with e odd. If c_1 = 0 the first leg is horizontal. If x_2 = 0 the dot product
is 2 c_1 e, nonzero. Otherwise v(2 c_1 e) = 1 + v(c_1) <= 1 + v(x_1) <
4 + v(x_1) + v(x_2), so the dot product is nonzero. QED.

**Remarks.**
1. Partial linkage is not enough. If (T) is imposed only for j <= j_1 with 2^(j_1) < k,
   the valuation argument forces every surviving right angle to have a leg with
   2^(j_1) dividing both its slot and row differences, but the conditional probability of
   the exact coincidence rises by the same factor. The expected count is unchanged.
2. The two sides cannot both be 2-adic. Conditions of type (T) for the odd and the even
   index together would force a relation between a and b, and every pair (a,b) is a label.
3. Under (P) and (T) with a fixed t, a label has exactly one admissible slot in each
   period p 2^J. In width O(h^2) it has O(1) choices. This rigidity is the cost of the
   theorem; see section 4.

## 2. Vertical rivals: parametrization and safe zones

Let an odd-row black cell and an even-row black cell have horizontal gap g != 0 and
vertical difference u (odd). They are the black diagonal of a vertical rival if and only
if g^2 + u^2 = L^2 with L an integer and both rows (y + y' -+ L)/2 in [1,h].

**Lemma V.** In that case:

(a) 4 divides g. Writing g = 4 x, there are odd positive integers m, e, f with e < f,
gcd(e,f) = 1, and |u| = m e f, x = m (f^2 - e^2)/8, L = m (e^2 + f^2)/2.

(b) |g| > 2 sqrt(|u|), and |g| < h.

(c) With lo and hi the smaller and larger of the two rows,
g^2 <= 4 min(lo - 1, h - hi) min(hi - 1, h - lo). In particular a cell in row 1 or row h
is never an endpoint of such a diagonal.

(d) 4^(v(g) - 1) <= min(hi - 1, h - lo).

**Proof.** (a) L is odd. Put m = gcd(L, |u|), L = m L_1, |u| = m u_1. Then
(L_1 - u_1)(L_1 + u_1) = (g/m)^2 and the two factors have gcd 2, so they are 2 A^2 and
2 B^2 with A, B coprime of opposite parity. Put e = B - A, f = B + A. Then u_1 = e f,
L_1 = (e^2 + f^2)/2, g/m = 2AB = (f^2 - e^2)/2, and f^2 - e^2 is divisible by 8.

(b) x = m (f - e)(f + e)/8 >= m 2 (2 sqrt(e f))/8 = sqrt(m |u|)/2, with equality
impossible since e < f. Also |g| < L <= h - 1.

(c) The lower white row is at least 1, so L <= lo + hi - 2, giving L - |u| <= 2 lo - 2
and L + |u| <= 2 hi - 2. The upper white row is at most h, giving L - |u| <= 2 (h - hi)
and L + |u| <= 2 (h - lo). Multiply.

(d) v(L - |u|) + v(L + |u|) = 2 v(g) and exactly one of the two has valuation 1. The
other is at least 2^(2 v(g) - 1) and at most L + |u| <= 2 min(hi - 1, h - lo). QED.

The triangle count sum over m of (number of primitive triples with hypotenuse below h/m)
is of order h log h. The logarithm is the sum over the scale m; each scale contributes
order h/m.

## 3. Regions separated by (h-1)^2 columns are independent for label-only obstructions

**Lemma S.** Let two sets of label columns be separated by more than (h-1)^2 columns.
Then no vertical rival, no tilted right angle of three label cells, and no mixed
side/diagonal collision of four label cells uses cells from both sets.

**Proof.** A vertical rival has gap below h. A right angle using both sets has a leg with
horizontal component larger than (h-1)^2 and a second leg with nonzero horizontal
component, so the horizontal product exceeds the vertical product, which is at most
(h-1)^2. A mixed collision consists of two rectangles sharing two corners; each spans at
most W = 1 + floor((h-1)^2/4) columns, so its four black cells lie within 2W <= (h-1)^2
columns for h >= 3. QED.

So a bounded number of regions, each with its own prime, its own map t, or an entirely
different layout, can be combined at a cost of O(h^2) columns of separation in total. The
separating columns still need singleton fillers; this lemma concerns label cells only.

## 4. Why these do not yet give O(h^2) (analysis; the counts here are heuristic)

**Conflicts in a Theorem R layout.** Take t the identity. Two labels at slot gap x < h/4
have odd indices differing by exactly x. The pair conflicts when 16 x^2 + (T - 2x)^2 is an
odd square with fitting white rows, where T is the row offset (even row minus odd row) of
one of the two labels, its owner. Each label owns D(T) gaps, and the average of D over T
is of order log h, although D(T) is O(1) for T with no divisor that is a suitable norm
from Q(sqrt 5). The admissible freedom is the choice of period (layer). Avoiding all
conflicts is therefore a proper coloring of a graph of average degree of order log h by
the layers, which needs an unbounded number of layers unless the graph has special
structure. For the linear map the graph on each chain is a Cayley graph of Z, and the
certified six-chromatic chain shows the number of layers is at least 6.

**The tension.** Right-angle exclusion by arithmetic (the two-prime CRT placement, or
Theorem R) leaves O(1) slots per label. Vertical-rival exclusion at constant density (the
global palette theorem) uses the opposite: each label chooses among order h blocks and
Hall's theorem finds the matching. In a block layout s = a + P c, condition (T) for
labels in different blocks would force v(b - b') <= v(a - a') for all labels within the
interaction range, which only a partial matching satisfies. So the two known mechanisms
cannot be imposed together in either of these two layouts.

**What Lemma S buys.** With n separated regions using different slopes for the odd side
(s r = a mod p for small r, which keeps the bracket argument valid), the owned-conflict
form changes from discriminant 5 to 4 + r^2. A label whose offset T has all prime factors
inert in the corresponding real quadratic field owns no conflict in that region. A label
with w prime factors is of this kind in a given region with probability about 2^(-w), so
covering typical labels needs about (log h)^(log 2) regions. This suggests width
h^2 (log h)^(0.70) for right angles and vertical rivals together, which is not O(h^2)
and does not include mixed collisions or fillers. It is not proved here.

**What would close the gap.** Any one of the following:
1. A family of maps t (or of slopes) for which the owned-conflict graphs are colorable by
   a bounded number of layers at every height.
2. A right-angle exclusion with order h admissible slots per label, so that a palette
   and Hall argument can run inside it.
3. A proof that fatal right angles (completion in the strip at a column whose black cell
   has the opposite parity) can be made harmless by the filler choice, removing the need
   for arithmetic rigidity.

Mixed collisions are not the bottleneck for a placement with any residual randomness:
under random placement at constant density their expected total number is of order
h log^2 h among h^2/4 labels, because a collision needs a side direction (u,v) with
u <= 2h and a long multiple of it.

## 5. Option 1 examined: bounded layers for linear Theorem R layouts

This section follows up item 1 of "What would close the gap". Statements 5.1 to 5.4 are
proved. Statement 5.5 is a negative result for one class of colorings. Statements 5.6 and
5.7 are heuristic and are marked as such. The conclusion is that option 1 very likely
cannot give O(h^2).

### 5.1 Theorem R with other slopes

**Theorem R'.** Theorem R remains true if (P) is replaced by either of the following.

(P1) r s(a,b) = a (mod p), with r an odd integer and p a prime, p > (r^2 + 5) h.

(P2) R s(a,b) = a (mod p), with R^2 = c_0 (mod p) for an odd positive integer c_0, and
p a prime with p > (c_0 + 5) h and p not dividing c_0 (c_0 + 4).

**Proof.** Only the two cases with an odd vertex and an odd endpoint use (P). Under (P1)
slot differences satisfy x = r^(-1) d (mod p). The all-odd dot product is
d_1 d_2 r^(-2) (16 + 4 r^2) (mod p), and p does not divide 4 (r^2 + 4). The mixed dot
product is 2 d_1 r^(-2) [8 (a_2 - a_0) + r^2 e] (mod p); the bracket is odd and has
absolute value below 4h + 4 + r^2 h < p. Under (P2) replace r^2 by c_0 throughout. QED.

In (P2) the multiplier R is of size p, so the odd index of a neighbor at slot gap x is
R x reduced modulo p, which is not a small multiple of x. Width stays O(h^2) for fixed
c_0.

### 5.2 Linear layouts: conflicts depend only on the diagonal

Take (P1) with slope r_o on the odd side and t(b) = r_e^(-1) b (mod 2^J) with r_e odd on
the even side, and 2^J > 2 |r_e| k. Two labels at slot gap x with |x| < h/4 then have
indices differing by exactly (r_o x, r_e x). Let T = (even row) - (odd row) be the
offset of a label. It is constant on diagonals b - a = const.

**Lemma D.** Labels with offsets T_1, T_2 at slot gap x form a vertical rival only if
there are an odd m >= 1, coprime positive integers A, B of opposite parity, and signs
eta, eps with x = eps m A B / 2 and

    {T_1, T_2} = { m [eta (B^2 - A^2) + r_o eps A B],  m [eta (B^2 - A^2) + r_e eps A B] }.

**Proof.** The two cross differences are T_1 - 2 r_o x and T_1 + 2 r_e x, and
T_2 = T_1 + 2 (r_e - r_o) x. By Lemma V(a) a rival needs one of them to equal
eta m (B^2 - A^2) with 4x = 2 eps m A B. Substituting gives the displayed pair in the
first case, and the same pair with eps replaced by -eps and the roles of T_1, T_2
exchanged in the second. QED.

So the layer problem for a linear layout contains the following coloring problem on odd
integers: color so that m F(r_o) and m F(r_e) differ, where
F(r) = eta (B^2 - A^2) + r eps A B. A proper coloring of this diagonal graph, used as the
layer index, removes every vertical rival. The forms are norm forms of discriminant
r^2 + 4.

### 5.3 A sign lemma

**Lemma.** Take r_o = R > 0 and r_e = -R. If R A B > |B^2 - A^2|, the two offsets in
Lemma D have opposite signs. So coloring a diagonal by the sign of T separates every
conflict with 1/rho < B/A < rho, where rho = (R + sqrt(R^2 + 4))/2.

The remaining conflicts have B/A > rho or A/B > rho. For these T_1 and T_2 have the same
sign, T_1 - T_2 = 2 m R eps A B, and T_1 / T_2 tends to 1 as B/A grows.

### 5.4 Residue colorings cannot finish

**Lemma.** For every odd prime l and every r_o, r_e, there are admissible (A, B) with
l dividing B, and then F(r_o) = F(r_e) (mod l) with both prime to l. Hence no coloring
that depends only on the residue modulo a fixed M of the part of T prime to M separates
all pairs of Lemma D. The same holds with l^i in place of l as long as l^(2i) < h.

**Proof.** F(r_e) - F(r_o) = (r_e - r_o) eps A B. With l | B and l not dividing A,
both values are congruent to -eta A^2. QED.

Because the scale m is arbitrary, a coloring must be compatible with multiplication, and
the lopsided pairs of 5.3 have ratios accumulating at 1. This is the same shape as the
odd Pythagorean graph, whose chromatic number is unbounded. I have no proof that the
diagonal graph of Lemma D has unbounded chromatic number when both forms are irreducible.

### 5.5 Density is conserved (heuristic count)

In every Theorem R or R' layout the number of labels within vertical-rival range of a
given label is (occupied slot density) times h/2, and a neighbor at gap x conflicts for
about |U(x)|/k of the offsets, where U(x) is the set of u with (x,u) Pythagorean. Summing,
(average conflicts per label) times (width) is of order h^2 log h for every choice of
slope, prime, and map t tried here: larger slopes or primes thin the neighbors exactly as
fast as they widen the board. A label of offset T owns conflicts at each scale m dividing
T, O(1) per scale on average, so it owns about tau(T) conflicts: typically
(log h)^(log 2), on average log h.

### 5.6 The free side always carries a log^2 load (heuristic count)

If one row parity is left free at each slot, as in the palette layout, right angles with
all three corners on the free side satisfy 4 x_1 x_2 + c_1 c_2 = 0. The number of
solutions with |c_i| < k and x_1 x_2 in range is of order k^2 log^2 k, so the load per
label is of order (density)^2 log^2 h. Linking the free rows to slots modulo any modulus
smaller than k does not change this count: fewer configurations survive, each more
likely by the same factor. Only full linkage, which is rigidity, removes it.

### 5.7 Assessment

Three independent routes give a growing factor:

* rigid on both sides (Theorem R, R', CRT): layers must properly color a graph in which
  a label of offset T has about tau(T) neighbors; this points to about (log h)^(0.69)
  layers, up to lower-order factors;
* free on one side with a local-lemma argument: density at most 1/log h;
* free on one side with a sparse-constraint coloring bound in place of the local lemma:
  the all-free-side right angles force (density)^2 log^2 h to be at most of order log h,
  that is density at most (log h)^(-1/2).

None of these is a lower bound for the threshold. They show that O(h^2) needs a mechanism
outside "arithmetic rigidity plus layers" and "one free side plus a matching argument",
or a proof that the true threshold carries a power of log h.
