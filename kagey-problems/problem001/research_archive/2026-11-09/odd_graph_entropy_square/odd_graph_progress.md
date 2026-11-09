# The odd Pythagorean graph: a stronger obstruction to digit colorings

9 November 2026. Let G have all nonzero odd integers as vertices. Join distinct
u,v when at least one of

    u^2+4(v-u)^2,    v^2+4(v-u)^2

is a square. This symmetrization expresses the coloring question: neither
orientation can be monochromatic. A bounded chromatic number is not proved
or disproved here.

The new result rules out more than fixed-period colorings. Every vertex has
arbitrarily large neighbors in every congruence neighborhood of that vertex.
Consequently, a proper finite coloring cannot be locally constant at even
one vertex. This excludes adaptive rules that inspect finitely many lower
p-adic digits before deciding their color, even if the number of inspected
digits depends on the input.

## 1. An anchored Pell construction

**Theorem.** For every nonzero odd integer v and every positive integer M,
there are infinitely many odd integers w such that

    w != v,    w = v mod M,
    w^2+4(v-w)^2 is a square.

The integers w can be chosen with the same sign as v and with unbounded
absolute value. In fact w=zv with z>1 an odd integer satisfying z=1 mod 2M.

**Proof.** Start from X=Y=1 in

    X^2-5Y^2=-4.

Multiplication of X+Y sqrt(5) by 9+4 sqrt(5) gives the integer update

    (X,Y) -> (9X+20Y,4X+9Y).

The update matrix has determinant one. It is invertible modulo 10M, so some
positive power returns (1,1) to itself modulo 10M. Repeating this power
gives an unbounded sequence of positive solutions with

    X = Y = 1 mod 10M.

For each noninitial solution, set z=(X+4)/5. Then z is an odd integer,
z>1, and z=1 mod 2M. Substitution of X=5z-4 into the norm equation gives

    z^2+4(z-1)^2=Y^2.

Therefore w=zv has all the required properties, with square root |v|Y.
The repeated positive matrix power makes z strictly increase. QED.

For example, two updates give X=521,Y=233,z=105. Thus v and 105v are
adjacent for every odd v. Longer return powers impose any desired modulus.

## 2. Consequences for digit and valuation rules

Give the odd integers their congruence topology: a neighborhood of v consists
of all odd integers congruent to v modulo some M. Suppose a coloring is
locally constant at v. Then one such neighborhood has color c(v), and the
theorem supplies a distinct adjacent w in that neighborhood. The coloring
is not proper.

This argument also applies to the topology defined by one prime, by taking
M=p^r, and to any finite list of primes, by taking their product powers.
It rules out the following types of globally defined coloring:

- A fixed residue rule.
- A rule that reads finitely many lower p-adic digits at each input and then
  halts, even with input-dependent stopping depth.
- A finite collection of valuations and leading unit residues of integer
  polynomials, at any odd input where the relevant polynomial values are
  nonzero. Such data are constant in a sufficiently small congruence
  neighborhood of that input.

The second assertion concerns lower-digit queries on an infinite p-adic
digit stream. A rule using the most significant digit of a finite binary
representation, its length, or unrestricted prime factorization need not
be locally constant in this topology. Those rules are not excluded.
Likewise, this theorem does not exclude colorings of each finite interval
whose digit depth grows with the interval. It does not establish unbounded
chromatic number.

## 3. Four colors are necessary

The positive odd vertices {5,11,15,33} form a complete graph. Exact witnesses
for its six edges are:

| Source u | Target v | Square root of u^2+4(v-u)^2 |
|---:|---:|---:|
| 5 | 11 | 13 |
| 15 | 5 | 25 |
| 33 | 5 | 65 |
| 15 | 11 | 17 |
| 33 | 11 | 55 |
| 15 | 33 | 39 |

Thus at least four colors are needed whenever H>33. This is a fixed lower
bound, not evidence of a diverging chromatic number by itself.

## 4. Exact scope of the remaining question

Let G_H^+ be the induced graph on positive odd integers below H, and G_H
the graph on all odd integers in (-H,H). Negation preserves adjacency, so

    chi(G_H^+) <= chi(G_H) <= 2 chi(G_H^+).

For the upper bound, use disjoint palettes for the positive and negative
vertices. Thus uniform boundedness is equivalent for the positive and signed
versions. A uniform K-coloring of all finite positive graphs is equivalent
to a K-coloring of the infinite positive graph, by the elementary compactness
argument using a finitely branching tree of finite proper colorings.

For positive u, the usual primitive Pythagorean parametrization writes every
edge with u^2+4(v-u)^2 square as

    u = g(m^2-n^2),
    v = g(m^2-n^2 +/- mn),

where m>n>0 are coprime and of opposite parity, g is positive and odd, and
the displayed v is positive. Conversely these parameters give an edge.
The square root is g(m^2+n^2). The parity restrictions are substantive:
they make both colored values odd. An edge of the symmetrized graph may
require swapping u and v before applying this parametrization.

The quadratic-pair results of
[Frantzikinakis, Klurman, and Moreira](https://arxiv.org/html/2407.08360v2)
are relevant to the unrestricted pair of forms. Their stated conclusions
do not directly provide the odd-input restriction above. Applying a theorem
on all positive integers to colors of odd parts does not close this gap:
the two polynomial values can have different 2-adic valuations. A proof
on the odd multiplicative semigroup, or an appropriate congruence-restricted
recurrence theorem, would be an additional result.

Thus the proved degeneracy upper bound h^(o(1)) remains the available
all-height bound. The anchored construction narrows the possible bounded
coloring mechanisms without deciding whether such a coloring exists.

`check_odd_graph_pell.py` verifies return powers and the exact square identity
for moduli through 32 and several signed anchors. The argument above proves
the statement for every modulus and every anchor.
