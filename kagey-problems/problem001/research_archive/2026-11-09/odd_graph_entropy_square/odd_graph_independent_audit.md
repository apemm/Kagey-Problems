# Independent audit of the odd Pythagorean graph

9 November 2026.

Let G have the nonzero odd integers as vertices. Distinct u,v are adjacent if
either u^2+4(v-u)^2 or v^2+4(v-u)^2 is an integer square. The results here
clarify the exact construction problem and the limit of the available
partition-regularity argument. They do not determine whether G has finite
chromatic number.

## 1. The graph is exactly the uniform P-layering problem

For the one-prime scaffold, a block b has columns indexed by a and rows
2a+1 and R=2b+2. Set u=2a-2b-1. Another index c gives
v=2c-2b-1, and the black diagonal using the odd point at a and the even
point at c has squared length

    u^2+4(v-u)^2.

Thus a K-coloring of G removes every P pair in every height by applying the
color to u in each b-block and separating the K layers.

Conversely, every finite induced subgraph of G occurs among the actual
in-strip P constraints of a sufficiently tall one-prime scaffold. To see
this, let U be a finite set of nonzero odd integers. Choose an even R large
enough that all R+u are positive and, for every directed square relation

    L^2=u^2+4(v-u)^2,

both completion rows

    R+(u-L)/2,    R+(u+L)/2

are positive. Choose h large enough to contain these rows, R, and every R+u.
With b=(R-2)/2 and a=b+(u+1)/2, all indices are valid and the desired
diagonal appears in block b. Its completion rows have opposite parity,
because L is odd. Their parity edge occurs elsewhere in the full scaffold,
so each relation is an actual unavoidable P collision when the two edges
receive the same layer.

Consequently, a uniform K-layer solution to the one-prime P problem exists
if and only if G is K-colorable. The converse uses the finite-subgraph
compactness theorem for graph coloring. This equivalence concerns P alone;
mixed four-double collisions and singleton completion remain additional tasks.

## 2. Positive odd integers and odd rationals

Let G_+ be the induced graph on positive odd integers. Simultaneous negation
preserves adjacency. Therefore

    chi(G_+) <= chi(G) <= 2 chi(G_+)

whenever the right side is finite: use disjoint palettes for the two signs.
Thus finiteness is equivalent for G and G_+.

The same finiteness question can be stated on positive rationals whose reduced
numerator and denominator are odd. Every finite collection of such rationals
can be multiplied by an odd common denominator to become positive odd
integers. Adjacency is preserved by nonzero rational dilation. Conversely,
the integers are a subgraph. Finite-subgraph compactness therefore gives the
same chromatic number for these two positive graphs.

This identifies the exact missing Ramsey statement: every finite coloring
of the positive odd rational units should contain a pair satisfying one of
the two displayed square relations, if the chromatic number is infinite.

## 3. Audit of the anchored local obstruction

The anchored Pell argument in `odd_graph_progress.md` is valid. Start from
X^2-5Y^2=-4 at (1,1), and apply the integer matrix

    [[9,20],[4,9]].

For any modulus M, its determinant is 1, so some positive power returns
(1,1) to itself modulo 10M. For that solution,

    z=(X+4)/5

is an odd integer greater than 1, z=1 modulo 2M, and

    z^2+4(z-1)^2=Y^2.

For every fixed nonzero odd v, the vertex w=zv is adjacent to v and
w=v modulo M. Repeating the returning matrix power gives infinitely many
such w.

In particular, no proper coloring can be constant on any residue-class
neighborhood of any vertex. This excludes finite lower-digit rules even when
the number of inspected digits depends on the input: a deterministic rule
that stops after finitely many lower-digit queries is constant on the
corresponding residue-class neighborhood. This is stronger than excluding a
single uniform period. It does not exclude discontinuous finite colorings.

## 4. The precise partition-regularity gap

The graph equation has the parametrization

    u=g(m^2-n^2),    v=g(m^2+mn-n^2),
    L=g(m^2+n^2).

To obtain odd u,v from integer parameters, it suffices to take g odd and
m,n of opposite parity. With m,n both odd, u is even and v is odd, so the
unrestricted parametrization does not meet the graph's domain.

Theorem 1.12 and its footnote in
[Frantzikinakis, Klurman, and Moreira, *Partition regularity of generalized Pythagorean pairs*](https://arxiv.org/html/2407.08360v2)
provide the relevant unrestricted quadratic-pair result. Its stated domain is
the positive integers. The proof's reducible-form case uses specializations
near a root modulo the averaging modulus; it does not state that the two
resulting colored values can both be odd. Its odd-input extension cannot be
used without a separate argument.

There are two concrete reasons not to treat this restriction as automatic.
First, ordinary Pythagorean pairs are partition regular, whereas two odd legs
cannot form a Pythagorean pair modulo 4. Second, taking odd parts does not
preserve the present graph relation:

    8^2+4(5-8)^2=10^2,

but the odd parts 1 and 5 are not adjacent, since the two candidate squares
are 65 and 89. Refining a coloring by parity and then removing a common
power of two does not ensure that both residual inputs are odd.

One possible extension would work with the multiplicative semigroup of odd
integers and restrict the parameters to opposite parity. In coordinates
r=m+n, s=m-n, this asks for odd r,s and odd g, with

    u=g rs,    v=g(r^2+4rs-s^2)/4.

The second quotient is an odd integer when r,s are odd. Establishing the
needed recurrence on this restricted domain remains a genuine proof step.
No finite-color obstruction beyond the anchored local result is claimed here.
