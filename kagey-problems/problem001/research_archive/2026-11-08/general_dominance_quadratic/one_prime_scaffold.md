# A one-prime scaffold and subpolynomial P coloring

8 November 2026.

For every height h, a one-prime placement of all parity doubles has quadratic
width and excludes every tilted right angle supported on three double cells.
The Pythagorean pair obstruction can then be removed with h^(o(1)) separated
layers. The resulting width is h^(2+o(1)). Four-double mixed collisions and
singleton completion are not settled by this construction.

This note independently audits the placement and coloring argument. Its P graph
differs from the two-prime CRT graph in `quadratic_lifts_pell.md`. In particular,
the K_4 example and periodic-color obstruction there do not apply here.

## 1. The quadratic placement

Let n_o=ceil(h/2), n_e=floor(h/2), and choose a prime p>10h. For each
0<=a<n_o and 0<=b<n_e, put

    x_ab = a+p b.

The physical column is 4x_ab, and its two marked rows are

    o_a=2a+1,    e_b=2b+2.

Distinct edges have distinct columns because 0<=a<p. Every parity edge occurs
once. Bertrand's postulate permits p<20h, so the width is less than 40h^2+1.

**Theorem 1.** No three marked cells form a tilted right angle, even when the
fourth corner is allowed outside the strip.

**Proof at an odd-row vertex.** At vertex (a_0,b_0), two even-row legs have
odd vertical components and horizontal components divisible by 4. Their dot
product is odd, hence nonzero.

For two odd-row legs, reducing the dot product modulo p gives

    20(a_1-a_0)(a_2-a_0).

Since p>10h, one actual index difference is zero. That leg is horizontal, so
any right angle is axis-aligned.

For one odd-row leg and one even-row leg, the reduction is

    2(a_1-a_0) [8a_2+2b_2-10a_0+1].

The bracket is odd and has absolute value below 10h. It cannot vanish modulo
p. Again the same-parity leg is horizontal.

**Proof at an even-row vertex.** A leg to another even-row cell has components

    dx=4(Delta a+p Delta b),    dy=2 Delta b.

If Delta b=0, it is horizontal. Otherwise

    |dx| >= 4(p-h/2)|Delta b|.

With two nonhorizontal even-row legs, the horizontal product has magnitude
greater than h^2, while the vertical product has magnitude at most (h-1)^2.
They cannot cancel. Two odd-row legs again give an odd dot product.

It remains to consider one even-row leg and one odd-row leg. The even-row
leg can be assumed nonhorizontal. If the odd endpoint lies in a different
b-block from the vertex, both horizontal components have magnitude greater
than 4(p-h/2), so their product again dominates the vertical product.

If the odd endpoint lies in the same b-block, its horizontal component is
4 Delta a. When Delta a=0, that leg is vertical and cannot form a tilted
right angle. Otherwise the horizontal product has magnitude at least

    16(p-h/2)|Delta b|,

while the vertical product has magnitude at most 2(h-1)|Delta b|. The first
is strictly larger. This exhausts all parity choices. QED.

## 2. P pairs stay in one block

A vertical P completion has length L<=h-1. Its horizontal black-diagonal
component is therefore less than h. Two columns in different b-blocks have
physical separation at least 4(p-h/2)>h, so the black diagonal must lie in
one b-block.

Use the odd point of column a and the even point of column c in that block.
Put

    u=2a-2b-1,    delta=c-a.

The vertical component u is odd and nonzero. The Pythagorean condition is

    L^2=16delta^2+u^2,

or equivalently

    (L-4|delta|)(L+4|delta|)=u^2.

Orient this forbidden pair from a to c, meaning that the odd point is taken
from the source column. Every actual P pair has at least one such orientation.

For fixed a,b, a positive factor pair r<s of u^2 determines at most one
positive |delta|=(s-r)/8. It contributes at most two target columns, one
on each side. Since u^2 is a square, there are
(tau(u^2)-1)/2 factor pairs with r<s. Thus the outdegree is at most

    tau(u^2)-1.

This bound remains valid after dropping the completion's height restriction.
Doing so only adds forbidden pairs to the graph being colored.

## 3. Coloring the P graph

Let

    D_h = max_{1<=u<h, u odd} (tau(u^2)-1).

The directed P graph has outdegree at most D_h. In every induced subgraph,
the number of undirected edges is at most D_h times the number of vertices.
Its average degree is at most 2D_h. Therefore the undirected P graph is
2D_h-degenerate and can be colored with at most

    K_h=2D_h+1

colors. The coloring is constructive: repeatedly remove a vertex of current
degree at most 2D_h, then color in reverse removal order.

Each b-block can use the same palette. The elementary divisor estimate
tau(n)=n^(o(1)) gives K_h=h^(o(1)). Unlike the two-prime argument, this
estimate uses direct factorization of u^2 and requires no Pell equation.

## 4. Separated lifts preserve the right-angle exclusion

Set M=p n_e. If k_ab is the color of edge (a,b), replace its slot by

    x'_ab = a+p b+2k_ab M.

All original slots lie in [0,M). Distinct layers are separated by more than
M slots. Their physical separation is therefore greater than 4M, which
exceeds both h and 2W_h.

Within a layer, Theorem 1 still applies because translation does not change
dot products. A tilted right angle involving more than one layer has a leg
with horizontal component greater than 4M. Its other leg has a nonzero
horizontal component divisible by 4. The horizontal product then exceeds
16M>(h-1)^2 and cannot cancel the vertical product. Thus no new tilted
right angle appears between layers.

A P black diagonal cannot cross layers because its length is at most h-1.
Within one layer, the proper coloring excludes every P pair. The number of
columns is at most

    4(2K_h-1)M+1 = O(K_h h^2) = h^(2+o(1)).

**Theorem 2.** For every height h, the lifted one-prime placement contains every
parity double once, has no three-double tilted right angle, has no in-strip
vertical P completion, and has width h^(2+o(1)).

This theorem concerns a scaffold of marked doubles. Four-double mixed
collisions remain possible. Even excluding those collisions would still leave
the task of adding one singleton black cell to every other column.

## 5. Verification

`one_prime_scaffold_check.py` builds the placement, constructs the factor-pair
graph, colors it by degeneracy, and checks actual coordinates independently.
It verifies tilted right angles before and after lifting and searches for
in-strip vertical P completions after lifting. It does not claim to verify
four-double mixed collisions or singleton completion.

All checks passed for heights 3 through 41 in 5.92 seconds. The greedy
colorings used at most four colors over this range. This finite observation
does not prove a uniform four-color bound. The complete numerical summaries
are saved in `one_prime_scaffold_checks.json`.

## 6. Every fixed-period coloring fails

Fix a positive integer N. In block b=0, take

    a=2N^2,    c=a+N.

The odd point of column a and the even point of column c have vertical
difference u=4N^2-1 and horizontal difference 4N. They satisfy

    u^2+(4N)^2=(4N^2+1)^2.

Their vertical completion has rows 1 and 4N^2+2. At height

    h_N=4N^2+2N+2,

both complete parity doubles and both completion rows are present. A coloring
periodic with period N in a gives the two edges the same layer. Their
Pythagorean separation is then unchanged by lifting, so the P collision
survives. The argument also applies to a coloring periodic with period N in
the original slot x=a+pb.

Thus a fixed-period coloring cannot remove P at all heights, regardless of
how many colors it uses. This does not rule out a bounded number of colors
with assignments that have increasing period or are aperiodic.

## 7. A literature question about constant colors

Writing v=2c-2b-1 turns the P equation into
u^2+4(v-u)^2=L^2, with u,v odd. It has the parametrization

    u=g(m^2-n^2),    v=g(m^2+mn-n^2).

Theorem 1.12 and its footnote in
[Frantzikinakis, Klurman, and Moreira, *Partition regularity of generalized Pythagorean pairs*](https://arxiv.org/html/2407.08360v2)
give related partition-regularity results for quadratic pairs on the positive
integers. They do not directly state the restriction needed here: both colored
values must be odd. Their arithmetic-progression steps do not by themselves
settle this restriction. Removing common powers of two also does not suffice,
because the two values can have different 2-adic valuations. No unbounded-color
claim is made for this graph. Establishing an appropriate odd-input extension,
or finding a bounded coloring, remains a separate research question.
