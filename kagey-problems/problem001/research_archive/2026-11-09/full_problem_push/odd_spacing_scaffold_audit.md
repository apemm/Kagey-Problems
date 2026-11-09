# Odd horizontal stretching gives identifying scaffolds

9 November 2026. This independently checks the odd-spacing argument and records
its precise scope. It constructs an identifying black set with empty inserted
columns. It does not give a maximum-blackout board.

Let the rows be the integers from 1 through \(h\), and put \(H=h-1\).
Let \(B\) be a finite black set whose bipartite row-column incidence graph has
no cycle of length four or six. Choose any positive odd integer \(D>H/2\).
Replace each black point \((x,r)\) by \((Dx,r)\), keeping all inserted columns
empty. The resulting black set is identifying for all lattice rectangles.

## The geometric restriction

No tilted rectangle in the strip can have all four x-coordinates divisible by
\(D\). To see this, orient its adjacent sides from its leftmost vertex as
\((a,-b)\) and \((c,d)\), where \(a,b,c,d>0\). Orthogonality gives
\(ac=bd\). The horizontal components \(a,c\) would each be at least \(D\),
whereas \(b+d\le H\). Consequently

\[
D^2\le ac=bd\le H^2/4<D^2,
\]

a contradiction. If three tilted corners are black, the fourth corner has
x-coordinate equal to the sum of two black x-coordinates minus the third.
It is therefore also divisible by \(D\). Thus a tilted rectangle has at most
two black corners.

The original incidence assumptions imply that all axis rectangle presentations
are distinct. In particular they exclude a hidden axis rectangle. Horizontal
stretching preserves this axis property.

## Comparing two weak tilted presentations

Distinct rectangles cannot share three corners. Since a tilted rectangle has
at most two black corners, its only possible collision has precisely two
common white corners. The other rectangle has the complementary pair black.

If the common pair is a side of both rectangles, their two complementary
black sides form another rectangle. If it is a diagonal of both, their two
black diagonals have equal midpoint and equal length, and their four black
endpoints form another rectangle. In either case that black rectangle is
nondegenerate: a repeated complementary endpoint would be a third shared
corner of the original rectangles. The black rectangle is either tilted,
contradicting the geometric restriction, or axis aligned, contradicting the
incidence four-cycle exclusion.

It remains to compare a black side \(A,B\) with a black diagonal \(C,E\).
The common white pair has x-coordinates

\[
\frac{C_x+E_x+(B_x-A_x)}2,
\qquad
\frac{C_x+E_x-(B_x-A_x)}2.
\]

Both numerators are divisible by \(D\). Since the displayed coordinates are
integers and \(D\) is odd, both coordinates are divisible by \(D\). The tilted
rectangle in this comparison consequently has all four corners on the coarse
x-lattice, again impossible. This also handles a comparison with an axis
rectangle. All possible collisions are excluded.

The C4/C6-free incidence hypothesis is a convenient sufficient hypothesis that
avoids tiny-board exceptions to the statement that axis validity implies the
absence of a hidden axis rectangle. The same proof works directly under axis
presentation uniqueness and absence of a hidden axis rectangle.

## Consequences and finite checks

Take the distinct double pairs to be the edges of any complete bipartite row
graph, and put them in any order. Subdivision of that triangle-free simple row
graph gives a C4/C6-free incidence graph. Odd spacing \(D>H/2\) therefore makes
every order a valid empty-column scaffold. A balanced graph has
\(q=\lfloor h^2/4\rfloor\) pairs, so its geometric width is
\(D(q-1)+1=O(h^3)\).

For height 15 and distinct parity double pairs, the even spacing 8 also works.
The odd-spacing proof does not by itself cover this even case. Here is the
additional argument. A mixed comparison with a vertical black side would give
an odd integer length \(L\le14\), a horizontal black-diagonal gap of 8, and an
odd vertical gap \(z\), with \(L^2-z^2=64\). The factor pairs of 64 give no such
odd \(L,z\) within the strip. A vertical black diagonal also has an odd length
\(L\le14\). Equating its length to a nonvertical black side gives the same
equation, so this case is excluded too.

For the remaining mixed comparison write the black side as \(U=(8a,y)\),
\(a>0\), the black diagonal as \(V=(8v,z)\), \(v>0\), and the perpendicular
translation between black and white sides as \(T=(4b,t)\). Their centers give
\(b\equiv v-a\pmod2\). Orthogonality and the strip bound imply
\[
32|ab|=|yt|\le49.
\]
If \(b\ne0\), then \(a=|b|=1\) and \(v\) is even, hence at least 2.
The equality of lengths gives \(y^2-z^2\ge192\), so the integer \(|y|\) is at
least 14. But \(t\ne0\), contradicting \(|y|+|t|\le14\).
If \(b=0\) and \(y\ne0\), then \(t=0\), which makes the side rectangle
degenerate. If \(y=0\), then \(a,v\) have the same parity, and a distinct
nondegenerate comparison requires \(a>v>0\). Thus
\(z^2=64(a^2-v^2)\ge512>14^2\), also impossible.
The same-side and same-diagonal cases still reduce to a hidden coarse
rectangle. Therefore every order of the distinct parity pairs is valid at
spacing 8, with empty seas.

The particular stretched order saved in
`spacing8_h15_seed17_empty.json` has 112 black points on a width-441 board.
Independent enumeration of every rectangle with at least two black points
finds 34,877 such rectangles and 34,877 different white presentations. The
result and input hash are in `spacing8_h15_seed17_empty_pair_check.json`.

The independent scaffold check alone does not establish a filling. A separate
exact fiber run has now supplied all 385 sea points, and a checked transition
to a constant tail proves equality at every width at least 441. The proof and
certificate paths are in height_fifteen_spacing_eight_completion.md.
The stronger power-of-two spacing statement, with the sharp height range
for universal order freedom, is in fixed_spacing_universal_order_threshold.md.
