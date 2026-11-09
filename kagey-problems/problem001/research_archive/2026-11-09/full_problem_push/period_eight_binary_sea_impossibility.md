# Every fixed period-eight binary sea fails at infinitely many heights

9 November 2026. A fixed seven-bit gap cannot replace the variable binary
filling in the successful height-15 construction.

**Theorem.** Let \(t\) be a positive odd integer and \(h=38t+1\). Put all
\(q=(19t)(19t+1)\) parity pairs, each once, in consecutive double slots
\(0,8,\ldots,8(q-1)\). For each residue \(j=1,\ldots,7\), choose one row
\(f_j\in\{1,h\}\), and use it in every sea column congruent to \(j\) modulo
eight. No order of the double pairs is identifying.

Thus all 128 fixed period-eight binary patterns fail at
\(h=39,115,191,\ldots\). The theorem permits a different pattern at each
height. It does not exclude larger periods, label-dependent patterns, or
arbitrary binary sea words.

All coordinates in the proof are relative to a chosen double column.
Translation by a multiple of eight preserves the sea pattern.

## 1. Odd residues must be constant within their classes modulo four

First suppose \(f_t\ne f_{37t}=f_{5t}\), with subscripts reduced modulo eight.
Take a double containing the even row \(r=t+1\). The sea points at offsets
\(p=t,q=37t\) have different boundary rows. Together with \((0,r)\), they
are three corners of a tilted rectangle, because
\[
pq=37t^2=(r-1)(h-r).
\]
This identity works for either assignment of the two boundary rows. Its fourth
corner is \((38t,37t+1)\). That row is even, while the sea at its column is
in an odd row. The singleton presentation therefore has an axis rival from
the full parity graph.

The even row \(t+1\) occurs in \(19t+1\) doubles. At most
\(\lceil38t/8\rceil\le5t\) slots are too close to the right endpoint for this
rectangle. Hence some occurrence gives the forbidden presentation. A valid
board would require \(f_t=f_{5t}\).

Similarly, take the even row \(r=5t+1\) and offsets \(p=3t,q=55t\). Since
\[
pq=165t^2=(5t)(33t)=(r-1)(h-r),
\]
different colors \(f_{3t}\ne f_{55t}=f_{7t}\) create a tilted singleton at
\((58t,33t+1)\). Again its row is even and its column is a sea column, so the
full parity graph supplies its axis rival. At most
\(\lceil58t/8\rceil\le8t\) centers lie too near the right endpoint, fewer than
the \(19t+1\) occurrences of row \(5t+1\). Thus \(f_{3t}=f_{7t}\).

Because \(t\) is odd, the two equalities give exactly one color on each of
the two odd residue classes modulo four. Write
\[
A=f_t=f_{5t},\qquad B=f_{3t}=f_{7t},\qquad C=f_{4t}=f_4.
\]

The axis-rival use here is global, but exact. The opposite-parity pair formed
by the displayed even white row and the actual boundary sea row has a unique
double owner elsewhere. The presentation column is \(2\bmod4\), so it cannot
be that owner. This produces a distinct axis rectangle with precisely the
same singleton presentation.

## 2. The two odd classes must agree, and residue four must differ

Consider the odd row \(r_L=4t+1\). A tilted rectangle with black diagonal
\((0,r_L),(3t,1)\) has white horizontal diagonal
\[
(-t,2t+1),\qquad(4t,2t+1).
\]
Indeed the two diagonals have the same midpoint and length \(5t\).
If \(B=C=1\), the row-1 sea points at offsets \(-t,3t,4t\) are black.
The two outer points provide the horizontal axis rival.

Reflecting the rows gives the same obstruction for \(B=C=h\), with central
odd row \(r_H=h-4t=34t+1\). Both central rows occur in \(19t\) doubles.
At most
\[
\lceil t/8\rceil+\lceil4t/8\rceil\le t+1<19t
\]
centers fail the required left and right margins. Thus \(B\ne C\).

Reflecting the columns replaces the three offsets by \(-4t,-3t,t\). Their
odd-residue color is \(A\), so the same argument gives \(A\ne C\).
Since the sea has only two colors,
\[
A=B,\qquad C\ne A.
\]
The colors in residues two and six remain unrestricted.

## 3. A mixed collision kills the remaining patterns

Suppose first \(A=B=1\), \(C=h\). At a double containing row \(34t+1\), the
four points
\[
(0,34t+1),\quad(17t,1),\quad(13t,1),\quad(12t,38t+1)
\]
are black. The last three columns have odd, odd, and four modulo eight
residues, so their colors are already forced. Define
\[
P=(4t,36t+1),\qquad Q=(21t,2t+1).
\]
The black side from \((0,34t+1)\) to \((17t,1)\) has perpendicular
translation \((4t,2t)\), so these black points together with \(P,Q\) form
a rectangle. The other two black points have midpoint and diagonal norm
equal to those of \(P,Q\):
\[
17^2+34^2=1+38^2=1445.
\]
They form a second rectangle with the same two white corners \(P,Q\).
The whites are strictly interior rows in sea columns, so their colors cannot
depend on unspecified double partners.

Only \(\lceil21t/8\rceil\le3t\) double centers lack enough room to the right.
Row \(34t+1\) occurs in \(19t\) doubles, so at least one occurrence gives this
collision. If \(A=B=h,C=1\), reflect the rows and use row \(4t+1\).
This excludes the last patterns and proves the theorem.

## 4. Consequence for an odd-row-block proposal

There is a related obstruction to filling a one-prime odd-row-block scaffold
by row 1 in non-four-slots and row \(h\) in unused four-slots. At height 39,
use the final double of the odd-row-35 block. The next long gap makes
\((12,39)\) black, while \((13,1),(17,1)\) are ordinary sea points. The
same mixed collision has common whites \((4,37),(21,3)\). Thus this default
gap filling fails whenever that gap has length at least 21. For a prime
parameter greater than \(10h\), it certainly does.

This failure does not exclude a different filling of the gaps.

## 5. The three surviving templates at every admissible height

The first two reductions give a useful general classification.

**Proposition.** If \(h\ge11\), \(h=3\bmod4\), and a complete parity board
with spacing eight and a fixed period-eight sea is valid, then all four odd
residue classes have one boundary color, and residue four has the other.
Up to vertical and horizontal reflection, only the seven-bit masks
\(8,10,42\) remain. Residues two and six are the only unconstrained bits.

To force \(f_1=f_5\) and \(f_3=f_7\), use the following central rows and
sea offsets:
\[
\begin{array}{c|c|c|c}
h\bmod8&\text{central row }r& (p,q)&\text{equality forced}\\ \hline
3&4&(1,3(h-4))&f_1=f_5\\
3&4&(3,h-4)&f_3=f_7\\
7&2&(1,h-2)&f_1=f_5\\
7&10&(3,3(h-10))&f_3=f_7.
\end{array}
\]
Each product equals \((r-1)(h-r)\). The central and completed rows are even,
and the completion column is two modulo four. Thus differing sea colors
produce the same tilted-singleton/axis-rival collision as in Section 1.
Every listed right span is at most \(3h-11\). Fewer than \((h+1)/2\) double
slots lie within that distance of the right endpoint, so the multiplicity
of the central even row forces a fitting occurrence.

Rows 5 and \(h-4\), with offsets \((-1,3,4)\) and their reflection, then give
\(f_1=f_3=f_5=f_7\ne f_4\), exactly as in Section 2. These row labels each
occur at least five times, while only the two endpoint slots can prevent
these short certificates.

If the common odd-residue color is row 1, the four masks are
\(8,10,40,42\). Horizontal reflection exchanges 10 and 40. Vertical reflection
handles the complementary colors, leaving the three stated representatives.

The companion verify_period_eight_obstruction.py checks the displayed
rectangles and matching presentations for all 128 patterns and odd scales
through 31. It uses only integer arithmetic and does not import the SAT or
existing geometric compilers.
