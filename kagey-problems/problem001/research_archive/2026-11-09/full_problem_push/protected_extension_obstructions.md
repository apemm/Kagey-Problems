# Protected constant connections and two-row obstructions

9 November 2026. These exact examples distinguish connections between constant states from a full two-row shift. The latter fails for every same-parity two-row alphabet once the height is at least six. Sections 1--3 passed independent review.

Throughout, axis rivals use the ordinary parity partition. A protected alphabet consists of rows of one physical parity.

## 1. A six-cell obstruction for two rows at distance two

Suppose \(r+4\le h\). Put \(W=(0,r+4)\), and consider
\[
\begin{aligned}
 R_1&=\{(0,r),(-2,r+2),(2,r+2),W\},\\
 R_2&=\{(3,r),(-1,r+2),(4,r+2),W\}.
\end{aligned}
\tag{1}
\]
Both are tilted rectangles. The adjacent vectors at their respective lower vertices are
\[
 (-2,2),(2,2),\qquad (-4,2),(1,2),
\]
whose dot products vanish. Their six nonshared corners occupy the distinct columns
\[
 -2,-1,0,2,3,4.
\]
If those six cells are black, both rectangles have precisely the singleton white presentation \(\{W\}\). This is a collision within the alphabet \(\{r,r+2\}\).

At height five, a concrete seven-column word is
\[
 (3,3,1,1,3,1,3).
\tag{2}
\]
After translating (1) three columns to the right, the common white corner is \((3,5)\). The letter in the fourth column is irrelevant to the collision.

Vertical reflection gives the corresponding obstruction when \(r-2\ge1\). Consequently the full shift on \(\{r,r+2\}\) can be valid only if
\[
 r\le2,\qquad h\le r+3.
\tag{3}
\]
The mistaken uniqueness shortcut would keep only the symmetric diamond in (1). The factorization \(4=1\cdot4=2\cdot2\) gives two different three-black completions at the same white corner.

## 2. Every larger even gap already has a four-cell obstruction

Let \(d\ge4\) be even and \(r+d\le h\). Put \(n=d^2/4\). The four required black cells are
\[
 A=(0,r),\quad B=(n-1,r+d),\quad
 C=(-1,r),\quad D=(n,r).
\tag{4}
\]
They occupy four distinct columns. Define the white pair
\[
 W=(-1,r+d/2),\qquad Z=(n,r+d/2).
\]
The segments \(AB\) and \(WZ\) have the same midpoint, and
\[
 |AB|^2=(n-1)^2+d^2=(n+1)^2=|WZ|^2.
\]
Thus \(R=\{A,B,W,Z\}\) is a nondegenerate tilted rectangle. The axis rectangle \(T=\{C,D,W,Z\}\) has the same white presentation \(\{W,Z\}\). Every cell lies between rows r and \(r+d\), so this obstruction needs no additional vertical margin.

It follows that no same-parity binary alphabet with gap at least four gives a full valid shift at any height.

For completeness, the gap-two cases left by (3) really are full valid shifts. A tilted rectangle with three black corners on two row levels must repeat one row on a diagonal; its fourth row is \(r-2\) or \(r+4\), both outside the strip in (3). There are no hidden rectangles, since a rectangle on exactly two row levels is axis-aligned and would require two black cells in one column.

In a mixed four-cell collision, the vertical components of the complementary black side and diagonal lie in \(\{0,\pm2\}\). If both are zero, equal length and the required midpoint force the black diagonal to equal the displayed white side, rather than give a distinct rectangle. If exactly one is zero, their equal norms would require a nontrivial integer solution \(L^2-D^2=4\). None exists with both horizontal black pairs nonvertical. If both components are nonzero, equal norms give equal absolute horizontal components. The same-slope choice is degenerate; in the opposite-slope choice both pair midpoints have the same row, and perpendicularity forces the midpoints to coincide, also degenerate. Same-side and same-diagonal collisions would give a hidden rectangle. Vertical axis rivals are impossible for a single-parity sea.

Therefore the complete list of same-parity binary full shifts, for \(h\ge3\), is
\[
 \begin{array}{c|c}
 h&\text{two-row alphabet}\\ \hline
 3&\{1,3\}\\
 4&\{1,3\},\{2,4\}\\
 5&\{2,4\}.
 \end{array}
\tag{5}
\]
There are none for \(h\ge6\). This concerns the ordinary parity sea model, with its fixed complete axis pair set.

## 3. Constant protected states are nevertheless connected

Every monotone sea whose rows have one physical parity is valid. Its black points form a coordinatewise chain, so it has no three corners of a tilted rectangle. The projection argument for chain supports excludes nonvertical mixed side/diagonal collisions, including horizontal axis rivals; see
[threshold_progress.md, Section 9.1](threshold_progress.md#91-the-binary-sea-and-the-monotone-one-double-gadget).
Hidden rectangles and the remaining tilted collisions are then excluded as well.

Only a vertical axis rival remains to check. Its complementary black diagonal has endpoints whose row difference is even. An integral vertical alternative has an integral midpoint column, so the black diagonal's horizontal displacement is even. Its integer length is consequently even. The two white rows have equal parity and cannot form a parity-axis pair.

In particular, for any same-parity rows a and b, both single-switch seas
\[
 a^\infty b^\infty,\qquad b^\infty a^\infty
\tag{6}
\]
are valid. They connect all constant histories inside one protected recurrent component. The component is primitive because every constant history has a self-loop.

More generally, a monotone protected word can be continued by its first row on the left and its last row on the right. Every full-memory state in such a word lies in this protected constant component.

These connections do not prove irreducibility of the protected shift or extension of every protected core. The examples in Sections 1--2 show why full two-row mixing cannot supply that missing step.

## 4. Appending the smallest protected row is not always valid

At height five, take the valid protected sea with row 3 everywhere except for one row-5 letter at column \(-4\). Its only three-black tilted rectangles have completion row 1 and completion columns \(-7,-4,-1\), one rectangle at each. This follows from the three unordered signed factor pairs of the right-angle equation \(ab=-4\). There is no singleton collision. The gap-two mixed-support argument in Section 2 excludes every four-cell collision, and same-parity axis rivals are absent. Thus this sea is valid.

Keep its five-column suffix at columns \(-5,\ldots,-1\), namely
\[
 (3,5,3,3,3).
\]
Appending row 1 at column zero creates the required black cells
\[
 A=(-5,3),\quad B=(-4,5),\quad C=(-1,3),\quad D=(0,1).
\]
The tilted rectangle
\[
 R=\{A,B,(-1,1),(0,3)\}
\]
has perpendicular side vectors \((1,2)\) and \((4,-2)\). The axis rectangle
\[
 T=\{C,D,(-1,1),(0,3)\}
\]
has exactly the same white pair. Hence this one-letter extension is invalid.

The starting word already belongs to the protected constant component. This example only rejects the greedy rule that always appends the smallest row. It does not obstruct extension through a longer buffer.
