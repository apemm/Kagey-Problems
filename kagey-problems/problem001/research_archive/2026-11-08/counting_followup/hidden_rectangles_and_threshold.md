# Hidden rectangles and the threshold lower bound

Research note, 8 November 2026. No earlier report or manuscript is modified here.

## 1. The quadratic threshold lower bound is already proved

For \(h\ge4\) and \(m\ge3\), the paper's equality-structure theorem says that a valid blackout
with \(m+q_h\) black points has exactly \(q_h=\lfloor h^2/4\rfloor\) double columns. Every other
column is a singleton. Distinct doubles occupy distinct columns, so

\[
 m\ge q_h.
\]

Thus the threshold satisfies \(m_h\ge\lfloor h^2/4\rfloor=\Omega(h^2)\). This is already the
paper's small-width corollary in `jis/sections/sec04_graph.tex`. It does not require the boundary-layer
lemma or the `1, x, h` family. The open order-of-growth question is the matching quadratic upper bound.

## 2. Crossing an oblique diagonal excludes a hidden rectangle

**Proposition.** A hidden tilted rectangle with an oblique diagonal cannot belong to a valid blackout.

**Proof.** Let its black diagonals be \(A,C\) and \(B,D\), with

\[
 A=(x,a),\qquad C=(z,c),\qquad x\ne z,\quad a\ne c.
\]

Set \(U=(x,c)\) and \(V=(z,a)\). The crossed pair \(U,V\) has the same midpoint and length
as \(A,C\), hence also as \(B,D\). Therefore \(U,V,B,D\) are the corners of a rectangle
\(R'\). Its two diagonals cannot coincide: if \(\{U,V\}=\{B,D\}\), the original rectangle
would have been axis-aligned. Distinct equal-length diagonals with a common midpoint give a
nondegenerate rectangle.

Let \(T\) be the axis-aligned rectangle with corners \(A,C,U,V\). The two rectangles are
distinct, all their corners lie in the grid, and

\[
 C(R')\mathbin\triangle C(T)=\{A,B,C,D\}\subseteq S.
\]

They consequently have the same presentation, whether neither, one, or both of \(U,V\) is black.
This contradicts validity. \(\square\)

The two crossed points stay inside the original bounding box. Unlike the outward-extension
argument in Appendix A of the earlier report, this argument has no end or boundary qualification.

## 3. Subdivision excludes nonprimitive sides

**Lemma.** A hidden lattice rectangle with a nonprimitive side vector is invalid.

**Proof.** Write its corners as \(p,p+v,p+w,p+v+w\), where \(v\cdot w=0\). Suppose
\(w=g w_0\) for an integer \(g\ge2\) and a lattice vector \(w_0\). The two rectangles

\[
 \{p,p+v,p+w_0,p+v+w_0\},
\]

\[
 \{p+w,p+v+w,p+w_0,p+v+w_0\}
\]

are distinct and nondegenerate. Their common side lies inside the original rectangle. Their
symmetric difference is precisely its four black corners, so their presentations coincide. \(\square\)

**Theorem.** If \(h,m\ge3\), every hidden rectangle in a valid \(h\times m\) blackout is a unit
diamond

\[
 \{(x-1,r),(x,r-1),(x+1,r),(x,r+1)\}.
\]

**Proof.** A hidden axis-aligned rectangle is invalid by the paper's four-cycle argument, using a
third column. By the crossing proposition, a hidden tilted rectangle must have both diagonals
parallel to the coordinate axes. Equal diagonal lengths then give

\[
 \{(x-d,r),(x,r-d),(x+d,r),(x,r+d)\}
\]

with an integer \(d\ge1\). If \(d\ge2\), each side vector is a multiple of \(d\), and the
subdivision lemma applies. Hence \(d=1\). \(\square\)

## 4. Consequences for the counting model

1. **Every sea is hidden-free.** A diamond requires two black points in its central column.
   Thus rejecting all hidden rectangles is exact for valid singleton words, for every partition.
2. **Every parity equality word is hidden-free.** Its doubles contain opposite-parity rows,
   whereas the vertical pair of a unit diamond has row difference two. This conclusion includes
   arbitrary singleton seas and free transition gaps. It is not restricted to the pure `1, x, h`
   family.
3. **The other partitions need only count unit diamonds.** Such a diamond has a central double
   \(\{r-1,r+1\}\) and row \(r\) black in its two neighboring columns. A hidden event is
   detected on a three-column window. Validity allows at most one on the entire board.
4. **A hidden rectangle is tied to a double.** It cannot appear as an additional independent
   defect in a long sea interval. This matters when determining the polynomial factor in counting
   asymptotics.

For another partition, the exception is real. On a \(3\times4\) grid, take the columns

\[
 \{2\},\quad\{1,3\},\quad\{2\},\quad\{2,3\}.
\]

The doubles realize \(K_{\{1,2\},\{3\}}\), and there are \(6=m+q_3\) black points.
An independent enumeration verifies that the blackout is valid and contains exactly one hidden
unit diamond, centered at \((1,2)\) with zero-based column coordinates. Thus one cannot discard
hidden words for every partition merely because the parity case is hidden-free.

The crossing and subdivision constructions also explain the difference from the earlier report:
failure of all outward extensions does not make a hidden tilted rectangle exceptional. The
crossing argument eliminates every oblique-diagonal case inside its existing bounding box, and
subdivision eliminates all remaining diamonds except the unit one.

## 5. Verification

`check_hidden_classification.py` enumerates rectangles by equal-length diagonals. It checks the
crossing and subdivision identities on all tilted rectangles in a \(9\times10\) grid, and checks
the nonparity \(3\times4\) example by direct presentation equality. The proofs establish the
classification at arbitrary dimensions.
