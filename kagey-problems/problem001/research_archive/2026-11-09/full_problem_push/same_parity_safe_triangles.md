# Retaining same-parity triangles rooted at a label

9 November 2026. The safe-triangle event family can also retain a tilted
right angle rooted at a label point, with its second label point on a
row of the same physical parity and its third point in binary sea row
\(L\) or \(H\). Its completion is white and has no axis rival.
The additional singleton collisions are controlled by the exact
events below. This is an event-family refinement; it does not improve
the established width bound on its own.

Use one of the oriented mixed-residue or separate zero-residue blocks
from [safe_triangle_pair_first_moment.md](safe_triangle_pair_first_moment.md).
Every label column is zero modulo seven. Two selected label rows of
the same physical parity have the same normalized residue. In a
mixed-residue block they are both zero or both five; in a zero-residue
block they are both zero.

## 1. The white completion and the axis test

Let the right-angle vertex be \(A=(0,a)\), the other label point
be \(C=(\Delta,c)\), and the sea point be \(X=(x,s)\), where
\(s\in\{L,H\}\) and \(a\equiv c\pmod2\). Put \(D=c-a\).
The angle equation and completion are
\[
\Delta x=-D(s-a),\qquad
W=(\Delta+x,s+D).
\tag{1}
\]
The two label columns are distinct. If \(D=0\), (1) forces
\(x=0\), where the label has replaced the sea point, so there is
no such triangle. Thus \(D\ne0\).

The completion column has the same nonzero residue as \(x\), so
its retained sea row is exactly \(s\). Its row differs from \(s\)
by the nonzero even integer \(D\). Hence the completion is white
and has the same physical parity as its retained sea point. The full
parity graph supplies no singleton axis rival.

The completion has normalized row residue zero or one, according to
the sea level. These residues differ from four, the residue of the
previously retained triangles rooted at a high sea point. Therefore
the new and old types cannot share a singleton presentation.

## 2. The exact two-label singleton collisions

Fix labels \(e=\{a,b\}\) at column zero and
\(f=\{c,d\}\) at column \(\Delta\). A collision of two new
triangles forces the same sea level \(s\), since low and high sea
columns have different character classes.

If the two triangles have their right-angle vertices in the same
label column, equality of completion rows gives
\(c-a=d-b=D\). Equality of completion columns then gives
\(D(a-b)=0\). This is impossible because \(D\ne0\) and the two
endpoints of a label are distinct. Reusing the same selected endpoints
gives the same triangle, not a collision.

If the right-angle vertices are in opposite label columns, use
\((a,c)\) for the first same-parity pair and \((d,b)\) for the
second. Equality of the white row and column gives exactly
\[
c-a=b-d=D,\qquad
\Delta^2=D(2s-a-d).
\tag{2}
\]
For the low sea level, both label rows are above \(s=L\), so
\(2s-a-d<0\). A genuine solution therefore has \(D<0\), and its
completion lies in the strip only if
\[
1-L\le D\le-1.
\tag{3}
\]
For the high level, both label rows are below \(s=H\), giving
\[
1\le D\le h-H.
\tag{4}
\]
Both ranges have absolute constant length. Once \(e\), \(s\),
and \(D\) are fixed, (2) determines the partner label
\(c=a+D,d=b-D\), and permits at most two column gaps. Consequently
the incident count of these restored two-label collision geometries
is \(O(1)\) per fixed label.

These events must be forbidden. They need not be four-cell events:
the two sea corners can be distinct, giving a genuine six-cell
symmetric difference on only two labels. Their bounded count, rather
than an absence claim, makes them harmless to the placement estimate.

## 3. The complete extra-event list

After retaining the new triangles, use the following forbidden events.

1. Retain every previously forbidden mixed four-cell support and
   vertical parity rival. Keep every three-black tilted rectangle
   forbidden unless it is one of the old safe high-root triangles or
   a new same-parity label-root triangle described here.
2. Add the bounded two-label singleton-collision family (2)--(4).
3. Add every genuine six-cell singleton collision of two new triangles
   using three or four labels. Their common white row imposes a
   nontrivial difference equation between four selected label rows.
   For each fixed row tuple, (1) gives divisor-many factorizations,
   uniformly \(h^{o(1)}\). As in the earlier proof, the row equation
   saves a factor \(h\) in the full squared count. Thus these events
   are absorbed by the existing higher-arity bound.

There is no mixed old/new singleton collision because their completion
residues differ. Shared-black-corner cases have a four-cell symmetric
difference and are already covered by item 1. Hidden rectangles are
still absent: every retained triangle has a white completion, while
all other three-black tilted rectangles remain forbidden. This proves
completeness of the augmented event list.

The additional two-label contribution is bounded, and the higher-arity
contribution has the same codimension saving as before. The audited
width theorem therefore remains valid with this larger allowed family.

## 4. Which private pair roles remain

In a mixed-residue block, endpoints of opposite physical parity have
normalized residues zero and five. A right angle rooted at a label
point has modular equation
\[
(c-a)(s-a)=0,
\]
because both label columns are zero. Thus the only remaining
opposite-parity label-root triangle has its root at the odd
normalized-residue-zero row and its sea point at low level \(L\).
No filler or high-sea counterpart survives modulo seven.

This conclusion does not extend unchanged to the separate zero-residue
blocks. There, endpoints of opposite physical parity can still have
the same normalized residue zero. Their label-root triangles are not
excluded by this modular equation, and the corresponding private
pair roles remain forbidden. Handling those blocks is part of any
future improvement.

## 5. An optional extension to filler-sea triangles

The same-parity calculation also applies when \(s=F\), except that
the completion column is another hole. Its normalized row is three,
so it cannot equal an endpoint of any ordinary label. It is therefore
always white. If the hole retains its filler, the white row has the
same physical parity as \(F\), and the axis test is safe.

If a real label occupies the completion column, its opposite-parity
endpoint supplies a singleton axis rival. Thus this extension requires
the additional event that no real label occupies the completion hole
of a retained filler-sea triangle.

When that label is the root label itself, (1) gives
\[
\Delta^2=(c-a)(F-a),\qquad 1-F\le c-a\le-1.
\tag{5}
\]
There are only \(O(h)\) partner labels per fixed label and at most
two gaps per selected row. These are arity-two exceptions. The
completion cannot coincide with the other label column, since that
would require the original sea point at the root column.
When a third label occupies the completion column, this is an
arity-three event; its center is fixed by the two triangle centers
and the selected factorization in (1).

The two-triangle analysis of Section 2 also applies with \(s=F\).
Its two-label collisions have \(1-F\le D\le-1\), and its
three-/four-label collisions have the same row-equation saving.
Completion residue three differs from the binary levels and the old
high-root residue, so there are no cross-type singleton collisions.

These statements specify the full geometric event list for the filler
extension. A quantitative placement bound for its new occupation
events is not asserted here.
