# A locally safe orientation for every parity edge

9 November 2026. This gives a positive construction rule for spacing eight.
It does not yet produce an equality board: collisions involving two or more
double labels and the transition between orientations remain open.

Let \(h\equiv3\pmod4\), and leave every column \(8j\) available for a double.
In the other columns use the background
\[
G_0=(1,1,1,h,1,1,1).
\]
Thus a low boundary black point has a column nonzero modulo four, and a high
boundary black point has a column four modulo eight. Write \(G_1\) for the row
reflection of this background.

**Local orientation theorem.** The background with all double slots empty
has no forbidden support, including its singleton and vertical axis rivals
against the final complete parity graph. Add one parity edge \(\{a,b\}\) at
column zero, where \(a\) is odd and \(b\) is even. If \(a=1\pmod4\), no
forbidden support uses only this edge and the background \(G_0\). If
\(a=3\pmod4\), the same conclusion holds for \(G_1\).

Here an axis rival with a singleton or vertical white presentation uses the
final parity graph, even though its remote owner is absent from this local
model. Horizontal and oblique rivals require their actual black points.
Other empty double slots cannot supply required black points. This is the
precise zero-label and one-label statement used below.

The theorem supplies the assignment
\[
\sigma(a)=(a-1)/2\pmod2.
\tag{1}
\]
It applies to the entire parity edge, not just its odd endpoint. The even
endpoint imposes no extra one-label obstruction.

## 1. Geometry that restricts the cases

Two boundary points in a tilted rectangle inside the strip must be on opposite
boundaries and form a diagonal. A side spanning the full height cannot have a
nonzero perpendicular translate inside the strip. A horizontal side would
make the rectangle axis-aligned.

A tilted rectangle cannot have three boundary black points. If it contains
both central points, they form a vertical diagonal. Its other corners have
rows strictly between the central rows, so neither is a boundary point.
Consequently no hidden rectangle can be formed from the background and the
single parity edge. Axis-aligned hidden rectangles are also impossible,
because only the central column has two black points.

Any collision involving a rectangle with three white corners is impossible:
three corners determine a rectangle. It therefore suffices to check
singleton and two-point white presentations, together with hidden rectangles.

For a two-point presentation, two distinct rectangles whose black pairs both
form sides would give a hidden rectangle between the two parallel black
sides. If both black pairs form diagonals, they have equal midpoint and
length and again form a hidden rectangle. The remaining case has one black
side and one black diagonal. Call it a mixed collision.

In a mixed collision, integrality of the shared white corners requires the
sum of the four black row coordinates to be even. Thus a mixed support with
the even central point and three boundary points is impossible. The same
argument excludes supports with both central points and two boundary points.
Only the odd central point and three boundary points need further analysis.

Vertical axis rivals are also impossible. For a black diagonal joining a
central point to a boundary point, its length is strictly greater than its
vertical difference. A vertical alternative diagonal therefore extends past
that boundary. For the two central points, the black diagonal is already
vertical, and the only vertical alternative with its midpoint and length is
the same pair. It cannot give a distinct rectangle.

## 2. Zero-label supports

Put \(H=h-1\), so \(H=2\pmod4\). A weak tilted rectangle supported by the
background has an opposite-boundary black diagonal. Its horizontal difference
\(d\) is nonzero modulo four. Its squared diagonal length is \(d^2+H^2\).
If \(d\) is odd, this is five or thirteen modulo sixteen. If
\(d=2\pmod4\), it is eight modulo sixteen. It is never a square.

The other diagonal therefore cannot be horizontal or vertical with integral
endpoints. An oblique axis rival would require an interior-row black point,
which the background does not have. Two tilted rectangles cannot have the
same white pair, since both black pairs would be diagonals and would form a
hidden rectangle. There are no three-black tilted rectangles. This proves
the zero-label assertion, including virtual parity axis rivals.

## 3. Singleton presentations

Any three-black tilted rectangle must contain one central point \((0,r)\)
and one point on each boundary. The right angle is at the central point:
placing it on a boundary would put the fourth row outside the strip.
Write the two horizontal offsets as \(p,q\). Then
\[
pq=(r-1)(h-r),\qquad
\text{completion}=(p+q,h+1-r).
\tag{2}
\]

If \(r\) is even, both offsets are odd. Both background points would then
be on row one, contradicting their opposite boundary rows. Thus the even
central point never participates in a three-black tilted rectangle.

Suppose \(r=a=1\pmod4\). For an interior \(a\), the product in (2) is
divisible by eight. The high boundary offset is four modulo eight. The low
boundary offset is nonzero modulo four. Their product can be divisible by
eight only when the low offset is two modulo four. Their sum is therefore
two modulo four, so the completion lies in a sea column. Its row is odd and
strictly interior. Every black point in that sea column is odd, so the
complete parity graph supplies no singleton axis rival. Boundary values of
\(a\) give no nondegenerate instance of (2).

There cannot be a second three-black tilted rectangle with the same singleton
presentation. Its completion row determines its central row. Its completion
column and (2) determine the unordered pair \(\{p,q\}\). The actual boundary
colors determine the assignment of the two offsets. Hence the rectangle is
unique. This also excludes six-point supports using at most one double label.

## 4. The central point as a black side endpoint

Only the odd central point \((0,a)\), with \(a=1\pmod4\), remains relevant
to mixed collisions. First let its black side partner be \((u,1)\). Put
\[
d=a-1,\qquad w=(h-a)/2.
\]
Then \(d=0\pmod4\) and \(w\) is odd. The black diagonal of the other
rectangle has one endpoint \((c,1)\) and one endpoint \((e,h)\). Equality
of midpoint and length gives
\[
v=dw/u,\qquad c+e=u+2v,\qquad
(e-c)^2=u^2+d^2-H^2.
\tag{3}
\]
All coordinates are integral. The low boundary conditions give
\(u,c\ne0\pmod4\), while \(e=4\pmod8\).

If \(u\) is odd, the last expression in (3) is five or thirteen modulo
sixteen and cannot be a square. Otherwise \(u=2\pmod4\), and \(v\) is
even. The midpoint equation forces \(c=2\pmod4\). Thus \(e-c=2\pmod4\),
but the squared-length equation requires \((e-c)^2=0\pmod{16}\), a
contradiction.

If the side partner is on the high boundary, reflect the rows for the
calculation. Now \(u=c=4\pmod8\), the other boundary column \(e\) is
nonzero modulo four, and the reflected vertical side component is
\(d=h-a=2\pmod4\). The length equation in (3) forces \(e-c=0\pmod4\),
again a contradiction. This excludes both possible boundary side partners.

## 5. The central point as a black diagonal endpoint

The other black pair is a side containing two boundary points. It cannot
span the two boundaries, so it is horizontal and belongs to an axis
rectangle. This is exactly a horizontal axis rival.

If the other endpoint of the black diagonal is on the high boundary, its
horizontal difference is four modulo eight and its vertical difference is
two modulo four. Its squared length is twenty modulo thirty-two, which is
not a square. It therefore cannot have a horizontal integral other diagonal.

If the other endpoint is \((t,1)\), put \(d=a-1\). Let the horizontal white
diagonal have endpoint columns \(u,v\). Equal midpoint and length give
\[
u+v=t,\qquad uv=-d^2/4.
\tag{4}
\]
Here \(d\) is divisible by four and \(t\ne0\pmod4\). A nondegenerate
instance has \(d>0\). The white endpoint
columns are nonzero, so neither can use a central black point for its axis
rival. If both axis-rival black points are on row one, then \(u,v\) are
nonzero modulo four. Since their product is divisible by four, both must be
two modulo four. This forces \(t=0\pmod4\), a contradiction. If both are on
row \(h\), both columns are four modulo eight, again forcing
\(t=0\pmod4\). A required black point in any other double slot would use a
second label and is outside the one-label scope.

Sections 1 through 5 exhaust the possible failures. Row reflection sends an odd row
three modulo four to one modulo four, proving the complemented statement.

## 6. Consequence and remaining construction problem

The local arithmetic does not require a different irregular sea for every
edge. It needs only two background orientations, selected by the odd
endpoint modulo four. This suggests two regions of consecutive occupied
double slots, one for each odd row class.

The theorem does not control supports using two or more labels, nor supports
crossing an orientation change. A successful construction still needs an
edge order and a transition whose length is \(O(h^2)\) in total. In
particular, placing edges into regions without checking those conditions
does not prove a quadratic equality construction.

The independent pair-completion script `verify_one_label_orientation.py`
checks every permitted edge at heights 7, 11, 15, and 19, together with the
zero-label backgrounds. All 98 cases pass. The checked intervals extend more
than twice the maximum tilted span on each side of the central double.
The script imposes the final parity graph for singleton and vertical rivals,
so the holes at other double slots do not silently remove those constraints.
