# The exact height range for universal order freedom at power-of-two spacing

9 November 2026. Fix \(D=2^s\) with \(s\ge3\). Place every opposite-parity row
pair once, in any order, in columns \(0,D,2D,\ldots\), and leave all other
columns empty.

**Theorem.** Every order is identifying if \(h\le2D\). For every
\(h\ge2D+1\), some order is not identifying.

This is a statement about universal order freedom for empty scaffolds. It
does not rule out a carefully chosen order above the threshold, and it does
not fill the empty columns. In particular, spacing eight requires a genuine
order search starting at height 17.

## Validity below the threshold

Put \(H=h-1<2D\). A tilted rectangle with all x-coordinates divisible by \(D\)
would have perpendicular side components satisfying
\[
D^2\le ac=bd\le H^2/4<D^2.
\]
Thus no such rectangle exists. Three black tilted corners would force the
fourth x-coordinate to be divisible by \(D\), so tilted rectangles have at
most two black corners. A hidden axis rectangle is excluded by distinctness
of the double pairs. The standard same-side and same-diagonal comparisons
reduce to these hidden rectangles. Only a mixed black-side/black-diagonal
comparison remains.

If either black pair is vertical, its length \(L\) is odd because it is a
parity double, and \(L\le H\). The other black pair has nonzero horizontal gap
a multiple of \(D\). Equality of lengths forces that gap to be exactly \(D\),
and
\[
L^2-z^2=D^2,\qquad L,z\ \hbox{odd}.
\]
The factorization \((L-z)(L+z)=2^{2s}\) forces the factors to be
\(2,2^{2s-1}\), up to order. Indeed one factor has 2-adic valuation one,
and both are powers of two. Therefore
\[
L=1+D^2/4>2D-1\ge H,
\]
a contradiction.

In the remaining comparison orient the black side and diagonal as
\[
U=(Da,y),\quad a>0,\qquad V=(Dv,z),\quad v>0.
\]
The translation from the black side to its common white side has the form
\(T=(Db/2,t)\), with \(b\equiv v-a\pmod2\). Orthogonality gives
\[
\frac{D^2|ab|}{2}=|yt|\le H^2/4<D^2.
\]
If \(b\ne0\), then \(a=|b|=1\). Hence \(v\) is a positive even integer.
Equality of lengths gives \(y^2-z^2\ge3D^2\), so
\(\sqrt3D\le|y|<2D\). On the other hand,
\(|yt|=D^2/2\) is a power of two, so the integer \(|y|\) must be a power
of two. There is none in that interval.

If \(b=0\) and \(y\ne0\), perpendicularity forces \(t=0\), making the side
rectangle degenerate. If \(y=0\), then \(a,v\) have the same parity. A
nondegenerate distinct comparison requires \(a>v>0\), giving
\[
z^2=D^2(a^2-v^2)\ge8D^2>H^2.
\]
This excludes the last possibility. Axis presentations were already distinct
because the simple parity graph is triangle-free. The scaffold is identifying.

## A counterexample at the next height

For \(h\ge2D+1\), put these four distinct parity pairs in the indicated slots:
\[
\begin{array}{c|cccc}
x&0&D&2D&3D\\ \hline
\hbox{black rows}&\{D+1,2\}&\{1,6\}&\{D+1,4\}&\{2D+1,6\}.
\end{array}
\]
Assign all remaining parity pairs to the remaining slots in any order.
The tilted square
\[
R=\{(0,D+1),(D,1),(2D,D+1),(D,2D+1)\}
\]
has three black corners and the singleton presentation
\(\{(D,2D+1)\}\). Its adjacent side vectors are \((D,-D)\) and \((D,D)\).
The axis rectangle
\[
T=\{(D,6),(3D,6),(D,2D+1),(3D,2D+1)\}
\]
has exactly the same presentation. Adding the remaining doubles does not
change either presentation. This proves failure of universal order freedom
at every larger height.
