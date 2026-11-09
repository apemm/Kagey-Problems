# A boundary star in width \(O(h^{5/3})\)

9 November 2026. This improves the spacing in [the quadratic boundary-star construction](boundary_star_quadratic_gadget.md). The original theorem and its verification remain unchanged.

Let \(n=\lfloor h/2\rfloor\). Keep row one black in every column of the infinite strip, and add
\[
 (pi,2i+2),\qquad 0\le i<n,
 \tag{1}
\]
where \(p\ge4\) is divisible by four. Test the word against the complete final opposite-parity pair set, including pairs not present in this block.

**Theorem.** If
\[
 h\le p(\sqrt p-1),
 \tag{2}
\]
then (1) is hidden-free and identifying. Its block of doubles has width \(p(n-1)+1\), and arbitrary constant row-one tails are allowed. Any subset of the displayed doubles can be retained.

In particular, let \(k\) be the smallest positive integer with \(k^3\ge h\), and take
\[
 p=4\left\lceil\frac{(k+1)^2}{4}\right\rceil .
 \tag{3}
\]
Then (2) holds and
\[
 p(n-1)+1=\left(\frac12+o(1)\right)h^{5/3}.
 \tag{4}
\]
The uniform-in-\(p\) safety exponent is matched by an explicit sequence of mixed collisions at heights \(\Theta(p^{3/2})\). This does not exclude a better construction that selects a special arithmetic subsequence of spacings.

This is a complete gadget for the boundary star, not a construction of every parity edge.

## 1. All cases except crossed mixed supports

Call the points in (1) extra points. They lie on a line of direction \((p,2)\), above the horizontal baseline at row one.

There is no hidden rectangle. Three points on either line are collinear. With two points on each line, the baseline pair cannot be a side of a tilted rectangle, and a baseline diagonal would require the other endpoints on opposite sides of row one.

A tilted rectangle with three black corners therefore has two extra points and one baseline point. The right angle cannot be at an extra point of row \(2i+2\): the perpendicular to \((p,2)\) meets the baseline at horizontal displacement \(2(2i+1)/p\), which is not integral when \(4\mid p\).

Let the two indices be \(i<j\), and let the baseline right-angle vertex be \((x,1)\). Its missing corner \(W\) satisfies
\[
 W_y=2(i+j)+3,\qquad W_x=p(i+j)-x,
\]
and
\[
 (pi-x)(pj-x)+(2i+1)(2j+1)=0.
 \tag{5}
\]
The vertical product in (5) is odd, so \(x\) is odd. Hence \(W_x\) is odd and cannot be an extra column. Its retained black point is on row one, of the same parity as \(W_y\), so there is no singleton parity-axis rival.

For a fixed \(W\), its row determines \(i+j\), and its column then determines \(x\). Equation (5) has coefficient \(p^2+4\) on \(ij\), so it determines the unordered pair \(\{i,j\}\). Thus singleton presentations are unique.

A black diagonal involving a baseline point has no distinct in-strip vertical alternative: the longer alternative extends below row one. If both endpoints are extra points, both rows are even, and any integral vertical alternative has even length and same-parity displayed rows. There is therefore no vertical parity-axis rival.

Two rectangles sharing a side in both, or a diagonal in both, would force a hidden rectangle on their four nonshared black corners. The remaining four-cell case is mixed: one black pair is a side \(U\), the other is a diagonal \(V\), their lengths agree, and \(U\) is perpendicular to the difference \(H\) of the two pair sums.

Integrality of their common corners requires an even total black-row sum. Thus a mixed support uses exactly two extra points and two baseline points; zero or four extra points would put all four black points on one line. Pairing the extras together and the baseline points together is impossible, because the former length is a nonzero integer multiple of \(\sqrt{p^2+4}\), which is irrational, and the latter length is an integer.

Only the crossed pairing remains.

## 2. An arithmetic lower bound on every crossed mixed support

Subtract one from all row coordinates. The baseline is now at height zero. Let the side's extra height be \(a\), and the diagonal's extra height be \(b\), both positive odd integers. The common corners have heights \((b-a)/2,(b+a)/2\), so they require \(b\ge a\). Equality repeats the same extra point, which is not a four-point support. Write
\[
 b=a+2D,\qquad D\ge1.
\]

Orient both pairs from their baseline point to their extra point, with horizontal components \(u,v\), respectively. Their extra horizontal coordinates differ by \(pD\), so
\[
 H=(2pD+u-v,2D).
\]
The norm equation gives \(|u|>|v|\). If \(u\ge0\), both terms of \(U\cdot H\) are positive. Therefore \(u=-U\), where \(U>0\).

The norm equation modulo four makes \(U,v\) have the same parity. Put
\[
 x=(U+v)/2,\qquad y=(U-v)/2.
\]
Then \(x,y\) are positive integers, \(U=x+y\), and the norm and perpendicularity equations are
\[
 xy=D(a+D),\qquad (pD-x)U=Da.
 \tag{6}
\]
Set \(z=pD-x\). This is a positive integer, and \(zU=Da\). Substituting into (6) gives
\[
 (pD-2z)U=(pD-z)^2+D^2>0.
\]
In particular \(pD-2z>0\). The integer
\[
 k=U-pD
\]
therefore satisfies
\[
 k(pD-2z)=z^2+D^2,
 \tag{7}
\]
so \(k>0\).

The relation \(Da=z(pD+k)\) implies \(D\mid zk\). Reducing (7) modulo \(D\) then gives
\[
 D\mid z^2.
 \tag{8}
\]
Consequently \(1\le D\le z^2\). Since \(k\ge1\), (7) implies
\[
 p\le \frac{2z}{D}+\frac{z^2}{D}+D
   \le 2z+z^2+1=(z+1)^2.
 \tag{9}
\]
The second inequality uses
\[
 D+\frac{z^2}{D}\le z^2+1
 \quad(1\le D\le z^2).
\]
On the other hand,
\[
 a=\frac{z(pD+k)}D>pz.
\]
Since the strip contains the larger extra row \(b+1>a\), every crossed mixed support forces
\[
 h>p z\ge p(\sqrt p-1).
 \tag{10}
\]
This contradicts (2). Thus all mixed supports are excluded.

For (3), \(\sqrt p-1\ge k\), and hence
\[
 p(\sqrt p-1)\ge (k+1)^2k\ge k^3\ge h.
\]
Also \(p=h^{2/3}+O(h^{1/3})\), proving (4).

## 3. Complete validity and deletions

The preceding sections exclude hidden rectangles, singleton collisions, all two-white tilted collisions, and virtual singleton or vertical axis rivals. Horizontal and oblique axis rivals fall under the same hidden or mixed four-cell classification. Presentations with at least three common corners determine the rectangle. Axis-axis uniqueness follows because the double pairs are distinct edges of a star.

The argument was made in the infinite strip, so it already includes every constant row-one tail and survives finite restriction. Deleting extra points preserves hidden-free validity relative to the same final pair set by the deletion lemma in [Hereditary marked bridges](hereditary_marked_bridges.md). Thus any subset of the boundary star can be placed.

## 4. A matching spacing-exponent obstruction

Take any positive odd integer \(z\), and put
\[
 p=(z+1)^2,\quad U=p+1,\quad a=zU,\quad
 h=a+3,\quad i=(a-1)/2,\quad X=pi.
\]
Then \(p\) is divisible by four and \(a\) is odd. The final two extra points of (1) are
\[
 A=(X,a+1),\qquad C=(X+p,a+3).
\]
Two baseline points are
\[
 B=(X+p+1,1),\qquad D_0=(X+2z+1,1).
\]
The side pair \(B,A\) and diagonal pair \(D_0,C\) have vectors
\[
 (-U,a),\qquad (z^2,a+2),
\]
of equal squared length. Translation of the side pair by \((z,1)\) is perpendicular to its side, and gives the shared white pair
\[
 W=(X+p+1+z,2),\qquad Z=(X+z,a+2).
\]
Indeed \((-U,a)\cdot(z,1)=0\), because \(a=zU\). The common midpoint and equal-length identities follow from \(p=(z+1)^2\).

Both shared corners are inside the vertical strip and are white: their column residues modulo \(p\) are \(z+1,z\), neither zero, and their rows exceed one. Therefore the two distinct rectangles have the same presentation.

This collision uses the right constant tail, with \(W\) lying \(z+1\) columns beyond the last double. If a collision entirely inside the bare double block is desired, increase the height from \(a+3\) to \(a+5\), adding one further extra point; then the same white pair lies before the new last double.

The obstruction height is
\[
 h=z\bigl((z+1)^2+1\bigr)+3=\Theta(p^{3/2}).
\]
Thus no safety guarantee valid for every admissible \(p\) can replace the \(p^{3/2}\) height scale by a uniformly larger power. The example does not exclude a better spacing chosen from a special arithmetic subsequence, and it is not a lower bound for other star constructions or for the full equality threshold.

## 5. Review status

The divisibility step, the lower bound (10), and the explicit mixed certificate have been independently checked. This is an analytical theorem; it does not rely on a search for a filled board.
