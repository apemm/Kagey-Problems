# Quadratic parity phases in a nonparity row partition

9 November 2026. Independent review checked the quadratic identity, anchor geometry, and cross-pair count. The leading entropy \(h/2\) is not specific to the ordinary parity partition. An integer quadratic identity gives a second balanced partition at every height, and dense buffers capture its natural phases in its boundary component.

Put
\[
 q(n)=\frac{n(n-1)}2,\qquad c(n)=q(n)\pmod2.
\]
The row colors are \(c(1),c(2),c(3),c(4),\ldots=0,1,1,0,\ldots\), with period four. Every initial interval has color-class sizes differing by at most one. Let \(\pi_q\) be this balanced partition and let \(C_{\partial,q}\) be its primitive boundary sea component, containing the constant row-1 and row-\(h\) states. Write \(\lambda_{\partial,q}\) for its Perron root.

For \(\alpha,\beta\in\{0,1\}\), consider the column law
\[
 q(w_x)+q(x)+\alpha x=\beta\pmod2.
\tag{1}
\]
These four laws are the four shifts of a period-four class pattern. Let \(r_q(h)\) be the entropy of the union of their valid sea languages.

**Theorem.** For all sufficiently large \(h\),
\[
 \lambda_{\partial,q}(h)>r_q(h)
 \ge \left\lfloor\frac h2\right\rfloor
       \exp\bigl(-O_\varepsilon(h^{-1+\varepsilon})\bigr).
\tag{2}
\]
In particular, the boundary component of this nonparity partition has entropy \(h/2-o(h)\). This is not a comparison with the ordinary parity component \(\lambda_*(h)\).

## 1. Why the quadratic law removes the large obstruction families

Define
\[
 Q_\alpha(x,y)=q(x)+q(y)+\alpha x.
\]
For arbitrary integer vectors \(u,v\),
\[
 Q_\alpha(P)+Q_\alpha(P+u+v)
 -Q_\alpha(P+u)-Q_\alpha(P+v)=u\cdot v.
\tag{3}
\]
Thus the left side is zero on the four corners of every lattice rectangle.

If three black corners satisfy (1), the fourth corner also has \(Q_\alpha=\beta\pmod2\). The selected black row in its column has the same \(c\)-color, so a singleton presentation has no \(\pi_q\)-axis rival.

If the black diagonal of a tilted rectangle satisfies (1) at both endpoints, (3) says that the two white corners have equal \(Q_\alpha\)-values modulo two. When the white pair is vertical, its columns agree, so its row colors \(c\) agree. It therefore has no vertical \(\pi_q\)-axis rival.

The remaining forbidden positive supports have four or six black cells, exactly as in the affine-parity argument. Hidden rectangles are included, common corners remain uncolored, and incompatible requests for different black rows in one column are discarded. Their normalized global counts are
\[
 B_4(h)=O_\varepsilon(h^{3+\varepsilon}),
 \qquad B_6(h)=O_\varepsilon(h^{5+\varepsilon}).
\tag{4}
\]
At each column, (1) allows at least \(\lfloor h/2\rfloor\) rows. The same variable local lemma consequently gives the lower bound for \(r_q\) in (2). The identity (3), rather than ordinary row parity, is what removes singleton and vertical rivals.

## 2. A universal adjacent-row boundary anchor

The following observation does not depend on the row partition.

**Anchor lemma.** A word on rows \(\{1,2\}\) in which no two row-2 letters are two columns apart is a valid sea for every pair set \(F\). In particular, the periodic word
\[
 \ldots112211221122\ldots
\tag{5}
\]
and each of its phases lie in every boundary component.

The adjacent-row geometric proof already excludes hidden rectangles, collisions between two tilted rectangles, horizontal rivals, and oblique rivals independently of \(F\). A tilted rectangle with three black adjacent-row corners is a unit diamond. The only in-strip missing corner not automatically excluded by the lower boundary is row 3, with black row-2 corners two columns apart. The stated condition prevents it.

For a vertical white pair, a black diagonal using both rows would require a nonzero integer solution of \(x^2+1=z^2\), which is impossible. A horizontal black diagonal in row 1 has no vertical alternative inside the strip. In row 2, the only possible in-strip alternative has white rows 1 and 3 and requires the same two row-2 points two columns apart. This is also prevented.

A run \(22\), separated from every other such run by at least two row-1 letters, has no prohibited row-2 pair. Hence the periodic word (5) can be entered from a constant row-1 tail and left for a constant row-1 tail, by cutting between a \(22\) block and a \(11\) block. Every phase reaches these cuts along its periodic orbit. This proves membership in the boundary component.

For a fixed law (1), use the anchor
\[
 a_x=1+\bigl(q(x)+\alpha x+\beta\bmod2\bigr)\in\{1,2\}.
\tag{6}
\]
Its period-four word is a phase of (5), and \(c(a_x)=q(x)+\alpha x+\beta\), as required.

## 3. Buffers preserving the quadratic row color

Use buffer alphabets
\[
 P_x=\{r:7\le r\le h,\ c(r)=c(a_x)\}.
\tag{7}
\]
They have \(h/2+O(1)\) rows and preserve the \(c\)-color of \(a_x\). No residue or primality condition beyond the required row color is needed. A preliminary proof used the smaller pool \(a_x+8\bmod16\); counting its formerly excluded degenerate conics gives the stronger version below.

Take two buffers of length \(L=2W_h\), an arbitrary-length core obeying (1), and the anchor tails from (6). All free variables are uniform on their respective alphabets. A support meeting a tail sees only its adjacent buffer, since its span is at most \(L\).

The pinned-support counts from [checkerboard_bridge_counting.md](checkerboard_bridge_counting.md) use only that pins lie in rows 1 and 2, that free points are above them, and that all pins lie on one side of all free points. Those geometric arguments apply here. In particular, hidden and same-pair mixed supports with two pins have \(O_\varepsilon(h^{3/2+\varepsilon})\) possibilities. Three-pin mixed supports and horizontal supports with two pins are impossible. The six-cell counts are unchanged; in this anchor, a three-pin right triangle is already impossible because (5) avoids the necessary unit-diamond pattern.

The cross-pair mixed family needs a new arithmetic check, given next.

## 4. Cross-pair pins without an affine column-parity assumption

Translate the side's pinned point to \(A=(0,a)\), where \(a\in\{1,2\}\), and write
\[
 B=(x,a+y),\quad C=(d,a+\delta),\quad
 D=(d+z,a+\delta+v),
\]
where \(A,C\) are pins, \(B,D\) are free, \(x,z>0\), \(y,v\ge5\), and \(\delta\in\{-1,0,1\}\). Both free points lie strictly to the right of both pins.

Here \(AB\) is the black side in one rectangle and \(CD\) is the black diagonal in the other. Put
\[
 \Delta=\frac{v-y+2\delta}{2}.
\]
The integral perpendicular connector and equal-norm conditions imply
\[
 x\mid y\Delta,\qquad
 z^2=x^2-4(\Delta-\delta)(y+\Delta-\delta),
 \qquad
 d=\frac{x-z}{2}-\frac{y\Delta}{x}.
\tag{8}
\]
The lower common white corner has row \(a+\Delta\). Hence
\[
 \Delta\ge1-a\ge-1.
\tag{9}
\]
Also \(\Delta=0\) would make both connector components zero, which is degenerate. Thus \(\Delta>0\), or \(\Delta=-1\) with \(a=2\).

Write
\[
 x=gX,\quad y=gY,\quad (X,Y)=1,\quad \Delta=XT.
\]
Equation (8) becomes
\[
 z^2=A_0X^2+B_0X+C_0,
\tag{10}
\]
where
\[
 A_0=g^2-4T^2,\quad
 B_0=4T(2\delta-gY),\quad
 C_0=4\delta gY-4\delta^2.
\]
Its discriminant is
\[
 B_0^2-4A_0C_0
 =16g^2(T^2Y^2-\delta gY+\delta^2).
\tag{11}
\]

Split at \(X=\sqrt h\). For \(X\le\sqrt h\), there are \(O(h^{3/2}\log h)\) triples \((g,Y,X)\), and the equal-norm circle has \(h^{o(1)}\) representations. This already includes \(\Delta=-1\), since \(XT=-1\) forces \(X=1\).

For \(X>\sqrt h\), (9) forces \(T>0\), and \(XT=\Delta=O(h)\) gives \(T=O(\sqrt h)\). There are \(O(h^{3/2}\log h)\) triples \((g,Y,T)\). The two possible conic degeneracies are handled as follows.

* **Zero leading coefficient.** Then \(x=2\Delta\), and
  \[
  z^2=-2xy+4\delta(x+y)-4\delta^2.
  \]
  For \(\delta\le0\) this is negative. For \(\delta=1\), the formula is
  \[
  z^2=4-2(x-2)(y-2).
  \]
  Because \(x=2\Delta\ge2\) and \(y\ge5\), its only possible positive case is \(x=z=2\). But then \(d=-y/2\), and the free point \(D\) has column \(2-y/2<0\), to the left of pin \(A\). This violates the one-sided order.
* **Zero discriminant.** Since \(T\ne0\), only \(\delta=1\) is possible. Reducing the vanishing factor in (11) modulo \(Y\) forces \(Y=1\), and then \(g=T^2+1\). There are only \(T\le\sqrt h\), and for each such \(T\), the bound \(XT=\Delta\le h\) leaves at most \(h/T\) choices of \(X\). Each tuple gives at most two \(z\)'s and one pin gap \(d\). The entire degenerate family therefore has only \(O(h\log h)\) supports.

For the remaining triples, the uniform conic lemma in [checkerboard_flip_conic_bound.md](checkerboard_flip_conic_bound.md) gives \(h^{o(1)}\) bounded-height integer solutions of (10). Section 7 of that note records this unrestricted low-pin version separately.

Consequently the entire cross-pair family has
\[
 O_\varepsilon(h^{3/2+\varepsilon})
\tag{12}
\]
normalized geometries. This argument does not require that column parity determine the pin row.

## 5. Conditional capture and strictness

The complete four/six pinned table is therefore the same as in the dense-residue capture theorem:
\[
\begin{array}{c|c|c}
\text{support size}&\text{number of pins}&\text{geometry count}\\ \hline
4&0&O_\varepsilon(h^{3+\varepsilon})\\
4&1&O_\varepsilon(h^{2+\varepsilon})\\
4&2&O_\varepsilon(h^{3/2+\varepsilon})\\
6&0&O_\varepsilon(h^{5+\varepsilon})\\
6&1&O_\varepsilon(h^{4+\varepsilon})\\
6&2&O_\varepsilon(h^{3+\varepsilon})\\
6&3&O_\varepsilon(h^{2+\varepsilon})\\
6&4&O_\varepsilon(h^{1+\varepsilon}).
\end{array}
\]
Each free alphabet has size \(\gg h\), so the incident local-lemma pressure is \(O_\varepsilon(h^{-1/2+\varepsilon})\). Every noncore event uses a buffer variable. Ordering all core events first in the conditional local lemma gives a positive factor, depending only on \(h\), between the number of valid cores and the number having buffered extensions.

The endpoints are phases of the universal anchor (5), hence lie in \(C_{\partial,q}\). Discarding the first \(L\) core letters shows that the induced subgraph of \(C_{\partial,q}\) consisting of histories obeying one of the four laws (1) has full entropy \(r_q(h)\).

This induced subgraph is proper: the constant row-1 history satisfies none of the period-four laws when \(L\ge4\). Strict Perron comparison for a proper principal submatrix of an irreducible matrix gives \(\lambda_{\partial,q}>r_q\), proving (2).

## 6. Consequence for the remaining dominance question

The ordinary parity partition is not the only balanced partition with a boundary component of entropy asymptotic to \(h/2\). Any argument separating partitions must distinguish these quadratic phases at lower order, or prove a suitable exact comparison.

The existence of the quadratic phase does not disprove ordinary parity dominance. It shows that single-class container templates can carry a quadratic column law, so reducing all near-maximal balanced-partition templates to ordinary affine parity would be false.

