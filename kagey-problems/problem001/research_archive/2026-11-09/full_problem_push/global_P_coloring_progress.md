# Global coloring of the vertical-rival scaffold

9 November 2026. Consider vertices \((a,b)\), where \(a\) is an odd row and
\(b\) is an even row in \(1,\ldots,h\). Give all vertices with the same
\(a\) different colors. A color \(c(a,b)\) places the edge at
\[
x(a,b)=2(a-1)+P c(a,b).
\tag{1}
\]
Within one color block, two vertices \((a,b),(a',b')\) conflict when either
\[
(a-b')^2+4(a-a')^2=L^2
\tag{2}
\]
has an integral vertical alternative diagonal inside the strip, or the
analogous condition with the two vertices reversed holds. In (2), the white
rows are \((a+b'\pm L)/2\). This note concerns only these vertical rivals.

The following results are proved:

* The color graph has chromatic number \(O(h\log h)\).
* Every fixed affine color formula, including a fixed modular refinement,
  fails at sufficiently large height.
* A palette of \(\lfloor h/2\rfloor+O(1)\) colors cannot work uniformly.

The desired bound \(O(h)\) remains open here. Even that bound would address
only the vertical-rival part of (1), not all the other rectangle laws.

## 1. An elementary logarithmic upper bound

Put \(H=h-1\) and \(n=\lfloor h/2\rfloor\). For each conflict witnessed by
(2), orient the edge from the vertex whose odd point is the source. Fix a
source odd row \(a\). Its targets \((a',b')\) have positive integer triangle
legs
\[
X=2|a-a'|,\qquad Y=|a-b'|,
\]
and hypotenuse \(L\le H\), since the white vertical diagonal fits in the
strip. A triangle \((X,Y,L)\) allows at most four choices of the signs
recovering \(a',b'\). This bound is independent of the source's even mate.

The number of integer right triangles with hypotenuse at most \(H\) is at
most
\[
T_H=\sum_{u=2}^{\lfloor\sqrt H\rfloor}
     \sum_{v=1}^{u-1}
     \left\lfloor\frac{H}{u^2+v^2}\right\rfloor.
\tag{3}
\]
Indeed, the primitive parameterization supplies integers \(u>v>0\) and a
positive scale factor. Dropping coprimality and parity restrictions only
increases (3). Moreover,
\[
T_H\le H\sum_{u=2}^{\lfloor\sqrt H\rfloor}\frac{u-1}{u^2}
\le\tfrac12H\log H.
\]
Choose one witnessing orientation when both exist, and orient each
same-odd-row clique arbitrarily. The resulting maximum outdegree is at most
\(4T_H+n-1\). Every induced subgraph consequently has average degree at
most twice this number, so greedy degeneracy coloring gives
\[
\chi\le8T_H+2n-1=O(h\log h).
\tag{4}
\]

If \(P\) is even and \(P>3(h-1)\), points in different color blocks have
horizontal separation exceeding \(h-1\), so they cannot supply an in-strip
vertical rival. Thus (4) gives a vertical-rival-free scaffold of width
\(O(h^2\log h)\). It is not a proof that this scaffold is identifying.

## 2. The entire fixed affine family fails

Suppose a proposed color is determined by
\[
\alpha a+\beta b,
\]
where \(\alpha,\beta\) are fixed integers and \(\beta\ne0\). Allow any
additional fixed refinement depending on \(a,b\) modulo \(M\).

Choose a sufficiently large positive even \(d\), divisible by
\(2|\beta|M\), and an odd \(a\) sufficiently large. Set
\[
a'=a-d,\qquad b'=a-d^2+1,\qquad
b=b'-\alpha d/\beta.
\tag{5}
\]
Both odd coordinates are odd, both even coordinates are even, and all four
rows can be made positive and placed in a sufficiently high strip. The two
vertices have the same affine value. They also have the same coordinates
modulo \(M\).

The diagonal from the source row \(a\) to target row \(b'\) has legs
\[
2d,\qquad d^2-1
\]
and hypotenuse \(d^2+1\). Its vertical white rows are
\[
a-d^2,\qquad a+1.
\]
These lie in the strip after the same choice of \(a,h\). Therefore the two
vertices conflict despite receiving the same color.

One completely explicit choice is
\[
d=2|\beta|M(|\alpha|+|\beta|+2),\quad
q=\alpha d/\beta,\quad a=d^2+2|q|+1,\quad h=a+1.
\]
It satisfies every positivity and containment condition. If \(\beta=0\),
the rule already fails on a same-odd-row clique. Thus no fixed affine rule,
even with bounded modular information appended, supplies the desired
coloring.

For example, \(b-a\) assigns the same color to \((11,12)\) and \((5,6)\),
which conflict at height fifteen. The sum \(a+b\) identifies \((9,4)\) and
\((7,6)\), which conflict at height ten.

## 3. More than a Latin-square palette is necessary

For \(h\ge10\), every vertex in the \(n\)-vertex clique with odd row nine
is adjacent to \((7,6)\). The witnessing diagonal has legs four and three
and white rows five and ten. Hence \(\chi\ge n+1\).

In fact the additive excess over \(n\) is unbounded. Let \(q\) be a product
of \(t\) distinct odd primes, and put
\[
h=8q^2+6,\qquad a=4q^2+3,\qquad a'=a-2q.
\]
For every positive divisor \(u\mid q^2\), put \(v=4q^2/u\). Then
\[
(4q)^2+(v-u)^2=(v+u)^2.
\]
The \(3^t\) positive values \(|v-u|\) are distinct. Their parity is odd,
since \(u\) is odd and \(v\) is even. Each of the \(2\cdot3^t\) even rows
\[
b'=a\pm|v-u|
\]
belongs to the strip. The corresponding vertical white rows are among
\(a-u,a+v,a-v,a+u\), all also inside the strip.

Thus all these vertices \((a',b')\) are adjacent to the entire odd-row-\(a\)
clique. They also form a clique themselves, since their odd row is the same.
Therefore
\[
\chi\ge n+2\cdot3^t.
\tag{6}
\]
This rules out \(n+O(1)\) colors, but does not rule out \(Cn\) for a fixed
constant \(C>1\).

## 4. The structural issue left by these bounds

For a vertex \((a,b)\), let \(B(a,b)\) be the set of odd rows \(a'\) whose
odd point forms an in-strip vertical rival with its even point. The vertex
then conflicts with every vertex in each odd-row clique indexed by
\(B(a,b)\). A color class is a partial transversal of the odd-row cliques,
and its selected row set must avoid every member's blocker set.

This is more structured than an arbitrary sparse graph, but the elementary
orientation bound only gives (4). The same-odd-row cliques and the joined
cliques in Section 3 also prevent treating the graph as triangle-free.
Neither an \(O(h)\) coloring nor a superlinear chromatic lower bound is
established by these arguments.
