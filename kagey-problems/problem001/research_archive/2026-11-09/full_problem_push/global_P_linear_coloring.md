# A linear palette for the global vertical-rival graph

9 November 2026. This note proves that the global vertical-rival graph in
`global_P_coloring_progress.md` has chromatic number \(O(h)\). Consequently,
the placement \(x(a,b)=2(a-1)+P c(a,b)\) can exclude all vertical rivals in
width \(O(h^2)\). The conclusion concerns only vertical rivals. It does not
assert the remaining identifying conditions for this placement.

## 1. The graph and its arithmetic parameters

Put \(H=h-1\). Its vertices are pairs \(v=(a,b)\), with \(a\) an odd row and
\(b\) an even row in \([1,h]\). Vertices with the same odd row form a clique.
For a vertex \(v=(a,b)\), define its blocker set
\[
B(v)=\{s\in[1,h]:s\text{ odd},\ s\ne a,
       \ (s-b)^2+4(s-a)^2=L^2\text{ for some integer }1\le L\le H\}.
\tag{1}
\]
Join \(v\) to every vertex whose odd row belongs to \(B(v)\), and take the
undirected union of these edges. This graph can contain extra edges: (1)
does not require the vertical white rows to remain inside the strip.
Every actual vertical-rival conflict is an edge of this graph.

For an odd offset \(u\in[-H,H]\), put
\[
D(u)=\#\{d\in2\mathbb Z\setminus\{0\}:
          (u+d)^2+4d^2=L^2,\quad 1\le L\le H\}.
\tag{2}
\]
Then \(|B(a,b)|\le D(a-b)\). Three bounds drive the proof:
\[
\sum_{u\text{ odd},\ |u|\le H}D(u)=O(h\log h),
\qquad \max_uD(u)=h^{o(1)},
\tag{3}
\]
and, for every pair of distinct odd rows \(a,s\),
\[
\#\{b\in[1,h]:b\text{ even},\ s\in B(a,b)\}=h^{o(1)}.
\tag{4}
\]
All asymptotic bounds here are uniform in the indicated rows and offsets.

### Total offset mass

Each solution of (2) gives an integer right triangle with legs
\(2|d|,|u+d|\) and hypotenuse at most \(H\). The first leg is even and the
second odd. Each such triangle permits at most four sign choices that
recover \(d,u\). The primitive Pythagorean parameterization therefore gives
\[
\sum_uD(u)\le4T_H,
\quad
T_H\le\sum_{r=2}^{\lfloor\sqrt H\rfloor}
          \sum_{s=1}^{r-1}\left\lfloor\frac{H}{r^2+s^2}\right\rfloor
       =O(H\log H).
\tag{5}
\]
Dropping coprimality and parity restrictions only increases the sum.

### Uniform bounds on a single offset and a single blocker

Completing the square in (2) gives
\[
X^2-5Y^2=-4u^2,
\qquad X=5d+u,\quad Y=L.
\tag{6}
\]
Here \(|X|\le6h\) and \(1\le Y\le h\). Let \(g=\gcd(X,Y)\). Then
\(g\mid2|u|\), and the primitive pair \(X_0=X/g,Y_0=Y/g\) has norm
\(N=-4u^2/g^2\). Since \(\gcd(X_0,Y_0)=1\), one has
\(\gcd(Y_0,|N|)=1\). Thus
\[
r=X_0Y_0^{-1}\pmod {|N|},\qquad r^2\equiv5\pmod {|N|}.
\]
There are at most \(4\tau(|N|)\) such roots. This follows prime by prime:
there are at most two roots at an odd prime other than five, at most one
at five, and at most four at two. Modulus one is harmless.

Two primitive solutions with the same root belong to the same integer
norm-one unit orbit. Indeed, in the quotient
\[
\frac{X_0+Y_0\sqrt5}{X'_0+Y'_0\sqrt5}
=\frac{X_0X'_0-5Y_0Y'_0}{N}
 +\frac{Y_0X'_0-X_0Y'_0}{N}\sqrt5,
\]
both coefficients are integers by their common congruence modulo \(|N|\).
The quotient has norm one. If its real value \(\eta=x+y\sqrt5\) exceeds
one, then its conjugate equals \(1/\eta\). Consequently \(x,y\) are positive
integers, and \(\eta\ge1+\sqrt5>2\). Thus distinct positive solutions in one
root class, ordered by their real values, grow by a factor greater than
two. No classification of Pell units is needed.

Because \(N<0\) and \(Y_0>0\), the real number
\(\alpha=X_0+Y_0\sqrt5\) is positive. Its size lies between \(1/(9h)\) and
\(9h\). Each root class therefore contributes \(O(\log h)\) solutions.
Summing over \(g\mid2|u|\), and using
\(\tau(4u^2)\le\tau(2|u|)^2\), proves
\[
D(u)\le C\tau(2|u|)^3\log h=h^{o(1)}.
\tag{7}
\]
For completeness, the uniform subpolynomial divisor bound follows by
splitting prime factors at \(\sqrt{\log h}\). For integers of size
\(O(h^2)\), the small primes contribute
\(O(\sqrt{\log h}\log\log h)\) to \(\log\tau\). The total exponent at
larger primes is \(O(\log h/\log\log h)\), and \(e+1\le2^e\) handles
their contribution. Both bounds are \(o(\log h)\).

For (4), fix \(a,s\). Any permitted \(b\) gives the factorization
\[
\bigl(L-(s-b)\bigr)\bigl(L+(s-b)\bigr)=4(s-a)^2.
\tag{8}
\]
Each factor pair determines \(L,b\), so the number of choices is at most
\(2\tau(4(s-a)^2)=h^{o(1)}\).

## 2. A palette lemma for one offset band

Let \(U\subseteq[-H,H]\cap(2\mathbb Z+1)\) be a set of \(N\) offsets.
Assume
\[
D(u)\le2R\log h\quad(u\in U),\qquad R\ge1.
\tag{9}
\]
Restrict the graph to vertices with \(a-b\in U\). Every odd-row clique now
has at most \(N\) vertices.

**Lemma.** If \(N\ge h^{1/3}\), then this induced graph is colorable with
\(\lceil4096RN\rceil\) colors, for all sufficiently large \(h\).

**Proof.** Independently for each of these \(K=\lceil4096RN\rceil\) colors,
sample a subset \(S\) of the odd rows. Include each row independently with
probability
\[
p=\frac1{64R}.
\]
A vertex \(v=(a,b)\) is eligible for this color if \(a\in S\) and
\(B(v)\cap S=\varnothing\). Two eligible vertices in different odd-row
cliques cannot be adjacent. It remains to match each odd-row clique
injectively to its eligible colors.

Since its own row is not a blocker, conditioning on \(a\in S\) leaves all
blocker choices independent. By (9), a vertex then has probability at least
\[
(1-p)^{|B(v)|}\ge\exp(-2p|B(v)|)\ge h^{-1/16}
\tag{10}
\]
of being eligible. Its expected number of eligible colors is therefore at
least
\[
Kp h^{-1/16}\ge64N h^{-1/16}\ge64h^{13/48}.
\tag{11}
\]
A binomial lower-tail bound shows that every vertex has at least
\(\lceil h^{1/4}\rceil\) eligible colors with probability tending to one.
The union bound has at most \(h^2\) vertices. This proves Hall's condition
for every subset of a row clique of size at most \(\lceil h^{1/4}\rceil\).

Consider a larger subset \(T\) within one fixed odd-row clique. By (3) and
(4), its blocker sets have maximum size \(h^{o(1)}\), and any particular
row belongs to at most \(h^{o(1)}\) of these sets. Their intersection graph
has maximum degree at most \(h^{o(1)}\). In particular, for sufficiently
large \(h\), greedy selection gives at least
\[
\frac{|T|}{h^{1/32}}\ge h^{7/32}
\]
pairwise disjoint blocker sets. The displayed lower bound can be decreased
by a factor two to absorb rounding. Empty blocker sets cause no problem:
if one exists, eligibility conditional on \(a\in S\) is certain.

The avoidance events for the selected nonempty, disjoint sets are
independent. By (10), conditional on \(a\in S\), the probability that no
vertex of \(T\) is eligible is at most
\[
\exp\bigl(-\tfrac12 h^{5/32}\bigr).
\tag{12}
\]
Thus each color belongs to the neighborhood of \(T\) with probability at
least \(p/2\), for sufficiently large \(h\). The choices for different
colors are independent. The expected neighborhood size is at least
\[
Kp/2\ge32N.
\]
Another binomial lower-tail bound gives
\[
\Pr\bigl(|\Gamma(T)|<N\bigr)\le e^{-4N}.
\tag{13}
\]
There are at most \(h\,2^N\) relevant choices of a row and its subset \(T\).
Their combined failure probability is at most
\(h\exp(-(4-\log2)N)=o(1)\), since \(N\ge h^{1/3}\).

With positive probability, all these Hall conditions hold simultaneously.
Choose a matching separately for each odd-row clique. Eligible vertices
assigned the same color are pairwise nonadjacent across cliques, and the
matching handles edges within each clique. This proves the lemma.

## 3. Summing the bands

Use a low band \(D(u)\le\log h\), with \(R=1\). For every integer \(j\ge0\),
use another band
\[
2^j\log h<D(u)\le2^{j+1}\log h,
\qquad R=2^j.
\]
Let \(N_R\) denote each band's number of offsets, distinguishing the low
band from the first high band. Equation (3) gives
\[
\sum_{\text{bands}}R N_R=O(h).
\tag{14}
\]
Indeed, the low band contains \(O(h)\) offsets. Every high-band term is at
most its offset mass divided by \(\log h\).

Apply the palette lemma to every band with \(N_R\ge h^{1/3}\), using
disjoint palettes for different bands. By (14), these bands use \(O(h)\)
colors in total.

For a small band, orient every non-clique conflict from its source odd
point toward the target even point. Fix a source odd row \(s\). For each
target offset \(u=a-b\in U\), every possible target corresponds to a
nonzero even \(d=s-a\) counted by \(D(u)\). Hence its outdegree to the
band is at most
\[
\sum_{u\in U}D(u)\le2R N_R\log h.
\]
Orient same-row clique edges arbitrarily. They add at most \(N_R-1\) to
the outdegree. The resulting orientation bounds every induced subgraph's
average degree, so greedy degeneracy coloring uses \(O(RN_R\log h)\)
colors.

By (7), the number of bands and their largest \(R\) are both \(h^{o(1)}\).
Since each small band's \(N_R<h^{1/3}\), their total cost is
\[
h^{1/3+o(1)}=o(h).
\tag{15}
\]
Combining (14) and (15) proves
\[
\boxed{\chi(G_h)=O(h).}
\tag{16}
\]
The argument treats sufficiently large \(h\). Enlarging the absolute
constant covers the finitely many remaining heights.

## 4. Consequence and limits

Choose an even integer \(P>3(h-1)\), and place the label \((a,b)\) at
\[
x(a,b)=2(a-1)+P c(a,b).
\]
The same-odd-row clique rule makes columns distinct within a color block.
Columns in different blocks have horizontal separation at least
\(P-2(h-1)>h-1\). They cannot form an in-strip vertical rival. Within a
block, (16) excludes every such rival. Since the number of blocks is
\(O(h)\), the total width is \(O(h^2)\).

This removes the logarithmic loss for the global P-only problem. It does
not establish a complete quadratic identifying construction: changing the
block coordinate to an arbitrary color can introduce other three-, four-,
or six-point rectangle obstructions. Those conditions require a separate
argument.

## 5. Review status

Two independent reviews checked the primitive Pell orbit argument, the uniform
arithmetic bounds, both Hall estimates, the small-band orientation, and the
sum of the band costs. No proof gap was found. The restriction to the
vertical-rival graph is part of the theorem.
