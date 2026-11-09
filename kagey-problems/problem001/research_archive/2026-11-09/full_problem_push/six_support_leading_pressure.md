# Leading six-cell support pressure in protected phases

9 November 2026. This note computes a leading geometric obstruction weight for the ordinary constant-parity phase O, the ordinary checkerboard phase C, and the quadratic phase Q from [phase_local_densities.md](phase_local_densities.md). It is not an entropy expansion.

For each phase, choose each column's black row independently and uniformly from its allowed class. Let \(\mu_{6,X}(h)\) be the mean number per column of distinct minimal six-cell collision events, where two tilted rectangles share one missing corner. Minimal means that the six required black cells contain no smaller forbidden positive support. Then
\[
\begin{aligned}
 \mu_{6,{\rm O}}(h)&\sim
       \frac{45}{\pi^4}\frac{(\log h)^4}{h},\\
 \mu_{6,{\rm C}}(h)&\sim
       \frac{324}{5\pi^4}\frac{(\log h)^4}{h},\\
 \mu_{6,{\rm Q}}(h)&\sim
       \frac{144}{5\pi^4}\frac{(\log h)^4}{h}.
\end{aligned}
\tag{1}
\]
The ratio Q/O is \(16/25\). Independent review checked the fixed-corner degree, constants, geometric multiplicity estimates, and lower-order exclusions.

## 1. Rectangles in the infinite strip

Every tilted rectangle has a unique lowest corner and adjacent vectors
\[
 k(a,b),\qquad l(-b,a),
 \qquad a,b,k,l\ge1,\quad(a,b)=1.
\]
Its vertical span is \(kb+la\). Consequently the number \(R_h\) of tilted rectangles per horizontal translation is
\[
 R_h=\sum_{(a,b)=1}\ \sum_{k,l\ge1}(h-kb-la)_+.
\tag{2}
\]
For fixed \(a,b\le h\), a monotone two-dimensional Riemann sum gives
\[
 \sum_{k,l\ge1}(h-kb-la)_+
 =\frac{h^3}{6ab}
   +O\left(\frac{h^2}{a}+\frac{h^2}{b}+h\right).
\tag{3}
\]
The error remains valid when \(a+b\ge h\), since it then bounds the displayed main term. Summing the error over \(a,b\le h\) gives \(O(h^3\log h)\). Möbius inversion gives
\[
 \sum_{\substack{a,b\le h\\(a,b)=1}}\frac1{ab}
 =\frac{(\log h)^2}{\zeta(2)}+O(\log h).
\tag{4}
\]
Hence
\[
 R_h\sim\frac{h^3(\log h)^2}{6\zeta(2)}
       =\frac{h^3(\log h)^2}{\pi^2}.
\tag{5}
\]

A repeated corner column requires \(ka=lb\), thus \(k=bt,l=at\) and vertical span \(t(a^2+b^2)\). These rectangles contribute only \(O(h^2\log h)\) to (2), so they do not affect (5).

The logarithm here is squared because the strip has no horizontal-width restriction. This differs from the \(h\times h\) square used in the container theorem.

## 2. The degree of a fixed corner

Fix a point \(W\) at row \(r\), and put \(H_-=r-1,H_+=h-r\). For a fixed primitive direction, W can be the lowest corner, highest corner, or either of the two intermediate corners. The leading count is
\[
 \frac{H_+^2+H_-^2}{2ab}
 +\frac{2H_+H_-}{ab}.
\]
Floor and residue-class errors sum to \(O(h^2\log h)\), uniformly in \(r\). Thus the number \(D_h(r)\) of tilted rectangles through W, with four distinct columns, satisfies
\[
 D_h(r)=\frac{h^2(\log h)^2}{\zeta(2)}
       f(r/h)+O(h^2\log h),
 \qquad f(t)=\frac12+t-t^2.
\tag{6}
\]
The repeated-column rectangles contribute only \(O(h\log h)\) to the degree of W.

For the three primitive parity types \((1,1),(1,0),(0,1)\), the harmonic coprime sum in (4) has equal leading coefficient \(1/[3\zeta(2)]\). For example, restricting both variables to odd integers yields
\[
 \frac14(\log h)^2
 \sum_{d\ {\rm odd}}\frac{\mu(d)}{d^2}
 =\frac{(\log h)^2}{3\zeta(2)}.
\]
The other two types are equal by symmetry and exhaust the remainder.

## 3. Phase-compatible degrees

Suppose W itself lies in phase X. The exact residue table in [phase_local_densities.md](phase_local_densities.md), averaged over the side scales modulo four, gives the conditional rectangle factors
\[
\begin{array}{c|ccc}
\text{primitive type}&{\rm O}&{\rm C}&{\rm Q}\\ \hline
(1,1)&1/4&1&1/2\\
(1,0)\text{ or }(0,1)&1/2&1/4&1/4.
\end{array}
\]
For Q, the scale-averaged values are independent of \(W\bmod2\). The same table applies to all four corner roles. Averaging the primitive types therefore gives
\[
 c_{\rm O}=5/12,\qquad c_{\rm C}=1/2,\qquad c_{\rm Q}=1/3.
\tag{7}
\]
Let \(D_{h,X}(W)\) count rectangles through W whose four corners all lie in phase X. Partitioning each scale sum into its residue classes modulo four gives
\[
 D_{h,X}(W)
 =c_X\frac{h^2(\log h)^2}{\zeta(2)}f(r/h)
   +O(h^2\log h)
\tag{8}
\]
when W is in the phase, and zero otherwise. The error is uniform in W. There is no loss of logarithmic order when imposing the fixed congruences.

## 4. Unordered pairs and their six distinct black columns

Start with unordered pairs of distinct rectangles through W whose four corners lie in phase X. Their number is
\[
 \frac12D_{h,X}(W)^2+O(D_{h,X}(W)).
\]

A six-cell event can also use a rectangle whose missing corner shares a column with one of its black corners. Such a rectangle has repeated corner columns and was omitted from \(D_{h,X}\). There are only \(O(h\log h)\) of them through W, so pairing them with arbitrary rectangles contributes \(O(h^4(\log h)^3)\) per horizontal translation. This is lower order than the count in (11).

Pairs sharing another corner column have lower order. Fix the first rectangle and one of its three non-W columns. A second rectangle through W with a corner in that column has at most \(O(h^2)\) possibilities: choose that corner's row in \(h\) ways; two specified rectangle corners lie on a side or diagonal, and admit \(O(h)\) completions in the strip. A perpendicular line contains at most \(h\) strip lattice points because its vertical component is nonzero, and a circle meets each row at most twice. Hence the number of excluded pairs is
\[
 O\bigl(h^2D_h(r)\bigr)=O(h^4(\log h)^2)
\tag{9}
\]
per W, or \(O(h^5(\log h)^2)\) per horizontal translation.

When two specified corners share a column, a vertical-side completion would be axis-aligned and is excluded from the tilted family. The diagonal-circle case still has \(O(h)\) choices. This convention is used in every two-corner completion bound below.

This removes pairs sharing an additional point, as well as pairs requesting different black rows in one column. Every remaining pair gives six distinct required black cells in six distinct columns.

## 5. Repeated descriptions and smaller supports

Two different descriptions of the same six-cell support must use a new black right triangle that takes points from both original triples. Otherwise the two original triples, their right angles, and their common completion are unchanged.

For a fixed first rectangle and a mixed right triangle with two of its black points, the third point lies on one of constantly many perpendicular lines or Thales circles. Each such locus contains \(O(h)\) strip points: the two fixed black points have distinct columns, so the perpendicular lines are not horizontal. Through W and this third point there are \(O(h)\) second rectangles. Thus pairs admitting a new mixed right triangle again number at most
\[
 O(h^4(\log h)^2)
\]
per W. All multiplicities beyond the original unordered pair therefore affect only \(O(h^5(\log h)^2)\) supports per translation.

A six-cell support containing a forbidden four-cell support also has lower order. There are \(O_\varepsilon(h^{3+\varepsilon})\) normalized four-cell supports. For fixed four cells, distribute them between the two black triples. In the \(3+1\) case, the first triple fixes W; the other rectangle has \(O(h)\) choices. In the \(2+2\) case, each fixed pair places W on a perpendicular line or a Thales circle. Their intersection has at most \(O(h)\) strip points, even when the two loci coincide. Once W and the roles are fixed, the other two black corners are determined. Thus each four-support lies in only \(O(h)\) such six-supports, giving
\[
 O_\varepsilon(h^{4+\varepsilon})
 =o(h^5(\log h)^4)
\tag{10}
\]
after choosing any fixed \(\varepsilon<1\).

The protected laws have no smaller singleton-axis or vertical-axis supports. Consequently these exclusions leave the leading count of distinct minimal six-cell events unchanged.

## 6. Sum over the common corner and take probabilities

For every horizontal phase, exactly half the rows lie in the prescribed phase, up to a bounded error. Therefore
\[
\begin{aligned}
 N_{6,X}(h)
 &\sim \frac14 c_X^2
   \frac{h^5(\log h)^4}{\zeta(2)^2}
   \int_0^1 f(t)^2\,dt\\
 &=\frac{9c_X^2}{80\zeta(2)^2}
     h^5(\log h)^4,
\end{aligned}
\tag{11}
\]
because
\[
 \int_0^1(1/2+t-t^2)^2\,dt=9/20.
\]
The factor \(1/4\) combines the unordered-pair factor \(1/2\) and the phase density of the common corner \(1/2\).

Each six-cell event has probability
\[
 (2/h)^6(1+O(1/h))
\]
under the uniform protected-phase product measure. Thus
\[
 \mu_{6,X}(h)
 \sim \frac{36c_X^2}{5\zeta(2)^2}
       \frac{(\log h)^4}{h},
\]
which is (1).

For comparison, the hidden-rectangle means obtained from (2) and its residue table are
\[
 \mu_{4,\rm hidden,O}\sim\frac{10}{3\pi^2}\frac{\log^2h}{h},
 \quad
 \mu_{4,\rm hidden,C}\sim\frac4{\pi^2}\frac{\log^2h}{h},
 \quad
 \mu_{4,\rm hidden,Q}\sim\frac8{3\pi^2}\frac{\log^2h}{h}.
\tag{12}
\]
They have lower logarithmic order than (1).

The mixed four-cell family has not been evaluated asymptotically here. Nor has the logarithm of the success probability been identified with minus the total event mean. Those are separate required steps before drawing an entropy-ordering conclusion.

