# The perpendicular-level route reaches a conditional partition problem

9 November 2026. A bounded refinement of the affine levels \(4a+b=K\)
would solve a difficult P-coloring subproblem. The odd-row restriction
does not remove the relevant partition-regularity obstruction.

## 1. The exact conic on one level

Within a block, put the odd point of label \((a,b)\) at horizontal
coordinate \(2(a-1)\). Restrict the labels to \(b=K-4a\), with \(K\) even.
The odd and even points lie on perpendicular lines. Their intersection
would require \(5a=K\), impossible for odd \(a\). Every tilted right angle
within this block is therefore excluded: two same-parity legs are
collinear, two opposite-parity legs have odd dot product, and the remaining
case would put an odd point at that intersection.

For labels with odd rows \(a,a'\), define
\[
u=5a-K,\qquad v=5a'-K.
\]
Both are odd and belong to the same residue class modulo five. The
odd-to-even diagonal has squared length
\[
4(a-a')^2+(a+4a'-K)^2=\frac{u^2+4v^2}{5}.
\]
Thus its P condition is exactly
\[
u^2+4v^2=5L^2.
\tag{1}
\]

## 2. Removing the parity and five-adic restrictions

**Lemma.** For a positive integer solution of (1),
\[
v_2(u)-v_2(v)\in\{0,2\},\qquad v_5(u)=v_5(v).
\tag{2}
\]

To prove the first statement, write \(r=v_2(u)\), \(s=v_2(v)\).
If \(r<s\), divide by \(2^{2r}\): the left side is one modulo eight,
while the right side is five modulo eight. If \(r=s+1\), the left
side has odd two-adic valuation, impossible for five times a square.
If \(r\ge s+3\), dividing by \(2^{2s+2}\) gives the same one-versus-five
contradiction modulo eight. Only \(r=s\) and \(r=s+2\) remain.

If the two five-adic valuations differ, the left side has even
five-adic valuation, while the right side has odd valuation. Hence
they agree. Dividing out the common power of five preserves an integral
solution: the remaining sum of squares has positive odd five-adic
valuation, so \(L\) contains at least the common power.

It follows that pair partition regularity of (1) on all positive integers
is equivalent to pair partition regularity on positive integers coprime
to ten. One direction is immediate by restricting a coloring. For the
other, start with any finite coloring of the positive ten-units and color
every positive integer \(n\) by
\[
\left(v_2(n)\bmod3,\quad
c\!\left(\frac{n}{2^{v_2(n)}5^{v_5(n)}}\right)\right).
\]
A monochromatic solution has equal two-adic valuations by (2), and equal
five-adic valuations automatically. Dividing their common powers of two
and five gives a distinct monochromatic ten-unit pair.

The same conclusion holds in every fixed odd residue class modulo five.
For a nonzero class \(r\), color each ten-unit \(n\) by its residue
\(s\bmod5\) and the color of \(t_s n\), where \(t_s\) is an odd positive
integer with \(t_s s\equiv r\pmod5\). A monochromatic pair has the same
\(s\), so common scaling transfers it to class \(r\). For class zero,
multiplication by five transfers every odd solution into that class.

## 3. What the primary theorem establishes

In the current primary source, the unconditional theorem requires
\(ac\) or \(bc\) to be square. Here these values are five and twenty.
The conditional theorem applies because \((a+b)c=25\), but assumes
an Elliott-type correlation conjecture. Its two parameter forms have
discriminants eighty and twenty, so both are irreducible; the
reducible-form extension does not apply. These are Theorems 1.2, 1.3,
and 1.13 of [Frantzikinakis, Klurman, and Moreira, version 3](https://arxiv.org/html/2407.08360v3).

Thus that paper gives a conditional unbounded-chromatic conclusion for
(1), including the odd and fixed-residue restrictions by Section 2.
It does not give an unconditional obstruction or a bounded coloring
for this affine-level route.

## 4. Finite in-strip embedding

The conditional conclusion genuinely applies to finite P graphs in the
strip. Take any finite graph of positive odd solutions to (1), all in one
residue class \(r\bmod5\). Choose an even \(K\equiv-r\pmod5\), large enough,
and put
\[
a_u=\frac{u+K}{5},\qquad b_u=\frac{K-4u}{5}.
\]
These are odd and even integers, respectively, and \(4a_u+b_u=K\).
Making \(K\) large puts every marked row and every vertical completion
above row zero. A sufficiently large height then contains them all.

For an edge \(u,v\), the two white rows are
\[
\frac K5+\frac{u-4v}{10}\pm\frac L2.
\]
They are integers because the corresponding odd and even black rows have
odd sum and (1) makes \(L\) odd. The horizontal midpoint is also integral.
The labels are distinct because the odd rows are distinct.

Consequently, a uniform bounded number of refinement colors for all
finite perpendicular levels would provide a bounded coloring of these
conic graphs, by compactness of finite graph colorings. Under the
conjecture used by the cited conditional theorem,
that is impossible. The broader quadratic construction is unaffected:
its color classes need not lie on fixed affine levels.

