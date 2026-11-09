# Conditional obstruction for most fixed-slope refinements

9 November 2026. Consider color blocks whose labels lie on a fixed slope
\[
b=t a+c,
\]
where \(a\) is odd, \(b\) is even, and \(t\) is a fixed integer.
For every nonzero \(t\ne1\) with either \(t\) odd, \(t\equiv2\pmod4\),
or \(t=-4\), a uniform bounded refinement eliminating all P pairs is
incompatible with the correlation conjecture used below. This is a
conditional obstruction, not an unconditional theorem about chromatic
growth.

## 1. Why these slopes were candidates

Within one block, the odd points \((2(a-1),a)\) lie on one line and the
even points \((2(a-1),ta+c)\) lie on another. All same-parity triples
are collinear. At an even vertex, a same-parity leg and an odd-point
leg would form a right angle only if
\[
(4+t)(s-a)=t(b-a).
\tag{1}
\]
Here \(s-a\) is even and \(b-a\) odd. If \(t\) is odd or two modulo four,
the two sides of (1) have different two-adic valuations. If \(t=-4\),
its left side vanishes and its right side does not. The other parity
cases are excluded by an odd dot product, or by the odd/even contradiction
\(4a+b=5s\) at an odd vertex.

These blocks therefore exclude tilted three-double right angles.
The parallel-line case \(t=1\) has the same geometric advantage, but
its P problem is different from the homogeneous reduction below.

## 2. Homogeneous coordinates and parameter forms

Put
\[
A=(1-t)a-c,\qquad S=(1-t)s-c.
\]
The black odd-to-even diagonal gives
\[
Q_t(A,S):=
5S^2-2(t+4)SA+(t^2+4)A^2=(1-t)^2L^2.
\tag{2}
\]
Equivalently, with \(d=(S-A)/(1-t)=s-a\),
\[
L^2=A^2+2Ad+5d^2.
\]

A homogeneous parameterization is
\[
\begin{aligned}
P_1(m,n)&=m^2-5n^2,\\
P_2(m,n)&=m^2+2(t-1)mn-(2t+3)n^2,\\
d&=2n(n-m),\qquad L=m^2-2mn+5n^2.
\end{aligned}
\tag{3}
\]
Indeed, \(P_2=P_1+(1-t)d\), and the displayed square identity holds.
The discriminants of the two forms are
\[
20,\qquad4(t^2+4).
\]
For integer \(t\ne0,1\), both forms are irreducible, are distinct, and
have the same leading coefficient.

Under its correlation conjecture, Theorem 1.13 makes such a pair
density regular, and hence gives a monochromatic positive pair for
every finite coloring. The reducible-form theorem does not cover these
parameters: only the integer slope zero makes the second discriminant
square. See [Frantzikinakis, Klurman, and Moreira, version 3](https://arxiv.org/html/2407.08360v3).

## 3. The odd restriction can be transferred

Let \(r=v_2(A)\) and \(s=v_2(S)\) for a positive integer solution of (2).
For the slopes in the statement, one has
\[
\begin{array}{c|c}
t\text{ odd}&r=s\\
t\equiv2\pmod4&r-s\in\{0,-1\}\\
t=-4&r-s\in\{0,-2\}.
\end{array}
\tag{4}
\]

For odd \(t\), both diagonal coefficients in \(Q_t\) are five modulo
eight, and its cross coefficient has valuation one. If \(r\ne s\),
division by \(2^{2\min(r,s)}\) gives an integer equal to five modulo
eight. It cannot be a rational square, contradicting (2).

For \(t\equiv2\pmod4\), the coefficients of \(A^2,AS,S^2\) have
valuations \(3,2,0\), respectively. If \(r>s\), the normalized odd part
is five modulo eight. If \(s\ge r+2\), the total valuation is \(2r+3\),
which is odd. Thus only \(r=s\) and \(s=r+1\) remain.
For \(t=-4\), (2) reduces to \(S^2+4A^2=5L^2\); the valuation lemma in
perpendicular_level_partition_reduction.md gives the last line.

Let \(M=2|1-t|\). Suppose there were a finite coloring avoiding every
odd positive pair in (2) whose difference is divisible by \(M\).
Extend it to all positive integers using the following data:
the color of the odd part, its residue modulo \(M\), and the two-adic
valuation modulo two or three as needed in (4).

A monochromatic positive pair supplied by the conditional theorem has
equal two-adic valuations. Divide them by the common power of two.
Their odd parts \(A_0,S_0\) have the same original color and residue
modulo \(M\). Thus
\[
d_0=\frac{S_0-A_0}{1-t}
\]
is an even integer. The normalized hypotenuse is initially a rational
number, but its square equals
\(A_0^2+2A_0d_0+5d_0^2\), an integer. A rational square root of an integer
is integral. Therefore the normalized pair is an actual forbidden odd
pair, a contradiction.

This proves conditional unbounded chromatic number even after restricting
to odd pairs in common residue classes modulo \(M\).

## 4. Embedding a finite graph in the strip

For a finite collection of odd vertices in one such residue class,
choose \(c\) so that
\[
a_A=\frac{A+c}{1-t}
\]
is an odd integer for each vertex. Then
\[
b_A=\frac{tA+c}{1-t}
\]
is even and satisfies \(b_A=t a_A+c\). Changing \(c\) by multiples of
\(M\) translates every \(a_A,b_A\), and every completion row, by the
same even integer. Choose the direction and size of this translation
to make all rows positive, then choose a height containing them all.

For every edge, the even difference \(d_0\) gives an integral horizontal
midpoint, and its integral hypotenuse is odd. The vertical white
completion is therefore integral and inside the chosen strip.

Compactness of graph coloring now shows that a uniform bounded
refinement of all such finite fixed-slope blocks would contradict the
conditional partition theorem.

The parallel slope \(t=1\) is excluded from this argument: the coordinates
\(A,S\) collapse to the fixed offset \(-c\). Its translation-invariant
distance graph remains a separate possible route. Cross-block geometry
also remains separate from all within-block statements here.

