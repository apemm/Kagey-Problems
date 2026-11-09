# What the linear P palette preserves

9 November 2026. The linear palette in global_P_linear_coloring.md gives
width \(O(h^2)\) for all vertical-rival exclusions. This note identifies
which original one-prime geometric arguments survive arbitrary block
colors, and gives a small obstruction to treating the P theorem as a
complete identifying construction.

## 1. All odd-vertex right angles are still excluded

Write the odd rows as \(2i+1\) and the even rows as \(2j+2\). Choose a prime
\(p>10h\), and put the label \((i,j)\) at
\[
x_{ij}=4i+4p\,c(i,j).
\]
The colors can be arbitrary in this statement.

At an odd-row vertex, two even-row legs have odd vertical components and
horizontal components divisible by four. Their dot product is odd.

If both other rows are odd, reduce the dot product modulo \(p\). It becomes
\[
20(i_1-i_0)(i_2-i_0).
\]
Thus one actual index difference is zero. The corresponding leg is
horizontal; a perpendicular leg must be vertical, so the angle is
axis-aligned.

If one other row is odd and one even, the reduction is
\[
2(i_1-i_0)\bigl(8i_2+2j_2-10i_0+1\bigr).
\]
The bracket is odd, has absolute value less than \(10h\), and is nonzero
modulo \(p\). Again the same-parity leg is horizontal.

At an even-row vertex, two odd-row legs have an odd dot product. Therefore
every remaining tilted three-double right angle is centered at an even
point and uses at least one other even point. In particular, a hidden
rectangle supported on double cells must have all four corners even.

The original even-vertex argument used the fact that a block fixed its
even row. Arbitrary colors do not retain that hypothesis.

## 2. A P-free block with a hidden rectangle

At height twenty, give these four labels a common color:
\[
(a,b)=(1,18),(3,20),(5,2),(7,4).
\]
Their odd rows are distinct. For all twelve ordered pairs, the squared
lengths tested by the stronger P graph are
\[
377,\ 65,\ 153,\ 241,\ 17,\ 65,\ 233,\ 241,\ 17,\ 265,\ 233,\ 41.
\]
None is a square. Thus these labels form an independent set even in the
stronger graph that ignores vertical-white containment.

Nevertheless, their even points in this block are
\[
A=(0,18),\quad B=(4,20),\quad C=(8,2),\quad D=(12,4).
\]
The side vectors \((4,2)\) and \((8,-16)\) are perpendicular. These four
points form a hidden tilted rectangle.

The failure has a direct presentation certificate. Put
\[
M=(2,19),\qquad N=(10,3).
\]
The two rectangles
\[
\{A,M,C,N\},\qquad \{M,B,N,D\}
\]
have the same white presentation \(\{M,N\}\). Their nonshared corners are
exactly the four required even points. Both rectangles lie in the
twenty-row strip. Since \(M,N\) lie outside the double columns, this is
already a collision in the empty scaffold.

Changing the other colors cannot repair the collision. The two
rectangles' symmetric difference remains black even if a later filling
also blacks out one or both common corners.

## 3. Scope of the remaining problem

The linear palette resolves the aggregate color cost for vertical rivals.
A construction still needs to constrain the even points in each block,
then control configurations across different blocks. Avoiding only the
remaining right angles within each color class would not itself settle
mixed four-cell collisions or the singleton filling problem.

The example does not disprove a different linear palette satisfying these
additional constraints. It rules out the implication that P-properness
alone supplies them.
