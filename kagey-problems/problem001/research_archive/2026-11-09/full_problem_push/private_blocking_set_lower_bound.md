# Even optimized disjoint private prescriptions need two logarithms

9 November 2026. The disjoint-influence obstruction can be strengthened.
The conclusion below concerns selected blocking prescriptions, not only
the larger sets of all influence columns.

Let \(h=2n\) be even, and use the binary sea alphabet \(\{1,h\}\).
For each opposite-parity edge \(e\), consider a finite prescription
\(S_e\subset\mathbb Z\setminus\{0\}\), assigning one sea letter to
each column in \(S_e\). Require that the isolated double \(e\) at column
zero, with these prescriptions, be valid for **every** completion of
the remaining columns by either sea letter in the infinite strip.
The requirement can also include the full final axis-pair graph.

**Proposition.** There is an absolute \(c>0\) such that
\[
 \sum_{e\in F}|S_e|\ge c h^2(\log h)^2
 \tag{1}
\]
for all sufficiently large even \(h\).
Consequently, if translates of these private prescription sets are
pairwise disjoint and contained in the final board, that board has
width \(\Omega(h^2(\log h)^2)\).

This does not lower-bound the true equality threshold. It rules out
an absolute quadratic width for this particular strategy even after
optimizing which blocking columns are prescribed. Compatible overlap,
joint completion constraints, or a different local background remain
possible.

## 1. A forced hitting set at each odd endpoint

Suppose \(e\) contains the odd row \(a=2k+1>1\).
For every positive factor pair
\[
 uv=k^2,\qquad u<v,
\]
consider the four required black points
\[
 (0,2k+1),\qquad(v-u,1),\qquad(-u,1),\qquad(v,1).
 \tag{2}
\]
The first two are a diagonal of a tilted rectangle whose other
diagonal is
\[
 W=(-u,k+1),\qquad Z=(v,k+1).
 \tag{3}
\]
Indeed the diagonals have the same midpoint, and
\[
 (v-u)^2+(2k)^2=(u+v)^2.
 \tag{4}
\]
The second rectangle is the axis rectangle with white side \(WZ\)
and black side joining \((-u,1)\) to \((v,1)\).
All rows lie in the strip, and the two rectangles are distinct.

The three sea columns
\[
 H_{u,v}=\{-u,v-u,v\}
 \tag{5}
\]
are distinct and nonzero. If the prescription does not assign row
\(h\) at any of these columns, complete all three with row 1.
Then both rectangles have exactly the white presentation \(\{W,Z\}\).
Here \(1<k+1<h\), so those two points remain white under either
binary sea choice. Thus every valid private prescription must put
row \(h\) on a hitting set of the family (5).

There are \((\tau(k^2)-1)/2\) members of this family.
A negative integer belongs to at most one member, as its value
determines \(u\). A positive integer can occur as \(v\) in at most
one member and as \(v-u\) in at most one member. In the latter case,
\(u(u+x)=k^2\) has at most one positive solution for fixed \(x\).
Hence the maximum incidence degree is two, and
\[
 \#\{x\in S_e:\text{the prescribed row is }h\}
 \ge \frac{\tau(k^2)-1}{4}.
 \tag{6}
\]
This argument uses an actual tilted/axis collision. It does not rely
on a virtual owner column elsewhere in the construction.

Reflecting the strip gives the corresponding lower bound on row-1
prescriptions from the even endpoint \(b\):
replace \(k\) in (6) by \((h-b)/2\). The odd-endpoint bound alone
already suffices for (1).

## 2. An elementary divisor average

For every positive integer \(k\),
\[
 \tau(k^2)=\sum_{d\mid k}2^{\omega(d)}.
 \tag{7}
\]
This follows at a prime power from \(2e+1=1+2e\).
Consequently, for \(X\ge2\),
\[
 \sum_{k\le X}\tau(k^2)
 =\sum_{d\le X}2^{\omega(d)}\left\lfloor\frac Xd\right\rfloor
 \ge\frac X2\sum_{d\le X}\frac{2^{\omega(d)}}d.
 \tag{8}
\]
The last harmonic sum is \(\Omega((\log X)^2)\).
To see this without a mean-value theorem, use
\[
 2^{\omega(d)}=\#\{(u,v):uv=d,\ (u,v)=1\}.
 \tag{9}
\]
Put \(Y=\lfloor\sqrt X\rfloor\). Then
\[
 \sum_{d\le X}\frac{2^{\omega(d)}}d
 \ge\sum_{\substack{u,v\le Y\\(u,v)=1}}\frac1{uv}.
 \tag{10}
\]
The weight of pairs with a common divisor is at most
\[
 \sum_{r=2}^Y\frac1{r^2}
       \left(\sum_{j\le Y/r}\frac1j\right)^2
 \le\left(\sum_{r=2}^{\infty}\frac1{r^2}\right)H_Y^2.
 \tag{11}
\]
The constant in parentheses is less than one. Subtracting (11)
from \(H_Y^2\) proves (10) is at least \(cH_Y^2\).
Equations (8)--(11) give
\[
 \sum_{k\le X}\tau(k^2)\ge cX(\log X)^2.
 \tag{12}
\]

Each odd row \(2k+1\), \(1\le k\le n-1\), occurs in exactly \(n\)
parity edges. Summing (6) therefore gives
\[
 \sum_e|S_e|
 \ge \frac n4\sum_{k=1}^{n-1}\bigl(\tau(k^2)-1\bigr)
 \ge c n^2(\log n)^2.
 \tag{13}
\]
This is (1).

## 3. Exact scope

The proposition assumes a private prescription that works in the
infinite strip under every remaining binary completion. This is the
local guarantee used before disjointly assembling the positional
construction. It does not apply to a finite board that relies on its
ends to truncate these rivals, or to a construction that chooses all
sea letters jointly rather than leaving each unprescribed letter free.
Nor does it prohibit two labels from sharing a compatible blocking
prescription at one physical column.

The collision, divisor summation, and scope have passed
[independent review](private_blocking_independent_audit.md).
