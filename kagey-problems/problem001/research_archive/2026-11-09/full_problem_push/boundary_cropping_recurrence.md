# A near-extremal recurrence from boundary cropping

For \(h\ge7\), let

\[
q_h=\left\lfloor\frac{h^2}{4}\right\rfloor,
\qquad r=\left\lfloor\frac h2\right\rfloor,
\qquad e_*=q_h-r+1.
\]

The large-column inequality and its equality classification give a useful finite-width recurrence:

\[
\boxed{
f(h,m)\le
\max\{m+q_h-r,\ f(h,m-1)+2\}
}
\tag{1}
\]

Here \(m\ge3\). When the first term already exceeds the number of board cells, the inequality is only a formal upper bound.

## Proof

Let \(S\) be valid, and suppose \(|S|\ge m+e_*\). Its axis row-tree graph has

\[
e(H)=|S|-\#\{\text{nonempty columns}\}\ge|S|-m\ge e_*.
\]

A column containing \(k\ge4\) black points would give

\[
e(H)\le h-1+q_{h-k}<h-1+q_{h-3}=e_*.
\]

Thus every column has at most three black points. If a triple occurs, its bound gives \(e(H)\le e_*\). Equality holds, and the classification in `large_column_boundary_classification.md` permits exactly one triple column. If \(e(H)>e_*\), there are no triples.

At least one of the two boundary columns therefore contains at most two black points. Delete that column. No remaining coordinates are compressed except by a uniform translation when the left column is deleted. The surviving blackout is valid on \(h\times(m-1)\): a collision there would already have been a collision in the original board. Hence

\[
|S|-2\le f(h,m-1).
\]

Either \(|S|\le m+e_*-1=m+q_h-r\), or the preceding inequality applies. This proves (1).

## An analytical upper bound at seven by eleven

The exact value \(f(7,10)=18\), proved in `seven_ten_exact.md`, gives

\[
f(7,11)\le\max\{11+12-3,18+2\}=20.
\]

The explicit 20-point construction in `seven_eleven_exact.md` therefore proves \(f(7,11)=20\) without requiring a separate exhaustive upper-bound search at width eleven. The completed 36,888-family search provides an independent finite check of this analytical implication.

## Cropped-subboard constraints for exact searches

Every consecutive \(k\)-column subboard of a valid board has at most \(f(h,k)\) black points. This requires no extension or padding theorem. It is a restriction to a smaller board.

Suppose an ordering search constructs an \(h\times m\) board with target \(N\). If the assigned prefix contains \(b\) black points and has length \(j\), then a necessary condition is

\[
N-b\le f(h,m-j).
\tag{2}
\]

Every completed consecutive block within that prefix must also satisfy its known finite-width upper bound. Equations (1) and (2) are safe pruning rules, including for boards with empty columns or repeated singleton types.

For a hypothetical 22-point seven-by-twelve board, the exact values at widths 9, 10, and 11 imply:

* Each boundary column contains at least two black points.
* Each boundary pair of columns contains at least four black points.
* Each boundary block of three columns contains at least five black points.

The cropped search `seven_twelve_22_crop_data.json` uses only the newly certified bounds \(f(7,9)=17\), \(f(7,10)=18\), and \(f(7,11)=20\), together with the empty-width value zero. Its pruning therefore does not depend on older small-board tables.

## A threshold lower bound from any exact finite width

Every board attaining the general row bound \(m+q_h\) has at most two black points per column. For any integer \(0\le k\le m\), restrict it to consecutive \(k\) columns. The deleted columns contain at most \(2(m-k)\) black points, so

\[
m+q_h-2(m-k)\le f(h,k).
\]

Thus every equality width \(m\) satisfies, for each \(k\le m\),

\[
\boxed{m\ge q_h+2k-f(h,k).}
\tag{3}
\]

An equality width always has \(m\ge q_h\), since \(m+q_h\le2m\). Therefore any fixed \(k\le q_h\) satisfies the required range automatically. For example, \(f(7,10)=18\) gives the necessary equality width \(m\ge14\). This is weaker than the suspected seven-row threshold near 20, but (3) converts any further exact finite-width result in the allowed range into an additional threshold obstruction.
