# Low quadratic anchors across a complement wall

9 November 2026. This note supplies a fixed valid low-row collar for both quadratic row laws. It proves only the all-pinned geometry. The conditional avoidance estimates for free cells outside a growing collar remain a separate step.

Put \(q(y)=\binom y2\bmod2\). Adding a constant to the row coloring does not change its rival pairs.

## 1. The two anchors

For \(c_0=q\), take
\[
 a_x=\begin{cases}
 (2,2,1,1)_{x\bmod4},&x<0,\\
 (1,1,2,2)_{x\bmod4},&x\ge0.
 \end{cases}                                                    \tag{1}
\]
This is a complement-phase splice with four consecutive row-1 cells. It has no row-2 cells at distance two.

For \(c_0=q+y\), take
\[
 a_x=\begin{cases}
 (3,3,2,2)_{x\bmod4},&x<-2,\\
 1,&-2\le x\le1,\\
 (2,2,3,3)_{x\bmod4},&x>1.
 \end{cases}                                                    \tag{2}
\]
The unrepaired splice has four consecutive row-2 cells. Replacing them by row 1 preserves their required row color, since \(c_0(1)=c_0(2)=1\). Around the splice, (2) reads
\[
 \cdots22\,33\,1111\,33\,22\cdots .
\]
Thus (2) realizes the displayed complement-wall alignment exactly, with no phase errors. The reverse complement orientation at the same cut is not asserted. In a lattice of alternating quadratic domains, choose each domain length congruent to two modulo four: the cut translation and the complement flip then preserve this local alignment.

Both words are valid seas for every height containing their selected rows. The proof uses the full fixed-final-F rival convention.

## 2. Four-cell collisions cannot use only three consecutive black rows

First, a hidden tilted rectangle with all black rows in \(\{1,2,3\}\) has vertical side increments 1 and 1. It is a unit diamond and puts two black points in one column. An axis rectangle has the same one-black-per-column obstruction.

Same-side and same-diagonal four-cell collisions produce a hidden rectangle. It remains to check mixed side/diagonal collisions. Write their black side and black diagonal vectors as
\[
 U=(x,u),\qquad V=(z,v),
\]
with \(x,z\ne0\), \(|u|,|v|\le2\), and \(|U|=|V|\). A shared integral white side requires \(U\equiv V\pmod2\).

If exactly one of u,v vanishes, the factorization of \(x^2-z^2\in\{\pm1,\pm4\}\) forces the other horizontal component to vanish. This contradicts distinct black columns. If \(\{|u|,|v|\}=\{1,2\}\), the vectors have different vertical parity and cannot share an integral midpoint.

If \(|u|=|v|=2\), both pairs use rows 1 and 3, so their midpoint heights agree. The perpendicular connector is then zero, giving degeneracy. The same conclusion holds when \(|u|=|v|=1\) and the two pairs use the same row pair.

The only remaining oblique case uses row pairs \(\{1,2\}\) and \(\{2,3\}\). Their midpoint heights differ by one. The connector is integral and perpendicular to U, so \(|x|=1\). Equal norms give \(|z|=1\). The two black-column intervals are unit intervals whose midpoints differ by one, so they share a column. The corresponding black rows differ, which is impossible in a sea.

If u=v=0, the equal-length horizontal black diagonal is exactly the shared white side. This is not a genuine collision. Thus no four-cell collision is possible.

This argument allows common white rows outside \(\{1,2,3\}\); it does not impose an artificial height-three restriction.

## 3. Three-black rectangles and singleton collisions

For (1), any three-black tilted rectangle using rows 1 and 2 is a unit diamond. An in-strip completion requires two row-2 cells at distance two. These do not occur. The other orientation completes below row 1.

For (2), row-2 and row-3 cells also never occur at distance two. This excludes every unit-diamond triple.

A triple using all three row values cannot have its right angle at row 2: the other two black points would have equal horizontal coordinate. A right angle at row 3 completes at row 0. A right angle at row 1 requires the row-2 and row-3 points on opposite sides, at horizontal distances 1 and 2. Every row-1 cell lies in the central four-column interval, and the nearest higher rows on opposite sides are separated by at least five. Hence this case cannot occur.

A repeated row-1 diagonal completes below the strip. The only remaining possibility has two row-3 endpoints and a row-1 right-angle vertex. The horizontal side lengths have product four, so the two row-3 columns differ by four or five. A row-1 vertex can lie between them only across the central interval. The unique such endpoint pair is
\[
 (-3,3),\qquad (2,3).
\]
Its two possible row-1 vertices are \((-2,1)\) and \((1,1)\). The completions are respectively \((1,5)\) and \((-2,5)\).

These completions are distinct. They cannot create a tilt/tilt singleton collision. They also have the same row color as the actual row-1 cells in their columns:
\[
 c_0(1)=c_0(5)=1.
\]
Thus they have no virtual singleton-axis rival.

There are no other three-black rectangles. In particular, the repair is valid but is not triangle-free.

## 4. Vertical-axis rivals

For black rows differing by one or two, a nontrivial integral vertical alternative diagonal would require
\[
 L^2-d_x^2\in\{1,4\},
\]
which has no solution with \(d_x>0\) and nonzero row difference.

If the two black rows agree, their horizontal distance is twice the vertical half-gap. For row 1 the lower white endpoint is outside the strip. For row 2, the only possible half-gap is one, requiring row-2 black cells at distance two. For row 3, half-gap one likewise requires row-3 black cells at distance two. None occur.

The remaining case is row 3 with half-gap two, whose displayed rows are 1 and 5. These have the same \(q+y\) color, so they do not form an F edge. All larger half-gaps leave the strip below row 1.

Sections 2--4 cover hidden rectangles, all four-cell collisions, singleton collisions, six-cell collisions, and every axis-rival type. Therefore (1) and (2) are valid.

## 5. Connections to the boundary component

The periodic word \(2233\) is valid by the same argument. The splice
\[
 1^\infty(2233)^\infty
\]
has no three-black tilted rectangle: any right-angle vertex at row 1 would need higher black points on both sides, and the repeated-row unit diamonds are absent. Sections 2 and 4 still apply. Reflection gives the reverse connection.

Hence every phase of \(2233\) belongs to the boundary component containing row 1 for the \(q+y\) partition. The existing \(1122\) anchor gives the corresponding statement for q.

The low-pin buffer estimates also extend from pins in rows 1,2 to pins in rows 2,3. After shifting down by one, the strip includes one extra row below the former boundary. In the cross-pair conic parametrization this changes the finite exceptional range from \(\Delta\ge-1\) to \(\Delta\ge-2\). The new value \(\Delta=-2\) forces the divisor parameter \(X\mid\Delta\), hence \(X\le2\), and is covered by the small-X count. The positive-Delta estimate is unchanged. The other pinned cases depend only on adjacent pin rows, one-sided order, and higher free rows.

## 6. Exact check

[verify_quadratic_low_anchor_wall.py](verify_quadratic_low_anchor_wall.py) independently hashes all tilted presentations in height 5 on 80-column truncations. It checks the two splices, both periodic anchors, and the row-1-to-2233 connection. The output is in [verify_quadratic_low_anchor_wall.json](verify_quadratic_low_anchor_wall.json).

The analytic proof explains why this small height contains every potentially dangerous completion. The finite check supplements that proof; it is not an asymptotic extrapolation.



## 7. Compatibility with a wide frozen collar

Freeze the appropriate word (1) or (2) on \([-R,R]\), with \(R>10h\). Outside the collar, retain only high rows and the prescribed left/right complement phases. Every pinned letter matches its prescribed phase exactly. In (2), the replacement \(2\mapsto1\) does not change its row color.

For any rectangle, an odd split across the cut occurs in one of the two outer gaps between its sorted corner columns. If the horizontal components of its perpendicular sides have absolute values a,b, this gap has length \(\min(a,b)\). Orthogonality gives \(ab\le(h-1)^2\), so the outer gap is at most h.

A new singleton-rival triangle has an odd split by the exact quadratic XOR identity. The isolated corner and the next corner therefore both lie within h of the cut and are frozen. If both are black, the triangle has at least two low pins. Any tilted triangle with two pins in rows 1--3 and one high free point has horizontal span at most \(Ch\): at a low right-angle pin the horizontal product has a vertical factor at most two; if the free point is the right-angle vertex, its completion lies below row 1. This would place the supposed free point inside the wide collar. Hence a surviving new triangle with free variables has exactly one pinned black cell, one nearby white completion, and two free black cells.

The two safe pinned triangles in (2) do not create an additional free collision. Their completions have row 5 and columns -2 or 1. Consider another tilted rectangle at such a completion W. If its two corners adjacent to W are both outside the collar, their horizontal product exceeds \((R-2)^2\), contradicting the height-h vertical product bound. If one adjacent corner is a low pin and the other is free, the vertical product is at most \(4h\), while the nonzero horizontal product is at least \(R-2\). This is again impossible for \(R>10h\). If neither adjacent corner is free, the opposite corner has horizontal coordinate equal to the sum of the two adjacent coordinates minus \(x_W\), but the low-row right-angle product bounds both adjacent horizontal displacements by sixteen; it also remains inside the collar for large h. Thus no free rectangle can share either safe completion.

This verifies the exact phase and pinned-triangle parts of a collar argument. It does not replace the required counts for partially pinned four/six supports or the conditional avoidance bound for the remaining one-pin triangles.



## 8. Uniform partially pinned support counts

The same counting bounds hold for the entire two-sided collar when every pin lies in rows 1--3 and every free row is at least 30. They do not require all free points to lie on the same side.

Count normalized supports, with any one free column fixed, and deduplicate the canonical hidden/mixed/six families. For a fixed epsilon>0 the bounds are
\[
\begin{array}{c|c|c}
\text{family}&\text{number of pins }j&\text{count}\\ \hline
\text{hidden/mixed four}&1&O_\epsilon(h^{2+\epsilon})\\
\text{mixed four}&2&O_\epsilon(h^{3/2+\epsilon})\\
\text{hidden four}&2&O_\epsilon(h^{1+\epsilon})\\
\text{four}&3&0\\
\text{six}&1\le j\le4&O_\epsilon(h^{5-j+\epsilon})\\
\text{six}&5&0 .
\end{array}                                                     \tag{3}
\]
The bounds are independent of the collar length. Prescribing a pin's row removes the ordinary vertical translation; its horizontal location is already determined by normalization and the geometry. Imposing membership in the actual collar only removes supports.

For mixed four with one pin in each black pair, use the notation of Section 7 of [checkerboard_flip_conic_bound.md](checkerboard_flip_conic_bound.md). Now \(\delta\in[-2,2]\), \(\Delta\ge-2\), and the second horizontal vector z may have either sign. The norm and perpendicularity equations remain
\[
 x\mid y\Delta,\qquad
 z^2=x^2-4(\Delta-\delta)(y+\Delta-\delta).
\]
Write \(x=gX,y=gY,\Delta=XT\). Negative Delta forces \(X\le2\), so it belongs to the small-X circle count. Delta zero is degenerate. For \(X>\sqrt h\), T is positive and at most \(\sqrt h\).

The nonsingular-conic proof is unchanged. If its leading coefficient vanishes, \(g=2T\), \(x=2\Delta\), and
\[
 z^2=4\delta^2-2(x-2\delta)(y-2\delta).
\]
Since \(y\ge27\) and \(|\delta|\le2\), nonnegativity forces \(x=O(1)\). This is again in the small-X branch. If the discriminant vanishes,
\[
 T^2Y^2-\delta gY+\delta^2=0.
\]
Here delta is positive and \(Y\mid\delta^2\), so Y has only boundedly many choices and \(g\asymp T^2\). Summing the remaining \(X\le h/T\) choices gives \(O(h\log h)\). Thus the full cross-pair count, including opposite-side free cells, is \(O_\epsilon(h^{3/2+\epsilon})\).

If the two pins belong to the same black pair, two free cells on opposite outer sides have a larger horizontal separation than the pin pair by at least two. Since their separation exceeds \(2R\), equality of norms is incompatible with the pin pair's vertical difference at most two. Same-side free cells obey the existing same-pair bound. Hidden rectangles with two pins must put the low pins on one side: opposite low corners would have the same midpoint height as two high corners. The free row difference is then at most two, leaving O(h) row choices and divisor-many geometries.

There are no four-cell events with three pins and one free cell. A hidden rectangle would put the free row at most five. For a mixed event whose black diagonal consists of two pins, its common white midpoint has height at most three, forcing the free row on the black side to be at most seven. In the remaining case the black side has two pins. Orient it as \(U=(x,u)\), \(x>0\), \(|u|\le2\). Let the alternate diagonal be \(V=(z,v)\), oriented from its low pin to its high free endpoint, and suppose the free endpoint is to the right of all pins. Reflection covers the other side. If T is the side connector, the free endpoint condition and equal norms give
\[
 2T_x>x-z,\qquad
 x(x-z)=\frac{x(v^2-u^2)}{x+z}\ge\frac{v^2-u^2}{2}.
\]
Perpendicularity gives \(xT_x=-uT_y\), while \(2T_y\le v+4\). Consequently
\[
 v^2-u^2<2|u|(v+4),
\]
which forces \(v<8\), hence the free row at most ten. The horizontal-side case has \(T_x=0\) and cannot place the free endpoint beyond both side pins. Thus row 30 is a conservative exclusion threshold.

Finally, a genuine six-cell support comes from two three-black right-angle triples with a common completion. Their row equation is one nontrivial linear relation among the \(6-j\) free row variables. It leaves \(O(h^{5-j})\) ordered row tuples, including repetitions. Fixed row tuples have divisor-many geometries because adjacent row differences of a tilted right angle are nonzero. This proves the six-cell bounds in (3). With five pins, the all-pinned triple completes at a row at most five; the other triple then forces its sole free row at most seven. Hence the unary case is absent.

After division by the free alphabet probabilities, every partially pinned four/six family has incident mass \(o(1)\), uniformly in collar length. The worst family is the two-pin mixed family, with mass \(O_\epsilon(h^{-1/2+\epsilon})\). All-pinned events are absent by the validity of the chosen anchor. These are the universal-family ingredients needed in the growing-collar wall argument.

