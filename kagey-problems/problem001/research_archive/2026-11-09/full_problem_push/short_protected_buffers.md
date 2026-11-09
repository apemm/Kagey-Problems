# Linear-length variable buffers for protected cores

9 November 2026. The existing entropy-capture argument uses a buffer as long as the full sea memory. The low-pin counts allow a shorter buffer: its length can be \(Ch\). The core may then participate in a pinned event, but all surviving pinned families still have small local-lemma pressure.

This note treats the ordinary-parity and \(q(y)=y(y-1)/2\bmod2\) partitions, with the adjacent-row anchors established in [dense_residue_entropy_capture.md](dense_residue_entropy_capture.md) and [quadratic_parity_entropy_capture.md](quadratic_parity_entropy_capture.md). Reflections of these statements are also valid. No claim about a new anchor for a different protected row partition is needed.

Let L be a bound for the horizontal span of every complete forbidden support, with \(L=O(h^2)\). Let \(O_x\) be the full row class of a fixed protected column law. Let \(a_x\in\{1,2\}\) be its established anchor, and put
\[
 P_x=O_x\cap[7,h].
\]
Thus \(|P_x|=h/2+O(1)\). For a sufficiently large absolute C, set \(B=\lceil Ch\rceil\).

**Short-buffer claim.** For all sufficiently large h, a fixed positive fraction of admissible protected cores of length \(m\ge L\) have valid extensions of the form
\[
 a^\infty\;P^{B}\;O^{m}\;P^{B}\;a^\infty.
\tag{1}
\]
The fraction depends on h but not on m. The claim passed [independent review](short_buffer_independent_audit.md).

The statement concerns the number of variable buffer columns. It does not claim that every core extends, or that the constant/periodic anchor state can be reached after fewer than L fixed anchor letters.

The all-core strengthening fails for a fixed anchor: [an explicit admissible-core obstruction](short_buffer_fixed_anchor_obstruction.md) has a pinned mixed collision reaching \(\Theta(h^{3/2})\) columns beyond the tail.

Admissible cores are counted in the normalized fixed-final-F support language, as in the earlier capture theorem. Core-only events may have a common white corner outside the finite core.

## 1. Low corners confine the exceptional supports

A tilted rectangle containing two corners in rows 1 and 2 has horizontal span \(O(h)\), provided those corners lie in distinct columns.

If they are adjacent, their vertical difference cannot be zero, since a horizontal side makes the rectangle axis-aligned. Their vertical difference is therefore \(\pm1\). Write the side as \((d,\pm1)\) and its perpendicular connector as \((e,f)\). Orthogonality gives \(de=\mp f\), so
\[
 |d|\le h-1,\qquad |e|\le h-1,
\]
and the full horizontal span is at most \(2h-2\).

If they are opposite, their midpoint row is at most 2. The other diagonal has vertical difference at most 2 because both its endpoints remain in the strip. Its vertical component differs in absolute value from that of the pinned diagonal unless the two diagonals give the same rectangle or an axis rectangle. Difference of squares then bounds the horizontal diagonal lengths by an absolute constant. This is stronger than the required \(O(h)\) bound.

A three-black right triangle on rows 1 and 2 is a unit diamond, with possible in-strip completion at row 3. In particular its horizontal span is bounded.

Now consider a six-cell collision with three pinned cells all belonging to one of its two three-black rectangles. Its common corner W has row at most 3 and lies in the tail. The other rectangle has three free points, all strictly to one horizontal side of the tail. Its two adjacent vectors from W therefore have positive horizontal components. Orthogonality forces their vertical components to have opposite signs. One downward component has absolute value at most 2; the other has absolute value at most h. Hence the product of the two positive horizontal components is at most \(2h\), and the horizontal span of that rectangle is at most \(4h\).

If all its free points lie in the buffer, their rows are at least 7, so both vertical components would be positive, which is impossible. If any free point lies in the core, its distance from W exceeds B. Taking \(C>10\) excludes this case as well.

## 2. Unary pinned events cannot reach the core

A four-cell support with three pins is either hidden or mixed.

For a hidden rectangle the free row is at most 3 and the span is bounded. It cannot be a high buffer letter or a core letter beyond B.

For a mixed support, a free row at least 7 is impossible by the already proved three-pin argument in [checkerboard_bridge_counting.md](checkerboard_bridge_counting.md), Section 4. That argument uses only the low pin rows and the one-sided horizontal order.

If the free row is at most 6, all four required black rows belong to a fixed bounded interval. The fixed-row mixed divisor equation has a nonzero product of two bounded row differences on its right side. It therefore bounds the horizontal side displacement by an absolute constant. Equal norms and perpendicular midpoint displacement bound every remaining horizontal coordinate by an absolute constant as well. The horizontal-side branch follows from the bounded difference-of-squares factorization; its zero product is a degenerate equal-diagonal configuration.

Thus a three-pin four-cell event either is impossible or has bounded horizontal span. Its free point can be neither a high buffer letter nor a core letter beyond B.

A six-cell support with five pins has pin distribution \((3,2)\). The first three-black rectangle has its common corner in row 3. The second rectangle's two pinned rows are 1 or 2, so its remaining corner has row at most 4. By the first section, its horizontal span is \(O(h)\). Again its free point belongs neither to the high buffer nor to the core beyond B.

All-fixed-tail events are excluded by the validity of the chosen anchor. Hence every surviving pinned event has at least two free columns.

## 3. The remaining pinned count table

All pins lie in one tail: the two tails are separated by more than L when \(m\ge L\). Reflect horizontally when needed so that every pin is left of every free point.

The usual table still holds:
\[
\begin{array}{c|c|c}
\text{support size}&\text{pins}&\text{normalized geometry count}\\ \hline
4&0&O_\epsilon(h^{3+\epsilon})\\
4&1&O_\epsilon(h^{2+\epsilon})\\
4&2&O_\epsilon(h^{3/2+\epsilon})\\
6&0&O_\epsilon(h^{5+\epsilon})\\
6&1&O_\epsilon(h^{4+\epsilon})\\
6&2&O_\epsilon(h^{3+\epsilon})\\
6&3&O_\epsilon(h^{2+\epsilon})\\
6&4&O_\epsilon(h^{1+\epsilon}).
\end{array}
\tag{2}
\]

Only the two-pin four-cell row needs an additional explanation. If both free rows are at least 7, use the universal low-pin conic bound from [checkerboard_flip_conic_bound.md](checkerboard_flip_conic_bound.md), Section 7. It requires no prime or residue restriction.

If some free row is at most 6, there are only \(O(h)\) free row pairs. For each fixed quadruple of rows, the nonhorizontal mixed-support divisor lemma gives \(O_\epsilon(h^\epsilon)\) geometries. The horizontal-side case follows from
\[
 (u-v)(u+v)=(d-c)^2;
\]
a zero right side is the degenerate equal-diagonal case. This contributes only \(O_\epsilon(h^{1+\epsilon})\).

For same-pair two-pin configurations, the original arguments remain valid without a lower bound on free rows. A pinned side gives \(U_x^2<2h\), by perpendicularity and the one-sided order, so the free row difference is \(O(\sqrt h)\). A pinned diagonal forces the free row difference to be at most 2. Hidden rectangles with two pins satisfy the same fixed-row count or the short-span conclusion from Section 1.

For six-cell supports, the row equation equating the two completion rows is nontrivial in the distinct formal free corner variables. With j pins, it gives at most \(O(h^{5-j})\) free row assignments. Repeated row values do not invalidate this upper bound. Each fixed triple has only divisor-many right-angle geometries: a zero row product would make the rectangle axis-aligned or repeat a black column. Thus these counts do not require every free row to exceed 6.

The exceptional distribution \((3,0)\) with three pins was excluded in Section 1. Four pins leave one nontrivial equation in two free rows, giving \(O(h)\) row pairs. The five-pin case was excluded in Section 2.

## 4. Conditional capture

Every free alphabet in (1) has size \(\gg h\). The table (2) therefore gives total incident local-lemma weight
\[
 \delta_h=O_\epsilon(h^{-1/2+\epsilon})
\]
at every free column. Each normalized geometry has only constantly many translations meeting a fixed column, even when some of its free points lie in the core.

Set \(x_E=2\Pr(E)\). The shared-variable local-lemma criterion holds for a fixed \(\epsilon<1/2\) and sufficiently large h.

Let I be the core-only bad events and J the other bad events. Every event in J has a free variable within distance \(L+B\) of one of the two ends of the core. Indeed an event using a buffer variable has this property directly; an event using a tail pin has all its free support within horizontal distance L of that pin. Consequently
\[
 \sum_{E\in J}x_E\le C(L+B)\delta_h=O_h(1).
\tag{3}
\]
This replaces the older assertion that every noncore event must use a buffer variable.

Order the core events first. The conditional local-lemma product bound gives
\[
 \Pr(\text{avoid all events})
 \ge \Pr(\text{avoid I})\prod_{E\in J}(1-x_E)
 \ge c_h\Pr(\text{avoid I}),
\tag{4}
\]
where \(c_h>0\) is independent of m. All product assignments have equal weight within their columns. Counting buffer choices shows that at least a fraction \(c_h\) of valid cores admit an extension (1).

The fixed anchor tails lie in the previously established boundary component. Thus these extensions give the same exact entropy capture and strict proper-submatrix comparison as the original long-buffer construction.

The improvement is geometric: the variable connector has length \(O(h)\). The success fraction in (4) is still height-dependent and controlled using an \(O(h^2)\) end region. Neither an individual-core extension theorem nor a general recurrent-component bridge follows.

