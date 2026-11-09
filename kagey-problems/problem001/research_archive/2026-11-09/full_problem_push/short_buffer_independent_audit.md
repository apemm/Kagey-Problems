# Independent audit of the linear variable buffers

9 November 2026. The positive-fraction theorem in
short_protected_buffers.md passes independent review, with admissible
cores interpreted in the normalized fixed-final-pair-set support
language used by the earlier capture theorem.

Two low pinned corners in distinct columns confine a tilted rectangle
to horizontal span \(O(h)\). If they are adjacent, their vertical
difference is one and perpendicularity bounds both horizontal
components by \(h-1\). If they are opposite, the midpoint row is at
most two; the bounded difference of squared diagonal components gives
bounded span.

The six-cell distribution with three pins in one triangle has common
corner in row three and in the tail. If the other three corners lie
to its right, the two horizontal legs are positive. Orthogonality
forces one downward vertical leg of length at most two, so the
horizontal product is at most \(2h\), and the span is at most \(4h\).
This cannot reach the core through a sufficiently long \(Ch\)
buffer, and high buffer rows alone are impossible.

For a three-pin mixed support, a free row at least seven is excluded
by the one-sided geometric inequalities. Otherwise all four required
rows lie in a bounded interval. The nonzero mixed divisor product,
or the horizontal difference-of-squares factorization, then bounds
its entire span absolutely. A five-pin six-cell support similarly
forces its free row at most four and its span \(O(h)\).
These checks exclude every unary pinned event.

The surviving two-pin mixed count remains
\(O_\varepsilon(h^{3/2+\varepsilon})\). If one free row is low,
there are only \(O(h)\) row pairs and the fixed-row divisor bound
suffices. The same-pair counts do not require high free rows.
The six-cell completion-row relation remains nontrivial after pinning;
its repeated numerical row values do not remove a formal variable.

Thus the stated local-lemma pressure is valid even when a pinned
support reaches the core. Noncore events need not contain a buffer
variable, but they do contain a free variable in the \(O(L+B)\)
end region. Charging their total weight to that region proves a
success fraction depending on \(h\), uniformly in the core length.
The fixed anchor tails are still long enough to give their exact
finite-state boundary states.

This proves positive-fraction entropy capture with \(O(h)\) variable
buffers. It does not prove universal extension of individual cores.
An explicit obstruction to that stronger fixed-anchor statement is
given in short_buffer_fixed_anchor_obstruction.md.
