# Independent review of the fixed-anchor obstruction

9 November 2026. The proof in
[short_buffer_fixed_anchor_obstruction.md](short_buffer_fixed_anchor_obstruction.md)
passes independent review. Its conclusion concerns a prescribed
anchor and a prescribed linear buffer. It leaves adaptive entrance
paths and component dominance open.

The two-pin completion argument uses the codegree bounds correctly.
After conditioning on either one or both pins, the total weight of
all compatible events meeting those pins is
\(O_\varepsilon(h^{-1+\varepsilon})\), uniformly in the finite
interval length. This bounds their added contribution at every free
column. Events avoiding both pins retain the ordinary incident bound.
There is no all-fixed event, because every minimal support has at
least four cells in distinct columns. The product-form local lemma
therefore applies, and compactness supplies a bi-infinite completion
in the normalized positive-support language.

Both coordinate families have the stated equal norms, perpendicular
connectors, and midpoint identities. Their two rectangles are distinct
and nondegenerate, and all six row coordinates fit in the chosen
height. In the quadratic family the two prescribed core cells satisfy
the phase law, while the common corners violate it. In the ordinary
family the prescribed core rows are odd, and at least the common
corner in the fixed tail is white. In either family the symmetric
difference consists of the four retained black cells, so no coloring
of the variable buffer or other common corner can repair the collision.

The first prescribed core column lies at distance
\(\Theta(h^{3/2})\) from the end of the fixed anchor. It therefore
lies beyond every prescribed \(C h\) buffer for sufficiently large
members of the family. The two-pin lemma places both prescribed cells
inside an admissible protected core. This establishes the stated
failure of universal fixed-anchor extension.
