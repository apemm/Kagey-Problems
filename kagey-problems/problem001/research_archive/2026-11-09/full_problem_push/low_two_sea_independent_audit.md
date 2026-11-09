# Independent audit of the punctured low-two sea

9 November 2026. The theorem in [Exact one-label exceptions for the gap (1,2,1)](low_two_sea_exact_exceptions.md) passes an independent analytical audit. Its scope is the infinite-strip background with row one in odd columns, row two in columns two modulo four, and empty columns zero modulo four. Singleton and vertical rivals use the complete final parity graph.

Adding one parity edge at column zero is safe against every support using at most that label precisely when the edge is not
\[
 \{1,4v^2+2\},\qquad v>0\text{ odd}.
\]

The exceptional geometry uses the central vertical diagonal and a row-two sea point at horizontal offset \(2v\). The circle equation is \(4v^2=b-2\). Its missing corner has odd row \(b-1\) over an even row-two sea point, so the final parity graph supplies the singleton rival.

The sufficiency case split is complete. Checkerboard parity excludes a four-cell support using the central odd point. Three-black rectangles using only the central even point have the two equations displayed in the note; their singleton completions are uniquely determined and lie in odd columns on odd rows. The two equations give different completion rows. Rectangles using both central points are exactly the exceptional family, whose completions are in even columns, so no cross-family six-cell collision is missed.

For the remaining mixed four-cell case, the central even point has row \(r\). With \(r\ge4\), a side pairing of that point with either low row puts a shared corner at row \(2-r/2\le0\). If it is diagonally paired with row two, an integral horizontal alternative has length two modulo four: the other possible even vertical residue makes the squared norm eight modulo sixteen. Consequently both alternative endpoint columns are even and cannot lie above two row-one sea points. If it is diagonally paired with row one, the other side has vector \((d,1)\), and perpendicularity gives \(d\mid(r-2)/2\), while equal lengths give \(|d|\ge r-1\). These inequalities are incompatible. At \(r=2\), horizontal alternatives with the same midpoint and length coincide, and cross pairings have zero connector. These are degenerate cases, not omitted rivals.

The note's explicit two-label singleton collision also checks. Thus the result is a local one-label theorem; it does not itself fill an equality board or remove interactions between different labels.

## The full period-four background

The companion theorem in [A fixed periodic sea valid at every height](universal_low_four_sea.md) also passes an independent audit. The word \(4,1,2,1\) repeated is valid for every height at least four, including virtual rivals supplied by the complete parity graph.

With one row-four point, the three-black classification above reduces to the two reflected row-three completions. Their column residues select one orientation uniquely. With two row-four points, a row-one right-angle vertex would require a product equal to minus nine, although both horizontal offsets have the same odd residue modulo four. A row-two vertex forces horizontal offsets \(2,-2\), producing the unique row-six completion. These completions lie over sea points of the same row parity.

For mixed four-cell supports with two row-four points, the remaining two points must have the same low row. Cross pairings have equal midpoint rows, so perpendicularity forces a zero connector. Horizontal pairings cannot give a nondegenerate alternative diagonal. With three row-four points, the fourth cannot be on row one by midpoint integrality; on row two it gives squared length eight modulo sixteen, unlike the squared length of a row-four pair. This accounts for every additional mixed case beyond the one-label audit.

The substitution counterexample is exact: the side vector \((9,-3)\), connector \((1,3)\), and diagonal vector \((3,-9)\) have the asserted orthogonality and equal squared length ninety. Its shared whites are \((-3,7),(6,4)\). Thus the universal background theorem does not supply arbitrary edge insertions.
