# A height-15 binary sea construction at spacing eight

9 November 2026. There is an identifying width-441, height-15 board with all
56 parity double pairs, and every other column black only in row 1 or row 15.
It has 497 black points and attains the axis upper bound.

This uses spacing eight between double columns. The original rigid formulation
in REPORT_1xh_construction.md fixes spacing four, so this result establishes
the broader binary sea construction and does not settle the spacing-four
formulation.

## Complete witness

Use zero-based slot indices \(j=0,\ldots,55\), with the double in geometric
column \(8j+1\). In order, the pairs are:

    (3,10),(7,10),(9,10),(10,13),(4,9),(6,7),(6,9),(4,13),
    (2,13),(10,11),(10,15),(12,13),(13,14),(9,12),(5,6),(1,6),
    (8,13),(2,7),(6,13),(3,4),(3,14),(5,10),(3,8),(1,2),
    (8,9),(5,8),(9,14),(5,14),(6,11),(3,6),(11,14),(2,9),
    (6,15),(2,3),(2,5),(7,14),(4,11),(2,15),(3,12),(8,15),
    (4,5),(14,15),(4,7),(8,11),(1,8),(1,12),(4,15),(1,4),
    (2,11),(11,12),(7,12),(7,8),(12,15),(5,12),(1,14),(1,10)

After slot \(j<55\), encode its seven sea columns by the integer \(M_j\).
Bit \(k-1\), \(1\le k\le7\), is one exactly when column \(8j+1+k\) is black
in row 15. A zero bit means row 1. The complete mask list is:

    76,124,109,76,108,108,108,126,108,102,102,110,109,124,78,100,
    114,110,74,8,98,79,118,98,106,30,118,102,36,68,84,68,
    98,44,104,72,41,9,117,94,111,14,45,12,107,6,39,102,
    68,4,87,118,115,34,105

There are 203 row-15 sea points and 182 row-1 sea points. The solver's full
column list is in constant_sea_h15_cadical195_seed91_high385_s8.json.
The file height15_width441_binary_coordinates.json lists all 497 black
coordinates with both coordinates starting at one.

## Verification and search scope

The joint search allows both the double order and the binary sea values to
change. Each failed model supplies a necessary positive-support clause from
actual geometry. It found the board after 732 models, 25,511 learned clauses,
and 147.516 seconds of solving.

The independent pair-completion verifier enumerated all 676,782 rectangles
with at least two black corners. All 676,782 white presentations were distinct.
Other rectangles have at least three white corners and are individually
determined by those points. The saved standalone check includes the source
hash and took 14.531 seconds.

The earlier odd-sea completion uses a different fixed order. Restricting that
order to rows 1 and 15 is UNSAT in the exact fiber model. The successful
binary witness therefore required changing the order.

Every immediate constant collar fails for this particular binary witness.
The bounded exact search also found no binary transition of lengths
4, 8, 16, 24, 40, or 60 to an eventual constant row 1 or row 15. These checks
do not rule out longer transitions or nonconstant infinite tails. The separate
odd-sea witness in height_fifteen_spacing_eight_completion.md already proves
ordinary equality for every width at least 441.

The height-16 odd-sea test at the same spacing ended unknown at its 240-second
cap. It gives neither a construction nor an impossibility result.

A height-19 joint order/binary-sea test also ended unknown at its 300-second
cap. Its width was 713, with 90 required doubles. The preferred order retained
the successful height-15 order, followed by the 34 new pairs. This preference
is explicitly marked as an unchecked candidate in
preferred_h19_spacing8_from_h15.json. The completed search log is
constant_sea_h19_cadical195_seed92_high623_s8.json. No height-19 existence or
impossibility conclusion follows from this run.
