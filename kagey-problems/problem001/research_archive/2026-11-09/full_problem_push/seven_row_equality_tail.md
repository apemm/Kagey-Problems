# Equality constructions at every width from 21 onward

9 November 2026. **For every `m>=21`, `f(7,m)=m+12`.** Use the first `m`
columns of the following infinite word:

```
16,36,5,25,2,2,14,7,12,27,2,7,67,7,47,7,7,56,45,34,23,1,1,1,2,2,2,...
```

The first 21 columns are the previously stored equality witness. Columns
22 through 24 are singleton row 1. Every later column is singleton row 2.
The twelve double columns are exactly the twelve odd/even row pairs, each
occurring once. Thus every prefix of length at least 21 has `m+12` black cells,
and its axis rectangles have distinct presentations.

## Finite verification

`equality_tail_search.py` found the transition `1,1,1` to the constant row-2
tail. Its saved result, `equality_width21_tail_search.json`, contains the first
60 columns: the core, three transition columns, and 36 copies of row 2.
The black set has 72 cells. All 41,860 rectangle presentations are distinct.

Two independent rectangle generators agree on this board. One groups pairs
of points by common midpoint and squared diagonal length. The other enumerates
perpendicular adjacent sides. Both generate the complete rectangle set before
its presentations are checked. This is a finite direct verification, without
SAT or a restricted list of candidate violations.

Every prefix with width between 21 and 60 is valid by restriction: its
rectangles already occur in the checked board, and restriction does not change
their corner colors. The remaining task is to justify the infinite tail.

## Why the tail remains valid

A tilted lattice rectangle in height seven has horizontal span at most ten.
Indeed, at its leftmost corner write the two incident side vectors as
`(a,b)` and `(c,-d)`, with positive integers `a,b,c,d`. Perpendicularity gives
`ac=bd`, while `b+d<=6`. Its horizontal span satisfies
`a+c<=ac+1=bd+1<=10`. Consequently two tilted rectangles sharing a point
have union span at most twenty. The 36-column checked tail is more than
sufficient for both locality bounds.

The constant row-2 sea is locally valid for the full odd/even row graph. A
tilted rectangle has at most two black corners. If it has two, they form a
horizontal diagonal. Its two white corners form a vertical diagonal with
rows symmetric about 2, hence of the same parity. The full odd/even graph
contains no edge between those white rows, so there is no vertical axis
rival. A vertical white diagonal determines its horizontal black diagonal
uniquely, so two tilted rectangles cannot share that presentation. With
three or four white corners, the rectangle is determined uniquely. No tilted
rectangle is hidden in this sea.

Consider any collision created by extending the checked width-60 board.
Axis/axis collisions remain impossible: the distinct double pairs are
unchanged, and new singleton columns add leaves to the incidence graph.
A newly appearing tilted rectangle lies entirely in the constant row-2
region, unless its rightmost column is at most 34; the latter rectangles
were already checked. Two colliding tilted rectangles with a nonempty
presentation share a shown corner. If one reaches beyond column 60, their
union cannot reach the nonconstant prefix ending at column 24. They would
therefore give a collision in the constant sea, which was just excluded.
An empty presentation would require a hidden rectangle, also excluded.

Distant axis rivals require a separate check. Every edge of the final row
graph already has its unique double owner among the first 21 columns. A
singleton or vertical-pair axis rival of an old tilted rectangle is thus
already available inside the checked board whenever its required edge
exists. New singleton tail columns cannot supply a missing double owner.
A horizontal or oblique axis rival uses the shown corner columns themselves,
so extending the board cannot create one for an old tilted rectangle.
For a new tilted rectangle in the constant sea, the same-parity vertical
white pair excludes its only possible axis rival, as above.

All possible collisions are therefore excluded at every larger width. The
general upper bound `f(7,m)<=m+12` proves equality. The completed finite
exclusions in `seven_row_equality_width_exclusions.md` rule out every smaller
width. Together these results give the exact threshold `m_0(7)=21`.
