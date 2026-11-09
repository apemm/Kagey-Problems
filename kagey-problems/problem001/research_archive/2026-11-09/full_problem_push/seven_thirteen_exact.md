# The exact value on the seven-by-thirteen board

9 November 2026. **\(f(7,13)=23\).** The upper bound is analytical, using the established value \(f(7,12)=21\). The lower bound has an explicit witness checked by two independent rectangle generators.

The column word is
\[
56,\ 45,\ 34,\ 23,\ 2,\ 12,\ 1,\ 2,\ 3,\ 14,\ 25,\ 367,\ 17.
\]
For example, \(367\) means that rows 3, 6, and 7 are black in that column. The word has eight double columns, one triple column, and four singleton columns, for 23 black points.

The checker `verify_seven_thirteen.py` generates all 2,333 rectangles in two ways. One groups equal diagonals with a common midpoint. The other uses axis rectangles and perpendicular integer side vectors. The resulting rectangle sets agree, and all 2,333 white presentations are distinct. The recorded check is `seven_thirteen_exact_check.json`.

For the upper bound, the proved boundary-cropping recurrence gives
\[
f(h,m)\le
\max\left(m+\left\lfloor\frac{h^2}{4}\right\rfloor
 -\left\lfloor\frac h2\right\rfloor,\ f(h,m-1)+2\right)
\quad(h\ge7,\ m\ge3).
\]
Putting \(h=7\), \(m=13\), and \(f(7,12)=21\) gives
\[
f(7,13)\le\max(22,23)=23.
\]
The proof of the recurrence is in `boundary_cropping_recurrence.md`; the width-12 result is in `seven_twelve_exact.md`.

The witness was found by the fixed-row-core SAT search at catalog index 996. The corresponding record is `fixed_core_h7_w13_100_cadical195_crop.json`. The search does not need to exhaust the remaining cores: the explicit lower witness and the analytical upper bound already establish the exact value. Partial or completed UNSAT ranges are not used in this proof.
