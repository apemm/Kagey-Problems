# Independent construction and insertion audit

8 November 2026. This audit checks the Q/T reductions, the eleven-row middle count, and the insertion bridge. It also identifies a correction to the earlier law (P). Existing reports and scripts were not changed.

## 1. Findings

* The Q/T equations and the hidden-bisection argument in `../construction_obstructions.md` are correct.
* The trimmed eleven-row core has exactly 384 valid middle assignments. Every one of the 384 was independently checked by direct presentation equality, not sampled.
* The isolated-double bridge is valid for every pair set containing its edge. Section 4 supplies a self-contained proof, including all tilted collisions.
* The older `REPORT_1xh_construction.md` misclassifies a boundary case of law (P) as a unit clause. An in-grid opposite-parity vertical completion is always fatal when its pair belongs to the final double graph. The exact middle-cell compiler does not inherit this error.
* Free seas cannot repair collisions whose symmetric difference already consists entirely of required double points. This limits what relaxing the rigid family can accomplish.

## 2. Q/T equations and hidden rectangles

Let four distinct black points be `A,B,C,D`. Put

\[
 U=B-A,\qquad V=D-C,\qquad S=(A+B)/2,\qquad M=(C+D)/2.
\]

Suppose both components of `U` are nonzero. The proposed common pair is

\[
 W=M-U/2,\qquad Z=M+U/2.
\]

The first rectangle, with complementary black side `AB`, exists exactly when

\[
 (S-M)\cdot U=0,\qquad S\ne M.
\]

The second, with complementary black diagonal `CD`, exists exactly when

\[
 |V|^2=|U|^2,\qquad V\ne U,-U.
\]

Indeed, its two adjacent side vectors are `(U+V)/2` and `(U-V)/2`; their dot product is zero. Integrality and membership of `W,Z` in the grid must also be imposed. The second rectangle is axis-aligned precisely when

\[
 V=(U_x,-U_y)\quad\hbox{or}\quad V=(-U_x,U_y).
\]

This confirms the equations, the Q/T distinction, and the all-double specializations in the audited note. For an exact *two-white-point* presentation, `W,Z` must be white. For an invalidity certificate, their colors need not be specified: the two rectangles have symmetric difference `{A,B,C,D}`, so blackening either shared point changes both presentations identically.

The reduction of side/side and diagonal/diagonal collisions to hidden rectangles is also valid. Two different complementary sides form a rectangle. Two distinct complementary diameters of one circle also form a rectangle. A mixed collision cannot share an additional black point: three common corners determine a rectangle.

The hidden-bisection proof is exact. If a hidden rectangle has a side vector `v` with `gcd(v_x,v_y)>=2`, split that side at `v/g`, where `g` is this gcd. The two resulting lattice rectangles share the intermediate side, and their symmetric difference is the original four black corners. They therefore have identical presentations. The argument does not require the intermediate points to be white. In a pure `1,x,h` region, any hidden rectangle is all-double; its horizontal side components are divisible by four, and perpendicularity forces at least one vertical component to be even. Thus a side is divisible by two and bisection applies.

The height threshold for Q is correct under the parity-double assumption. Write its positive horizontal side components as `a,c`, positive vertical components as `b,d`, so `ac=bd`. Both `a,c` are positive multiples of four. If they differ, `bd>=32`, hence the integral row span `b+d` is at least 12. If `a=c`, two forced black points share a column. Their vertical separation is `b` or `d` and must be odd. Since `bd=a^2` is divisible by 16, the other factor is at least 16, giving span at least 17. Therefore `h>=13`. The displayed height-13 example attains this bound. Among heights `h=3 mod 4`, the first possible Q is consequently at height 15.

The independent checker verifies both displayed Q/T rectangle pairs by equal diagonals and tests every triple of their completed black patches for a right angle. Both patches have zero black right angles. Thus those examples establish independence from law (i), while making no assertion that the patches avoid every other obstruction.

## 3. The exact count 384, checked in both directions

The object counted is the width-117 core from `dfs_gap_h11_s23.json`, trimmed to its first and last doubles. There are 29 middle variables. The count does not include the two original end seas or a collar.

The independent checker uses the stored geometric certificates only to obtain an **upper bound** on valid assignments. For each of the 38 certificates it checks, without importing any existing checker:

1. both four-point sets are nondegenerate rectangles;
2. they are distinct;
3. the cells of their symmetric difference are either fixed black or precisely the variable literals in the stored condition.

Every valid assignment must therefore avoid the 38 certified forbidden conjunctions. Exhaustive truth tables on their variable components give exactly 384 survivors. The nontrivial component counts multiply to `2^7*3`; no formula-completeness assumption is used.

For the matching **lower bound**, the checker freshly enumerates rectangles by grouping all unordered grid-point pairs according to doubled midpoint and squared length. Two different diagonals in one group give one rectangle. This enumerates all 435,307 rectangles of the `11 x 117` grid. Of these, 54,885 can show at most two points under any middle assignment. Every other rectangle always shows at least three points, which determine the rectangle uniquely.

For **each of the 384 survivors**, the checker constructs its black set and directly hashes the actual presentation of every potentially weak rectangle. No presentation is repeated. This also allows the empty presentation once, as the definition requires; it does not rely on a blanket hidden-rectangle rejection.

Thus 384 is an exact independent count. The check took about 14 seconds with the bundled Python interpreter. The new law-(P) correction below does not change it: its necessary certificates and all 384 direct presentation tests already use actual rectangles, not the older geometric classification.

Reproduce with `construction_audit_check.py` in this directory. The script imports only Python standard-library modules and does not import the existing clause generator or rectangle checker.

## 4. Self-contained isolated-double insertion proof

Fix `1<=a<b<=h`. Put black points in row 1 at every column `x<0`, in rows `a,b` at column 0, and in row `h` at every column `x>0`. Call the central pair `D`. The following proof does not assume a parity partition and does not invoke the isolated-double proposition from the paper.

Three elementary geometric facts will be used. A tilted rectangle has only one corner at its lowest row and one at its highest row. Corners in rows 1 and `h`, if both present, are opposite: a side joining those rows leaves no vertical room for a nonzero perpendicular side. Two corners in one column are also opposite, because a vertical side would make the rectangle axis-aligned.

### There are at most two black corners in a tilted rectangle

If both central points are corners, they are a vertical diagonal. The other two corners lie strictly between rows `a,b`, so neither can be a boundary sea point.

Otherwise three black corners would consist of one central point `(0,c)` and sea points `(s,1),(t,h)`, where `s<0<t`. The sea points are opposite, so their adjacent central corner would satisfy

\[
 s t=(c-1)(h-c).
\]

The left side is negative and the right side nonnegative. This is impossible. Three sea corners are impossible as well. Hence no tilted rectangle is hidden or shows a singleton.

### White pairs from black diagonals straddle column zero

There are four types of black diagonal:

* a left sea point `(s,1)` and a right sea point `(t,h)`;
* the central pair `(0,a),(0,b)`;
* a left sea point `(s,1)` and one central point `(0,c)`;
* the horizontal/vertical reflection of the preceding type on the right.

For the first type, the white rows lie in `2,...,h-1`. Comparing the equal diagonal lengths shows that the white horizontal half-separation exceeds `(t-s)/2`. Thus the left white column is less than `s<0`, and the right white column exceeds `t>0`.

For the central vertical diagonal, the white columns are nonzero opposites, and their rows lie strictly between `a,b`.

For the third type, the boundary point is the bottom corner and the central point the opposite top corner. The white rows lie in `2,...,c-1`. Equal diagonal lengths give white horizontal half-separation strictly greater than `|s|/2`. Thus one white column is less than `s<0` and the other is positive. The fourth type is symmetric.

Consequently every white pair in these cases is in interior rows and straddles column zero. It is not vertical. If horizontal, its two columns have different black rows, 1 and `h`, so it has no axis rival. If oblique, its crossed cells are interior cells of sea columns and are white, so again it has no axis rival. These statements are independent of the final pair set `F`.

### White pairs from black sides lie strictly on one side

A black side on the left joins `U=(s,1)`, with `s<0`, to `d=(0,c)`, with `c>1`. Its vector is `(-s,c-1)`. The perpendicular translation to the other side has the form

\[
 n=t(-(c-1),-s),\qquad t>0.
\]

The sign follows because the translated row of `U` must remain above row 1. The white points `U+n,d+n` both have negative columns and rows greater than 1. Their pair is oblique, and its crossed cells are white because all those sea columns are black only in row 1. The right-hand case has both white columns positive and both white rows below `h`.

### Two tilted rectangles cannot show the same pair

A diagonal presentation straddles zero, whereas a side presentation lies strictly on one side. These cases cannot coincide.

For diagonal presentations, a common white pair fixes the midpoint and length of the black diagonal. Within each of the four types above, those data fix the black endpoints. Across types:

* the central diagonal has midpoint column zero, excluding either sea/central type;
* left and right sea/central types have midpoint columns of opposite signs;
* a two-sea diagonal can match a left sea/central diagonal in midpoint row only if the central point is in row `h`. Writing the two-sea columns as `s<0<t`, equal midpoint columns and lengths then require `(s+t)^2=(t-s)^2`, hence `st=0`, impossible. The right case is symmetric;
* a two-sea diagonal with midpoint column zero has squared length `4t^2+(h-1)^2`, larger than the squared length of the central diagonal, which is at most `(h-1)^2`.

For a side presentation wholly on the left, orient its vector with positive horizontal component. Its black complementary side then has vector `(-s,c-1)` with both components positive. This vector determines the sea column `s` and central row `c` uniquely. It therefore determines the black side and the rectangle. The right case is identical after reflection, and a left presentation cannot equal a right presentation.

This exhausts tilted collisions. Presentations of at least three points determine their rectangle uniquely.

For completeness, axis-aligned rectangles are distinguished as well. A hidden one would require two double columns. A singleton presentation must use column zero as its three-black-corner partner and is then uniquely determined. A vertical two-point presentation likewise determines the central double. A horizontal two-point presentation has its other black row in the intersection of two column black sets; that intersection has at most one row because at most one column is a double. An oblique two-point presentation already determines its axis-aligned rectangle. Thus no two axis-aligned rectangles coincide in presentation.

### Consequence for insertion

There are no hidden tilted rectangles, singleton presentations, vertical presentations, or tilted collisions. The only axis-rival tests that can arise are horizontal and oblique tests already excluded above. Thus the isolated configuration is valid even when rivals are tested against an arbitrary full pair set `F` containing `D`.

With memory `L=2W_h`, the finite word

\[
 1^L\,\{a,b\}\,h^L
\]

therefore gives a marked bridge from `1^L` to `h^L`. Its proof uses no assumption about other components' entropy. The single-switch boundary paths connect those states in one primitive component for every partition, so every edge has positive insertion weight on that component. The unresolved issue is whether this component uniquely dominates, not whether its insertion operators are positive.

## 5. Correction to the boundary case of law (P)

Section 9 of `../../2026-11-07/REPORT_1xh_construction.md` says that when one point of the vertical completion is on row 1 or `h`, the event becomes a unit clause. This misses the singleton rival created when that boundary point is blackened.

Suppose a tilted rectangle has a black diagonal and its other diagonal is the in-grid vertical pair `W=(c,u),Z=(c,v)`, with `{u,v}` in the full pair set `F`. If both points are white, the pair has an axis rival. If exactly one is black, the other has a singleton axis rival through the same edge `{u,v}`. If both are black, the rectangle is hidden; in the Pythagorean family below it has an even side vector, so bisection proves invalidity. Therefore changing the sea at column `c` cannot remove the obstruction.

Here is a minimal patch in the admissible `h=3 mod 4` family. At height seven use doubles

\[
 \{1,2\}\text{ at column }0,\qquad
 \{4,5\}\text{ at column }4,\qquad
 \{1,6\}\text{ at column }8.
\]

The tilted rectangle and its axis rival are

\[
 R=\{(0,2),(4,5),(2,1),(2,6)\},
\]
\[
 T=\{(8,1),(8,6),(2,1),(2,6)\}.
\]

Their symmetric difference consists of four required double points. If the middle at column 2 is row 1, both presentations are `{(2,6)}`. If it is row 7, both presentations are `{(2,1),(2,6)}`. Every other singleton choice at column 2 also gives equal presentations. The checker tests all seven choices directly.

Thus this is an order-only obstruction, not a unit constraint. It also persists when the middle is allowed to be any row. The earlier exact compiler is unaffected because it uses rectangle symmetric differences, and the count 384 has now been independently checked against all actual presentations.

## 6. What a random quadratic-width placement must overcome

There is a quantitative version of the preceding obstruction. Let `q=floor(h^2/4)` and place the `q` parity edges uniformly without replacement into `m` columns. The remaining columns can be filled with seas in any way, even after inspecting the edge placement.

For an odd positive integer `d`, black points

\[
 (x,a),\qquad (x+4d,a+3d)
\]

have an in-grid vertical completion

\[
 (x+2d,a-d),\qquad (x+2d,a+4d)
\]

whenever `d+1<=a<=h-4d`. Its row difference is `5d`, which is odd, so its edge belongs to the parity graph. The preceding argument makes this a sea-independent invalidity certificate. The horizontal reflection gives the reversed row assignment as well.

For opposite-parity rows `a,b`, the number of ordered distinct edge pairs with `a` in the first edge and `b` in the second is

\[
 \deg(a)\deg(b)-1=q-1.
\]

Every specified ordered edge pair occupies two specified columns with probability `1/(m(m-1))`. By linearity of expectation, the expected number of these certificates is exactly

\[
 \frac{2(q-1)}{m(m-1)}
 \sum_{\substack{d\ge1\text{ odd}\\5d<h}}
 (m-4d)(h-5d),
\]

with terms omitted if `4d>=m`. At `m=Cq` for fixed `C>=1`, this is

\[
 \frac{h^2}{10C}+O_C(h).
\]

At rigid spacing four, a uniform permutation of the edges has the corresponding expectation

\[
 \frac2q\sum_{\substack{d\ge1\text{ odd}\\5d<h}}
 (q-d)(h-5d)=\frac{h^2}{10}+O(h).
\]

These formulas count certificates, allowing overlaps. They do not prove that a valid random placement has vanishing probability, or rule out a local-lemma or alteration construction. They do show that a union bound with no double-order repair, or an alteration that only changes seas, cannot establish the desired construction.

The sea-entropy argument does not directly supply that repair. Its odd-row alphabet suppresses odd-distance singleton rivals when all black points are odd. An inserted even double point destroys that protection: together with two odd sea points it can create a right angle whose completion has even row, giving an axis rival against the odd sea point in the completion column.

## 7. Recommended construction direction

The rigid `1,x,h` family remains a useful exact testbed. Its fixed-order middle problem is tractable, it eliminates one-double right angles at the admissible heights, and its obstruction certificates are explicit. The 384 calculation confirms that a successful order can leave substantial middle freedom.

For a general quadratic-width theorem, I would prioritize controlled free-sea gaps over further unrestricted rigid-order annealing. The reason is limited but concrete: the direct split of the two-adic mechanisms has proved capacity obstructions, and new order-only Q configurations appear at the first unresolved admissible height 15. This is not a proof that the rigid family fails.

The relaxation should preserve a separate analytic task: construct a double placement avoiding the immutable three-double and four-double certificates, including the corrected P family. Free gaps can then address constraints whose symmetric difference genuinely uses sea points. They cannot repair Q/T certificates supported entirely on doubles. A direct probabilistic placement is still worth investigating, but it needs an explicit mechanism for repairing or avoiding its double-supported obstructions; the existing sea local lemma alone does not provide one.
