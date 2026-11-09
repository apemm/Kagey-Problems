# A finite cover by fully filled period-seven profiles

9 November 2026. For every sufficiently large height \(h\), a fixed
finite number of fully filled period-seven sea profiles provide
compatible one-label substitutions for every parity label outside
\(O(h^{3/2})\) exceptional labels. The exceptional labels can be
handled at total width \(O(h^2)\) by the established positional
construction. Each profile also has a filled \(O(h^2)\) collar to
constant row \(h\).

This removes the need to prescribe a different private sea around each
ordinary label. It does not, by itself, exclude obstructions involving
two or more substituted labels. A full quadratic construction still
requires that placement step.

## 1. The profile and the normalization

Let \(\chi\) denote the quadratic character modulo seven. Choose
\(L<F<H\) with
\[
H-L\equiv g\ne0\pmod7,\qquad F-L\equiv3g\pmod7,
\tag{1}
\]
and physical row parities
\[
F\equiv L\pmod2,\qquad H\not\equiv L\pmod2.
\tag{2}
\]
The periodic sea is
\[
s(x)=
\begin{cases}
F,&x\equiv0\pmod7,\\
L,&\chi(x)=-1,\\
H,&\chi(x)=1.
\end{cases}
\tag{3}
\]
A double substitution replaces the filler point at a column
\(x\equiv0\pmod7\) by its two assigned opposite-parity rows.
It does not retain a third point in row \(F\).

The allowed inserted row residues are
\[
r-L\in\{0,5g\}\pmod7.
\tag{4}
\]
For modular calculations, translate \(L\) to zero and divide all
vertical coordinates by \(g\). Divide horizontal coordinates by
\(g\) or \(-g\), choosing the sign for which the divisor is a
quadratic residue. This preserves the norm and perpendicularity
equations up to a nonzero common factor and keeps the sea character
convention unchanged. The normalized levels are therefore
\[
L=0,\quad F=3,\quad H=1,
\quad r\in\{0,5\}\pmod7.
\]
Nonzero low columns are \(3,5,6\); nonzero high columns are
\(1,2,4\). Filler columns are zero.

## 2. What the finite-field calculation excludes

The exact mixed-support equations for black side \(A,B\) and black
diagonal \(C,D\) are
\[
|B-A|^2=|D-C|^2,\qquad
(B-A)\cdot(C+D-A-B)=0.
\tag{5}
\]
The common corner pair is \((C+D\pm(B-A))/2\). A zero in a table
below refers to a column residue, not an empty column.

First consider one inserted point and binary sea points only.
For an inserted residue 5, the punctured mod-seven proof applies:
\(\chi(r(H-r))=1\), and the mixed calculation in
`mod7_inset_profile_cover.md`, Section 1, excludes every case that
can lie in the smaller strip \([L,H]\).
For inserted residue zero, a central right angle would require a
product of two nonzero sea columns to be zero. In the remaining mixed
case, the notation of that calculation gives
\(a+b-1=0\), where \(a\) is a nonzero square and \(b\) a
nonsquare. The only possible pair is \((a,b)=(2,6)\), for which
\(1-(b-a)^2=6\) is a nonsquare. The norm equation is impossible.
The horizontal-side case is excluded by \(\chi(-1)=-1\), as before.

Now add one filler point. Up to exchanging endpoints within each
black pair, every modular mixed case is in the following table:

| Inserted residue | Black side | Black diagonal | Outcome |
| --- | --- | --- | --- |
| 5 | any placement of the filler and two binary points | remaining two points | no solution |
| 0 | filler and high point | inserted point and high point | possible modulo seven |
| 0 | low and high points | inserted point and filler | possible modulo seven |
| 0 | any other pairing | remaining two points | no solution |

In the first surviving row, the normalized high-column residues are
1 for the side and 2 for the diagonal. In the second, the side's
low/high column residues are 3 and 2. These are obtained by substituting
the three low and three high residues in (5). There are only three
pairings and two choices of which pair is the side. In particular,
there is no surviving central-side case.

The two survivors cannot fit in the ambient strip when
\[
r>F+2(h-H),\qquad r+F<H-L+2.
\tag{6}
\]
The first has a common upper row \(H+(r-F)/2\). The second has a
common lower row \((r+F-H+L)/2\).

With two filler points and one binary point, every mixed case vanishes
modulo seven. A filler/filler pair has zero norm modulo seven; a pair
containing the binary point cannot have zero norm because \(-1\) is
a nonsquare. In the remaining pairing, substitution in (5) forces the
inserted and binary row residues to agree, and then forces the nonzero
binary column to be zero. With three fillers, one black pair has zero
norm and the inserted/filler pair has nonzero vertical norm.

The three-black calculation is equally short. Inserted residue 5 has
no modular right angle involving a filler and a binary point.
Inserted residue zero has just two types:

| Right-angle vertex | Other black rows | Completion row |
| --- | --- | --- |
| inserted point | filler and low | \(F+L-r\) |
| high sea point | inserted point and filler | \(r+F-H\) |

They lie below row one for the bulk rows chosen below. With two filler
points, an angle at the inserted point is excluded modulo seven; an
angle at a filler would require a different point in its own column.

These calculations are geometric exclusions for one inserted row.
Vertical-pair axis rivals require a separate treatment in Section 5.

## 3. Choosing actual rows and excluding zero-label rivals

The following deliberately generous constants make all choices
explicit. Assume \(h\ge10^{10}\). For every
\(L\in\{1,\ldots,14\}\) and \(g\in\mathbb F_7^*\), choose
\(H\) among the fourteen integers in \([h-195,h]\) satisfying
\[
H-L\equiv g\pmod7,\qquad H\not\equiv L\pmod2.
\]
Require
\[
j(H-L+j)\text{ not a square}
\quad(1\le j\le L-1).
\tag{7}
\]
Each fixed \(j\le13\) excludes at most one candidate. Indeed, two
distinct square values of \(j(G+j)\) at these large spans differ in
\(G\) by more than 182. There are at most thirteen bad candidates,
so one of the fourteen remains.

Put \(M=h-H\le195\). Choose \(F\) among the 196 integers in
\([1000,3743]\) satisfying (1) and \(F\equiv L\pmod2\), requiring
\[
j(H-F+j)\text{ not a square}
\quad(1\le j\le M).
\tag{8}
\]
For a fixed \(j\le195\), consecutive possible values of \(F\) are
separated by more than 2743: their square roots are at least
\(\sqrt{j(h-4000)}\), giving separation greater than
\(2\sqrt{(h-4000)/j}\). Thus each \(j\) excludes at most one
candidate, and at most 195 are excluded.

These choices ensure
\[
F-L>2\max(L-1,h-H),\qquad H-F>2\max(L-1,h-H).
\tag{9}
\]
Thus the punctured one-point proof for filler residue 3 remains valid
in the larger strip: every previously out-of-strip three- or four-corner
case still lies outside \([1,h]\).

The filled sea (3) has no tilted three-black rectangle. Cases with
zero or one filler follow from the binary and punctured calculations
and (9). With two fillers, a right angle at the binary point would
give a sum of two squares equal to zero modulo seven with a nonzero
column coordinate; an angle at a filler is impossible by the
one-point-per-column rule. Three fillers are collinear.

For four-cell mixed supports, zero or one filler is already covered.
Two fillers and two binary points on the same level are a degenerate
two-level case: equal norms and the common vertical midpoint force
parallel diagonals or coincident centers. If the binary points are on
opposite levels, their total row parity is odd by (2). With three
fillers, one pair has zero norm modulo seven and the binary/filler
pair has nonzero norm by anisotropy. Four fillers are collinear.
Same-side and same-diagonal collisions reduce to a hidden rectangle,
and there are no hidden rectangles because there are no three-black
tilted rectangles and only one point in each column.

Finally consider virtual vertical-axis rivals from the final parity
graph. A diagonal joining the low and high levels can fit a vertical
alternative only if its hypotenuse is \(H-L+2j\), where
\(1\le j\le\min(L-1,h-H)\). Its horizontal gap squared is
\(4j(H-L+j)\), excluded by (7). The filler/high case is similarly
excluded by (8). Low/filler pairs, and pairs on the same row, have the
same physical parity and cannot rival a parity-graph axis side.
There are no singleton rivals because there are no three-black tilted
rectangles. Hence the background is valid relative to the full final
parity graph.

## 4. Substituting an opposite-parity double

Take both central rows in \([5000,h-5000]\), with residues in (4).
They satisfy (6), and every distance from the relevant low/high
boundaries exceeds the corresponding outer-margin allowance.
For example, \(r-F\ge1257>390\), and
\(r+F\le h-1257<H-L+2\). Thus Sections 1–2 exclude all one-point
three-black and ordinary four-cell obstructions.

No genuinely two-row one-label obstruction appears. Every sea level
is below both central rows or above both, so a tilted right angle
using both central points is impossible. In a four-cell support using
both central points, two remaining points on the same sea level have
odd total row parity. Points on the low and filler levels also have
odd total row parity because those levels have the same physical
parity. The remaining choices are low/high or filler/high; these
bracket both central rows, so the two-boundary mixed inequality in
`binary_boundary_one_label_separability.md`, Section 2, excludes them.
The two central rows have opposite parity throughout this argument.

All tilted singleton collisions are absent because the foregoing
calculations exclude every three-black tilted rectangle in the
one-label substitution. Axis collisions are controlled by the fixed
row-pair graph. Thus only a one-point vertical rival remains to be
removed.

## 5. A small exceptional set of central rows

For each selected profile, exclude the boundary rows outside
\([5000,h-5000]\), and all rows satisfying any of
\[
\begin{array}{ll}
j(r-L+j)\text{ square},&1\le j\le L-1,\\
j(r-F+j)\text{ square},&1\le j\le F-1,\\
j(H-r+j)\text{ square},&1\le j\le h-H.
\end{array}
\tag{10}
\]
Only bulk rows between \(F\) and \(H\) need these tests. For fixed
\(j\), there are \(O(\sqrt h)\) solutions, by writing the square
as \(s^2\) with \(s=O(\sqrt h)\). The numbers of profiles and
values of \(j\) are absolute constants. Their union \(E_h\)
therefore has size \(O(\sqrt h)\).

These are exactly the possible small-overhang vertical alternatives
of a central/sea diagonal, with extra cases harmlessly overcounted.
For example, against low level \(s\in\{L,F\}\), the hypotenuse is
\(r-s+2j\), and the horizontal gap squared is
\(4j(r-s+j)\). Against the high level the analogous formula uses
\(H-r\). Every parity label with both endpoints outside \(E_h\)
and obeying (4) can therefore be substituted at any hole without a
zero-label or one-label obstruction.

Every row pair is covered by one of at most 84 profiles. Choose
\(L\equiv a\pmod7\). If \(a\not\equiv b\pmod7\), take
\(g=(b-a)/5\pmod7\); otherwise take any nonzero \(g\).
The two endpoint classes are then 0 and 5, or both zero. Physical
row parities are unaffected by this residue choice.

Only \(O(h^{3/2})\) parity labels meet \(E_h\). The established
uniform positional lemma for an arbitrary assigned \(n\)-label
subfamily has internal width \(O((n+1)T(h)^2)\), where
\(T(h)=h^{o(1)}\). Applying it to the exceptional labels costs
\(h^{3/2+o(1)}\) internally, plus a constant number of \(O(h^2)\)
collars. Thus the exceptions cost \(O(h^2)\) in total. This uses
the positional lemma, not an interior constant-baseline star.

## 6. Filled collars

In the background (3), every hole column may independently choose
either \(F\) or \(H\), without invalidating the sea. The proof above
for two or more filler points is unchanged. With one filler point,
the punctured calculation still works when some high sea columns
are zero modulo seven. A central-side equation has the nonzero
product \((F-L)(H-F)\), so its side column cannot be zero. In the
normalized calculation, an additional zero high diagonal column can
only support central residue 5, whereas the filler has residue 3.
After the double reflection for the high-side case, the newly allowed
zero is a low column; that case requires central residue 4, not the
reflected filler residue 5. In the horizontal-side case the negative
square product is nonzero, forcing both side columns to remain
nonzero. All formerly exterior cases remain exterior by (9).
The vertical-rival filters (7)–(8) apply to every horizontal gap,
including zero-residue high columns.

Let \(W=h^2\), a convenient upper bound for the horizontal span of
one tilted rectangle. Two intersecting tilted rectangles have union
span at most \(2W\). Virtual axis rivals use only the tilted columns
and the retained point in a white column; their distant owner is
already represented by the fixed final graph.

Beyond a core, first keep the periodic profile unchanged for \(2W\)
columns. Replace all further filler points by \(H\), while retaining
the binary character choices elsewhere. After a further \(2W\)
columns, change the remaining binary choices to constant row \(H\).
The intermediate region is valid by the independent hole-choice
property. Beyond the last filler the sea uses only \(L,H\), and
arbitrary choices of these two rows are valid here: the span,
opposite-parity, and vertical-rival arguments of Section 3 do not
depend on the character pattern. The buffers prevent a new local
support from reaching both a filler and the changed distant bits.

Finally pass from constant \(H\) to constant \(h\) through the
adjacent rows, using the established adjacent-row bridge and a
\(2W\) constant buffer between successive switches. There are at
most 195 switches. The same construction works at the left end.
All collars are fully filled and have width \(O(h^2)\), with an
absolute constant independent of the core.

## 7. Scope of the resulting reduction

Assign each ordinary label to one of its safe profiles. At a label
column replace the filler by the two assigned rows; leave every
unused hole filled by its original filler. There are no private sea
prescriptions to reconcile. Any remaining violation must involve at
least two labels, apart from the separately handled exceptional
subfamily. A placement theorem controlling those multi-label events
can now be combined with the collars above. The present theorem does
not claim that an arbitrary order or placement of the labels is valid.

## 8. Reproducible finite checks

`verify_filled_mod7_profiles.py` exhausts the one-filler mixed pairings
and right-angle positions over \(\mathbb F_7\), checks the two- and
three-filler exclusions, and checks all 84 central-side residue cases
needed for the arbitrary-hole-choice collar. It also constructs and
checks all 84 profiles at each of 28 consecutive heights beginning at
\(10^{10}\), including all square filters, margin inequalities, and
49 row-residue pairs. All checks pass; the exact output is
`filled_mod7_profile_checks.json`. The finite checks support the
analytical argument and do not replace the uniform existence proof.
