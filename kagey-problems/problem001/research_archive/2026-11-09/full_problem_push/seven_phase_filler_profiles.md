# Seven filler rows and two occupied phases

9 November 2026. The fully filled period-seven profile admits a
period-49 refinement with seven distinct low filler rows. The refined
sea is valid, has the same one-label insertion property, and retains
filled quadratic-length collars. If two selected hole phases are
completely occupied by labels, the refinement excludes every
two-label horizontal mixed support in that region. A separate
two-phase rule excludes the remaining opposite-parity label-root
triangles in mixed-residue blocks.

These are construction lemmas. They do not yet provide a placement
of all labels avoiding the other multi-label collisions.
The repaired proof has passed independent review; see
[seven_phase_fillers_independent_audit.md](seven_phase_fillers_independent_audit.md).

## 1. The refined sea

Use odd \(L\), even \(H\), and nonzero
\(g=H-L\pmod7\). Choose an odd low row \(F_0\) with
\(F_0-L\equiv3g\pmod7\). Choose \(\kappa\in\mathbb F_7^*\)
such that
\[
\chi(\kappa g)=-1,\qquad \chi(1+4\kappa^2)=-1.
\]
One uniform choice is \(\kappa=-1\) when \(g\) is a square,
and \(\kappa=1\) when \(g\) is a nonsquare. Then
\(1+4\kappa^2=5\) is a nonsquare. For \(j\in\mathbb Z\), let
\[
t_j\in\{0,1,\ldots,6\},\qquad
t_j\equiv\kappa j\pmod7,
\qquad F_j=F_0+14t_j.
\tag{1}
\]
At a hole column \(x=7j\), use row \(F_j\). At other columns,
retain low row \(L\) when \(\chi(x)=-1\), and high row \(H\)
when \(\chi(x)=1\). This is a period-49 singleton sea. The seven
filler rows are distinct, have the same physical parity, and have
the same normalized residue three modulo seven.

For any two fillers, write their coordinate difference as
\(7(d,v)\). Then
\[
v\equiv2\kappa d\pmod7.
\tag{2}
\]
Moreover, equal hole phases imply equal actual filler rows.

The key nonvanishing fact is
\[
x+2\kappa(s-F_0)\not\equiv0\pmod7
\tag{3}
\]
for any binary sea point \((x,s)\). At the low level, a zero would
require \(x=6\kappa g\), a quadratic residue rather than a low
column. At the high level it would require \(x=4\kappa g\), a
nonsquare rather than a high column. The assertion also holds for
a high point at a hole, where \(x=0\pmod7\).

## 2. Zero-label three-black rectangles

Cases with zero or one filler are the existing punctured-profile
calculation, applied separately to each bounded row \(F_j\).
Choose all filler rows well above the lower outer margin and well
below the bulk, as in Section 5.

For two fillers and one binary point, an angle at the binary point
is impossible modulo seven by anisotropy of \(x^2+y^2\): both
filler points have column zero and normalized row three, whereas the
binary point differs in at least one coordinate. At a filler vertex,
divide the scalar product by seven and use (2). Equation (3) forces
the other filler to have the same phase. Its actual row is then the
same, so it gives a horizontal leg. The other leg would have to be
vertical in the same column, impossible in a singleton sea.

For three fillers, divide both side vectors by seven. Their scalar
product modulo seven is
\[
(1+4\kappa^2)d_1d_2.
\]
The coefficient is nonzero because \(-1\) is a nonsquare modulo
seven. One leg must have zero phase difference, hence equal actual
row. The horizontal-leg argument again excludes the angle.

Thus the refined sea has no three-black tilted rectangle.

## 3. Zero-label mixed supports

The zero-/one-filler cases remain the existing profile proof.
Three fillers and one binary point are impossible modulo seven:
one black pair has zero norm, while the other has nonzero norm by
anisotropy. Two fillers and binary points on opposite levels have
odd total physical row sum, so their common corner pair is not integral.

Consider two fillers and two binary points on the same level \(s\).
If the fillers form the black side, the norm equation forces the
binary columns to agree modulo seven. Dividing perpendicularity by
seven then gives
\(d[x+2\kappa(s-F_0)]=0\). Thus (3) forces the filler phases to
agree.

If instead the fillers form the black diagonal, the binary side is
horizontal. Its midpoint has column zero modulo seven, and its
length is zero modulo seven, so both binary columns are holes. This
is impossible in the unmodified background. It must nevertheless
be checked for the high-hole replacements used in Section 4.
Divide the norm equation by 49. Modulo seven it becomes
\[
\lambda^2=(1+4\kappa^2)d^2.
\]
The coefficient is a nonsquare, so \(d=0\). The filler phases,
and hence their actual rows, agree. Both black pairs are then
horizontal, giving a degenerate diagonal rectangle. This is why
the nonsquare norm condition on \(\kappa\) is needed.

For the crossed pairing, translate the first filler to \((0,F)\).
Write the other as \((7d,F+7v)\), and the binary points as
\((x,s),(x+7t,s)\). The zeroth-order norm and perpendicularity
equations first force their binary columns to agree modulo seven.
Put \(y=s-F\). After division by fourteen in the norm equation,
and by seven in perpendicularity, the first-order congruences are
\[
x(t-d)=yv,\qquad x(t+d)=-yv\pmod7.
\tag{4}
\]
For a nonzero binary column, they give \(t=0\) and
\(d[x+2\kappa y]=0\), so again \(d=0\).
For a high hole point, \(x=0\), while \(y\ne0\); (4) gives
\(v=0\), hence \(d=0\) directly. In every case the actual
filler rows agree. A mixed support using two points on each of two
fixed rows is degenerate: horizontal-pair roles have parallel
diagonals, while crossed roles have the same vertical center and
equal vertical differences, forcing the remaining center difference
to vanish. A vertical black side would repeat a column.

Finally take four fillers. After dividing coordinates by seven,
their phase points lie on the nonisotropic line of direction
\((1,2\kappa)\). Equal norms and perpendicularity imply that
the side and diagonal have the same unordered pair of phases, unless
both pairs have equal phases internally. In the first case their
actual row pairs agree, so equal lengths and perpendicularity force
degeneracy. In the second case both actual pairs are horizontal,
also giving degeneracy.

This excludes every zero-label mixed support. Same-side and
same-diagonal collisions reduce to hidden rectangles, which are
already excluded by the three-black result.

## 4. One-label substitutions and arbitrary high-hole replacements

Insert an ordinary opposite-parity double at any hole, with both
rows in normalized classes zero or five and well inside the bulk.
The existing one-label proof applies to every configuration with at
most one filler, since only its normalized residue, bounded height,
and physical parity were used.

With two fillers, an angle at the inserted point is impossible
modulo seven. At a filler, the horizontal scalar-product term is
divisible by 49, while the other term is the filler row difference
times a number nonzero modulo seven. Equation (2) forces the filler
phases to agree, giving the same horizontal-leg contradiction as
before. The mixed cases with two or three fillers are already
excluded modulo seven by the original one-label calculation.

For a support using both opposite-parity rows of the inserted double,
two low filler rows still have the same physical parity, so the
four-point parity exclusion applies. A filler and a high point
bracket both inserted rows, so the original two-boundary inequality
applies. No new genuinely two-row one-label case appears.

All vertical rivals are removed by the same square filters as before,
now imposed for each of the seven filler rows. The excluded central
rows are still a union of constantly many \(O(\sqrt h)\) sets.

The zero-label arguments also permit arbitrary replacement of any
filler by \(H\). Equation (3) remains nonzero at high hole columns;
the high-hole version of (4), and the filler-diagonal/high-horizontal-
side norm test, were included explicitly. The old
one-filler calculation already permits high hole points. Therefore
the same filled collars work: keep the refined sea beyond the labels,
replace all later fillers by \(H\), and then pass through the binary
sea to constant \(H\) and adjacent-row bridges to the boundary.
Their width remains \(O(h^2)\).

## 5. The finite profile choices still exist

Fix an absolute upper bound on the allowed lower row \(L\).
Choose \(H=h-O(1)\), of the required residue and opposite parity,
from more candidates than the number of lower-overhang square tests.
Each test excludes at most one candidate for sufficiently large \(h\).

Next choose \(F_0=O(1)\), with the required residue and parity,
from more than seven times the number of upper-overhang tests.
For each candidate, the seven filler rows are \(F_0+14t\),
\(0\le t\le6\). Each fixed test and each \(t\) excludes at
most one candidate, by the same square-gap estimate. The candidate
interval and its starting point are absolute constants. Choose the
starting point above twice both outer margins, and choose the bulk
margin above the largest filler row plus twice those margins.

This proves existence of a constant-sized cover with the refined
fillers. It also permits \(L\) to range over \([1,98]\), if the
7-adic condition in Section 7 is desired. No new growing divisor
factor enters the exceptional-label cost.

## 6. Completely occupying two hole phases eliminates the horizontal pair role

Suppose every hole of phases zero and one in a finite region is
occupied by a distinct real label. The holes of phases two through
six retain their distinct rows from (1). Suppose all these labels
belong to one oriented mixed-residue block.

Then no horizontal mixed support contained in that region uses
exactly two labels. Binary-sea horizontal sides are excluded by the
argument in mod7_multilabel_reductions.md. For a filler horizontal
side, equal actual filler rows imply that both endpoints have the
same hole phase \(j\in\{2,3,4,5,6\}\). Its horizontal length is
divisible by 49.

The black label diagonal must have endpoints of the same physical
parity, since otherwise its midpoint row is not integral. Their
row difference is divisible by fourteen. Divide its norm equation
by 49 and reduce modulo seven. The side length is zero modulo
seven, so anisotropy forces both the coarse horizontal difference
and the coarse vertical difference of the label diagonal to vanish.
The midpoint identity then forces both label columns to have hole
phase \(j\). But label phases are zero or one, a contradiction.

A label/sea horizontal side would identify a bulk and sea row.
A two-label horizontal side cannot reuse either endpoint column in
a nonhorizontal equal-length diagonal. Its remaining possible
diagonal consists of two sea points. Two different filler rows need
an additional check: division of the norm equation by 49 gives
\(e^2=(1+4\kappa^2)d^2\pmod7\). The nonsquare coefficient forces
\(e=d=0\), so the filler rows agree and the diagonal rectangle is
degenerate. A filler/low binary pair is excluded by norm anisotropy
modulo seven; a filler/high pair has odd physical row sum. Two binary
points either have odd row sum or form a horizontal diagonal, again
degenerate. This covers every horizontal role.

This lemma concerns supports contained in the stated region. Filler
collars outside it can create additional boundary events. A full
construction must still control them.

## 7. A two-phase exclusion of the remaining mixed-endpoint triangle

Assume each label's odd endpoint \(a\) satisfies
\(v_7(a-L)=1\). This can be arranged by choosing \(L\) among
finitely many lower shifts of the prescribed residue and parity.
Define
\[
\sigma(e)=\chi\!\left(5g\frac{a-L}{7}\right)\in\{-1,1\}.
\]
Put a label of sign \(+1\) only in holes \(x=7i\) with
\(i\equiv0\pmod7\), and a label of sign \(-1\) only in
holes with \(i\equiv1\pmod7\).

The only opposite-parity label-root triangle permitted by the
modulo-seven calculation in a mixed-residue block has its root at
the odd endpoint \(a\), its other label point at an even endpoint
\(c\), and its sea point at low row \(L\). Writing the center
gap as \(7d\) and the sea offset as \(z\), its right-angle equation
requires
\[
d z\equiv5g(a-L)/7\pmod7,\qquad\chi(z)=-1.
\tag{5}
\]
For labels of the same sign, \(d=0\pmod7\), contradicting the
nonzero right side. For opposite signs,
\(\chi(d)=\sigma(e)\), whereas (5) requires
\(\chi(d)=-\sigma(e)\). Thus no such triangle occurs.

Every label retains a constant-density placement domain. Combining
complete occupation of these two phases with Section 6 would remove
both leading pair families. This does not yet handle the remaining
mixed supports, higher-arity supports, boundary interactions, or
the separate equal-residue label blocks.

A concrete remaining mixed support shows why those qualifications
matter. Take \(g=L=1\), odd label points
\[
A=(7,421),\qquad C=(350,505),
\]
and low sea points
\[
B=(367,1),\qquad D=(122,1).
\]
The side \(AB\) and diagonal \(CD\) both have squared norm
306000, and their common corner pair is
\[
W=(416,43),\qquad Z=(56,463).
\]
Both labels have sign \(-1\), are in hole phase one, and have
\(v_7(a-L)=1\). Both sea points are in nonzero low columns.
The point \(W\) is white. The point \(Z\) is in an occupied
hole phase, but its color cannot repair the equal presentations:
the symmetric difference consists of the four prescribed black
points. Thus full occupation and the phase rule do not automatically
exclude same-parity two-label/two-low-sea mixed supports.

For arbitrarily large versions, multiply every offset from \((7,1)\)
by an integer \(t\equiv1\pmod7\), and take \(h=1000t\).
The six points become
\[
\begin{array}{lll}
A=(7,1+420t),&B=(7+360t,1),&C=(7+343t,1+504t),\\
D=(7+115t,1),&W=(7+409t,1+42t),&Z=(7+49t,1+462t).
\end{array}
\tag{6}
\]
All six rows lie in the strip. The two inserted rows are bulk rows
for sufficiently large \(t\), and the residue, valuation, and
phase conditions persist. Norms scale by \(t^2\), and
perpendicularity is unchanged.

This family is compatible with actual admissible profile choices,
not just formal residues. Take \(L=1\), \(H=1000t-4\),
\(F_0=1005\), and \(\kappa=-1\). All required residues,
parities, and margin inequalities hold for sufficiently large \(t\).
The finitely many background and central-row square filters are
nonconstant linear functions of \(t\). Each is square at only
\(O(\sqrt T)\) integers \(t\le T\). Thus infinitely many
\(t\equiv1\pmod7\) avoid all the filters simultaneously.
For those \(t\), choose the even partners in their required
residue class outside the remaining \(O(\sqrt h)\) exceptional
rows. Both doubles are individually valid substitutions, while
their prescribed relative placement has the mixed collision (6).

## 8. Exact checks and the strengthened slope hypothesis

`verify_seven_phase_fillers.py` checks all six nonzero choices of
\(g\), with the uniform slope choice \(\kappa=\pm1\). Its
16,000-plus finite-field cases cover binary transversality, crossed
filler pairs, four-filler phase pairings, horizontal norms, and the
Paley angle filter. The exact output is
`seven_phase_filler_checks.json`.

Independent review identified the need for the nonsquare norm
condition, in addition to \(\chi(\kappa g)=-1\). The weaker
condition alone permits \(g=1,\kappa=3\). In that case fillers
at columns zero and 56 have rows \(F_0,F_0+42\), and two high-hole
points at columns \(-7,63\) form a horizontal black side of length
70. Their common white pair is
\((-7,F_0+21),(63,F_0+21)\), giving a genuine mixed collision.
The checker preserves this counterexample and checks the repaired
norm condition. Sections 3 and 6 explicitly include the two roles
that require it.
