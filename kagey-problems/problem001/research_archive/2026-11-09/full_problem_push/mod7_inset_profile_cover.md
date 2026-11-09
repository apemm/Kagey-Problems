# Eighteen compatible punctured sea profiles

9 November 2026. For every sufficiently large height, at most eighteen
period-seven punctured sea profiles cover every odd/even row pair
outside a set of \(O(\sqrt h)\) exceptional rows. Each covered label
can be inserted at any hole without a zero-label or one-label
obstruction, even with the complete final parity graph supplying axis
rivals. This is a compatibility theorem for private prescriptions.
It does not yet arrange all labels or fill unused holes.

## 1. The mod-seven one-point calculation

Let \(\chi\) be the quadratic character modulo seven, with
\(\chi(-1)=-1\). For sea rows \(L<H\), put a black point in row
\(L\) at each nonzero residue with \(\chi(x)=-1\), and in row
\(H\) where \(\chi(x)=1\). Leave every column \(x\equiv0\pmod7\)
empty. A central row \(r\) is allowed when
\[
r-L\in(H-L)T\pmod7,\qquad T=\{3,4,5\}.
\tag{1}
\]
Here \(H-L\not\equiv0\pmod7\). Equivalently,
\(\chi((r-L)(H-r))=1\).

First consider geometry inside the smaller strip \([L,H]\), and
translate \(L\) to zero. Write \(G=H-L\) and \(r\) for the translated
central row. Three black corners would require boundary points at
nonzero columns \(u,v\) with
\(uv=r(G-r)\). Their characters would have to be opposite, whereas
the product has character one. Vertical rivals extend outside the
smaller strip.

For a mixed four-cell support, a horizontal black side with the central
point in the opposite black diagonal forces the product of its two
nonzero sea columns to be a negative square. Both side points have the
same sea row, so this contradicts \(\chi(-1)=-1\). A diagonal with two
sea points on the same boundary puts a common white point outside the
smaller strip. A side joining opposite boundaries, with the central
point in the diagonal, does the same.

The remaining case has black side \((0,r),(x,0)\) and black diagonal
\((z,0),(w,G)\). Reflection in both coordinates reduces the high-side
case to this one. Its equations are
\[
x(z+w-x)=r(G-r),\qquad (w-z)^2+G^2=x^2+r^2.
\tag{2}
\]
All three sea columns are nonzero modulo seven. Set
\(a=z/x\), \(b=w/x\), \(c=a+b-1\), and
\(d=1-(b-a)^2\). Then \(a\in\{1,2,4\}\),
\(b\in\{3,5,6\}\), and \(c\) is a nonzero square. The only
possibilities are
\[
(a,b)=(2,3),(4,5),(4,6).
\]
The corresponding values of \(d-2c\) are \(6,5,0\).
Writing \(u=r/x\), \(v=G/x\), equations (2) imply
\[
u(v-u)=c,\quad v^2-u^2=d,\quad
u^2(d-2c)=c^2.
\]
The first two nonzero values of \(d-2c\) are nonsquares, and the third
is zero while \(c\ne0\). All three cases are impossible.

For an opposite-parity double whose two rows obey (1), no genuinely
two-row one-label support remains. The proof in
`binary_boundary_one_label_separability.md` applies because both
central rows lie strictly between the sea rows. Its two-central mixed
contradiction does not require the sea rows to be the outer boundaries
of the ambient strip.

## 2. Choosing inset sea rows without a zero-label obstruction

Assume \(h\ge1000\). For each \(L\in\{1,2,3\}\) and
\(d\in\mathbb F_7^*\), choose \(H\) satisfying
\[
h-41\le H\le h,\qquad H-L\equiv d\pmod7,
\qquad H-L\text{ odd}.
\tag{3}
\]
There are exactly three candidates, spaced fourteen apart. We also
require
\[
j(H-L+j)\text{ is not a square for }1\le j\le L-1.
\tag{4}
\]
Such a candidate always exists. There are at most two values of \(j\).
For \(j=1\), the bad spans are \(n^2-1\); for \(j=2\), they are
\(2n^2-2\). Above span 956, consecutive values in either sequence
are more than twenty-eight apart. Each sequence therefore excludes
at most one of the three candidates.

Here is the reason for (4). A black diagonal joining the two sea rows
has an in-strip vertical alternative only if its hypotenuse is
\(G+2j\), where \(G=H-L\) and
\[
1\le j\le\min(L-1,h-H),\qquad
(\text{horizontal gap})^2=4j(G+j).
\]
Condition (4) excludes every such zero-label vertical rival. A diagonal
whose two sea points are on the same row has an even vertical
alternative, so it cannot rival an axis side in the parity graph.

All other zero-label failures are also absent. Three sea corners
complete beyond the ambient strip, since the sea span exceeds both
outer margins. In a four-cell support, a three-to-one split between
the sea rows has odd total row parity, because \(L,H\) have opposite
parity. A two-to-two split is degenerate: cross-boundary pairs have
the same vertical midpoint, and equal norms and perpendicularity force
coincident centers or parallel diagonals. Same-side and same-diagonal
collisions would give a hidden rectangle, which is impossible with
one point in each sea column. Thus the punctured background is valid
even in the presence of the final parity graph.

It is important to impose (4). Opposite sea parity alone does not
exclude a vertical rival whose two white endpoints fit in the small
outer margins.

## 3. The exceptional rows caused by the margins

For each of the eighteen chosen profiles, exclude the following rows:

1. Every row outside \([125,h-124]\).
2. Every \(r\) for which
   \(j(r-L+j)\) is a square for some \(1\le j\le L-1\).
3. Every \(r\) for which
   \(j(H-r+j)\) is a square for some \(1\le j\le h-H\).

Let \(E_h\) be their union over all profiles. There are
\(O(\sqrt h)\) rows in \(E_h\): the boundary contribution is constant,
there are at most 41 values of \(j\) in any profile, and each equation
\(j(t+j)=s^2\) supplies only \(O(\sqrt h)\) possible \(s\).
This deliberately overcounts, without testing whether the associated
sea column is a hole or has the required character.

For a central row outside \(E_h\), both distances to the sea rows
exceed 82, while each outer margin is at most 41. Hence all the
three-corner and four-corner cases previously excluded for lying
outside \([L,H]\) still lie outside \([1,h]\). For example, two
diagonal sea points on one boundary give common whites centered on
that boundary with separation \(|r-s|>82\), where \(s\) is the
other sea endpoint row. A side crossing the sea rows, with the central
point in the black diagonal, would require
\(H-r\le2(L-1)\) or \(r-L\le2(h-H)\), also impossible.

The only newly possible one-label rivals with a small overhang are
vertical alternatives of a central/sea diagonal. Their equations are
exactly the square families in items 2 and 3. Thus the exclusions above
complete the passage from the smaller sea strip to the ambient strip.

## 4. Covering every remaining row pair

The quotient set \(T/T\) is all of \(\mathbb F_7^*\). Given any row
pair \(a,b\), choose \(L\in\{1,2,3\}\) whose residue differs from
both \(a\) and \(b\). Such an \(L\) exists because there are only
two forbidden residues. Both differences are nonzero, so there is
some \(d\ne0\) with
\[
a-L,\ b-L\in dT.
\]
The profile selected for this \((L,d)\) satisfies (1) for both rows.
If \(a,b\notin E_h\), Sections 1–3 show that inserting this label at
any hole creates no zero-label or one-label obstruction.

The number of parity labels incident to \(E_h\) is \(O(h^{3/2})\).
The established positional construction for \(n\) prescribed labels,
with the complete final graph of size \(Q=\Theta(h^2)\), has internal
width \((n+\sqrt{nQ})h^{o(1)}\). Applied to these exceptional labels,
this is \(h^{7/4+o(1)}\). A constant number of \(O(h^2)\) collars
therefore keeps their total cost \(O(h^2)\). This application uses the
existing positional theorem; it does not rely on an interior-star
construction.

## 5. What remains

All nonexceptional labels can now be assigned to eighteen compatible
periodic punctured backgrounds. The outstanding problem is to order
or place many labels in the same background while excluding supports
involving two or more labels. If a placement leaves unused holes,
those columns must also be filled to obtain an equality board.
Replacing holes by an arbitrary fixed interior row is an additional
problem and is not included in this theorem.
