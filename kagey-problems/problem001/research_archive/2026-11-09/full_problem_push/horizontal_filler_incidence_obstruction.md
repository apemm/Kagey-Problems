# A genuine square-divisor family in the filler holes

9 November 2026. The two-label horizontal term in the period-seven
placement proof has an actual incidence sum of order
\(h^2\log^2 h\). Thus its square-divisor factor is not merely an
artifact of discarding the geometric equations. This is a limitation
of that geometry-counting majorant, not a lower bound on the width of
an identifying board.

## 1. The exact family

Fix an oriented mixed-residue profile from
[safe_triangle_pair_first_moment.md](safe_triangle_pair_first_moment.md).
Its hole filler is row \(F\). Choose an allowed even endpoint
\(r\) of normalized residue five. Let \(k,u,v\) be positive
integers with
\[
uv=k^2,\qquad u<v.
\]
Use two labels whose even endpoints are \(r\) and \(r+14k\),
at hole columns zero and \(7(v-u)\), respectively. The odd partners
can be any allowed normalized-residue-zero rows. Suppose the two
other hole columns below retain their filler points.

There are two rectangles with the same white pair
\[
W_-=(-7u,r+7k),\qquad W_+=(7v,r+7k).
\tag{1}
\]
The first is axis aligned, with black pair
\[
(-7u,F),\qquad(7v,F).
\tag{2}
\]
The second has black diagonal
\[
(0,r),\qquad(7(v-u),r+14k).
\tag{3}
\]
The midpoint of (3) equals that of (1), and their squared lengths agree:
\[
49\bigl((v-u)^2+4k^2\bigr)=49(u+v)^2.
\tag{4}
\]
The second rectangle is nondegenerate because \(k>0\). Both common
corners are white: their columns retain filler row \(F\), whereas
their common row is a bulk row. The two displayed black label points
are not at the filler columns. All required coordinates fit in the
strip whenever the two inserted rows are bulk rows.

Different unordered factorizations \(uv=k^2\), with \(u<v\),
give different relative geometries. Their number is exactly
\[
\frac{\tau(k^2)-1}{2}.
\tag{5}
\]
The subtraction removes \(u=v=k\), which would put both labels in
the same column.

## 2. An elementary incidence lower bound

Choose \(r\in[h/3,h/2]\) outside the exceptional row set, and let
\(1\le k\le X=\lfloor h/100\rfloor\). All rows \(r+14k\)
remain in the bulk. Only \(O(\sqrt h)\) values of \(k\) are lost
to the exceptional row set. The uniform divisor bound makes their
total contribution \(h^{1/2+o(1)}\).

The elementary estimate
\[
\sum_{k\le X}\tau(k^2)\asymp X(1+\log X)^2
\tag{6}
\]
suffices. Here is a proof of its order of magnitude. Prime-power
comparison gives \(\tau(k^2)\le d_3(k)\), and summing the three
factor variables gives the upper bound. For the lower bound, use
\[
\tau(k^2)=\sum_{d\mid k}2^{\omega(d)},\qquad
2^{\omega(d)}=\sum_{e\mid d}\mu(e)^2.
\]
Hence
\[
\sum_{k\le X}\tau(k^2)
\ge\frac X2\sum_{d\le X}\frac{2^{\omega(d)}}d
\ge\frac X2
\left(\sum_{e\le\sqrt X}\frac{\mu(e)^2}{e}\right)
\left(\sum_{m\le\sqrt X}\frac1m\right).
\]
Squarefree integers have positive lower density by the elementary
union bound over square divisors. Partial summation then makes the
first parenthesis \(\gg\log X\), proving (6).

For each surviving even row, there are \(\Theta(h)\) possible odd
partners of the required residue, outside the exceptional set.
Every such label is in the same oriented profile. For any fixed
ordinary label with even endpoint \(r\), the family (1)--(3)
therefore gives
\[
\sum_f G_{e,f}\gg h^2\log^2 h.
\tag{7}
\]
The uniform upper moment in the placement proof has the same order
for this role. Equation (7) is before partitioning labels into their
arithmetic weight classes.

## 3. What the lower bound does and does not say

The geometry count treats the two filler positions in (2) as available
sea points. A third label placed at one of them removes that filler
point. Likewise, changing one of their filler rows can destroy this
particular four-black support. The positional proof deliberately
forbids the stronger relative configuration without relying on these
possible repairs.

Consequently (7) does not imply a width lower bound, nor does it show
that every placement at quadratic width fails. Correlated placement,
occupation of the filler positions by other labels, or a compatible
change of hole rows can avoid the counted supports. The exact family
identifies a place where those mechanisms could improve the theorem.

For example, if unused holes can choose \(F\) or \(H\), the pair
of holes in (1) must receive different choices whenever both remain
unused. Choosing both \(F\) gives the axis rectangle (2); choosing
both \(H\) gives its high-row counterpart. This is an exact binary
inequality constraint for this family. Other one-label and multi-label
supports still have to be checked before such hole choices can be used.
