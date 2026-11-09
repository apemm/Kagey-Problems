# Mixed supports force equal filler rows

9 November 2026. In the period-49 refined profile, every mixed support with two label points and two filler points uses the same actual filler row twice. This reduces that family to the same-row counting lemma. It does not exclude mixed supports using two different binary boundary levels.

Use the setup of [seven_phase_filler_profiles.md](seven_phase_filler_profiles.md). The label columns and filler columns are multiples of seven. Every filler has the same normalized row residue three and the same physical parity. Its actual row is
\[
 F_j=F_0+14t_j,\qquad
 t_j\in\{0,\ldots,6\},\qquad t_j\equiv\kappa j\pmod7,
\]
at column \(7j\), where \(\kappa=\pm1\). Thus
\[
 \frac{F_l-F_j}{7}\equiv2\kappa(l-j)\pmod7,
\tag{1}
\]
and equal column phases give equal actual filler rows.

In an oriented mixed-residue block, label endpoints of the same physical parity have the same normalized residue, zero or five. The separate zero-residue blocks have the same property. An integral mixed configuration has even total row sum, so two filler points force the two selected label points to have the same physical parity. They therefore have a common row residue \(r\) modulo seven. This residue differs from the filler residue \(f\).

Write the points exactly as
\[
 A=(7i,r+7\alpha),\quad C=(7k,r+7\gamma),\qquad
 B=(7j,f+7\beta),\quad D=(7l,f+7\delta),
\tag{2}
\]
where \(A,C\) are label points and \(B,D\) are fillers. The integers \(r,f\) are fixed representatives of their residues, with \(r-f\) a unit modulo seven.

## 1. Crossed pairing

Suppose \(AB\) is the black side and \(CD\) the black diagonal. All horizontal components are divisible by seven. Equality of squared lengths, reduced modulo 49, gives
\[
 \gamma-\alpha\equiv\delta-\beta\pmod7.
\tag{3}
\]
Indeed the leading vertical difference in both pairs is \(f-r\), and the difference of their squares has first-order coefficient
\(14(f-r)[(\beta-\alpha)-(\delta-\gamma)]\).

The perpendicularity equation
\[
 (B-A)\mathbin\cdot(C+D-A-B)=0
\]
has horizontal term divisible by 49. Its vertical term modulo 49 yields
\[
 \gamma-\alpha\equiv-(\delta-\beta)\pmod7.
\tag{4}
\]
Since two is invertible, (3)–(4) imply \(\delta\equiv\beta\pmod7\). Equation (1) then gives \(l\equiv j\pmod7\), so the actual filler rows are equal. Relabeling covers the other crossed roles.

## 2. The two fillers form one black pair

If the fillers form the black side, its vertical component is \(7(\delta-\beta)\). The connector's doubled vertical component is \(2(r-f)\) modulo seven. Perpendicularity modulo 49 therefore forces \(\delta\equiv\beta\pmod7\), again giving equal actual filler rows.

If the labels form the black side and the fillers form the black diagonal, the same perpendicularity argument gives
\(\gamma\equiv\alpha\pmod7\). Divide the norm equation by 49 and reduce modulo seven. The label side's coarse vertical component vanishes, while (1) determines the filler diagonal's coarse vertical component. Thus
\[
 (k-i)^2\equiv(1+4\kappa^2)(l-j)^2
          =5(l-j)^2\pmod7.
\tag{5}
\]
Five is a nonsquare modulo seven, so both differences vanish. In particular \(l\equiv j\pmod7\), and the filler rows are equal.

These cases exhaust the side/diagonal roles, proving the assertion.

## 3. Consequence and scope

The apparent bounded difference between two filler levels does not create an extra mixed-pair family in this specific refined profile. Every surviving oblique crossed filler pair is covered by [same_sea_mixed_power_saving.md](same_sea_mixed_power_saving.md), with fixed-side incidence \(O_\varepsilon(h^{1/2+\varepsilon})\). There are only seven filler rows. The earlier squarefree-kernel argument remains in [same_sea_mixed_square_filter.md](same_sea_mixed_square_filter.md).

The other pair roles still need their existing treatment. Completely occupying phases zero and one excludes horizontal mixed supports inside that occupied region. The bounded near-boundary horizontal-diagonal exception has only bounded incidence per endpoint. Mixed configurations using one low and one high binary sea point are not covered by the present argument, nor are higher-arity collisions or the problem of finding a complete label order. No improved construction threshold is asserted.
