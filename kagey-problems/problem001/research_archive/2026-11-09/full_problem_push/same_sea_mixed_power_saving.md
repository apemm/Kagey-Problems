# A uniform power saving for the same-sea mixed role

9 November 2026. The quadratic-norm lemma from [low_high_mixed_power_saving.md](low_high_mixed_power_saving.md) also strengthens the same-sea bound. For a sea row at bounded distance from a strip boundary, the incidence at a fixed endpoint in the black side is
\[
 \boxed{I_{\mathrm{side}}(a)=O_\varepsilon(h^{1/2+\varepsilon}).}
\tag{1}
\]
This improves the earlier global first-moment bound, but it still concerns the same-sea crossed role and does not supply a full label placement.

The square-root split and exceptional-row transfer have passed independent review in [mixed_power_savings_independent_audit.md](mixed_power_savings_independent_audit.md).

## 1. Positive connector scales

Translate the sea row to zero and reflect at an upper boundary when needed. Write
\[
 U=k(p,q),\quad kq=a,\quad k,p,q>0,\quad(p,q)=1,
 \qquad T=l(-q,p).
\]
The other label point has row \(c=a+2lp\), and equal norms give
\[
 v^2+c^2=k^2p^2+a^2,
 \qquad
 v^2=(k^2-4l^2)p^2-4lap.
\tag{2}
\]
The black side is oblique, and the four required black columns are distinct. For \(l>0\), strip containment gives \(lp\le h\). Norm positivity forces \(k>2l\).

If \(p\le\sqrt h\), fix \(p\) and \(k\mid a\). The circle equation in (2) has \(h^{o(1)}\) integer representations \((v,c)\), each determining \(l=(c-a)/(2p)\). There are \(O(\sqrt h)\) values of \(p\) and \(h^{o(1)}\) divisors \(k\), so this contributes \(O_\varepsilon(h^{1/2+\varepsilon})\).

Otherwise \(l\le\sqrt h\). Fix \(l\) and \(k\mid a\), and set
\[
 A=k^2-4l^2>0,\qquad B=-4la.
\]
Completing the square in (2) gives
\[
 (2Ap+B)^2-A(2v)^2=B^2=16l^2a^2>0.
\tag{3}
\]
All variables and coefficients have polynomial size in \(h\). The uniform quadratic-norm lemma gives \(h^{o(1)}\) solutions for each \(l,k\), including when \(A\) is a square. There are \(O(\sqrt h)h^{o(1)}\) parameter pairs, giving the same bound. There is no zero-quadratic-coefficient branch: \(A=0\) would make the right side of the second equation in (2) negative.

## 2. Boundary margins

If the sea row is at distance at most a fixed \(M\) from the boundary, a negative \(l\) requires \(|lp|\le M\). Thus there are only \(O_M(1)\) pairs \((l,p)\), and \(h^{o(1)}\) choices of \(k\mid a\). This lower-order contribution completes (1).

Summing (1) over the possible side-label rows gives
\[
 O_\varepsilon(h^{3/2+\varepsilon})
\tag{4}
\]
geometries. Every geometry has one diagonal-label row. Removing the diagonal rows whose incidence exceeds \(h^{3/4}\) discards at most
\[
 O_\varepsilon(h^{3/4+\varepsilon})
\tag{5}
\]
rows. Outside them, incidence in both endpoint roles is \(O_\varepsilon(h^{3/4+\varepsilon})\). With unused label partners included, the exceptional labels and the remaining incident label-pair geometries each number at most
\[
 O_\varepsilon(h^{7/4+\varepsilon})=o(h^2)
\tag{6}
\]
for a sufficiently small fixed \(\varepsilon\).

## 3. Construction scope

The seven refined filler rows are a fixed finite set near the lower boundary. By [refined_filler_mixed_rigidity.md](refined_filler_mixed_rigidity.md), every two-label/two-filler mixed support uses one actual filler row, so its crossed role is covered here. The binary same-low and same-high roles are covered as well. Their exceptional row sets can be united over the fixed profile family without changing the exponent.

The roles with a horizontal sea side and a label diagonal are separate. Their exclusion in the refined scaffold requires complete occupation of the selected hole phases. A label side with a horizontal sea diagonal has the previously bounded near-boundary exception. The theorem also leaves vertical parity rivals, other higher-arity events, and complete occupation/order to the rest of the construction.

Thus these same-sea crossed events can be reduced below the quadratic pair-incidence scale, with a subquadratic exceptional-label family. It is not an unconditional quadratic-threshold theorem.
