# A residual mixed template with arbitrarily deep congruences

9 November 2026. The refined filler sea and the two-phase triangle
rule still admit a same-parity two-label mixed support. This note
gives an exact family whose two labels and centers agree modulo any
prescribed fixed modulus. It limits automatic exclusion by residue
eligibility within this profile. It does not obstruct a correlated
placement, a different profile assignment, or quadratic width itself.

## 1. The unscaled identity

Let \(K\ge2\), \(T=7^K\), and \(s=T+7\). Put
\[
\begin{aligned}
x&=3(s^2+1),& a&=7x=21(s^2+1),\\
c&=a+6T,& z&=42T+150,& D&=3T^2+42T.
\end{aligned}
\tag{1}
\]
At baseline row zero, prescribe
\[
A=(0,a),\quad B=(x,0),\quad C=(D,c),\quad E=(z,0).
\]
The black side \(AB\) and black diagonal \(CE\) have the same
norm and perpendicular center displacement. Their common corner pair is
\[
W=(3T^2+63T+150,3T),\qquad
Z=(21T,a+3T).
\tag{2}
\]

Here is a direct algebraic check. Since \(x=D+150\),
\[
E-C=(150-3T^2,-c),\qquad B-A=(x,-a).
\]
The center displacement doubled is
\[
C+E-A-B=(42T,6T).
\]
It is perpendicular to \((x,-a)\), because \(a=7x\).
Moreover,
\[
x^2-(150-3T^2)^2
 =36T(T+7)(7T+50)
 =c^2-a^2.
\tag{3}
\]
The midpoint identity \(W+Z=C+E\) follows directly from (1)--(2),
and \(W-Z=B-A\). Thus both rectangles are nondegenerate, and
their symmetric difference is exactly \(\{A,B,C,E\}\).

The relevant congruences are
\[
\begin{gathered}
v_7(a)=v_7(c)=1,\qquad c-a=6\cdot7^K,\\
D=3\cdot7^{K+1}(7^{K-1}+2),\qquad
x\equiv z\equiv W_x\equiv3\pmod7,\qquad
Z_x\equiv0\pmod{49}.
\end{gathered}
\tag{4}
\]

## 2. Put the template into the refined profile

Choose a positive even integer \(t\equiv1\pmod7\), multiply all
coordinates by \(t\), and translate vertically by \(L=1\).
An additional horizontal translation \(x_0\equiv0\pmod{49}\)
is permitted. Take
\[
h=1000T^2t,\quad H=h-12,\quad F_0=1005,
\quad g=1,\quad\kappa=-1.
\tag{5}
\]
These have the residues, parities, and margins required by
[seven_phase_filler_profiles.md](seven_phase_filler_profiles.md).
Every row of both rectangles lies in \([1,h]\). The two central
rows \(1+ta\), \(1+tc\) lie in the bulk for large \(t\).

The two prescribed sea points are in nonzero low columns by (4), so
they are black in the refined profile. The point corresponding to
\(W\) is in a nonzero low column but above row one, so it is white.
The point corresponding to \(Z\) is in hole phase zero. Whether it
is white or black cannot repair the collision, because the symmetric
difference consists of the four prescribed black cells.

Both central rows are odd, normalized residue zero, and satisfy the
valuation-one hypothesis. Their two-phase signs are
\[
\chi(5ta/7)=\chi(5tc/7)=1.
\]
Both center columns are in hole phase zero. Thus the Paley triangle
filter accepts this relative placement.

The background and one-label square filters can be met along an
infinite subsequence. For fixed \(K\), every relevant filter in
(5) and at the two central rows is a nonconstant linear function of
\(t\). A fixed such function is square at only \(O(\sqrt R)\)
integers \(t\le R\). There are only constantly many filters,
so infinitely many \(t\) in any prescribed compatible arithmetic
progression avoid them all. Choose both even partners in their
normalized residue-five class and outside the remaining
\(O(\sqrt h)\) exceptional row set. They can be the same actual
row. The two labels are still distinct because their odd endpoints
differ.

For those choices each double is an individually safe substitution,
but their relative placement has the immutable mixed collision.

## 3. What fixed residue eligibility can and cannot exclude

Fix a positive integer modulus \(M\), enlarged to a multiple of
49 if necessary. Write \(M=7^kM'\) with \(7\nmid M'\).
Choose \(K\ge\max(k,2)\), and restrict the scaling parameter to
\[
t\equiv0\pmod{2M'},\qquad t\equiv1\pmod{7^K}.
\tag{6}
\]
The Chinese remainder theorem gives an infinite progression.
Equations (1), (4), and (6) imply
\[
t(c-a)\equiv0\pmod M,\qquad tD\equiv0\pmod M.
\tag{7}
\]
Choose the same even partner for the two labels. Their ordered odd/even
endpoint pairs are then identical modulo \(M\).

Suppose a rule for this fixed profile assigns an eligible set of
center residues modulo \(M\) to that common endpoint class, and
the set contains a residue compatible with hole phase zero. Choose
\(x_0\) in that residue. By (7), both label centers satisfy the
rule, while the collision remains. On a sufficiently long finite
interval both centers and the complete certificate fit.

Consequently, a fixed residue rule that assigns a nonempty compatible
center domain to **every** ordinary label in this profile cannot
guarantee that every eligible placement is valid. The common endpoint
class of this template must also be eligible under that hypothesis.

The qualification matters. The template does not reach every possible
endpoint residue class. A strategy can exclude this class from this
profile, assign it to a different profile, or impose further conditions
on the joint order or distances of labels. This note does not rule
out any of those possibilities.

## 4. Exact verification

`verify_residual_mixed_congruences.py` checks norms, perpendicularity,
midpoints, physical parity, in-strip containment, and the congruence
conditions for several moduli. Its output is
`residual_mixed_congruence_checks.json`. The checker verifies the
algebraic family; the simultaneous square-filter avoidance follows
from the density argument in Section 2.
