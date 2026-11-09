# Same-slope walls: corrected crossing constants and a narrow fixed collar

9 November 2026. This note audits Sections 6--8 of
[the light-window attempt](../exact_dominance_attempt.md).
The fixed-collar construction below repairs the missing passage from
crossing means to exact interface counts. The ordinary and quadratic
cases, including the canonical rate consequence, have
[independent review](same_slope_resolution_independent_audit.md).

Throughout, \(\Lambda=1+\log h\), \(L=O(h^2)\) is the complete support
memory, and all partition functions use the normalized sea language
with the final complete bipartite row-pair set fixed. The phases are
\[
 {\rm O}: y=0\pmod2,\quad
 {\rm C}: x+y=0\pmod2,\quad
 {\rm Q}:q(x)+q(y)=0\pmod2,\quad q(t)=t(t-1)/2.
\]
Translations, complements and linear terms in Q give the corresponding
protected variants. At a complement wall the law on the right is
the complement of the law on the left.
For Q, the interface theorem concerns the anchor alignments specified
in Section 4. The wall lattice in Section 7 preserves those alignments.

## 1. The interface being compared

For adjacent intervals \(I_-,I_+\), each of length at least \(2L\),
write
\[
 J_{XY}=\log Z_{XY}(I_-\cup I_+)
          -\log Z_X(I_-)-\log Z_Y(I_+),
\]
where \(Y\) is the complement of X. Define \(J_{XX},J_{YY}\) in the
same way with one protected law on both sides. The relative wall gain is
\[
 {\cal G}_X=J_{XY}-\tfrac12(J_{XX}+J_{YY}).
\tag{1}
\]
This separates a wall's gain from the ordinary cost of joining two
independently counted half-words.

Put \(z_0=\zeta(2)/\zeta(3)\). The corrected leading constants are
\[
\begin{array}{c|c|c|c}
 X&W_{6,X}/(h\log^2h)&W_{6,XY}/W_{6,X}
       &{\cal G}_X/(h\log^2h)\\ \hline
 {\rm O}&(34/189)z_0&15/17&(4/189)z_0\\
 {\rm C}&(16/45)z_0&1/7&(32/105)z_0\\
 {\rm Q}&(128/945)z_0&13/16&(8/315)z_0.
\end{array}
\tag{2}
\]
Each displayed asymptotic has an \(o(1)\) relative error.
The first two columns concern crossing means. Sections 4--6 justify
the last column at the level of partition functions.

The relative gain is positive. The interface \(J_{XY}\) itself is
negative to leading order:
\[
 J_{XY}=-W_{6,XY}+o(h\log^2h).
\tag{3}
\]
A positive relative gain does not by itself prove that every
maximum-entropy component is canonical.

## 2. Why the scale average changes

Let
\[
 a=\sum_{v\ {\rm odd}}\frac{\varphi(v)}{v^3}
   =\frac{6\zeta(2)}{7\zeta(3)},\qquad
 b=\sum_{v\ {\rm even}}\frac{\varphi(v)}{v^3}=\frac a6.
\]
A span-dominant rectangle has sides
\(k(u,v)\) and \(\ell(-v,u)\), with v bounded while u has order h.
The transverse scale \(\ell\) has weight \(1/\ell^2\).
Its even part has weight \(1/4\), rather than \(1/2\), of the total.
Using an unweighted scale-parity density changes the leading term.

For a fixed root at normalized row \(z\), put
\[
 f(z)=\tfrac12+z-z^2,\qquad
 A(z)=\frac{z^4+(1-z)^4}{24}
          +\frac{z^2(1-z)^2}{2}.
\]
The first span moment is
\[
 S_X(z)=2\zeta(2)C_XA(z)h^4+o(h^4),
\tag{4}
\]
where the pure and long-gap wall coefficients are
\[
\begin{array}{c|c|c}
 X&C_X&C_{XY}\\ \hline
 {\rm O}&5a/16+b/4=17a/48&5a/16=15a/48\\
 {\rm C}&9a/16+b/8=28a/48&a/16+b/8=4a/48\\
 {\rm Q}&a/3=16a/48&13a/48.
\end{array}
\tag{5}
\]
For Q, average the root parity uniformly over \(\mathbb F_2^2\).
For a primitive odd/odd direction, the weighted pure and wall factors
are \(3/8\) and \(1/4\). For either opposite-parity direction, both
are \(7/32\). The odd transverse scales have weight \(3/4\),
scales congruent to two modulo four have weight \(3/16\), and
multiples of four have weight \(1/16\).

Here is a controlled way to obtain (4). First fix v and \(\ell\).
The sums over u and k are ordinary residue-class Riemann sums.
The four root-corner positions give \(A(z)\). The tails are bounded
by \(Ch^4/(v^2\ell^2)\), so they are summable. First let h tend to
infinity, then remove the fixed cutoffs on v and \(\ell\).
Replacing the full span by its long gap costs only
\(O(h^3\log h)\), from the elementary minimum-span sum.

The partner rectangle degree is
\[
 D_X(z)=c_X\frac{h^2\log^2h}{\zeta(2)}f(z)
            +O(h^2\log h),\qquad
 (c_{\rm O},c_{\rm C},c_{\rm Q})=(5/12,1/2,1/3).
\]
At the crossing scale, one rectangle carries the macroscopic span
and its partner supplies the \(\log^2h\) degree factor. Pairs with
both spans larger than \(\epsilon h^2\) contribute only \(O_\epsilon(h)\)
to the final mean. The small-span first moment tends to zero after
division by \(h^4\), as \(\epsilon\downarrow0\).
Consequently the unordered pair-span sum has leading term \(D_XS_X\).

Since \(\int_0^1 f(z)A(z)\,dz=1/45\), the six-cell crossing mean is
\[
 W_{6,X}\sim\frac{64}{45}c_XC_Xh\log^2h.
\tag{6}
\]
Only the long rectangle's factor changes at the wall. This gives (2).

As a finite arithmetic check,
[the exact span-moment script](probe_wall_span_moments.py) enumerates
primitive directions and both side scales at the central root.
The saved [larger-height output](wall_span_moments_large.json) gives:

| Height | O long-gap ratio | C long-gap ratio |
|---|---:|---:|
| 1025 | 0.8678274 | 0.1391992 |
| 2049 | 0.8752049 | 0.1408283 |
| Limit | \(15/17=0.8823529\ldots\) | \(1/7=0.1428571\ldots\) |

These are central-root span-moment ratios, not a direct enumeration
of full six-support partition functions. The controlled sums above
supply the asymptotic proof.

The full weighted exclusion argument is in
[the crossing-mass audit](exact_dominance_crossing_mass_independent_audit.md).
Repeated columns and repeated six-support descriptions cost \(O(h)\).
Six-supports containing smaller old or new forbidden supports are also
lower order. In particular, the two-original-triangle descriptions
which already violate the wall's singleton rule must be discarded.

The mixed-four claim \(O(\log^4h)\) in the attempt is false:
explicit horizontal and connector-long families have mass \(\Omega(h)\).
The sufficient corrected result is
\[
 W_{4,\mathrm{mix}}=o(h\log^2h).
\tag{7}
\]
The proof splits connector and long-side span, then applies the
already audited fixed-arc average to the long-side part. It includes
the reflected trivial circle representations. Hidden rectangles
contribute \(O(h)\).

## 3. Why the original avoidance argument is insufficient

A near-wall column has vertical-rival incident load
\(\Theta(\log h)\) under the unrestricted product measure.
Thus the protected local lemma with weights \(2p_E\), and its
\(p_E(1+o(1))\) conditional expansion, do not apply to all the wall
events. A total new-event mean \(O(h\log h)\) alone does not prove
that their avoidance costs \(\exp[-O(h\log h)]\).

The following construction changes the local product space before
using the local lemma.

## 4. Fix a collar of width \(O(h\sqrt{\log h})\)

Take
\[
 R=\lceil A_0h\sqrt{\Lambda}\rceil
\]
for a sufficiently large absolute \(A_0\). Fix every letter in
\([-R,R]\) to a valid bounded-row anchor matching the two phases.
Outside the collar, exclude a fixed finite set of low rows, only
in the \(O(L+R)\) columns that can interact with it. Retain the full
phase alphabets farther away.

For O and C the anchors use rows one and two.
For Q with row law q, use the natural
\(2211\,|\,1122\) splice, producing a run of four row-one letters.
For q+y, use the \(3322\,|\,2233\) splice and replace its four
central row-two letters by row one. The colors are unchanged.
Its two three-black triangles have safe, distinct row-five
completions. The complete anchor verification is in
[the quadratic low-anchor note](quadratic_low_anchor_complement_wall.md).
These are particular cut alignments. The reverse orientation at the
same fixed cut is not covered by these anchors: the naive reversed q
splice has four consecutive row-two letters and a vertical rival.

The collar costs at most
\[
 O(R\log h)=O(h\Lambda^{3/2})=o(h\log^2h)
\tag{8}
\]
in logarithmic count. Removing finitely many low letters in the
interaction region costs only \(O(L/h)=O(h)\).

All new vertical pairs disappear. A pair using an outer free cell
and crossing the wall has horizontal separation exceeding h.
Pairs using only pins are excluded by anchor validity.

An odd-split rectangle has an isolated corner across the wall.
The gap separating it from the other three corners is at most
\(\min(|U_x|,|V_x|)\le h\).
A new triangle with no pin is therefore impossible.
Two low pins confine a tilted rectangle to horizontal span \(O(h)\);
such a cross-wall rectangle cannot reach an outer free cell.
Every remaining new triangle has one low pin and two outer free
corners. The pin is its lowest corner, and the isolated missing
corner is on the other side of the wall.

## 5. The one-pin triangle load

Reflect if necessary. For a free column at \(-X\), \(X\ge R\), the
total incident probability of these triangles is
\[
 O\left(\frac{h^2\Lambda}{X^2}+\frac hX\right).
\tag{9}
\]
Both possible free-corner roles matter.

For the lower free corner \((-X,b)\) and pin \((-s,a)\), put
\(e=b-a>0\) and \(g=\gcd(X-s,e)\).
The short perpendicular leg is
\[
 j\left(e/g,(X-s)/g\right).
\]
Containment and the isolated completion give
\(j\le hg/(X-s)\) and \(s\le je/g\).
The other free corner remains outside the collar; this implies
\(X-s\ge X/2\). Grouping by \(g\mid e\) bounds the number of
geometries for a fixed b by
\[
 C\left(\frac{h^2e\tau(e)}{X^2}
               +\frac{h\sigma(e)}X\right).
\]
Sum over b and multiply by the two-free-letter probability
\(O(h^{-2})\). The elementary divisor sums give (9).

For the upper free corner \((-X,c)\), put \(q=c-a\).
Writing the isolated white column as \(w\ge0\), and
\(u=s+w\), orthogonality gives
\[
 v(q-v)=u(X+w),\qquad 0\le w\le u,\qquad u\le U=h^2/X.
\]
Write \(v=gz,u=g\alpha\), with \((z,\alpha)=1\).
Then \(z\mid d=X+w\), and
\[
 \alpha X/h\le z\le h/g.
\]
There are at most \(u/z+1\) multiples d in \([X,X+u]\).
Summing over \(g\mid u\) and z gives
\[
 C\{u\tau(u)\log(eU/u)+h\sigma_{-1}(u)\}.
\]
The sum over \(u\le U\) is \(O(U^2\Lambda+hU)\), proving (9)
for this role too.

For \(X\ge R\), (9) is as small as required by choosing \(A_0\)
large. The total mean of all the one-pin triangles is
\(O(h\Lambda)\): use the same minimum-span sum as for unpinned
cross-wall triangles, with a fixed low root row and two free-letter
probabilities.

The universal pinned four/six supports have local pressure
\(O_\eta(h^{-1/2+\eta})\) and total mean
\[
 O_\eta(Rh^{-1/2+\eta})=o(h\log^2h).
\tag{10}
\]
The two-pin mixed bound extends to either horizontal ordering.
Six-supports with three low pins in one rectangle must be included;
their row-completion equation gives the usual \(O_\eta(h^{2+\eta})\)
count. All unary events are excluded by choosing the outer low-row
cutoff sufficiently large.

## 6. Exact conditional counting

First avoid the internal universal bulk events on the two outer
half-words. Fixing the collar loses at most \(h^{2R+1}\) extensions
per outer assignment. Add the forbidden low-letter events only in
the finite interaction region. The conditional local lemma bounds
their cost by \(\exp[-O(h)]\).

Next impose the universal crossing four/six supports which use no
collar pin. Their raw and compatible extension pressures tend to
zero, uniformly in the two half lengths. The existing conditional
first-order expansion gives their logarithmic cost
\[
 -W_{6,XY}+o(h\log^2h).
\]
Deleting low rows changes the remaining letter probabilities by
\(1+O(1/h)\); omitting supports touching the fixed collar only helps
this lower bound.

Finally add the pinned universal events and the one-pin triangles.
Equations (9)--(10), with \(A_0\) large, verify the ordinary local
lemma jointly with the unpinned bulk. Its conditional product bound
costs only \(O(h\Lambda)+O_\eta(Rh^{-1/2+\eta})\).
Together with (8), this proves the lower bound in (3).

For the upper bound, ignore the new two/three-cell events and
retain only the universal crossing four/six family.
The conditional first-order expansion relative to the two internal
protected families gives the matching upper bound in (3).
Comparing with the pure interface proves (1)--(2).

This is an exact conditional partition-function argument.
It does not condition an arbitrary competing Perron measure on a
chosen boundary word.

## 7. Canonical rate gain

Choose alternating complementary domains of length \(n=D L+O(1)\),
with fixed \(D>4\). For Q choose \(n\equiv2\pmod4\).
Since \(q(x+2)=q(x)+1\pmod2\), the translated cut and the complement
bit change together. Every wall therefore keeps the verified local
anchor alignment. For O and C an ordinary period adjustment suffices.
Their collars are disjoint and a support cannot meet two walls.
The protected finite-word expansion is
\[
 \log Z_X(n)=n\log r_X+W_{6,X}+o(h\log^2h).
\]
Thus the gain per column from the wall lattice is
\[
 (g_X+o(1))\,\frac{h\log^2h}{n},
\]
where \(g_X\) is the positive last-column coefficient in (2).
Complementary protected rates differ by only \(O(1/h)\) in their
logarithms, so that difference is lower order here.

A canonical-capture argument accompanies this lattice count.
Append fixed-height buffers and canonical anchor tails
at both ends, keeping the first and last walls more than \(2L\)
from those tails. The same joint local lemma gives a positive
fraction of extendible cores independent of core length.
The two-sided pinned counts and the canonical capture are checked in
[the collar audit](central_low_collar_independent_audit.md) and
[the final rate audit](same_slope_resolution_independent_audit.md).

This proves
\[
 \lambda_{*,X}(h)\ge r_X(h)+c\log^2h
\]
for sufficiently large h, with an absolute positive c.
For a balanced quadratic row law Q, combining this lower bound with
the [global excess upper bound](polylogarithmic_span_tail.md) gives
\[
 c\log^2h\le \lambda_{*,Q}(h)-r_Q(h)
 \le R_h-r_Q(h)
 \le C\log^2h(1+\log\log h)^2.
\]
The law q on rows one through h is balanced at every height.
Thus the previously allowed logarithmic excess is real.
It does not determine the optimal wall spacing or prove general
canonical dominance.

