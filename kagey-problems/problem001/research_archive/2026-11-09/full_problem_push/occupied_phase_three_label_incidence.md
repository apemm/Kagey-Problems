# A surviving three-label incidence cost under full occupation

9 November 2026. Completely occupying one period-49 phase removes the
horizontal filler-pair family, but exposes a genuine three-label
right-angle family. In a constant-density eligible label universe its
incident template count is
\[
 D_3\gg h^4\log^2h\asymp n^2\log^2h.
\tag{1}
\]
Consequently the sufficient uniform-permutation criterion in
[permutation_occupation_mixed_pair_lemma.md](permutation_occupation_mixed_pair_lemma.md)
does not control the full event family at the quadratic occupation
scale. This is an incidence obstruction to that criterion, not a
lower bound on the width of valid boards or an impossibility theorem
for correlated orders.

The angle count, deleted-row estimate, and actual canonical-event load
have passed independent review in
[occupied_phase_three_label_independent_audit.md](occupied_phase_three_label_independent_audit.md).

## 1. A constant-density eligible universe

Fix one oriented \(0,5\) profile, with odd low row \(L\),
even high row \(H\), and \(g=H-L\not\equiv0\pmod7\).
Choose an odd residue \(a_0\pmod {98}\) with
\(v_7(a_0-L)=1\). Use odd endpoints in this residue class in a
fixed bulk interval, and even endpoints satisfying
\(b-L\equiv5g\pmod7\) in another fixed bulk interval.
Both intervals have length proportional to \(h\). The finite
one-label square filters exclude only \(O(\sqrt h)\) rows.
The finite exceptional sum/difference identities exclude only
\(O(1)\) mates of each selected odd endpoint. Thus these labels
form a universe of size \(n\asymp h^2\), with \(\Theta(h)\)
eligible even mates for each remaining odd endpoint.

The same conclusion holds after deleting the
\(O_\varepsilon(h^{3/4+\varepsilon})\) exceptional rows from
the mixed-pair power-saving argument. The loss estimate in Section 3
will also show that these deletions preserve the right-angle count.

## 2. Count actual right angles

Fix a surviving odd root \(A=(0,a)\), with \(a\) in a bulk
interval around \(h/3\). Choose a sufficiently small fixed
\(\eta>0\) and put \(X=\lfloor\eta h\rfloor\).
For coprime positive \(p,q\le X\), and positive integers
\(k,l\) with
\[
 kq\le X,\qquad lp\le X,
\tag{2}
\]
let
\[
 U=98k(p,q),\qquad V=98l(-q,p).
\tag{3}
\]
Then \(U\cdot V=0\). The three selected black points are
\(A,A+U,A+V\), in three distinct columns. Their rows all lie
in the same odd residue class modulo 98. Taking \(\eta\)
small enough puts these rows and the fourth corner \(A+U+V\)
in the bulk. Their horizontal diameter is \(O(\eta^2h^2)\),
and all four columns are multiples of 49. Hence they fit well
inside an occupied interval of any prescribed positive constant
multiple of \(h^2\), after reducing \(\eta\) if necessary.

Different parameter quadruples give different rooted right angles:
the right-going leg determines its primitive direction \((p,q)\)
and scale \(k\), and the left-going leg determines \(l\).
Their number is
\[
 \sum_{p,q\le X\atop(p,q)=1}
       \left\lfloor\frac Xq\right\rfloor
       \left\lfloor\frac Xp\right\rfloor
 \asymp X^2\log^2X.
\tag{4}
\]
For the lower bound, each floor is at least half its argument.
The coprime harmonic sum is
\[
 \sum_{p,q\le X\atop(p,q)=1}\frac1{pq}
 =\sum_{d\le X}\frac{\mu(d)}{d^2}
       \left(\sum_{j\le X/d}\frac1j\right)^2
 =\frac1{\zeta(2)}\log^2X+O(\log X).
\tag{5}
\]
Absolute convergence of the corresponding log-weighted series
justifies the final estimate. The unrestricted harmonic sum gives
the matching upper bound in (4).

## 3. Deleted rows do not remove the leading family

For a fixed forbidden selected row \(r\), the condition
\(a+98kq=r\) has at most \(h^{o(1)}\) pairs \((k,q)\).
After fixing them, the remaining choices satisfy
\[
 \sum_{p\le X}\left\lfloor\frac Xp\right\rfloor
 =O(X\log X).
\]
Thus at most \(O_\varepsilon(h^{1+\varepsilon})\) angles
use \(r\) on the first nonroot leg. The second leg has the
same bound. Deleting \(O_\varepsilon(h^{3/4+\varepsilon})\)
rows removes at most \(O_\varepsilon(h^{7/4+2\varepsilon})\)
angles. For fixed sufficiently small \(\varepsilon\), this is
\(o(h^2\log^2h)\). The one-label square exclusions are smaller.

Choose an eligible even mate for each of the two nonroot odd points.
There are \(\Theta(h^2)\) choices. If their odd rows coincide,
exclude the \(O(h)\) choices that make the two labels identical.
The fixed root label is distinct because both other odd rows are
strictly larger than \(a\). Thus (4) gives the lower bound (1)
for relative three-label templates incident to this fixed label.
All selected labels satisfy the one-label profile conditions and
survive the mixed-pair exceptional-row removal.

Choose \(\eta\) so that every counted horizontal diameter is
less than half the occupied interval length. Each template then has
\(\Omega(n)\) translations into the consecutive phase slots.
Its canonical event has probability \(1/(n)_3\), so the actual
sum of these probabilities at the fixed root-label resource is
\(\Omega(D_3/n^2)=\Omega(\log^2h)\). Thus the more precise
resource criterion, not just its uniform-degree corollary, also fails
for this unmodified universe.

## 4. These triangles cannot be retained as safe completions

The fourth corner \(W=A+U+V\) has a column in the occupied
phase. Its column lies between those of \(A+U\) and \(A+V\),
so it is inside the occupied interval whenever these two points are.
Its row lies in the strip by construction.

If \(W\) is white, its column contains a real parity double.
Choose the endpoint \(t\) of that double with physical parity
opposite to \(W_y\). The final complete parity graph contains
the label \(\{t,W_y\}\) in another column. These three black
cells give an axis-aligned rectangle with the same singleton white
presentation \(\{W\}\) as the tilted rectangle. The other
owner column is distinct because \(W\) is white in its own
column. Therefore this is a genuine identifying failure.

If \(W\) is black, the tilted rectangle is hidden and is
forbidden by the all-grid theorem in
[hidden_rectangles_and_exact_hypergraph.md](hidden_rectangles_and_exact_hypergraph.md).
The complete-parity-graph premise concerns the final board; the owner
of the axis rival need not lie in the same profile block.

Thus every right angle counted above must be avoided in a completely
occupied block. The lower bound remains a statement about the full
eligible universe before a new correlated subdivision or ordering.
It does not prove that every such order fails. A successful quadratic
construction must exploit additional structure in these three-label
constraints, or use a different occupation/background mechanism.
