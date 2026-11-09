# Problem 001: construction obstructions, sea entropy, and a local square bound

Research results, 8 November 2026. This continues `../2026-11-07/REPORT.md` and
`../2026-11-07/REPORT_1xh_construction.md`. The existing reports and manuscripts were not edited.
No commits were made. The proofs below are research results checked during this session, not
externally refereed results or a claim of priority in the literature.

The general `1, x, h` construction remains open. This session first establishes restrictions on
the proposed residue split and replaces the residual Q/T descriptions with exact equations.
It then proves two results on the other research questions:

\[
\boxed{\rho_h\ge c h^{1/3}}\qquad\text{and}\qquad
\boxed{f(n,n)=O\!\left(\frac{n^{4/3}}{(\log n)^{1/3}}\right)}.
\]

Here \(\rho_h\) is the parity-partition sea entropy. Its lower bound does not assume, or prove,
that the same growth rate governs maximum-blackout counts.

## 1. The priority construction

### The direct residue split has a counting obstruction

Write \(h=8n+3\), \(k=4n+1\), and \(q=k(k+1)\). Proposition 18 puts hot odd rows at even
slots. On odd slots, track A has even partners congruent to 0 modulo 4, and track B has partners
congruent to 2 modulo 4. The suggested split would impose the sufficient condition

\[
 v_2(r_i-r_j)\le1+v_2(i-j)
\]

on distinct non-hot odd rows at odd slots. This cannot hold globally for any \(h=8n+3\ge11\).
The two non-hot row types are 1 and 3 modulo 8. Distinct rows of either type cannot lie on
opposite tracks. Each type then needs at least \(2n(n+1)\) edges on even slots, but only
\(4n+1\) even slots remain after placing the hot edges. The required total is
\(4n(n+1)>4n+1\).

More importantly, the obstruction persists when the inequality is required only within the
geometrically relevant radius \(R=\lfloor k^2/16\rfloor\), for \(h\ge131\) in this residue
class. Overlapping windows of \(2k+1\) odd slots force the same track allocation throughout.
A contiguous core with this local property contains at most \(k(n+1)\) of the board's
\(k(2n+1)\) odd slots. Thus short free transition regions do not repair this mechanism.
The corresponding direct even-row valuation mechanism fails locally from \(h=67\).

These statements obstruct a sufficient valuation mechanism. They do not rule out valid orders
that fail the inequality but avoid the actual right-angle equation by size or divisibility.

The range proof in Proposition 24 also needed a correction. Its two row differences need not
have opposite signs. When they have the same sign, the in-grid completion supplies the bound
\(|A|+|B|\le h-1\). The proposition itself survives.

Full proofs: [construction_split_obstruction.md](construction_split_obstruction.md).

### Exact residual collision equations

After excluding law (i), a remaining collision between two tilted rectangles uses the common
pair as a side in one and a diagonal in the other. If their complementary black pairs are
\(A,B\) and \(C,D\), the exact equations are

\[
 |B-A|^2=|D-C|^2,\qquad
 (A+B-C-D)\cdot(B-A)=0.
\]

The shared white points are \((C+D\pm(B-A))/2\), subject to integrality, containment,
whiteness, and nondegeneracy. Axis reflection of the second diagonal gives Q; the other
nondegenerate possibilities give the mixed tilted law T.

Two independent obstructions follow.

* At height 11, the consecutive doubles \(\{3,4\},\{2,11\},\{1,8\}\) force a collision
  with presentation \(\{(2,2),(6,10)\}\), although none of their six black cells forms a
  right angle. There is an infinite scaled version for odd slot distance \(d\).
* The all-double Q configuration first fits at height 13. It therefore first enters the
  admissible pure family at height 15. The consecutive doubles
  \(\{2,9\},\{4,13\},\{5,6\},\{1,8\}\) demonstrate the obstruction without a
  three-black right angle. This identifies an additional geometric constraint at the first
  unresolved height; it does not prove infeasibility there.

A hidden rectangle in a pure region is all-double and has an even side vector. Bisecting that
side gives two distinct rectangles with identical presentations. This closes the hidden-rectangle
qualification for the pure family even when no outward extension fits. It does not justify
rejecting every hidden rectangle in arbitrary free-gap layouts.

Full equations, proofs, and examples: [construction_obstructions.md](construction_obstructions.md).

### Exhaustive middle-cell formulas

The new checker builds constraints directly from symmetric differences of rectangle corner sets.
It does not assume the obstruction classification or sample middle-cell assignments to discover
clauses. For the trimmed known seven-row and eleven-row orders, it finds exactly 128 and 384 valid
middle assignments, respectively. The eleven-row formula has five unit and 33 binary constraints.

All 2,048 middle assignments on the seven-row core were checked against independent rectangle
enumeration. The eleven-row computation independently matches all 435,307 rectangles, checks
32 random assignments and a satisfying assignment, and verifies the count 384 by component
truth tables. These counts concern pure cores, not collars or free transitions.

Proof of the algorithm and evidence: [exact_middle_reduction.md](exact_middle_reduction.md).

## 2. Sea entropy is unbounded

There is an absolute \(c>0\) such that the parity-partition sea shift satisfies

\[
 \rho_h\ge c h^{1/3}
\]

for all sufficiently large heights. This resolves the unboundedness question in the earlier report.

The proof chooses a random sparse set of odd rows and deletes rows to make it Sidon, leaving
\(k\asymp h^{1/3}\) letters. Parity and the Sidon property remove hidden rectangles,
singleton and vertical axis rivals, oblique axis rivals, and same-side or same-diagonal tilted
collisions. The surviving forbidden patterns specify four or six black cells.

Arithmetic counting and the alphabet selection give

\[
 B_4=O_\epsilon(k^3h^\epsilon),\qquad
 B_6=O_\epsilon(k^5h^\epsilon).
\]

A random word realizes an individual pattern with probability \(k^{-4}\) or \(k^{-6}\).
Each column lies in at most four or six translates of each pattern, regardless of its span.
The weighted local lemma therefore gives at least

\[
 k^m\exp(-C_\epsilon m h^\epsilon/k)
\]

valid sea words of length \(m\). Fixing \(0<\epsilon<1/3\) proves the claimed bound.
The proof handles repeated row values and overlapping rectangle pairs explicitly.

Full proof and links to the standard arithmetic and local-lemma inputs:
[sea_entropy_lower_bound.md](sea_entropy_lower_bound.md).

This does not prove parity dominance, primitivity of a dominant component, or access to that
component through every double insertion. The maximum-blackout product formula remains conditional.

## 3. Removing the iterated logarithm from the square bound

For any region \(U\), validity gives a local completion budget: at most \(|U\setminus S|+4\)
black right angles can complete in \(U\). The extra four allow one hidden rectangle.

If a square \(Q\) of side \(\ell\) has its threefold expansion inside the grid, every
completion of a triple in \(Q\) lies in that expansion. Its budget is therefore
\(9\ell^2+4\). Summing the report's line-counting inequality over primitive perpendicular
directions gives

\[
 |S\cap Q|^3\log(|S\cap Q|/\ell)\le C\ell^4,
\]

and hence \(|S\cap Q|\le C\ell^{4/3}/(\log(\ell+2))^{1/3}\). A dyadic Whitney
decomposition has \(O(n/\ell)\) such squares at scale \(\ell\). The geometric sum over
scales gives

\[
 f(n,n)=O\!\left(n^{4/3}(\log n)^{-1/3}\right).
\]

This removes the earlier factor \((\log\log n)^{2/3}\). The same proof gives
\(f(h,m)=O(mh^{1/3}/(\log h)^{1/3})\) for \(2\le h\le m\), though other bounds can
be stronger on long strips. The exponent gap remains open.

Full self-contained proof: [square_local_budget.md](square_local_budget.md).

## 4. Checks, limits, and the next construction target

The split and collision proofs were independently reviewed during the session. Their finite
checks found no failures: 4,680 admissible windows, 31,648 range cases, both obstruction patches,
the scaled mixed family, and all relevant all-double shapes through height 15. These checks
support the general proofs; they are not substitutes for them. The square and entropy arguments
are analytical and do not depend on search results. The entropy collision counts and local-lemma
step were independently audited twice.

The priority existence problem remains unresolved: no general valid `1, x, h` order and no
general \(O(h^2)\) threshold are claimed. The work narrows the next construction target.
It must exploit the exact right-angle equation, near-side inequalities, or divisibility instead
of imposing the failed pairwise valuation rule on almost every slot. The exact Q/T relations must
be included alongside law (D); at height 15, Q is an additional constraint. End transitions and
collar extension still need separate proofs.

Other remaining questions include the sharp growth of \(\rho_h\), insertion into a dominant
sea component, the exact intermediate widths, and the square exponent. No long SAT search was
used to support a general mathematical claim in this session.
