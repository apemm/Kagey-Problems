# Complete occupation for a sparse family of translated constraints

9 November 2026. The new mixed-pair incidence bounds are strong enough
for a random-permutation local lemma. Thus complete occupation is
compatible with avoiding these particular pair families. This does
not resolve vertical parity rivals, equal-residue triangles, the
remaining higher-arity events, or the occupied region's ends.

The lemma, its primary-source input, and the one-phase application
have passed independent review in
[permutation_occupation_independent_audit.md](permutation_occupation_independent_audit.md).

## 1. A permutation lemma

Let \(E\) be a set of \(n\) labels and \(S\subset\mathbb Z\)
a set of \(n\) distinct slots. A forbidden pair template specifies
two distinct labels \(e,f\) and a nonzero offset \(\delta\).
It forbids \(\pi(f)-\pi(e)=\delta\), possibly only for a
specified subset of the translations that fit in \(S\).
Duplicate templates may be removed. Let \(D\) bound the number
of templates incident to any one label, counting both endpoint roles.

**Lemma.** If
\[
 4\mathrm eD\le n-1,
\tag{1}
\]
there is a bijection \(\pi:E\to S\) avoiding every forbidden
template. In particular, \(D=o(n)\) suffices asymptotically.

Choose a uniform random bijection. For every allowed translation
of a template, introduce its canonical event
\[
 \pi(e)=x,\qquad\pi(f)=x+\delta.
\tag{2}
\]
Its probability is \(p=1/[n(n-1)]\). At most \(nD\) events
use a fixed label. There are at most \(nD/2\) pair templates in
total, and each admits at most two translations using a specified
slot. Thus at most \(nD\) events use a fixed slot. An event has
two labels and two slots, so the graph joining events that share
either has maximum degree at most \(4nD-1\).

This is a valid lopsided dependency graph. The canonical conflict
graph theorem is Theorem 1 of Lu and Székely,
[Using Lovász Local Lemma in the Space of Random Injections](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v14i1r63),
Electronic Journal of Combinatorics 14 (2007), R63; the
[primary manuscript](https://people.math.sc.edu/lu/papers/randinj.pdf)
states the theorem on page 4. Joining all shared-label or shared-slot
events only enlarges that graph. The symmetric lopsided local lemma
now applies because \(\mathrm e p(4nD)\le1\), proving (1).

The slot bound is essential. A label-only dependency estimate would
not justify a permutation argument.

## 2. A resource criterion and fixed phase capacities

Here is a form that also handles higher arity and prescribed phases.
Partition labels and slots into corresponding parts
\(E_i,S_i\), with \(|E_i|=|S_i|=n_i\). Choose the bijections
\(E_i\to S_i\) independently and uniformly. A canonical event
\(A\) specifies distinct label-to-slot assignments respecting
these parts. If it uses \(k_i\) labels in part \(i\), its
probability is exactly
\[
 p_A=\prod_i(n_i)_{k_i}^{-1}.
\tag{3}
\]
Assume every event uses at most \(r\) labels. Treat each label
and each slot as a resource, and put
\[
 L=\max_z\sum_{A:\,A\text{ uses }z}p_A.
\tag{4}
\]
Then \(L\le1/(8r)\) suffices to avoid all events while
completely occupying every specified slot.

For completeness, the lopsided graph extends to this product space
directly. Starting with an unconditioned set of bijections, force the
assignments of one event \(A\) successively by swapping the two
relevant images within the appropriate part. The result is uniform
conditional on \(A\). Any canonical event compatible with \(A\)
that held before a swap still holds afterward: a changed domain or
image in its matching would already force that swap to be trivial.
Therefore avoiding any collection of nonconflicting events after
the forcing implies avoiding them before it. This is exactly the
negative-dependency inequality.

Set the local-lemma variable to \(x_A=2p_A\). Each event uses
at most \(2r\) resources, so the sum of its neighbors' variables
is at most \(4rL\le1/2\). Consequently
\(\prod_{B\sim A}(1-x_B)\ge1/2\), and
\(p_A\le x_A\prod_{B\sim A}(1-x_B)\). This proves the
criterion. It also deals with unequal phase sizes whenever the
actual probabilities in (3) satisfy (4); no balance is implicit.

For one unrestricted permutation and rigid translated templates of
arity \(k\), let \(D_k\) bound template incidence at a fixed
label. Each template has at most \(n\) translations. At a fixed
slot it has at most \(k\) translations, while the total number
of templates is at most \(nD_k/k\). Both resource counts are
therefore at most \(nD_k\). A sufficient condition is
\[
 \sum_{k=2}^r\frac{nD_k}{(n)_k}\le\frac1{8r}.
\tag{5}
\]
In particular, \(D_k=o(n^{k-1})\) for each bounded arity
suffices. If all occupied phase sizes satisfy \(n_i\ge\eta n\)
for fixed \(\eta>0\), the same asymptotic condition suffices,
with constants depending on \(r,\eta\). It does not follow for
arbitrarily small phase capacities from the unweighted \(D_k\)
bounds alone.

## 3. Application to the controlled mixed pairs

After the exceptional-row removal in
[low_high_mixed_power_saving.md](low_high_mixed_power_saving.md) and
[same_sea_mixed_power_saving.md](same_sea_mixed_power_saving.md), the
remaining oblique two-label/two-sea mixed templates satisfy
\[
 D=O_\varepsilon(h^{7/4+\varepsilon}).
\tag{6}
\]
The endpoint-role bound is uniform, and a geometric offset template
remains rigid under translation. Prescribed sea phases and strip
containment only remove allowed translations. For a block with
\(n\asymp h^2\), (6) is \(o(n)\), so the lemma gives a
complete occupation avoiding all these mixed pair families.

There are only finitely many profile blocks. If a block is smaller
than \(h^{7/4+\delta}\), for some fixed small \(\delta>0\),
its labels can instead join the exceptional construction. For each
remaining block, choose \(\varepsilon<\delta\), so (6) is
again \(o(n)\). The total additional exceptional-label cost is
still subquadratic internally, with quadratic collars.

This application is deliberately restricted to the templates in
(6). It does not say that (5) holds for all geometric events.

The subsequent
[inserted mixed-support bounds](inserted_mixed_higher_arity_bounds.md)
give \(D_3=O_\varepsilon(h^{3+\varepsilon})\) and
\(D_4=O_\varepsilon(h^{5+\varepsilon})\) for nonvertical-side
mixed supports with four inserted points. They can be included in
the same permutation argument: when \(n\asymp h^2\), their
contributions to (5) are both \(O_\varepsilon(h^{-1+\varepsilon})\).
The pair contribution is \(O_\varepsilon(h^{-1/4+\varepsilon})\).
Thus these three arities can be avoided simultaneously. This still
does not include the three-inserted-point right-angle family.

## 4. One occupied phase suffices in an oriented block

The horizontal exclusion from
[seven_phase_filler_profiles.md](seven_phase_filler_profiles.md)
also works with **one** completely occupied hole phase. Put all
labels in the slots \(49\mathbb Z\), and retain the six other
filler phases. A horizontal side formed by two equal filler rows has
both endpoint columns in the same unoccupied phase \(j\ne0\).
Its length is divisible by 49. The diagonal norm and midpoint
identities force both label columns into phase \(j\), impossible.
The other horizontal pairings are excluded by the same parity and
nonsquare-norm arguments as in the two-phase proof. This statement
only concerns supports contained in the occupied region.

For the oriented \(0,5\) block, choose the finite lower-row
profile so that every assigned odd endpoint \(a\) satisfies
\(v_7(a-L)=1\). The only remaining opposite-parity label-root
triangle would use an even endpoint \(c\) and a low sea point.
Its equation is
\[
 \Delta x=-(c-a)(L-a).
\tag{7}
\]
The right side has valuation one, since
\(c-a\equiv5(H-L)\not\equiv0\pmod7\). But
\(49\mid\Delta\), so the left side has valuation at least
two. Thus this triangle is absent without any sign split or phase
capacity condition.

Choose \(n\) consecutive slots in \(49\mathbb Z\) and apply
the ordinary permutation lemma. This simultaneously preserves full
occupation, the preceding horizontal exclusion, the triangle
valuation exclusion, and avoidance of the controlled oblique mixed
pair families. It leaves unresolved the vertical rivals, the other
higher-arity events, the separate all-zero blocks, and interactions
with fillers beyond the occupied interval. It is therefore a partial
occupation theorem, not a valid complete-board construction.

Including the preceding higher-arity mixed bounds removes all
nonvertical-side mixed side/diagonal supports contained in this
occupied oriented region: the zero- and one-label cases are safe,
three inserted points plus one sea point are excluded modulo seven,
the oblique two-label cases and four-inserted-point cases satisfy
(5), and horizontal cases are excluded by occupation. The remaining
right-angle templates have the actual large incidence proved in
[occupied_phase_three_label_incidence.md](occupied_phase_three_label_incidence.md),
so this simultaneous mixed-support conclusion does not close the
complete-board construction.
