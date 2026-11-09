# Remaining costs in the refined periodic scaffold

9 November 2026. The new square-compatibility estimates remove the
nonhorizontal two-label/two-sea mixed roles from the leading placement
budget, after transferring a subquadratic set of exceptional labels.
They do **not** yet improve the complete-board theorem
\[
 m_0(h)\ll h^2(1+\log h)^2(1+\log\log(3h))^C.
\tag{1}
\]
This note separates the remaining geometric families from losses in
the existing placement proof. No logarithmic width lower bound is
claimed.

## 1. The exact budget already proved

Write \(Q=\lfloor h^2/4\rfloor\), \(\Lambda=1+\log h\), and
\(\ell=1+\log\log(3h)\). In
[two_moment_threshold_refinement.md](two_moment_threshold_refinement.md),
a dyadic label class of size \(n_w\) and private divisor weight at
most \(w\) uses
\[
 \begin{split}
 M(w)&=\min\{1,C\Lambda/w,C\Lambda^3/w^2\},\\
 B(w)&\ll Q\ell^{C_1}(\Lambda^2+w\Lambda)M(w)+h^{1+o(1)},\\
 A(w)&=\Lambda^4\ell^{C_2}+w\Lambda^{3/2},\\
 N_w&\ll B(w)+\sqrt{n_wQ}\sqrt{A(w)}+n_w+1.
 \end{split}
\tag{2}
\]
Both \(\sum_wB(w)\) and the higher-arity sum in (2) are bounded
by \(Q\Lambda^2\ell^{O(1)}\). The separate collars cost
\(O(Q\Lambda)\). Thus improving just one term in (2) does not
improve (1).

## 2. The mixed pair roles now have a power saving

Use the period-49 profiles from
[seven_phase_filler_profiles.md](seven_phase_filler_profiles.md).
For the two selected label points and two sea points, the modulo-seven
norm and perpendicularity equations, together with physical row
parity, leave only the following sea-level pairs:

| Label block | Possible sea-level pairs |
| --- | --- |
| Oriented residues \(0,5\) | \(L,L\), \(H,H\), \(F,F\), and one crossed \(L,H\) role |
| Both endpoint residues zero | \(L,L\), \(H,H\), \(F,F\) |

Here \(F,F\) initially means two rows from the seven-row filler
family. The modulo-49 rigidity theorem in
[refined_filler_mixed_rigidity.md](refined_filler_mixed_rigidity.md)
forces these two actual rows to agree. The small exact checker
[verify_refined_pair_role_table.py](verify_refined_pair_role_table.py)
exhausts all 816 modular role assignments; its output is
[refined_pair_role_table_check.json](refined_pair_role_table_check.json).
This finite check is a verification of necessary congruence conditions,
not a count of actual strip geometries.

For an oblique crossed side, the remaining equal-level cases have
fixed-side incidence \(O_\varepsilon(h^{1/2+\varepsilon})\), by
[same_sea_mixed_power_saving.md](same_sea_mixed_power_saving.md).
The unique low/high role in the oriented block has the same bound,
by [low_high_mixed_power_saving.md](low_high_mixed_power_saving.md).
The latter improvement uses its specific \(0,5\) congruences to
exclude the zero quadratic coefficient; it is not asserted for
arbitrary low/high row assignments.

For each fixed profile, total incidence over the side endpoint rows
is \(O_\varepsilon(h^{3/2+\varepsilon})\). Delete diagonal
endpoint rows of degree greater than \(h^{3/4}\). This removes
\(O_\varepsilon(h^{3/4+\varepsilon})\) rows and leaves both
endpoint roles with degree \(O_\varepsilon(h^{3/4+\varepsilon})\).
The unused endpoint of the other label costs a factor \(h\).
Consequently both the exceptional-label count and the remaining
incident label-pair count are
\[
 O_\varepsilon(h^{7/4+\varepsilon})=o(Q).
\tag{3}
\]
There are only constantly many profiles and roles. The exceptional
labels can use the existing uniform positional construction in
\(o(h^2)\) internal width and \(O(h^2)\) collars.

Equation (3) is a uniform degree statement after removal, not merely
a global average. A global count such as \(O(h^2)\), without
this removal step, would not control the local lemma at a fixed label.

The remaining pairing in an equal-level case puts the two sea points
in a horizontal black side. It is **not** covered by the oblique-side
power saving. This is the occupation-sensitive family discussed next.
Three inserted points and one sea point are already excluded modulo
seven, even when two inserted points belong to the same label.

## 3. The pair families that remain

### Horizontal filler-side supports

In the original period-seven sea, the horizontal family in
[horizontal_filler_incidence_obstruction.md](horizontal_filler_incidence_obstruction.md)
has actual incident geometry count \(\Theta(h^2\log^2h)\) before
arithmetic class restriction. This is a lower bound on that particular
geometry-counting majorant. It is not a lower bound on board width:
occupying a required filler position changes the black support.

In the refined period-49 profile, complete occupation of a selected
hole phase excludes these horizontal two-label supports inside the
occupied region. The one-phase version is proved in
[permutation_occupation_mixed_pair_lemma.md](permutation_occupation_mixed_pair_lemma.md).
The independent-position local lemma used for (1)
does not enforce that occupation: it places \(n\) labels in
\(N>n\) available positions. Therefore the occupation lemma cannot
be substituted into (2) without a new placement argument. A random
permutation or another correlated placement would also need the
phase capacities and the end interactions proved explicitly. The cited
permutation lemma now supplies complete occupation for the controlled
oblique mixed-pair families, using their \(o(n)\) incident degree.
It does not yet avoid the full list of remaining geometric events.

### Opposite-parity label-root triangles in equal-residue blocks

The safe-triangle extension
[same_parity_safe_triangles.md](same_parity_safe_triangles.md) retains
the binary-sea triangles whose two label points have the same physical
parity. In an oriented \(0,5\) block, restricting all centers to
one phase in \(49\mathbb Z\), with \(v_7(a-L)=1\) for the
odd endpoint, also excludes the remaining opposite-parity label-root
triangle by valuation. No phase-sign balance is needed for this case.

The same conclusion does not apply to the separate all-zero blocks.
Their two selected label rows can have opposite physical parity but
the same normalized residue. A right angle rooted at row \(a\),
with second label row \(c\) and sea row \(s\), still has the
factorization
\[
 \Delta x=-(c-a)(s-a).
\tag{4}
\]
The two-label majorant contains a private factor
\(\tau(|s-a|)\) and an averaged varying factor
\(\tau(|c-a|)\). Its present class cost is the
\(Qw\Lambda M(w)\) term in (2), whose sum is
\(Q\Lambda^2\ell^{O(1)}\). Equal-residue labels form a
positive-density family, so the exceptional-label transfer cannot
dispose of all of them at subquadratic cost. No sharp width lower
bound follows from (4); a new profile or a compatible placement rule
could still avoid it more efficiently. A finite-level valuation filter
does exclude the subfamily with distinct endpoint residues modulo 49,
but its stronger column modulus again leaves filler holes; see
[equal_residue_triangle_valuation_filter.md](equal_residue_triangle_valuation_filter.md).

### Vertical parity rivals

The exact vertical containment condition saves one logarithm in the
unrestricted fixed-label incidence. The black diagonal's horizontal
gap \(x\), row difference \(d\ne0\), and vertical alternative
length \(t\) satisfy
\[
 x^2+d^2=t^2,\qquad t\le h-1.
\tag{5}
\]
The number of positive integral right triangles with hypotenuse at
most \(h\) is \(O(h\log h)\). Indeed Euclid's parametrization
and dilation give the upper bound
\[
 \sum_{u>v\ge1\atop u^2+v^2\le h}
       \frac{h}{u^2+v^2}=O(h\log h).
\tag{6}
\]
The signs and the interchange of the legs cost only a constant.
Fixing one endpoint row and allowing the other row within the strip
can only decrease this count. The unused partner endpoint therefore
gives a uniform \(O(h^2\log h)=O(Q\Lambda)\) incident
label-pair bound.

This improves the unrestricted \(Q\Lambda^2\) divisor majorant
for this role. It does not yet give a corresponding restricted-class
bound with factor \(M(w)\). Charging \(Q\Lambda\) separately
to all \(O(\log h)\) classes would again cost
\(O(Q\Lambda^2)\). A weighted Pythagorean-triangle estimate or
a placement avoiding the class split is needed to realize this
one-logarithm saving in the complete theorem. The existing linear
coloring theorem for the P-only graph uses a different arrangement of
columns and cannot be combined with the periodic scaffold without
checking the other geometric constraints.

## 4. Higher arity and the ends remain separate tasks

The existing higher-arity estimate in (2) still gives
\[
 \sum_w\sqrt{n_wQ}\sqrt{A(w)}
 \ll Q\left(\Lambda^2\ell^{O(1)}+\Lambda^{5/4}\ell\right).
\tag{7}
\]
The leading term comes from a squared divisor-count moment
\(\Lambda^8\ell^{O(1)}\), followed by Cauchy--Schwarz and the
square root needed for three-label event probabilities. It is an
upper-budget loss, not a proved incidence or width lower bound.

A separate exact family now identifies a genuine lower obstacle to
the unmodified full-occupation permutation criterion:
[occupied_phase_three_label_incidence.md](occupied_phase_three_label_incidence.md)
gives \(D_3=\Omega(n^2\log^2h)\) in a constant-density eligible
universe, even after the mixed-pair exceptional rows are deleted.
The actual canonical-event load at a root label is
\(\Omega(\log^2h)\). All three selected points are inserted
odd points; their fourth column is occupied, so their completion is
unsafe relative to the final complete parity graph. This does not
force a \(\log^2h\) width factor: the corresponding raw
independent-position budget would scale as
\(\sqrt{D_3}=\Omega(n\log h)\), and a structured order could
avoid the family without paying that budget. It does show that the
new pair-only permutation lemma cannot finish the construction by
itself.

For mixed supports with four inserted points, the old coarse budget
is now superseded by
[inserted_mixed_higher_arity_bounds.md](inserted_mixed_higher_arity_bounds.md):
\[
 D_3=O_\varepsilon(h^{3+\varepsilon}),\qquad
 D_4=O_\varepsilon(h^{5+\varepsilon}).
\tag{8}
\]
The proof extends the crossed-pair codegree to two fixed cells in
the same column, then counts the unused endpoint of each label.
Vertical black sides remain in the virtual vertical-rival family.
At \(n\asymp h^2\), both terms in (8) have a power margin in
the permutation criterion. Three inserted points plus one sea point
are already excluded modulo seven. Thus mixed side/diagonal supports
are no longer the leading higher-arity issue in the refined block.
The three-inserted-point right angles above remain, as do any extra
occupation events if filler-root triangles are retained.

The six-cell singleton collisions restored by the audited safe-triangle
extensions already have a nontrivial row-sum or row-difference equation.
Their squared incidence has an \(h^{-1+o(1)}\) saving. Those
particular restored events are not the source of the leading
\(\Lambda^4\) factor in \(A(w)\).

Finally, the horizontal occupation argument only applies to supports
contained in the occupied region. The existing filled collars handle
the independent-position construction, but an occupied-region
permutation theorem must also control interactions with the unoccupied
filler collar. Keeping the old dyadic decomposition additionally
retains \(O(Q\Lambda)\) collar cost. With a constant number of
fully controlled blocks the collar cost would instead be \(O(Q)\).

## 5. A concrete next step

The new square-compatibility lemmas make further divisor estimates for
nonhorizontal two-label/two-sea mixed supports a lower priority. The
next construction argument needs a structured placement that avoids
the actual three-label right-angle load while keeping the required
occupation, together with a treatment of the equal-residue
opposite-parity triangles in (4). Vertical rivals and the ends still
need compatible control. The mixed-pair and inserted mixed
higher-arity estimates already meet the quadratic permutation scale;
simply enlarging that uniform permutation's event family fails on
the three-label load proved above. Until these remaining steps are
supplied, (1) remains the strongest proved all-height complete-board
threshold.
