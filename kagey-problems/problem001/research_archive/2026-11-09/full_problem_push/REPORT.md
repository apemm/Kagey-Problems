# Problem 001: general-answer research

9 November 2026. Work in progress. No changes have been committed.

The all-height equality construction has width
\[
 O\!\left(h^2(1+\log h)^2(1+\log\log(3h))^C\right)
\]
for an absolute constant \(C\). In particular, its width is
\(O_\varepsilon(h^2(1+\log h)^{2+\varepsilon})\) for every
\(\varepsilon>0\).
Together with the lower bound \(m_0(h)\ge\lfloor h^2/4\rfloor\), this determines the polynomial order of the equality threshold:
\[
 m_0(h)=h^{2+o(1)}.
\]
An absolute \(O(h^2)\) bound remains open. The complete scalar formula for every width and the proposed single-product asymptotic for every height also remain open.

Ordinary-parity partition dominance is false already at height seven:
the partition \(\{1,3,6\}\mid\{2,4,5,7\}\) has sea entropy at least
3.780928, whereas the parity entropy is at most 3.776801. The seven-row
equality threshold is exactly 21.

The global sea-entropy coefficient is now determined:
\[
 R_h:=\max_{\pi\ {\rm balanced}}\rho_\pi(h)
 =\frac h2-(0.1595753\ldots+o(1))(\log h)^4.
\]
The same expansion holds for both the fixed-height liminf and limsup
exponential growth rates of the maximum-blackout counts as h tends to
infinity. Maximizing row partitions are \(O((1+\log\log h)^2)\) rows from a
quadratic protected law. The exact maximizing partition and recurrent
component at every height remain open.

## Audit of the light-window and wall argument

The audit of Sections 6--8 of
[exact_dominance_attempt.md](../exact_dominance_attempt.md) resolves the
fixed affine-phase tail and proves a positive same-slope interface gain.
The original note is unchanged.

The codegree hypothesis written in Proposition 9 is false by one
factor of h. The existing weaker codegree theorem nevertheless proves
the stated deleted-letter tail and the missing multi-free-cell load
estimate. For the parity partition at sufficiently large height,
a window sampled uniformly from the normalized allowed language of
one fixed affine phase is light except with probability
\[
 \exp[-c_\epsilon h^{1/6}\log h].
\]
This uses the established same-phase anchor bounds.
It does not transfer to an arbitrary
competing component's Perron measure.
See [the codegree and load audit](exact_dominance_codegree_tail_audit.md).

The corrected six-cell crossing survival ratios at a complement wall
are \(15/17\) for constant parity, \(1/7\) for checkerboard parity,
and \(13/16\) for a quadratic phase. The transverse scale has weight
\(1/\ell^2\), so its even part contributes \(1/4\), not \(1/2\).
Mixed-four crossing mass is \(o(h\log^2h)\); the stronger proposed
\(O(\log^4h)\) bound is false.

Raw near-wall vertical-rival load is of order \(\log h\), so the
crossing means alone do not give an avoidance probability.
Fixing a valid low-row collar of width \(O(h\sqrt{\log h})\)
repairs that step at logarithmic counting cost
\(O(h(\log h)^{3/2})=o(h\log^2h)\).
The exact relative interface gains are
\[
 {\cal G}_X=(g_X+o(1))h\log^2h,\qquad
 (g_{\rm O},g_{\rm C},g_{\rm Q})
 =\frac{\zeta(2)}{\zeta(3)}
 \left(\frac4{189},\frac{32}{105},\frac8{315}\right).
\]
Quadratic walls use the verified cut alignments. Taking successive
domain lengths congruent to two modulo four preserves those
alignments at every wall.

The resulting wall lattice lies in the canonical component. For a
balanced quadratic law, it proves
\[
 c\log^2h\le\lambda_{*,Q}(h)-r_Q(h)
 \le R_h-r_Q(h)
 \le C\log^2h(1+\log\log h)^2
\]
for sufficiently large h. The excess above the pure quadratic phase
is therefore real. The proof does not identify optimal wall spacing,
the exact maximizing partition, or every recurrent component.
See [the wall proof](same_slope_wall_resolution.md),
[the crossing-mass audit](exact_dominance_crossing_mass_independent_audit.md),
and [the final collar and capture audit](same_slope_resolution_independent_audit.md).

The remaining dominance step is to capture every competing component
with root at least \(\lambda_*\). A light window suffices, but no
bounded-density theorem for such a component is proved. A bridge
that works without lightness would also close this gap.

## Continuation: exact comparisons and construction obstructions

### Slot lists and filler compatibility

The global P palette now has an arbitrary-list version:
\[
 \chi_{\rm list}(G_h+\hbox{fixed level cliques})=O(h).
\]
The level slopes are any fixed finite set excluding -1. Each label
can receive its own list of \(C h\) physical block slots, and the
coloring uses those slots without relabeling them.
[The proof](global_P_linear_list_coloring.md) and
[independent audit](slot_filler_routes_independent_audit.md)
complete this combinatorial interface.

However, fixed slot lists cannot themselves supply right-angle
exclusion in the current one-prime coordinates
\(x=2(a-1)+4pc\). With \(O(h)\) available block colors and
\(\Omega(h)\) listed colors per label, a dense-box argument finds four
labels with a common admissible color whose even cells form a hidden
rectangle. They can be P-free and satisfy every fixed finite family
of linear-level rules. The result survives deletion of o(h^2) labels.
For sufficiently large lists, the prescription for those four labels extends
to a full proper P-and-level coloring.
See [the geometric list obstruction](linear_slot_filter_obstruction.md)
and [its audit](linear_slot_filter_independent_audit.md).
Coordinated or adaptive choices remain outside this obstruction.

An inserted right angle can be retained by a filler, but only under
specific completion conditions. Every in-board completion must lie
in a singleton column. At one such column, all completion rows must
belong to one row part and leave a row of that part available for the
filler. No two inserted rectangles may have the same completion cell.
These conditions exactly settle the associated hidden,
axis-singleton, and duplicate-completion tests. They do not settle
all later four- and six-cell collisions.

The verified \(7\times21\) equality board retains two inserted-only
triangles in precisely this way. Conversely, for any balanced
partition, a fixed double-column set that must admit a filling for
every label assignment has width
\[
 \Omega(h^{5/2}).
\]
Repeated short differences in the double-column set force an
immutable collision under some assignment. Thus every h-column
interval must contain only O(sqrt(h)) doubles.
This is a lower bound for that universal-order requirement, not for
the true equality threshold.
[The filler theorem and examples](filler_safe_inserted_triangles.md)
include an exact checker that verifies 5,785 rectangles of the
seven-row board and 14,070 obstruction assignments.

A separate attempted flexible CRT rule also has a proved limitation.
For canonical representatives
\[
 x_{ij}=4z_{ij},\qquad
 z_{ij}\equiv i\pmod p,\qquad
 z_{ij}\equiv F(j)\pmod N,\qquad 0\le z_{ij}<pN,
\]
with p>10h and an arbitrary injective even-row map F, P exclusion
requires \(N=\Omega(h^{3/2})\), hence actual occupied span
\(\Omega(h^{5/2})\). This remains true when odd rows are split modulo
four. Close same-parity F-images create the Pythagorean pair with
legs \(4d\) and \(4d^2-1\).
[The CRT obstruction](continuation_separable_crt_p_obstruction.md)
also extends to any fully retained fixed residue-pair family.
It does not cover arbitrary label-dependent lifts, exceptional-label
reassignment, or non-residue subdivisions. Those and nonseparable
placements remain open. Eighteen exact collision certificates check
identity, random-injection, and dyadic-isometry maps at three heights.

These results point to a coupled construction: choose label positions
and singleton completion demands together, while controlling the
remaining mixed collisions. They do not establish an absolute
quadratic-width construction.

The continuation strengthens the exact dominance reduction. Let c be a
balanced partition at row distance r from a quadratic law, with
\(1\le r\le\delta_0h\), and put
\[
 P_h(r)=\frac rh\log^2(h/r).
\]
Within the entire language having at most \(\epsilon_0h\) phase errors
in each aligned h-column block about one matched quadratic law, its
rate is at most \(r_{\rm ref}\exp[-aP_h(r)]\). This includes r=1 and
compares with the complete reference bulk, with no extensive
span-truncation remainder. See [the local-cap theorem](continuation_exact_row_local_cap.md)
and [independent audit](continuation_exact_row_pressure_independent_audit.md).

A nonquadratic competing Perron component must consequently use bad
blocks or changes of its nearest quadratic phase at frequency at least
\[
 c\,\frac{r\log^2(h/r)}{h^2(1+\log h)^2}
\]
per column. In the known optimizer neighborhood, this is
\(\Omega(r/h^2)\).
[The witness-frequency proof](continuation_domain_witness_frequency.md)
retains an explicit \(O(h\log^2h)\) interface cost per witness.
Controlling that cost for arbitrary phase behavior remains open.

A controlled surface comparison identifies a favorable term that should
be retained. With identical alphabets excluding the changed rows, and
one fixed quadratic phase, changing r rows decreases the exact
interface log-weight by \(\Theta(rh)\), uniformly for
\(1\le r\le h^{1/4}\). This rules out the proposed absolute
\(O(r\log^2h)\) Lipschitz bound. It supports a one-sided bound on possible
interface improvement instead.
[The proof](continuation_common_alphabet_surface.md) and
[independent audit](common_alphabet_surface_independent_audit.md)
first concern the common alphabet. The subsequent
[changed-letter restoration theorem](continuation_changed_black_letter_suppression.md),
with its [independent audit](changed_black_letter_suppression_independent_audit.md),
bounds arbitrary clusters of restored changed letters by
\[
 O\!\left(\frac rh e^{-c(1+\log h)^{3/2}}\right)
\]
per permitted column in exact logarithmic count. It preserves the
surface comparison for polynomially many collar columns in one fixed
phase. Arbitrary phase walls and arbitrary exterior conditioning are
outside that restoration theorem.

For the quadratic construction, a CRT placement assigns all parity
doubles distinct columns in \(O(h^2)\) width and excludes every
inserted-only tilted right angle. Its short vertical rivals lie on
equal-offset chains. However, every fixed finite menu of rational
slopes has a positive-density collection of unsafe chains, so deleting
whole unsafe chains cannot leave a subquadratic exceptional set.
[The reduction and obstruction](crt_scaffold_independent_reductions.md)
include exact certificates.

Mixed supports remain an independent obstruction. There are explicit
CRT counterexamples at heights 884198 for slope one and 1493512 for
slope four thirds. The first retains both primes above \(4h\), with two
a quadratic nonresidue at both primes. The second retains both primes
above \(25h\). In both cases, the four labels have no vertical P rival,
yet a tilted rectangle and an axis rectangle have the same white
presentation.
[The mixed obstruction](continuation_crt_mixed_obstruction.md),
[exact checker](verify_continuation_crt_mixed.py), and
[independent audit](continuation_crt_mixed_independent_audit.md)
show why angle exclusion and P coloring alone do not finish this scaffold.

There is also an exact axis-only staircase. Put
\(w=\lfloor h^2/4\rfloor-\lfloor h/2\rfloor\). For
\(h-3\ge12(\ell+1)\),
\[
 f_{\rm ax}(h,w-\ell)
 =2(w-\ell)+1+
   \left\lfloor\frac{\sqrt{4\ell+1}-1}{2}\right\rfloor.
\]
At \(h\ge9\), the axis-only optimal multiplicity at width \(w-2\) is
also explicit. These give structural upper bounds for the full problem;
their constructions are not asserted to satisfy the tilted conditions.
See [the staircase and count](axis_borderline_single_triple.md).

At every jump \(\ell=k(k+1)\), \(k\ge1\), the same range permits a complete
axis-only equality classification and count. Put
\(A=\lfloor(h-1)/2\rfloor\), \(B=\lceil(h-1)/2\rceil\), and
\(m=w-k(k+1)\). The number of ordered axis-only optima is
\[
 \frac{h!\,m!}
 {2^{[h\ {\rm odd}]}(k+1)!(A-k-1)!(B-k-1)!}.
\]
Every optimum consists of \(k+1\) triples sharing one row, together
with a balanced bipartite double graph missing the product of their
selected endpoint sets.
[The classification and multiplicity](axis_staircase_jump_multiplicity.md)
explain the loss of \(k(k+1)\) columns at successive jumps.
This is not asserted to be the full geometric count \(a_h(m)\).

The rational \(4/3\) P-chain coloring problem also has an exact
height-independent formulation: it is equivalent to coloring a single
Cayley graph on \(2\mathbb Z_{(2)}\), the even rationals with odd
denominator. A 150-vertex in-strip graph requires at least six colors.
Its five-color unsatisfiability certificate passes an independent
integer-arithmetic proof check, and every one of its 1,289 edges has
an actual in-strip vertical-rival realization at height 80,998.
See [the coloring certificate audit](crt_chain_chromatic_independent_audit.md).
Every coloring through a finite additive quotient fails; a proper
coloring also cannot be locally constant at any vertex in either the
real or 2-adic topology.
[The equivalence](crt_chain_cayley_equivalence.md) leaves bounded
colorability open and does not remove mixed supports.


Finally, [the higher-power filler counterexample](higher_power_filler_collar_obstruction.md)
shows that even a single monotone transition to a high-row constant tail
can fail for the proposed \(7^K\) extension. The established period-49
construction is unaffected.


## Results and proof status

| Question | Result | Main proof |
|---|---|---|
| Equality threshold at every height | \(f(h,m)=m+\lfloor h^2/4\rfloor\) for every \(m\ge C_\varepsilon h^2(1+\log h)^{2+\varepsilon}\), for every fixed \(\varepsilon>0\) | [Safe triangles and weighted first moments](safe_triangle_pair_first_moment.md) |
| Fixed logarithmic refinement | The stronger threshold \(O(h^2(1+\log h)^2(1+\log\log(3h))^C)\) holds with one absolute exponent \(C\) | [Two fixed moments](two_moment_threshold_refinement.md) |
| Odd Pythagorean graph | Its chromatic number is unbounded. Every finite coloring of the positive odd integers has a same-color edge. | [Odd Følner adaptation](odd_graph_odd_folner_adaptation.md) |
| Global vertical-rival coloring | Allowing labels from different even-row blocks to mix gives \(O(h)\) colors and a vertical-rival-free scaffold of width \(O(h^2)\) | [Linear global palette](global_P_linear_coloring.md) |
| Hidden rectangles | Every valid blackout has no hidden rectangle when both grid dimensions are at least four. | [Exact hypergraph](hidden_rectangles_and_exact_hypergraph.md) |
| Sharp sea entropy | \(\rho_h\sim h/2\), uniformly as an upper bound over all balanced row partitions. The canonical lower bound is \(\lambda_*(h)\ge h/2-O((\log h)^4)\). | [Container proof](sea_entropy_half_container.md), [four logarithms](mixed_four_logarithmic_lower_bound.md) |
| Canonical entropy capture | The canonical component strictly dominates every component obeying a single affine row-parity law, including both checkerboard laws, for sufficiently large \(h\). | [Dense residue buffers](dense_residue_entropy_capture.md) |
| Marked transfer paths | Marker insertions respect the ordinary sea component order. The general upper polynomial exponent improves to \(q_h+k-1\). | [Hereditary bridges](hereditary_marked_bridges.md) |
| Collared equality words | The product asymptotic, with positive insertion factors, holds unconditionally for the entire collared class of every balanced partition. | [Hereditary bridges](hereditary_marked_bridges.md) |
| Simultaneous counting asymptotic | \(a_h(m)^{1/m}/h\to1/2\) when \(h\to\infty\) and \(m/[h^2(1+\log h)^{3+\varepsilon}]\to\infty\), for any fixed \(\varepsilon>0\) | [Joint height-width count](joint_height_width_counting.md) |
| All finite widths | An exact finite rational transfer formula returns the full black-cell enumerator, hence the optimum and its multiplicity. This is an algorithmic formula, not a simplified scalar answer. | [All-width formula](all_width_counting_formula.md) |
| Unconditional fixed-height asymptotic | On each effectively computable width residue class, \(a_h(m)=R^mP(m)+O(\theta^m)\), with algebraic parameters, \(\theta<R\), and positive leading coefficient | [Residue-class asymptotics](unconditional_residue_asymptotics.md) |
| Exact eventual counting recurrence | Each equality-partition series uses \(q_h+1\) sea resolvents; the optimal counts eventually obey an integer recurrence with denominator controlled by ordinary sea determinants | [Resolvent formula](sea_resolvent_counting_formula.md) |
| Seven-row finite cases | \(f(7,9)=17,\ f(7,10)=18,\ f(7,11)=20,\ f(7,12)=21,\ f(7,13)=23,\ f(7,14)=24\) | [Nine](seven_nine_exact.md), [ten](seven_ten_exact.md), [eleven](seven_eleven_exact.md), [twelve](seven_twelve_exact.md), [thirteen](seven_thirteen_exact.md), [fourteen](seven_fourteen_exact.md) |
| Nonparity entropy | A balanced quadratic row partition has a boundary component with entropy \((1/2+o(1))h\), and captures its four quadratic phases | [Quadratic capture](quadratic_parity_entropy_capture.md) |
| Protected-phase entropy expansion | \(\log r_X=\overline{\log k_X}-\mu_X+O_\epsilon(h^{-2+\epsilon})\), with \(\mu_X\) the exact mean of minimal forbidden supports | [Crossed codegrees and avoidance](crossed_codegree_and_avoidance.md) |
| Protected-phase ordering | At sufficiently large height, \(r_{\mathrm Q}>r_{\mathrm O}>r_{\mathrm C}\), with both additive gaps of order \((\log h)^4\); the mixed-support ratios are \(13/16\) and \(5/4\) | [Weighted ratios and entropy](protected_mixed_ratios_and_ordering.md) |
| Explicit protected-phase coefficients | \(r_X=h/2-(d_X/2)(\log h)^4+o((\log h)^4)\), with \((d_O,d_C,d_Q)=\pi^{-4}(45+32\mathcal P/9,324/5+40\mathcal P/9,144/5+26\mathcal P/9)\) and an explicit positive Euler product \(\mathcal P\) | [Complete constants](protected_phase_explicit_constants.md) |
| Full ordinary and quadratic row shifts | Arbitrary column phases preserve the best protected leading coefficient: \(\rho_{\rm parity}=h/2-(d_O/2)\log^4h+o(\log^4h)\), while \(\rho_{\rm quadratic}=h/2-(d_Q/2)\log^4h+o(\log^4h)\); the quadratic full shift eventually wins | [Full protected-row pressure](full_protected_row_leading_pressure.md), [independent audit](full_protected_row_pressure_independent_audit.md) |
| Global sea and counting coefficient | \(R_h=h/2-(d_Q/2)\log^4h+o(\log^4h)\), with \(d_Q/2\approx0.1595753\); both maximum-blackout exponential liminf/limsup have the same expansion. | [Global leading pressure](global_sea_leading_pressure.md), [independent audit](global_sea_pressure_independent_audit.md) |
| Quantitative optimizer neighborhood | Every maximizing partition is \(O((1+\log\log h)^2)\) rows from quadratic, and \(0\le R_h-r_Q(h)\le C\log^2h(1+\log\log h)^2\) for the exact protected rate \(r_Q\). | [Explicit span tail](polylogarithmic_span_tail.md), [independent audit](polylog_span_tail_independent_audit.md) |
| Positive same-slope wall gain | Corrected crossing ratios are \(15/17,1/7,13/16\) for O, C, Q; a fixed low collar proves the exact positive relative interface gains | [Wall proof](same_slope_wall_resolution.md), [final audit](same_slope_resolution_independent_audit.md) |
| Canonical excess over a pure quadratic phase | \(\lambda_{*,Q}(h)\ge r_Q(h)+c\log^2h\) for sufficiently large h; exact dominance remains open | [Captured wall lattice](same_slope_wall_resolution.md) |
| Fixed-phase light windows | For the parity partition and a fixed affine phase, the deleted-letter and multi-free-load tails hold under the normalized allowed-window measure without the extra codegree hypothesis | [Moment and codegree audit](exact_dominance_codegree_tail_audit.md) |
| Height-seven canonical dominance | The parity sea has one recurrent component, with 16,886,304 states and \(3.776799\le\rho_7\le3.776801\). The quadratic partition has smaller entropy. | [Height-seven components](sea_components_height_seven.md) |
| Height-eight canonical lower certificate | \(\lambda_*(8)\ge2.928738\), from the exact frozen model on 55,967,492 states. Its unique cyclic component has 18,590,384 states and Perron root in \([2.928738,2.928739]\); the full graph remains unresolved. | [Frozen-state certificate](height_eight_frozen_certificate.md) |
| Full seven-row counting asymptotic | \(a_7(m)\sim C_7m^{12}R_7^m\), with \(C_7>0\), \(3.780928\le R_7\le3.780929\), and exactly two reflected maximizing partitions | [Complete partition comparison](sea_components_height_seven.md) |
| Finite optimum counts | \(a_7(8)=18,\ a_7(13)=8,\ a_7(14)=80,\ a_7(20)=3364,\ a_7(21)=4\), with every board independently verified by actual rectangle presentations | [Eight](seven_eight_exact_count.md), [thirteen](seven_thirteen_exact_count.md), [fourteen](seven_optimum_count14_independent_audit.md), [twenty](seven_optimum_count20.md), [twenty-one](seven_equality_count21_independent_audit.md) |
| Exact seven-row threshold | \(m_0(7)=21\), equality holds at every width at least 21, and \(f(7,20)=31\) | [Threshold proof](seven_row_equality_width_exclusions.md) |
| Parity-partition dominance | False at height seven: \(\rho_{\{1,3,6\}}\ge3.780928>3.776801\ge\rho_{\rm parity}\) | [Counterexample](parity_partition_dominance_counterexample.md) |
| Compact fifteen-row equality | A verified width-441 board extends to every greater width | [Fifteen-row construction](height_fifteen_spacing_eight_completion.md) |
| Compact nineteen-row equality | \(f(19,m)=m+90\) for every \(m\ge713\), from a binary width-713 core and a verified tail | [Periodic binary completions](periodic_binary_completions_h15_h19.md) |
| Constant-alphabet stability | Above \(\lceil h/3\rceil\) rows, excluding singleton and vertical axis rivals forces the ordinary parity partition | [Sharp one-third theorem](constant_alphabet_stability.md) |
| Arbitrary full row-class phases | At \(h=6\) and every \(h\ge8\), nine columns force exactly the ordinary or quadratic parity laws, without a column-period assumption | [Full-box classification](full_row_class_phase_classification.md) |
| Approximate reflection closure | A balanced row block at \(h\ge8\) differs from physical parity in at most \(C V/h\) rows, where \(V\) counts its reflection-closure violations | [Interval stability](reflection_interval_stability.md) |
| Near-full variable alphabets | If each column omits at most \(M\) rows from its balanced row class, validity forces \(O(M)\) row errors from an ordinary or quadratic parity law and an exact matching column law, provided \(h\ge C(M+1)\) and \(m\ge4h+20\) | [Cartesian stability](near_full_variable_box_stability.md) |
| An entire boundary star | All parity doubles incident to row one fit in width \(h^{3/2+o(1)}\), with arbitrary constant tails; exponent \(3/2\) is optimal for the uniform collinear family | [Arithmetic spacing](boundary_star_arithmetic_spacing.md) |
| Bounded-period component exclusion | For each fixed period bound, every parity-sea language confined to those phase profiles is strictly subdominant to the canonical component at sufficiently large height | [Periodic entropy gap](bounded_period_entropy_gap.md) |
| Arbitrary phase stability for protected row partitions | Few singleton-rival hyperedges force a near-half-density container close to a matched protected product pattern; phase profiles far from those patterns have a fixed entropy gap | [Aggregate inverse](protected_row_aggregate_inverse.md), [entropy concentration](protected_partition_entropy_stability.md) |
| Arbitrary row partitions at constant phase | A balanced full row-class box with \(o(h^4\log h)\) three-corner rectangles differs from ordinary parity in \(o(h)\) rows | [Component repair](component_permutation_repair.md), [periodic Fourier amplification](constant_phase_periodic_amplification.md) |
| Arbitrary rows at any bounded-period phase | A fixed periodic column phase and an arbitrary balanced row partition have a uniform three-corner gap unless they approach matched protected laws | [Bounded-phase inverse](bounded_phase_arbitrary_row_inverse.md) |
| Fixed periodic nonprotected row partitions | For each fixed nonprotected balanced periodic row law, its entire sea has entropy at most \((1/2-\gamma)h\), with no column-phase restriction | [Transposed bounded-phase inverse](bounded_phase_arbitrary_row_inverse.md) |
| General near-maximal profile complexity | There are only \(\exp(o(h))\) balanced partitions with sea entropy \(h/2-o(h)\); every near-maximal stationary sea measure has phase entropy \(o(1)\) | [Profile complexity](low_rectangle_profile_complexity.md) |
| General partition entropy stability | Every balanced partition with sea entropy \(h/2-o(h)\) is \(o(h)\)-close to an ordinary or quadratic protected row law, with no phase restriction | [Partition rigidity](near_maximal_partition_rigidity.md) |
| Exact pressure of row changes | Every sufficiently small fractional perturbation of a balanced protected row partition strictly reduces its fixed-phase entropy; controlled phase errors and domain switches are also covered | [Robust row pressure](robust_row_perturbation_pressure.md), [stronger logarithmic penalties](changed_row_relative_pressure.md) |
| Protected domains with dilute packets | In this restricted phase language, a competitive partition differs from a protected row law in at most \(O(\log^2h)\) rows; its leading protected pressure is unchanged, so the ordinary class lies below the quadratic protected phase | [Polylogarithmic packet and domain theorem](polylog_packets_in_protected_domains.md) |
| Exact counting by SAT | A parsimonious encoding has at most \(20M\) auxiliary variables and \(75M\) clauses when both dimensions are at least four, where \(M\) is the number of rectangles | [Presentation fibers](presentation_fiber_factorization.md) |
| Minimum-width auxiliary conjecture | The proposed OEIS identification first fails at geometric height 655: minimum width 104, versus proposed value 115. | [Counterexample](minimum_width_counterexample.md) |
| Exact sea series | Integer-certified rational generating functions at heights four and five | [Sea series](sea_exact_series.md) |

## The threshold construction

The current construction uses finitely many fully filled period-seven seas.
Each uses two rows near the lower boundary and one near the upper boundary.
A quadratic-character pattern fixes all ordinary sea letters. The assigned
doubles can replace the filler at period-zero columns without any
one-label obstruction. A union of square families accounts for only
\(O(h^{3/2})\) exceptional labels, which the earlier positional
construction handles in \(O(h^2)\) total width.

The remaining placement proof controls only supports involving at least
two labels. An oriented profile makes a particular family of three-black
triangles harmless: their white completions have no axis rival and cannot
collide when only two labels are involved. Class-restricted first divisor
moments then control the remaining pair events. Higher-arity events use
second moments. A local lemma gives width
\(O_\varepsilon(h^2(1+\log h)^{2+\varepsilon})\).
Using only the fixed moments one and two strengthens this to
\(O(h^2(1+\log h)^2(1+\log\log(3h))^C)\), with an absolute \(C\).
Explicit filled transitions join every periodic block to constant tails,
so the result holds at every larger width and at every height.

The original sparse binary construction gave \(h^{2+o(1)}\).
Averaged divisor estimates successively gave logarithmic exponents sixteen
and \(8+\varepsilon\). Compatible profiles removed the private
prescription cost, first giving \(4+\varepsilon\). Fractional moments
gave the intermediate exponent \(16/5\). Allowing the safe triangles and
using weighted first moments now gives \(2+\varepsilon\).
The absolute \(O(h^2)\) threshold remains open.

New square-compatibility estimates give fixed-side incidence
\(O_\varepsilon(h^{1/2+\varepsilon})\) for the
[same-sea mixed role](same_sea_mixed_power_saving.md) and the
[oriented low/high role](low_high_mixed_power_saving.md). Removing
\(O_\varepsilon(h^{3/4+\varepsilon})\) exceptional rows leaves
uniform label incidence \(O_\varepsilon(h^{7/4+\varepsilon})\).
An [audited permutation lemma](permutation_occupation_mixed_pair_lemma.md)
therefore permits complete slot occupation while avoiding these pair
families. One occupied period-49 phase also removes the horizontal
filler-pair role and the oriented mixed-endpoint triangle. The proved
threshold is unchanged: vertical rivals, equal-residue blocks,
higher-arity events, and the occupied region's ends remain. The
[remaining-cost map](refined_scaffold_remaining_costs.md) distinguishes
these tasks from the incidence estimates already settled.

The [inserted mixed-support reduction](inserted_mixed_higher_arity_bounds.md)
also gives \(D_3=O_\varepsilon(h^{3+\varepsilon})\) and
\(D_4=O_\varepsilon(h^{5+\varepsilon})\), below the quadratic
permutation scales for three- and four-label mixed events. Its
[audit](inserted_mixed_higher_arity_independent_audit.md) includes the
previously missing same-column crossed-pair case. Vertical black sides
stay in the separate vertical-rival family.

Full occupation has a specific higher-arity obstacle: a constant-density
eligible label universe contains \(\Omega(h^4\log^2h)\) actual
three-label right-angle templates incident to one label. Their
completions lie in occupied columns and are unsafe relative to the
complete parity graph. The resulting canonical-event load is
\(\Omega(\log^2h)\), so the permutation local-lemma criterion
proved here does not apply to the full event family. The
[incidence proof](occupied_phase_three_label_incidence.md) and its
[independent audit](occupied_phase_three_label_independent_audit.md)
identify a structured-placement problem, not a width lower bound.

The private-prescription requirement in the earlier proof has its own
limitation. At every sufficiently large even height, any such collection
in the two-boundary-row background has total size
\(\Omega(h^2(\log h)^2)\). This includes optimized blocking subsets:
each individual prescription must work for every completion of its
remaining binary sea. If translated prescriptions are disjoint, their
width has the same lower bound. Thus an absolute quadratic construction
needs compatible overlap, a joint sea assignment, finite-end effects,
or another background.
[The stronger obstruction](private_blocking_set_lower_bound.md) and its
[independent audit](private_blocking_independent_audit.md) concern this
construction requirement, not the true threshold.

The complete underlying proof and its independent audit are in:

* [Filled period-seven profiles](filled_mod7_profile_cover.md)
* [Profile audit](filled_mod7_independent_audit.md)
* [Two-logarithm placement proof](safe_triangle_pair_first_moment.md)
* [Independent geometry and first-moment audit](safe_triangle_first_moment_independent_audit.md)
* [Third audit of the complete bound](safe_triangle_pair_third_audit.md)
* [Fixed two-moment refinement](two_moment_threshold_refinement.md)
* [Independent two-moment audit](two_moment_threshold_independent_audit.md)
* [Fourth-logarithm placement proof](compatible_profile_threshold.md)
* [Placement audit](compatible_profile_threshold_independent_audit.md)
* [Intermediate fractional-moment bound](fractional_moment_threshold.md)
* [Original near-quadratic construction](near_quadratic_threshold.md)
* [Independent geometry and boundary audit](near_quadratic_independent_audit.md)
* [Averaged-divisor refinement](polylogarithmic_threshold.md)
* [Sharper divisor moments](sharper_polylogarithmic_threshold.md)
* [Independent sharper-moment audit](sharper_polylogarithmic_threshold_independent_audit.md)
* [Construction checks](near_quadratic_threshold_check.json)

The original construction checks enumerate actual rectangle presentations for sampled boards. The new profile checker independently exhausts its modular cases and verifies all row and square filters at 28 consecutive large heights. The analytical proof covers all heights; the finite checks do not replace it. No practical value for the final asymptotic constant is claimed.

Separate finite constructions are much smaller. At height fifteen, width
441 suffices and a verified transition reaches a constant tail. At height
nineteen, a width-713 core repeats the seven-singleton gap
\((1,1,1,19,1,1,1)\) between doubles. A sixteen-column transition followed
by a constant row-2 tail proves equality at every width at least 713.
Coordinates and independent geometric checks are in
[the binary-completion note](periodic_binary_completions_h15_h19.md).

These examples do not establish an all-height spacing-eight construction.
Every fixed period-eight boundary pattern fails at an infinite family of
heights. Even allowing a periodic choice between the central-spike pattern
and its complement cannot solve all heights with a bounded period budget.
The latter theorem allows arbitrary boundary choices at gap residues two
and six, but does not cover every possible periodic binary sea. See
[fixed-period impossibility](period_eight_binary_sea_impossibility.md) and
[orientation-period impossibility](periodic_orientation_impossibility.md).

There is also an all-height boundary gadget. Put row one in every
column and place the doubles \(\{1,2i+2\}\) at columns \(pi\), where
\(4\mid p\) and \(p>h\). A direct norm-and-divisibility argument excludes
every collision, including virtual rivals from the full final parity
pair set. The entire star occupies \(O(h^2)\) columns and has constant
tails. [The proof](boundary_star_quadratic_gadget.md) and
[independent audit](wide_linear_star_independent_audit.md) include checks
through height thirty. This handles a boundary-edge family, not all
parity edges. A sharper analysis gives a uniformly valid spacing
\(p=O(h^{2/3})\). Choosing the spacing arithmetically improves this further
to \(p=h^{1/2+o(1)}\), hence star width \(h^{3/2+o(1)}\). The same analysis
gives an explicit mixed collision at height \(p^2/2\) for every spacing
divisible by four. Thus the exponent \(3/2\) is optimal for this particular
constant-baseline, uniformly spaced star. See
[the arithmetic-spacing theorem](boundary_star_arithmetic_spacing.md).
Interior stars need a different local background.

## The odd graph has a negative answer

For every finite coloring of the positive odd integers, there are distinct same-color \(u,v\) with
\[
 u^2+4(v-u)^2=z^2.
\]
Consequently the finite odd graphs require arbitrarily many colors. This rules out a bounded palette for the proposed P layers in the one-prime scaffold. It does not rule out quadratic-width constructions using other layouts.

The proof adapts the multiplicative-correlation and concentration estimates of Frantzikinakis, Klurman, and Moreira to an odd multiplicative Følner sequence. The odd restriction is proved explicitly; it is not inferred from their unrestricted partition-regularity theorem.

* [Full adaptation](odd_graph_odd_folner_adaptation.md)
* [Primary-source audit](odd_graph_primary_source_audit.md)
* [Independent review and sign correction](odd_folner_independent_review.md)

For a finite certificate, [odd_graph_five_chromatic.json](odd_graph_five_chromatic.json) records a five-chromatic graph on 199 positive odd vertices, with largest vertex 2607 and 825 edges. Every edge has an integer-square certificate. A proper five-coloring is included. An independent exhaustive solver proves that four colors do not suffice in [verify_odd_graph_five_chromatic.json](verify_odd_graph_five_chromatic.json). The infinite theorem is nonquantitative.

A separate global coloring theorem overcomes the P obstruction by mixing
labels from different even-row blocks. The stronger global conflict graph,
including same-odd-row cliques, has chromatic number \(O(h)\). Pell-orbit
bounds give subpolynomial blocker multiplicities; a random palette and
Hall's theorem remove the logarithm from the elementary degeneracy bound.
This yields a scaffold of width \(O(h^2)\) with no vertical rivals.
[The proof](global_P_linear_coloring.md) passed two independent audits.
It does not contradict the unbounded odd graph, whose labels are colored
within one fixed block. Nor does it complete the identifying construction:
[a twenty-row example](global_P_remaining_geometry.md) has no P conflict
but still has a hidden tilted rectangle inside one color block.

## What the counting results settle

The canonical component contains the full entropy of each affine row-parity sea language. This includes constant parity and checkerboard parity. Dense residue-class buffers and a conditional local lemma supply the bridges. Strict Perron comparison then excludes every component confined to one such law from being a competing maximum.

The checkerboard bridge has genuine pinned collisions. Their number is \(O_\epsilon(h^{3/2+\epsilon})\), by a hyperbola split and a uniform quadratic-equation estimate. This closes the bridge argument without requiring prime alphabets:

* [Dense residue entropy capture](dense_residue_entropy_capture.md)
* [Conic counting bound](checkerboard_flip_conic_bound.md)

Components with unrestricted parity patterns can still compete. The sharp upper estimate
\[
 \max_{\pi\ {\rm balanced}}\rho_\pi(h)
 \le(1/2+o(1))h
\]
does not establish exact dominance at a fixed height. Its proof uses dense-set tilted-rectangle supersaturation and hypergraph containers, keeping each independent transversal's fingerprint to avoid an unnecessary counting loss. Together with the canonical lower bound, it determines the leading entropy constant:
\[
 \lambda_*(h)\sim\rho_{\rm parity}(h)
 \sim\max_\pi\rho_\pi(h)\sim h/2.
\]

Deleting black cells from marked bridges proves that a double insertion cannot reverse the sea component order. If \(\rho\) is the largest sea radius and \(k\) is the maximum number of radius-\(\rho\) components on one sea path, the contribution of a fixed balanced partition satisfies
\[
 O(m^{q_h+k-1}\rho^m).
\]
The no-hidden theorem makes this argument apply to every balanced partition, once both dimensions are at least four.

For equality words beginning and ending with fixed constant collars, all marked paths return through the canonical component. The complete collared class therefore has an unconditional asymptotic
\[
 d_\pi(m)\sim
 \lambda_\pi^{-L}B_\pi
 \left(\prod_{e\in E_\pi}\kappa_e\right)
 m^{q_h}\lambda_\pi^m,
\qquad \kappa_e>0.
\]
The collar factor follows the state and length conventions in the proof. This result includes nearby double insertions. It is not restricted to widely separated insertion positions.

The remaining arbitrary-height counting theorem requires control of competing recurrent components and balanced partitions. Earlier certificates settle heights five and six. At height seven, all 35 balanced partitions have now been compared. Exactly the class \(\{1,3,6\}\) and its reflection \(\{2,5,7\}\) maximize the entropy. Their complete graphs have one recurrent primitive boundary component, and all insertion factors are positive. Hence
\[
 a_7(m)\sim C_7m^{12}R_7^m,\qquad
 3.780928\le R_7\le3.780929,\qquad C_7>0.
\]

Without any dominance hypothesis, the exact used-label transfer matrix
still proves a general fixed-height asymptotic on width residue classes.
Powering the matrix by the least common multiple of its recurrent periods
makes every recurrent block primitive. The largest accessible radius and
the longest chain of blocks at that radius give the exponential base and
polynomial degree exactly. All parameters are algebraic and computable.
The [complete argument](unconditional_residue_asymptotics.md) does not
assume that different residues have the same base or degree.
Ordinary-parity partition dominance is disproved, while arbitrary-height boundary-component dominance remains open. The coefficient \(C_7\) is twice the full boundary/insertion constant of one maximizing partition.

There is also an explicit exact recurrence. For each balanced partition,
sum over the chronological orders of its doubles, placing a singleton-sea
resolvent before, between, and after them. The resulting generating
function has denominator dividing
\(\det(I-zT_\pi)^{q_h+1}\). Past doubles disappear after finitely
many singleton steps, so the marker histories create no new
exponential base. Summing the partitions and adding the finitely many
pre-threshold corrections gives an eventual integer recurrence for
\(a_h(m)\). The [formula](sea_resolvent_counting_formula.md) and
[independent audit](sea_resolvent_independent_audit.md) retain exact
finite-end conditions and allow adjacent doubles.

The competing partitions deserve separate attention. The balanced row partition
\[
 \pi_Q(r)=\frac{r(r-1)}2\pmod2
\]
also has a boundary component of entropy \((1/2+o(1))h\). Its four protected quadratic phases admit the same type of entropy capture. Thus the leading constant alone cannot distinguish parity from this nonparity family.

For each protected ordinary, checkerboard, or quadratic phase, the [crossed-pair codegree bound](crossed_codegree_and_avoidance.md) now gives a first-order entropy expansion in the exact geometric obstruction mean. The probability proof uses Suen's inequality for arbitrary indicators and a matching local-lemma lower bound. It applies to the categorical column variables without a monotonicity assumption.

The leading six-cell obstruction means are computed in [six_support_leading_pressure.md](six_support_leading_pressure.md). The quadratic phase has a smaller six-cell coefficient than the ordinary constant-parity phase. The mixed four-cell contribution is now also evaluated, giving explicit protected-phase pressures. Unrestricted components remain a separate comparison.

The [mixed four-cell estimate](mixed_four_logarithmic_lower_bound.md) now proves
that its mean has exactly the same logarithmic order:
\[
 \mu_{{\rm mixed},X}(h)=\Theta((\log h)^4/h).
\]
Consequently every protected ordinary, checkerboard, or quadratic phase has
\[
 r_X(h)=h/2-\Theta((\log h)^4).
\]
Entropy capture yields the sharper canonical lower bound
\[
 \lambda_*(h)\ge h/2-O((\log h)^4),
\]
and the same lower bound for the quadratic boundary component.
The protected phases can now be compared: the quadratic phase has larger
entropy than the ordinary constant-parity phase, which has larger entropy
than the checkerboard phase, for all sufficiently large heights.
Both gaps have order \((\log h)^4\). The full protected-row comparison below now extends the best-phase leading coefficient to arbitrary column phases.

The arithmetic comparison now has three further proved inputs.
The weighted circle-scale categories \(\nu_2(k)=0,1,\ge2\)
have asymptotic weights \(1/2,1/4,1/4\), uniformly on polynomially
long scale intervals. Connector and vertical-base residues have
uniform leading weights with error \(O(h^3\log^3h)\).
The [scale average](uniform_circle_scale_valuation.md),
[connector average](uniform_connector_base_residues.md), and
[combined audit](mixed_residue_average_independent_audit.md)
remove those hypotheses from the comparison on their stated ranges.
The [short-scale bound](mixed_short_scale_truncation.md) extends the
scale weights to the complete leading vertical contribution.
The [averaged angular estimate](averaged_circle_angles.md), which
also passed [independent review](averaged_circle_angles_independent_audit.md),
proves that nearly horizontal mixed supports are lower order.
It averages fixed Fourier modes over scale and does not require
angular equidistribution on individual circles.
The [primitive parity weights](primitive_parity_weight_equidistribution.md)
are now also proved equal at leading order, with an
[independent audit](primitive_parity_weight_independent_audit.md).
The complete [mixed-ratio synthesis](protected_mixed_ratios_and_ordering.md)
therefore proves \(Q/O\to13/16\) and \(C/O\to5/4\).
Combining these with the six-cell constants and avoidance expansion gives
the stated protected-phase ordering. The geometric counting and adaptive-root argument below supplies the separate full-shift comparison.

The [absolute primitive-weight calculation](primitive_weight_absolute_constant.md)
now gives a convergent positive Euler product
\[
 \mathcal P=\prod_{p\equiv1\ (4)}
       \frac{(p-1)(p^2+4p+1)}{(p+1)^3}.
\]
The leading mixed means have coefficients
\((32,40,26)\mathcal P/(9\pi^4)\) for O, C, and Q. Adding the six-cell
terms gives the exact protected growth expansion
\[
 r_X(h)=h/2-\tfrac12d_X(\log h)^4+o((\log h)^4),
\]
with
\[
 (d_O,d_C,d_Q)=\frac1{\pi^4}
 \left(45+\frac{32\mathcal P}{9},\ 
       \frac{324}{5}+\frac{40\mathcal P}{9},\ 
       \frac{144}{5}+\frac{26\mathcal P}{9}\right).
\]
The [explicit-constants theorem](protected_phase_explicit_constants.md)
includes the global orientation normalization and audit links.
It determines the leading loss within each protected language.

The new [full protected-row theorem](full_protected_row_leading_pressure.md), with its [independent adversarial audit](full_protected_row_pressure_independent_audit.md), proves
\[
 \log\rho(c_0,h)=\max_{X\in\mathcal X(c_0)}\log r_{c_0,X}(h)
                    +o(\log^4h/h)
\]
for every balanced protected row law \(c_0\), allowing arbitrary column phases. Bad height-sized phase blocks and transitions between good blocks supply local counting deficits. One-sided adaptive rectangle families control all remaining errors, including those adjacent to independently counted guards. Thus the full ordinary and quadratic row shifts have additive coefficients \(d_O/2\) and \(d_Q/2\), respectively. The quadratic full shift eventually has larger entropy by \(\Theta(\log^4h)\).

The [global extension](global_sea_leading_pressure.md), also [independently audited](global_sea_pressure_independent_audit.md), retains a row-defect penalty while allowing all column phases. For \(r=o(h)\) changed rows and \(r\to\infty\), it gives
\[
 \log\rho_c\le\max_X\log r_{c_0,X}
 -a(r/h)\log^2(h/r)+o(\log^4h/h).
\]
Combining this with partition rigidity determines \(R_h=\max_\pi\rho_\pi\) with the quadratic coefficient \(d_Q/2\), and places every maximizing partition within \(o(\log^2h)\) rows of a quadratic law. The marked-resolvent upper bound and quadratic canonical-insertion lower bound give the same expansion for both \(\liminf_m a_h(m)^{1/m}\) and \(\limsup_m a_h(m)^{1/m}\). This does not determine their exact fixed-height equality, the polynomial factor in m, the exact maximizing partition, or its dominant recurrent component.

The [explicit span-tail refinement](polylogarithmic_span_tail.md), with its [independent audit](polylog_span_tail_independent_audit.md), strengthens the optimizer neighborhood to \(O((1+\log\log h)^2)\) rows and proves
\[
 0\le R_h-r_Q(h)\le C\log^2h(1+\log\log h)^2.
\]
The same exact-reference upper excess applies to both maximum-blackout exponential rates and to the canonical quadratic component. The proof retains supports of span \(O(h^2/\log^6h)\), and bounds the omitted mean by \(O(\log^2h(1+\log\log h)^2/h)\). It needs no convergence rate for the arithmetic leading coefficient.

The independently audited [relative defect estimate](relative_sparse_defect_pressure.md)
permits minimum defect spacing \(g_h=h^{o(1)}\), much shorter than the
memory length. Each defect costs a factor \(\exp(-c(\log h)^2)\) relative
to the exact protected-word count, with no extensive bulk-pressure error.
A weighted local-density extension also permits clusters. Arbitrarily
dense defect profiles remain open.

There are also exact structural results for large Cartesian alphabets.
Every constant singleton-free full alphabet is a full residue class.
If an alphabet contained in a balanced row block has more than
\(\lceil h/3\rceil\) rows and excludes singleton and vertical axis rivals,
the row block is exactly ordinary parity. The one-third threshold is sharp.
The proofs are in [the XOR classification](separable_rectangle_xor_classification.md)
and [constant-alphabet stability](constant_alphabet_stability.md).

The [full row-class theorem](full_row_class_phase_classification.md)
removes every column-period assumption. For \(h=6\) and every \(h\ge8\),
a full balanced row-class box on nine columns excludes singleton and
vertical axis rivals exactly when its row and column colors follow the
ordinary or quadratic parity laws. The proof uses only two short
rectangle templates and distance-one and distance-two reflection defects.
Height seven has a genuine modulo-three exception.

The reflection step now has a general quantitative stability theorem:
for any balanced row block \(A\) at height at least eight,
\[
 \operatorname{dist}(A,\text{physical parity})
 \le C\,V(A)/h.
\]
The proof combines an explicit estimate near parity with ordinary
arithmetic removal and the asymmetric \(3k-4\) theorem in the remaining
range. The absolute constant is not evaluated numerically. In particular,
at most \(2M\) violations at every reflection distance imply \(O(M)\)
exceptional rows, without a periodicity or domain-wall hypothesis.
See [the proof](reflection_interval_stability.md) and
[independent source audit](reflection_interval_independent_audit.md).

The [near-full Cartesian theorem](near_full_variable_box_stability.md)
now permits a different alphabet in every column, with at most \(M\)
omissions from its selected balanced row class. For \(h\ge C(M+1)\) and
width at least \(4h+20\), the row coloring differs from an ordinary or
quadratic parity law on at most \(KM\) rows. The column phase follows the
matching law exactly. Both the main proof and its finite-width limitation
passed [independent audit](near_full_variable_box_independent_audit.md).

This does not yet classify arbitrary high-entropy components. The
[container reduction](container_stability_reduction.md) proves that an
almost-half-density container with few singleton-rival hyperedges is
within \(o(h^2)\) cells of a full row-class box. The unresolved step is
an aggregate inverse theorem: few rectangles with exactly three selected
corners must force that full box close to an ordinary or quadratic law.
Pointwise validity of a Cartesian box is stronger than this aggregate
hypothesis.

For bounded-period profiles, the aggregate gap is closed.
[Periodic amplification](periodic_rectangle_amplification.md) reproduces
one nonprotected rectangle obstruction along logarithmically many primitive
directions. A profile of common period \(P\le h^{1/16}\) has at least
\(c h^4\log h/P^6\) rectangles with exactly three selected corners.
Intersecting entropy containers with that profile gives
\[
 r_{c,t}(h)\le (1/2-b/P^6)h
\]
for each fixed nonprotected period \(P\), at sufficiently large admissible
heights. Together with affine entropy capture, this excludes all sea
components confined to any fixed bounded-period parity profile from
competing with the canonical component. The period bound is fixed before
the height grows. [The complete argument](bounded_period_entropy_gap.md)
does not cover arbitrary phase profiles.

The later [general entropy rigidity theorem](near_maximal_partition_rigidity.md)
does cover arbitrary phases at the level of near-maximal entropy.
Every balanced row partition with entropy \(h/2-o(h)\) differs in
\(o(h)\) rows from an ordinary or quadratic protected law. Near-maximal
stationary measures also concentrate, on height-sized intervals, near
the corresponding protected phases. The proof combines vertical-rival
pressure, low phase-profile complexity, and a dense approximate-antiperiod
lemma. It does not require the still-open full aggregate inverse theorem.
This is a stability statement: it does not identify the exact maximizing
partition or prove boundary-component dominance.

An exact pressure comparison gives a sharper reduction when the phase
profile consists of protected domains of length at least \(Ch\).
Let \(r\) be the row distance from a protected reference and put
\[
 P_h(r)=\frac rh\log^2(h/r).
\]
For \(R_0\le r\le\delta_0h\), the combined row-root and domain-wall
families give
\[
 \log\rho_{\mathrm{domains},\sigma}
 \le\log\lceil h/2\rceil-aP_h(r)
       +H_2(\sigma)+C\sigma+Ce^{-ah},
\]
where \(\sigma\) is the fraction of phase-error columns. Those errors
may be arbitrarily clustered. In particular, if
\[
 r\ge K(1+\log h)^2,\qquad
 \sigma\le b\,P_h(r)/\log(e/P_h(r)),
\]
this language has smaller entropy than the best protected reference.
The adaptive primitive-direction cutoff gives the row penalty without
a fixed power-saving restriction on r. Its \(O(\sqrt{rh})\) endpoint
loss is absorbed by the actual wall roots, so no interface prefactor
is needed. See [the proof](separated_domain_partition_comparison.md)
and [independent audit](separated_domain_pressure_independent_audit.md).
The general stability theorem does not yet supply this quantitative
domain-and-error representation, so the conclusion remains restricted.

A larger packet class removes the condition relating total phase-error
density to r. Packets may have width
\(\ell\le h/(1+\log h)^3\), with arbitrary internal error patterns
of density at least \((1+\log h)^{-B}\), for any fixed B.
Their expansions by \((1+\log h)^{10}\ell\) on each side must be
disjoint. The exact packet penalty is
\(\exp[-c|S|\log^2(h/\ell)]\). An averaged diagonal-completion
estimate replaces the maximum-divisor loss, giving the polylogarithmic
separation condition. Packets near a domain wall cost only
\(\exp(o(h))\) descriptions and are absorbed by the wall roots.
The resulting row-pressure bound still leaves only \(O(\log^2h)\)
potentially competitive changed rows.

For an exactly protected row partition, the same domain-and-packet
language satisfies
\[
 \log\rho_{\mathrm{domains+packets}}
 =\max_X\log\rho_X+o((\log h)^4/h).
\]
The proof retains bulk supports of span \(h^{2-\delta}\), loses only
an \(O(\delta)\) fraction of the leading pressure, and takes
\(\delta\downarrow0\) after \(h\to\infty\).
Consequently the quadratic protected phase has larger entropy than
the entire ordinary-parity class covered by this theorem, for large h.
See [the combined proof](polylog_packets_in_protected_domains.md),
[the kernel and packet estimate](polylogarithmic_packet_separation.md),
and [independent audit](polylog_packet_independent_audit.md).
Unrestricted dense phase errors and the full ordinary-parity sea shift
remain outside this comparison.

For an already protected row partition, arbitrary phase profiles are now
controlled. The [aggregate inverse theorem](protected_row_aggregate_inverse.md)
turns the three-corner rectangle count into a one-dimensional XOR test.
Four nearby primitive directions give approximate periods whose gcd is
two. Uniform repair and a Chinese-remainder comparison force the phase
within \(o(h)\) positions of a matched affine or quadratic law.

Consequently, near-half-density containers with few forbidden hyperedges
are within \(o(h^2)\) cells of protected product patterns. A weighted
transversal count then shows that all phase words at a fixed positive
Hamming distance from those patterns have a fixed entropy gap, counting
all such words together. High-entropy stationary sea measures therefore
concentrate locally near the protected phases. See
[entropy concentration](protected_partition_entropy_stability.md) and
[the independent audit](rectangle_inverse_independent_audit.md).
This is local phase concentration, not general component connectivity.

The complementary constant-phase case now allows an arbitrary balanced
row partition. A lifted matrix with few three-one subrectangles is close
to a disjoint union of complete bipartite blocks. Its exact overlaps
permute the large blocks. Repairing all overlap shifts gives a bounded
period, and a uniform Fourier amplification forces ordinary parity.
See [component-permutation repair](component_permutation_repair.md) and
[the periodic estimate](constant_phase_periodic_amplification.md).
Together with transposition and robustness under a small fraction of
phase changes, this also excludes near-maximal entropy whenever the
column phase is close to a protected law but the row partition is far
from every matching law. The unresolved aggregate inverse case has both
row and column laws far from the protected families.

More generally, the column phase can have any fixed period while the
row partition is arbitrary. Taking side scales divisible by that period
supplies complementary row-XOR tests. The lifted repair forces the row
law close to a bounded-period word, after which periodic amplification
forces a protected pair. Thus every fixed nonprotected periodic column
phase, and a sufficiently small Hamming neighborhood of it, has a
uniform entropy gap across all balanced row partitions. See
[the bounded-phase inverse](bounded_phase_arbitrary_row_inverse.md).

The complete odd-row-only graphs at physical heights seven and eight each
have one primitive recurrent component. Their entropies lie respectively
in \([2.771037,2.771038]\) and \([2.715792,2.715793]\). A short valid
seven-row odd prefix nevertheless forces an even next letter, so finite
protected prefixes need not extend inside the protected alphabet.
[The graph certificates and explicit obstruction](protected_components_heights_seven_eight.md)
record both conclusions.

Short variable buffers give positive-fraction entropy capture for
already anchored protected sources, but cannot connect every admissible
core to the same fixed entrance. An explicit quadratic-phase family
forces a mixed collision at distance \(\Theta(h^{3/2})\) from that
entrance, defeating every prescribed \(Ch\) buffer. The
[short-buffer audit](short_buffer_independent_audit.md) and
[fixed-entrance obstruction](short_buffer_fixed_anchor_obstruction.md)
leave adaptive entrances and longer general bridges open.

There is also a simultaneous asymptotic without any dominance hypothesis:
\[
 \log a_h(m)=m\log(h/2)+o(m)
\]
when \(h\to\infty\) and
\(m/[h^2(1+\log h)^{3+\varepsilon}]\to\infty\), for any fixed
\(\varepsilon>0\). The upper bound counts one-or-two-cell columns with
the same container fingerprints. The lower bound appends a long buffered
odd-row core to the completed threshold construction. The reserved
construction columns account for the extra logarithm in this width regime.

## Finite-width progress

The seven-row values use exhaustive searches after analytical reduction to complete axis-valid column families. Witnesses are independently checked by actual rectangle presentations. Search coverage, symmetry reduction, and the larger-column classification are recorded in the linked notes.

The \(7\times11\) witness has two triple columns. This explains the previous obstruction in searches restricted to doubles, without proving the old proposed scalar rule at other widths.

The earlier eighteen-board list at \(7\times8\) now has an independent
completed enumeration. Every first-column mask is covered, and a different
rectangle generator checks all 866 presentations on every board.
Thus \(a_7(8)=18\); the
[count note](seven_eight_exact_count.md) records the exact computational scope.

The \(7\times13\) value disproves that rule for unrestricted blackouts: it predicts 22, whereas a checked 23-point witness is optimal. The \(7\times14\) upper bound uses a complete 229-core classification and exhaustive ordering search. Its 24-point witness is independently checked by actual presentations.

There are exactly eight optimal \(7\times13\) blackouts on the labeled grid.
The proof excludes all but three row cores, then counts projected black-point
assignments in those cores. A separate full-presentation-fiber encoding gives
the same count. Two representatives generate the eight distinct boards by
horizontal and vertical reflection; each board is checked against all 2,333
rectangles using two independent rectangle generators.

There are exactly eighty optimal \(7\times14\) blackouts. The complete
search covers 2,683 row cores modulo reflection, including the nineteen
full \(K_{3,4}\) cores with two empty columns. Twenty-two projected
models expand to eighty distinct labeled boards. An independent
equal-diagonal generator verifies all 2,691 rectangle presentations
for each board. See [the count audit](seven_optimum_count14_independent_audit.md).

Equality-board windows retain more structure than arbitrary valid boards. They have only singleton and double columns, and retain the final balanced pair set for virtual axis rivals. This gives stronger cropping constraints than unrestricted optimum values alone.

In particular, a completed 1,164-core search proves that a fourteen-column
equality window contains at most nine doubles. Since a seven-row equality
board must contain twelve doubles in total, its width is at least 17. This
does not assert that every ordinary valid fourteen-column board has at most
nine doubles.

Complete searches of all 19 balanced row cores modulo reflection then
exclude widths 17, 18, 19, and 20. A width-21 witness has a verified
transition to an infinite constant tail. Therefore \(m_0(7)=21\), and
cropping a boundary double from that witness also proves \(f(7,20)=31\).

There are exactly four optimal \(7\times21\) boards. A completed projected
enumeration covers all 35 balanced row cores, reduced to 19 reflection
classes. Only the ordinary-parity core has models. Two stored models and
their horizontal reflections give the four distinct boards, each with
33 black cells. An independent equal-diagonal generator checks all 5,785
rectangle presentations for each board. The complete coverage and
symmetry audit is [recorded separately](seven_equality_count21_independent_audit.md).

At the preceding width, there are exactly \(a_7(20)=3364\) optimal
boards, each with 31 black cells. All 229 deficit-one row cores have
completed projected enumeration records. An independent catalog and
reflection checker expands 843 projected models to those 3,364 boards
and verifies all 5,280 actual rectangle presentations on each.
The [count and verification scope](seven_optimum_count20.md) are saved
with the full board list.

Further complete deficit-one core searches give
\[
 f(7,15)=25,\quad f(7,16)=26,\quad f(7,17)=27,\quad
 f(7,18)=29,\quad f(7,19)=30.
\]
The upper bounds at widths fifteen through seventeen exhaust all 229
possible deficit-one row cores. The
eighteen- and nineteen-column witnesses meet the upper bound obtained by
excluding equality.

Including the previously proved smaller-height cases by transposition
gives the complete seven-row size formula:
\[
 f(7,m)=
 \begin{cases}
 m+6,&1\le m\le3,\\
 m+7,&4\le m\le7,\\
 m+8,&8\le m\le10,\\
 m+9,&11\le m\le12,\\
 m+10,&13\le m\le17,\\
 m+11,&18\le m\le20,\\
 m+12,&m\ge21.
 \end{cases}
\]

The values through width seven use the existing thin-grid formulas and
the manuscript's four-, five-, and six-row results; width eight was
already established there. The newly completed searches supply widths
nine through twenty and the exact threshold. This is a complete formula
at height seven, not a proposed pattern for other heights.

The general row-tree analysis also gives the exact axis-only optimum near the equality threshold, and a classification of all large-column cases at the relevant boundary. These are constraints on a full solution, not substitutes for the tilted-rectangle conditions:

* [Finite-width and square progress](square_finitewidth_progress.md)
* [Large-column boundary classification](large_column_boundary_classification.md)

## What is still open

1. A simple exact expression for \(f(h,m)\) at every pair of dimensions, especially below the equality threshold.
2. An absolute quadratic equality threshold, or a lower bound proving that a growing factor is necessary.
3. General boundary-component dominance and identification of the maximizing balanced partitions. Ordinary-parity partition dominance is false.
4. Finer sea-entropy terms beyond the proved correction
   \(-c_Q(\log h)^4\), and exact values within the remaining
   \(O((\log h)^2(1+\log\log h)^2)\) excess over the protected quadratic rate.
5. Closing the square gap between the existing lower construction of order \(n^{6/5}(\log n)^{-1/5}\) and upper bound \(n^{4/3}(\log n)^{-1/3}\).

The exact matrix formula gives an unconditional computational answer to both finite-grid questions. The unresolved points concern the structural general answer requested for the paper.

A precise next target for component dominance is the
[returning-gate lemma](exact_canonical_gate_and_uniqueness_limits.md):
modify a finite interval of a periodic sea, preserving its two exterior
memory-length collars, so that it contains a constant row-one history.
Such a modification puts that recurrent component in the canonical
component. It is enough to treat components whose entropy is at least
the canonical entropy. The same note checks why the currently available
sampling-local-lemma and nearest-neighbor uniqueness theorems do not
directly apply at our parameters; it does not rule out other cluster or
coupling arguments.
