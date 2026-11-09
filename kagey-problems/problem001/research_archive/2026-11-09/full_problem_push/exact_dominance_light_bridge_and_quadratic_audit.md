# Audit of the light-window criterion and quadratic wall extension

9 November 2026. This note audits
[exact_dominance_attempt.md](../exact_dominance_attempt.md), with emphasis on Sections 6--8. It does not modify that source.

The deterministic light-window bridge is valid and extends to the quadratic protected row laws. The rectangle-XOR rule also extends exactly. The source's wall entropy argument has a gap: the new vertical-rival family has logarithmically growing incident and conditional load, so the protected first-order avoidance expansion cannot be applied to its combined wall family. A separate growing-collar argument now repairs that gap; see [same_slope_wall_resolution.md](same_slope_wall_resolution.md) and [its independent audit](same_slope_wall_resolution_independent_audit.md).

No claim in the pending changed-black-letter restoration draft is used here.

## 1. The deterministic light-window bridge passes

For one protected phase, the complete forbidden family has four or six required black cells. A length-L buffer prevents any such support from meeting both the fixed core s and the anchor tail.

After removing every letter that creates a one-free-cell event, the remaining event families are:

1. events meeting the core and at least two free buffer columns;
2. events using only buffer and tail cells.

Their total probability mass through a free column is at most 1/50 under the source's two load assumptions. With \(x_E=2\Pr(E)\), an event has at most six free variables, so
\[
 \sum_{F\sim E}x_F\le6\cdot2/50<1/2.
\]
The product bound \(\prod(1-x_F)\ge1-\sum x_F\) verifies the local lemma. Each individual x_E is also less than one, since its probability is included in a column load.

Singleton reduced alphabets cause no problem. They are deterministic variables, and retaining their columns in the dependency graph only enlarges the neighbor set. The explicit load condition already rules out a nonzero probability-one event.

The right extension gives a path from s to the canonical component. The reflected left extension gives a path back to s. This is enough for membership; it is stronger than a one-way escape.

The conclusion concerns a full-memory state in the normalized sea graph. It does not assert that every finite rectangle-contained pure word is such a state.

### Quadratic extension

Write
\[
 c_0(y)=q(y)+\beta y+\eta,\qquad
 X(x)=q(x)+\gamma x+\delta,\qquad
 q(n)=\binom n2\bmod2.
\]
For
\[
 F(x,y)=c_0(y)+X(x)
\]
and perpendicular integer side vectors U,V,
\[
 F(P)+F(P+U)+F(P+V)+F(P+U+V)=0.
\tag{1}
\]
Thus three phase-compatible black corners have a phase-compatible completion, and a vertical displayed pair has equal row colors. The same four/six support reduction applies.

For beta=0, use the phase-compatible anchor on rows 1 and 2. Its sequence is a shift of 1122. The universal anchor lemma in
[quadratic_parity_entropy_capture.md](quadratic_parity_entropy_capture.md)
places every such anchor phase in the boundary component containing row 1.

For beta=1, rows 1 and 2 have the same color, so that anchor would be incorrect. Use rows 2 and 3 with a phase of 2233. The explicit connection to row 1 and the low-pin adjustment are proved in
[quadratic_low_anchor_complement_wall.md](quadratic_low_anchor_complement_wall.md).

Use the high-row buffer alphabet
\[
 P_x=\{y\ge8:c_0(y)=X(x)\}.
\]
Its size is \(h/2+O(1)\). The audited low-pin geometry gives incident pressure \(O_\varepsilon(h^{-1/2+\varepsilon})\), with no three-pin mixed support or five-pin six-cell support. These are exactly the ingredients needed by the lightness proof.

Therefore the same deterministic membership theorem holds for each quadratic row law, using its boundary component. Balance is not needed for this particular bridge; it matters when comparing extremal row partitions.

### General impure windows

The conditional generalization in Section 8 is valid if its event list is complete. For an impure s, the list must include singleton-axis and vertical-axis rivals, as well as four/six supports.

One should either use the unprojected singleton support, including the selected black cell in the completion column, or explicitly test all zero-free events after conditioning. A projected triangle can otherwise have its three black cells in s but a completion phase fixed by the new buffer. It cannot be dismissed merely because s was previously allowed.

With zero-free events absent, all unary events removed, and the remaining reduced-alphabet loads satisfying the same bound, the local-lemma proof applies. The unresolved statement is that every competitive component contains such a window.

## 2. The exact wall-XOR rule is the same for quadratic phases

Let \(X_2-X_1=d\), where \(d(x)=ax+b\) over \(\mathbb F_2\). This difference is affine even when both phases are quadratic.

At a wall at zero, put
\[
 \epsilon(x)=1_{\{x\ge0\}}.
\]
If three black corners obey their side's phase, (1) shows that their completion disagrees with its side's phase exactly when
\[
 \sum_{\text{four rectangle corners }P}
       \epsilon(x_P)d(x_P)=1.
\tag{2}
\]
Thus Lemma 5 transfers unchanged to the quadratic row law.

For a hidden, mixed-four, or genuine six-cell support H, symmetric difference of rectangle identities gives
\[
 \sum_{P\in H}F(P)=0.
\tag{3}
\]
Consequently compatibility of H with the wall implies
\[
 \sum_{P\in H}\epsilon(x_P)d(x_P)=0.
\tag{4}
\]
For a complement wall, d=1, so the required black support must have an even split. This necessary split condition is the same for ordinary and quadratic protected laws.

For a six-cell support, let the two underlying rectangles share W. Their mismatch bits from (2) agree, because the six black assignments share the same completion color at W. If the common bit is one, each triple is already a forbidden singleton-rival support. The six-cell event is then redundant in the minimal wall family. If the common bit is zero, both rectangles have phase-compatible completions.

The finer acceptance densities do depend on the row law. An even split is necessary, not a sufficient residue criterion.

## 3. Correct weighted quadratic long-gap densities

For a long rectangle, write
\[
 S=k(u,v),\qquad T=\ell(-v,u).
\]
A cut in its long gap separates \(\{P,P+T\}\) from \(\{P+S,P+S+T\}\). The pure condition is
\[
 \Delta_S F=0,\quad \Delta_T F=0,
\]
and the complement-wall condition is
\[
 \Delta_S F=1,\quad \Delta_T F=0.
\tag{5}
\]

The span-weighted scale sum does not make ell uniform modulo four. Its leading weights are proportional to \(\ell^{-2}\), giving
\[
 \Pr(\ell\text{ odd})=3/4,\quad
 \Pr(\ell=2\bmod4)=3/16,\quad
 \Pr(4\mid\ell)=1/16.
\tag{6}
\]
The long scale k is uniform modulo four in the leading term.

Average the root parity uniformly over \(\mathbb F_2^2\). If u,v are both odd, the two odd-scale increment forms are A and A+1. If u,v have opposite parity, they are independent linear forms. Direct enumeration gives
\[
\begin{array}{c|cc}
\text{primitive type}&\text{pure}&\text{complement wall}\\ \hline
\text{odd,odd}&3/8&1/4\\
\text{opposite parity}&7/32&7/32.
\end{array}
\tag{7}
\]

The root-parity averaging is compatible with conditioning \(F(P)=0\). For each prescribed parity pair of x_P,y_P, the same number of modulo-four lifts satisfy F=0. Long cut-translation intervals and row sums provide these lifts with lower-order residue errors. The leading partner degree for the quadratic law is uniform in the root parity, so it creates no additional correlation.

Let
\[
 a=\sum_{v\ {\rm odd}}\frac{\phi(v)}{v^3},\qquad
 b=\sum_{v\ {\rm even}}\frac{\phi(v)}{v^3}=a/6.
\]
For odd v, the two parities of primitive u have equal leading weight. For even v, u is odd. Thus (7) gives
\[
 C_{{\rm Q},0}
 =\frac{19a}{64}+\frac{7b}{32}
 =\frac a3,
\]
\[
 C_{{\rm Q},{\rm wall}}
 =\frac{15a}{64}+\frac{7b}{32}
 =\frac{13a}{48}.
\tag{8}
\]
The quadratic long-span ratio is therefore 13/16.

This calculation checks the residue component of the corrected span computation supplied by the parallel audit. It does not identify an exact wall partition function.

The source's original unweighted scale table cannot determine the span constant. For example, v=1 and \(h/2<u<3h/4\) force ell=1 by vertical containment. This range contributes at the leading span scale. Replacing its parity by density one half changes a leading constant.

## 4. The stated mixed crossing bound is false

The source claims that mixed-four crossing weight is \(O(\Lambda^4)\). The following protected all-odd family gives a lower bound of order h.

Take b,r odd, with b,l,r each in suitable fixed positive fractions of h. Put
\[
 A=(0,r),\qquad B=(2,r+2b),\qquad T=2l(-b,1).
\]
The common displayed side has endpoints A+T and B+T. Its alternate black diagonal is
\[
 V=(2b,2),
\]
which has the same length as B-A. The other required black cells are
\[
 C=(1-b-2lb,\ r+2l+b-1),
\]
\[
 D=(1+b-2lb,\ r+2l+b+1).
\tag{9}
\]
All four required rows are odd. The four black columns are distinct for b>1, and both rectangles are nondegenerate. For example, choose
\[
 h/20\le b,l\le h/10,\qquad h/10\le r\le h/5.
\]
All geometric rows then fit in the strip.

There are \(\Theta(h^3)\) normalized supports, of span \(\Theta(h^2)\), and each has probability \(\Theta(h^{-4})\). Hence their crossing weight is \(\Omega(h)\).

The horizontal extent comes from the connector T. It does not require a long black diagonal, so the claimed angular cancellation does not cover this family.

A sharper \(o(h\Lambda^2)\) upper bound has been established separately in
[the crossing-mass audit](exact_dominance_crossing_mass_independent_audit.md).
That corrected bound is compatible with (9). The \(O(\Lambda^4)\) assertion itself is not.

## 5. A wall has logarithmically growing vertical-rival load

The remaining obstacle is not just a lattice-count error. New wall events fail the small conditional-extension test used for protected phases.

First take an odd/even wall. Fix a black cell A just to the left of the cut, at an odd row in the central third of the strip. For every integer Pythagorean triple
\[
 d_x^2+d_y^2=\ell^2,
\]
with d_x even, d_y and ell odd, and \(\ell\le h/16\), choose the partner
\[
 B=A+(d_x,d_y)
\]
on the right. Its row is even. The vertical alternative diagonal has integer endpoints, odd length ell, and lies inside the strip. It is a parity-axis rival.

There are \(\Theta(h\log h)\) such triples. An elementary proof uses primitive opposite-parity coprime parameters in dyadic annuli and odd dilations. Each primitive-hypotenuse scale contributes order h distinct dilated triples.

Conditioned on A being black, each partner assignment has probability \(\Theta(1/h)\). Therefore
\[
 \sum_{V\ni A}\Pr(V\mid A\text{ black})=\Theta(\log h).
\tag{10}
\]
Summing over the central allowed rows of A shows raw incident weight \(\Theta(\log h)\) at its near-wall column as well.

The same lower bound holds for opposite checkerboard phases: the even horizontal gap preserves column parity while the complement wall changes the required row parity.

It also holds for a quadratic complement wall. The even leg of an odd-hypotenuse triple is divisible by four. For each triple, choose one of the two signs of the odd vertical leg. These signs give opposite changes of the quadratic adjusted color, so one choice makes B match the complemented right phase. The rectangle XOR identity then makes the two vertical displayed row colors different. The central row choice leaves room for either sign.

Thus neither \(x_E=2\Pr(E)\) nor the protected \(p(1+o(1))\) conditional expansion is verified for the combined wall family. The load in (10) diverges.

## 6. What is actually needed to turn the mass sign into an entropy sign

For a complement wall, let B_wall be its universal four/six family and let T_wall,V_wall be the new minimal singleton and vertical families. The universal family still has small local-lemma pressure on its own.

A sufficient additional estimate is
\[
 \Pr(\operatorname{avoid}(T_{\rm wall}\cup V_{\rm wall})
       \mid\operatorname{avoid}B_{\rm wall})
 \ge \exp[-o(h\Lambda^2)].
\tag{11}
\]
Together with a rigorous favorable four/six crossing-mass difference, (11) would establish a positive wall factor at that scale.

An upper bound \(O(h\Lambda)\) on the expected number of new wall violations does not prove (11). Nor does the local lemma for the universal four/six family prove a local lemma for the enlarged family. Equation (10) gives the explicit missing hypothesis.

The first-order formula for protected bulk is therefore not a first-order formula for the full wall. The source alone does not prove (11). The separate [growing-collar proof](same_slope_wall_resolution.md) changes the local product space and proves the required joint lower bound. Its audited conclusion includes a positive relative complement-wall gain and a canonical growth excess of order at least log-squared h. The source's light-window measure and general component claims still require the missing hypotheses described next.

## 7. Measure claims remain separate from the deterministic bridge

The pure-window lightness criterion is deterministic. Its validity does not depend on Proposition 9.

The codegree hypothesis in Section 7 is false in its stated form; a separate audit gives an explicit mixed-four family. Even apart from that issue, the weighted load with at least two free cells is not proved in the source. Thus the assertion in Section 8 that fixed-phase measures have light windows with overwhelming probability is not established there.

Finally, closeness of entropy rates is not closeness to one fixed-phase measure. A measure assigning positive weight to other phase profiles is not absolutely continuous with respect to a measure supported on one pure phase. A Donsker--Varadhan comparison needs an actual relative-entropy bound in a common support, not just a comparison of the two entropy values.

The valid conclusion is the conditional gate statement: if a competitive component contains a window with a complete, light buffer event system on both sides, then it is the canonical component. Proving that premise remains the exact dominance problem.

