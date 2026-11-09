# Counting follow-up: insertion is reduced to component dominance

Research results, 8 November 2026. This follows the request to prioritize the counting formula.
The preceding reports and manuscripts are unchanged. No commits were made.

The main progress is a primitive sea component with positive insertion weights for every balanced
partition. General dominance is not proved. The remaining problem is now more precise than the
original three separate transfer-matrix assumptions.

## 1. The quadratic threshold lower bound is already available

The paper's equality-structure theorem forces exactly \(q_h=\lfloor h^2/4\rfloor\) distinct
double columns whenever \(f(h,m)=m+q_h\), for \(h\ge4,m\ge3\). Therefore

\[
 m_h\ge q_h=\Omega(h^2).
\]

This is already the paper's small-width corollary. The open threshold-order problem is the
matching \(O(h^2)\) upper bound, not the lower bound.

## 2. A primitive component admitting every double

Fix any balanced partition \(\pi\), and use its full pair set when testing sea words. Let
\(L=2W_h\) be the memory length. The constant boundary states \(1^L\) and \(h^L\) lie in
one strongly connected component \(C_{\pi,*}\).

The key observation is that the single-switch sea \(1^\infty h^\infty\) is valid for every
partition. Its weak tilted rectangles have the two boundary black points as a diagonal. Their
white points have no axis rival, and midpoint and length determine the black diagonal uniquely.
The reverse switch is valid too. Hence \(1^Lh^L\) and \(h^L1^L\) connect the boundary states.
Their self-loops make this component primitive.

For every double \(e\in E_\pi\), the paper's isolated-double geometry gives the valid bridge

\[
 1^L\ e\ h^L.
\]

It therefore inserts \(e\) from \(C_{\pi,*}\) back into \(C_{\pi,*}\), with strictly
positive insertion weight. Write \(\lambda_{\pi,*}\) for the component's Perron root.
It is greater than one. For even heights it is at least two, because every word on the two
boundary rows is valid.

Parity gives a stronger structural result: every adjacent-row alphabet \(\{r,r+1\}\) is a
full two-shift. Consequently all constant-row states belong to its component \(C_*\), and
\(\rho_*:=\lambda_{{\rm par},*}\ge2\) at every height.

These facts give the unconditional lower bounds

\[
 b_\pi(m)\ge c_{h,\pi}m^{q_h}\lambda_{\pi,*}^{\,m},
 \qquad
 a_h(m)\ge c_hm^{q_h}\rho_*^m
\]

for sufficiently large widths. Here \(b_\pi\) counts completed equality words for that partition.
Fix a double order, use the insertion bridges, and distribute the remaining width among the
\(q_h+1\) intervening sea paths. Primitivity gives exponentially many paths between the fixed
endpoints, and the compositions supply the factor \(m^{q_h}\).

Full proofs and finite checks: [insertion_adjacent_component.md](insertion_adjacent_component.md).

**What this does not prove.** A component with larger entropy might exist elsewhere. The new
\(\rho_*\) must not be identified with the earlier full parity sea entropy \(\rho_h\) without
proving dominance. In particular the earlier bound \(\rho_h\ge c h^{1/3}\) does not yet imply
the same bound for \(\rho_*\).

## 3. Hidden rectangles no longer obstruct the parity formula

If a hidden tilted rectangle has an oblique diagonal, cross that diagonal's two row coordinates.
The crossed pair and its other black diagonal form a second tilted rectangle. The crossed pair
and the original diagonal form an axis-aligned rectangle. These two rectangles have symmetric
difference equal to the four original black corners, so their presentations coincide. Every point
stays in the original bounding box.

If both diagonals are axis-parallel, the rectangle is a square diamond. A diamond of size at
least two has a nonprimitive side vector; subdividing along that side again gives two rectangles
whose symmetric difference is its black corner set. Thus, when both grid dimensions are at least
three, the only possible hidden rectangle in a valid blackout is a unit diamond.

This has three useful consequences:

* Every valid sea word is hidden-free, for every partition.
* Every parity equality word is hidden-free, including arbitrary singleton seas and free
  transition gaps. Its double columns cannot contain the diamond's even-distance vertical pair.
* Other partitions need only keep a global count of unit diamonds. Each is centered at a double
  and is detected in a three-column window. It cannot create an independent defect far inside a sea.

The exception is real: the \(3\times4\) columns \(\{2\},\{1,3\},\{2\},\{2,3\}\)
form a valid nonparity optimum with one hidden unit diamond.

Proofs and checked identities: [hidden_rectangles_and_threshold.md](hidden_rectangles_and_threshold.md).

## 4. An exact replacement for the marked transfer argument

Use full local histories, including transient histories containing a double. Let \(T\) append
singletons without creating a hidden rectangle, and let \(E_e\) append double \(e\).
For parity, put \(R(z)=(I-zT)^{-1}\). Then the exact completed-word generating function is

\[
 F_{\rm par}(z)=\sum_{\sigma\in S_q}
 \alpha R(z)zE_{\sigma(1)}R(z)\cdots zE_{\sigma(q)}R(z)\beta.
\]

This counts close doubles without ambiguous overlapping insertion windows. For other partitions,
square-free markers also record whether one unit diamond has appeared. Its correction is local
to an insertion and does not add an independent polynomial degree.

Unconditionally, all exponential bases are sea eigenvalues. The exact automaton gives a finite
exponential-polynomial expansion. After passing to a computable common period \(p\), it gives

\[
 a_h(pn+r)\sim C_{h,r}\,n^{d_{h,r}}\Lambda_{h,r}^{\,n}.
\]

The exponent \(d_{h,r}\) is the largest number of useful maximal-radius components on one
start-to-accept path, minus one. This is a rigorous general asymptotic description, but not the
desired simple uniform formula in \(h\).

Two corrections to Appendix A are necessary. If a sea path can visit \(k\) maximal-radius
components, marked insertions can reset that chain. The generic upper-bound degree is therefore
\((q_h+1)k-1\), rather than \(q_h+k-1\). Also the subdominant remainder needs its own Jordan
or pole-multiplicity bound; \(O(m^{q_h}(\rho')^m)\) does not follow automatically.

Full exact formulas, the hidden correction, and proofs:
[exact_counting_scc_and_resolvent.md](exact_counting_scc_and_resolvent.md).

## 5. What remains for the simple counting formula

For the parity product formula, it suffices to prove that \(C_*\) is the unique maximal-entropy
parity sea component. Primitivity and every \(\kappa_e>0\) would then follow from section 2.
Strict dominance over other balanced partitions would identify parity as the source of the full
optimum asymptotic.

There is also a route that does not require proving parity is the winner. If \(C_{\pi,*}\) is
uniquely dominant for every balanced partition, then

\[
 b_\pi(m)\sim C_\pi m^{q_h}\lambda_{\pi,*}^{\,m},\qquad C_\pi>0.
\]

With \(\Lambda_h=\max_\pi\lambda_{\pi,*}\), summing gives

\[
 a_h(m)\sim m^{q_h}\Lambda_h^m
       \sum_{\lambda_{\pi,*}=\Lambda_h}C_\pi.
\]

For parity, \(C_\pi=B_\pi\prod_e\kappa_{e,0}\). Other partitions can have the explicitly
derived one-diamond correction. Strict parity dominance would simplify this finite maximum and sum,
but it is not logically necessary for a clean \(m^{q_h}\Lambda_h^m\) formula.

Both arbitrary-height component dominance and arbitrary-height parity dominance remain open here.

## 6. Dominance has geometric content beyond Perron--Frobenius theory

Each sea word has a partition-compatibility graph on its rows. Its edges are the exposed row pairs
from singleton and vertical presentations. Once partition-independent tests pass, a partition
admits the word exactly when every connected component of this graph is monochromatic.

This proves that parity is the unique nontrivial partition admitting all constant-row seas.
It does not prove entropy dominance. Already at height four the partition languages are
incomparable under identity. One nonparity shift embeds in parity after swapping two symbols;
the other admits no such embedding under any row-symbol permutation.

Exact height-four graph construction and integer Collatz bounds do independently certify strict
parity dominance. The parity graph has 2,368 states and 7,938 edges and is strongly connected.

Global irreducibility is not available as an arbitrary-height shortcut. At height ten a valid
word reachable from the boundary component has no allowed next sea letter. Two right-angle
completions in the next column force opposite parities. This is a transient dead end, so it
does not disprove dominance among recurrent components. Immediate boundary padding also fails
for an explicit valid Sidon-alphabet word at height fifteen.

Dominance results and exact certificates: [dominance_partition_analysis.md](dominance_partition_analysis.md).

Finally, the numerical evidence does not give exact entropies through height twenty. The larger
heights in the earlier report use Monte Carlo estimates, often for restricted odd-row seas.
Their actual entropies are lower bounds on the full entropy; the Monte Carlo point estimates
are not certified bounds by themselves.

## 7. Verification and scope

The new geometric and matrix proofs were independently reviewed. Reproduction scripts check
3,584 adjacent-row words and 33 isolated parity doubles. Across all balanced partitions through
height seven they also check 122 boundary switches and 588 isolated doubles, together with 3,328
boundary words at even heights. Further checks verify the padding and dead-end certificates, the
hidden classification identities, and the exact height-four graphs, spectral inequalities, and symbol maps.
All completed checks passed. No inference about arbitrary-height dominance is made from them.

The substantive next target is dominance of the boundary component among recurrent components.
The present work establishes its aperiodicity and insertion positivity, supplies exact counting
formulas without those dominance assumptions, and removes the hidden-rectangle ambiguity in the
parity case. It does not solve the general threshold construction or the intermediate-width values.
