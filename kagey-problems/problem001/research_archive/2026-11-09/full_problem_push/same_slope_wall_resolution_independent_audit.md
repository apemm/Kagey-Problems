# Independent audit of the repaired same-slope wall theorem

9 November 2026. The theorem in [same_slope_wall_resolution.md](same_slope_wall_resolution.md) passes this independent review, including the quadratic complement wall and the canonical rate consequence. The argument repairs the missing mass-to-avoidance step in the original attempt. It does not prove exact component dominance.

## 1. The quadratic residue and anchor inputs

Direct modulo-four enumeration gives the weighted long-gap factors
\[
\begin{array}{c|cc}
 &\text{pure}&\text{complement wall}\\ \hline
u,v\text{ odd}&3/8&1/4\\
u,v\text{ of opposite parity}&7/32&7/32.
\end{array}
\]
Here k is uniform modulo four, while the ell weights are \(1/16,3/8,3/16,3/8\) for residues \(0,1,2,3\). Averaging the root over the eight modulo-four points satisfying its protected law gives these values. The same result holds for the translated quadratic variants.

With \(a=\sum_{v\ {\rm odd}}\varphi(v)/v^3\) and \(b=a/6\), the pure coefficient is \(a/3\) and the complement coefficient is \(13a/48\). Their ratio is \(13/16\). The independently audited span argument therefore gives
\[
 {\cal G}_{\rm Q}
 =\left(\frac8{315}\frac{\zeta(2)}{\zeta(3)}+o(1)\right)
       h\log^2h.
\]

The anchor for q is the natural \(2211|1122\) splice. For q+y it is \(3322|2233\), with the four central row-2 cells replaced by row 1. The replacement preserves the prescribed phase. These are specific cut alignments. Reversing the complement orientation at the same cut is not covered: the naive q anchor would have four row-2 cells and a vertical rival. The full case proof is in [quadratic_low_anchor_complement_wall.md](quadratic_low_anchor_complement_wall.md).

In particular, the q+y repair has two three-black triangles. Their completions are distinct row-5 cells with the same row color as the selected row-1 cells. They are safe. At collar radius \(R>10h\), no rectangle involving an outer free cell can share either completion. Thus treating these anchors as valid does not silently require them to be triangle-free.

## 2. The partially pinned and new wall families

The universal pinned four/six counts extend to pins in rows 1--3 and high free rows, in either horizontal ordering. The only worst case is mixed four with two pins, with \(O_\epsilon(h^{3/2+\epsilon})\) normalized supports. The conic degeneracies remain controlled when the pin-row difference is any bounded value: negative connector heights enter the small-X case, zero discriminant has only boundedly many Y values, and zero leading coefficient forces bounded x.

Three pins in a four-cell support, or five pins in a six-cell support, force the sole free row to remain bounded. A fixed cutoff of 30 removes these unary events. The remaining incident mass is \(O_\epsilon(h^{-1/2+\epsilon})\). Normalizing at a pin and summing its O(R) positions gives the stated \(O_\epsilon(Rh^{-1/2+\epsilon})\) total mean.

The exact rectangle-XOR identity shows that a new singleton triangle has an odd split. Its two nearest corners to the cut are at distance at most h. With the wide collar, any surviving free event has exactly one low pin and two free black cells. Both free-corner roles are included in the estimate
\[
 C\left(h^2\Lambda/X^2+h/X\right),\qquad X\ge R.
\]
This is uniformly small for \(R=A_0h\sqrt\Lambda\) with A_0 large. Its total mean is \(O(h\Lambda)\). New vertical rivals cross the cut over horizontal distance at most h, so they are entirely pinned and are excluded by anchor validity.

The original unrestricted near-wall load is \(\Theta(\log h)\). The proof does not reuse a small-load claim for that product space. It first changes the product space by fixing the collar.

## 3. Exact interface conditioning

The lower bound starts from the exact two internal partition functions. Restriction to the outer columns loses at most \(h^{2R+1}\) extensions. The low-letter exclusions cost only \(\exp[-O(h)]\) by the conditional local lemma.

For the unpinned universal crossing family, raw and compatible conditional extensions are small. Its conditional first-order expansion is therefore valid relative to the internal protected families. The remaining pinned and triangle events are then added by the conditional local-lemma product bound. Their cost is
\[
 O(h\Lambda)+O_\epsilon(Rh^{-1/2+\epsilon})
       =o(h\log^2h).
\]
The collar cost \(O(R\log h)\) has the same required smaller order.

For the matching upper bound, one ignores the new two/three-cell events and keeps only universal crossing four/six events. This uses the valid protected expansion and gives
\[
 J_{XY}=-W_{6,XY}+o(h\log^2h).
\]
No approximate finite-volume pressure formulas are subtracted with uncontrolled extensive errors. The conditioning is directly on crossing events, as required.

## 4. Wall lattices and canonical capture

Choose complementary domains of length \(n=DL+O(1)\), with fixed \(D>4\). For the quadratic laws, require \(n\equiv2\pmod4\). Since \(q(x+2)=q(x)+1\), the two-column cut shift and the alternating complement both flip the local phase constant. Every wall therefore has the same audited anchor alignment. Domain lengths divisible by four would instead alternate the local orientation and are not justified by this anchor. The collars are disjoint, and no support meets two walls. The finite protected-word expansion has the surface correction
\[
 \log Z_X(n)=n\log r_X+W_{6,X}+o(h\log^2h).
\]
The error from the bulk avoidance expansion is \(O(nh^{-2+\epsilon})\), which is lower order at \(n=O(h^2)\) for fixed epsilon<1. Changing a domain length by at most two contributes only a bounded-end correction, also lower order; the conditional protected local lemma supplies the corresponding partition-function padding estimate. Mixed and hidden surface means are also lower order. The relative wall gain therefore contributes a positive constant times \(\log^2h/h\) to the logarithmic growth rate. Complementary-phase rate differences \(O(1/h)\) are smaller.

For capture, leave a pure end domain of length more than 2L at each end. Append high-row protected buffers and the appropriate periodic anchor tails. An event touching an outer tail cannot reach an internal wall. The boundary family is therefore the already controlled protected pinned family.

Place the core, wall, and boundary events in a single local-lemma system. Its boundary and universal loads vanish; its wall-triangle load is a sufficiently small absolute constant fixed by A_0. The conditional product inequality gives
\[
 \Pr(\text{avoid boundary events}\mid
          \text{avoid all core events})\ge c_h>0,
\]
where c_h is independent of the number of domains. Every core assignment has the same product probability for this prescribed lattice. Thus a fixed positive fraction of the counted lattice cores has the required extensions.

Both periodic anchors lie in the boundary component. Fixed connecting paths at the two ends turn the extensions into paths within that component at a bounded length cost. Restricting to one parity of the number of domains fixes the endpoint phases if necessary. This proves
\[
 \lambda_{*,X}(h)\ge r_X(h)+c\log^2h
\]
for all sufficiently large h, including X=Q.

The result gives a genuine logarithmic excess over the exact protected rate. It does not determine the best wall spacing, classify all maximizing components, or prove exact quadratic-partition optimality.

