# Exact canonical dominance: a returning gate and limits of generic uniqueness criteria

9 November 2026. The leading pressure is now determined, but it does not imply uniqueness of the maximizing recurrent component. This note records a precise finite-edit target and checks several possible shortcuts against their actual hypotheses.

Fix h and a final row partition. Let G be the finite history graph with memory L, let \(g=1^L\) be its constant-row-one state, and let C_* be the canonical strongly connected component containing g.

## 1. A returning-gate lemma

**Lemma.** Let C be a recurrent strongly connected component. Suppose there is a periodic sea word supported on C that admits a finite modification with the following properties:

1. Outside a finite interval the word is unchanged.
2. The modified word is valid.
3. The modified interval contains L consecutive row-one letters.

Then \(C=C_*\).

**Proof.** Take a left cut before the first edit and a right cut at least
L columns after the last edit. Both histories then belong to C, because
their complete L-column windows are unchanged. The modified word gives
a path from the first history to g and then to the second history.
Inside C there is a path from the second history back to the first.
Thus g and C are mutually reachable. They belong to the same strongly
connected component. This is C_*.

It is enough to establish this modification for one periodic word in every component whose Perron root is at least that of C_*. Establishing it for every periodic sea proves that C_* is the only recurrent component.

The modification need not have a width uniform in h or in the chosen periodic word. At each fixed h, existence is enough. For a constructive proof, it is sufficient to preserve the original L-column collars at both ends of the modified interval and validate all supports inside the resulting enlarged window.

This is stronger than proving a path from C to a constant state. One-way escape does not imply that the original component can be reached back from the canonical component. The two unchanged exterior collars provide exactly the missing return path.

There is, however, a useful symmetry refinement. Horizontal reflection
maps a component C to a reversed component \(C^{\rm rev}\) with the same
Perron root. It reverses directed paths and fixes C_*, since the constant
history g is unchanged. Therefore the following **uniform one-way
criterion** is sufficient:
\[
 \text{Every recurrent C with }\rho(C)\ge\rho(C_*)
       \text{ has a path }C\longrightarrow C_*.
\]
Apply the same hypothesis to \(C^{\rm rev}\), then reverse its escape
path to obtain \(C_*\longrightarrow C\). Thus \(C=C_*\).
This criterion does not require a separately constructed return path,
but its hypothesis must cover the reversed component as well. A
one-way path verified for just one component is still insufficient.

In geometric terms, a universal theorem giving a finite transition
from each competing periodic sea to a constant right tail would settle
dominance, because the same theorem applies to the reflected periodic
sea. A theorem for every recurrent periodic sea would prove the
stronger assertion that C_* is the only recurrent component.

The existing fixed-anchor counterexamples do not refute this lemma's hypothesis: the proposed modification may change a larger finite region on both sides, and its inserted gate is not required to occur at a prescribed phase or distance. Neither do isolated-lowering obstructions rule out a coordinated finite modification.

## 2. An equivalent entropy target

Let \(X_{\neg g}\) be the sea shift with the additional forbidden word \(1^L\). Then
\[
 C_*\text{ is the unique maximal-entropy component}
 \quad\Longleftrightarrow\quad
 h_{\rm top}(X_{\neg g})<\log\rho(C_*).
\tag{1}
\]

For the forward implication, removing g strictly decreases the Perron root inside the irreducible component C_*; every other recurrent component already has smaller root, and there are only finitely many. For the reverse implication, every component other than C_* avoids g, so its root is smaller.

Thus a rigorous exponential upper bound on gate avoidance would settle exact dominance. The current pressure estimates compare errors only up to a positive remainder that may be much larger than the unknown fixed-height gap in (1).

A particularly concrete sufficient target is: every periodic sea can be modified in a finite interval, with its two L-collars held fixed, to create the gate \(1^L\). That statement is presently unproved.

## 3. Sampling local-lemma results do not apply at the available parameters

Wang and Yin's
[A Sampling Lovász Local Lemma for Large Domain Sizes](https://arxiv.org/abs/2307.14872)
proves approximate counting and sampling for atomic constraints in a regime of the form
\[
 pD^{\,2+o_q(1)}\lesssim1,
\]
where p is the largest atomic violation probability and D is the dependency degree. This is a sampling theorem, not by itself a theorem identifying a particular infinite-volume component.

Even the protected mixed-four subfamily is outside this displayed regime. Each event has probability \(\Theta(h^{-4})\). The proved mixed mean is \(\Theta(\log^4h/h)\), so the number of normalized mixed supports per horizontal translation is
\(\Theta(h^3\log^4h)\). Translating each such support to meet a prescribed column gives this order of incident distinct events. Hence the ordinary dependency degree satisfies
\[
 D\ge c h^3\log^4h,\qquad
 pD^2\ge c h^2\log^8h\longrightarrow\infty.
\tag{2}
\]
Adding the six-cell family cannot improve this test. The small compatible extension sums used in the pressure proofs are different quantities from D and do not verify the cited theorem's hypotheses.

Dobrushin-type uniqueness criteria require bounds on the change of conditional single-site laws under arbitrary admissible boundary changes. For example,
[Hayes's influence-matrix theorem](https://www.cs.unm.edu/~hayes/papers/EigenvalueDobrushin/EigenvalueDobrushin-FOCS06.pdf)
requires an influence contraction. Our product-measure and finitely pinned-cell estimates do not supply that worst-boundary estimate. Conditioning on an entire history is not the same operation as conditioning on one or two black assignments. No Dobrushin contraction has been proved here.

## 4. Near-full entropy also needs a range hypothesis

Pavlov's
[Shifts of finite type with nearly full entropy](https://arxiv.org/abs/1301.0854)
proves uniqueness of the maximal-entropy measure under a sufficiently small entropy deficit for a **nearest-neighbor** shift. It does not assert the same conclusion with a range-independent deficit for arbitrary memory.

For an overlapping L-history presentation, the state alphabet has at least \(\rho^L\) recurrently appearing words, while the entropy per original shift is \(\log\rho\). Its deficit from the full state alphabet is therefore at least
\((L-1)\log\rho\), far from the required small constant.

Nonoverlapping L-block coding changes entropy to \(L\log\rho\), but then the required deficit is
\[
 \log |\mathcal L_L(X)|-L\log\rho.
\]
The current finite-end comparison bounds this only by quantities of order \(h\log^2h\). It does not prove the small constant required by the nearest-neighbor theorem.

Here is a direct reason that the range restriction matters. Take an alphabet of k data letters and two markers 0,1. Impose:

- every L consecutive positions contain a marker;
- opposite markers cannot occur within distance L.

Every bi-infinite valid word uses only one marker type: consecutive markers have gap at most L, so their types must agree. There are two disjoint recurrent components, exchanged by swapping 0 and 1.

Each component is the shift on k data letters and one marker with data runs of length at most L-1. Its growth lambda satisfies
\[
 1=\sum_{j=0}^{L-1}\frac{k^j}{\lambda^{j+1}},
\]
and tends to k+1 as L tends to infinity. Choosing L sufficiently large with k gives
\[
 \log(k+2)-\log\lambda\longrightarrow0
\]
while there remain two maximal-entropy components.

This example does not refute a theorem using the bounded arity and
stronger compatible-extension estimates available for the rectangle
model: its no-marker rule has arity L, and its marker interactions have
large conditioned pressure. It does show why entropy closeness alone
cannot replace the missing finite returning bridge.

## 5. Remaining geometric task

The useful target is now local and exact: create a constant-history gate inside a periodic sea while keeping both exterior histories. A proof may use a variable transition region, but must check interactions across both ends. The existing positive-fraction entropy captures, fixed-anchor buffers, and asymptotic pressure comparisons do not yet establish this returning-gate property.

No uniqueness or canonical-dominance claim is made in this note.

The elementary gate statements and marker example passed
[independent review](canonical_gate_elementary_audit.md). That review
does not claim a second verification of the external theorem statements;
the source-hypothesis checks in Sections 3--4 are recorded separately
from the proved geometric results.

