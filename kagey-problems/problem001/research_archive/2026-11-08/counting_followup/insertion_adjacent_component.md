# Primitive boundary sea components with positive insertion weights

8 November 2026. Every row partition has a primitive sea component containing the two constant boundary states, and every edge can be inserted through that component. The parity partition has the stronger adjacent-row connection proved below. This note does not claim that the constructed component has maximal entropy among all sea components.

Let `L=2W_h` be the memory length in the report's sea graph. A state is an allowed sea word of length `L`. The sea graph excludes hidden tilted rectangles, axis rivals computed with the specified full pair set `F_pi`, and repeated tilted presentations.

## 0. Boundary switches work for every partition

**Boundary-switch lemma.** The bi-infinite sea `1^infinity h^infinity`, with one switch, is valid for every row partition. So is its horizontal reflection.

**Proof.** A tilted rectangle has at most one corner in each boundary row. If it has two black corners, those corners lie in rows 1 and `h` and are opposite. Write them as `A=(x,1)` and `C=(z,h)`, with `x<z` across the switch. The white diagonal has the same midpoint and length as `AC`.

The two white rows are strictly interior. A vertical white diagonal would have length `sqrt((z-x)^2+(h-1)^2)>h-1`, so it does not fit in the grid. If the whites form a horizontal diagonal, their columns lie strictly to the left of `x` and to the right of `z`. Their columns therefore have different black rows, 1 and `h`, so they have no horizontal axis rival. An oblique white pair has no axis rival because the crossed cells are in interior rows, whereas all black points are on boundary rows. Rectangles with zero or one black corner show at least three points. There are no hidden rectangles or singleton presentations.

Two tilted rectangles sharing a white pair must use it as a diagonal: a side presentation would require a black complementary side joining rows 1 and `h`, which is impossible for a tilted rectangle. The common midpoint and length determine the horizontal separation of the black boundary corners. Their orientation is fixed by the switch, so their positions, and therefore the rectangle, are unique. None of these arguments uses `F_pi`. ∎

**General boundary component.** It follows that `1^L` and `h^L` lie in one strongly connected component `C_boundary,pi`. Its constant states have self-loops, so the component is primitive. Arbitrary concatenations of the constant blocks `1^L` and `h^L` are valid: every forbidden window of length at most `L+1` sees at most one switch. Hence

\[
 \rho_{\mathrm{boundary},\pi}\ge 2^{1/L}>1.
\]

For even `h`, the stronger bound `rho_boundary,pi>=2` holds. Every word over `{1,h}` is valid for every partition. In the preceding proof, a horizontal white diagonal is impossible because its midpoint row `(1+h)/2` is not an integer. Two possible orientations of a black boundary diagonal cannot both occur, because that would require both boundary rows black in the same columns.

## 1. Every adjacent-row alphabet is a full two-shift

**Proposition 1.** For every `1<=r<h`, every word over the two rows `{r,r+1}` is an allowed parity sea word.

**Proof.** A tilted lattice rectangle has row span at least two: its vertical side components have positive magnitudes `b,d`, so its four corners cannot all lie on two adjacent rows. Thus no tilted rectangle is hidden.

Suppose a tilted rectangle has three black corners. Two of those corners have the same row. They cannot be adjacent, since a horizontal side would make the rectangle axis-aligned. Thus they form a horizontal diagonal, and the third black corner lies in the other row. If their horizontal displacements from the right-angle vertex are `u,v`, orthogonality gives `uv=-1`. Hence the rectangle is a unit diamond. Its missing point is in the column of the black vertex, two rows away from that vertex. This pair has even row difference, so the singleton has no axis rival for the parity pair set. Moreover, a missing point determines at most one such unit diamond over the fixed alphabet `{r,r+1}`. Thus two tilted rectangles cannot have the same singleton presentation.

Now suppose a tilted rectangle shows a pair of white points. If that pair is vertical, its black diagonal either is horizontal or joins the two adjacent rows. In the horizontal case, its length is even because its midpoint column is integral. The white vertical pair therefore has even row difference and is not in the parity pair set. In the adjacent-row case, an integral diagonal length would require `x^2+1=z^2` with nonzero integer `x`, which is impossible. The same equation excludes a horizontal white pair whose black diagonal joins adjacent rows. A horizontal black diagonal cannot have a distinct horizontal white diagonal. Thus there is no horizontal rival.

For an oblique axis rival, the two crossed cells are also black. If the white pair is a diagonal of the tilted rectangle, its black diagonal and the crossed black diagonal form a hidden rectangle. This is impossible on two adjacent rows. If the white pair is a side, its black complementary side and the crossed pair both use the row set `{r,r+1}`. The white side and the complementary black side consequently have the same midpoint row. Their translation is horizontal; perpendicularity to the oblique side then forces that translation to be zero. This is degenerate, so there is no oblique rival.

Finally consider two tilted rectangles with the same white pair. When the pair is a side of both, their two complementary black sides form a hidden rectangle. When it is a diagonal of both, their two black diagonals form a hidden rectangle. Both cases are impossible. In the remaining mixed case, let `U` be the complementary black side vector and `V` the other black diagonal vector. They have equal lengths. The side has vertical component of magnitude one, whereas the diagonal has vertical component zero or one. The zero case again requires a difference of two squares to equal one, with a nonzero horizontal side component. The one case gives `|U_x|=|V_x|`; then the diagonals are coincident or the second rectangle is axis-aligned. Neither yields two distinct tilted rectangles. ∎

The parity assumption is necessary. For a general partition, a unit diamond can have a singleton rival through a same-parity pair of rows.

## 2. A canonical primitive component

**Corollary 2.** All constant sea states `1^L,...,h^L` belong to one strongly connected component `C_*`. This component is primitive and its Perron root `rho_*` is at least two when `h>=2`.

**Proof.** Proposition 1 allows the concatenations `r^L(r+1)^L` and `(r+1)^L r^L`. Thus successive constant states reach each other. Every constant state has a self-loop. A strongly connected component containing a self-loop has period one. The full two-shift over any adjacent pair lies in this component: each of its states reaches and is reached from the associated constant states. Its entropy is two. ∎

This proves aperiodicity for a specific component at every height. It does not prove irreducibility of the entire sea graph or identify the globally maximal component.

## 3. Every double can be inserted through its boundary component

**Proposition 3.** For every partition `pi`, every edge `e={a,b}` admits a valid marked bridge

\[
 1^L\ e\ h^L
\]

from the constant state `1^L` to the constant state `h^L`. Consequently every double has positive insertion weight on `C_boundary,pi`. For parity, this is the component `C_*` of Corollary 2.

**Proof.** Use the isolated-double configuration with row-1 seas to the left and row-h seas to the right. The proof of Proposition "alternating seas" in `jis/sections/sec075_general.tex` verifies this configuration locally. Its verification remains valid when rivals are tested against the full pair set `F_pi`, rather than the one-edge graph: every weak tilted rectangle shows exactly two points, and these points are never a vertical pair. The only possible axis rivals are horizontal or oblique, whose tests depend on the black rows in the shown columns and are excluded in that proof. Its tilted-tilted comparison also uses only this local configuration. There are no hidden rectangles.

Therefore all windows in `1^infinity e h^infinity` are allowed. Starting in state `1^L`, reading `e` followed by `L` copies of `h` leaves state `h^L`. Both states lie in `C_boundary,pi`. Their Perron coordinates are positive, so this positive marked transfer gives a strictly positive insertion weight. ∎

Thus, if `C_boundary,pi` is the unique component of maximal sea entropy, both primitivity and the double-insertion hypothesis of Theorem A3 hold automatically. The remaining component question is dominance, not insertion. For nonparity partitions, the hidden-diamond correction in `exact_counting_scc_and_resolvent.md` must still be included in the full leading constant.

## 4. An unconditional counting lower bound

**Corollary 4.** For fixed `h>=3` and any balanced partition `pi`, let `q=floor(h^2/4)`. There is a constant `c_h,pi>0` such that, for all sufficiently large `m`,

\[
 a_h(m)\ge b_\pi(m)\ge c_{h,\pi}m^q\rho_{\mathrm{boundary},\pi}^{\,m}.
\]

**Proof.** Fix one order of all edges of `pi`. Start with state `1^L`. Between successive marked bridges of Proposition 3, use sea paths in `C_boundary,pi` from `h^L` back to `1^L`. Before the first bridge use a sea path from `1^L` to itself, and after the last use a sea path from `h^L` to itself. Each bridge reads its double and then `h^L`, so its memory is cleared before the next sea path. Every resulting full word is locally valid, has no hidden rectangle, and contains each double exactly once. The localization lemma therefore makes it a valid blackout. Its black count is `m+q`, which is optimal for sufficiently large widths.

There are `q+1` free sea-path lengths. Primitivity and Perron--Frobenius give a positive constant times `rho_boundary,pi^n` paths for each specified pair of endpoints when `n` is sufficiently large. Summing over compositions of the remaining length yields a positive constant times `m^q rho_boundary,pi^m`. The decomposition is unambiguous: the double positions determine every intervening path length, and the `L` prescribed letters after each double belong to its marked bridge. ∎

For parity this gives the stated bound `a_h(m)>=c_h m^q rho_*^m`. The general result does not identify the leading growth of all maximum blackouts if another sea component, or another partition, has larger entropy.

## 5. A concrete obstruction to blind boundary padding

A valid sea word, even on a Sidon row alphabet, need not admit immediate constant-boundary padding.

At height 15, the word

\[
 w=(1,15,1,1,1,1,1,11)
\]

is a valid finite parity sea word. Its row alphabet `{1,11,15}` is Sidon. However, `1^6 w` is invalid. With zero-based column coordinates its two rectangles are

\[
 R=\{(1,3),(5,1),(7,15),(11,13)\},
\]
\[
 R'=\{(1,3),(3,1),(11,13),(13,11)\}.
\]

They have the same presentation `{(1,3),(11,13)}`. The other four displayed cells are black. Both rectangles are tilted, as direct side-vector dot products verify.

The finite word's validity was checked by exhaustive tilted-rectangle enumeration with the full parity pair set. This example disproves a direct-padding argument; it does not disprove a longer bridge, or establish that the word belongs to a different recurrent component.

## 6. The full parity sea graph is not irreducible

At height 10, `W_h=21` and `L=42`. Define the 13-letter word

\[
 v=5^5\,1^4\,(10,2,1,4).
\]

Exhaustive checking shows that `1^42 v` is an allowed sea word. Hence its final length-42 state is reachable from the constant state `1^42` in `C_*`. Nevertheless, this final state has no outgoing edge.

To prove the last assertion, index its last nine letters as

\[
 (w_0,\ldots,w_8)=(5,1,1,1,1,10,2,1,4).
\]

The three black corners

\[
 (6,2),\ (7,1),\ (8,4)
\]

complete a tilted rectangle at `(9,3)`. Indeed, the two vectors from `(6,2)` are `(1,-1)` and `(2,2)`. Similarly,

\[
 (0,5),\ (4,1),\ (5,10)
\]

complete a tilted rectangle at `(9,6)`, using the perpendicular vectors `(4,-4)` and `(5,5)` from `(0,5)`.

If the appended sea letter is even, the first rectangle shows the singleton `(9,3)` and has an axis rival through the parity pair `{3,w_9}`. If it is odd, the second rectangle shows `(9,6)` and has an axis rival through `{6,w_9}`. Thus every possible next letter fails.

This is a transient dead-end state, not another recurrent component. It disproves irreducibility of the full state graph and the assertion that every locally allowed state can be bridged to a constant sea. It does not refute uniqueness or dominance of `C_*` among recurrent components. A proof of the counting theorem must distinguish locally allowed states from recurrent sea states.

## 7. Finite verification

`insertion_check.py` independently enumerates all tilted rectangle placements and tests rivals against the specified full virtual pair set. It checks all 3,584 length-eight words over adjacent rows at heights 3 through 6 and all 33 isolated parity doubles at heights 3 through 7. Across all balanced partitions at heights 3 through 7, it also checks 122 boundary switches and 588 isolated doubles. The even-height boundary check covers 3,328 length-eight words. The height-15 padding counterexample and the height-10 dead-end certificate pass independent checks. Results are recorded in `insertion_checks.json`. The analytical arguments above establish the adjacent-row, boundary-switch, and insertion results at every height.
