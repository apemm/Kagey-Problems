# Dominance of the canonical sea component: reductions and a forcing lemma

Research note, 9 November 2026. General dominance is not proved here. This note proves
three reductions that show exactly what a proof must supply, and a parity forcing lemma
that explains why constant exits fail. It builds on
`../2026-11-08/general_dominance_quadratic/dominance_comparison.md`,
`../2026-11-08/general_dominance_quadratic/dominance_bridge.md`, and
`../2026-11-08/counting_followup/`.

Notation. Fix the parity partition and height h. Let W = 1 + floor((h-1)^2/4) and L = 2W.
The sea graph G has the allowed sea words of length L as states and the allowed words of
length L+1 as edges. C_* is the primitive component containing every constant state.

## 1. Which components control the counting formula

The exact automaton of `exact_counting_scc_and_resolvent.md` starts from the empty history
and accepts any terminal history whose used-edge set is complete.

**Lemma 1.1 (universal ends).** Every finite word read along a path of G is a valid prefix
from the empty history. Every terminal history is accepted once all doubles have been used.

Proof. Each test applied when a letter is appended concerns only cells in the current
window. The window from the empty history is a suffix of the corresponding window in G.
Removing columns on the left removes rectangles and never creates a presentation or a rival.
The acceptance condition involves only the used-edge set. QED.

**Lemma 1.2 (reversal).** The map x -> -x on columns sends allowed sea words to allowed sea
words. It fixes C_* and sends a recurrent component C to a recurrent component C^R with
the same Perron root. Moreover, C_* reaches C exactly when C^R reaches C_*.

Proof. Reflection sends rectangles to rectangles and keeps tilted ones tilted. It maps
presentations bijectively, and it maps horizontal, vertical, and oblique axis rivals to
rivals of the same type. The pair set F does not depend on columns. Cycles reverse to
cycles, the constant states are fixed, and a path from C_* to C reverses to a path from
C^R to C_*. QED.

**Proposition 1.3.** Let K be the set of recurrent components that lie on at least one
accepting path of the automaton for the parity partition. Then:

1. K contains C_* and every recurrent component C comparable with C_*, that is,
   C_* reaches C or C reaches C_*.
2. b_par(m) = O(m^D R^m) for some D, and limsup b_par(m)^{1/m} = R, where
   R = max over C in K of rho(C).
3. If rho_* > rho(C) for every other C in K, then the product formula
   b_par(m) ~ B (prod kappa_e) m^q rho_*^m holds. If some C in K has rho(C) > rho_*,
   it fails.

Proof. For item 1, suppose C_* reaches C. Read 1^L from the empty history. Insert all q
doubles with the bridges 1^L e h^L of `insertion_adjacent_component.md`. Join the bridges
by sea paths in C_*. Follow the path into C, stay in C for any length, and stop. Lemma 1.1
accepts the result. If instead C reaches C_*, start inside C, move to C_*, and insert the
doubles there. Item 2 is the critical-chain formula (5) of the resolvent note. Only components on
accepting paths contribute poles, and a component of K gives a lower bound
c R^m on one residue class. For item 3, under the hypothesis, the components outside K
contribute nothing and section 6 of the resolvent note applies to the trimmed automaton.
Its insertion weights are positive by the bridges. If rho(C) > rho_* for some C in K,
item 2 gives a larger base. A tie at rho_* is not decided by this argument. QED.

**Consequence.** The weaker target "every component into which some double inserts has
root at most rho_*" is not enough. A component downstream of C_* with no double
insertion still contributes rho(C)^m, because the doubles can be spent inside C_* first.
By Lemma 1.2, it is enough to control the components downstream of C_*. The component
C^R of an upstream component C has the same root and lies downstream.

## 2. Bridge proofs are proofs of irreducibility

**Proposition 2.1.** The following are equivalent.

1. (Exit property) Every recurrent state of G has a path to the constant state 1^L.
2. C_* is the only recurrent component of G.

Proof. Item 2 implies item 1 because C_* is strongly connected and contains 1^L. Assume
item 1, and let C be a recurrent component. Then C reaches C_*. Item 1 applied to C^R
shows that C^R reaches C_*, so Lemma 1.2 shows that C_* reaches C. Hence C = C_*. QED.

So any argument that sends every recurrent state into C_* by a bridge, of any length,
proves much more than dominance: the recurrent part of the sea graph is irreducible.
Proposition 2.1 and Lemma 1.2 also show that proving only half of the property gives
the whole of it.

**Proposition 2.2 (no shared windows).** If C is a recurrent component other than C_*,
no word of L(C_*) contains a factor of length L that is a state of C. Any map that edits
words of L(C) into words of L(C_*) must therefore change at least one letter in every
window of length L.

Proof. The windows of a word read inside a component are states of that component.
Distinct components have disjoint state sets. QED.

Thus an entropy comparison by sparse edits can't have edit density below 1/L. Density
1/L would already cost a factor of up to h^(n/L) in multiplicity. Such a comparison
gives at best log rho(C) <= log rho_* + O(log h / h^2), and only an exit argument makes
it exact. A true spectral comparison must avoid bridging altogether. I found no
candidate of that kind, because by Proposition 2.2 the two languages have no common
long factors to compare.

## 3. Parity forcing and the failure of constant exits

**Lemma 3.1 (parity forcing).** In a valid parity sea w, let A, B, C be black points that
form a tilted right angle at B. Let D = A + C - B = (c, r). Suppose that 1 <= r <= h and
that column c belongs to the sea. Then

    w_c != r    and    w_c = r (mod 2).

Proof. If w_c = r, all four corners are black and the rectangle is hidden. A sea has no
hidden rectangle. Suppose instead that w_c and r have opposite parity. The pair {r, w_c}
is then a parity edge, which occurs as a double in some column x_e. The axis rectangle
with corners (c,r), (c,w_c), (x_e,r), (x_e,w_c) shows only (c,r), as does the tilted
rectangle ABCD. These two distinct rectangles collide. QED.

So each black right angle fixes the parity of one column, possibly a future one, and
excludes one row in it. This explains the height-11 table in `dominance_bridge.md`:
singleton failures are forced-parity violations.

**Corollary 3.2 (necessary condition for a constant exit).** Let x be a valid
left-infinite sea ending at column n-1. Let F_n(x) be the set of pairs (c, r) with c >= n
that arise as completions D, with 1 <= r <= h, of black right angles of x. If x r0^∞ is
valid, every (c, r) in F_n(x) has r = r0 (mod 2) and r != r0.

In particular, if F_n(x) contains completion rows of both parities, no constant row can
follow at time n. A two-row tail over {s, s+1} can meet any single forced parity column
by column. It fails at a column c only when the forced row there lies in {s, s+1}, or
when c is forced with both parities.

**Lemma 3.3 (boundary tails have no vertical exposure).** If x 1^∞ is a sea word, no
vertical white pair whose black diagonal has an endpoint on the tail fits in the strip.
The same holds for h^∞ by vertical reflection.

Proof. Let the black diagonal join (x0, a) to (z, 1), with z != x0. Its length L
satisfies L > a - 1, so the lower white row (a + 1 - L)/2 is less than 1. If both
endpoints lie on the tail, the white rows are 1 - d and 1 + d, and 1 - d < 1. QED.

So a boundary exit can fail only through forced parity (Lemma 3.1), horizontal or
oblique rivals with one tail endpoint, and mixed side/diagonal collisions. The height-37
and height-43 certificates show that the last mechanism really occurs.

## 4. Status and stuck point

Proved: Proposition 1.3 (the counting base is controlled by K, which contains every
component comparable with C_*); Lemma 1.2 and Proposition 2.1 (exit for every recurrent
state is equivalent to irreducibility of the recurrent part); Proposition 2.2 (any
edit-based comparison needs density at least 1/L); and Lemmas 3.1 and 3.3 (forcing
structure of exits).

Open: goal 1, goal 3, and any sharpening of goal 2 beyond Proposition 1.3.

Stuck point. Every route I found reduces to the exit property of Proposition 2.1:

> For every recurrent sea state s there is a word u with s u 1^L allowed.

Equivalently, the recurrent part of the sea graph is strongly connected. The obstacle is
an arbitrary recurrent past within distance W of the exit. Its black right angles force
the parities of future columns through Lemma 3.1, with both parities possible. Its point
pairs also create mixed collisions with any fixed tail, as at heights 37 and 43. A proof
needs a bridge u, chosen depending on the past, that satisfies the forced parities column
by column while avoiding the mixed collisions. Natural tails (constants, two-row bands,
modular ramps) each fail on an explicit past. I have no argument that controls the mixed
collisions for an arbitrary past. I also have no spectral comparison that avoids bridges,
which Proposition 2.2 shows would have to be global.
