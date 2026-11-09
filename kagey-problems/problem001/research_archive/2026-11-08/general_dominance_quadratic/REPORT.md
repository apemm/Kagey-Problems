# General dominance and the quadratic threshold construction

Research results, 8 November 2026. All work in this directory is uncommitted.
The manuscript and earlier reports are unchanged.

Neither general dominance nor a quadratic-width equality board is proved.
The new results give explicit all-height double placements, a subpolynomial
bound for separating their Pythagorean conflicts, and additional canonical
component bridge lemmas. Exact counterexamples identify the remaining
four-black obstructions in both directions.

## 1. A simpler arithmetic construction replaces the rigid order problem

Index the odd and even rows by `o_a=2a+1` and `e_b=2b+2`. Choose a prime
`10h<p<20h`, and place the double `{o_a,e_b}` in column

\[
 x_{a,b}=4(a+pb).
\]

Every parity edge occurs exactly once, the width is less than `40h^2+1`,
and **no three marked cells form a tilted right angle**. This holds for
every height `h>=3`, including even heights.

The proof uses reduction modulo `p` at an odd-row vertex and separation
between the `b`-blocks at an even-row vertex. Thus it avoids the even-row
valuation obstruction of the `1,x,h` construction by changing the layout.
It is a placement of doubles, with the other columns still empty.

Its Pythagorean conflicts have a particularly simple form. A vertical
Pythagorean completion fits only when its two marked diagonal endpoints
belong to the same `b`-block. If the odd endpoint comes from column index
`a`, put `u=2a-2b-1`, an odd integer. The other column index `c` must satisfy

\[
 (L-4|c-a|)(L+4|c-a|)=u^2.
\]

There are at most `tau(u^2)-1` choices of `c`. Orient each conflict from
its odd endpoint. The resulting graph has bounded outdegree

\[
 D_h=\max_{\substack{1\le u<h\\u\ \mathrm{odd}}}(\tau(u^2)-1),
\]

so every induced subgraph has average degree at most `2D_h`. It can be
colored with `2D_h+1=h^{o(1)}` colors. Moving the color classes into
separated layers preserves the right-angle exclusion and eliminates every
in-strip vertical P conflict. The resulting width is

\[
 h^{2+o(1)}.
\]

This is an analytical construction with a finite coloring algorithm. It
does not establish `O(h^2)`, exclude the mixed four-black collisions, or
provide the singleton sea.

A fixed-period coloring cannot make the layer count constant in this
placement. For any proposed period `N`, the indices `b=0`, `a=2N^2`,
`c=a+N` have a P conflict from the triple
`(4N,4N^2-1,4N^2+1)`, and the two columns have the same periodic color.
This rules out periodic rules, not a bounded palette assigned aperiodically.

Full proof and coordinate checks: [one_prime_scaffold.md](one_prime_scaffold.md).
The checker verifies the unlifted and lifted right-angle exclusions and
the lifted P exclusion at heights 3 through 41.

## 2. The remaining mixed collisions are real

The one-prime placement has an exact mixed collision for the permitted
choice

\[
 h=9800,\qquad p=115163.
\]

Two tilted rectangles have the same white pair. Their four required black
points come from three double columns, one contributing both of its cells.
Their side and diagonal vectors are

\[
 U=(922080,9605),\qquad V=(922084,-9213),
\]

and their doubled midpoint difference is `H=(4,-384)`. Direct calculation
gives `|U|^2=|V|^2` and `H dot U=0`. Both rectangles fit in the strip.
The prime, all coordinates, and both presentations are checked exactly.

The earlier two-prime CRT placement also has an exact oblique-axis rival
at height 4469 for permitted prime choices. Thus neither arithmetic
placement automatically eliminates Q/T. These examples concern the
specified prime choices and unlifted placements; they do not rule out
other prime choices or a successful additional coloring.

See [one_prime_mixed_obstruction.md](one_prime_mixed_obstruction.md) and
[crt_oblique_counterexample.md](crt_oblique_counterexample.md).

The four double indices in the CRT certificate form an independent set in
the Pythagorean graph. Thus a proper P-coloring can leave this Q collision
intact; the P-coloring requirement alone does not imply Q/T exclusion.

The construction problem now has a concrete alternative to ordering the
rigid `1,x,h` layout: color the mixed-collision hypergraph as well as the
Pythagorean graph, then prove singleton completion. The available
subpolynomial coloring bound controls only the Pythagorean graph.

## 3. A complete identifying set of doubles at width O(h^(5/2))

There is also an all-height theorem that excludes **every** collision
supported by the required double cells alone. Let `S` be the least power
of two satisfying `S^2>4h`, choose primes `p,q` of order `h` as specified
in the proof, and use

\[
 x_{a,b}=S\operatorname{CRT}(a\bmod p,b\bmod q).
\]

The marked doubles form an identifying set of width `O(h^(5/2))`.
The proof separately excludes three-black right angles, vertical and
horizontal axis rivals, and every mixed side/diagonal collision. The
two-adic argument handles the opposite-parity cases, while the two
moduli handle same-parity cases.

This is a valid partial board with empty columns. It is **not an equality
board**, and gives **no new upper bound on the equality threshold**.
Adding one singleton to each empty column is a separate unsolved step.

The proof is in [quadratic_arithmetic.md](quadratic_arithmetic.md), with
an independent review in [arithmetic_audit.md](arithmetic_audit.md).
Coordinate checks through height 25 found no right-angle, P, or mixed
certificate, consistently with the all-height proof.

For the original CRT placement, [quadratic_lifts_pell.md](quadratic_lifts_pell.md)
also proves a subpolynomial P-coloring bound through a generalized Pell
equation. That graph contains an actual `K_4` at height 146, and every
fixed-period coloring eventually fails. These two lower obstructions
apply to the CRT graph, not automatically to the different one-prime graph.

## 4. General dominance: new bridge lemmas

Write `W_h=1+floor((h-1)^2/4)` and use full-history memory `L=2W_h`.

**Boundary reset.** A recurrent component containing `W_h` consecutive
copies of row 1 or row `h` is the boundary component. A tilted rectangle
has span at most `W_h` and at most one corner on a boundary row. Flattening
either side of such a run therefore creates no new weak rectangle or
presentation collision.

**Monotone bridge.** Every valid nondecreasing sea word `w` extends as

\[
 1^\infty\,w\,h^\infty.
\]

For a nonincreasing word, reverse the two boundary rows. This holds for
every row partition. On a monotone graph, the only possible sea violations
are vertical Pythagorean presentations with an axis rival. A new such
presentation using a boundary endpoint cannot fit in the strip.

**Fixed-point loss.** At odd height `h=2k+1`, every nonparity balanced
partition permits at most `k+1` constant-row seas, sharply. At even height
`h=2k`, the same upper bound holds. The proof counts midpoints of separated
same-parity row pairs using the integer sumset inequality. It also gives
exact counts of the additional two-letter diamond prohibitions.

These statements are proved in [dominance_comparison.md](dominance_comparison.md).
The checks cover 1,709 monotone words through height eight and all balanced
partitions through height fourteen.

The results do not give a sufficient entropy penalty outside the canonical
component. In particular, counting lost fixed points does not prove a
Perron-root comparison. A hypothetical external recurrent component also
cannot be repaired into canonical words by a bounded number of edits:
for a length-`n` word, at least `ceil((n-L+1)/L)` edits are required.
This follows because the two components share no full memory state.

## 5. Longer bridges are necessary

For every odd prime `p`, choose a nonzero residue `c` such that
`1+c^2` is a quadratic nonresidue modulo `p`. The periodic sea

\[
 y_x=cx\pmod p,\qquad 0\le y_x<p,
\]

is valid for every partition at height `p`. Such a slope exists by the
elementary quadratic-character sum. These are explicit recurrent seas
using all rows.

At height 11, one phase of the slope-one sea has no immediate constant
exit in any row. At heights 37 and 43, the proposed phase-zero exit to
row `p-2` fails by exact mixed collisions, despite smaller successful
checks. The height-37 collision uses only one black point from the tail;
the height-43 collision uses two.

The modular sea remains parity-valid when placed in a `p`-row band of
any taller strip. Thus the failed prescribed height-37 exit persists at
every height at least 37. None of these facts proves a separate recurrent
component: longer bridges may still connect these periodic seas to the
canonical component.

Proofs and exact certificates: [dominance_bridge.md](dominance_bridge.md)
and [modular_bridge_audit.md](modular_bridge_audit.md).

## 6. Consequences for the two main questions

For dominance, the earlier bound `lambda_*(h)>=c h^(1/3)` remains proved
inside the canonical component. The new bridge criteria enlarge the
class of states known to belong to it, but no general entropy comparison
or arbitrary-past bridge has been established. The all-height counting
formula therefore remains conditional on dominance.

For the threshold, the arithmetic layouts work at every height and remove
the three-double order obstruction. The one-prime divisor argument also
removes P at a subpolynomial cost. Q/T and singleton completion remain,
and the full `O(h^2)` equality construction is open.

The rigid `1,x,h` family is therefore no longer the only analytically
structured option. The one-prime placement provides a simpler all-height
starting point, but the evidence does not yet justify treating its
completion as likely or its remaining hypergraph as bounded-colorable.
