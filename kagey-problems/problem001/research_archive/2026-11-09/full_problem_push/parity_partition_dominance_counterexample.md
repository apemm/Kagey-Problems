# Ordinary parity does not maximize the seven-row sea entropy

9 November 2026. The proposed dominance of the ordinary parity partition is
false already at height seven.

Let
\[
 \pi_{\mathrm P}=\{2,4,6\}\mid\{1,3,5,7\},\qquad
 \pi_{\mathrm A}=\{1,3,6\}\mid\{2,4,5,7\}.
\]
The complete normalized sea automata have the exact spectral enclosures
\[
 3.776799\le\rho_{\mathrm P}\le3.776801,
 \qquad
 3.780928\le\rho_{\mathrm A}\le3.780929.          \tag{1}
\]
In particular, \(\rho_{\mathrm A}>\rho_{\mathrm P}\).

These are rational bounds with denominator one million. Floating-point
iteration proposes a positive vector; the final inequalities use integers.
An independent verifier checks every coordinate of
\[
 L v\le T v\le U v
\]
on the recurrent component, checks positivity, and verifies an explicit
integer overflow bound.

## Complete graph certificates

The parity graph has 17,463,676 reachable residual states and one recurrent
component of size 16,886,304. The graph for \(\pi_{\mathrm A}\) has
12,928,518 reachable states, 50,304,452 accepted labeled edges, and one
recurrent component of size 12,630,235. Its remaining 298,283 components are
transient singletons.

The \(\pi_{\mathrm A}\) component contains the constant states at rows
1, 2, 6, and 7. It is therefore the boundary component and is primitive.
The constant words at rows 3, 4, and 5 are invalid for this partition.

The independent SCC check verifies every edge against a strict component
ordering, then proves forward and reverse reachability inside the large
component. It does not reuse the builder's SCC algorithm.

The certificates are:

* [Nonparity complete graph report](sea_packed_h7_p136.json)
* [Nonparity SCC verification](sea_packed_h7_p136.scc_verified.json)
* [Nonparity exact spectral bounds](sea_packed_h7_p136.perron.203412.json)
* [Independent nonparity spectral check](sea_packed_h7_p136.perron.203412.verified.json)
* [Independent parity spectral check](sea_packed_h7.perron.307694.verified.json)

The nonparity graph's SHA256 is

8E7686F6CECC428DB3027DCE7958542B9AA588A7F9F89212CC3FE119FAC78CC8.

The automaton uses the complete cross-block pair set of its stated
partition. It does not use parity rival tests for the nonparity graph.
As with the parity graph, normalized supports describe the recurrent sea
language exactly, while finite endpoint constants require the end-aware
model.

The [independent compiler audit](nonparity_sea_compiler_independent_audit.md)
regenerates the full nonparity residual input identically and checks every
period of lengths one through four against a separate equal-diagonal
rectangle generator and explicit presentation tests. All 2,800 periods
agree for each of the parity and nonparity partitions. These finite-period
tests are calibration checks; the entropy comparison uses the complete
graphs and integer certificates.

## Consequence for optimal-board counting

Every balanced seven-row partition has twelve double labels. The positive
insertion bridges through its boundary component give a collared equality
class of order
\[
 m^{12}\rho_{\mathrm A}^{\,m}
\]
for \(\pi_{\mathrm A}\), with a positive constant. The complete parity graph
has one recurrent component, so its full parity equality contribution is
of order
\[
 m^{12}\rho_{\mathrm P}^{\,m}.
\]
Thus the nonparity contribution eventually exceeds the parity contribution
by an exponential factor. A proposed formula for all optimal blackouts with
ordinary-parity exponential base cannot hold.

This counterexample does not disprove dominance of the boundary component
within each partition: both graphs in (1) have exactly that property.
Nor does it affect the parity construction used to prove equality at large
widths. It changes which partition must supply the counting asymptotic.

The final comparison with every balanced partition is recorded separately
in [the height-seven component analysis](sea_components_height_seven.md).
